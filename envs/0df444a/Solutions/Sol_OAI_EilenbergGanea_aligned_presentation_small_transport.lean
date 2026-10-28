-- Prove2me | solution 1 for OAI.EilenbergGanea.aligned_presentation_small_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:24:19.88675+00:00
-- url     : https://prove2.me/submissions/10a53f27-416b-48d5-b5ce-cc4d80ade13f

import Mathlib
import Definitions.Def_OAIEGC003

section
-- module Solutions.OAIEG.Regularization
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology

/-! Localized regularization for finite SU(2) systems. -/
namespace EilenbergGanea
section ComplexCentralizer
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem complex_smul_decompose (z : ℂ) (x : V) :
    z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul]
  change (algebraMap ℝ ℂ z.re) • x +
    (algebraMap ℝ ℂ z.im) • (Complex.I • x) = _
  simp only [IsScalarTower.algebraMap_smul]

/-- Commuting with a non-real scalar forces a real-linear map to be complex-linear. -/
theorem realLinear_map_complex_smul (f : V →ₗ[ℝ] V) (z : ℂ) (hz : z.im ≠ 0)
    (hf : ∀ x, f (z • x) = z • f x) (w : ℂ) (x : V) :
    f (w • x) = w • f x := by
  have hI (y : V) : f (Complex.I • y) = Complex.I • f y := by
    have he := hf y
    rw [complex_smul_decompose z y, complex_smul_decompose z (f y),
      map_add, map_smul, map_smul] at he
    exact smul_right_injective V hz (add_left_cancel he)
  rw [complex_smul_decompose w x, complex_smul_decompose w (f x),
    map_add, map_smul, map_smul, hI]

theorem complexLinear_of_commutes_nonreal (N : V →ₗ[ℝ] V) (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ v, N (z • v) = z • N v) :
    ∃ C : V →ₗ[ℂ] V, C.restrictScalars ℝ = N := by
  let C : V →ₗ[ℂ] V :=
    { toFun := N
      map_add' := N.map_add
      map_smul' := realLinear_map_complex_smul N z hz h }
  exact ⟨C, rfl⟩

end ComplexCentralizer

section RotationDerivative
variable {A V : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- A real derivative commuting with the fixed-plus-rotating representation
has no mixed blocks. Its normal block is complex-linear. -/
theorem rotation_commutant_blocks (L : A × V →ₗ[ℝ] A × V)
    (z : ℂ) (hz : z.im ≠ 0)
    (h : ∀ a v, L (a, z • v) = ((L (a, v)).1, z • (L (a, v)).2)) :
    ∃ (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V),
      L = T.prodMap (N.restrictScalars ℝ) := by
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  let T := (LinearMap.fst ℝ A V).comp (L.comp (LinearMap.inl ℝ A V))
  let N := (LinearMap.snd ℝ A V).comp (L.comp (LinearMap.inr ℝ A V))
  let P := (LinearMap.fst ℝ A V).comp (L.comp (LinearMap.inr ℝ A V))
  have hP (v : V) : P (z • v) = P v := by
    have hv := congrArg Prod.fst (h 0 v)
    exact hv
  have hPzero (v : V) : P v = 0 := by
    let u := (z - 1)⁻¹ • v
    have huv : z • u - u = v := by
      dsimp [u]
      calc
        z • ((z - 1)⁻¹ • v) - (z - 1)⁻¹ • v =
            (z - 1) • ((z - 1)⁻¹ • v) := by rw [sub_smul, one_smul]
        _ = v := by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hz1), one_smul]
    rw [← huv, map_sub, hP, sub_self]
  have hQzero (a : A) : (L (a, 0)).2 = 0 := by
    have hv := congrArg Prod.snd (h a 0)
    simp only [smul_zero] at hv
    have hh : (z - 1) • (L (a, 0)).2 = 0 := by
      rw [sub_smul, one_smul, ← hv, sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hz1)
  obtain ⟨C, hC⟩ := complexLinear_of_commutes_nonreal N z hz
    (fun v => congrArg Prod.snd (h 0 v))
  refine ⟨T, C, ?_⟩
  rw [hC]
  apply LinearMap.ext
  intro q
  apply Prod.ext
  · change (L q).1 = T q.1
    have he : q = (q.1, 0) + (0, q.2) := by simp
    rw [he, map_add]
    change T q.1 + P q.2 = _
    rw [hPzero, add_zero]
    simp
  · change (L q).2 = N q.2
    have he : q = (q.1, 0) + (0, q.2) := by simp
    rw [he, map_add]
    change (L (q.1, 0)).2 + N q.2 = _
    rw [hQzero, zero_add]
    simp

end RotationDerivative

section NormalDeterminant
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

theorem complex_real_det_pos (N : V →ₗ[ℂ] V) (hN : N.det ≠ 0) :
    0 < (N.restrictScalars ℝ).det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  exact Complex.normSq_pos.mpr hN

end NormalDeterminant

section SimultaneousShift
open Set
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A single real scalar regularizes any finite collection of normal blocks. -/
theorem exists_small_simultaneous_regular_shift {ι : Type*} [Fintype ι]
    (N : ι → Module.End ℂ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, |s| < ε ∧ ∀ i, IsUnit (N i + algebraMap ℂ (Module.End ℂ V) (s : ℂ)) := by
  let bad : Set ℝ := ⋃ i, {r | -(r : ℂ) ∈ spectrum ℂ (N i)}
  have hbad : bad.Finite := Set.finite_iUnion (fun i =>
    (Module.End.finite_spectrum (N i)).preimage
      (fun _ _ _ _ h => Complex.ofReal_injective (neg_injective h)))
  obtain ⟨s, hs, hgood⟩ := (Set.Ioo_infinite (by linarith : -ε < ε)).exists_notMem_finite hbad
  refine ⟨s, abs_lt.mpr hs, fun i => ?_⟩
  have hn : -(s : ℂ) ∉ spectrum ℂ (N i) := by
    intro hh
    exact hgood (Set.mem_iUnion.mpr ⟨i, hh⟩)
  have hi := (spectrum.notMem_iff.mp hn).neg
  simpa only [map_neg, neg_sub, sub_neg_eq_add] using hi

end SimultaneousShift
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section EquivariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem equivariant_fderiv (f : E → E) (L : E ≃L[ℝ] E)
    (hf : Differentiable ℝ f) (he : ∀ x, f (L x) = L (f x)) (x : E) :
    (fderiv ℝ f (L x)).comp L.toContinuousLinearMap =
      L.toContinuousLinearMap.comp (fderiv ℝ f x) := by
  have h₁ := (hf (L x)).hasFDerivAt.comp x L.hasFDerivAt
  have h₂ := L.hasFDerivAt.comp x (hf x).hasFDerivAt
  have hh : f ∘ L = L ∘ f := funext he
  rw [hh] at h₁
  exact h₁.unique h₂

omit [FiniteDimensional ℝ E] in
theorem equivariant_fderiv_det (f : E → E) (L : E ≃L[ℝ] E)
    (hf : Differentiable ℝ f) (he : ∀ x, f (L x) = L (f x)) (x : E) :
    (fderiv ℝ f (L x)).det = (fderiv ℝ f x).det := by
  have h := congrArg (fun M : E →L[ℝ] E => M.det) (equivariant_fderiv f L hf he x)
  change ((fderiv ℝ f (L x)).toLinearMap.comp L.toLinearEquiv.toLinearMap).det =
    (L.toLinearEquiv.toLinearMap.comp (fderiv ℝ f x).toLinearMap).det at h
  rw [LinearMap.det_comp, LinearMap.det_comp, mul_comm] at h
  exact mul_left_cancel₀ L.toLinearEquiv.isUnit_det'.ne_zero h
end EquivariantDerivative

section FixedRegularization
variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem normalShift_contDiff (f : A × V → A × V) (hf : ContDiff ℝ ∞ f) (s : ℝ) :
    ContDiff ℝ ∞ (normalShift f s) :=
  hf.add ((show ContDiff ℝ ∞ (fun _ : A × V => s) from contDiff_const).smul
    (normalProjection (A := A) (V := V)).contDiff)

theorem normalShift_fderiv (f : A × V → A × V) (hf : Differentiable ℝ f) (s : ℝ) (x : A × V) :
    fderiv ℝ (normalShift f s) x = fderiv ℝ f x + s • normalProjection :=
  ((hf x).hasFDerivAt.add ((normalProjection (A := A) (V := V)).hasFDerivAt.const_smul s)).fderiv

variable [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

/-- At a fixed point the derivative splits with a complex-linear normal block. -/
theorem fixed_fderiv_blocks (f : A × V → A × V) (hf : Differentiable ℝ f)
    (z : ℂˣ) (hz : (z : ℂ).im ≠ 0)
    (he : ∀ q, f (scalarRotation z q) = scalarRotation z (f q)) (a : A) :
    ∃ (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V),
      (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ) := by
  apply rotation_commutant_blocks _ (z : ℂ) hz
  intro b v
  have h := congrArg (fun L : (A × V) →L[ℝ] (A × V) => L (b, v)) (equivariant_fderiv f (scalarRotation z) hf he (a, 0))
  simpa using h

variable [FiniteDimensional ℝ A] [FiniteDimensional ℂ V]

/-- Scalar shifts have the claimed fixed-block Jacobian, with no chart convention. -/
theorem normalShift_fixed_det (f : A × V → A × V) (hf : Differentiable ℝ f)
    (a : A) (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V)
    (h : (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ)) (s : ℝ) :
    (fderiv ℝ (normalShift f s) (a, 0)).det =
      T.det * ((N + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ).det := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  rw [normalShift_fderiv f hf]
  have he : (fderiv ℝ f (a, 0) + s • normalProjection).toLinearMap =
      T.prodMap ((N + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ) := by
    apply LinearMap.ext
    intro q
    have hh := LinearMap.congr_fun h q
    change (fderiv ℝ f (a, 0)) q + s • (0, q.2) = _
    change (fderiv ℝ f (a, 0)) q = (T q.1, N q.2) at hh
    rw [hh]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero,
      LinearMap.prodMap_apply, LinearMap.restrictScalars_apply, LinearMap.add_apply,
      Module.algebraMap_end_apply]
    congr 2
    exact (IsScalarTower.algebraMap_smul ℂ s q.2).symm
  change (fderiv ℝ f (a, 0) + s • normalProjection).toLinearMap.det = _
  rw [he, LinearMap.det_prodMap]


omit [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
theorem fixedRestriction_fderiv (f : A × V → A × V) (hf : Differentiable ℝ f)
    (a : A) (T : A →ₗ[ℝ] A) (N : V →ₗ[ℂ] V)
    (h : (fderiv ℝ f (a, 0)).toLinearMap = T.prodMap (N.restrictScalars ℝ)) :
    (fderiv ℝ (fixedRestriction f) a).toLinearMap = T := by
  have hd := (ContinuousLinearMap.fst ℝ A V).hasFDerivAt.comp a
    ((hf (a, 0)).hasFDerivAt.comp a (ContinuousLinearMap.inl ℝ A V).hasFDerivAt)
  have hfun : (ContinuousLinearMap.fst ℝ A V) ∘ (f ∘ (ContinuousLinearMap.inl ℝ A V)) =
      fixedRestriction f := rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  apply LinearMap.ext
  intro q
  exact congrArg Prod.fst (LinearMap.congr_fun h (q, 0))

/-- Simultaneously regularize the finite fixed fiber, retaining its tangent sign. -/
theorem exists_normalShift_regular_fixed (f : A × V → A × V) (hf : Differentiable ℝ f)
    (z : ℂˣ) (hz : (z : ℂ).im ≠ 0)
    (he : ∀ q, f (scalarRotation z q) = scalarRotation z (f q))
    (S : Finset A) (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, |s| < ε ∧ ∀ a ∈ S,
      (fderiv ℝ (normalShift f s) (a, 0)).det ≠ 0 ∧
      (0 < (fderiv ℝ (normalShift f s) (a, 0)).det ↔ 0 < c) := by
  classical
  choose T N hblock using (fun a : S => fixed_fderiv_blocks f hf z hz he a.val)
  obtain ⟨s, hs, hregular⟩ := exists_small_simultaneous_regular_shift N hε
  refine ⟨s, hs, fun a ha => ?_⟩
  let i : S := ⟨a, ha⟩
  have ht : (T i).det = c := by
    rw [← fixedRestriction_fderiv f hf a (T i) (N i) (hblock i)]
    exact hT a ha
  have hn : 0 < ((N i + algebraMap ℂ (Module.End ℂ V) (s : ℂ)).restrictScalars ℝ).det :=
    complex_real_det_pos _ (LinearMap.isUnit_det _ (hregular i)).ne_zero
  rw [normalShift_fixed_det f hf a (T i) (N i) (hblock i), ht]
  exact ⟨mul_ne_zero hc hn.ne', mul_pos_iff_of_pos_right hn⟩

end FixedRegularization
end EilenbergGanea

open Set Filter Topology
namespace EilenbergGanea
section LinearParameters
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem linearPerturbation_hasFDerivAt (f : E → E) (T : ι → E → (E →L[ℝ] E))
    {x : E} (hf : DifferentiableAt ℝ f x) (hT : ∀ j, DifferentiableAt ℝ (T j) x)
    (p : ι → E) : HasFDerivAt (fun z => linearPerturbation f T z p)
      (linearPerturbationDerivative f T x p) x := by
  apply hf.hasFDerivAt.add
  apply HasFDerivAt.fun_sum
  intro j _
  simpa using (hT j).hasFDerivAt.clm_apply (hasFDerivAt_const (p j) x)

theorem linearSolvedParameter_outside (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i j : ι) (hji : j ≠ i) :
    (fun q => linearSolvedParameter f T i q j) = fun q => q j := by
  funext q
  exact Function.update_of_ne hji _ _

theorem inverse_apply_cancel (A : E →L[ℝ] E) (hA : IsUnit A) (v : E) :
    Ring.inverse A (A v) = v := by
  exact congrArg (fun B : E →L[ℝ] E => B v) (Ring.inverse_mul_cancel A hA)

theorem apply_inverse_cancel (A : E →L[ℝ] E) (hA : IsUnit A) (v : E) :
    A (Ring.inverse A v) = v := by
  exact congrArg (fun B : E →L[ℝ] E => B v) (Ring.mul_inverse_cancel A hA)

theorem linearSolvedParameter_root (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hi : IsUnit (T i (q i))) :
    linearPerturbation f T (q i) (linearSolvedParameter f T i q) = 0 := by
  rw [linearPerturbation, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i, T j (q i) (linearSolvedParameter f T i q j)) =
      ∑ j ∈ Finset.univ.erase i, T j (q i) (q j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [linearSolvedParameter, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp only [linearSolvedParameter, Function.update_self, map_neg,
    apply_inverse_cancel _ hi]
  abel

variable [FiniteDimensional ℝ E]

theorem linearSolvedParameter_differentiableAt (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hf : DifferentiableAt ℝ f (q i))
    (hT : ∀ j, DifferentiableAt ℝ (T j) (q i)) (hi : IsUnit (T i (q i))) :
    DifferentiableAt ℝ (linearSolvedParameter f T i) q := by
  have hproj := differentiableAt_apply i q (𝕜 := ℝ)
  apply differentiableAt_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [linearSolvedParameter, Function.update_self]
    apply DifferentiableAt.neg
    apply DifferentiableAt.clm_apply
    · exact ((hT i).inverse hi).comp q hproj
    · exact (hf.comp q hproj).add (DifferentiableAt.fun_sum (fun k _ =>
        ((hT k).comp q hproj).clm_apply (differentiableAt_apply k q)))
  · simpa only [linearSolvedParameter_outside f T i j hj] using differentiableAt_apply j q (𝕜 := ℝ)

omit [FiniteDimensional ℝ E] in
theorem linearSolvedParameter_fderiv_outside (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i j : ι) (hji : j ≠ i) (q : ι → E)
    (hG : DifferentiableAt ℝ (linearSolvedParameter f T i) q) :
    (ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E).comp
      (fderiv ℝ (linearSolvedParameter f T i) q) = ContinuousLinearMap.proj j := by
  have h := ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt.comp q hG.hasFDerivAt
  have he : (ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E) ∘
      linearSolvedParameter f T i = fun q => q j :=
    linearSolvedParameter_outside f T i j hji
  rw [he] at h
  exact h.unique ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt

theorem linearSolvedParameter_differential_relation
    (f : E → E) (T : ι → E → (E →L[ℝ] E)) (i : ι) (q : ι → E)
    (hf : DifferentiableAt ℝ f (q i)) (hT : ∀ j, DifferentiableAt ℝ (T j) (q i))
    (hi : IsUnit (T i (q i))) (v : E) :
    linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q) v +
      ∑ j, T j (q i) ((fderiv ℝ (linearSolvedParameter f T i) q (Pi.single i v)) j) = 0 := by
  let G := linearSolvedParameter f T i
  have hG := linearSolvedParameter_differentiableAt f T i q hf hT hi
  have hfi := hf.hasFDerivAt.comp q ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)).hasFDerivAt
  have hx := hfi.fun_add (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hT j).hasFDerivAt.comp q ((ContinuousLinearMap.proj i : (ι → E) →L[ℝ] E)).hasFDerivAt).clm_apply
      (((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E)).hasFDerivAt.comp q hG.hasFDerivAt)))
  have hz : (fun t => linearPerturbation f T (t i) (G t)) =ᶠ[𝓝 q] fun _ => 0 := by
    have hcont : ContinuousAt (fun t : ι → E => T i (t i)) q :=
      ((hT i).comp q (differentiableAt_apply i q)).continuousAt
    have he : ∀ᶠ t in 𝓝 q, IsUnit (T i (t i)) :=
      hcont (Units.isOpen.mem_nhds hi)
    filter_upwards [he] with t ht
    exact linearSolvedParameter_root f T i t ht
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (0 : E) q).congr_of_eventuallyEq hz
  have he := congrArg (fun l : (ι → E) →L[ℝ] E => l (Pi.single i v)) (hx.unique hc)
  simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply,
    Pi.single_eq_same, zero_apply, Finset.sum_add_distrib] at he
  simp only [linearPerturbationDerivative, add_apply, sum_apply, ContinuousLinearMap.flip_apply]
  dsimp [G] at he
  exact (by convert he using 1; abel)

omit [FiniteDimensional ℝ E] in
theorem linearSolvedParameter_recovers_root (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (x : E) (p : ι → E) (hi : IsUnit (T i x))
    (hroot : linearPerturbation f T x p = 0) :
    linearSolvedParameter f T i (Function.update p i x) = p := by
  have he : (∑ j ∈ Finset.univ.erase i, T j x (Function.update p i x j)) =
      ∑ j ∈ Finset.univ.erase i, T j x (p j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hs : T i x (p i) = -(f x + ∑ j ∈ Finset.univ.erase i, T j x (p j)) := by
    rw [linearPerturbation, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← add_assoc] at hroot
    exact eq_neg_of_add_eq_zero_right hroot
  funext j
  by_cases hj : j = i
  · subst j
    simp only [linearSolvedParameter, Function.update_self, he]
    rw [← map_neg, ← hs, inverse_apply_cancel _ hi]
  · simp [linearSolvedParameter, Function.update_of_ne hj]

theorem linearSolvedParameter_critical (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (i : ι) (q : ι → E) (hf : DifferentiableAt ℝ f (q i))
    (hT : ∀ j, DifferentiableAt ℝ (T j) (q i)) (hi : IsUnit (T i (q i)))
    (hcrit : (linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q)).det = 0) :
    (fderiv ℝ (linearSolvedParameter f T i) q).det = 0 := by
  have hG := linearSolvedParameter_differentiableAt f T i q hf hT hi
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hcrit)
  change linearPerturbationDerivative f T (q i) (linearSolvedParameter f T i q) v = 0 at hv
  let w := fderiv ℝ (linearSolvedParameter f T i) q (Pi.single i v)
  have hw (j : ι) (hji : j ≠ i) : w j = 0 := by
    have he := congrArg (fun l : (ι → E) →L[ℝ] E => l (Pi.single i v))
      (linearSolvedParameter_fderiv_outside f T i j hji q hG)
    simpa [w, Pi.single_eq_of_ne hji] using he
  have hrel := linearSolvedParameter_differential_relation f T i q hf hT hi v
  rw [hv, zero_add] at hrel
  have hwi : w i = 0 := by
    have hs : (∑ j, T j (q i) (w j)) = T i (q i) (w i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hw j hji]
      · simp
    rw [hs] at hrel
    have he := congrArg (fun v => Ring.inverse (T i (q i)) v) hrel
    simpa only [inverse_apply_cancel _ hi, map_zero] using he
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨Pi.single i v, ?_, ?_⟩
  · change w = 0
    funext j
    by_cases hj : j = i
    · subst j; exact hwi
    · exact hw j hj
  · intro he
    apply hv0
    simpa using congrFun he i

/-- Transversality with source-dependent linear parameter blocks, including
finite equivariant bump perturbations. Only invertibility of a single active
block is required at each root. -/
theorem ae_regular_linear_parameters [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure (ι → E)) [μ.IsAddHaarMeasure]
    (f : E → E) (T : ι → E → (E →L[ℝ] E)) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hT : ∀ i x, x ∈ s → DifferentiableAt ℝ (T i) x) :
    ∀ᵐ p ∂μ, ∀ x ∈ s, linearPerturbation f T x p = 0 →
      (∃ i, IsUnit (T i x)) → (linearPerturbationDerivative f T x p).det ≠ 0 := by
  let C : ι → Set (ι → E) := fun i =>
    {q | q i ∈ s ∧ IsUnit (T i (q i)) ∧ (fderiv ℝ (linearSolvedParameter f T i) q).det = 0}
  have hnull (i : ι) : μ (linearSolvedParameter f T i '' C i) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    · intro q hq
      exact (linearSolvedParameter_differentiableAt f T i q (hf _ hq.1)
        (fun j => hT j _ hq.1) hq.2.1).hasFDerivAt.hasFDerivWithinAt
    · intro q hq
      exact hq.2.2
  have hae : ∀ᵐ p ∂μ, p ∉ ⋃ i, linearSolvedParameter f T i '' C i := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using MeasureTheory.measure_iUnion_null hnull
  filter_upwards [hae] with p hp
  intro x hs hx ⟨i, hi⟩ hcrit
  let q := Function.update p i x
  have hqi : q i = x := Function.update_self _ _ _
  have hGq : linearSolvedParameter f T i q = p :=
    linearSolvedParameter_recovers_root f T i x p hi hx
  apply hp
  apply Set.mem_iUnion.mpr
  refine ⟨i, q, ⟨?_, ?_, ?_⟩, hGq⟩
  · simpa only [hqi] using hs
  · simpa only [hqi] using hi
  · apply linearSolvedParameter_critical f T i q
        (by simpa only [hqi] using hf x hs)
        (fun j => by simpa only [hqi] using hT j x hs)
    · simpa only [hqi] using hi
    · simpa only [hqi, hGq] using hcrit

end LinearParameters
end EilenbergGanea
open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
section EquivariantBumps
variable {G E : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype G] in
theorem representation_cancel (ρ : G →* E ≃L[ℝ] E) (g : G) (x : E) :
    ρ g⁻¹ (ρ g x) = x := by
  change ((ρ g⁻¹) * ρ g) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

omit [Fintype G] in
theorem representation_mul_apply (ρ : G →* E ≃L[ℝ] E) (g h : G) (x : E) :
    ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl

theorem equivariantBumpOperator_equivariant (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (h : G) (x : E) :
    equivariantBumpOperator ρ b (ρ h x) =
      (ρ h : E →L[ℝ] E).comp (equivariantBumpOperator ρ b x) := by
  ext v
  simp only [equivariantBumpOperator, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul]
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft h)
  intro g
  change b (ρ g⁻¹ x) • ρ h (ρ g v) =
    b (ρ (h * g)⁻¹ (ρ h x)) • ρ (h * g) v
  simp only [mul_inv_rev, representation_mul_apply, representation_cancel]

theorem equivariantBumpOperator_contDiff (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (equivariantBumpOperator ρ b) := by
  apply ContDiff.sum
  intro g _
  exact (hb.comp (ρ g⁻¹).contDiff).smul contDiff_const

theorem unit_smul_equiv (a : ℝ) (ha : a ≠ 0) (e : E ≃L[ℝ] E) :
    IsUnit (a • (e : E →L[ℝ] E)) := by
  refine ⟨⟨a • (e : E →L[ℝ] E), a⁻¹ • (e.symm : E →L[ℝ] E), ?_, ?_⟩, rfl⟩
  · ext v
    simp [smul_smul, ha]
  · ext v
    simp [smul_smul, ha]

theorem equivariantBumpOperator_isUnit (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ)
    (hbd : Pairwise fun g h : G => Disjoint (ρ g '' tsupport b) (ρ h '' tsupport b))
    (x : E) (g : G) (hg : b (ρ g⁻¹ x) ≠ 0) : IsUnit (equivariantBumpOperator ρ b x) := by
  have hx (k : G) (hk : b (ρ k⁻¹ x) ≠ 0) : x ∈ ρ k '' tsupport b :=
    ⟨ρ k⁻¹ x, subset_tsupport b hk, by simpa using representation_cancel ρ k⁻¹ x⟩
  have he : equivariantBumpOperator ρ b x = b (ρ g⁻¹ x) • (ρ g : E →L[ℝ] E) := by
    apply Finset.sum_eq_single g
    · intro h _ hh
      have hh0 : b (ρ h⁻¹ x) = 0 := by
        by_contra hh0
        exact Set.disjoint_left.mp (hbd hh) (hx h hh0) (hx g hg)
      simp only [hh0, zero_smul]
    · simp
  rw [he]
  exact unit_smul_equiv _ hg _

/-- A free orbit for a finite linear action has a neighborhood with pairwise
disjoint translates. No isometry hypothesis or metric constants are needed. -/
theorem free_orbit_disjoint_neighborhood (ρ : G →* E ≃L[ℝ] E) (x : E)
    (hx : ∀ g : G, ρ g x = x → g = 1) (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧
      Pairwise fun g h : G => Disjoint (ρ g '' V) (ρ h '' V) := by
  classical
  have hsep (g : {g : G // g ≠ 1}) :
      ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ Disjoint U (ρ g.val '' U) := by
    have hgx : x ≠ ρ g.val x := fun he => g.property (hx _ he.symm)
    obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := t2_separation hgx
    refine ⟨A ∩ (ρ g.val ⁻¹' B), hA.inter (hB.preimage (ρ g.val).continuous), ⟨hxA, hxB⟩, ?_⟩
    apply hAB.mono inter_subset_left
    rintro y ⟨z, hz, rfl⟩
    exact hz.2
  choose U hU hxU hdU using hsep
  let V : Set E := W ∩ ⋂ g : {g : G // g ≠ 1}, U g
  have hVo : IsOpen V := hW.inter (isOpen_iInter_of_finite hU)
  have hxV : x ∈ V := ⟨hxW, mem_iInter.mpr hxU⟩
  refine ⟨V, hVo, hxV, inter_subset_left, ?_⟩
  intro g h hgh
  apply Set.disjoint_left.mpr
  rintro y ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
  have hk : g⁻¹ * h ≠ 1 := by
    intro heq
    apply hgh
    have := congrArg (fun k => g * k) heq
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using this.symm
  have haU : a ∈ U ⟨g⁻¹ * h, hk⟩ := mem_iInter.mp ha.2 _
  have hbU : b ∈ U ⟨g⁻¹ * h, hk⟩ := mem_iInter.mp hb.2 _
  apply Set.disjoint_left.mp (hdU ⟨g⁻¹ * h, hk⟩) haU
  refine ⟨b, hbU, ?_⟩
  rw [representation_mul_apply, he, representation_cancel]

variable [FiniteDimensional ℝ E]

/-- The bump family used in the free part of the localized-degree argument.
Its complete closed support has disjoint translates, so each active parameter
block is invertible. -/
theorem free_orbit_smooth_bump (ρ : G →* E ≃L[ℝ] E) (x : E)
    (hx : ∀ g : G, ρ g x = x → g = 1) (W : Set E) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ W ∧ b x = 1 ∧
      Pairwise fun g h : G => Disjoint (ρ g '' tsupport b) (ρ h '' tsupport b) := by
  obtain ⟨V, hV, hxV, hVW, hdisj⟩ := free_orbit_disjoint_neighborhood ρ x hx W hW hxW
  obtain ⟨b, hbV, hcb, hdb, _, hbx⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hV.mem_nhds hxV)
  refine ⟨b, hdb, hcb, hbV.trans hVW, hbx, ?_⟩
  intro g h hgh
  exact (hdisj hgh).mono (image_mono hbV) (image_mono hbV)

end EquivariantBumps
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section CompactRootStability
variable {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace X] [T1Space Y]

theorem compact_root_good_stability (f : P × X → Y) (hf : Continuous f)
    (y : Y) (V : Set (P × X)) (hV : IsOpen V) (p₀ : P)
    (h₀ : ∀ x, f (p₀, x) = y → (p₀, x) ∈ V) :
    ∀ᶠ p in 𝓝 p₀, ∀ x, f (p, x) = y → (p, x) ∈ V := by
  let C : Set (P × X) := {q | f q = y} ∩ Vᶜ
  have hC : IsClosed C := (isClosed_singleton.preimage hf).inter hV.isClosed_compl
  have hn : p₀ ∉ Prod.fst '' C := by
    rintro ⟨⟨p, x⟩, ⟨hr, hv⟩, rfl⟩
    exact hv (h₀ x hr)
  filter_upwards [(isClosedMap_fst_of_compactSpace _ hC).isOpen_compl.mem_nhds hn] with p hp
  intro x hr
  by_contra hv
  exact hp ⟨(p, x), ⟨hr, hv⟩, rfl⟩
end CompactRootStability

section CompactFreeBumps
universe uE uG
variable {G : Type uG} {E : Type uE} [Group G] [Fintype G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem compact_free_bump_family (ρ : G →* E ≃L[ℝ] E)
    (K W : Set E) (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hfree : ∀ x ∈ K, ∀ g : G, ρ g x = x → g = 1) :
    ∃ (ι : Type uE) (_ : Fintype ι) (b : ι → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧ tsupport (b i) ⊆ W ∧
        Pairwise fun g h : G => Disjoint (ρ g '' tsupport (b i)) (ρ h '' tsupport (b i))) ∧
      (∀ x ∈ K, ∃ i, IsUnit (equivariantBumpOperator ρ (b i) x)) := by
  classical
  have hb (x : K) := free_orbit_smooth_bump ρ x.val (hfree x.val x.property)
    W hW (hKW x.property)
  choose b hbd hbc hbs hbx hdis using hb
  have hcov : K ⊆ ⋃ x : K, {y | b x y ≠ 0} := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simp [hbx]⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => {y | b x y ≠ 0})
    (fun x => isOpen_ne_fun (hbd x).continuous continuous_const) hcov
  refine ⟨{x // x ∈ t}, inferInstance, fun i => b i.val, ?_, ?_⟩
  · exact fun i => ⟨hbd i.val, hbc i.val, hbs i.val, hdis i.val⟩
  · intro x hx
    obtain ⟨i, hi, hbix⟩ := Set.mem_iUnion₂.mp (ht hx)
    refine ⟨⟨i, hi⟩, equivariantBumpOperator_isUnit ρ (b i) (hdis i) x 1 ?_⟩
    rw [inv_one, map_one]
    exact hbix

end CompactFreeBumps

section LinearRegularization
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem linearPerturbation_contDiff (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i)) :
    ContDiff ℝ ∞ (fun q : (ι → E) × E => linearPerturbation f T q.2 q.1) := by
  apply (hf.comp contDiff_snd).add
  apply ContDiff.sum
  intro i _
  exact ((hT i).comp contDiff_snd).clm_apply ((contDiff_apply ℝ E i).comp contDiff_fst)

omit [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem linearPerturbationDerivative_continuous (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i)) :
    Continuous (fun q : (ι → E) × E => linearPerturbationDerivative f T q.2 q.1) := by
  apply (hf.continuous_fderiv (by norm_num)).comp continuous_snd |>.add
  apply continuous_finsetSum
  intro i _
  exact ((ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.comp
    (((hT i).continuous_fderiv (by norm_num)).comp continuous_snd)).clm_apply
    ((continuous_apply i).comp continuous_fst)

/-- A finite linear bump family regularizes all roots on a compact set, provided
it has an invertible block at every initially critical root. The parameters
can be chosen in any prescribed neighborhood of zero. -/
theorem exists_regular_linear_perturbation
    (μ : MeasureTheory.Measure (ι → E)) [μ.IsAddHaarMeasure]
    (f : E → E) (T : ι → E → (E →L[ℝ] E))
    (hf : ContDiff ℝ ∞ f) (hT : ∀ i, ContDiff ℝ ∞ (T i))
    (K : Set E) (hK : IsCompact K)
    (hcover : ∀ x ∈ K, f x = 0 → (fderiv ℝ f x).det = 0 → ∃ i, IsUnit (T i x))
    (U : Set (ι → E)) (hU : U ∈ 𝓝 0) :
    ∃ p ∈ U, ∀ x ∈ K, linearPerturbation f T x p = 0 →
      (linearPerturbationDerivative f T x p).det ≠ 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (ι → E) × K → E := fun q => linearPerturbation f T q.2.val q.1
  let V : Set ((ι → E) × K) := {q |
    (linearPerturbationDerivative f T q.2.val q.1).det ≠ 0 ∨ ∃ i, IsUnit (T i q.2.val)}
  have hc : Continuous (fun q : (ι → E) × K => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hV : IsOpen V := by
    have hd : IsOpen {q : (ι → E) × K |
        (linearPerturbationDerivative f T q.2.val q.1).det ≠ 0} :=
      isOpen_ne_fun (ContinuousLinearMap.continuous_det.comp
        ((linearPerturbationDerivative_continuous f T hf hT).comp hc)) continuous_const
    have ho := isOpen_iUnion (fun i => Units.isOpen.preimage ((hT i).continuous.comp
      (continuous_subtype_val.comp (continuous_snd : Continuous (Prod.snd : (ι → E) × K → K)))))
    have he : {q : (ι → E) × K | ∃ i, IsUnit (T i q.2.val)} =
        ⋃ i, (T i ∘ Subtype.val ∘ Prod.snd) ⁻¹' {a | IsUnit a} := by
      ext q
      simp
    have hi : IsOpen {q : (ι → E) × K | ∃ i, IsUnit (T i q.2.val)} := he ▸ ho
    exact hd.union hi
  have h₀ : ∀ x : K, F (0, x) = 0 → ((0 : ι → E), x) ∈ V := by
    intro x hx
    by_cases hd : (fderiv ℝ f x.val).det = 0
    · exact Or.inr (hcover x.val x.property (by simpa [F, linearPerturbation] using hx) hd)
    · exact Or.inl (by simpa [linearPerturbationDerivative] using hd)
  have he := compact_root_good_stability F ((linearPerturbation_contDiff f T hf hT).continuous.comp hc)
    0 V hV 0 h₀
  have hdense : Dense {p : ι → E | ∀ x ∈ K, linearPerturbation f T x p = 0 →
      (∃ i, IsUnit (T i x)) → (linearPerturbationDerivative f T x p).det ≠ 0} :=
    MeasureTheory.Measure.dense_of_ae (ae_regular_linear_parameters μ f T K
      (fun x _ => hf.differentiable (by norm_num) x)
      (fun i x _ => (hT i).differentiable (by norm_num) x))
  obtain ⟨p, hpreg, hpU, hpgood⟩ := hdense.inter_nhds_nonempty (inter_mem hU he)
  refine ⟨p, hpU, ?_⟩
  intro x hx hr
  rcases hpgood ⟨x, hx⟩ hr with hd | hi
  · exact hd
  · exact hpreg x hx hr hi

end LinearRegularization
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
section EquivariantRegularization
universe uE uG
variable {G : Type uG} {E : Type uE} [Group G] [Fintype G] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem equivariantBumpOperator_eventually_zero_outside
    (ρ : G →* E ≃L[ℝ] E) (b : E → ℝ) (W : Set E)
    (hb : tsupport b ⊆ W) (hinv : ∀ g x, x ∈ W → ρ g x ∈ W)
    (x : E) (hx : x ∉ W) : equivariantBumpOperator ρ b =ᶠ[𝓝 x] 0 := by
  have hzero (a : G) : ∀ᶠ y in 𝓝 x, b (ρ a⁻¹ y) = 0 := by
    have hn : ρ a⁻¹ x ∉ tsupport b := by
      intro hs
      have hw := hinv a (ρ a⁻¹ x) (hb hs)
      have he : ρ a (ρ a⁻¹ x) = x := by
        rw [← representation_mul_apply, mul_inv_cancel, map_one]
        rfl
      exact hx (he ▸ hw)
    filter_upwards [((isClosed_tsupport b).preimage (ρ a⁻¹).continuous).isOpen_compl.mem_nhds hn]
      with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  filter_upwards [Filter.eventually_all.mpr hzero] with y hy
  change (∑ a : G, b (ρ a⁻¹ y) • (ρ a : E →L[ℝ] E)) = 0
  apply Finset.sum_eq_zero
  intro a _
  rw [hy a, zero_smul]

/-- The free-action regularization step. Critical roots must lie in the free
locus, but already regular fixed roots need not. The perturbation is unchanged
outside any chosen invariant open neighborhood of the critical roots. -/
theorem exists_equivariant_regular_perturbation
    (ρ : G →* E ≃L[ℝ] E) (f : E → E) (hf : ContDiff ℝ ∞ f)
    (heq : ∀ g x, f (ρ g x) = ρ g (f x))
    (K W : Set E) (hK : IsCompact K) (hW : IsOpen W)
    (hinv : ∀ g x, x ∈ W → ρ g x ∈ W)
    (hcritical : ∀ x ∈ K, f x = 0 → (fderiv ℝ f x).det = 0 →
      x ∈ W ∧ ∀ g : G, ρ g x = x → g = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ a x, g (ρ a x) = ρ a (g x)) ∧
      (∀ x ∉ W, g =ᶠ[𝓝 x] f) ∧ (∀ x ∈ K, ‖g x - f x‖ < ε) ∧
      ∀ x ∈ K, g x = 0 → (fderiv ℝ g x).det ≠ 0 := by
  classical
  let A : Set E := {x ∈ K | f x = 0 ∧ (fderiv ℝ f x).det = 0}
  have hA : IsCompact A := hK.inter_right
    ((isClosed_singleton.preimage hf.continuous).inter
      (isClosed_singleton.preimage (ContinuousLinearMap.continuous_det.comp
        (hf.continuous_fderiv (by norm_num)))))
  obtain ⟨ι, hι, b, hb, hcover⟩ := compact_free_bump_family ρ A W hA hW
    (fun x hx => (hcritical x hx.1 hx.2.1 hx.2.2).1)
    (fun x hx => (hcritical x hx.1 hx.2.1 hx.2.2).2)
  let := hι
  let T : ι → E → (E →L[ℝ] E) := fun i => equivariantBumpOperator ρ (b i)
  have hT (i : ι) : ContDiff ℝ ∞ (T i) := equivariantBumpOperator_contDiff ρ _ (hb i).1
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : (ι → E) × K => (q.1, q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hopen : IsOpen {q : (ι → E) × K |
      ‖linearPerturbation f T q.2.val q.1 - f q.2.val‖ < ε} :=
    isOpen_lt (((linearPerturbation_contDiff f T hf hT).continuous.comp hc).sub
      (hf.continuous.comp (continuous_subtype_val.comp continuous_snd))).norm continuous_const
  have hsmall : ∀ᶠ p : ι → E in 𝓝 0,
      ∀ x : K, ‖linearPerturbation f T x.val p - f x.val‖ < ε := by
    have h := compact_root_good_stability (fun _ : (ι → E) × K => (0 : ℝ))
      continuous_const (0 : ℝ) _ hopen (0 : ι → E) (by
        intro x _
        simpa [linearPerturbation] using hε)
    filter_upwards [h] with p hp
    exact fun x => hp x rfl
  obtain ⟨p, hp, hreg⟩ := exists_regular_linear_perturbation
    (Module.finBasis ℝ (ι → E)).addHaar f T hf hT K hK
    (fun x hx hr hd => hcover x ⟨hx, hr, hd⟩) _ hsmall
  refine ⟨fun x => linearPerturbation f T x p, ?_, ?_, ?_, ?_, ?_⟩
  · exact (linearPerturbation_contDiff f T hf hT).comp (contDiff_const.prodMk contDiff_id)
  · intro a x
    simp only [linearPerturbation, heq, map_add, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun L : E →L[ℝ] E => L (p i)) (equivariantBumpOperator_equivariant ρ (b i) a x)
  · intro x hx
    have hz (i : ι) : T i =ᶠ[𝓝 x] 0 :=
      equivariantBumpOperator_eventually_zero_outside ρ (b i) W (hb i).2.2.1 hinv x hx
    filter_upwards [Filter.eventually_all.mpr hz] with y hy
    simp only [linearPerturbation, hy, Pi.zero_apply, zero_apply,
      Finset.sum_const_zero, add_zero]
  · intro x hx
    exact hp ⟨x, hx⟩
  · intro x hx hr
    rw [(linearPerturbation_hasFDerivAt f T (hf.differentiable (by norm_num) x)
      (fun i => (hT i).differentiable (by norm_num) x) p).fderiv]
    exact hreg x hx hr

end EquivariantRegularization
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section MixedRegularization
variable {G A V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
 theorem scalarRotation_free (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (q : A × V) (hq : q.2 ≠ 0) :
    ∀ g : G, scalarRotationRepresentation χ g q = q → g = 1 := by
  intro g hg
  have hh : (χ g : ℂ) • q.2 = (1 : ℂ) • q.2 := by
    have hg_snd := congrArg Prod.snd hg
    change (χ g : ℂ) • q.2 = q.2 at hg_snd
    simpa using hg_snd
  have he : (χ g : ℂ) = 1 := (smul_left_injective ℂ hq) hh
  apply hχ
  apply Units.ext
  simpa using he

omit [Fintype G] [FiniteDimensional ℝ A] [FiniteDimensional ℂ V] in
 theorem normalShift_equivariant (χ : G →* ℂˣ) (f : A × V → A × V)
    (hf : ∀ g q, f (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (f q)) (s : ℝ) :
    ∀ g q, normalShift f s (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (normalShift f s q) := by
  intro g q
  simp only [normalShift, hf, map_add, map_smul]
  congr 1

/-- The full fixed-plus-free regularization step in fixed/normal coordinates.
Unlike an assumed transversality interface, this is assembled from the finite
normal spectrum argument and explicit free-orbit bump parameters above. -/
theorem exists_fixed_free_regularization (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (a₀ : G) (ha₀ : (χ a₀ : ℂ).im ≠ 0)
    (f : A × V → A × V) (hf : ContDiff ℝ ∞ f)
    (he : ∀ g q, f (scalarRotationRepresentation χ g q) =
      scalarRotationRepresentation χ g (f q))
    (K : Set (A × V)) (hK : IsCompact K) (S : Finset A)
    (hS : ∀ a, (a, 0) ∈ K → f (a, 0) = 0 → a ∈ S)
    (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : A × V → A × V, ContDiff ℝ ∞ g ∧
      (∀ a q, g (scalarRotationRepresentation χ a q) =
        scalarRotationRepresentation χ a (g q)) ∧
      (∀ a, g (a, 0) = f (a, 0)) ∧
      (∀ q ∈ K, ‖g q - f q‖ < ε) ∧
      (∀ q ∈ K, g q = 0 → (fderiv ℝ g q).det ≠ 0) ∧
      (∀ a ∈ S, (0 < (fderiv ℝ g (a, 0)).det ↔ 0 < c)) := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  let : MeasurableSpace (A × V) := borel (A × V)
  let : BorelSpace (A × V) := ⟨rfl⟩
  let ρ := scalarRotationRepresentation (A := A) (V := V) χ
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  have hδ : 0 < (ε / 2) / (R + 1) := div_pos (by linarith) (by linarith)
  obtain ⟨s, hs, hreg⟩ := exists_normalShift_regular_fixed f
    (hf.differentiable (by simp)) (χ a₀) ha₀ (he a₀) S c hc hT _ hδ
  let f₁ := normalShift f s
  have hf₁ : ContDiff ℝ ∞ f₁ := normalShift_contDiff f hf s
  have he₁ : ∀ a q, f₁ (ρ a q) = ρ a (f₁ q) := normalShift_equivariant χ f he s
  have hsmall : ∀ q ∈ K, ‖f₁ q - f q‖ < ε / 2 := by
    intro q hq
    have hnorm : ‖normalProjection q‖ ≤ R + 1 := by
      simp only [normalProjection_apply, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
      exact (norm_snd_le q).trans (hbound q hq).le |>.trans (by linarith)
    calc
      ‖f₁ q - f q‖ = |s| * ‖normalProjection q‖ := by simp only [f₁, normalShift, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * (R + 1) := mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
      _ < ε / 2 := (lt_div_iff₀ (by linarith : 0 < R + 1)).mp hs
  let W : Set (A × V) := {q | q.2 ≠ 0}
  have hW : IsOpen W := (isClosed_singleton.preimage continuous_snd).isOpen_compl
  have hinv : ∀ a q, q ∈ W → ρ a q ∈ W := by
    intro a q hq
    exact smul_ne_zero (Units.ne_zero _) hq
  have hcritical : ∀ q ∈ K, f₁ q = 0 → (fderiv ℝ f₁ q).det = 0 →
      q ∈ W ∧ ∀ a : G, ρ a q = q → a = 1 := by
    intro q hq hr hd
    have hn : q.2 ≠ 0 := by
      intro hz
      have hqeq : q = (q.1, 0) := Prod.ext rfl hz
      rw [hqeq] at hq hr hd
      have ha : q.1 ∈ S := hS q.1 hq (by simpa [f₁] using hr)
      exact (hreg q.1 ha).1 hd
    exact ⟨hn, scalarRotation_free χ hχ q hn⟩
  obtain ⟨g, hg, hge, hprotected, hclose, hgood⟩ :=
    exists_equivariant_regular_perturbation ρ f₁ hf₁ he₁ K W hK hW hinv hcritical
      (ε / 2) (by linarith)
  refine ⟨g, hg, hge, ?_, ?_, hgood, ?_⟩
  · intro a
    exact ((hprotected (a, 0) (by simp [W])).eq_of_nhds).trans (normalShift_fixed f s a)
  · intro q hq
    have hh := norm_sub_le_norm_sub_add_norm_sub (g q) (f₁ q) (f q)
    linarith [hclose q hq, hsmall q hq]
  · intro a ha
    have hd := (hprotected (a, 0) (by simp [W])).fderiv_eq (𝕜 := ℝ)
    rw [hd]
    exact (hreg a ha).2

end MixedRegularization
end EilenbergGanea


namespace EilenbergGanea
section SignedAction
variable {G X : Type*} [Group G] [MulAction G X]

theorem signed_finite_action_nonzero {p : ℕ} [Fact p.Prime] [Fintype X]
    (hG : IsPGroup p G) (σ : X → Bool)
    (hσ : ∀ (g : G) x, σ (g • x) = σ x)
    (b : Bool) (hb : ∀ x ∈ MulAction.fixedPoints G X, σ x = b)
    (hex : (MulAction.fixedPoints G X).Nonempty)
    (hsmall : Nat.card (MulAction.fixedPoints G X) < p) :
    (∑ x : X, (if σ x then (1 : ℤ) else -1)) ≠ 0 := by
  classical
  let A := {x : X // σ x = b}
  let B := {x : X // σ x ≠ b}
  let : MulAction G A := invariantSubtypeAction _ (by intro g x hx; simpa [hσ] using hx)
  let : MulAction G B := invariantSubtypeAction _ (by intro g x hx; simpa [hσ] using hx)
  let e : MulAction.fixedPoints G A ≃ MulAction.fixedPoints G X :=
    { toFun := fun x => ⟨x.1.1, fun g => congrArg Subtype.val (x.2 g)⟩
      invFun := fun x => ⟨⟨x.1, hb x.1 x.2⟩, fun g => Subtype.ext (x.2 g)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  have hempty : IsEmpty (MulAction.fixedPoints G B) := ⟨by
    intro x
    have hx : x.1.1 ∈ MulAction.fixedPoints G X := fun g => congrArg Subtype.val (x.2 g)
    exact x.1.2 (hb x.1.1 hx)⟩
  have hnon : Nonempty (MulAction.fixedPoints G X) := hex.to_subtype
  have hpos : 0 < Nat.card (MulAction.fixedPoints G A) := by
    rw [Nat.card_congr e]
    exact Nat.card_pos
  have hs : Nat.card (MulAction.fixedPoints G A) < p := by rw [Nat.card_congr e]; exact hsmall
  have hn : Nat.card (MulAction.fixedPoints G B) = 0 := by simp
  have hneq : Nat.card A ≠ Nat.card B := by
    intro hh
    have h := (hG.card_modEq_card_fixedPoints A).symm
    rw [hh] at h
    have h' := h.trans (hG.card_modEq_card_fixedPoints B)
    rw [hn] at h'
    have heq := h'.eq_of_lt_of_lt hs (Fact.out : p.Prime).pos
    omega
  have hcounts : (∑ x : X, (if σ x = b then (1 : ℤ) else -1)) =
      (Nat.card A : ℤ) - Nat.card B := by
    rw [Finset.sum_ite]
    simp [A, B, Nat.card_eq_fintype_card, Fintype.card_subtype, sub_eq_add_neg]
  intro hz
  have hz' : (∑ x : X, (if σ x = b then (1 : ℤ) else -1)) = 0 := by
    cases b
    · have hh : (fun x : X => if σ x = false then (1 : ℤ) else -1) =
          fun x => -(if σ x then (1 : ℤ) else -1) := by funext x; cases σ x <;> rfl
      rw [hh, Finset.sum_neg_distrib, hz, neg_zero]
    · simpa using hz
  rw [hcounts, sub_eq_zero] at hz'
  exact hneq (by exact_mod_cast hz')
end SignedAction
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/- A nonsingular derivative supplies an open inverse patch, without assuming
that the map is proper or globally injective. -/
theorem exists_regular_inverse_patch (f : E → E) {x : E}
    (hf : ContDiffAt ℝ 1 f x) (hd : (fderiv ℝ f x).det ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ InjOn f V ∧
      IsOpen (f '' V) := by
  let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hd
  have he : (e : E →L[ℝ] E) = fderiv ℝ f x := rfl
  have hf' : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [he]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let p := hf.toOpenPartialHomeomorph f hf' (by norm_num)
  refine ⟨p.source, p.open_source, hf.mem_toOpenPartialHomeomorph_source hf' (by norm_num),
    p.injOn, ?_⟩
  change IsOpen (p '' p.source)
  rw [p.image_source_eq_target]
  exact p.open_target

/- A regular level set is discrete. Only smoothness at the level set is
required. -/
theorem regular_fiber_isDiscrete (f : E → E) (y : E) (K : Set E)
    (hf : ∀ x ∈ K, f x = y → ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ K, f x = y → (fderiv ℝ f x).det ≠ 0) :
    IsDiscrete (K ∩ f ⁻¹' {y}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro x ⟨hxK, hxy⟩
  obtain ⟨V, ho, hxV, hi, _⟩ := exists_regular_inverse_patch f (hf x hxK hxy) (hd x hxK hxy)
  refine ⟨V, ho, ?_⟩
  ext z
  constructor
  · rintro ⟨hzV, hzK, hzy⟩
    exact hi hzV hxV (hzy.trans hxy.symm)
  · rintro rfl
    exact ⟨hxV, hxK, hxy⟩

/- Compact regular fibers are finite, in the form needed by the signed
count formula after regularization. -/
theorem compact_regular_fiber_finite (f : E → E) (y : E) (K : Set E)
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hs : ∀ x ∈ K, f x = y → ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ K, f x = y → (fderiv ℝ f x).det ≠ 0) :
    (K ∩ f ⁻¹' {y}).Finite := by
  exact (hK.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hK.isClosed
    isClosed_singleton) inter_subset_left).finite
    (regular_fiber_isDiscrete f y K hs hd)


end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section LocalizedRegularization
variable {G A V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]

/-- The localized noncancellation part of degree, now for actual regular
perturbations of a smooth map, not an assumed finite-orbit-count interface. -/
theorem exists_regularization_nonzero_count {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (χ : G →* ℂˣ) (hχ : Function.Injective χ)
    (a₀ : G) (ha₀ : (χ a₀ : ℂ).im ≠ 0)
    (f : A × V → A × V) (hf : ContDiff ℝ ∞ f)
    (he : ∀ a q, f (scalarRotationRepresentation χ a q) =
      scalarRotationRepresentation χ a (f q))
    (K : Set (A × V)) (hK : IsCompact K)
    (hKi : ∀ a q, q ∈ K → scalarRotationRepresentation χ a q ∈ K)
    (L : Set (A × V)) (hL : IsCompact L) (hKL : K ⊆ L)
    (S : Finset A) (hS : ∀ a, (a, 0) ∈ L → f (a, 0) = 0 → a ∈ S)
    (hex : ∃ a, (a, 0) ∈ K ∧ f (a, 0) = 0) (hSp : S.card < p)
    (c : ℝ) (hc : c ≠ 0)
    (hT : ∀ a ∈ S, (fderiv ℝ (fixedRestriction f) a).det = c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : A × V → A × V, ContDiff ℝ ∞ g ∧
      (∀ q ∈ L, ‖g q - f q‖ < ε) ∧
      ∃ s : Finset (A × V), (∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0) ∧
        (∀ q ∈ s, (fderiv ℝ g q).det ≠ 0) ∧
        (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then 1 else -1 : ℝ)) ≠ 0 := by
  classical
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  let ρ := scalarRotationRepresentation (A := A) (V := V) χ
  obtain ⟨g, hg, hge, hgf, hclose, hreg, hsign⟩ := exists_fixed_free_regularization
    χ hχ a₀ ha₀ f hf he L hL S hS c hc hT ε hε
  have hfinite : (K ∩ g ⁻¹' {0}).Finite := compact_regular_fiber_finite g 0 K hK
    hg.continuous.continuousOn (fun q _ _ => hg.of_le (by norm_num) |>.contDiffAt) (fun q hq => hreg q (hKL hq))
  let s := hfinite.toFinset
  have hs : ∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0 := by intro q; exact hfinite.mem_toFinset
  let X := {q : A × V // q ∈ K ∧ g q = 0}
  let : Fintype X := hfinite.fintype
  let : MulAction G (A × V) := {
    smul := fun a q => ρ a q
    one_smul := by intro q; change ρ 1 q = q; rw [map_one]; rfl
    mul_smul := by intro a b q; change ρ (a * b) q = ρ a (ρ b q); rw [map_mul]; rfl }
  let : MulAction G X := invariantSubtypeAction _ (by
    intro a q hq
    refine ⟨hKi a q hq.1, ?_⟩
    change g (ρ a q) = 0
    rw [hge, hq.2, map_zero])
  have hfixed (x : MulAction.fixedPoints G X) : x.1.1.2 = 0 := by
    by_contra hn
    have hh := congrArg (fun q : X => q.1.2) (x.2 a₀)
    change (χ a₀ : ℂ) • x.1.1.2 = x.1.1.2 at hh
    have hh' : (χ a₀ : ℂ) • x.1.1.2 = (1 : ℂ) • x.1.1.2 := by simpa using hh
    have heq := (smul_left_injective ℂ hn) hh'
    exact ha₀ (by rw [heq]; rfl)
  have hmem (x : MulAction.fixedPoints G X) : x.1.1.1 ∈ S := by
    have hx := x.1.2
    have heq : x.1.1 = (x.1.1.1, 0) := Prod.ext rfl (hfixed x)
    rw [heq] at hx
    exact hS _ (hKL hx.1) (by rw [← hgf]; exact hx.2)
  let e : MulAction.fixedPoints G X ↪ S :=
    ⟨fun x => ⟨x.1.1.1, hmem x⟩, by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact (hfixed x).trans (hfixed y).symm⟩
  have hsmall : Nat.card (MulAction.fixedPoints G X) < p :=
    (Nat.card_le_card_of_injective e e.injective).trans_lt (by simpa using hSp)
  have hex' : (MulAction.fixedPoints G X).Nonempty := by
    obtain ⟨a, haK, haf⟩ := hex
    refine ⟨⟨(a, 0), haK, by rw [hgf]; exact haf⟩, ?_⟩
    intro b
    apply Subtype.ext
    change ρ b (a, 0) = (a, 0)
    simp [ρ]
  let σ : X → Bool := fun q => decide (0 < (fderiv ℝ g q.1).det)
  have hσ : ∀ (a : G) (q : X), σ (a • q) = σ q := by
    intro a q
    unfold σ
    congr 1
    exact congrArg (fun t : ℝ => 0 < t)
      (equivariant_fderiv_det g (ρ a) (hg.differentiable (by simp)) (hge a) q.1)
  have hb : ∀ q ∈ MulAction.fixedPoints G X, σ q = decide (0 < c) := by
    intro q hq
    let x : MulAction.fixedPoints G X := ⟨q, hq⟩
    have heq : q.1 = (q.1.1, 0) := Prod.ext rfl (hfixed x)
    change decide (0 < (fderiv ℝ g q.1).det) = decide (0 < c)
    rw [heq]
    exact decide_eq_decide.mpr (hsign _ (hmem x))
  have hcount := signed_finite_action_nonzero hG σ hσ (decide (0 < c)) hb hex' hsmall
  refine ⟨g, hg, hclose, s, hs, fun q hq => hreg q (hKL ((hs q).mp hq).1) ((hs q).mp hq).2, ?_⟩
  have hsum : (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1)) ≠ 0 := by
    have hsum' : (∑ q : X, (if σ q then (1 : ℤ) else -1)) =
        ∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1) := by
      unfold σ
      simpa only [decide_eq_true_eq] using (Finset.sum_subtype s hs
        (fun q => if 0 < (fderiv ℝ g q).det then (1 : ℤ) else -1)).symm
    exact hsum' ▸ hcount
  exact_mod_cast hsum
end LocalizedRegularization
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.UnitaryWords
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped Quaternion ContDiff

open scoped Quaternion
namespace EilenbergGanea

open Set Filter Topology
open scoped ContDiff

theorem normalizeQuaternion_coe_of_ne_zero {q : ℍ} (hq : q ≠ 0) :
    (normalizeQuaternion q : ℍ) = ‖q‖⁻¹ • q := by simp [normalizeQuaternion, hq]

theorem normalizeQuaternion_coe_contDiffAt {q : ℍ} (hq : q ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => (normalizeQuaternion z : ℍ)) q := by
  have h : ContDiffAt ℝ ∞ (fun z : ℍ => ‖z‖⁻¹ • z) q :=
    ((contDiffAt_norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul contDiffAt_id
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hq] with z hz
  exact normalizeQuaternion_coe_of_ne_zero hz

@[simp] theorem normalizeQuaternion_unitary (q : SU2) : normalizeQuaternion (q : ℍ) = q := by
  have hqnorm : ‖(q : ℍ)‖ = 1 := (quaternion_mem_unitary_iff _).mp q.property
  have hq : (q : ℍ) ≠ 0 := by intro he; simp [he] at hqnorm
  apply Subtype.ext
  simp [normalizeQuaternion_coe_of_ne_zero hq, hqnorm]

/-- Smoothness of coefficient-free word evaluation follows directly by
induction, using quaternion conjugation for unitary inverses. -/
theorem freeGroup_lift_coe_contDiffAt {D ι : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] (w : FreeGroup ι)
    (a : D) (x : D → ι → SU2)
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun z => (x z i : ℍ)) a) :
    ContDiffAt ℝ ∞ (fun z => ((FreeGroup.lift (x z) w : SU2) : ℍ)) a := by
  induction w using OAI.freeGroupInductionOn with
  | one => simpa using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : D => (1 : ℍ)) a)
  | of i => simpa using hx i
  | inv_of i hi =>
      simp only [map_inv]
      change ContDiffAt ℝ ∞ (fun z => star ((FreeGroup.lift (x z) (FreeGroup.of i) : SU2) : ℍ)) a
      let L : ℍ →ₗ[ℝ] ℍ :=
        { toFun := star
          map_add' := star_add
          map_smul' := Quaternion.star_smul }
      exact L.toContinuousLinearMap.contDiff.contDiffAt.comp a hi
  | mul v w hv hw => simpa only [map_mul, Submonoid.coe_mul] using hv.mul hw

theorem radialWordMap_contDiffAt {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (hx : ∀ i, x i ≠ 0) : ContDiffAt ℝ ∞ (radialWordMap w) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact ((contDiffAt_apply ℝ ℍ i x).norm ℝ (hx i)).smul
    (freeGroup_lift_coe_contDiffAt (w i) x (fun z j => normalizeQuaternion (z j))
      (fun j => (normalizeQuaternion_coe_contDiffAt (hx j)).comp (f := fun z : Fin m → ℍ => z j) x (contDiffAt_apply ℝ ℍ j x)))

theorem radialWordMap_eq_one_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : radialWordMap w x = 1 ↔
      (∀ i, ‖x i‖ = 1) ∧ wordMap w (fun j => normalizeQuaternion (x j)) = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : ‖x i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [radialWordMap_norm, Pi.one_apply, norm_one] using he
    refine ⟨hn, ?_⟩
    funext i
    apply Subtype.ext
    have he := congrFun h i
    simpa [radialWordMap, hn] using he
  · rintro ⟨hn, hw⟩
    funext i
    simp [radialWordMap, hn, hw]


theorem radialCutoff_contDiff {m : ℕ} : ContDiff ℝ ∞ (@radialCutoff m) := by
  apply contDiff_prod
  intro i _
  have hn : ContDiff ℝ ∞ (fun x : Fin m → ℍ => ‖x i‖ ^ 2) :=
    (contDiff_apply ℝ ℍ i).norm_sq ℝ
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul hn).sub contDiff_const)

theorem radialCutoff_nonneg {m : ℕ} (x : Fin m → ℍ) : 0 ≤ radialCutoff x :=
  Finset.prod_nonneg (fun _ _ => Real.smoothTransition.nonneg _)

theorem radialCutoff_le_one {m : ℕ} (x : Fin m → ℍ) : radialCutoff x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => Real.smoothTransition.nonneg _)
    (fun _ _ => Real.smoothTransition.le_one _)

theorem radialCutoff_eq_one {m : ℕ} (x : Fin m → ℍ) (hx : ∀ i, 1 ≤ ‖x i‖) :
    radialCutoff x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply Real.smoothTransition.one_of_one_le
  nlinarith [hx i]

theorem radialCutoff_eventually_zero {m : ℕ} (x : Fin m → ℍ) (i : Fin m)
    (hi : x i = 0) : radialCutoff =ᶠ[𝓝 x] (fun _ => 0) := by
  have h : ∀ᶠ y in 𝓝 x, ‖y i‖ < (1 / 2 : ℝ) :=
    ((continuous_apply i).norm.continuousAt.eventually_lt_const (by simp [hi]))
  filter_upwards [h] with y hy
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [norm_nonneg (y i)]

theorem radialCutoff_eventually_one {m : ℕ} (x : Fin m → ℍ)
    (hx : ∀ i, ‖x i‖ = 1) : radialCutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  have h (i : Fin m) : ∀ᶠ y in 𝓝 x, (3 / 4 : ℝ) < ‖y i‖ :=
    ((continuous_apply i).norm.continuousAt.eventually_const_lt (by change (3 / 4 : ℝ) < ‖x i‖; rw [hx i]; norm_num))
  filter_upwards [Filter.eventually_all.mpr h] with y hy
  apply Finset.prod_eq_one
  intro i _
  apply Real.smoothTransition.one_of_one_le
  nlinarith [hy i]

theorem smoothRadialWordMap_contDiff {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    ContDiff ℝ ∞ (smoothRadialWordMap w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ∀ i, x i ≠ 0
  · exact radialCutoff_contDiff.contDiffAt.smul (radialWordMap_contDiffAt w x hx)
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin m → ℍ => (0 : Fin m → ℍ)) x).congr_of_eventuallyEq
    filter_upwards [radialCutoff_eventually_zero x i hi] with y hy
    simp [smoothRadialWordMap, hy]

theorem smoothRadialWordMap_eq_one_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) : smoothRadialWordMap w x = 1 ↔ radialWordMap w x = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : radialCutoff x * ‖x i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [smoothRadialWordMap, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (radialCutoff_nonneg x), radialWordMap_norm, Pi.one_apply, norm_one] using he
    have hlarge (i : Fin m) : 1 ≤ ‖x i‖ := by
      have hle := mul_le_mul_of_nonneg_right (radialCutoff_le_one x) (norm_nonneg (x i))
      rw [hn i, one_mul] at hle
      exact hle
    simpa only [smoothRadialWordMap, radialCutoff_eq_one x hlarge, one_smul] using h
  · intro h
    have hn := (radialWordMap_eq_one_iff w x).mp h
    simp only [smoothRadialWordMap, radialCutoff_eq_one x (fun i => (hn.1 i).ge), one_smul, h]

theorem smoothRadialWordMap_eventuallyEq {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℍ) (hx : ∀ i, ‖x i‖ = 1) :
    smoothRadialWordMap w =ᶠ[𝓝 x] radialWordMap w := by
  filter_upwards [radialCutoff_eventually_one x hx] with y hy
  simp [smoothRadialWordMap, hy]

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem radialAngularLinear_det (B : Matrix n n ℝ) :
    (radialAngularLinear B).toLinearMap.det = B.det := by
  change LinearMap.det ((splitComplex (n := n)).symm.toLinearMap ∘ₗ
    ((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin') ∘ₗ
    (splitComplex (n := n)).toLinearMap) = _
  have he := LinearMap.det_conj
    ((LinearMap.id : (n → ℝ) →ₗ[ℝ] (n → ℝ)).prodMap B.toLin')
    (splitComplex (n := n)).symm
  rw [LinearEquiv.symm_symm] at he
  rw [he, LinearMap.det_prodMap, LinearMap.det_id, one_mul, LinearMap.det_toLin']

theorem normalize_complex_mul_exp (x z : ℂ) (hx : ‖x‖ = 1) :
    ‖x * Complex.exp z‖⁻¹ • (x * Complex.exp z) =
      x * Complex.exp ((z.im : ℂ) * Complex.I) := by
  rw [norm_mul, hx, one_mul, Complex.norm_exp, Complex.real_smul, Complex.ofReal_inv]
  have he : Complex.exp z = (Real.exp z.re : ℂ) *
      Complex.exp ((z.im : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
  rw [he]
  have hn : (Real.exp z.re : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero z.re
  field_simp

 theorem complexRadialTorus_chart (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, ‖x i‖ = 1) (hroot : ∀ i, ∏ j, x j ^ B i j = 1) :
    complexRadialTorus B ∘ complexPolarChart x =
      fun z => fun i => Complex.exp (radialAngularLinear (B.map (Int.castRingHom ℝ)) z i) := by
  funext z i
  have hn (j : n) := normalize_complex_mul_exp (x j) (z j) (hx j)
  simp only [Function.comp_apply, complexRadialTorus, complexPolarChart]
  simp only [hn]
  simp only [mul_zpow, Finset.prod_mul_distrib,
    hroot, one_mul, norm_mul, hx, one_mul, Complex.norm_exp, radialAngularLinear_apply,
    ← Complex.exp_int_mul]
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [Matrix.map_apply, Int.coe_castRingHom, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem complexDiagonal_det (x : n → ℂ) (hx : ∀ i, ‖x i‖ = 1) :
    (complexDiagonal x).toLinearMap.det = 1 := by
  change (((Matrix.diagonal x).toLin').restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.det_toLin',
    Matrix.det_diagonal]
  rw [Complex.normSq_eq_norm_sq, norm_prod]
  simp [hx]

theorem complexPolarChart_hasFDerivAt (x : n → ℂ) :
    HasFDerivAt (complexPolarChart x) (complexDiagonal x) 0 := by
  apply hasFDerivAt_pi'.mpr
  intro i
  have h := ((ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).hasFDerivAt
    (x := 0)).cexp.const_mul (x i)
  change HasFDerivAt (fun z : n → ℂ => x i * Complex.exp (z i)) _ (0 : n → ℂ)
  have he : (ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).comp (complexDiagonal x) =
      x i • (ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ) := by
    ext z
    simp
  rw [he]
  simpa using h

theorem exp_radialAngularLinear_hasFDerivAt (B : Matrix n n ℝ) :
    HasFDerivAt (fun z i => Complex.exp (radialAngularLinear B z i))
      (radialAngularLinear B) 0 := by
  apply hasFDerivAt_pi'.mpr
  intro i
  simpa using (((ContinuousLinearMap.proj i : (n → ℂ) →L[ℝ] ℂ).comp
    (radialAngularLinear B)).hasFDerivAt (x := 0)).cexp

theorem complexRadialTorus_differentiableAt (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, x i ≠ 0) : DifferentiableAt ℝ (complexRadialTorus B) x := by
  apply differentiableAt_pi.mpr
  intro i
  have hn (j : n) : DifferentiableAt ℝ (fun z : n → ℂ => ‖z j‖) x :=
    (differentiableAt_apply j x).norm ℝ (hx j)
  apply (hn i).smul
  have hp (j : n) : DifferentiableAt ℝ (fun z : n → ℂ => (‖z j‖⁻¹ • z j) ^ B i j) x := by
    have hne : ‖x j‖⁻¹ • x j ≠ 0 :=
      smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hx j))) (hx j)
    have hz : DifferentiableAt ℝ (fun z : ℂ => z ^ B i j) (‖x j‖⁻¹ • x j) :=
      ((differentiableAt_zpow (𝕜 := ℂ) (m := B i j)).mpr (Or.inl hne)).restrictScalars ℝ
    exact hz.comp x (((hn j).inv (norm_ne_zero_iff.mpr (hx j))).smul
      (differentiableAt_apply j x))
  exact (HasFDerivAt.finsetProd (fun j _ => (hp j).hasFDerivAt)).differentiableAt

/-- At every torus root, the radial extension has exactly determinant det B.
The extra radial coordinates contribute the identity, not an additional sign. -/
theorem complexRadialTorus_det (B : Matrix n n ℤ) (x : n → ℂ)
    (hx : ∀ i, ‖x i‖ = 1) (hroot : ∀ i, ∏ j, x j ^ B i j = 1) :
    (fderiv ℝ (complexRadialTorus B) x).det = (B.det : ℝ) := by
  have hne (i : n) : x i ≠ 0 := by intro h; simpa [h] using hx i
  have hd := (complexRadialTorus_differentiableAt B x hne).hasFDerivAt
  have hchart : complexPolarChart x 0 = x := by ext i; simp [complexPolarChart]
  have hc := (show HasFDerivAt (complexRadialTorus B) (fderiv ℝ (complexRadialTorus B) x)
      (complexPolarChart x 0) by rw [hchart]; exact hd).comp 0 (complexPolarChart_hasFDerivAt x)
  have he : (fderiv ℝ (complexRadialTorus B) x).comp (complexDiagonal x) =
      radialAngularLinear (B.map (Int.castRingHom ℝ)) := by
    apply hc.unique
    rw [complexRadialTorus_chart B x hx hroot]
    exact exp_radialAngularLinear_hasFDerivAt _
  have hdet := congrArg (fun L : (n → ℂ) →L[ℝ] (n → ℂ) => L.det) he
  change ((fderiv ℝ (complexRadialTorus B) x).toLinearMap.comp
    (complexDiagonal x).toLinearMap).det = (radialAngularLinear (B.map (Int.castRingHom ℝ))).toLinearMap.det at hdet
  rw [LinearMap.det_comp, complexDiagonal_det x hx,
    mul_one, radialAngularLinear_det] at hdet
  exact hdet.trans ((Int.castRingHom ℝ).map_det B).symm

end EilenbergGanea
namespace EilenbergGanea
section CommutativeWords
variable {n A : Type*} [Fintype n] [DecidableEq n] [CommGroup A]

theorem freeGroup_lift_commutative (x : n → A) (w : FreeGroup n) :
    FreeGroup.lift x w = ∏ j, x j ^ wordExponents w j := by
  induction w using OAI.freeGroupInductionOn with
  | one => simp
  | of i => simp
  | inv_of i hi => simp [hi, Finset.prod_inv_distrib]
  | mul a b ha hb => simp [ha, hb, zpow_add, Finset.prod_mul_distrib]

end CommutativeWords
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

theorem normalizeCircle_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    (normalizeCircle z : ℂ) = ‖z‖⁻¹ • z := by simp [normalizeCircle, hz]

theorem normalizeQuaternion_ofComplex (z : ℂ) :
    normalizeQuaternion (Quaternion.ofComplex z) = circleQuaternion (normalizeCircle z) := by
  by_cases hz : z = 0
  · subst z
    simp [normalizeQuaternion, normalizeCircle]
  · have hq : Quaternion.ofComplex z ≠ 0 := by
      intro h
      have hh := congrArg quaternionCoordinates h
      apply hz
      have hz0 := congrArg Prod.fst hh
      change (quaternionCoordinates (Quaternion.ofComplex z)).1 = (quaternionCoordinates (Quaternion.ofComplex 0)).1 at hz0
      simpa only [quaternionCoordinates_ofComplex] using hz0
    apply Subtype.ext
    rw [normalizeQuaternion_coe_of_ne_zero hq, circleQuaternion_coe,
      normalizeCircle_coe_of_ne_zero hz, norm_quaternion_ofComplex]
    exact (map_smul Quaternion.ofComplex (‖z‖⁻¹) z).symm

theorem wordMap_circleQuaternion {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (x : Fin m → Circle) :
    wordMap w (fun j => circleQuaternion (x j)) =
      fun i => circleQuaternion (∏ j, x j ^ exponentMatrix w i j) := by
  funext i
  have he : FreeGroup.lift (fun j => circleQuaternion (x j)) =
      circleQuaternion.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro j
    simp
  change FreeGroup.lift (fun j => circleQuaternion (x j)) (w i) = _
  rw [he, MonoidHom.comp_apply, freeGroup_lift_commutative]
  rfl

theorem radialWordMap_fixed {m : ℕ} (w : Fin m → FreeGroup (Fin m)) (z : Fin m → ℂ)
    (hz : ∀ i, z i ≠ 0) :
    radialWordMap w (fun i => Quaternion.ofComplex (z i)) =
      fun i => Quaternion.ofComplex (complexRadialTorus (exponentMatrix w) z i) := by
  funext i
  simp only [radialWordMap, normalizeQuaternion_ofComplex, wordMap_circleQuaternion,
    circleQuaternion_coe, complexRadialTorus, norm_quaternion_ofComplex]
  rw [map_smul]
  congr 1
  apply congrArg Quaternion.ofComplex
  change Circle.coeHom (∏ j, normalizeCircle (z j) ^ exponentMatrix w i j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change (normalizeCircle (z j) : ℂ) ^ exponentMatrix w i j = _
  rw [normalizeCircle_coe_of_ne_zero (hz j)]

theorem quaternionCoordinates_conjComplex (c : ℂ) (q : ℍ) :
    quaternionCoordinates (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
      ((Complex.normSq c : ℂ) * (quaternionCoordinates q).1,
        c ^ 2 * (quaternionCoordinates q).2) := by
  apply Prod.ext <;> apply Complex.ext <;>
    simp [quaternionCoordinates_apply, Complex.normSq_apply, pow_two] <;> ring

@[simp] theorem quaternionCoordinates_conjCircle (c : Circle) (q : ℍ) :
    quaternionCoordinates (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
      ((quaternionCoordinates q).1, (c : ℂ) ^ 2 * (quaternionCoordinates q).2) := by
  simpa using quaternionCoordinates_conjComplex (c : ℂ) q

theorem quaternionConjugate_smul (a : SU2) (r : ℝ) (q : ℍ) :
    quaternionConjugate a (r • q) = r • quaternionConjugate a q := by
  simp only [quaternionConjugate, mul_smul_comm, smul_mul_assoc]

theorem normalizeQuaternion_conjugate (a : SU2) (q : ℍ) :
    normalizeQuaternion (quaternionConjugate a q) = a * normalizeQuaternion q * a⁻¹ := by
  by_cases hq : q = 0
  · subst q; simp [normalizeQuaternion]
  · have hn : quaternionConjugate a q ≠ 0 := by
      intro hz
      have he := quaternionConjugate_norm a q
      rw [hz, norm_zero, eq_comm, norm_eq_zero] at he
      exact hq he
    apply Subtype.ext
    rw [normalizeQuaternion_coe_of_ne_zero hn, ← quaternionConjugate_coe,
      normalizeQuaternion_coe_of_ne_zero hq, quaternionConjugate_smul, quaternionConjugate_norm]

theorem wordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → SU2) :
    wordMap w (fun i => a * x i * a⁻¹) = fun i => a * wordMap w x i * a⁻¹ := by
  have he : FreeGroup.lift (fun i => a * x i * a⁻¹) =
      (MulAut.conj a).toMonoidHom.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  funext i
  change FreeGroup.lift (fun i => a * x i * a⁻¹) (w i) = _
  rw [he]
  rfl

theorem radialWordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → ℍ) :
    radialWordMap w (fun i => quaternionConjugate a (x i)) =
      fun i => quaternionConjugate a (radialWordMap w x i) := by
  funext i
  simp only [radialWordMap, quaternionConjugate_norm, normalizeQuaternion_conjugate,
    wordMap_conjugation, quaternionConjugate_smul, quaternionConjugate_coe]

theorem smoothRadialWordMap_conjugation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (a : SU2) (x : Fin m → ℍ) :
    smoothRadialWordMap w (fun i => quaternionConjugate a (x i)) =
      fun i => quaternionConjugate a (smoothRadialWordMap w x i) := by
  funext i
  simp only [smoothRadialWordMap, radialCutoff, quaternionConjugate_norm,
    Pi.smul_apply, radialWordMap_conjugation, quaternionConjugate_smul]

end EilenbergGanea


namespace EilenbergGanea

theorem complex_root_of_unity_norm {p : ℕ} (hp : p ≠ 0) (z : rootsOfUnity p ℂ) :
    ‖((z : ℂˣ) : ℂ)‖ = 1 := by
  have h := congrArg norm ((mem_rootsOfUnity' p (z : ℂˣ)).mp z.property)
  simpa only [norm_pow, norm_one, pow_eq_one_iff_of_nonneg (norm_nonneg _) hp] using h

theorem rootsOfUnity_isPGroup {p : ℕ} [Fact p.Prime] : IsPGroup p (rootsOfUnity p ℂ) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [isPGroup_iff_card_dvd_pow, Complex.card_rootsOfUnity]
  exact ⟨1, by simp⟩

theorem rootsOfUnity_exists_nonreal {p : ℕ} (hp : 2 < p) :
    ∃ z : rootsOfUnity p ℂ, (((z : ℂˣ) : ℂ)).im ≠ 0 := by
  have hp0 : p ≠ 0 := by omega
  let ζ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp0
  let u : ℂˣ := Units.mk0 ζ (Complex.exp_ne_zero _)
  let z : rootsOfUnity p ℂ := ⟨u, (mem_rootsOfUnity' p u).mpr hζ.pow_eq_one⟩
  refine ⟨z, ?_⟩
  intro him
  change ζ.im = 0 at him
  have hn : ‖ζ‖ = 1 := complex_root_of_unity_norm hp0 z
  have hs : ζ.re ^ 2 = 1 := by
    have hh := Complex.normSq_eq_norm_sq ζ
    simp only [Complex.normSq_apply, him, mul_zero, add_zero, hn, one_pow] at hh
    nlinarith
  have hpow : ζ ^ 2 = 1 := by
    apply Complex.ext <;> simp [pow_two, him]
    nlinarith
  have hd := hζ.dvd_of_pow_eq_one 2 hpow
  have ht := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

theorem circle_exists_square_root (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ c : Circle, (c : ℂ) ^ 2 = z := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0 < 2)
  have hn : ‖c‖ = 1 := by
    have hh := congrArg norm hc
    rw [norm_pow, hz] at hh
    nlinarith [norm_nonneg c]
  exact ⟨⟨c, mem_sphere_zero_iff_norm.mpr hn⟩, hc⟩

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

theorem splitWordMap_contDiff {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    ContDiff ℝ ∞ (splitWordMap w) :=
  (quaternionTupleCoordinates.contDiff.comp ((smoothRadialWordMap_contDiff w).comp
    quaternionTupleCoordinates.symm.contDiff)).sub contDiff_const

theorem quaternionTupleCoordinates_conjCircle {m : ℕ} (c : Circle) (q : Fin m → ℍ) :
    quaternionTupleCoordinates (fun i => quaternionConjugate (circleQuaternion c) (q i)) =
      ((quaternionTupleCoordinates q).1, (c : ℂ) ^ 2 • (quaternionTupleCoordinates q).2) := by
  apply Prod.ext
  · funext i
    change (quaternionCoordinates (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).1 = _
    have hh := congrArg Prod.fst (quaternionCoordinates_conjCircle c (q i))
    exact hh
  · funext i
    change (quaternionCoordinates (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).2 = _
    have hh := congrArg Prod.snd (quaternionCoordinates_conjCircle c (q i))
    exact hh

theorem splitWordMap_rotation {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (z : ℂ) (hz : ‖z‖ = 1) (q : (Fin m → ℂ) × (Fin m → ℂ)) :
    splitWordMap w (q.1, z • q.2) = ((splitWordMap w q).1, z • (splitWordMap w q).2) := by
  obtain ⟨c, hc⟩ := circle_exists_square_root z hz
  let x := quaternionTupleCoordinates.symm q
  have hx : quaternionTupleCoordinates x = q := quaternionTupleCoordinates.apply_symm_apply q
  have heq : (q.1, z • q.2) = quaternionTupleCoordinates
      (fun i => quaternionConjugate (circleQuaternion c) (x i)) := by
    rw [quaternionTupleCoordinates_conjCircle, hc, hx]
  have hh := congrArg (fun v : Fin m → ℍ => quaternionTupleCoordinates v)
    (smoothRadialWordMap_conjugation w (circleQuaternion c) x)
  rw [quaternionTupleCoordinates_conjCircle, hc] at hh
  have heq' : quaternionTupleCoordinates.symm (q.1, z • q.2) =
      fun i => quaternionConjugate (circleQuaternion c) (x i) := by
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  unfold splitWordMap
  rw [heq', hh]
  change (_, z • _) - (1, 0) = ((quaternionTupleCoordinates (smoothRadialWordMap w x) - (1, 0)).1,
    z • (quaternionTupleCoordinates (smoothRadialWordMap w x) - (1, 0)).2)
  simp

theorem splitWordMap_fixed_eventually {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℂ) (hx : ∀ i, ‖x i‖ = 1) :
    (fun z => (splitWordMap w (z, 0)).1) =ᶠ[𝓝 x]
      (fun z => complexRadialTorus (exponentMatrix w) z - 1) := by
  have hne (i : Fin m) : x i ≠ 0 := by intro h; simpa [h] using hx i
  have hz : ∀ᶠ z in 𝓝 x, ∀ i, z i ≠ 0 := Filter.eventually_all.mpr
    (fun i => (continuous_apply i).continuousAt.eventually_ne (hne i))
  have hcont : Continuous (fun z : Fin m → ℂ => fun i => Quaternion.ofComplex (z i)) :=
    continuous_pi (fun i => Quaternion.ofComplex.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_apply i))
  have he := (smoothRadialWordMap_eventuallyEq w (fun i => Quaternion.ofComplex (x i))
    (fun i => (norm_quaternion_ofComplex _).trans (hx i))).comp_tendsto hcont.continuousAt
  filter_upwards [hz, he] with z hz he
  change smoothRadialWordMap w (fun i => Quaternion.ofComplex (z i)) =
    radialWordMap w (fun i => Quaternion.ofComplex (z i)) at he
  simp only [splitWordMap, quaternionTupleCoordinates_symm_fixed]
  rw [he, radialWordMap_fixed w z hz, quaternionTupleCoordinates_fixed]
  rfl

theorem splitWordMap_fixed_det {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (x : Fin m → ℂ) (hx : ∀ i, ‖x i‖ = 1)
    (hr : ∀ i, ∏ j, x j ^ exponentMatrix w i j = 1) :
    (fderiv ℝ (fun z => (splitWordMap w (z, 0)).1) x).det =
      ((exponentMatrix w).det : ℝ) := by
  rw [(splitWordMap_fixed_eventually w x hx).fderiv_eq (𝕜 := ℝ)]
  have hne (i : Fin m) : x i ≠ 0 := by intro h; simpa [h] using hx i
  rw [((complexRadialTorus_differentiableAt (exponentMatrix w) x hne).hasFDerivAt.sub_const 1).fderiv]
  exact complexRadialTorus_det (exponentMatrix w) x hx hr

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion

theorem splitWordMap_zero_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (q : (Fin m → ℂ) × (Fin m → ℂ)) :
    splitWordMap w q = 0 ↔
      smoothRadialWordMap w (quaternionTupleCoordinates.symm q) = 1 := by
  unfold splitWordMap
  rw [sub_eq_zero]
  have he : quaternionTupleCoordinates (1 : Fin m → ℍ) = (1, 0) := by
    change quaternionTupleCoordinates (fun i : Fin m => Quaternion.ofComplex (1 : ℂ)) = _
    exact quaternionTupleCoordinates_fixed 1
  rw [← he]
  exact quaternionTupleCoordinates.injective.eq_iff

theorem splitWordMap_fixed_zero_iff {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (z : Fin m → ℂ) : splitWordMap w (z, 0) = 0 ↔
      (∀ i, ‖z i‖ = 1) ∧ (∀ i, ∏ j, z j ^ exponentMatrix w i j = 1) := by
  rw [splitWordMap_zero_iff, quaternionTupleCoordinates_symm_fixed,
    smoothRadialWordMap_eq_one_iff]
  constructor
  · intro h
    have hn : ∀ i, ‖z i‖ = 1 := fun i => (norm_quaternion_ofComplex (z i)).symm.trans
      (((radialWordMap_eq_one_iff w _).mp h).1 i)
    have hz (i : Fin m) : z i ≠ 0 := by intro h; simpa [h] using hn i
    rw [radialWordMap_fixed w z hz] at h
    refine ⟨hn, fun i => ?_⟩
    have hh := congrArg (fun v : Fin m → ℍ => (quaternionCoordinates (v i)).1) h
    change (quaternionCoordinates (Quaternion.ofComplex _)).1 = (1 : ℂ) at hh
    simpa only [quaternionCoordinates_ofComplex, complexRadialTorus, hn, inv_one, one_smul] using hh
  · rintro ⟨hn, hr⟩
    have hz (i : Fin m) : z i ≠ 0 := by intro h; simpa [h] using hn i
    rw [radialWordMap_fixed w z hz]
    funext i
    simp [complexRadialTorus, hn, hr]

@[simp] theorem splitWordMap_fixed_one {m : ℕ} (w : Fin m → FreeGroup (Fin m)) :
    splitWordMap w (1, 0) = 0 := by
  rw [splitWordMap_fixed_zero_iff]
  simp

end EilenbergGanea

namespace EilenbergGanea
open Set
section Torus
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [CommGroup A]
theorem zpow_finite_sum {ι : Type*} (a : A) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ i ∈ s, e i) = ∏ i ∈ s, a ^ e i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add]

omit [DecidableEq n] in
theorem torusMap_comp (B C : Matrix n n ℤ) (x : n → A) :
    torusMap B (torusMap C x) = torusMap (B * C) x := by
  funext i
  simp only [torusMap, Matrix.mul_apply, ← Finset.prod_zpow, zpow_finite_sum, ← zpow_mul]
  rw [Finset.prod_comm]
  congr 1
  funext j
  congr 1
  funext k
  rw [Int.mul_comm]

theorem torusMap_det_one (B : Matrix n n ℤ) (x : n → A) :
    torusMap (B.det • (1 : Matrix n n ℤ)) x = fun i => x i ^ B.det := by
  funext i
  simp [torusMap, Matrix.one_apply]

theorem torusMap_kernel_pow_det (B : Matrix n n ℤ) (x : n → A)
    (hx : torusMap B x = 1) (i : n) : x i ^ B.det = 1 := by
  have he := congrArg (fun y => torusMap B.adjugate y i) hx
  rw [torusMap_comp, Matrix.adjugate_mul, torusMap_det_one] at he
  simpa [torusMap] using he

theorem circle_finite_pow_roots {d : ℤ} (hd : d ≠ 0) :
    {z : Circle | z ^ d = 1}.Finite := by
  have hr := Polynomial.finite_setOfPred_isRoot
    (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hd)) (1 : ℂ))
  apply Set.Finite.of_injOn (f := fun z : Circle => (z : ℂ)) _
    Subtype.val_injective.injOn hr
  intro z hz
  have hp : z ^ d.natAbs = 1 := pow_natAbs_eq_one.mpr hz
  have he : (z : ℂ) ^ d.natAbs = 1 := by
    simpa using congrArg (fun t : Circle => (t : ℂ)) hp
  simpa [Polynomial.IsRoot.def] using sub_eq_zero.mpr he

theorem torusMap_finite_kernel (B : Matrix n n ℤ) (hB : B.det ≠ 0) :
    {x : n → Circle | torusMap B x = 1}.Finite := by
  apply Set.Finite.subset (Set.Finite.pi (fun _ : n => circle_finite_pow_roots hB))
  intro x hx i _
  exact torusMap_kernel_pow_det B x hx i

end Torus
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology

theorem splitWordMap_fixed_finite {m : ℕ} (w : Fin m → FreeGroup (Fin m))
    (hB : (exponentMatrix w).det ≠ 0) :
    {z : Fin m → ℂ | splitWordMap w (z, 0) = 0}.Finite := by
  classical
  let e : (Fin m → Circle) → (Fin m → ℂ) := fun x i => (x i : ℂ)
  have hf := (torusMap_finite_kernel (exponentMatrix w) hB).image e
  apply hf.subset
  intro z hz
  obtain ⟨hn, hr⟩ := (splitWordMap_fixed_zero_iff w z).mp hz
  let x : Fin m → Circle := fun i => ⟨z i, mem_sphere_zero_iff_norm.mpr (hn i)⟩
  refine ⟨x, ?_, rfl⟩
  funext i
  apply Subtype.ext
  change Circle.coeHom (∏ j, x j ^ exponentMatrix w i j) = (1 : ℂ)
  rw [map_prod]
  simp only [map_zpow]
  exact hr i

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

/-- The signed-root noncancellation for the actual ambient quaternion word
map, with no regularity assumed of the original word map. -/
theorem word_exists_regularization_nonzero_count {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (K : Set ((Fin m → ℂ) × (Fin m → ℂ))) (hK : IsCompact K)
    (hKi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ K, (q.1, z • q.2) ∈ K)
    (h1 : (1, 0) ∈ K)
    (L : Set ((Fin m → ℂ) × (Fin m → ℂ))) (hL : IsCompact L) (hKL : K ⊆ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)),
      ContDiff ℝ ∞ g ∧ (∀ q ∈ L, ‖g q - splitWordMap w q‖ < ε) ∧
      ∃ s : Finset ((Fin m → ℂ) × (Fin m → ℂ)),
        (∀ q, q ∈ s ↔ q ∈ K ∧ g q = 0) ∧
        (∀ q ∈ s, (fderiv ℝ g q).det ≠ 0) ∧
        (∑ q ∈ s, (if 0 < (fderiv ℝ g q).det then 1 else -1 : ℝ)) ≠ 0 := by
  classical
  let S := (splitWordMap_fixed_finite w hB).toFinset
  have hS (z) : z ∈ S ↔ splitWordMap w (z, 0) = 0 := (splitWordMap_fixed_finite w hB).mem_toFinset
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (S.card + 3)
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fintype (rootsOfUnity p ℂ) := Fintype.ofFinite _
  obtain ⟨a₀, ha₀⟩ := rootsOfUnity_exists_nonreal (p := p) (by omega)
  let χ : rootsOfUnity p ℂ →* ℂˣ := (rootsOfUnity p ℂ).subtype
  apply exists_regularization_nonzero_count (rootsOfUnity_isPGroup (p := p)) χ
    Subtype.val_injective a₀ ha₀ (splitWordMap w) (splitWordMap_contDiff w)
    (fun a q => splitWordMap_rotation w (χ a : ℂ) (complex_root_of_unity_norm hp.ne_zero a) q)
    K hK (fun a q hq => hKi (χ a : ℂ) (complex_root_of_unity_norm hp.ne_zero a) q hq)
    L hL hKL S (fun z _ hz => (hS z).mpr hz) ⟨1, h1, splitWordMap_fixed_one w⟩ (by omega)
    ((exponentMatrix w).det : ℝ) (by exact_mod_cast hB) _ ε hε
  intro z hz
  obtain ⟨hn, hr⟩ := (splitWordMap_fixed_zero_iff w z).mp ((hS z).mp hz)
  exact splitWordMap_fixed_det w z hn hr

end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.IntegralDegree
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
/- Avoidance of an arbitrary open boundary makes the selected fiber
compact whenever the closure of the open set is compact. -/
theorem exists_constant_jacobian_sign_patch (f : E → E) {x : E}
    (hf : ContDiff ℝ 1 f) (hd : (fderiv ℝ f x).det ≠ 0) (W : Set E)
    (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ InjOn f V ∧ IsOpen (f '' V) ∧
      ∀ z ∈ V, (fderiv ℝ f z).det =
        (if 0 < (fderiv ℝ f x).det then 1 else -1) * |(fderiv ℝ f z).det| := by
  let d : E → ℝ := fun z => (fderiv ℝ f z).det
  have hc : Continuous d := ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  let e := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hd
  have hf' : HasFDerivAt f (e : E →L[ℝ] E) x :=
    (hf.differentiable (by norm_num) x).hasFDerivAt
  let p := hf.contDiffAt.toOpenPartialHomeomorph f hf' (by norm_num)
  have hxP : x ∈ p.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hf' (by norm_num)
  let A : Set E := if 0 < d x then {z | 0 < d z} else {z | d z < 0}
  have hA : IsOpen A := by
    dsimp [A]
    split_ifs
    · exact isOpen_lt continuous_const hc
    · exact isOpen_lt hc continuous_const
  have hxA : x ∈ A := by
    dsimp [A]
    split_ifs with hp
    · exact hp
    · exact lt_of_le_of_ne (le_of_not_gt hp) hd
  let V := W ∩ p.source ∩ A
  have hV : IsOpen V := (hW.inter p.open_source).inter hA
  refine ⟨V, hV, ⟨⟨hxW, hxP⟩, hxA⟩, fun _ h => h.1.1,
    p.injOn.mono (fun _ h => h.1.2), ?_, ?_⟩
  · exact p.isOpen_image_of_subset_source hV (fun _ h => h.1.2)
  · intro z hz
    have hzA := hz.2
    dsimp [A] at hzA
    split_ifs at hzA ⊢ with hp
    · change 0 < (fderiv ℝ f z).det at hzA
      simp [abs_of_pos hzA]
    · change (fderiv ℝ f z).det < 0 at hzA
      simp [abs_of_neg hzA]

/- Finitely many regular roots admit pairwise disjoint inverse neighborhoods,
all contained in the prescribed isolating open set. -/
theorem disjoint_regular_inverse_patches (f : E → E) (hf : ContDiff ℝ 1 f)
    (U : Set E) (hU : IsOpen U) (S : Set E) (hS : S.Finite)
    (hSU : S ⊆ U) (hd : ∀ x ∈ S, (fderiv ℝ f x).det ≠ 0) :
    ∃ V : S → Set E,
      (∀ x, IsOpen (V x) ∧ (x : E) ∈ V x ∧ V x ⊆ U ∧ InjOn f (V x) ∧
        IsOpen (f '' V x) ∧ ∀ z ∈ V x, (fderiv ℝ f z).det =
          (if 0 < (fderiv ℝ f x).det then 1 else -1) * |(fderiv ℝ f z).det|) ∧
      Pairwise (fun x y => Disjoint (V x) (V y)) := by
  classical
  obtain ⟨W, hW, hdisj⟩ := hS.t2_separation
  have hp (x : S) := exists_constant_jacobian_sign_patch f hf (hd x x.property)
    (U ∩ W x) (hU.inter (hW x).2) ⟨hSU x.property, (hW x).1⟩
  choose V hopen hmem hsub hinj himg hsign using hp
  refine ⟨V, fun x => ⟨hopen x, hmem x, fun _ h => (hsub x h).1,
    hinj x, himg x, hsign x⟩, ?_⟩
  intro x y hxy
  exact (hdisj x.property y.property (fun he => hxy (Subtype.ext he))).mono
    (fun _ h => (hsub x h).2) (fun _ h => (hsub y h).2)

/- Compactness shrinks the target neighborhood so that all selected
preimages remain in the chosen inverse patches. It does not assert a
smooth boundary or a proper global map. -/
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem exists_target_neighborhood_of_patches {ι : Type*} [Fintype ι]
    (f : E → E) (y : E) (U : Set E) (hU : IsOpen U)
    (hc : IsCompact (closure U)) (hf : ContinuousOn f (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) (V : ι → Set E)
    (hV : ∀ i, IsOpen (V i)) (himg : ∀ i, IsOpen (f '' V i))
    (hy : ∀ i, y ∈ f '' V i)
    (hcover : ∀ x ∈ U, f x = y → ∃ i, x ∈ V i) :
    ∃ N : Set E, IsOpen N ∧ y ∈ N ∧ (∀ i, N ⊆ f '' V i) ∧
      ∀ x ∈ U, f x ∈ N → ∃ i, x ∈ V i := by
  let K := closure U \ ⋃ i, V i
  have hK : IsCompact K := hc.diff (isOpen_iUnion hV)
  have hclosed : IsClosed (f '' K) := (hK.image_of_continuousOn
    (hf.mono (fun _ h => h.1))).isClosed
  have hyK : y ∉ f '' K := by
    rintro ⟨x, ⟨hxcl, hxV⟩, hxy⟩
    have hxU : x ∈ U := by
      by_contra hn
      exact hb x ⟨hxcl, by simpa only [hU.interior_eq] using hn⟩ hxy
    obtain ⟨i, hi⟩ := hcover x hxU hxy
    exact hxV (mem_iUnion.mpr ⟨i, hi⟩)
  refine ⟨(f '' K)ᶜ ∩ ⋂ i, f '' V i,
    hclosed.isOpen_compl.inter (isOpen_iInter_of_finite himg),
    ⟨hyK, mem_iInter.mpr hy⟩, ?_, ?_⟩
  · intro i z hz
    exact mem_iInter.mp hz.2 i
  · intro x hxU hxN
    by_contra hn
    apply hxN.1
    refine ⟨x, ⟨subset_closure hxU, ?_⟩, rfl⟩
    simpa only [mem_iUnion] using hn

end EilenbergGanea

open Set MeasureTheory
namespace EilenbergGanea
section SignedIntegralDegree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/- The integral representative of local degree against a target bump. -/
theorem jacobianIntegral_of_injOn (f : E → E) (U : Set E) (hU : MeasurableSet U)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : InjOn f U)
    (ρ : E → ℝ) (σ : ℝ) (hσ : ∀ x ∈ U,
      (fderiv ℝ f x).det = σ * |(fderiv ℝ f x).det|) :
    jacobianIntegral μ f U ρ = σ * ∫ y in f '' U, ρ y ∂μ := by
  have hc := integral_image_eq_integral_abs_det_fderiv_smul μ hU
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj ρ
  rw [jacobianIntegral, hc, ← integral_const_mul]
  apply setIntegral_congr_fun hU
  intro x hx
  dsimp only
  calc
    _ = (σ * |(fderiv ℝ f x).det|) * ρ (f x) := congrArg (· * ρ (f x)) (hσ x hx)
    _ = _ := by simp only [smul_eq_mul, mul_assoc]

/- If the normalized target bump is supported inside an inverse patch, the
patch contributes exactly the sign of its Jacobian. -/
theorem jacobianIntegral_inverse_patch (f : E → E) (U : Set E) (hU : MeasurableSet U)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : InjOn f U)
    (ρ : E → ℝ) (σ : ℝ) (hσ : ∀ x ∈ U,
      (fderiv ℝ f x).det = σ * |(fderiv ℝ f x).det|)
    (hsupp : Function.support ρ ⊆ f '' U) (hunit : ∫ y, ρ y ∂μ = 1) :
    jacobianIntegral μ f U ρ = σ := by
  rw [jacobianIntegral_of_injOn μ f U hU hf hinj ρ σ hσ]
  have he : (∫ y in f '' U, ρ y ∂μ) = ∫ y, ρ y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_contra hn
    exact hy (hsupp hn)
  rw [he, hunit, mul_one]

/- Excision and finite additivity of the analytic degree representative. -/
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem jacobianIntegral_sum_patches {ι : Type*} [Fintype ι]
    (f : E → E) (U : Set E) (hU : MeasurableSet U) (V : ι → Set E)
    (hV : ∀ i, MeasurableSet (V i)) (hsub : ∀ i, V i ⊆ U)
    (hdisj : Pairwise (fun i j => Disjoint (V i) (V j))) (ρ : E → ℝ)
    (hsupp : ∀ x ∈ U, ρ (f x) ≠ 0 → ∃ i, x ∈ V i)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ) :
    jacobianIntegral μ f U ρ = ∑ i, jacobianIntegral μ f (V i) ρ := by
  unfold jacobianIntegral
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU
    (iUnion_subset hsub)]
  · exact integral_iUnion_fintype hV hdisj (fun i => hint.mono_set (hsub i))
  · rintro x ⟨hxU, hxV⟩
    have hz : ρ (f x) = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := hsupp x hxU hn
      exact hxV (mem_iUnion.mpr ⟨i, hi⟩)
    rw [hz, mul_zero]

/- The regular signed-count formula, once disjoint inverse patches and a
small normalized target bump have been chosen. -/
theorem jacobianIntegral_eq_sum_signs {ι : Type*} [Fintype ι]
    (f : E → E) (U : Set E) (hU : MeasurableSet U) (V : ι → Set E)
    (hV : ∀ i, MeasurableSet (V i)) (hsub : ∀ i, V i ⊆ U)
    (hdisj : Pairwise (fun i j => Disjoint (V i) (V j)))
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x) (hinj : ∀ i, InjOn f (V i))
    (ρ : E → ℝ) (σ : ι → ℝ)
    (hσ : ∀ i x, x ∈ V i → (fderiv ℝ f x).det = σ i * |(fderiv ℝ f x).det|)
    (hcovered : ∀ x ∈ U, ρ (f x) ≠ 0 → ∃ i, x ∈ V i)
    (hsupp : ∀ i, Function.support ρ ⊆ f '' V i)
    (hunit : ∫ y, ρ y ∂μ = 1)
    (hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ) :
    jacobianIntegral μ f U ρ = ∑ i, σ i := by
  rw [jacobianIntegral_sum_patches μ f U hU V hV hsub hdisj ρ hcovered hint]
  apply Finset.sum_congr rfl
  intro i _
  exact jacobianIntegral_inverse_patch μ f (V i) (hV i)
    (fun x hx => hf x (hsub i hx)) (hinj i) ρ (σ i) (hσ i) (hsupp i) hunit

/- A vanishing selected preimage forces every supported degree integral to
vanish. This implication supplies existence from nonzero degree. -/
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem jacobianIntegral_eq_zero_of_no_preimage (f : E → E) (U : Set E) (ρ : E → ℝ)
    (h : ∀ x ∈ U, ρ (f x) = 0) : jacobianIntegral μ f U ρ = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  simp only [h x hx, mul_zero]

end SignedIntegralDegree
end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A normalized smooth target bump can be supported in any prescribed
neighborhood of the target. -/
theorem exists_normalized_smooth_bump (y : E) (N : Set E) (hN : IsOpen N) (hy : y ∈ N) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ N ∧
      (∫ z, ρ z ∂μ) = 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN y hy
  let b : ContDiffBump y := ⟨r / 4, r / 2, by linarith, by linarith⟩
  refine ⟨b.normed μ, b.contDiff_normed, b.hasCompactSupport_normed,
    ?_, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro z hz
  apply hball
  exact lt_of_le_of_lt hz (by change r / 2 < r; linarith)

/-- One target neighborhood works for every normalized continuous density.
This uniformity lets the same density be used throughout a localized homotopy. -/
theorem regular_signed_count_neighborhood (f : E → E) (hf : ContDiff ℝ 1 f)
    (y : E) (U : Set E) (hU : IsOpen U) (hc : IsCompact (closure U))
    (hb : ∀ x ∈ frontier U, f x ≠ y) (s : Finset E)
    (hs : ∀ x, x ∈ s ↔ x ∈ U ∧ f x = y)
    (hd : ∀ x ∈ s, (fderiv ℝ f x).det ≠ 0) :
    ∃ N : Set E, IsOpen N ∧ y ∈ N ∧ ∀ ρ : E → ℝ, Continuous ρ →
      Function.support ρ ⊆ N → (∫ z, ρ z ∂μ) = 1 →
      jacobianIntegral μ f U ρ = ∑ x ∈ s, (if 0 < (fderiv ℝ f x).det then 1 else -1) := by
  classical
  obtain ⟨V, hV, hdisj⟩ := disjoint_regular_inverse_patches f hf U hU
    (s : Set E) s.finite_toSet (fun x hx => ((hs x).mp hx).1) hd
  obtain ⟨N, hN, hyN, hNimg, hNpre⟩ := exists_target_neighborhood_of_patches f y U hU
    hc hf.continuous.continuousOn hb V (fun i => (hV i).1)
    (fun i => (hV i).2.2.2.2.1)
    (fun i => ⟨i, (hV i).2.1, ((hs i).mp i.property).2⟩)
    (fun x hx hxy => ⟨⟨x, (hs x).mpr ⟨hx, hxy⟩⟩, (hV _).2.1⟩)
  refine ⟨N, hN, hyN, fun ρ hρ hρN hρunit => ?_⟩
  have hcont : Continuous (fun x => (fderiv ℝ f x).det * ρ (f x)) :=
    (ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by norm_num))).mul
      (hρ.comp hf.continuous)
  have hint : IntegrableOn (fun x => (fderiv ℝ f x).det * ρ (f x)) U μ :=
    (hcont.continuousOn.integrableOn_compact hc).mono_set subset_closure
  have hcount := jacobianIntegral_eq_sum_signs μ f U hU.measurableSet V
    (fun i => (hV i).1.measurableSet) (fun i => (hV i).2.2.1) hdisj
    (fun x _ => hf.differentiable (by norm_num) x) (fun i => (hV i).2.2.2.1)
    ρ (fun i => if 0 < (fderiv ℝ f i).det then 1 else -1)
    (fun i => (hV i).2.2.2.2.2)
    (fun x hx hn => hNpre x hx (hρN hn))
    (fun i z hz => hNimg i (hρN hz)) hρunit hint
  exact hcount.trans (Finset.sum_subtype (p := fun x => x ∈ (s : Set E)) s
    (fun _ => Iff.rfl) (fun x => (if 0 < (fderiv ℝ f x).det then 1 else -1 : ℝ))).symm

end EilenbergGanea

open Set MeasureTheory Filter Topology
namespace EilenbergGanea

/-- Stokes on a rectangular box, as a direct consequence of Mathlib's
Bochner divergence theorem. No smoothness of an arbitrary open-set boundary
is assumed in the later application. -/
theorem integral_extDeriv_box {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (hint : IntegrableOn (fun x => extDeriv form x (coordinateBasis (n + 1))) (Icc a b)) :
    (∫ x in Icc a b, extDeriv form x (coordinateBasis (n + 1))) =
      ∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (a i) x)) := by
  have hd (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
      DifferentiableAt ℝ (formFlux form i) x := by
    exact ((hform x).continuousAlternatingMap_apply_const _).const_mul _
  have he (x : Fin (n + 1) → ℝ) :
      (∑ i : Fin (n + 1), fderiv ℝ (formFlux form i) x (Pi.single i 1)) =
        extDeriv form x (coordinateBasis (n + 1)) := by
    rw [extDeriv_apply (hform x)]
    apply Finset.sum_congr rfl
    intro i _
    change (fderiv ℝ (fun y => (-1 : ℝ) ^ i.val *
      form y (i.removeNth (coordinateBasis (n + 1)))) x) (Pi.single i 1) = _
    rw [fderiv_const_mul ((hform x).continuousAlternatingMap_apply_const _) ]
    simp [coordinateBasis]
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (formFlux form) (fun i x => fderiv ℝ (formFlux form i) x) ∅ countable_empty
    (fun i => (show Differentiable ℝ (formFlux form i) from hd i).continuous.continuousOn)
    (fun x _ i => (hd i x).hasFDerivAt) (by simpa only [he] using hint)
  simpa only [he] using h

/-- Every top-degree differential form on Euclidean n-space is closed. -/
theorem extDeriv_topForm_eq_zero {n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) (x : Fin n → ℝ) :
    extDeriv φ x = 0 := by
  ext v
  apply (extDeriv φ x).toAlternatingMap.map_linearDependent
  intro hv
  have h := hv.fintype_card_le_finrank
  simp at h

/-- The pullback of a top form by a C² map is closed (the Piola identity). -/
theorem extDeriv_pullback_topForm_eq_zero {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : Differentiable ℝ φ) (F : E → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F) (x : E) :
    extDeriv (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y)) x = 0 := by
  rw [extDeriv_pullback (hφ _) hF.contDiffAt (by simp), extDeriv_topForm_eq_zero]
  ext v
  rfl


/-- A closed form has total signed flux zero across the faces of a box. -/
theorem closedForm_boundary_box {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (hclosed : ∀ x, extDeriv form x = 0)
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) :
    (∑ i : Fin (n + 1),
        ((∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (b i) x)) -
        ∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          formFlux form i (i.insertNth (a i) x))) = 0 := by
  have hz (x) : extDeriv form x (coordinateBasis (n + 1)) = 0 := by rw [hclosed]; rfl
  have h := integral_extDeriv_box form hform a b hab (by simpa only [hz] using integrableOn_zero)
  simpa only [hz, integral_zero] using h.symm

/-- The coefficient integrals on two opposing faces of a box agree for a
closed form whose flux on all other faces is zero. This is the analytic
homotopy-invariance step with the sides outside the support of the form. -/
theorem closedForm_opposite_faces {n : ℕ}
    (form : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hform : Differentiable ℝ form) (hclosed : ∀ x, extDeriv form x = 0)
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b) (k : Fin (n + 1))
    (hside : ∀ i, i ≠ k → ∀ x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      formFlux form i (i.insertNth (b i) x) = 0 ∧
      formFlux form i (i.insertNth (a i) x) = 0) :
    (∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux form k (k.insertNth (b k) x)) =
    ∫ x in Icc (a ∘ k.succAbove) (b ∘ k.succAbove),
      formFlux form k (k.insertNth (a k) x) := by
  have h := closedForm_boundary_box form hform hclosed a b hab
  rw [Finset.sum_eq_single k] at h
  · exact sub_eq_zero.mp h
  · intro i _ hi
    have hb0 : (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux form i (i.insertNth (b i) x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hside i hi x hx).1
    have ha0 : (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        formFlux form i (i.insertNth (a i) x)) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact (hside i hi x hx).2
    rw [hb0, ha0, sub_self]
  · simp

/-- Smooth pullbacks of a top form are differentiable. -/
theorem differentiable_pullback_topForm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (Fin n → ℝ) → (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hφ : Differentiable ℝ φ) (F : E → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (fun y => (φ (F y)).compContinuousLinearMap (fderiv ℝ F y)) := by
  intro x
  apply ((hφ (F x)).comp x (hF.differentiable (by norm_num) x)
    ).continuousAlternatingMapCompContinuousLinearMap
  exact (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x


/-- Restricting a field to an open set whose boundary avoids its topological
support is locally either the original field or zero. -/
theorem indicator_eventuallyEq_or_zero {X A : Type*} [TopologicalSpace X] [Zero A]
    (U : Set X) (hU : IsOpen U) (f : X → A)
    (hb : Disjoint (frontier U) (tsupport f)) (x : X) :
    U.indicator f =ᶠ[nhds x] f ∨ U.indicator f =ᶠ[nhds x] fun _ => 0 := by
  classical
  by_cases hx : x ∈ U
  · left
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy f
  · right
    by_cases hc : x ∈ closure U
    · have hf : x ∉ tsupport f := by
        apply Set.disjoint_left.mp hb
        exact ⟨hc, by simpa only [hU.interior_eq] using hx⟩
      have he := notMem_tsupport_iff_eventuallyEq.mp hf
      filter_upwards [he] with y hy
      by_cases hyU : y ∈ U <;> simp [Set.indicator, hyU, hy]
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
      exact Set.indicator_of_notMem (fun hyU => hy (subset_closure hyU)) f

/-- Excision at the differential-form level: cutting off at an arbitrary
isolating open-set boundary preserves differentiability and closedness. -/
theorem localized_closedForm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (form : E → E [⋀^Fin n]→L[ℝ] ℝ) (hform : Differentiable ℝ form)
    (hclosed : ∀ x, extDeriv form x = 0) (U : Set E) (hU : IsOpen U)
    (hb : Disjoint (frontier U) (tsupport form)) :
    Differentiable ℝ (U.indicator form) ∧ ∀ x, extDeriv (U.indicator form) x = 0 := by
  constructor
  · intro x
    rcases indicator_eventuallyEq_or_zero U hU form hb x with hx | hx
    · exact (hform x).congr_of_eventuallyEq hx
    · exact differentiableAt_const (c := (0 : E [⋀^Fin n]→L[ℝ] ℝ)) |>.congr_of_eventuallyEq hx
  · intro x
    rcases indicator_eventuallyEq_or_zero U hU form hb x with hx | hx
    · rw [hx.extDeriv_eq, hclosed]
    · rw [hx.extDeriv_eq]
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]


/-- Evaluation of the standard volume form is the ordinary linear
 determinant. -/
theorem coordinateVolumeForm_linear {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    coordinateVolumeForm n (fun i => L (coordinateBasis n i)) = L.det := by
  change Matrix.det (fun i => L (Pi.single i 1)) = _
  calc
    _ = (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      L.toLinearMap).transpose.det := by
        congr 1
    _ = _ := by rw [Matrix.det_transpose, LinearMap.det_toMatrix]

/-- At a temporal face, the pullback coefficient is precisely the signed
Jacobian density of the corresponding slice. -/
theorem formFlux_pullback_first_face {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ))
    (t : ℝ) (x : Fin n → ℝ) (hF : DifferentiableAt ℝ F (Fin.cons t x)) :
    formFlux (fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
      (fderiv ℝ F y)) 0 (Fin.cons t x) =
      (fderiv ℝ (fun z => F (Fin.cons t z)) x).det * ρ (F (Fin.cons t x)) := by
  let J : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    (0 : (Fin n → ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin n → ℝ))
  have hJ : HasFDerivAt (fun z : Fin n → ℝ => Fin.cons t z) J x :=
    (hasFDerivAt_const t x).finCons (hasFDerivAt_id x)
  have hs := hF.hasFDerivAt.comp x hJ
  have he (i : Fin n) : J (coordinateBasis n i) = coordinateBasis (n + 1) i.succ := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [J, coordinateBasis, ContinuousLinearMap.finCons]
    · simp [J, coordinateBasis, ContinuousLinearMap.finCons, Pi.single_apply]
  have hs' : fderiv ℝ (fun z => F (Fin.cons t z)) x =
      (fderiv ℝ F (Fin.cons t x)).comp J := hs.fderiv
  rw [hs']
  have hd := coordinateVolumeForm_linear ((fderiv ℝ F (Fin.cons t x)).comp J)
  simp only [ContinuousLinearMap.comp_apply, he] at hd
  simp only [formFlux, Fin.val_zero, pow_zero, one_mul, Fin.removeNth_zero,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1


/-- The support of a pulled-back density lies above the support of the target
bump. This provides the needed collar at an arbitrary isolating boundary. -/
theorem tsupport_pullback_density_subset {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : (Fin n → ℝ) → ℝ) (F : E → (Fin n → ℝ)) (hF : Continuous F) :
    tsupport (fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
      (fderiv ℝ F y)) ⊆ F ⁻¹' tsupport ρ := by
  apply closure_minimal _ ((isClosed_tsupport ρ).preimage hF)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by ext v; simp [hz])

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory

/-- Stokes localization in an arbitrary open subset of time times space.
The two slices may be different; no regularity of the moving boundary is used. -/
theorem jacobian_integral_moving_box {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, F y ∉ tsupport ρ)
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) (a b : Fin n → ℝ) (hab : a ≤ b)
    (hbox : ∀ t, {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} ⊆ Icc a b)
    (hside : ∀ i : Fin (n + 1), i ≠ 0 →
      ∀ x ∈ Icc ((Fin.cons t₀ a : Fin (n + 1) → ℝ) ∘ i.succAbove)
        ((Fin.cons t₁ b : Fin (n + 1) → ℝ) ∘ i.succAbove),
      i.insertNth ((Fin.cons t₁ b : Fin (n + 1) → ℝ) i) x ∉ C ∧
      i.insertNth ((Fin.cons t₀ a : Fin (n + 1) → ℝ) i) x ∉ C) :
    (∫ x in {x | (Fin.cons t₁ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det * ρ (F (Fin.cons t₁ x))) =
    ∫ x in {x | (Fin.cons t₀ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det * ρ (F (Fin.cons t₀ x)) := by
  classical
  let form := fun y => ((ρ (F y)) • coordinateVolumeForm n).compContinuousLinearMap
    (fderiv ℝ F y)
  have hc : Disjoint (frontier C) (tsupport form) := by
    apply disjoint_left.mpr
    intro y hy hs
    exact hboundary y hy (tsupport_pullback_density_subset ρ F hF.continuous hs)
  obtain ⟨hd, hz⟩ := localized_closedForm form
    (differentiable_pullback_topForm _ (hρ.smul_const _) F hF)
    (extDeriv_pullback_topForm_eq_zero _ (hρ.smul_const _) F hF) C hC hc
  have htbox : (Fin.cons t₀ a : Fin (n + 1) → ℝ) ≤ Fin.cons t₁ b := by
    intro i
    exact Fin.cases ht (fun j => hab j) i
  have he := closedForm_opposite_faces (C.indicator form) hd hz
    (Fin.cons t₀ a) (Fin.cons t₁ b) htbox 0 (by
      intro i hi x hx
      obtain ⟨h₁, h₀⟩ := hside i hi x hx
      simp [formFlux, indicator_of_notMem h₁, indicator_of_notMem h₀])
  have hface (t : ℝ) (x : Fin n → ℝ) :
      formFlux (C.indicator form) 0 (Fin.cons t x) =
        {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C}.indicator
          (fun z => (fderiv ℝ (fun w => F (Fin.cons t w)) z).det *
          ρ (F (Fin.cons t z))) x := by
    by_cases hx : (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C
    · rw [indicator_of_mem (show x ∈ {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} from hx)]
      change (-1 : ℝ) ^ (0 : Fin (n + 1)).val *
        (C.indicator form) (Fin.cons t x) _ = _
      rw [indicator_of_mem hx]
      exact formFlux_pullback_first_face ρ F t x (hF.differentiable (by norm_num) _)
    · simp [formFlux, hx]
  have hins (t : ℝ) (x : Fin n → ℝ) :
      (0 : Fin (n + 1)).insertNth t x = (Fin.cons t x : Fin (n + 1) → ℝ) := by
    simp only [Fin.insertNth_zero, cast_eq]
  have hm (t : ℝ) : MeasurableSet {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C} := by
    apply (hC.preimage _).measurableSet
    apply continuous_pi
    intro i
    exact Fin.cases continuous_const (fun j => continuous_apply j) i
  simpa only [Fin.succAbove_zero, Function.comp_def, Fin.cons_succ, Fin.cons_zero,
    hins, hface, setIntegral_indicator (hm _),
    inter_eq_right.mpr (hbox _)] using he

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology

/-- Box-free moving-domain Stokes, with arbitrary open moving slices contained
in one bounded spatial set. -/
theorem jacobian_integral_moving {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, F y ∉ tsupport ρ)
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t : ℝ, Fin.cons t x ∈ C})
    (t₀ t₁ : ℝ) (ht : t₀ ≤ t₁) :
    (∫ x in {x | (Fin.cons t₁ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₁ z)) x).det * ρ (F (Fin.cons t₁ x))) =
    ∫ x in {x | (Fin.cons t₀ x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons t₀ z)) x).det * ρ (F (Fin.cons t₀ x)) := by
  obtain ⟨R, hR, hbound⟩ := hCb.exists_pos_norm_lt
  have hcoord (t : ℝ) (x : Fin n → ℝ) (hx : Fin.cons t x ∈ C) (i : Fin n) : |x i| < R :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
      (hbound x ⟨t, hx⟩)
  have hout (y : Fin (n + 1) → ℝ) (j : Fin n)
      (hj : y j.succ = R ∨ y j.succ = -R) : y ∉ C := by
    intro hy
    have hh := hcoord (y 0) (Fin.tail y) (by simpa only [Fin.cons_self_tail] using hy) j
    change |y j.succ| < R at hh
    rcases hj with hj | hj
    · rw [hj, abs_of_pos hR] at hh; exact lt_irrefl _ hh
    · rw [hj, abs_neg, abs_of_pos hR] at hh; exact lt_irrefl _ hh
  apply jacobian_integral_moving_box ρ hρ F hF C hC hboundary t₀ t₁ ht
    (fun _ => -R) (fun _ => R) (fun _ => by linarith)
  · intro t x hx
    constructor <;> intro i
    · exact (abs_lt.mp (hcoord t x hx i)).1.le
    · exact (abs_lt.mp (hcoord t x hx i)).2.le
  · intro i hi x _
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    constructor
    · apply hout _ j
      left
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]
    · apply hout _ j
      right
      simp only [Fin.insertNth_apply_same, Fin.cons_succ]

/-- Smooth time saturation reduces the collar hypothesis to the actual time
interval even for moving open domains. -/
theorem jacobian_integral_moving_interval {n : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (hρ : Differentiable ℝ ρ)
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hboundary : ∀ y ∈ frontier C, y 0 ∈ Icc (0 : ℝ) 1 → F y ∉ tsupport ρ)
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ C}) :
    (∫ x in {x | (Fin.cons 1 x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons 1 z)) x).det * ρ (F (Fin.cons 1 x))) =
    ∫ x in {x | (Fin.cons 0 x : Fin (n + 1) → ℝ) ∈ C},
      (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det * ρ (F (Fin.cons 0 x)) := by
  let T : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => Fin.cons (Real.smoothTransition (y 0)) (Fin.tail y)
  have hT : ContDiff ℝ 2 T := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Real.smoothTransition.contDiff.comp (contDiff_apply ℝ ℝ 0)
    · exact contDiff_apply ℝ ℝ j.succ
  have hb : ∀ y ∈ frontier (T ⁻¹' C), (F ∘ T) y ∉ tsupport ρ := by
    intro y hy
    exact hboundary (T y) (hT.continuous.frontier_preimage_subset C hy)
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hbound : Bornology.IsBounded {x : Fin n → ℝ | ∃ t : ℝ, Fin.cons t x ∈ T ⁻¹' C} := by
    apply hCb.subset
    rintro x ⟨t, ht⟩
    exact ⟨Real.smoothTransition t, ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ht⟩
  have he := jacobian_integral_moving ρ hρ (F ∘ T) (hF.comp hT) (T ⁻¹' C)
    (hC.preimage hT.continuous) hb hbound 0 1 zero_le_one
  simpa only [T, Function.comp_apply, mem_preimage, Fin.cons_zero, Fin.tail_cons,
    Real.smoothTransition.zero, Real.smoothTransition.one] using he

end EilenbergGanea

namespace EilenbergGanea
open Set MeasureTheory Filter Topology

/-- A nonzero signed count survives an arbitrary moving open set. The compact
boundary slab hypothesis is satisfied by the fixed annulus in the quaternion
application; no boundary triangulation or regular-value hypothesis is used
along the homotopy. -/
theorem regular_count_persists_moving {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 2 F)
    (y : Fin n → ℝ) (C : Set (Fin (n + 1) → ℝ)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (Fin.cons 0 x : Fin (n + 1) → ℝ) ∈ C}))
    (hc₁ : IsCompact (closure {x | (Fin.cons 1 x : Fin (n + 1) → ℝ) ∈ C}))
    (hcB : IsCompact {q | q ∈ frontier C ∧ q 0 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ C})
    (hb : ∀ q ∈ frontier C, q 0 ∈ Icc (0 : ℝ) 1 → F q ≠ y)
    (s : Finset (Fin n → ℝ))
    (hs : ∀ x, x ∈ s ↔ Fin.cons 0 x ∈ C ∧ F (Fin.cons 0 x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) : ∃ x, Fin.cons 1 x ∈ C ∧ F (Fin.cons 1 x) = y := by
  classical
  by_contra hno
  have hno' : ∀ x, Fin.cons 1 x ∈ C → F (Fin.cons 1 x) ≠ y := by simpa using hno
  let U : ℝ → Set (Fin n → ℝ) := fun t => {x | (Fin.cons t x : Fin (n + 1) → ℝ) ∈ C}
  let f₀ := fun x => F (Fin.cons 0 x)
  let f₁ := fun x => F (Fin.cons 1 x)
  have hcons (t : ℝ) : ContDiff ℝ 2 (fun x : Fin n → ℝ => (Fin.cons t x : Fin (n + 1) → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    exact Fin.cases contDiff_const (fun j => contDiff_apply ℝ ℝ j) i
  have hU (t : ℝ) : IsOpen (U t) := hC.preimage (hcons t).continuous
  have hfront (t : ℝ) : frontier (U t) ⊆
      (fun x : Fin n → ℝ => Fin.cons t x) ⁻¹' frontier C :=
    (hcons t).continuous.frontier_preimage_subset C
  have hf₀ : ContDiff ℝ 1 f₀ := (hF.comp (hcons 0)).of_le (by norm_num)
  have hf₁ : Continuous f₁ := (hF.comp (hcons 1)).continuous
  obtain ⟨N, hN, hyN, hsign⟩ := regular_signed_count_neighborhood volume f₀ hf₀ y (U 0)
    (hU 0) hc₀ (fun x hx => hb _ (hfront 0 hx) (by simp)) s hs hd
  let K := F '' {q | q ∈ frontier C ∧ q 0 ∈ Icc (0 : ℝ) 1}
  have hK : IsCompact K := hcB.image hF.continuous
  have hyK : y ∉ K := by
    rintro ⟨q, ⟨hq, ht⟩, he⟩
    exact hb q hq ht he
  have hy₁ : y ∉ f₁ '' closure (U 1) := by
    rintro ⟨x, hx, he⟩
    by_cases hxU : x ∈ U 1
    · exact hno' x hxU he
    · have hxf : x ∈ frontier (U 1) := ⟨hx, by simpa only [(hU 1).interior_eq] using hxU⟩
      exact hb _ (hfront 1 hxf) (by simp) he
  let M := N \ (K ∪ f₁ '' closure (U 1))
  have hM : IsOpen M := hN.sdiff (hK.isClosed.union (hc₁.image hf₁).isClosed)
  have hyM : y ∈ M := ⟨hyN, fun h => h.elim hyK hy₁⟩
  obtain ⟨ρ, hρ, _, hρM, hunit⟩ := exists_normalized_smooth_bump volume y M hM hyM
  have hρN : Function.support ρ ⊆ N := fun z hz => (hρM (subset_tsupport ρ hz)).1
  have hval : jacobianIntegral volume f₀ (U 0) ρ =
      ∑ x ∈ s, (if 0 < (fderiv ℝ f₀ x).det then 1 else -1) :=
    hsign ρ hρ.continuous hρN hunit
  have hcollar : ∀ q ∈ frontier C, q 0 ∈ Icc (0 : ℝ) 1 → F q ∉ tsupport ρ := by
    intro q hq ht hsup
    exact (hρM hsup).2 (Or.inl ⟨q, ⟨hq, ht⟩, rfl⟩)
  have hinv := jacobian_integral_moving_interval ρ (hρ.differentiable (by simp)) F hF C hC hcollar hCb
  have hzero : jacobianIntegral volume f₁ (U 1) ρ = 0 := by
    apply jacobianIntegral_eq_zero_of_no_preimage
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hsup
    exact (hρM hsup).2 (Or.inr ⟨x, subset_closure hx, rfl⟩)
  apply hcount
  exact hval.symm.trans (hinv.symm.trans hzero)

end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coordinate-free moving-domain nonzero-count persistence. -/
theorem regular_count_persists_moving_finiteDimensional
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F) (y : E)
    (C : Set (ℝ × E)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ y)
    (s : Finset E) (hs : ∀ x, x ∈ s ↔ (0, x) ∈ C ∧ F (0, x) = y)
    (hd : ∀ x ∈ s, (fderiv ℝ (fun z => F (0, z)) x).det ≠ 0)
    (hcount : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => F (0, z)) x).det
      then 1 else -1 : ℝ)) ≠ 0) : ∃ x, (1, x) ∈ C ∧ F (1, x) = y := by
  classical
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := (Module.finBasis ℝ E).equivFunL
  let H : (ℝ × E) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e).trans (Fin.consEquivL ℝ (fun _ => ℝ))
  let G : (Fin (n + 1) → ℝ) → (Fin n → ℝ) := fun q => e (F (H.symm q))
  let D := H.symm ⁻¹' C
  have hH (t : ℝ) (x : E) : H (t, x) = Fin.cons t (e x) := rfl
  have hHi (t : ℝ) (x : Fin n → ℝ) : H.symm (Fin.cons t x) = (t, e.symm x) := by
    apply H.injective
    rw [H.apply_symm_apply, hH, e.apply_symm_apply]
  have hG : ContDiff ℝ 2 G := e.contDiff.comp (hF.comp H.symm.contDiff)
  have hdet (x : E) :
      (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det =
      (fderiv ℝ (fun z => F (0, z)) x).det := by
    have h₀ : DifferentiableAt ℝ (fun z => F (0, z)) x :=
      (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
    have h₀' : HasFDerivAt (fun z => F (0, z))
        (fderiv ℝ (fun z => F (0, z)) x) (e.symm (e x)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using h₀.hasFDerivAt
    have hcomp := e.hasFDerivAt.comp (e x) (h₀'.comp (e x) e.symm.hasFDerivAt)
    have hh : (fun z => G (Fin.cons 0 z)) = e ∘ (fun z => F (0, z)) ∘ e.symm := by
      funext z; simp only [G, hHi, Function.comp_def]
    rw [hh, hcomp.fderiv]
    exact LinearMap.det_conj _ e.toLinearEquiv
  have hslice (t : ℝ) : {x : Fin n → ℝ | Fin.cons t x ∈ D} = e '' {x | (t, x) ∈ C} := by
    ext x
    change H.symm (Fin.cons t x) ∈ C ↔ _
    rw [hHi]
    constructor
    · intro hx; exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨z, hz, rfl⟩; simpa only [ContinuousLinearEquiv.symm_apply_apply, mem_ofPred_eq] using hz
  have hcompact (t : ℝ) (ht : IsCompact (closure {x : E | (t, x) ∈ C})) :
      IsCompact (closure {x : Fin n → ℝ | Fin.cons t x ∈ D}) := by
    rw [hslice, ← show (e : E → (Fin n → ℝ)) '' closure {x | (t, x) ∈ C} = closure (e '' {x | (t, x) ∈ C}) from e.toHomeomorph.image_closure _]
    exact ht.image e.continuous
  have hfront : frontier D = H.symm ⁻¹' frontier C := by
    exact (H.symm.toHomeomorph.preimage_frontier C).symm
  have hboundary : {q : Fin (n + 1) → ℝ | q ∈ frontier D ∧ q 0 ∈ Icc (0 : ℝ) 1} =
      H '' {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1} := by
    ext q
    rw [hfront]
    constructor
    · rintro ⟨hq, ht⟩
      refine ⟨H.symm q, ⟨hq, ?_⟩, H.apply_symm_apply q⟩
      exact ht
    · rintro ⟨z, ⟨hz, ht⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
      · exact ht
  have hbounded : {x : Fin n → ℝ | ∃ t ∈ Icc (0 : ℝ) 1, Fin.cons t x ∈ D} =
      e '' {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C} := by
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      have hx' : x ∈ e '' {z | (t, z) ∈ C} := by rw [← hslice]; exact hx
      obtain ⟨z, hz, rfl⟩ := hx'
      exact ⟨z, ⟨t, ht, hz⟩, rfl⟩
    · rintro ⟨z, ⟨t, ht, hz⟩, rfl⟩
      exact ⟨t, ht, by change e z ∈ {x | Fin.cons t x ∈ D}; rw [hslice]; exact ⟨z, hz, rfl⟩⟩
  let s' := s.map e.toEquiv.toEmbedding
  have hs' : ∀ x, x ∈ s' ↔ Fin.cons 0 x ∈ D ∧ G (Fin.cons 0 x) = e y := by
    intro x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      change H.symm (Fin.cons 0 (e z)) ∈ C ∧ e (F (H.symm (Fin.cons 0 (e z)))) = e y
      rw [hHi, e.symm_apply_apply]
      exact ⟨((hs z).mp hz).1, congrArg e ((hs z).mp hz).2⟩
    · rintro ⟨hx, he⟩
      refine Finset.mem_map.mpr ⟨e.symm x, (hs _).mpr ⟨?_, ?_⟩, e.apply_symm_apply x⟩
      · simpa only [D, mem_preimage, hHi] using hx
      · apply e.injective; simpa only [G, hHi] using he
  have hd' : ∀ x ∈ s', (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det ≠ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    change (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e z)).det ≠ 0
    rw [hdet]; exact hd z hz
  have hcount' : (∑ x ∈ s', (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) x).det
      then 1 else -1 : ℝ)) ≠ 0 := by
    change (∑ x ∈ s.map e.toEquiv.toEmbedding, _) ≠ 0
    rw [Finset.sum_map]
    change (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (Fin.cons 0 z)) (e x)).det then 1 else -1 : ℝ)) ≠ 0
    simpa only [hdet] using hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists_moving G hG (e y) D
    (hC.preimage H.symm.continuous) (hcompact 0 hc₀) (hcompact 1 hc₁)
    (by rw [hboundary]; exact hcB.image H.continuous)
    (by rw [hbounded]; exact e.lipschitz.isBounded_image hCb)
    (by
      intro q hq ht heq
      apply hb (H.symm q) (by rw [hfront] at hq; exact hq) ht
      exact e.injective heq) s' hs' hd' hcount'
  exact ⟨e.symm x, by simpa only [D, mem_preimage, hHi] using hx,
    e.injective (by simpa only [G, hHi] using he)⟩
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Arbitrarily small regular approximations at the initial slice suffice for
moving-domain continuation. Uniform closeness is requested on the spatial
projection of the boundary slab, not on an assumed fixed isolating domain. -/
theorem regular_approximation_persists_moving
    (F : ℝ × E → E) (hF : ContDiff ℝ 2 F)
    (C : Set (ℝ × E)) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0)
    (L : Set E) (hLB : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → q.2 ∈ L)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : E → E, ContDiff ℝ ∞ g ∧
      (∀ x ∈ L, ‖g x - F (0, x)‖ < ε) ∧
      ∃ s : Finset E, (∀ x, x ∈ s ↔ x ∈ closure {z | (0, z) ∈ C} ∧ g x = 0) ∧
        (∀ x ∈ s, (fderiv ℝ g x).det ≠ 0) ∧
        (∑ x ∈ s, (if 0 < (fderiv ℝ g x).det then 1 else -1 : ℝ)) ≠ 0) :
    ∃ x, (1, x) ∈ C ∧ F (1, x) = 0 := by
  classical
  let P := {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1}
  have hz : (0 : E) ∈ (F '' P)ᶜ := by
    rintro ⟨q, ⟨hq, ht⟩, he⟩
    exact hb q hq ht he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hcB.image hF.continuous).isClosed.isOpen_compl 0 hz
  have hbound : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → ε ≤ ‖F q‖ := by
    intro q hq ht
    by_contra hn
    have hmem : F q ∈ Metric.ball (0 : E) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hn
    exact hball hmem ⟨q, ⟨hq, ht⟩, rfl⟩
  obtain ⟨g, hg, hclose, s, hs, hd, hcount⟩ := happrox ε hε
  let G : ℝ × E → E := fun q => F q + (1 - q.1) • (g q.2 - F (0, q.2))
  have hG : ContDiff ℝ 2 G := hF.add
    ((contDiff_const.sub contDiff_fst).smul (((contDiff_infty.mp hg 2).comp contDiff_snd).sub
      (hF.comp (contDiff_const.prodMk contDiff_snd))))
  have hG0 : (fun x => G (0, x)) = g := by funext x; simp [G]
  have hG1 : (fun x => G (1, x)) = fun x => F (1, x) := by funext x; simp [G]
  have hGb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → G q ≠ 0 := by
    intro q hq ht he
    have heq : F q = -((1 - q.1) • (g q.2 - F (0, q.2))) := eq_neg_of_add_eq_zero_left he
    have hn : ‖F q‖ < ε := by
      rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
      calc
        (1 - q.1) * ‖g q.2 - F (0, q.2)‖ ≤ ‖g q.2 - F (0, q.2)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
        _ < ε := hclose q.2 (hLB q hq ht)
    exact (not_lt_of_ge (hbound q hq ht)) hn
  have hU : IsOpen {x : E | (0, x) ∈ C} := hC.preimage (continuous_const.prodMk continuous_id)
  have hfront : frontier {x : E | (0, x) ∈ C} ⊆ (fun x : E => ((0 : ℝ), x)) ⁻¹' frontier C :=
    (continuous_const.prodMk continuous_id).frontier_preimage_subset C
  have hsU : ∀ x, x ∈ s ↔ (0, x) ∈ C ∧ G (0, x) = 0 := by
    intro x
    rw [hs, show G (0, x) = g x from congrFun hG0 x]
    constructor
    · rintro ⟨hx, he⟩
      refine ⟨?_, he⟩
      by_contra hn
      have hxf : x ∈ frontier {z : E | (0, z) ∈ C} :=
        ⟨hx, by simpa only [hU.interior_eq, mem_ofPred_eq] using hn⟩
      exact hGb (0, x) (hfront hxf) (by simp)
        (by rw [show G (0, x) = g x from congrFun hG0 x]; exact he)
    · rintro ⟨hx, he⟩; exact ⟨subset_closure hx, he⟩
  have hd' : ∀ x ∈ s, (fderiv ℝ (fun z => G (0, z)) x).det ≠ 0 := by rw [hG0]; exact hd
  have hcount' : (∑ x ∈ s, (if 0 < (fderiv ℝ (fun z => G (0, z)) x).det then 1 else -1 : ℝ)) ≠ 0 := by
    rw [hG0]; exact hcount
  obtain ⟨x, hx, he⟩ := regular_count_persists_moving_finiteDimensional G hG 0 C hC hc₀ hc₁ hcB hCb hGb s hsU hd' hcount'
  exact ⟨x, hx, by simpa only [show G (1, x) = F (1, x) from congrFun hG1 x] using he⟩

/-- Full localized word-root persistence for moving open sets. Contains the
singular pure-word initial maps used in the manuscript's finite-quotient step. -/
theorem localized_word_root_persists_moving {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (F : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)))
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ q, F (0, q) = splitWordMap w q)
    (C : Set (ℝ × ((Fin m → ℂ) × (Fin m → ℂ)))) (hC : IsOpen C)
    (hc₀ : IsCompact (closure {x | (0, x) ∈ C}))
    (hc₁ : IsCompact (closure {x | (1, x) ∈ C}))
    (hcB : IsCompact {q | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1})
    (hCb : Bornology.IsBounded {x | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C})
    (hUi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ closure {x | (0, x) ∈ C},
      (q.1, z • q.2) ∈ closure {x | (0, x) ∈ C})
    (h1 : (0, (1, 0)) ∈ C)
    (hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0) :
    ∃ x, (1, x) ∈ C ∧ F (1, x) = 0 := by
  let K := closure {x | (0, x) ∈ C}
  let L := K ∪ Prod.snd '' {q | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1}
  have hL : IsCompact L := hc₀.union (hcB.image continuous_snd)
  apply regular_approximation_persists_moving F hF C hC hc₀ hc₁ hcB hCb hb L
    (fun q hq ht => Or.inr ⟨q, ⟨hq, ht⟩, rfl⟩)
  intro ε hε
  simpa only [hF0] using word_exists_regularization_nonzero_count w hB
    K hc₀ hUi (subset_closure h1) L hL subset_union_left ε hε
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.RightAngledArtin_ResidualFiniteness
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set

namespace EilenbergGanea
universe u
/-! Finite permutation separation for free groups. -/


section FiniteQuotientSeparation

variable {A : Type*} [Group A] [Group.ResiduallyFinite A]

/-- Finitely many nonidentity elements can be excluded by one finite quotient. -/
theorem finite_nonidentity_separation (s : Finset A) :
    ∃ H : FiniteIndexNormalSubgroup A, ∀ a ∈ s, a ≠ 1 → a ∉ H := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨.ofSubgroup ⊤, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨H, hH⟩ := ih
    by_cases h1 : a = 1
    · refine ⟨H, ?_⟩
      intro b hb hb1
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hb1 h1).elim
      · exact hH b hb hb1
    · obtain ⟨K, hK⟩ := Group.exists_finiteIndexNormalSubgroup_notMem a h1
      refine ⟨H ⊓ K, ?_⟩
      intro b hb hb1 hm
      change b ∈ H.toSubgroup ⊓ K.toSubgroup at hm
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hK hm.2
      · exact hH b hb hb1 hm.1

/-- The exact finite-set injectivity consequence of residual finiteness. -/
theorem finite_set_quotient_injective (s : Finset A) :
    ∃ H : FiniteIndexNormalSubgroup A,
      Set.InjOn (QuotientGroup.mk' H.toSubgroup) (s : Set A) := by
  classical
  obtain ⟨H, hH⟩ := finite_nonidentity_separation
    ((s ×ˢ s).image (fun z => z.1⁻¹ * z.2))
  refine ⟨H, ?_⟩
  intro a ha b hb he
  by_contra hn
  apply hH (a⁻¹ * b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)
    (fun h => hn (eq_of_inv_mul_eq_one h))
  exact QuotientGroup.eq.mp he

end FiniteQuotientSeparation


end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.WordEquations
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff

/-- A concrete sublevel version of localized degree. The only root isolation
conditions are a uniform radial bound and exclusion of the threshold; no
regularity of any root or of the sublevel boundary is assumed. -/
theorem localized_word_root_sublevel {m : ℕ}
    (w : Fin m → FreeGroup (Fin m)) (hB : (exponentMatrix w).det ≠ 0)
    (F : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ((Fin m → ℂ) × (Fin m → ℂ)))
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ q, F (0, q) = splitWordMap w q)
    (h : ℝ × ((Fin m → ℂ) × (Fin m → ℂ)) → ℝ) (hh : Continuous h)
    (δ R : ℝ) (hR : ‖((1 : Fin m → ℂ), (0 : Fin m → ℂ))‖ < R)
    (h1 : h (0, (1, 0)) < δ)
    (hi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q, h (0, (q.1, z • q.2)) = h (0, q))
    (hbound : ∀ q, q.1 ∈ Icc (0 : ℝ) 1 → F q = 0 → ‖q.2‖ < R)
    (hiso : ∀ q, q.1 ∈ Icc (0 : ℝ) 1 → F q = 0 → h q ≠ δ) :
    ∃ x, F (1, x) = 0 ∧ h (1, x) < δ := by
  let E := (Fin m → ℂ) × (Fin m → ℂ)
  let C : Set (ℝ × E) := {q | ‖q.2‖ < R ∧ h q < δ}
  have hC : IsOpen C := (isOpen_lt continuous_snd.norm continuous_const).inter
    (isOpen_lt hh continuous_const)
  have hcl : closure C ⊆ {q | ‖q.2‖ ≤ R ∧ h q ≤ δ} :=
    closure_minimal (fun _ hq => ⟨hq.1.le, hq.2.le⟩)
      ((isClosed_le continuous_snd.norm continuous_const).inter (isClosed_le hh continuous_const))
  have hslice (t : ℝ) : Bornology.IsBounded {x : E | (t, x) ∈ C} := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.1.le)
  have hBcompact : IsCompact {q : ℝ × E | q ∈ frontier C ∧ q.1 ∈ Icc (0 : ℝ) 1} := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
      (isClosed_frontier.inter (isClosed_Icc.preimage continuous_fst))
    intro q hq
    refine ⟨hq.2, ?_⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (hcl (frontier_subset_closure hq.1)).1)
  have hCb : Bornology.IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, (t, x) ∈ C} := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
    rintro x ⟨t, _, hx⟩
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.1.le)
  have hUi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q ∈ closure {x : E | (0, x) ∈ C},
      (q.1, z • q.2) ∈ closure {x : E | (0, x) ∈ C} := by
    intro z hz
    have hmaps : MapsTo (fun q : E => (q.1, z • q.2)) {x | (0, x) ∈ C} {x | (0, x) ∈ C} := by
      intro q hq
      refine ⟨?_, ?_⟩
      · have hn : ‖(q.1, z • q.2)‖ = ‖q‖ := by
          change max ‖q.1‖ ‖z • q.2‖ = max ‖q.1‖ ‖q.2‖
          rw [norm_smul, hz, one_mul]
        simpa only [hn] using hq.1
      · simpa only [hi z hz q] using hq.2
    have hr : Continuous (fun q : E => (q.1, z • q.2)) := by fun_prop
    exact hmaps.closure_of_continuousOn hr.continuousOn
  have hb : ∀ q ∈ frontier C, q.1 ∈ Icc (0 : ℝ) 1 → F q ≠ 0 := by
    intro q hq ht hf
    have hhδ : h q < δ := lt_of_le_of_ne (hcl (frontier_subset_closure hq)).2 (hiso q ht hf)
    have hqC : q ∈ C := ⟨hbound q ht hf, hhδ⟩
    exact hq.2 (by simpa only [hC.interior_eq] using hqC)
  obtain ⟨x, hx, he⟩ := localized_word_root_persists_moving w hB F hF hF0 C hC
    (hslice 0).isCompact_closure (hslice 1).isCompact_closure hBcompact hCb hUi ⟨hR, h1⟩ hb
  exact ⟨x, he, hx.2⟩
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

theorem coefficientWordMap_initial {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (x : Fin m → SU2) :
    coefficientWordMap w a (0, x) = fun i => FreeGroup.lift x (eraseCoefficients (w i)) := by
  have he : FreeGroup.lift (Sum.elim (a 0) x) = (FreeGroup.lift x).comp eraseCoefficients := by
    apply FreeGroup.ext_hom
    intro i
    cases i with
    | inl i => simp [eraseCoefficients, ha]
    | inr i => simp [eraseCoefficients]
  funext i
  exact congrArg (fun f : FreeGroup (ι ⊕ Fin m) →* SU2 => f (w i)) he

/-- The same conjugation-invariant radial cutoff handles arbitrary coefficient
words, and does not create roots on the coordinate hyperplanes. -/
theorem radialCutoff_family_smooth {m : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ × (Fin m → ℍ) → V)
    (hf : ∀ q, (∀ i, q.2 i ≠ 0) → ContDiffAt ℝ ∞ f q) :
    ContDiff ℝ ∞ (fun q => radialCutoff q.2 • f q) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : ∀ i, q.2 i ≠ 0
  · exact (radialCutoff_contDiff.comp contDiff_snd).contDiffAt.smul (hf q hq)
  · push Not at hq
    obtain ⟨i, hi⟩ := hq
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × (Fin m → ℍ) => (0 : V)) q).congr_of_eventuallyEq
    have he : ∀ᶠ p in 𝓝 q, radialCutoff p.2 = 0 :=
      continuous_snd.continuousAt (radialCutoff_eventually_zero q.2 i hi)
    filter_upwards [he] with p hp
    simp only [hp, zero_smul]

theorem coefficientWordMap_normalized_smoothAt {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ)))
    (q : ℝ × (Fin m → ℍ)) (hq : ∀ i, q.2 i ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Fin m → ℍ) =>
      fun i => (coefficientWordMap w a (p.1, fun j => normalizeQuaternion (p.2 j)) i : ℍ)) q := by
  apply contDiffAt_pi.mpr
  intro i
  refine freeGroup_lift_coe_contDiffAt (w i) q
    (fun parameter => Sum.elim (a parameter.1)
      (fun index => normalizeQuaternion (parameter.2 index))) ?_
  intro j
  cases j with
  | inl j => exact ((ha j).comp contDiff_fst).contDiffAt
  | inr j =>
      change ContDiffAt ℝ ∞ (fun p : ℝ × (Fin m → ℍ) => (normalizeQuaternion (p.2 j) : ℍ)) q
      exact (normalizeQuaternion_coe_contDiffAt (hq j)).comp (f := fun p : ℝ × (Fin m → ℍ) => p.2 j) q
        ((contDiff_apply ℝ ℍ j).comp contDiff_snd).contDiffAt

theorem smoothRadialCoefficientWordMap_smooth {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ))) :
    ContDiff ℝ ∞ (smoothRadialCoefficientWordMap w a) := by
  apply radialCutoff_family_smooth
  intro q hq
  apply contDiffAt_pi.mpr
  intro i
  exact (((contDiff_apply ℝ ℍ i).comp contDiff_snd).contDiffAt.norm ℝ (hq i)).smul
    ((contDiffAt_pi.mp (coefficientWordMap_normalized_smoothAt w a ha q hq)) i)

theorem radialCoefficientWordMap_eq_one_iff {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : radialCoefficientWordMap w a q = 1 ↔
      (∀ i, ‖q.2 i‖ = 1) ∧ coefficientWordMap w a
        (q.1, fun j => normalizeQuaternion (q.2 j)) = 1 := by
  constructor
  · intro h
    have hn (i : Fin m) : ‖q.2 i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [radialCoefficientWordMap_norm, Pi.one_apply, norm_one] using he
    refine ⟨hn, ?_⟩
    funext i
    apply Subtype.ext
    have he := congrFun h i
    simpa [radialCoefficientWordMap, hn] using he
  · rintro ⟨hn, hw⟩
    funext i
    simp [radialCoefficientWordMap, hn, hw]

theorem smoothRadialCoefficientWordMap_eq_one_iff {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (q : ℝ × (Fin m → ℍ)) : smoothRadialCoefficientWordMap w a q = 1 ↔
      (∀ i, ‖q.2 i‖ = 1) ∧ coefficientWordMap w a
        (q.1, fun j => normalizeQuaternion (q.2 j)) = 1 := by
  rw [← radialCoefficientWordMap_eq_one_iff]
  constructor
  · intro h
    have hn (i : Fin m) : radialCutoff q.2 * ‖q.2 i‖ = 1 := by
      have he := congrArg (fun y : Fin m → ℍ => ‖y i‖) h
      simpa only [smoothRadialCoefficientWordMap, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (radialCutoff_nonneg q.2), radialCoefficientWordMap_norm, Pi.one_apply, norm_one] using he
    have hlarge (i : Fin m) : 1 ≤ ‖q.2 i‖ := by
      have hle := mul_le_mul_of_nonneg_right (radialCutoff_le_one q.2) (norm_nonneg (q.2 i))
      rw [hn i, one_mul] at hle
      exact hle
    simpa only [smoothRadialCoefficientWordMap, radialCutoff_eq_one q.2 hlarge, one_smul] using h
  · intro h
    have hn := (radialCoefficientWordMap_eq_one_iff w a q).mp h
    simp only [smoothRadialCoefficientWordMap, radialCutoff_eq_one q.2 (fun i => (hn.1 i).ge), one_smul, h]

theorem smoothRadialCoefficientWordMap_initial {ι : Type*} {m : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (x : Fin m → ℍ) :
    smoothRadialCoefficientWordMap w a (0, x) =
      smoothRadialWordMap (fun i => eraseCoefficients (w i)) x := by
  unfold smoothRadialCoefficientWordMap smoothRadialWordMap
  congr 1
  funext i
  dsimp only [radialCoefficientWordMap, radialWordMap]
  rw [coefficientWordMap_initial w a ha]
  rfl
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

theorem cutoffCoefficientProducts_smooth {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ))) :
    ContDiff ℝ ∞ (cutoffCoefficientProducts w a) :=
  radialCutoff_family_smooth _ (coefficientWordMap_normalized_smoothAt w a ha)

theorem cutoffCoefficientProducts_unitary {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (t : ℝ) (x : Fin m → SU2) :
    cutoffCoefficientProducts w a (t, fun i => (x i : ℍ)) =
      fun i => (coefficientWordMap w a (t, x) i : ℍ) := by
  have hn (i : Fin m) : ‖(x i : ℍ)‖ = 1 := (quaternion_mem_unitary_iff _).mp (x i).property
  simp only [cutoffCoefficientProducts, radialCutoff_eq_one _ (fun i => (hn i).ge), one_smul,
    normalizeQuaternion_unitary]
end EilenbergGanea

namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff

 theorem quaternionConjugate_sub (a : SU2) (q r : ℍ) :
    quaternionConjugate a (q - r) = quaternionConjugate a q - quaternionConjugate a r := by
  simp only [quaternionConjugate, mul_sub, sub_mul]

 theorem coefficientWordMap_initial_conjugate {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → SU2) :
    coefficientWordMap w a (0, fun i => b * x i * b⁻¹) =
      fun i => b * coefficientWordMap w a (0, x) i * b⁻¹ := by
  rw [coefficientWordMap_initial w a ha, coefficientWordMap_initial w a ha]
  have he : FreeGroup.lift (fun i => b * x i * b⁻¹) =
      (MulAut.conj b).toMonoidHom.comp (FreeGroup.lift x) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  funext i
  rw [he]
  rfl

 theorem cutoffCoefficientProducts_initial_conjugate {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → ℍ) :
    cutoffCoefficientProducts w a (0, fun i => quaternionConjugate b (x i)) =
      fun i => quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) := by
  funext i
  simp only [cutoffCoefficientProducts, radialCutoff, quaternionConjugate_norm,
    normalizeQuaternion_conjugate, coefficientWordMap_initial_conjugate w a ha,
    Pi.smul_apply, quaternionConjugate_smul, quaternionConjugate_coe]

 theorem cutoffCoefficientProducts_initial_size_invariant {ι : Type*} {m d : ℕ}
    (w : Fin d → FreeGroup (ι ⊕ Fin m)) (a : ℝ → ι → SU2)
    (ha : ∀ i, a 0 i = 1) (b : SU2) (x : Fin m → ℍ) :
    ‖cutoffCoefficientProducts w a (0, fun i => quaternionConjugate b (x i)) - 1‖ =
      ‖cutoffCoefficientProducts w a (0, x) - 1‖ := by
  rw [cutoffCoefficientProducts_initial_conjugate w a ha]
  have hn (i : Fin d) : ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) - 1‖ =
      ‖cutoffCoefficientProducts w a (0, x) i - 1‖ := by
    calc
      _ = ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i - 1)‖ := by rw [quaternionConjugate_sub, quaternionConjugate_one]
      _ = _ := quaternionConjugate_norm _ _
  have hnn (i : Fin d) : ‖quaternionConjugate b (cutoffCoefficientProducts w a (0, x) i) - 1‖₊ =
      ‖cutoffCoefficientProducts w a (0, x) i - 1‖₊ := NNReal.eq (hn i)
  simp only [Pi.norm_def, Pi.sub_apply, Pi.one_apply, hnn]

/-- Finite-word-system solvability with an actual distinguished-word sublevel
isolator. Arbitrarily singular initial word roots are allowed. -/
theorem coefficient_word_sublevel_solvable {ι : Type*} {m d : ℕ}
    (w : Fin m → FreeGroup (ι ⊕ Fin m)) (ρ : Fin d → FreeGroup (ι ⊕ Fin m))
    (a : ℝ → ι → SU2) (ha : ∀ i, ContDiff ℝ ∞ (fun t => (a t i : ℍ)))
    (ha0 : ∀ i, a 0 i = 1)
    (hB : (exponentMatrix (fun i => eraseCoefficients (w i))).det ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Fin m → SU2,
      coefficientWordMap w a (t, x) = 1 →
      ‖(fun i => (coefficientWordMap ρ a (t, x) i : ℍ)) - 1‖ ≠ δ) :
    ∃ x : Fin m → SU2, coefficientWordMap w a (1, x) = 1 ∧
      ‖(fun i => (coefficientWordMap ρ a (1, x) i : ℍ)) - 1‖ < δ := by
  let E := (Fin m → ℂ) × (Fin m → ℂ)
  let e : (Fin m → ℍ) ≃L[ℝ] E := quaternionTupleCoordinates
  let H : ℝ × E → ℝ × (Fin m → ℍ) := fun q => (q.1, e.symm q.2)
  have hH : ContDiff ℝ ∞ H := contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd)
  let F : ℝ × E → E := fun q => e (smoothRadialCoefficientWordMap w a (H q)) - (1, 0)
  let h : ℝ × E → ℝ := fun q => ‖cutoffCoefficientProducts ρ a (H q) - 1‖
  have hF : ContDiff ℝ 2 F := contDiff_infty.mp
    ((e.contDiff.comp ((smoothRadialCoefficientWordMap_smooth w a ha).comp hH)).sub contDiff_const) 2
  have hF0 : ∀ q, F (0, q) = splitWordMap (fun i => eraseCoefficients (w i)) q := by
    intro q
    dsimp only [F, H]
    rw [smoothRadialCoefficientWordMap_initial w a ha0]
    rfl
  have hh : Continuous h := (((cutoffCoefficientProducts_smooth ρ a ha).comp hH).continuous.sub continuous_const).norm
  have he1 : e (1 : Fin m → ℍ) = (1, 0) := by
    change quaternionTupleCoordinates
      (fun _ : Fin m => Quaternion.ofComplex (1 : ℂ)) = _
    exact quaternionTupleCoordinates_fixed 1
  have hroot (q : ℝ × E) (hq : F q = 0) :
      (∀ i, ‖e.symm q.2 i‖ = 1) ∧
      coefficientWordMap w a (q.1, fun i => normalizeQuaternion (e.symm q.2 i)) = 1 := by
    apply (smoothRadialCoefficientWordMap_eq_one_iff w a (H q)).mp
    apply e.injective
    rw [he1]
    exact sub_eq_zero.mp hq
  have hnorm (q : ℝ × E) (hq : F q = 0) : ‖q.2‖ ≤ ‖e.toContinuousLinearMap‖ := by
    have hle : ‖e.symm q.2‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      (fun i => (hroot q hq).1 i |>.le)
    calc
      ‖q.2‖ = ‖e (e.symm q.2)‖ := by rw [e.apply_symm_apply]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm q.2‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ := mul_le_of_le_one_right (norm_nonneg e.toContinuousLinearMap) hle
  have hunit (q : ℝ × E) (hq : F q = 0) :
      (fun i => ((normalizeQuaternion (e.symm q.2 i) : SU2) : ℍ)) = e.symm q.2 := by
    funext i
    have hn := (hroot q hq).1 i
    rw [normalizeQuaternion_coe_of_ne_zero (by intro hz; simp [hz] at hn), hn, inv_one, one_smul]
  have hsizeroot (q : ℝ × E) (hq : F q = 0) :
      h q = ‖(fun i => (coefficientWordMap ρ a
        (q.1, fun j => normalizeQuaternion (e.symm q.2 j)) i : ℍ)) - 1‖ := by
    dsimp only [h, H]
    conv_lhs => rw [← hunit q hq, cutoffCoefficientProducts_unitary]
  have hi : ∀ z : ℂ, ‖z‖ = 1 → ∀ q : E, h (0, (q.1, z • q.2)) = h (0, q) := by
    intro z hz q
    obtain ⟨c, hc⟩ := circle_exists_square_root z hz
    have heq : e.symm (q.1, z • q.2) =
        fun i => quaternionConjugate (circleQuaternion c) (e.symm q i) := by
      apply e.injective
      rw [e.apply_symm_apply, quaternionTupleCoordinates_conjCircle, hc, e.apply_symm_apply]
    dsimp only [h, H]
    rw [heq]
    exact cutoffCoefficientProducts_initial_size_invariant ρ a ha0 _ _
  have h1 : h (0, (1, 0)) < δ := by
    have he : e.symm (1, 0) = 1 := by rw [← he1, e.symm_apply_apply]
    have hp : coefficientWordMap ρ a (0, (1 : Fin m → SU2)) = 1 := by
      rw [coefficientWordMap_initial ρ a ha0]
      have hl : FreeGroup.lift (1 : Fin m → SU2) = 1 := by
        apply FreeGroup.ext_hom
        intro i
        simp
      funext i
      rw [hl]
      rfl
    dsimp only [h, H]
    rw [he]
    have hco : (1 : Fin m → ℍ) = fun i => ((1 : Fin m → SU2) i : ℍ) := rfl
    rw [hco, cutoffCoefficientProducts_unitary, hp]
    change ‖(1 : Fin d → ℍ) - 1‖ < δ
    simpa only [sub_self, norm_zero] using hδ
  let R : ℝ := ‖e.toContinuousLinearMap‖ + ‖((1 : Fin m → ℂ), (0 : Fin m → ℂ))‖ + 1
  obtain ⟨q, hq, hhq⟩ := localized_word_root_sublevel
    (fun i => eraseCoefficients (w i)) hB F hF hF0 h hh δ R
    (by dsimp only [R]; have hn := norm_nonneg e.toContinuousLinearMap; linarith) h1 hi
    (fun q _ hq => by dsimp only [R]; have hn := hnorm q hq; have hp := norm_nonneg ((1 : Fin m → ℂ), (0 : Fin m → ℂ)); linarith)
    (fun q ht hq => by rw [hsizeroot q hq]; exact hiso q.1 ht _ (hroot q hq).2)
  refine ⟨fun i => normalizeQuaternion (e.symm q i), (hroot (1, q) hq).2, ?_⟩
  simpa only [hsizeroot (1, q) hq] using hhq
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.SmallHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion ContDiff
/-- Squared chord length on the unit-quaternion sphere. -/
theorem su2_distance_square (a : SU2) :
    ‖(a : ℍ) - 1‖ ^ 2 = 2 - 2 * (a : ℍ).re := by
  have hu := (quaternion_mem_unitary_iff _).mp a.property
  have hs : Quaternion.normSq ((a : ℍ) - 1) = Quaternion.normSq (a : ℍ) + 1 - 2 * (a : ℍ).re := by
    simp only [Quaternion.normSq_def', Quaternion.re_sub, Quaternion.imI_sub,
      Quaternion.imJ_sub, Quaternion.imK_sub, Quaternion.re_one,
      Quaternion.imI_one, Quaternion.imJ_one, Quaternion.imK_one]
    ring
  simpa only [Quaternion.normSq_eq_norm_mul_self, hu, one_mul, sq, one_add_one_eq_two] using hs

theorem arcBlend_norm_le (a : SU2) (t : ℝ) : ‖arcBlend a t‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  have hn := (quaternion_mem_unitary_iff _).mp a.property
  calc
    _ ≤ ‖(1 - Real.smoothTransition t) • (1 : ℍ)‖ +
        ‖Real.smoothTransition t • (a : ℍ)‖ := norm_add_le _ _
    _ = 1 := by rw [norm_smul, norm_smul, norm_one, hn, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg h0]; ring

theorem small_unit_re (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) :
    0 < (a : ℍ).re ∧ (a : ℍ).re ≤ 1 := by
  have h := su2_distance_square a
  have hn := norm_nonneg ((a : ℍ) - 1)
  constructor <;> nlinarith [sq_nonneg ‖(a : ℍ) - 1‖]

theorem arcBlend_re_le (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    (a : ℍ).re ≤ (arcBlend a t).re := by
  have h := (small_unit_re a ha).2
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  simp only [arcBlend, Quaternion.re_add, Quaternion.re_smul, Quaternion.re_one, smul_eq_mul]
  nlinarith

theorem arcBlend_ne_zero (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    arcBlend a t ≠ 0 := by
  have h := (small_unit_re a ha).1.trans_le (arcBlend_re_le a ha t)
  intro he
  simp only [he, Quaternion.re_zero, lt_self_iff_false] at h

@[simp] theorem smallQuaternionArc_zero (a : SU2) : smallQuaternionArc a 0 = 1 := by
  simpa [smallQuaternionArc, arcBlend] using (normalizeQuaternion_unitary (1 : SU2))

@[simp] theorem smallQuaternionArc_one (a : SU2) : smallQuaternionArc a 1 = a := by
  simp [smallQuaternionArc, arcBlend]

theorem smallQuaternionArc_smooth (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) :
    ContDiff ℝ ∞ (fun t => (smallQuaternionArc a t : ℍ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  exact (normalizeQuaternion_coe_contDiffAt (arcBlend_ne_zero a ha t)).comp t
    (((contDiff_const.sub Real.smoothTransition.contDiff).smul contDiff_const).add
      (Real.smoothTransition.contDiff.smul contDiff_const)).contDiffAt

theorem smallQuaternionArc_distance (a : SU2) (ha : ‖(a : ℍ) - 1‖ < 1) (t : ℝ) :
    ‖(smallQuaternionArc a t : ℍ) - 1‖ ≤ ‖(a : ℍ) - 1‖ := by
  have hp : 0 < ‖arcBlend a t‖ := norm_pos_iff.mpr (arcBlend_ne_zero a ha t)
  have hre : (a : ℍ).re ≤ (smallQuaternionArc a t : ℍ).re := by
    rw [smallQuaternionArc, normalizeQuaternion_coe_of_ne_zero (arcBlend_ne_zero a ha t)]
    simp only [Quaternion.re_smul, smul_eq_mul]
    rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact (mul_le_of_le_one_right (small_unit_re a ha).1.le (arcBlend_norm_le a t)).trans
      (arcBlend_re_le a ha t)
  have h0 := su2_distance_square a
  have h1 := su2_distance_square (smallQuaternionArc a t)
  nlinarith [norm_nonneg ((a : ℍ)-1), norm_nonneg ((smallQuaternionArc a t : ℍ)-1)]

end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section SelectedEquations
variable {E : Type*} {m d : ℕ}

 theorem selectedAlphabet_other (σ : Fin m ↪ E) (e : E) (he : ∀ i, σ i ≠ e) :
    selectedAlphabet σ e = .inl e := by
  classical
  simp [selectedAlphabet, he]

 theorem selectedLabel_other (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2)
    (e : E) (he : ∀ i, σ i ≠ e) : selectedLabel σ a x e = a e := by
  rw [selectedLabel, selectedAlphabet_other σ e he]
  rfl

 theorem selectedWord_eval (σ : Fin m ↪ E) (a : E → SU2) (x : Fin m → SU2)
    (w : FreeGroup E) :
    FreeGroup.lift (Sum.elim a x) (selectedWord σ w) =
      FreeGroup.lift (selectedLabel σ a x) w := by
  have he : (FreeGroup.lift (Sum.elim a x)).comp (selectedWord σ) =
      FreeGroup.lift (selectedLabel σ a x) := by
    apply FreeGroup.ext_hom
    intro e
    simp [selectedWord, selectedLabel]
  exact congrArg (fun f : FreeGroup E →* SU2 => f w) he

 theorem selectedWord_exponents [DecidableEq E] (σ : Fin m ↪ E) (w : FreeGroup E) (j : Fin m) :
    wordExponents (eraseCoefficients (selectedWord σ w)) j = wordExponents w (σ j) := by
  classical
  have he : (FreeGroup.lift (fun i : Fin m => Multiplicative.ofAdd (if j = i then (1 : ℤ) else 0))).comp
      (eraseCoefficients.comp (selectedWord σ)) =
      FreeGroup.lift (fun e : E => Multiplicative.ofAdd (if σ j = e then (1 : ℤ) else 0)) := by
    apply FreeGroup.ext_hom
    intro e
    by_cases h : ∃ i, σ i = e
    · obtain ⟨i,rfl⟩ := h
      simp [selectedWord, eraseCoefficients, σ.injective.eq_iff]
    · have h' : ∀ i, σ i ≠ e := by simpa only [not_exists] using h
      simp [selectedWord, eraseCoefficients, selectedAlphabet_other σ e h', h' j]
  exact congrArg (fun f : FreeGroup E →* Multiplicative ℤ => (f w).toAdd) he

/-- Solve a finite, full-rank system while keeping every unselected label fixed.
The distinguished sublevel condition is the actual isolated root condition,
not a nonsingularity assumption on the roots. -/
theorem selected_word_sublevel_solvable [DecidableEq E]
    (σ : Fin m ↪ E) (w : Fin m → FreeGroup E) (ρ : Fin d → FreeGroup E)
    (a : ℝ → E → SU2) (ha : ∀ e, ContDiff ℝ ∞ (fun t => (a t e : ℍ)))
    (ha0 : ∀ e, a 0 e = 1)
    (hB : Matrix.det (fun i j => wordExponents (w i) (σ j)) ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hiso : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : Fin m → SU2,
      (∀ i, FreeGroup.lift (selectedLabel σ (a t) x) (w i) = 1) →
      ‖(fun i => (FreeGroup.lift (selectedLabel σ (a t) x) (ρ i) : ℍ)) - 1‖ ≠ δ) :
    ∃ b : E → SU2,
      (∀ e, (∀ i, σ i ≠ e) → b e = a 1 e) ∧
      (∀ i, FreeGroup.lift b (w i) = 1) ∧
      ‖(fun i => (FreeGroup.lift b (ρ i) : ℍ)) - 1‖ < δ := by
  have hb : (exponentMatrix (fun i => eraseCoefficients (selectedWord σ (w i)))).det ≠ 0 := by
    change (Matrix.det (fun i j => wordExponents (eraseCoefficients (selectedWord σ (w i))) j)) ≠ 0
    simpa only [selectedWord_exponents] using hB
  obtain ⟨x,hx,hρ⟩ := coefficient_word_sublevel_solvable
    (fun i => selectedWord σ (w i)) (fun i => selectedWord σ (ρ i)) a ha ha0 hb δ hδ
    (fun t ht x hx => by
      simp only [coefficientWordMap, selectedWord_eval]
      apply hiso t ht x
      intro i
      have hi := congrFun hx i
      simpa only [coefficientWordMap, selectedWord_eval, Pi.one_apply] using hi)
  refine ⟨selectedLabel σ (a 1) x, fun e he => selectedLabel_other σ _ x e he, ?_, ?_⟩
  · intro i
    have hi := congrFun hx i
    simpa only [coefficientWordMap, selectedWord_eval, Pi.one_apply] using hi
  · simpa only [coefficientWordMap, selectedWord_eval] using hρ

end SelectedEquations
end EilenbergGanea

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

 theorem pathProduct_conjugate_loop (v : S → Γ) (a : Γ → S → H)
    (u r : FreeGroup S) (hr : wordValue v r = 1) (g : Γ) :
    pathProduct v a (u*r*u⁻¹) g = pathProduct v a u g *
      pathProduct v a r (g * wordValue v u) * (pathProduct v a u g)⁻¹ := by
  rw [pathProduct_mul, pathProduct_mul, pathProduct_inv, map_mul, hr, mul_one]
  simp only [mul_inv_cancel_right]

 theorem pathProduct_continuous [TopologicalSpace H] [IsTopologicalGroup H]
    (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    Continuous (fun a : Γ → S → H => pathProduct v a w g) := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simpa using (continuous_const : Continuous (fun _ : Γ → S → H => (1 : H)))
  | of s =>
      simp only [pathProduct_of]
      exact continuous_apply_apply g s
  | inv_of s =>
      simp only [pathProduct_inv, pathProduct_of]
      exact (continuous_apply_apply (g * (wordValue v (FreeGroup.of s))⁻¹) s).inv
  | mul w z hw hz =>
      simp only [pathProduct_mul]
      exact (hw g).mul (hz (g * wordValue v w))

/-- The set of vertices inspected by a word is finite, independently of the
label values. No countability hypothesis on the alphabet is needed. -/
theorem pathProduct_finite_locations (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    ∃ P : Finset Γ, ∀ a b : Γ → S → H,
      (∀ p ∈ P, ∀ s, a p s = b p s) → pathProduct v a w g = pathProduct v b w g := by
  classical
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => exact ⟨∅, fun _ _ _ => by simp⟩
  | of s => exact ⟨{g}, fun a b hab => by simpa using hab g (by simp) s⟩
  | inv_of s =>
      exact ⟨{g * (wordValue v (FreeGroup.of s))⁻¹}, fun a b hab => by
        rw [pathProduct_inv, pathProduct_inv, pathProduct_of, pathProduct_of, hab _ (by simp)]⟩
  | mul w z hw hz =>
      obtain ⟨P, hP⟩ := hw g
      obtain ⟨Q, hQ⟩ := hz (g * wordValue v w)
      refine ⟨P ∪ Q, fun a b hab => ?_⟩
      rw [pathProduct_mul, pathProduct_mul, hP a b (fun p hp => hab p (Finset.mem_union_left Q hp)),
        hQ a b (fun p hp => hab p (Finset.mem_union_right P hp))]

/-- Evaluation commutes with pullback of a labeling along a group quotient,
including when different alphabet letters have the same image. -/
theorem pathProduct_pullback {D : Type*} [Group D] (q : Γ →* D)
    (v : S → Γ) (a : D → S → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v (fun p s => a (q p) s) w g = pathProduct (fun s => q (v s)) a w (q g) := by
  have hv : ∀ w : FreeGroup S, wordValue (fun s => q (v s)) w = q (wordValue v w) := by
    have he : wordValue (fun s => q (v s)) = q.comp (wordValue v) := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue]
    intro w
    exact congrArg (fun f : FreeGroup S →* D => f w) he
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s => simp
  | inv_of s => simp only [pathProduct_inv, pathProduct_of, hv, map_inv, map_mul]
  | mul w z hw hz => simp only [pathProduct_mul, hv, map_mul, hw, hz]


/-- Once every final relator has trivial transport at every vertex, normal
closure gives trivial transport on every null word, not just on a finite
collection of test loops. -/
 theorem pathProduct_trivial_of_relators (v : S → Γ) (a : Γ → S → H)
    (R : Set (FreeGroup S)) (hR : R ⊆ (wordValue v).ker)
    (hp : (wordValue v).ker = Subgroup.normalClosure R)
    (ha : ∀ r ∈ R, ∀ g, pathProduct v a r g = 1)
    (w : FreeGroup S) (hw : wordValue v w = 1) (g : Γ) : pathProduct v a w g = 1 := by
  have hrel : R ⊆ (labelLift v a).ker := by
    intro r hr
    change labelLift v a r = 1
    apply SemidirectProduct.ext
    · funext g
      exact ha r hr g
    · rw [labelLift_right]
      exact hR hr
  have hle : Subgroup.normalClosure R ≤ (labelLift v a).ker :=
    Subgroup.normalClosure_le_normal hrel
  have he : labelLift v a w = 1 := hle (by rw [← hp]; exact hw)
  change (labelLift v a w).left g = 1
  rw [he]
  rfl

 theorem pathChain_conjugate (v : S → Γ) (u r : FreeGroup S)
    (hr : wordValue v r = 1) (g : Γ) :
    pathChain v (u*r*u⁻¹) g = pathChain v r (g * wordValue v u) := by
  simp only [pathChain, pathProduct_conjugate_loop v _ u r hr g,
    toAdd_mul, toAdd_inv]
  abel

variable {R : Type*}

 theorem normalFactor_value (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (f : NormalFactor S R) :
    wordValue v (normalFactorWord r f) = 1 := by
  dsimp only [normalFactorWord]
  split_ifs <;> simp [hr]

 theorem pathChain_normalFactor (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (f : NormalFactor S R) (g : Γ) :
    pathChain v (normalFactorWord r f) g = relatorChainMap v r (normalFactorCount v f g) := by
  simp only [normalFactorWord, normalFactorCount, relatorChainMap, Finsupp.linearCombination_single]
  split_ifs with h
  · rw [pathChain_conjugate v _ _ (hr _)]; simp only [one_smul]
  · rw [pathChain_conjugate v _ _ (by simp [hr]), pathChain_inv, hr]
    simp only [inv_one, mul_one, neg_one_smul]

 theorem pathChain_normalProduct (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (l : List (NormalFactor S R)) (g : Γ) :
    pathChain v (l.map (normalFactorWord r)).prod g =
      relatorChainMap v r (l.map (fun f => normalFactorCount v f g)).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_add, pathChain_mul,
        normalFactor_value v r hr f, mul_one, pathChain_normalFactor v r hr f g, ih]

/-- The coefficient identity is an equality in the full free abelian group of
translated indexed relators. Injectivity is sufficient; no finiteness of the
relator or generator types is assumed. -/
 theorem exact_translated_relator_counts (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (hinj : Function.Injective (relatorChainMap v r))
    (z : FreeGroup S) (ρ : R) (hchain : pathChain v z 1 = pathChain v (r ρ) 1)
    (l : List (NormalFactor S R)) (he : z = (l.map (normalFactorWord r)).prod) :
    (l.map (fun f => normalFactorCount v f 1)).sum = Finsupp.single (1,ρ) 1 := by
  apply hinj
  rw [← pathChain_normalProduct v r hr, ← he, hchain]
  simp [relatorChainMap]

end EilenbergGanea

namespace EilenbergGanea
variable {Γ S H : Type*} [Group Γ] [Group H]


section CompactLabeling
variable {T I : Type*}

 omit [Group Γ] [Group H] in
 theorem mergeLabels_continuous [TopologicalSpace H] (a : Γ → S → H) :
    Continuous (fun b : Γ → T → H => mergeLabels a b) := by
  apply continuous_pi
  intro g
  apply continuous_pi
  intro s
  cases s with
  | inl s => exact continuous_const
  | inr t => exact continuous_apply_apply g t

/-- Copy arbitrary prescribed labels to a finite quotient solely on the finite
set of vertices currently being tested. This does not assert that the original
labeling is periodic or descends to a single quotient. -/
 theorem copy_labels_on_finite_set {D : Type*} [Group D] (q : Γ →* D)
    (P : Finset Γ) (hq : Set.InjOn q (P : Set Γ)) (a : Γ → S → H)
    (Allowed : H → Prop) (h1 : Allowed 1) (ha : ∀ g s, Allowed (a g s)) :
    ∃ aF : D → S → H, (∀ d s, Allowed (aF d s)) ∧ ∀ p ∈ P, ∀ s, aF (q p) s = a p s := by
  classical
  let aF : D → S → H := fun d s => if hd : ∃ p ∈ P, q p = d then a hd.choose s else 1
  refine ⟨aF, ?_, ?_⟩
  · intro d s
    dsimp [aF]
    split_ifs
    · exact ha _ _
    · exact h1
  · intro p hp s
    have he : ∃ p' ∈ P, q p' = q p := ⟨p, hp, rfl⟩
    simp only [aF, dite_eq_left he]
    have heq : he.choose = p := hq he.choose_spec.1 hp he.choose_spec.2
    rw [heq]

/-- Tychonoff compactness for all extra generators, with the original labels
fixed. The finite-quotient premise is exactly the separate finite solvability
obligation, not a periodicity assumption on the prescribed assignment. -/
 theorem compact_labeling_from_finite_quotients [Group.ResiduallyFinite Γ]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (v : S ⊕ T → Γ) (a : Γ → S → H) (w : I → FreeGroup (S ⊕ T)) (g : I → Γ)
    (K : I → Set H) (hK : ∀ i, IsClosed (K i))
    (Allowed : H → Prop) (h1 : Allowed 1) (ha : ∀ g s, Allowed (a g s))
    (hsolve : ∀ (N : FiniteIndexNormalSubgroup Γ) (J : Finset I)
      (aF : (Γ ⧸ N.toSubgroup) → S → H), (∀ d s, Allowed (aF d s)) →
      ∃ bF : (Γ ⧸ N.toSubgroup) → T → H, ∀ i ∈ J, ∀ d,
        pathProduct (fun s => QuotientGroup.mk' N.toSubgroup (v s))
          (mergeLabels aF bF) (w i) d ∈ K i) :
    ∃ b : Γ → T → H, ∀ i, pathProduct v (mergeLabels a b) (w i) (g i) ∈ K i := by
  classical
  let C : I → Set (Γ → T → H) := fun i =>
    {b | pathProduct v (mergeLabels a b) (w i) (g i) ∈ K i}
  have hc : ∀ i, IsClosed (C i) := fun i =>
    (hK i).preimage ((pathProduct_continuous v (w i) (g i)).comp (mergeLabels_continuous a))
  have hf : ∀ J : Finset I, (⋂ i ∈ J, C i).Nonempty := by
    intro J
    choose P hP using (fun i : I => pathProduct_finite_locations (H := H) v (w i) (g i))
    let V := J.biUnion P
    obtain ⟨N, hN⟩ := finite_set_quotient_injective V
    let q := QuotientGroup.mk' N.toSubgroup
    obtain ⟨aF, haF, heF⟩ := copy_labels_on_finite_set q V hN a Allowed h1 ha
    obtain ⟨bF, hbF⟩ := hsolve N J aF haF
    refine ⟨fun p t => bF (q p) t, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change pathProduct v (mergeLabels a (fun p t => bF (q p) t)) (w i) (g i) ∈ K i
    have he : pathProduct v (mergeLabels a (fun p t => bF (q p) t)) (w i) (g i) =
        pathProduct v (fun p s => mergeLabels aF bF (q p) s) (w i) (g i) := by
      apply hP i
      intro p hp s
      cases s with
      | inl s => exact (heF p (Finset.mem_biUnion.mpr ⟨i, hi, hp⟩) s).symm
      | inr t => rfl
    rw [he, pathProduct_pullback]
    exact hbF i hi (q (g i))
  obtain ⟨b, hb⟩ := CompactSpace.iInter_nonempty hc hf
  exact ⟨b, fun i => Set.mem_iInter.mp hb i⟩
end CompactLabeling
end EilenbergGanea

open scoped Quaternion
namespace EilenbergGanea

theorem su2_norm (a : SU2) : ‖(a : ℍ)‖ = 1 := by
  have h : star (a : ℍ) * (a : ℍ) = 1 := a.property.1
  have hn := congrArg norm h
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg (a : ℍ)]

/-- The two elementary estimates needed for the presentation argument, with
constants independent of the Cayley graph or any finite quotient. -/
theorem unit_product_linearization (l : List ℍ) (h : ℝ) (hh : 0 ≤ h)
    (hu : ∀ a ∈ l, ‖a‖ = 1) (hb : ∀ a ∈ l, ‖a - 1‖ ≤ h) :
    ‖l.prod - 1‖ ≤ l.length * h ∧
    ‖l.prod - 1 - (l.map (fun a => a - 1)).sum‖ ≤ (l.length : ℝ)^2 * h^2 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨hp, he⟩ := ih (fun b hm => hu b (by simp [hm])) (fun b hm => hb b (by simp [hm]))
      have hna := hu a (by simp)
      have hba := hb a (by simp)
      have hid : a * l.prod - 1 = a * (l.prod - 1) + (a - 1) := by noncomm_ring
      have hie : a * l.prod - 1 - ((a - 1) + (l.map (fun b => b - 1)).sum) =
          (a - 1) * (l.prod - 1) + (l.prod - 1 - (l.map (fun b => b - 1)).sum) := by noncomm_ring
      constructor
      · simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hid]
        calc
          _ ≤ ‖a * (l.prod - 1)‖ + ‖a - 1‖ := norm_add_le _ _
          _ = ‖l.prod - 1‖ + ‖a - 1‖ := by rw [norm_mul, hna, one_mul]
          _ ≤ (l.length + 1) * h := by nlinarith
      · simp only [List.prod_cons, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hie]
        have hn : 0 ≤ (l.length : ℝ) := Nat.cast_nonneg _
        calc
          _ ≤ ‖(a - 1) * (l.prod - 1)‖ + ‖l.prod - 1 - (l.map (fun b => b - 1)).sum‖ := norm_add_le _ _
          _ = ‖a - 1‖ * ‖l.prod - 1‖ + ‖l.prod - 1 - (l.map (fun b => b - 1)).sum‖ := by rw [norm_mul]
          _ ≤ h * (l.length * h) + (l.length : ℝ)^2 * h^2 :=
            add_le_add (mul_le_mul hba hp (norm_nonneg _) hh) he
          _ ≤ (l.length + 1)^2 * h^2 := by nlinarith [sq_nonneg h]

 theorem quaternion_commutator_bound (a b : ℍ) :
    ‖a * b - b * a‖ ≤ 2 * ‖a - 1‖ * ‖b - 1‖ := by
  have he : a * b - b * a = (a - 1) * (b - 1) - (b - 1) * (a - 1) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(a - 1) * (b - 1)‖ + ‖(b - 1) * (a - 1)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, norm_mul]; ring

 theorem su2_conjugation_error (a b : SU2) :
    ‖((a * b * a⁻¹ : SU2) : ℍ) - (b : ℍ)‖ ≤ 2 * ‖(a : ℍ) - 1‖ * ‖(b : ℍ) - 1‖ := by
  have he : ((a * b * a⁻¹ : SU2) : ℍ) - (b : ℍ) =
      ((a : ℍ) * (b : ℍ) - (b : ℍ) * (a : ℍ)) * ((a⁻¹ : SU2) : ℍ) := by
    change (a : ℍ) * (b : ℍ) * star (a : ℍ) - (b : ℍ) = _
    change _ = ((a : ℍ) * (b : ℍ) - (b : ℍ) * (a : ℍ)) * star (a : ℍ)
    rw [sub_mul, mul_assoc (b : ℍ), a.property.2, mul_one]
  rw [he, norm_mul, su2_norm, mul_one]
  exact quaternion_commutator_bound _ _

 theorem su2_inverse_distance (b : SU2) : ‖((b⁻¹ : SU2) : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  change ‖star (b : ℍ) - 1‖ = _
  calc
    _ = ‖star ((b : ℍ) - 1)‖ := by rw [star_sub, star_one]
    _ = _ := norm_star _

 theorem su2_inverse_linearization (b : SU2) :
    ‖((b⁻¹ : SU2) : ℍ) - 1 + ((b : ℍ) - 1)‖ ≤ ‖(b : ℍ) - 1‖^2 := by
  have he : ((b⁻¹ : SU2) : ℍ) - 1 + ((b : ℍ) - 1) =
      -((((b⁻¹ : SU2) : ℍ) - 1) * ((b : ℍ) - 1)) := by
    have hb : ((b⁻¹ : SU2) : ℍ) * (b : ℍ) = 1 := b.property.1
    noncomm_ring [hb]
  rw [he, norm_neg, norm_mul, su2_inverse_distance, pow_two]

/-- Replacing each displacement by its linear model introduces only the sum
of the errors. Combined with exact signed counts, this avoids any choice of
an ordering of the relator indices (which can be uncountable). -/
theorem unit_product_with_linear_models {I : Type*} (l : List I)
    (f : I → SU2) (v : I → ℍ) (h D : ℝ) (hh : 0 ≤ h)
    (hb : ∀ i ∈ l, ‖(f i : ℍ) - 1‖ ≤ h)
    (he : ∀ i ∈ l, ‖(f i : ℍ) - 1 - v i‖ ≤ D) :
    ‖((l.map (fun i => (f i : ℍ))).prod - 1) - (l.map v).sum‖ ≤
      (l.length : ℝ)^2 * h^2 + l.length * D := by
  have hp := (unit_product_linearization (l.map (fun i => (f i : ℍ))) h hh
    (by intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact su2_norm _)
    (by intro a ha; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha; exact hb i hi)).2
  simp only [List.length_map, List.map_map, Function.comp_def] at hp
  have hs : ∀ l : List I, (∀ i ∈ l, ‖(f i : ℍ) - 1 - v i‖ ≤ D) →
      ‖(l.map (fun i => (f i : ℍ) - 1)).sum - (l.map v).sum‖ ≤ l.length * D := by
    intro l he
    induction l with
    | nil => simp
    | cons i l ih =>
        have hi := he i (by simp)
        have hrest := ih (fun j hj => he j (by simp [hj]))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        have heq : (f i : ℍ) - 1 + (l.map (fun j => (f j : ℍ) - 1)).sum -
            (v i + (l.map v).sum) = ((f i : ℍ) - 1 - v i) +
              ((l.map (fun j => (f j : ℍ) - 1)).sum - (l.map v).sum) := by abel
        rw [heq]
        exact (norm_add_le _ _).trans (by linarith)

  calc
    _ ≤ ‖((l.map (fun i => (f i : ℍ))).prod - 1) - (l.map (fun i => (f i : ℍ) - 1)).sum‖ +
      ‖(l.map (fun i => (f i : ℍ) - 1)).sum - (l.map v).sum‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hp (hs l he)
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion

theorem su2_conjugation_distance (a b : SU2) :
    ‖((a * b * a⁻¹ : SU2) : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  have he : ((a * b * a⁻¹ : SU2) : ℍ) - 1 =
      (a : ℍ) * ((b : ℍ) - 1) * star (a : ℍ) := by
    change (a : ℍ) * (b : ℍ) * star (a : ℍ) - 1 = _
    rw [mul_sub, sub_mul, mul_one, a.property.2]
  rw [he, norm_mul, norm_mul, norm_star, su2_norm, one_mul, mul_one]

 theorem signedUnit_distance (b : SU2) (ε : Bool) :
    ‖(signedUnit b ε : ℍ) - 1‖ = ‖(b : ℍ) - 1‖ := by
  cases ε <;> simp [signedUnit, su2_inverse_distance]

 theorem signedUnit_error (b : SU2) (ε : Bool) :
    ‖(signedUnit b ε : ℍ) - 1 - signedDisplacement b ε‖ ≤ ‖(b : ℍ) - 1‖^2 := by
  cases ε with
  | false =>
      change ‖((b⁻¹ : SU2) : ℍ) - 1 - (-((b : ℍ) - 1))‖ ≤ _
      simpa only [sub_neg_eq_add] using su2_inverse_linearization b
  | true => simp [signedUnit, signedDisplacement]

 theorem conjugated_signedUnit_error (a b : SU2) (ε : Bool) (A h : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (ha : ‖(a : ℍ) - 1‖ ≤ A) (hb : ‖(b : ℍ) - 1‖ ≤ h) :
    ‖((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - 1 - signedDisplacement b ε‖ ≤
      2 * A * h + h^2 := by
  have he : ((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - 1 - signedDisplacement b ε =
      (((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - (signedUnit b ε : ℍ)) +
      ((signedUnit b ε : ℍ) - 1 - signedDisplacement b ε) := by abel
  rw [he]
  have hsq : ‖(b : ℍ) - 1‖^2 ≤ h^2 := by nlinarith [norm_nonneg ((b : ℍ) - 1)]
  calc
    _ ≤ ‖((a * signedUnit b ε * a⁻¹ : SU2) : ℍ) - (signedUnit b ε : ℍ)‖ +
      ‖(signedUnit b ε : ℍ) - 1 - signedDisplacement b ε‖ := norm_add_le _ _
    _ ≤ 2 * ‖(a : ℍ) - 1‖ * ‖(b : ℍ) - 1‖ + ‖(b : ℍ) - 1‖^2 := by
      simpa only [signedUnit_distance] using add_le_add (su2_conjugation_error a (signedUnit b ε)) (signedUnit_error b ε)
    _ ≤ _ := add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) hb
      (norm_nonneg _) (mul_nonneg (by positivity) hA)) hsq

 theorem relator_linear_models {I : Type*} (l : List (RelatorFactor I)) (x : I → SU2) :
    (l.map (fun r => signedDisplacement (x r.2.1) r.2.2)).sum =
      Finsupp.linearCombination ℤ (fun i => (x i : ℍ) - 1) (relatorSignedCounts l) := by
  induction l with
  | nil => simp [relatorSignedCounts]
  | cons r l ih =>
      simp only [List.map_cons, List.sum_cons, relatorSignedCounts, map_add, Finsupp.linearCombination_single]
      rw [← show Finsupp.linearCombination ℤ (fun i => (x i : ℍ) - 1)
          ((l.map (fun r => Finsupp.single r.2.1 (if r.2.2 then 1 else -1))).sum) =
          (l.map (fun r => signedDisplacement (x r.2.1) r.2.2)).sum from ih.symm]
      congr 2
      cases r.2.2 <;> simp [signedDisplacement]

/-- Exact translated counts cancel the full linear term; the remaining bound
is quadratic. The index set is arbitrary, not necessarily countable. -/
theorem relator_product_quadratic {I : Type*} (l : List (RelatorFactor I)) (x : I → SU2)
    (i₀ : I) (hc : relatorSignedCounts l = Finsupp.single i₀ 1)
    (h ε K : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hb : ∀ r ∈ l, ‖(x r.2.1 : ℍ) - 1‖ ≤ h)
    (ha : ∀ r ∈ l, ‖(r.1 : ℍ) - 1‖ ≤ K * (ε + h)) :
    ‖(l.map (fun r => (relatorFactorValue x r : ℍ))).prod - (x i₀ : ℍ)‖ ≤
      ((l.length : ℝ)^2 + l.length + 2 * l.length * K) * (ε + h) * h := by
  have hp := unit_product_with_linear_models l (relatorFactorValue x)
    (fun r => signedDisplacement (x r.2.1) r.2.2) h
    (2 * (K * (ε + h)) * h + h^2) hh
    (fun r hr => by rw [relatorFactorValue, su2_conjugation_distance, signedUnit_distance]; exact hb r hr)
    (fun r hr => conjugated_signedUnit_error r.1 (x r.2.1) r.2.2 _ h
      (mul_nonneg hK (add_nonneg hε hh)) hh (ha r hr) (hb r hr))
  rw [relator_linear_models, hc, Finsupp.linearCombination_single, one_smul] at hp
  have he : (l.map (fun r => (relatorFactorValue x r : ℍ))).prod - 1 - ((x i₀ : ℍ) - 1) =
      (l.map (fun r => (relatorFactorValue x r : ℍ))).prod - (x i₀ : ℍ) := by abel
  rw [he] at hp
  apply hp.trans
  have hlen : 0 ≤ (l.length : ℝ) := Nat.cast_nonneg _
  have hnh : 0 ≤ ((l.length : ℝ)^2 + l.length) * ε * h :=
    mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) hlen) hε) hh
  nlinarith
end EilenbergGanea

namespace EilenbergGanea

 theorem familySize_nonneg {I : Type*} (f : I → ℝ) (hf : BddAbove (Set.range f)) :
    0 ≤ familySize f := by
  apply le_csSup (hf.union bddAbove_singleton)
  exact Or.inr (Set.mem_singleton _)

 theorem le_familySize {I : Type*} (f : I → ℝ) (hf : BddAbove (Set.range f)) (i : I) :
    f i ≤ familySize f := le_csSup (hf.union bddAbove_singleton) (Or.inl (Set.mem_range_self i))

 theorem familySize_le {I : Type*} (f : I → ℝ) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i, f i ≤ c) :
    familySize f ≤ c := by
  apply csSup_le (Set.union_nonempty.mpr (Or.inr (Set.singleton_nonempty 0)))
  rintro x (⟨i, rfl⟩ | rfl)
  · exact hf i
  · exact hc

/-- The source no-threshold-crossing argument does not assume attainment of
its supremum. -/
 theorem familySize_ne_threshold {I : Type*} (f : I → ℝ)
    (hf : BddAbove (Set.range f)) (C δ η ε : ℝ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (_hη : 0 ≤ η) (hε : 0 ≤ ε) (hεη : ε ≤ η)
    (hc₁ : C * (δ + η) < 1/2) (hc₂ : C * η < δ/2)
    (hbound : ∀ i, f i ≤ C * ε + C * (familySize f + ε) * familySize f) :
    familySize f ≠ δ := by
  intro he
  have hs : familySize f ≤ C * ε + C * (familySize f + ε) * familySize f :=
    familySize_le f (by positivity [familySize_nonneg f hf]) hbound
  rw [he] at hs
  have hce : C * ε ≤ C * η := mul_le_mul_of_nonneg_left hεη hC
  have hfactor : C * (δ + ε) ≤ C * (δ + η) := mul_le_mul_of_nonneg_left (by linarith) hC
  nlinarith [mul_lt_mul_of_pos_right hc₁ hδ, mul_le_mul_of_nonneg_right hfactor hδ.le]

/-- Uniform contraction of all residual errors. This handles even an
uncountable family and does not replace the supremum by a maximum. -/
 theorem familySize_contraction {I : Type*} (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) (δ C η : ℝ) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hb : ∀ i, f i ≤ δ) (hc : C * (δ + η) < 1)
    (he : ∀ i, f i ≤ C * (familySize f + η) * familySize f) : ∀ i, f i = 0 := by
  have hbounded : BddAbove (Set.range f) := ⟨δ, by rintro _ ⟨i, rfl⟩; exact hb i⟩
  have h0 := familySize_nonneg f hbounded
  have hmax := familySize_le f hδ hb
  have hs := familySize_le f (c := C * (familySize f + η) * familySize f) (by positivity) he
  have hmul : C * (familySize f + η) ≤ C * (δ + η) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have heq : familySize f = 0 := by
    by_contra hn
    have hp : 0 < familySize f := lt_of_le_of_ne h0 (Ne.symm hn)
    have ht := mul_lt_mul_of_pos_right (lt_of_le_of_lt hmul hc) hp
    nlinarith
  intro i
  exact le_antisymm (by simpa only [heq] using le_familySize f hbounded i) (hf i)

 theorem small_thresholds_exist (C : ℝ) (hC : 1 ≤ C) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < η ∧ η < 1 ∧
      C * (δ + η) < 1/2 ∧ C * η < δ/2 := by
  have hc : 0 < C := by linarith
  let δ := 1 / (8*C)
  let η := δ / (8*C)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have he : 0 < η := by dsimp [η]; positivity
  have heδ : η < δ := by dsimp [η]; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have hcd : C * δ = 1/8 := by dsimp [δ]; field_simp
  have hce : C * η = δ/8 := by dsimp [η]; field_simp
  refine ⟨δ, η, hd, hd1, he, heδ.trans hd1, ?_, ?_⟩
  · rw [mul_add, hcd, hce]; linarith
  · rw [hce]; linarith
end EilenbergGanea


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationComparison
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
section NaturalPath
variable {Γ S H K : Type*} [Group Γ] [Group H] [Group K]

theorem pathProduct_map (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S)
    (g : Γ) (f : H →* K) :
    pathProduct v (fun p s => f (a p s)) w g = f (pathProduct v a w g) := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s => simp
  | inv_of s => simp only [pathProduct_inv, pathProduct_of, map_inv]
  | mul w z hw hz => simp only [pathProduct_mul, hw, hz, map_mul]

theorem pathSpelling_eval (v : S → Γ) (a : Γ → S → H) (w : FreeGroup S) (g : Γ) :
    FreeGroup.lift (fun i : Γ × S => a i.1 i.2) (pathSpelling v w g) =
      pathProduct v a w g := by
  symm
  simpa only [FreeGroup.lift_apply_of, pathSpelling] using
    pathProduct_map v (fun p s => FreeGroup.of (p,s)) w g
      (FreeGroup.lift (fun i : Γ × S => a i.1 i.2))

/-- Abelianizing the literal edge word gives exactly the integral edge chain. -/
theorem pathSpelling_abelianization (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    FreeGroup.lift (fun i : Γ × S => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)))
      (pathSpelling v w g) = Multiplicative.ofAdd (pathChain v w g) := by
  exact pathSpelling_eval v (fun p s => Multiplicative.ofAdd (Finsupp.single (p,s) (1 : ℤ))) w g

end NaturalPath
end EilenbergGanea

namespace EilenbergGanea
section NormalExpressions
variable {S R : Type*}

theorem normalFactor_inverse (r : R → FreeGroup S) (f : NormalFactor S R) :
    normalFactorWord r (inverseNormalFactor f) = (normalFactorWord r f)⁻¹ := by
  rcases f with ⟨u, i, ε⟩
  cases ε <;> simp [normalFactorWord, inverseNormalFactor, mul_assoc]

/-- Every element of a normal closure admits one finite product of conjugates,
including for arbitrary (possibly uncountable) index types. -/
theorem exists_normalExpression (r : R → FreeGroup S) {w : FreeGroup S}
    (hw : w ∈ Subgroup.normalClosure (Set.range r)) :
    ∃ l : List (NormalFactor S R), w = (l.map (normalFactorWord r)).prod := by
  change w ∈ Subgroup.closure (Group.conjugatesOfSet (Set.range r)) at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨y, ⟨i, rfl⟩, hy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨u, hu⟩ := isConj_iff.mp hy
      refine ⟨[(u,i,true)], ?_⟩
      simpa [normalFactorWord] using hu.symm
  | one => exact ⟨[], by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨l, rfl⟩ := ihx
      obtain ⟨k, rfl⟩ := ihy
      exact ⟨l ++ k, by simp⟩
  | inv x hx ih =>
      obtain ⟨l, rfl⟩ := ih
      refine ⟨(l.map inverseNormalFactor).reverse, ?_⟩
      simp only [List.map_reverse, List.prod_inv_reverse, List.map_map]
      congr 2
      apply List.map_congr_left
      intro f _
      exact (normalFactor_inverse r f).symm

end NormalExpressions
end EilenbergGanea

namespace EilenbergGanea
section WordNorm
open scoped Quaternion
variable {Γ S : Type*} [Group Γ]

theorem su2_mul_distance (a b : SU2) :
    ‖((a*b : SU2) : ℍ) - 1‖ ≤ ‖(a : ℍ) - 1‖ + ‖(b : ℍ) - 1‖ := by
  have he : ((a*b : SU2) : ℍ) - 1 = ((a : ℍ) - 1) * (b : ℍ) + ((b : ℍ) - 1) := by
    change (a : ℍ) * (b : ℍ) - 1 = _
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, su2_norm, mul_one])

/-- A finite control set for a word, uniform over all base vertices and all
labelings. Both the set and the coefficient are chosen before any quotient. -/
theorem finite_word_control_universal (w : FreeGroup S) :
    ∃ (P : Finset S) (n : ℕ), ∀ {D : Type u} [Group D] (v : S → D) (ε : ℝ), 0 ≤ ε → ∀ (a : D → S → SU2),
      (∀ g, ∀ s ∈ P, ‖(a g s : ℍ) - 1‖ ≤ ε) →
      ∀ g, ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ ≤ n * ε := by
  classical
  induction w using OAI.freeGroupInductionOn with
  | one => exact ⟨∅, 0, fun v ε _ a _ g => by simp⟩
  | of s =>
      refine ⟨{s}, 1, fun v ε _ a ha g => ?_⟩
      simpa using ha g s (by simp)
  | inv_of s ih =>
      obtain ⟨P, n, hn⟩ := ih
      refine ⟨P, n, fun v ε hε a ha g => ?_⟩
      rw [pathProduct_inv, su2_inverse_distance]
      exact hn v ε hε a ha _
  | mul w z hw hz =>
      obtain ⟨P, n, hn⟩ := hw
      obtain ⟨Q, m, hm⟩ := hz
      refine ⟨P ∪ Q, n+m, fun v ε hε a ha g => ?_⟩
      rw [pathProduct_mul]
      calc
        _ ≤ ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ +
            ‖((pathProduct v a z (g * wordValue v w) : SU2) : ℍ) - 1‖ := su2_mul_distance _ _
        _ ≤ n * ε + m * ε := add_le_add
          (hn v ε hε a (fun p s hs => ha p s (Finset.mem_union_left _ hs)) _)
          (hm v ε hε a (fun p s hs => ha p s (Finset.mem_union_right _ hs)) _)
        _ = _ := by push_cast; ring

end WordNorm
end EilenbergGanea

namespace EilenbergGanea
section EvaluatedNormalExpression
open scoped Quaternion
variable {Γ D S R : Type*} [Group Γ] [Group D]

theorem wordValue_quotient (v : S → Γ) (q : Γ →* D) (w : FreeGroup S) :
    wordValue (fun s => q (v s)) w = q (wordValue v w) := by
  have he : wordValue (fun s => q (v s)) = q.comp (wordValue v) := by
    apply FreeGroup.ext_hom
    intro s
    simp [wordValue]
  exact congrArg (fun f : FreeGroup S →* D => f w) he

theorem evaluatedNormalFactor_value (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (f : NormalFactor S R) (g : Γ) :
    relatorFactorValue (fun i : Γ × R => pathProduct v a (r i.2) i.1)
      (evaluatedNormalFactor v a f g) = pathProduct v a (normalFactorWord r f) g := by
  rcases f with ⟨u, i, σ⟩
  cases σ <;>
    simp [relatorFactorValue, evaluatedNormalFactor, signedUnit, normalFactorWord,
      pathProduct_conjugate_loop, hr, pathProduct_inv]

theorem pathProduct_normalProduct (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (l : List (NormalFactor S R)) (g : Γ) :
    ((l.map (fun f => evaluatedNormalFactor v a f g)).map
      (relatorFactorValue (fun i : Γ × R => pathProduct v a (r i.2) i.1))).prod =
      pathProduct v a (l.map (normalFactorWord r)).prod g := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, pathProduct_mul,
        normalFactor_value v r hr, mul_one, evaluatedNormalFactor_value v a r hr, ih]

/-- Exact translated signed counts are preserved upon passage to every quotient.
No flatness, finiteness, or injectivity of the quotient is used. -/
theorem quotient_evaluated_counts (v : S → Γ) (q : Γ →* D)
    (a : D → S → SU2) (l : List (NormalFactor S R)) (ρ : R)
    (hc : (l.map (fun f => normalFactorCount v f 1)).sum = Finsupp.single (1,ρ) 1)
    (g : D) :
    relatorSignedCounts (l.map (fun f => evaluatedNormalFactor (fun s => q (v s)) a f g)) =
      Finsupp.single (g,ρ) 1 := by
  let T : ((Γ × R) →₀ ℤ) →ₗ[ℤ] ((D × R) →₀ ℤ) :=
    Finsupp.lmapDomain ℤ ℤ (fun i => (g * q i.1, i.2))
  have hs : relatorSignedCounts
      (l.map (fun f => evaluatedNormalFactor (fun s => q (v s)) a f g)) =
      T (l.map (fun f => normalFactorCount v f 1)).sum := by
    simp only [relatorSignedCounts, List.map_map, map_list_sum]
    congr 1
    apply List.map_congr_left
    intro f _
    simp [T, evaluatedNormalFactor, normalFactorCount, wordValue_quotient]
  rw [hs, hc]
  simp [T]

/-- The actual relator expression, evaluated by arbitrary edge labels on a
quotient graph, has the uniform quadratic error predicted by its exact chain
counts. -/
theorem normalExpression_quadratic (v : S → Γ) (q : Γ →* D)
    (a : D → S → SU2) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (z : FreeGroup S)
    (l : List (NormalFactor S R)) (he : z = (l.map (normalFactorWord r)).prod)
    (ρ : R) (hc : (l.map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,ρ) 1)
    (h ε K : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hb : ∀ f ∈ l, ∀ g, ‖((pathProduct (fun s => q (v s)) a (r f.2.1) g : SU2) : ℍ) - 1‖ ≤ h)
    (ha : ∀ f ∈ l, ∀ g, ‖((pathProduct (fun s => q (v s)) a f.1 g : SU2) : ℍ) - 1‖ ≤ K * (ε+h))
    (g : D) :
    ‖((pathProduct (fun s => q (v s)) a z g : SU2) : ℍ) -
      ((pathProduct (fun s => q (v s)) a (r ρ) g : SU2) : ℍ)‖ ≤
      ((l.length : ℝ)^2 + l.length + 2*l.length*K) * (ε+h)*h := by
  let v' := fun s => q (v s)
  let L := l.map (fun f => evaluatedNormalFactor v' a f g)
  let x := fun i : D × R => pathProduct v' a (r i.2) i.1
  have hp := relator_product_quadratic L x (g,ρ)
    (quotient_evaluated_counts v q a l ρ hc g) h ε K hh hε hK
    (by intro f hf; obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hf; exact hb b hb' _)
    (by intro f hf; obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hf; exact ha b hb' _)
  have hprod : (L.map (fun f => (relatorFactorValue x f : ℍ))).prod =
      ((pathProduct v' a z g : SU2) : ℍ) := by
    have hz := pathProduct_normalProduct v' a r
      (fun i => by simp [v', wordValue_quotient, hr]) l g
    rw [← he] at hz
    have hco (ll : List SU2) : ((ll.prod : SU2) : ℍ) = (ll.map (fun b : SU2 => (b : ℍ))).prod := by
      induction ll with
      | nil => rfl
      | cons b ll ih => simp only [List.prod_cons, Submonoid.coe_mul, List.map_cons, ih]
    have hz' := congrArg (fun x : SU2 => (x : ℍ)) hz
    rw [hco] at hz'
    simpa only [L, x, List.map_map, Function.comp_def] using hz' 
  simpa only [hprod, L, List.length_map, x, v'] using hp

end EvaluatedNormalExpression
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section NormalProductSize
variable {Γ S R : Type*} [Group Γ]

 theorem normalFactor_product_distance (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (f : NormalFactor S R) (g : Γ) :
    ‖((pathProduct v a (normalFactorWord r f) g : SU2) : ℍ) - 1‖ =
      ‖((pathProduct v a (r f.2.1) (g * wordValue v f.1) : SU2) : ℍ) - 1‖ := by
  rw [← evaluatedNormalFactor_value v a r hr]
  exact (su2_conjugation_distance _ _).trans (signedUnit_distance _ _)

/-- Unlike the quadratic estimate, this linear bound needs no information
whatever about the conjugating words. It controls the finitely many auxiliary
loop labels before any bound on the conjugators is obtained. -/
theorem normalProduct_distance (v : S → Γ) (a : Γ → S → SU2)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (l : List (NormalFactor S R)) (h : ℝ)
    (hb : ∀ f ∈ l, ∀ g, ‖((pathProduct v a (r f.2.1) g : SU2) : ℍ) - 1‖ ≤ h)
    (g : Γ) :
    ‖((pathProduct v a (l.map (normalFactorWord r)).prod g : SU2) : ℍ) - 1‖ ≤ l.length * h := by
  induction l with
  | nil => simp
  | cons f l ih =>
      simp only [List.map_cons, List.prod_cons, pathProduct_mul, normalFactor_value v r hr, mul_one]
      calc
        _ ≤ ‖((pathProduct v a (normalFactorWord r f) g : SU2) : ℍ) - 1‖ +
            ‖((pathProduct v a (l.map (normalFactorWord r)).prod g : SU2) : ℍ) - 1‖ := su2_mul_distance _ _
        _ ≤ h + l.length * h := add_le_add
          (by rw [normalFactor_product_distance v a r hr]; exact hb f (by simp) _)
          (ih (fun b hb' => hb b (by simp [hb'])))
        _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

end NormalProductSize
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section FiniteControl
variable {S T H : Type*} [Group H]

 theorem pathProduct_map_alphabet {Γ : Type*} [Group Γ]
    (f : S → T) (v : T → Γ) (a : Γ → T → H) (w : FreeGroup S) (g : Γ) :
    pathProduct v a (FreeGroup.map f w) g =
      pathProduct (v ∘ f) (fun p s => a p (f s)) w g := by
  have he : (labelLift v a).comp (FreeGroup.map f) =
      labelLift (v ∘ f) (fun p s => a p (f s)) := by
    apply FreeGroup.ext_hom
    intro s
    simp [labelLift]
  exact congrArg (fun l : FreeGroup S →* ((Γ → H) ⋊[functionShift Γ H] Γ) => (l w).left g) he

 theorem finite_word_family_control (W : Finset (FreeGroup S)) :
    ∃ (P : Finset S) (n : ℕ), ∀ w ∈ W,
      ∀ {D : Type u} [Group D] (v : S → D) (ε : ℝ), 0 ≤ ε → ∀ (a : D → S → SU2),
      (∀ g, ∀ s ∈ P, ‖(a g s : ℍ) - 1‖ ≤ ε) →
      ∀ g, ‖((pathProduct v a w g : SU2) : ℍ) - 1‖ ≤ n * ε := by
  classical
  induction W using Finset.induction_on with
  | empty => exact ⟨∅,0, by simp⟩
  | @insert w W _ ih =>
      obtain ⟨P,n,hn⟩ := finite_word_control_universal w
      obtain ⟨Q,m,hm⟩ := ih
      refine ⟨P ∪ Q, n+m, ?_⟩
      intro z hz D _ v ε hε a ha g
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact (hn v ε hε a (fun p s hs => ha p s (Finset.mem_union_left _ hs)) g).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n m) hε)
      · exact (hm z hz v ε hε a (fun p s hs => ha p s (Finset.mem_union_right _ hs)) g).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left m n) hε)

end FiniteControl
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion BigOperators
section UniformComparison
variable {Γ S T Z R : Type*} [Group Γ] [Fintype Z]

/-- All constants and all ordinary relators needed by the quadratic estimate
are chosen before the group quotient and before the edge labels. The normal
expressions are literal finite words, while the ambient alphabets may have any
cardinality. -/
theorem finite_normal_comparison
    (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T))
    (hr : ∀ i, wordValue v (r i) = 1) (z : Z → FreeGroup S)
    (lz : Z → List (NormalFactor (S ⊕ T) (Z ⊕ R)))
    (lt : T → List (NormalFactor (S ⊕ T) (Z ⊕ R)))
    (hz : ∀ i, FreeGroup.map Sum.inl (z i) = ((lz i).map (normalFactorWord r)).prod)
    (ht : ∀ t, FreeGroup.of (Sum.inr t) = ((lt t).map (normalFactorWord r)).prod)
    (hc : ∀ i, ((lz i).map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,Sum.inl i) 1) :
    ∃ (A : Finset R) (C : ℝ), 1 ≤ C ∧
      ∀ {F : Type u} [Group F] (q : Γ →* F) (a : F → S ⊕ T → SU2)
        (ε h : ℝ), 0 ≤ ε → 0 ≤ h →
      (∀ g s, ‖(a g (.inl s) : ℍ) - 1‖ ≤ ε) →
      (∀ i ∈ A, ∀ g, pathProduct (fun s => q (v s)) a (r (.inr i)) g = 1) →
      (∀ i g, ‖((pathProduct (fun s => q (v s)) a (r (.inl i)) g : SU2) : ℍ) - 1‖ ≤ h) →
      ∀ i g,
        ‖((pathProduct (fun s => q (v s)) a (FreeGroup.map Sum.inl (z i)) g : SU2) : ℍ) -
          ((pathProduct (fun s => q (v s)) a (r (.inl i)) g : SU2) : ℍ)‖ ≤ C * (ε+h)*h ∧
        ‖((pathProduct (fun s => q (v s)) a (FreeGroup.map Sum.inl (z i)) g : SU2) : ℍ) - 1‖ ≤ C*ε := by
  classical
  let W : Finset (FreeGroup (S ⊕ T)) := Finset.univ.biUnion fun i =>
    (lz i).toFinset.image Prod.fst
  obtain ⟨P,n,hn⟩ := finite_word_family_control W
  obtain ⟨_,nz,hnz⟩ := finite_word_family_control (Finset.univ.image z)
  let U : Finset (Z ⊕ R) :=
    (Finset.univ.biUnion fun i => (lz i).toFinset.image (fun f => f.2.1)) ∪
    (P.toRight.biUnion fun t => (lt t).toFinset.image (fun f => f.2.1))
  let M : ℕ := 1 + P.toRight.sup (fun t => (lt t).length)
  let N : ℕ := Finset.univ.sup (fun i => (lz i).length)
  let K : ℝ := n * M
  let C : ℝ := 1 + nz + (N : ℝ)^2 + N + 2*N*K
  have hM : 1 ≤ M := Nat.le_add_right 1 _
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcoef : 0 ≤ (2 : ℝ)*N*K := by positivity
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hnzr : (0 : ℝ) ≤ nz := Nat.cast_nonneg _
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N : ℝ)]
  have hnzC : (nz : ℝ) ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N : ℝ)]
  have hNC : (N : ℝ)^2 + N + 2*N*K ≤ C := by dsimp [C]; linarith
  refine ⟨U.toRight,C,hC,?_⟩
  intro F _ q a ε h hε hh ha hordinary hdist i g
  let v' := fun s => q (v s)
  have hr' (j) : wordValue v' (r j) = 1 := by simp [v', wordValue_quotient, hr]
  have hused (j : Z ⊕ R) (hj : j ∈ U) (p : F) :
      ‖((pathProduct v' a (r j) p : SU2) : ℍ)-1‖ ≤ h := by
    rcases j with j | j
    · exact hdist j p
    · rw [hordinary j (Finset.mem_toRight.mpr hj) p]
      simpa using hh
  have hZ (j : Z) (f : NormalFactor (S ⊕ T) (Z ⊕ R)) (hf : f ∈ lz j) (p : F) :
      ‖((pathProduct v' a (r f.2.1) p : SU2) : ℍ)-1‖ ≤ h := by
    apply hused _ _ p
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩)
  have hT (t : T) (htP : t ∈ P.toRight) (p : F) : ‖(a p (.inr t) : ℍ)-1‖ ≤ M*h := by
    have hb := normalProduct_distance v' a r hr' (lt t) h
      (fun f hf p => hused _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨t,htP,Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩)) p) p
    rw [← ht t, pathProduct_of] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (lt t).length ≤ M from
        (Finset.le_sup (f := fun t => (lt t).length) htP).trans (Nat.le_add_left _ 1))) hh)
  have hsize : 0 ≤ (M : ℝ)*(ε+h) := mul_nonneg (Nat.cast_nonneg _) (add_nonneg hε hh)
  have hP (p : F) (s : S ⊕ T) (hs : s ∈ P) : ‖(a p s : ℍ)-1‖ ≤ M*(ε+h) := by
    rcases s with s | t
    · calc
        _ ≤ ε := ha p s
        _ ≤ (M : ℝ)*ε := by nlinarith
        _ ≤ (M : ℝ)*(ε+h) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    · exact (hT t (Finset.mem_toRight.mpr hs) p).trans
        (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  have hconj (j : Z) (f : NormalFactor (S ⊕ T) (Z ⊕ R)) (hf : f ∈ lz j) (p : F) :
      ‖((pathProduct v' a f.1 p : SU2) : ℍ)-1‖ ≤ K*(ε+h) := by
    have hW : f.1 ∈ W := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,rfl⟩⟩
    simpa only [K, mul_assoc] using hn f.1 hW v' _ hsize a hP p
  constructor
  · have hb := normalExpression_quadratic v q a r hr _ (lz i) (hz i) (.inl i) (hc i)
      h ε K hh hε hK (hZ i) (hconj i) g
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hh
    apply mul_le_mul_of_nonneg_right _ (add_nonneg hε hh)
    have hl : ((lz i).length : ℝ) ≤ N := by
      exact_mod_cast (show (lz i).length ≤ N from
        Finset.le_sup (f := fun j => (lz j).length) (Finset.mem_univ i))
    have h0 : (0 : ℝ) ≤ (lz i).length := Nat.cast_nonneg _
    have hn0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hp := mul_le_mul_of_nonneg_right hl hK
    nlinarith [sq_nonneg ((N : ℝ) - (lz i).length)]
  · rw [pathProduct_map_alphabet]
    exact (hnz (z i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      _ ε hε (fun p s => a p (.inl s)) (fun p s _ => ha p s) g).trans
      (mul_le_mul_of_nonneg_right hnzC hε)

end UniformComparison
end EilenbergGanea



namespace EilenbergGanea
open scoped BigOperators

/-- A finite family with an integral left inverse has a nonzero square minor.
Expansion of the alternating determinant avoids a flatness or rationalization
assumption, and also covers the empty row family. -/
theorem nonsingular_minor_of_left_inverse {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (v : J → I → ℤ) (b : I → J → ℤ)
    (hb : ∀ i, ∑ j, b i j • v j = Pi.single i 1) :
    ∃ e : I → J, Function.Injective e ∧ Matrix.det (fun i k => v (e i) k) ≠ 0 := by
  classical
  have hex : ∃ e : I → J, Matrix.det (fun i k => v (e i) k) ≠ 0 := by
    by_contra h
    push Not at h
    let D := (Matrix.detRowAlternating : (I → ℤ) [⋀^I]→ₗ[ℤ] ℤ).toMultilinearMap
    have hz : D (fun i => ∑ j, b i j • v j) = 0 := by
      rw [D.map_sum]
      apply Finset.sum_eq_zero
      intro e _
      rw [D.map_smul_univ]
      change (∏ i, b i (e i)) • Matrix.det (fun i k => v (e i) k) = 0
      rw [h]
      exact smul_zero _
    have he : (fun i => ∑ j, b i j • v j) = (1 : Matrix I I ℤ) := by
      ext i k
      rw [show (∑ j, b i j • v j) = Pi.single i 1 from hb i]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [he] at hz
    change Matrix.det (1 : Matrix I I ℤ) = 0 at hz
    simp at hz
  obtain ⟨e, he⟩ := hex
  refine ⟨e, ?_, he⟩
  intro i j hij
  by_contra hne
  exact he (Matrix.det_zero_of_row_eq hne (by simp [hij]))

/-- The same finite-minor statement for an arbitrary direct sum. All supports
are retained, but only the finite union needed by the chosen rows is used. -/
theorem finitely_supported_split_family_minor {I S : Type*} [Fintype I] [DecidableEq I]
    (v : I → S →₀ ℤ) (B : (S →₀ ℤ) →ₗ[ℤ] (I → ℤ))
    (hB : ∀ i, B (v i) = Pi.single i 1) :
    ∃ e : I → S, Function.Injective e ∧ Matrix.det (fun i j => v i (e j)) ≠ 0 := by
  classical
  let P : Finset S := Finset.univ.biUnion (fun i => (v i).support)
  have hP (i : I) : (v i).support ⊆ P := by
    intro s hs
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
  have hexpand (i : I) : v i = ∑ p : P, (v i) p.1 • (Finsupp.single p.1 (1 : ℤ)) := by
    rw [Finset.sum_coe_sort P (fun p => (v i) p • (Finsupp.single p (1 : ℤ)))]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [← Finsupp.sum_of_support_subset (v i) (hP i)
      (fun p t => Finsupp.single p t) (by intro p _; simp)]
    exact (Finsupp.sum_single (v i)).symm
  let w : P → I → ℤ := fun p j => v j p.1
  let b : I → P → ℤ := fun i p => B (Finsupp.single p.1 1) i
  have hb (i : I) : ∑ p, b i p • w p = Pi.single i 1 := by
    ext j
    have hi := congrFun (hB j) i
    rw [hexpand j, map_sum] at hi
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
    simpa only [b, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm,
      Pi.single_apply, eq_comm] using hi
  obtain ⟨e, he, hd⟩ := nonsingular_minor_of_left_inverse w b hb
  refine ⟨fun i => (e i).1, ?_, ?_⟩
  · intro i j hij
    exact he (Subtype.ext hij)
  · have ht := Matrix.det_transpose (fun i j => v i (e j).1)
    exact fun h => hd (ht.trans h)

/-- Every finite subfamily of an arbitrary integral basis has a nonsingular
finite coordinate minor, including when the ambient basis is uncountable. -/
theorem basis_subfamily_minor {I R S : Type*} [Fintype I] [DecidableEq I]
    (A : (R →₀ ℤ) ≃ₗ[ℤ] (S →₀ ℤ)) (j : I ↪ R) :
    ∃ e : I → S, Function.Injective e ∧
      Matrix.det (fun i k => A (Finsupp.single (j i) 1) (e k)) ≠ 0 := by
  classical
  let B : (S →₀ ℤ) →ₗ[ℤ] (I → ℤ) :=
    LinearMap.pi fun i => (Finsupp.lapply (j i)).comp A.symm.toLinearMap
  apply finitely_supported_split_family_minor (fun i => A (Finsupp.single (j i) 1)) B
  intro i
  ext k
  simp [B, Pi.single_apply, Finsupp.single_apply, j.injective.eq_iff, eq_comm]

end EilenbergGanea

namespace EilenbergGanea
section ChainProjection
variable {Γ D S T R : Type*} [Group Γ] [Group D]

theorem pathChain_translate (v : S → Γ) (w : FreeGroup S) (g h : Γ) :
    translateChains g (pathChain v w h) = pathChain v w (g*h) := by
  induction w using OAI.freeGroupInductionOn generalizing h with
  | one => simp
  | of s => simp
  | inv_of s ih => simp only [pathChain_inv, map_neg, ih, mul_assoc]
  | mul w z hw hz => simp only [pathChain_mul, map_add, hw, hz, mul_assoc]

theorem pathChain_quotient (v : S → Γ) (q : Γ →* D) (w : FreeGroup S) (g : Γ) :
    quotientChains q (pathChain v w g) = pathChain (fun s => q (v s)) w (q g) := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp
  | of s => simp
  | inv_of s ih => simp only [pathChain_inv, map_neg, ih, map_mul, map_inv, wordValue_quotient]
  | mul w z hw hz => simp only [pathChain_mul, map_add, hw, hz, map_mul, wordValue_quotient]

theorem projectExtraChains_translate (g : Γ) (c : BasedChains Γ (S ⊕ T)) :
    projectExtraChains (translateChains g c) = translateChains g (projectExtraChains c) := by
  have he : (projectExtraChains (Γ := Γ) (S := S) (T := T)).comp (translateChains g) =
      (translateChains g).comp projectExtraChains := by
    apply Finsupp.lhom_ext
    rintro ⟨h, s | t⟩ n <;> simp
  exact LinearMap.congr_fun he c

theorem projectExtraChains_quotient (q : Γ →* D) (c : BasedChains Γ (S ⊕ T)) :
    projectExtraChains (quotientChains q c) = quotientChains q (projectExtraChains c) := by
  have he : (projectExtraChains (Γ := D) (S := S) (T := T)).comp (quotientChains q) =
      (quotientChains q).comp projectExtraChains := by
    apply Finsupp.lhom_ext
    rintro ⟨h, s | t⟩ n <;> simp
  exact LinearMap.congr_fun he c

theorem extraRelatorMap_equivariant (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T)) :
    ChainsEquivariant (extraRelatorMap v r) := by
  intro g c
  have he : (extraRelatorMap v r).comp (translateChains g) =
      (translateChains g).comp (extraRelatorMap v r) := by
    apply Finsupp.lhom_ext
    rintro ⟨h,i⟩ n
    simp only [LinearMap.comp_apply, translateChains_single, extraRelatorMap_single, map_smul]
    rw [← projectExtraChains_translate, pathChain_translate]
  exact LinearMap.congr_fun he c

theorem extraRelatorMap_quotientMatrix (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (q : Γ →* D) :
    quotientMatrix q (extraRelatorMap v r) = extraRelatorMap (fun s => q (v s)) r := by
  apply Finsupp.lhom_ext
  rintro ⟨g,i⟩ n
  simp only [quotientMatrix_single, extraRelatorMap_single, one_smul]
  rw [← projectExtraChains_quotient, pathChain_quotient,
    ← projectExtraChains_translate, pathChain_translate, map_one, mul_one]

/-- The exponent minor used on a finite quotient is a consequence of the
ordinary projected boundary isomorphism itself; no independent rank hypothesis
and no unproved flatness claim is inserted. -/
theorem finite_extra_boundary_minor {I : Type*} [Fintype I] [DecidableEq I]
    (v : S ⊕ T → Γ) (r : R → FreeGroup (S ⊕ T))
    (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
    (hA : A.toLinearMap = extraRelatorMap v r) (q : Γ →* D) (j : I ↪ D × R) :
    ∃ e : I → D × T, Function.Injective e ∧
      Matrix.det (fun i k => projectExtraChains
        (pathChain (fun s => q (v s)) (r (j i).2) (j i).1) (e k)) ≠ 0 := by
  let B := quotientChainEquiv q A (by rw [hA]; exact extraRelatorMap_equivariant v r)
  obtain ⟨e,he,hd⟩ := basis_subfamily_minor B j
  refine ⟨e,he,?_⟩
  have hB : B.toLinearMap = extraRelatorMap (fun s => q (v s)) r := by
    change quotientMatrix q A.toLinearMap = _
    rw [hA, extraRelatorMap_quotientMatrix]
  have hb (i : I) : B (Finsupp.single (j i) 1) = projectExtraChains
        (pathChain (fun s => q (v s)) (r (j i).2) (j i).1) := by
    change B.toLinearMap _ = _
    rw [hB]
    rcases j i with ⟨g,k⟩
    simp
  simpa only [hb] using hd

end ChainProjection
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section FiniteQuotientEquations
variable {Γ F S T R Z : Type*} [Group Γ] [Group F]

/-- The exponent of a literal edge is exactly its cellular path coefficient. -/
theorem pathSpelling_exponent [DecidableEq F] [DecidableEq S]
    (v : S → F) (w : FreeGroup S) (g : F) (e : F × S) :
    wordExponents (pathSpelling v w g) e = pathChain v w g e := by
  have he : (FreeGroup.lift (fun i : F × S =>
      Multiplicative.ofAdd (if e = i then (1 : ℤ) else 0))) =
      (Finsupp.applyAddHom e).toMultiplicative.comp
        (FreeGroup.lift (fun i : F × S => Multiplicative.ofAdd (Finsupp.single i (1 : ℤ)))) := by
    apply FreeGroup.ext_hom
    intro i
    simp [Finsupp.single_apply, eq_comm]
  simp only [wordExponents, he, MonoidHom.comp_apply, pathSpelling_abelianization]
  rfl

omit [Group F] in
/-- Projection to the extra alphabet really deletes only the prescribed edges. -/
theorem projectExtraChains_apply (c : BasedChains F (S ⊕ T)) (e : F × T) :
    projectExtraChains c e = c (e.1, Sum.inr e.2) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single p n =>
      rcases p with ⟨g,s | t⟩
      · simp
      · simp [Finsupp.single_apply, Prod.ext_iff]

/-- Sup norm agrees with the zero-normalized supremum, including an empty index. -/
theorem norm_eq_familySize {I : Type*} [Fintype I] (f : I → ℍ) :
    ‖f‖ = familySize (fun i => ‖f i‖) := by
  have hb : BddAbove (Set.range (fun i => ‖f i‖)) := Set.finite_range _ |>.bddAbove
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (familySize_nonneg _ hb)).mpr
      (fun i => le_familySize _ hb i)
  · exact familySize_le _ (norm_nonneg _) (fun i => norm_le_pi_norm f i)

/-- Reindexing does not change the actual supremum norm of a finite word family. -/
theorem norm_comp_equiv {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) (f : J → ℍ) :
    ‖fun i => f (e i)‖ = ‖f‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm f (e i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => by
      simpa using norm_le_pi_norm (fun i => f (e i)) (e.symm j)

end FiniteQuotientEquations
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section FiniteQuotientSolvability
variable {F S T R Z : Type*} [Group F] [Fintype F] [Fintype Z]

/-- The full finite quotient step. All coefficients on the prescribed alphabet
are retained exactly, not merely up to a small perturbation. -/
theorem finite_quotient_comparison_solvable
    (v : S ⊕ T → F) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
    (A : Finset R) (B : Finset R) (hAB : A ⊆ B)
    (Q : BasedChains F R ≃ₗ[ℤ] BasedChains F T)
    (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i)))
    (C δ η : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1)
    (hc₁ : C*(δ+η) < 1/2) (hc₂ : C*η < δ/2)
    (hcomp : ∀ (b : F → S ⊕ T → SU2) (h : ℝ), 0 ≤ h →
      (∀ g s, ‖(b g (.inl s) : ℍ)-1‖ ≤ η) →
      (∀ i ∈ A, ∀ g, pathProduct (H := SU2) v b (r (.inr i)) g = 1) →
      (∀ i g, ‖(pathProduct (H := SU2) v b (r (.inl i)) g : ℍ)-1‖ ≤ h) →
      ∀ i g,
        ‖(pathProduct (H := SU2) v b (FreeGroup.map Sum.inl (z i)) g : ℍ) -
          (pathProduct (H := SU2) v b (r (.inl i)) g : ℍ)‖ ≤ C*(η+h)*h ∧
        ‖(pathProduct (H := SU2) v b (FreeGroup.map Sum.inl (z i)) g : ℍ)-1‖ ≤ C*η)
    (a : F → S → SU2) (ha : ∀ g s, ‖(a g s : ℍ)-1‖ < η) :
    ∃ b : F → T → SU2,
      (∀ i ∈ B, ∀ g, pathProduct (H := SU2) v (mergeLabels a b) (r (.inr i)) g = 1) ∧
      (∀ i g, ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)-1‖ < δ) := by
  classical
  let I := F × ↥B
  let J := F × Z
  let eI : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let j : Fin (Fintype.card I) ↪ F × R :=
    ⟨fun k => ((eI k).1, (eI k).2.val), fun k l h => by
      apply eI.injective
      exact Prod.ext (congrArg (fun p : F × R => p.1) h) (Subtype.ext (congrArg (fun p : F × R => p.2) h))⟩
  obtain ⟨e,he,hd⟩ := finite_extra_boundary_minor v (fun i => r (.inr i)) Q hQ
    (MonoidHom.id F) j
  let σ : Fin (Fintype.card I) ↪ F × (S ⊕ T) :=
    ⟨fun k => ((e k).1, .inr (e k).2), fun k l h =>
      he (Prod.ext (congrArg (fun p : F × (S ⊕ T) => p.1) h)
        (Sum.inr_injective (congrArg (fun p : F × (S ⊕ T) => p.2) h)))⟩
  let w : Fin (Fintype.card I) → FreeGroup (F × (S ⊕ T)) :=
    fun k => pathSpelling v (r (.inr (eI k).2.val)) (eI k).1
  let ρ : Fin (Fintype.card J) → FreeGroup (F × (S ⊕ T)) :=
    fun k => pathSpelling v (r (.inl (eJ k).2)) (eJ k).1
  have hdet : Matrix.det (fun i k => wordExponents (w i) (σ k)) ≠ 0 := by
    simp only [projectExtraChains_apply, MonoidHom.id_apply] at hd
    simp only [w, pathSpelling_exponent]
    exact hd
  let base : F × (S ⊕ T) → SU2 := fun p => Sum.elim (a p.1) (fun _ => 1) p.2
  have hbase (p) : ‖(base p : ℍ)-1‖ < 1 := by
    rcases p with ⟨g,s | t⟩
    · exact (ha g s).trans hη1
    · simp [base]
  let arc : ℝ → F × (S ⊕ T) → SU2 := fun t p => smallQuaternionArc (base p) t
  let L (t : ℝ) (x : Fin (Fintype.card I) → SU2) : F → S ⊕ T → SU2 :=
    fun g s => selectedLabel σ (arc t) x (g,s)
  have hleft (g : F) (s : S) (k : Fin (Fintype.card I)) : σ k ≠ (g,.inl s) := by
    change ((e k).1, Sum.inr (e k).2) ≠ (g,Sum.inl s)
    simp
  have hsmall (t : ℝ) (x : Fin (Fintype.card I) → SU2) (g : F) (s : S) :
      ‖(L t x g (.inl s) : ℍ)-1‖ ≤ η := by
    dsimp only [L]
    rw [selectedLabel_other σ _ x _ (hleft g s)]
    exact (smallQuaternionArc_distance (base (g,.inl s)) (hbase _) t).trans (ha g s).le
  have hword (b : F × (S ⊕ T) → SU2) (r : FreeGroup (S ⊕ T)) (g : F) :
      FreeGroup.lift b (pathSpelling v r g) = pathProduct (H := SU2) v (fun g s => b (g,s)) r g :=
    pathSpelling_eval v (fun g s => b (g,s)) r g
  obtain ⟨b,hfixed,hw,hρ⟩ := selected_word_sublevel_solvable σ w ρ arc
    (fun p => smallQuaternionArc_smooth _ (hbase p)) (by intro p; simp [arc])
    hdet δ hδ (fun t _ x hx => by
      let f : J → ℍ := fun p => (pathProduct (H := SU2) v (L t x) (r (.inl p.2)) p.1 : ℍ)-1
      have hordinary (i : R) (hi : i ∈ B) (g : F) :
          pathProduct (H := SU2) v (L t x) (r (.inr i)) g = 1 := by
        have h := hx (eI.symm (g,⟨i,hi⟩))
        simpa only [w, Equiv.apply_symm_apply, hword] using h
      have hb (i : Z) (g : F) : ‖(pathProduct (H := SU2) v (L t x) (r (.inl i)) g : ℍ)-1‖ ≤
          C*η + C*(‖f‖+η)*‖f‖ := by
        obtain ⟨h₁,h₂⟩ := hcomp (L t x) ‖f‖ (norm_nonneg _) (hsmall t x)
          (fun i hi => hordinary i (hAB hi))
          (fun i g => norm_le_pi_norm f (g,i)) i g
        have htri := norm_sub_le_norm_sub_add_norm_sub (pathProduct (H := SU2) v (L t x) (r (.inl i)) g : ℍ)
          (pathProduct (H := SU2) v (L t x) (FreeGroup.map Sum.inl (z i)) g : ℍ) 1
        calc
          _ ≤ C*(η+‖f‖)*‖f‖ + C*η := htri.trans (add_le_add ((norm_sub_rev _ _).trans_le h₁) h₂)
          _ = _ := by ring
      have hne : ‖f‖ ≠ δ := by
        rw [norm_eq_familySize]
        exact familySize_ne_threshold (fun p : J => ‖f p‖) (Set.finite_range _ |>.bddAbove)
          C δ η η hδ hC hη.le hη.le le_rfl hc₁ hc₂ (fun p => by
            simpa only [← norm_eq_familySize] using hb p.2 p.1)
      have heq : ‖(fun k => (FreeGroup.lift (selectedLabel σ (arc t) x) (ρ k) : ℍ))-1‖ = ‖f‖ := by
        change ‖fun k => (FreeGroup.lift (selectedLabel σ (arc t) x) (ρ k) : ℍ)-1‖ = _
        simpa only [ρ, hword, f, L] using norm_comp_equiv eJ f
      intro h
      exact hne (heq.symm.trans h))
  let b' : F → T → SU2 := fun g t => b (g,.inr t)
  have heval : (fun g s => b (g,s)) = mergeLabels a b' := by
    funext g s
    rcases s with s | t
    · rw [hfixed _ (hleft g s)]
      simp [arc, base, mergeLabels]
    · rfl
  refine ⟨b',?_,?_⟩
  · intro i hi g
    have h := hw (eI.symm (g,⟨i,hi⟩))
    simpa only [w, Equiv.apply_symm_apply, hword, heval] using h
  · intro i g
    have h := (norm_le_pi_norm
      ((fun k => (FreeGroup.lift b (ρ k) : ℍ))-1) (eJ.symm (g,i))).trans_lt hρ
    simpa only [ρ, Pi.sub_apply, Pi.one_apply, Equiv.apply_symm_apply, hword, heval] using h

end FiniteQuotientSolvability
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section AlignedComparison
variable {Γ : Type u} {S T Z R : Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]

omit [Group.ResiduallyFinite Γ] in
theorem wordValue_map_alphabet {E : Type*} (v : S → Γ) (f : E → S) (w : FreeGroup E) :
    wordValue v (FreeGroup.map f w) = wordValue (fun e => v (f e)) w := by
  have he : (wordValue v).comp (FreeGroup.map f) = wordValue (fun e => v (f e)) := by
    apply FreeGroup.ext_hom
    intro e
    simp [wordValue]
  exact congrArg (fun h : FreeGroup E →* Γ => h w) he

/-- The algebraic core of the manuscript's presentation comparison, for an
actual aligned presentation. The passage from arbitrary ordinary CW classifying
spaces to this presentation is a separate topological obligation. -/
theorem aligned_presentation_small_transport_oai
    (v : S ⊕ T → Γ) (r : Z ⊕ R → FreeGroup (S ⊕ T)) (z : Z → FreeGroup S)
    (hvT : ∀ t, v (.inr t) = 1)
    (hr : ∀ i, wordValue v (r i) = 1)
    (hz : ∀ i, wordValue (fun s => v (.inl s)) (z i) = 1)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r))
    (hinj : Function.Injective (relatorChainMap v r))
    (hchain : ∀ i, pathChain v (FreeGroup.map Sum.inl (z i)) 1 = pathChain v (r (.inl i)) 1)
    (Q : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ T)
    (hQ : Q.toLinearMap = extraRelatorMap v (fun i => r (.inr i))) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
      (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
      (∀ i g, pathProduct (fun s => v (.inl s)) a (z i) g = 1) →
      ∀ w : FreeGroup S, wordValue (fun s => v (.inl s)) w = 1 → ∀ g,
        pathProduct (fun s => v (.inl s)) a w g = 1 := by
  classical
  have hzn (i) : FreeGroup.map Sum.inl (z i) ∈ Subgroup.normalClosure (Set.range r) := by
    rw [← hp]
    change wordValue v (FreeGroup.map Sum.inl (z i)) = 1
    rw [wordValue_map_alphabet, hz]
  have htn (t) : FreeGroup.of (.inr t) ∈ Subgroup.normalClosure (Set.range r) := by
    rw [← hp]
    change wordValue v (FreeGroup.of (.inr t)) = 1
    simpa [wordValue] using hvT t
  choose lz hlz using fun i => exists_normalExpression r (hzn i)
  choose lt hlt using fun t => exists_normalExpression r (htn t)
  have hc (i) : ((lz i).map (fun f => normalFactorCount v f 1)).sum =
      Finsupp.single (1,Sum.inl i) 1 :=
    exact_translated_relator_counts v r hr hinj _ (.inl i) (hchain i) (lz i) (hlz i)
  obtain ⟨A,C,hC,hcomp⟩ := finite_normal_comparison v r hr z lz lt hlz hlt hc
  obtain ⟨δ,η,hδ,hδ1,hη,hη1,hc₁,hc₂⟩ := small_thresholds_exist C hC
  refine ⟨η,hη,?_⟩
  intro a ha haz
  let W : Γ × (Z ⊕ R) → FreeGroup (S ⊕ T) := fun p => r p.2
  let K : Γ × (Z ⊕ R) → Set SU2 := fun p => match p.2 with
    | .inl _ => {b | ‖(b : ℍ)-1‖ ≤ δ}
    | .inr _ => {1}
  have hK (p) : IsClosed (K p) := by
    rcases p with ⟨g,i | i⟩
    · exact isClosed_le ((continuous_subtype_val.sub continuous_const).norm) continuous_const
    · exact isClosed_singleton
  obtain ⟨b,hb⟩ := compact_labeling_from_finite_quotients v a W Prod.fst K hK
    (fun b : SU2 => ‖(b : ℍ)-1‖ < η) (by simpa using hη) ha (by
      intro N J aF haF
      let : Fintype (Γ ⧸ N.toSubgroup) := Fintype.ofFinite _
      let q := QuotientGroup.mk' N.toSubgroup
      let B := A ∪ (J.image Prod.snd).toRight
      let QF := quotientChainEquiv q Q (by rw [hQ]; exact extraRelatorMap_equivariant _ _)
      have hQF : QF.toLinearMap = extraRelatorMap (fun s => q (v s)) (fun i => r (.inr i)) := by
        change quotientMatrix q Q.toLinearMap = _
        rw [hQ, extraRelatorMap_quotientMatrix]
      obtain ⟨bF,hord,hdis⟩ := finite_quotient_comparison_solvable (fun s => q (v s)) r z A B
        (Finset.subset_union_left) QF hQF C δ η (by linarith) hδ hη hη1 hc₁ hc₂
        (fun b h hh hsmall hord hdist => hcomp q b η h hη.le hh hsmall hord hdist) aF haF
      refine ⟨bF,?_⟩
      rintro ⟨g,i | i⟩ hi d
      · exact (hdis i d).le
      · exact hord i (Finset.mem_union_right _ (Finset.mem_toRight.mpr
          (Finset.mem_image.mpr ⟨(g,.inr i),hi,rfl⟩))) d)
  have hord (i : R) (g : Γ) : pathProduct v (mergeLabels a b) (r (.inr i)) g = 1 :=
    hb (g,.inr i)
  have hdis (i : Z) (g : Γ) : ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)-1‖ ≤ δ :=
    hb (g,.inl i)
  let f : Z × Γ → ℝ := fun p => ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl p.1)) p.2 : ℍ)-1‖
  have hbounded : BddAbove (Set.range f) := ⟨δ, by rintro _ ⟨⟨i,g⟩,rfl⟩; exact hdis i g⟩
  have hzero : ∀ p, f p = 0 := familySize_contraction f (fun _ => norm_nonneg _)
    δ C η hδ.le (by linarith) hη.le (fun p => hdis p.1 p.2) (by linarith) (by
      rintro ⟨i,g⟩
      have h := (hcomp (MonoidHom.id Γ) (mergeLabels a b) η (familySize f) hη.le
        (familySize_nonneg f hbounded) (fun g s => (ha g s).le) (fun i _ => hord i)
        (fun i g => le_familySize f hbounded (i,g)) i g).1
      have hz' : pathProduct v (mergeLabels a b) (FreeGroup.map Sum.inl (z i)) g = 1 := by
        rw [pathProduct_map_alphabet]
        exact haz i g
      change ‖(pathProduct (H := SU2) v (mergeLabels a b) (FreeGroup.map Sum.inl (z i)) g : ℍ)-
        (pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)‖ ≤ _ at h
      rw [hz'] at h
      change ‖(1 : ℍ) - (pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ)‖ ≤
        C * (η + familySize f) * familySize f at h
      change ‖(pathProduct (H := SU2) v (mergeLabels a b) (r (.inl i)) g : ℍ) - 1‖ ≤
        C * (familySize f + η) * familySize f
      rw [norm_sub_rev]
      rwa [add_comm η (familySize f)] at h)
  have hdist (i : Z) (g : Γ) : pathProduct v (mergeLabels a b) (r (.inl i)) g = 1 := by
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp (hzero (i,g)))
  intro w hw g
  have hw' : wordValue v (FreeGroup.map Sum.inl w) = 1 := by
    rw [wordValue_map_alphabet, hw]
  have h := pathProduct_trivial_of_relators v (mergeLabels a b) (Set.range r)
    (by rintro _ ⟨i,rfl⟩; exact hr i) hp
    (by rintro _ ⟨i | i,rfl⟩ g; exact hdist i g; exact hord i g)
    (FreeGroup.map Sum.inl w) hw' g
  simpa only [pathProduct_map_alphabet, mergeLabels, Sum.elim_inl, Function.comp_def] using h

end AlignedComparison
end EilenbergGanea

end

end OAI
end

theorem solution.{u, u_1, u_2, u_3, u_4} : type_of% @OAI.EilenbergGanea.aligned_presentation_small_transport_oai.{u, u_1, u_2, u_3, u_4} := @OAI.EilenbergGanea.aligned_presentation_small_transport_oai.{u, u_1, u_2, u_3, u_4}
