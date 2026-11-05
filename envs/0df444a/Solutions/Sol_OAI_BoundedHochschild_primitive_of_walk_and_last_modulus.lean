-- Prove2me | solution 1 for OAI.BoundedHochschild.primitive_of_walk_and_last_modulus
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:02:24.953723+00:00
-- url     : https://prove2.me/submissions/35fff244-97b0-4374-82b0-56c2663cac9d

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildLiouville_atoms_multiplier

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild

section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

@[simp] theorem differentialValue_add {n : ℕ} (f g : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (f + g) v = differentialValue f v + differentialValue g v := by
  simp only [differentialValue, add_apply, mul_add, add_mul,
    smul_add, Finset.sum_add_distrib]
  abel

@[simp] theorem differentialValue_smul {n : ℕ} (c : ℂ) (f : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (c • f) v = c • differentialValue f v := by
  simp only [differentialValue, smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm c]
  · rw [mul_comm c]

noncomputable def insertLast {n : ℕ} (f : Cochain M (n + 1)) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.apply ℂ M) u).compContinuousMultilinearMap f.curryRight

@[simp] theorem insertLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : M)
    (v : Fin n → M) : insertLast f u v = f (Fin.snoc v u) := rfl

theorem norm_insertLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : M) :
    ‖insertLast f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  simpa [mul_assoc, mul_left_comm, mul_comm] using f.norm_map_snoc_le v u

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

theorem snoc_succ_tuple {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    (fun i : Fin (n + 1) => (Fin.snoc v u : Fin (n + 2) → M) i.succ) =
      Fin.snoc (fun i : Fin n => v i.succ) u := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [← Fin.castSucc_succ, Fin.snoc_castSucc]

theorem snoc_castSucc_tuple {n : ℕ} (v : Fin n → M) (u : M) :
    (fun i : Fin n => (Fin.snoc v u : Fin (n + 1) → M) i.castSucc) = v := by
  funext i
  exact Fin.snoc_castSucc (α := fun _ => M) u v i

@[simp] theorem mergeInputs_snoc_castSucc [Mul M] {n : ℕ} (v : Fin (n + 1) → M)
    (u : M) (j : Fin n) :
    mergeInputs (Fin.snoc v u) j.castSucc = Fin.snoc (mergeInputs v j) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hlt : ¬ Fin.last n < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
    have heq : Fin.last n ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [mergeInputs, hlt, heq]
  · simp [mergeInputs, ← Fin.castSucc_succ]

@[simp] theorem mergeInputs_snoc_last [Mul M] {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    mergeInputs (Fin.snoc v u) (Fin.last n) =
      Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]

end TupleIdentities

section CocycleIdentity
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

theorem differentialValue_snoc {n : ℕ} (f : Cochain M (n + 1))
    (v : Fin (n + 1) → M) (u : M) :
    differentialValue f (Fin.snoc v u) =
      v 0 * f (Fin.snoc (fun i : Fin n => v i.succ) u) +
      (∑ j : Fin n, ((-1 : ℂ) ^ (j.val + 1)) • f (Fin.snoc (mergeInputs v j) u)) +
      ((-1 : ℂ) ^ (n + 1)) •
        f (Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u)) +
      ((-1 : ℂ) ^ (n + 2)) • (f v * u) := by
  rw [differentialValue, snoc_succ_tuple, snoc_castSucc_tuple, Fin.sum_univ_castSucc]
  simp only [mergeInputs_snoc_castSucc, Fin.val_castSucc, mergeInputs_snoc_last,
    Fin.val_last, Fin.snoc_last]
  have hzero : (Fin.snoc v u : Fin (n + 2) → M) 0 = v 0 := by
    exact Fin.snoc_castSucc (α := fun _ => M) u v 0
  rw [hzero]
  abel

noncomputable def rightMultiply {n : ℕ} (f : Cochain M n) (u : M) : Cochain M n :=
  ((ContinuousLinearMap.mul ℂ M).flip u).compContinuousMultilinearMap f

@[simp] theorem rightMultiply_apply {n : ℕ} (f : Cochain M n) (u : M)
    (v : Fin n → M) : rightMultiply f u v = f v * u := rfl

noncomputable def lastHomotopy {n : ℕ} (f : Cochain M (n + 1)) (u v : M) : Cochain M n :=
  rightMultiply (insertLast f u) v

@[simp] theorem lastHomotopy_apply {n : ℕ} (f : Cochain M (n + 1)) (u v : M)
    (x : Fin n → M) : lastHomotopy f u v x = f (Fin.snoc x u) * v := rfl

theorem lastHomotopy_cocycle {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x : Fin (n + 2) → M, differentialValue f x = 0)
    (u u' : M) (hu : u * u' = 1) (x : Fin (n + 1) → M) :
    differentialValue (lastHomotopy f u u') x =
      ((-1 : ℂ) ^ (n + 1)) •
        (f x - f (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) * u)) * u' +
          (lastHomotopy f u u' (fun i : Fin n => x i.castSucc)) * x (Fin.last n)) := by
  have hz := congrArg (fun y : M => y * u') (hf (Fin.snoc x u))
  rw [differentialValue_snoc] at hz
  simp only [add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc, hu, mul_one,
    zero_mul] at hz
  have hp : (-1 : ℂ) ^ (n + 2) = -((-1 : ℂ) ^ (n + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul] at hz
  simp only [differentialValue, lastHomotopy_apply, mul_assoc, smul_add, smul_sub]
  apply eq_of_sub_eq_zero
  rw [sub_eq_add_neg]
  have hz' := hz
  abel_nf at hz' ⊢
  simpa only [add_assoc, add_left_comm, add_comm] using hz'

end CocycleIdentity

section UnitaryAveraging
variable {M : Type*} [CStarAlgebra M]

noncomputable def translateLast {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    Cochain M (n + 1) :=
  rightMultiply
    (f.compContinuousLinearMap (fun i : Fin (n + 1) =>
      if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
      else ContinuousLinearMap.id ℂ M)) (star (u : M))

@[simp] theorem translateLast_apply {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M)
    (x : Fin (n + 1) → M) :
    translateLast f u x =
      f (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) * u)) * star (u : M) := by
  change f (fun i => (if i = Fin.last n then (ContinuousLinearMap.mul ℂ M).flip (u : M)
    else ContinuousLinearMap.id ℂ M) (x i)) * star (u : M) = _
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem norm_translateLast_le {n : ℕ} (f : Cochain M (n + 1)) (u : unitary M) :
    ‖translateLast f u‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  rw [translateLast_apply]
  have hnorm (z : M) : ‖z * star (u : M)‖ = ‖z‖ :=
    CStarRing.norm_mul_coe_unitary z (star u)
  rw [hnorm]
  calc
    _ ≤ ‖f‖ * (∏ i : Fin n, ‖x i.castSucc‖) * ‖x (Fin.last n) * (u : M)‖ :=
      f.norm_map_snoc_le _ _
    _ = ‖f‖ * ∏ i, ‖x i‖ := by
      rw [CStarRing.norm_mul_coe_unitary, Fin.prod_univ_castSucc, mul_assoc]

@[simp] theorem translateLast_add {n : ℕ} (f g : Cochain M (n + 1)) (u : unitary M) :
    translateLast (f + g) u = translateLast f u + translateLast g u := by
  ext x
  simp [add_mul]

@[simp] theorem translateLast_smul {n : ℕ} (c : ℂ) (f : Cochain M (n + 1)) (u : unitary M) :
    translateLast (c • f) u = c • translateLast f u := by
  ext x
  simp

noncomputable def averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (f : Cochain M (n + 1)) : Cochain M (n + 1) :=
  ∑' j, (p j : ℂ) • translateLast f (u j)

theorem summable_averageLast {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (f : Cochain M (n + 1)) :
    Summable (fun j => (p j : ℂ) • translateLast f (u j)) := by
  refine (hs.mul_right ‖f‖).of_norm_bounded (fun j => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)

theorem norm_averageLast_le {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) (f : Cochain M (n + 1)) :
    ‖averageLast p u f‖ ≤ ‖f‖ := by
  have hbound (j : ℕ) : ‖(p j : ℂ) • translateLast f (u j)‖ ≤ p j * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
    exact mul_le_mul_of_nonneg_left (norm_translateLast_le _ _) (hp j)
  simpa [averageLast] using tsum_of_norm_bounded (hs.mul_right ‖f‖) hbound
end UnitaryAveraging
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

noncomputable def translateLastCLM {n : ℕ} (u : unitary M) :
    Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := fun f => translateLast f u
      map_add' := fun f g => translateLast_add f g u
      map_smul' := fun c f => translateLast_smul c f u }
    1 (fun f => by change ‖translateLast f u‖ ≤ 1 * ‖f‖; simpa only [one_mul] using norm_translateLast_le f u)

@[simp] theorem translateLast_one {n : ℕ} (f : Cochain M (n+1)) :
    translateLast f 1 = f := by
  ext x
  simp only [translateLast_apply,Submonoid.coe_one,star_one,mul_one]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem translateLast_mul {n : ℕ} (f : Cochain M (n+1)) (u v : unitary M) :
    translateLast (translateLast f v) u = translateLast f (u*v) := by
  ext x
  simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,Submonoid.coe_mul,
    star_mul,mul_assoc]

noncomputable def averageLastCLM {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) :
    Cochain M (n+1) →L[ℂ] Cochain M (n+1) :=
  LinearMap.mkContinuous
    { toFun := averageLast p u
      map_add' := fun f g => by
        simp only [averageLast,translateLast_add,smul_add]
        exact Summable.tsum_add (summable_averageLast p u hp hs.summable f)
          (summable_averageLast p u hp hs.summable g)
      map_smul' := fun c f => by
        simp only [averageLast,translateLast_smul,smul_comm (p _ : ℂ) c,
          tsum_const_smul'',RingHom.id_apply] }
    1 (fun f => by change ‖averageLast p u f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using norm_averageLast_le p u hp hs f)

@[simp] theorem averageLastCLM_apply {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1)) :
    averageLastCLM p u hp hs f = averageLast p u f := rfl

noncomputable def residualCLM {n : ℕ} (x : Fin (n+1) → M) : Cochain M (n+1) →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M (x 0)).comp
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M
        (Fin.snoc (fun i : Fin n => x i.succ) 1)) +
    ∑ j : Fin n, ((-1:ℂ)^(j.val+1)) •
      ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M
        (Fin.snoc (mergeInputs x j) 1) +
    ((-1:ℂ)^(n+1)) • ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x

@[simp] theorem residualCLM_apply {n : ℕ} (x : Fin (n+1) → M) (F : Cochain M (n+1)) :
    residualCLM x F =
      x 0 * F (Fin.snoc (fun i : Fin n => x i.succ) 1) +
        ∑ j : Fin n, ((-1:ℂ)^(j.val+1)) • F (Fin.snoc (mergeInputs x j) 1) +
        ((-1:ℂ)^(n+1)) • F x := by
  simp [residualCLM]

lemma residual_eq_differential {n : ℕ} (x : Fin (n+1) → M) (F : Cochain M (n+1)) :
    residualCLM x F = differentialValue (insertLast F 1) x +
      ((-1:ℂ)^(n+1)) •
        (F x - insertLast F 1 (fun i : Fin n => x i.castSucc) * x (Fin.last n)) := by
  simp only [residualCLM_apply,differentialValue,insertLast_apply,smul_sub]
  abel

lemma insertLast_translateLast {n : ℕ} (f : Cochain M (n+1)) (u : unitary M) :
    insertLast (translateLast f u) 1 = lastHomotopy f (u:M) (star (u:M)) := by
  ext x
  simp [translateLast_apply]

lemma residual_translate_cocycle {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0)
    (u : unitary M) (x : Fin (n+1) → M) :
    residualCLM x (translateLast f u) = ((-1:ℂ)^(n+1)) • f x := by
  rw [residual_eq_differential,insertLast_translateLast,
    lastHomotopy_cocycle f hf (u:M) (star (u:M)) (Unitary.mul_star_self_of_mem u.property)]
  simp only [translateLast_apply,smul_add,smul_sub]
  abel

lemma residual_average_invariant {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (F : Cochain M (n+1))
    (c : (Fin (n+1) → M) → M)
    (hF : ∀ v x, residualCLM x (translateLast F v) = c x) :
    ∀ v x, residualCLM x (translateLast (averageLast p u F) v) = c x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  have he : L (averageLast p u F) = ∑' i, (p i : ℂ) • c x := by
    rw [averageLast,L.map_tsum (summable_averageLast p u hp hs.summable F)]
    congr 1
    funext i
    simp only [map_smul,L,ContinuousLinearMap.comp_apply]
    change (p i:ℂ) • residualCLM x (translateLast (translateLast F (u i)) v) = _
    rw [translateLast_mul,hF]
  change L (averageLast p u F) = _
  rw [he]
  have hsc : HasSum (fun i => (p i : ℂ)) 1 := by simpa only [Complex.ofReal_one] using Complex.hasSum_ofReal.mpr hs
  simpa only [one_smul] using (hsc.smul_const (c x)).tsum_eq

lemma residual_iterate {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) (j : ℕ) :
    ∀ v x, residualCLM x (translateLast ((averageLastCLM p u hp hs)^[j] f) v) =
      ((-1:ℂ)^(n+1)) • f x := by
  induction j with
  | zero => exact fun v x => residual_translate_cocycle f hf v x
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact residual_average_invariant p u hp hs _ _ ih

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_of_norm {a : I → M} {l : Filter I} {b : M}
    (h : Tendsto a l (𝓝 b)) : PredualTendsto e a l b := by
  intro z
  exact (((ContinuousLinearMap.apply ℂ ℂ) z).continuous.tendsto _).comp
    (e.symm.continuous.tendsto _ |>.comp h)

lemma predual_tendsto_sum {a : I → J → M} {b : J → M} (l : Filter I) (s : Finset J)
    (h : ∀ j ∈ s, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑ j ∈ s, a i j) l (∑ j ∈ s, b j) := by
  intro z
  simpa only [map_sum,sum_apply] using
    tendsto_finsetSum s (fun j hj => h j hj z)

lemma predual_tendsto_tsum [CompleteSpace M] {a : I → J → M} {b : J → M}
    {l : Filter I} [l.NeBot] (C : J → ℝ) (hC : Summable C)
    (ha : ∀ i j, ‖a i j‖ ≤ C j)
    (h : ∀ j, PredualTendsto e (fun i => a i j) l (b j)) :
    PredualTendsto e (fun i => ∑' j, a i j) l (∑' j, b j) := by
  have hCb (j : J) : ‖b j‖ ≤ C j :=
    predual_norm_le e (C j) (by obtain ⟨i,_⟩ := (Eventually.of_forall (fun _i : I => True.intro) : ∀ᶠ _i in l, True).exists; exact (norm_nonneg (a i j)).trans (ha i j))
      (Eventually.of_forall fun i => ha i j) (h j)
  have hsa (i : I) : Summable (a i) := hC.of_norm_bounded (ha i)
  have hsb : Summable b := hC.of_norm_bounded hCb
  intro z
  let ev : M →L⋆[ℂ] ℂ := ((ContinuousLinearMap.apply ℂ ℂ) z).comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change Tendsto (fun i => ev (∑' j, a i j)) l (𝓝 (ev (∑' j, b j)))
  simp_rw [ev.map_tsum (hsa _),ev.map_tsum hsb]
  apply tendsto_tsum_of_dominated_convergence (hC.mul_right ‖z‖) (fun j => h j z)
  exact Eventually.of_forall fun i j => calc
    ‖ev (a i j)‖ ≤ ‖e.symm (a i j)‖ * ‖z‖ := (e.symm (a i j)).le_opNorm z
    _ ≤ C j * ‖z‖ := mul_le_mul_of_nonneg_right (by simpa using ha i j) (norm_nonneg _)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace HochschildCesaro
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def avg (P : E →L[ℂ] E) (f : E) (n : ℕ) : E :=
  (n+1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (n+1), P^[j] f

lemma iterate_norm_le (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (f : E) (j : ℕ) : ‖P^[j] f‖ ≤ ‖f‖ := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simpa only [Function.iterate_succ_apply'] using (hP (P^[j] f)).trans ih

lemma norm_avg_le (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (f : E) (n : ℕ) : ‖avg P f n‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < n+1 := by positivity
  have hs : ‖∑ j ∈ Finset.range (n+1), P^[j] f‖ ≤ (n+1 : ℝ) * ‖f‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), ‖P^[j] f‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range (n+1), ‖f‖ :=
        Finset.sum_le_sum fun j _ => iterate_norm_le P hP f j
      _ = _ := by simp [nsmul_eq_mul]
  calc
    ‖avg P f n‖ = (n+1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (n+1), P^[j] f‖ := by
      rw [avg, norm_smul, norm_inv, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
    _ ≤ (n+1 : ℝ)⁻¹ * ((n+1 : ℝ) * ‖f‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ‖f‖ := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

lemma sum_defect (P : E →L[ℂ] E) (f : E) (n : ℕ) :
    P (∑ j ∈ Finset.range n, P^[j] f) - (∑ j ∈ Finset.range n, P^[j] f) = P^[n] f - f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, map_add]
    rw [show P (P^[n] f) = P^[n+1] f by rw [Function.iterate_succ_apply']]
    calc
      _ = (P (∑ j ∈ Finset.range n, P^[j] f) - (∑ j ∈ Finset.range n, P^[j] f)) + (P^[n+1] f - P^[n] f) := by abel
      _ = _ := by rw [ih]; abel

lemma avg_defect (P : E →L[ℂ] E) (f : E) (n : ℕ) :
    P (avg P f n) - avg P f n = (n+1 : ℂ)⁻¹ • (P^[n+1] f - f) := by
  simp only [avg,map_smul,← smul_sub,sum_defect]

lemma avg_defect_tendsto (P : E →L[ℂ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (f : E) :
    Tendsto (fun n => P (avg P f n) - avg P f n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have H : Tendsto (fun n : ℕ => (n+1 : ℝ)⁻¹ * (2*‖f‖)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (2*‖f‖)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) H
  rw [avg_defect,norm_smul]
  have hn : ‖(n+1:ℂ)⁻¹‖ = (n+1 : ℝ)⁻¹ := by
    rw [norm_inv, ← Nat.cast_add_one, Complex.norm_natCast, Nat.cast_add_one]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_sub_le _ _).trans (by linarith [iterate_norm_le P hP f (n+1)])

end HochschildCesaro

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]
lemma residual_cesaro {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1) (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) (j : ℕ) :
    ∀ v x, residualCLM x (translateLast (HochschildCesaro.avg (averageLastCLM p u hp hs) f j) v) =
      ((-1:ℂ)^(n+1)) • f x := by
  intro v x
  let L : Cochain M (n+1) →L[ℂ] M := (residualCLM x).comp (translateLastCLM v)
  change L (HochschildCesaro.avg (averageLastCLM p u hp hs) f j) = _
  rw [HochschildCesaro.avg,map_smul,map_sum]
  have hL (k : ℕ) : L ((averageLastCLM p u hp hs)^[k] f) = ((-1:ℂ)^(n+1)) • f x :=
    residual_iterate p u hp hs f hf k v x
  simp only [hL,Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_add_one,smul_smul]
  rw [← mul_assoc,inv_mul_cancel₀ (show (j+1:ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero j),one_mul]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma averageLast_apply {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (F : Cochain M (n+1)) (x : Fin (n+1) → M) :
    averageLast p u F x = ∑' j, (p j : ℂ) • translateLast F (u j) x := by
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x).map_tsum
    (summable_averageLast p u hp hs F)

lemma predual_tendsto_average {n : ℕ}
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    {F : I → Cochain M (n+1)} {G : Cochain M (n+1)} {l : Filter I} [l.NeBot]
    (C : ℝ) (hF : ∀ i, ‖F i‖ ≤ C)
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x)) :
    ∀ x, PredualTendsto e (fun i => averageLast p u (F i) x) l (averageLast p u G x) := by
  intro x
  simp_rw [averageLast_apply p u hp hs]
  apply predual_tendsto_tsum e (fun j => p j * (C * ∏ k, ‖x k‖)) (hs.mul_right _)
  · intro i j
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp j)]
    apply mul_le_mul_of_nonneg_left _ (hp j)
    exact ((translateLast (F i) (u j)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((norm_translateLast_le _ _).trans (hF i))
        (Finset.prod_nonneg fun k _ => norm_nonneg _))
  · intro j
    apply predual_tendsto_smul e _ (p j : ℂ)
    simp only [translateLast_apply]
    exact (hR (star (u j : M))).tendsto e (ht _)

lemma predual_tendsto_residual {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    {F : I → Cochain M (n+1)} {G : Cochain M (n+1)} {l : Filter I}
    (ht : ∀ x, PredualTendsto e (fun i => F i x) l (G x)) (x : Fin (n+1) → M) :
    PredualTendsto e (fun i => residualCLM x (F i)) l (residualCLM x G) := by
  simp only [residualCLM_apply]
  apply predual_tendsto_add e
  · apply predual_tendsto_add e
    · exact (hL (x 0)).tendsto e (ht _)
    · apply predual_tendsto_sum e l Finset.univ
      intro j _
      exact predual_tendsto_smul e (ht _) _
  · exact predual_tendsto_smul e (ht _) _

theorem exists_average_fixed_cocycle {n : ℕ}
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (f : Cochain M (n+1)) (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0) :
    ∃ G : Cochain M (n+1), ‖G‖ ≤ ‖f‖ ∧ averageLast p u G = G ∧
      (∀ x, residualCLM x G = ((-1:ℂ)^(n+1)) • f x) ∧
      ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop ∧
        ∀ x, PredualTendsto e
          (fun j => HochschildCesaro.avg (averageLastCLM p u hp hs) f j x) U (G x) := by
  let P : Cochain M (n+1) →L[ℂ] Cochain M (n+1) := averageLastCLM p u hp hs
  let F : ℕ → Cochain M (n+1) := fun j => HochschildCesaro.avg P f j
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hP (g : Cochain M (n+1)) : ‖P g‖ ≤ ‖g‖ := norm_averageLast_le p u hp hs g
  have hF (j : ℕ) : ‖F j‖ ≤ ‖f‖ := HochschildCesaro.norm_avg_le P hP f j
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hF
  have hfix : averageLast p u G = G := by
    ext x
    have hpa := predual_tendsto_average e hR p u hp hs.summable ‖f‖ hF ht x
    have hsub := predual_tendsto_sub e hpa (ht x)
    have hn : Tendsto (fun j => P (F j)-F j) (U : Filter ℕ) (𝓝 0) :=
      (HochschildCesaro.avg_defect_tendsto P hP f).mono_left hU
    have hxn : Tendsto (fun j => (P (F j)-F j) x) (U : Filter ℕ) (𝓝 0) := by
      convert
        ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M x).continuous.tendsto 0).comp hn using 1
      · rfl
      · simp

    have hz := predual_tendsto_of_norm e hxn
    have he := predual_tendsto_unique e hsub hz
    exact sub_eq_zero.mp he
  refine ⟨G,hG,hfix,?_,U,hU,ht⟩
  intro x
  have hr := predual_tendsto_residual e hL ht x
  have hid (j : ℕ) : residualCLM x (F j) = ((-1:ℂ)^(n+1)) • f x := by
    simpa only [translateLast_one] using residual_cesaro p u hp hs f hf j 1 x
  apply predual_tendsto_unique e hr
  simp only [hid]
  exact predual_tendsto_const e (((-1:ℂ)^(n+1)) • f x) (U : Filter ℕ)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section Modulus
variable {A E : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup E]

theorem ballSequential_iff_modulus (q : A → E) (R : A → A) :
    BallSequential q R ↔ BallModulus q R := by
  constructor
  · intro hs r ε hε
    by_contra h
    push Not at h
    choose x hx hxq hRx using fun j : ℕ =>
      h (1 / ((j : ℝ) + 1)) (by positivity)
    have hlim : Tendsto (fun j => ‖q (x j)‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun j => (hxq j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hout := (hs x ⟨r, hx⟩ hlim).eventually_lt_const hε
    obtain ⟨j, hj⟩ := hout.exists
    exact (not_lt_of_ge (hRx j)) hj
  · intro hm x hx hlim
    obtain ⟨r, hr⟩ := hx
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hm r ε hε
    filter_upwards [hlim.eventually_lt_const hδ] with j hj
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) (hr j) hj
end Modulus
end
end TracialUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace HochschildMartingale

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {f : ℕ → Ω → H}

end HochschildMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in

lemma integrable_of_countable_bound {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν]
    (f : S → H) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f ν :=
  Integrable.of_bound (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

include htr in
lemma trace_norm_unitary_right (a : A) (u : unitary A) :
    ‖τ.toPreGNS (a*(u:A))‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    τ ((star (u:A)*star a)*(a*(u:A))) = τ (star (u:A)*((star a*a)*(u:A))) := by
      simp only [mul_assoc]
    _ = τ (((star a*a)*(u:A))*star (u:A)) := htr _ _
    _ = τ (star a*a) := by rw [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

variable {G : Type*} [Group G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)

variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr

end HochschildLiouville

open MeasureTheory Filter Topology TopologicalSpace
namespace HochschildProbability

end HochschildProbability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hf : ∀ x : A, τ (star x * x) = 0 → x = 0)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr hf

theorem multiplier_of_walk (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (hh : ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g)
    (hdense : ∀ u : unitary A, ∃ g : ℕ → G, (∀ n, μ {g n} ≠ 0) ∧
      Tendsto (fun n => ‖τ.toPreGNS ((ρ (g n) : A)-(u:A))‖) atTop (𝓝 0)) :
    ∀ x : A, R x = R 1*x := by
  have hatom := atoms_multiplier τ h1 htr hf ρ R μ hR hsym time htime hmom hh
  have hu (u : unitary A) : R (u:A) = R 1*(u:A) := by
    obtain ⟨g,hg,hlim⟩ := hdense u
    have hbound : ∀ n, ‖(ρ (g n) : A)-(u:A)‖ ≤ 2*‖(1:A)‖ := by
      intro n
      have ha := CStarRing.norm_coe_unitary_mul (ρ (g n)) (1:A)
      have hb := CStarRing.norm_coe_unitary_mul u (1:A)
      simp only [mul_one] at ha hb
      exact (norm_sub_le _ _).trans (by rw [ha,hb]; ring_nf; rfl)
    have hRl := hR (fun n => (ρ (g n):A)-(u:A)) ⟨_,hbound⟩ hlim
    have hmul : Tendsto (fun n => ‖τ.toPreGNS (R 1*((ρ (g n):A)-(u:A)))‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun _ => preGNS_norm_mul_le τ _ _)
        (by simpa using hlim.const_mul ‖R 1‖)
    have hzero : Tendsto (fun _ : ℕ => ‖τ.toPreGNS (R (u:A)-R 1*(u:A))‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hRl.add hmul)
      have he : R (u:A)-R 1*(u:A) =
          -(R ((ρ (g n):A)-(u:A))) + R 1*((ρ (g n):A)-(u:A)) := by
        rw [map_sub,mul_sub,hatom _ (hg n)]
        abel
      rw [he,map_add,map_neg]
      exact (norm_add_le _ _).trans_eq (by simp only [norm_neg, map_sub])
    have hz := tendsto_nhds_unique tendsto_const_nhds hzero
    exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hf _).mp hz)
  intro x
  obtain ⟨u,c,hx,_⟩ := CStarAlgebra.exists_sum_four_unitary x
  rw [hx,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hu, mul_smul_comm]

end HochschildLiouville

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace HochschildLiouville
open HochschildWalk HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

theorem hilbertD_harmonic
    (hh : ∀ x : A, ∫ u, R (x*(ρ u:A)) * (ρ u⁻¹:A) ∂μ = R x) :
    ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g := by
  intro g
  let L : A →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    ((ContinuousLinearMap.mul ℂ A).flip (ρ g⁻¹:A))
  have hb (u : G) : ‖R ((ρ g:A)*(ρ u:A)) * (ρ u⁻¹:A)‖ ≤ ‖R‖*‖(1:A)‖ := by
    rw [CStarRing.norm_mul_coe_unitary]
    have he : ‖(ρ g:A)*(ρ u:A)‖ = ‖(1:A)‖ := by
      rw [CStarRing.norm_coe_unitary_mul]
      have h := CStarRing.norm_coe_unitary_mul (ρ u) (1:A)
      simpa only [mul_one] using h
    exact (R.le_opNorm _).trans_eq (by rw [he])
  have hi : Integrable (fun u => R ((ρ g:A)*(ρ u:A))*(ρ u⁻¹:A)) μ :=
    integrable_of_countable_bound μ _ (‖R‖*‖(1:A)‖) hb
  have he (u : G) : hilbertD τ h1 ρ R (g*u) = L (R ((ρ g:A)*(ρ u:A))*(ρ u⁻¹:A)) := by
    simp only [hilbertD,algebraD,map_mul,Submonoid.coe_mul,mul_inv_rev]
    simp only [mul_assoc,L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply']
  simp_rw [he]
  rw [L.integral_comp_comm hi,hh]
  rfl
end HochschildLiouville
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

theorem primitive_from_average {n : ℕ} (f F : Cochain M (n+1))
    (hF : ‖F‖ ≤ ‖f‖)
    (hr : ∀ x, residualCLM x F = ((-1:ℂ)^(n+1)) • f x)
    (hm : ∀ (a : Fin n → M) (x : M), F (Fin.snoc a x) = F (Fin.snoc a 1)*x) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  let g : Cochain M n := ((-1:ℂ)^(n+1)) • insertLast F 1
  have hnorm : ‖g‖ ≤ ‖f‖ := by
    calc
      ‖g‖ = ‖insertLast F 1‖ := by simp [g,norm_smul,norm_pow]
      _ ≤ ‖F‖ * ‖(1:M)‖ := norm_insertLast_le _ _
      _ ≤ ‖F‖ := by
        rcases subsingleton_or_nontrivial M with h | h
        · have : (1:M) = 0 := Subsingleton.elim _ _
          simp [this]
        · simp
      _ ≤ ‖f‖ := hF
  refine ⟨g,hnorm,fun x => ?_⟩
  have he : F x = insertLast F 1 (fun i : Fin n => x i.castSucc)*x (Fin.last n) := by
    have h := hm (Fin.init x) (x (Fin.last n))
    rw [Fin.snoc_init_self] at h
    exact h
  have hd : differentialValue (insertLast F 1) x = ((-1:ℂ)^(n+1)) • f x := by
    have h := hr x
    rw [residual_eq_differential,he,sub_self,smul_zero,add_zero] at h
    exact h
  change differentialValue (((-1:ℂ)^(n+1)) • insertLast F 1) x = f x
  rw [differentialValue_smul,hd,smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

lemma last_bound_average {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C) :
    ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (averageLast p u F (Fin.snoc a x))‖ ≤ C := by
  intro x hx hδ
  let L : Cochain M (n+1) →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M (Fin.snoc a x))
  have he (j : ℕ) : ‖L ((p j:ℂ) • translateLast F (u j))‖ ≤ p j*C := by
    change ‖hilbertMap τ h1 (((p j:ℂ) • translateLast F (u j)) (Fin.snoc a x))‖ ≤ _
    rw [smul_apply,map_smul,norm_smul,hilbertMap_norm,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp j)]
    apply mul_le_mul_of_nonneg_left _ (hp j)
    simp only [translateLast_apply,Fin.snoc_castSucc,Fin.snoc_last]
    have hu := trace_norm_unitary_right τ htr (F (Fin.snoc a (x*(u j:M)))) (star (u j))
    rw [show star (u j:M) = ((star (u j):unitary M):M) by rfl,hu]
    exact hF _ (by simpa only [CStarRing.norm_mul_coe_unitary] using hx)
      (by simpa only [trace_norm_unitary_right τ htr] using hδ)
  have ht := L.map_tsum (summable_averageLast p u hp hs.summable F)
  have hb := tsum_of_norm_bounded (hs.mul_right C) he
  rw [← ht] at hb
  simpa only [averageLast,ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.apply_apply,
    hilbertMap_norm,L,one_mul] using hb

lemma last_bound_iterate {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C)
    (j : ℕ) : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (((averageLastCLM p u hp hs)^[j] F) (Fin.snoc a x))‖ ≤ C := by
  induction j with
  | zero => exact hF
  | succ j ih =>
    simpa only [Function.iterate_succ_apply',averageLastCLM_apply] using
      last_bound_average τ h1 htr p u hp hs a R δ C ((averageLastCLM p u hp hs)^[j] F) ih

lemma last_bound_cesaro {n : ℕ} (p : ℕ → ℝ) (u : ℕ → unitary M)
    (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (a : Fin n → M) (R δ C : ℝ) (F : Cochain M (n+1))
    (hF : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (F (Fin.snoc a x))‖ ≤ C)
    (j : ℕ) : ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ →
      ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ ≤ C := by
  intro x hx hδ
  let L : Cochain M (n+1) →L[ℂ] τ.GNS := (hilbertMap τ h1).comp
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin (n+1) => M) M (Fin.snoc a x))
  have he (k : ℕ) : ‖L ((averageLastCLM p u hp hs)^[k] F)‖ ≤ C :=
    (hilbertMap_norm τ h1 _).le.trans (last_bound_iterate τ h1 htr p u hp hs a R δ C F hF k x hx hδ)
  have hb : ‖∑ k ∈ Finset.range (j+1), L ((averageLastCLM p u hp hs)^[k] F)‖ ≤ (j+1:ℝ)*C := by
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1), ‖L ((averageLastCLM p u hp hs)^[k] F)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range (j+1), C := Finset.sum_le_sum fun k _ => he k
      _ = _ := by simp [nsmul_eq_mul]
  have hj : (j+1:ℝ) ≠ 0 := by positivity
  have heq : ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ =
      ‖L (HochschildCesaro.avg (averageLastCLM p u hp hs) F j)‖ := (hilbertMap_norm τ h1 _).symm
  rw [heq,HochschildCesaro.avg,map_smul,map_sum,norm_smul,norm_inv,
    ← Nat.cast_add_one,Complex.norm_natCast,Nat.cast_add_one]
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
    rw [← mul_assoc,inv_mul_cancel₀ hj,one_mul])

theorem cesaro_limit_last_modulus {n : ℕ}
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ)
    (p : ℕ → ℝ) (u : ℕ → unitary M) (hp : ∀ i, 0 ≤ p i) (hs : HasSum p 1)
    (F G : Cochain M (n+1)) (U : Ultrafilter ℕ)
    (ht : ∀ x, PredualTendsto e
      (fun j => HochschildCesaro.avg (averageLastCLM p u hp hs) F j x) U (G x))
    (hF : ∀ a : Fin n → M, BallModulus τ.toPreGNS (F.curryRight a)) :
    ∀ a : Fin n → M, BallModulus τ.toPreGNS (G.curryRight a) := by
  intro a R ε hε
  obtain ⟨δ,hδ,hm⟩ := hF a R (ε/2) (half_pos hε)
  refine ⟨δ,hδ,fun x hx hxδ => ?_⟩
  have hb (j : ℕ) : ‖τ.toPreGNS (HochschildCesaro.avg (averageLastCLM p u hp hs) F j (Fin.snoc a x))‖ ≤ ε/2 :=
    last_bound_cesaro τ h1 htr p u hp hs a R δ (ε/2) F
      (fun y hy hyδ => (hm y hy hyδ).le) j x hx hxδ
  exact (preGNS_norm_le_of_predual_tendsto e τ hL hτ (ε/2) (half_pos hε).le
    (Eventually.of_forall hb) (ht (Fin.snoc a x))).trans_lt (half_lt_self hε)

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

omit [MeasurableSingletonClass G] in
lemma atomicLaw_probability (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (a : ℕ → G) : IsProbabilityMeasure (atomicLaw p a) := by
  constructor
  simp only [atomicLaw,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hp hs.summable,hs.tsum_eq,ENNReal.ofReal_one]

lemma integral_atomicLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : Summable p)
    (a : ℕ → G) (f : G → E) (C : ℝ) (hf : ∀ j, ‖f (a j)‖ ≤ C) :
    ∫ g, f g ∂atomicLaw p a = ∑' j, p j • f (a j) := by
  have hs' : Summable (fun j => (ENNReal.ofReal (p j)).toReal * ‖f (a j)‖) := by
    simp only [ENNReal.toReal_ofReal (hp _)]
    apply (hs.mul_right C).of_nonneg_of_le (fun j => mul_nonneg (hp j) (norm_nonneg _))
    exact fun j => mul_le_mul_of_nonneg_left (hf j) (hp j)
  simpa only [atomicLaw,ENNReal.toReal_ofReal (hp _)] using
    integral_sum_dirac_eq_tsum (f := f) (x := a) (fun j => ENNReal.ofReal_ne_top) hs'

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

lemma average_fixed_harmonic {n : ℕ} (ρ : G →* unitary M)
    (p : ℕ → ℝ) (atoms : ℕ → G) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (F : Cochain M (n+1)) (hF : averageLast p (fun j => ρ (atoms j)) F = F)
    (a : Fin n → M) (x : M) :
    ∫ u, (F.curryRight a) (x*(ρ u:M)) * (ρ u⁻¹:M) ∂atomicLaw p atoms = (F.curryRight a) x := by
  have hb (j : ℕ) : ‖(F.curryRight a) (x*(ρ (atoms j):M)) * (ρ (atoms j)⁻¹:M)‖ ≤
      ‖F.curryRight a‖ * ‖x‖ := by
    rw [CStarRing.norm_mul_coe_unitary]
    exact ((F.curryRight a).le_opNorm _).trans_eq (by rw [CStarRing.norm_mul_coe_unitary])
  rw [integral_atomicLaw p hp hs.summable atoms _ _ hb]
  have he := congrArg (fun H : Cochain M (n+1) => H (Fin.snoc a x)) hF
  rw [averageLast_apply p _ hp hs.summable] at he
  convert he using 1
  · apply tsum_congr
    intro j
    simp only [translateLast_apply,Fin.snoc_last,Fin.snoc_castSucc,map_inv]
    rw [← algebraMap_smul ℝ (p j)]
    rfl
  · rfl

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem primitive_of_walk_and_last_modulus
    (h1 : τ 1 = 1) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ)
    (ρ : G →* unitary M) (p : ℕ → ℝ) (atoms : ℕ → G)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (hsym : (atomicLaw p atoms).map (fun g => g⁻¹) = atomicLaw p atoms)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability (atomicLaw p atoms) (fun g => ‖τ (ρ g : M)‖) time)
    (hdense : ∀ u : unitary M, ∃ g : ℕ → G, (∀ j, atomicLaw p atoms {g j} ≠ 0) ∧
      Tendsto (fun j => ‖τ.toPreGNS ((ρ (g j):M)-(u:M))‖) atTop (𝓝 0))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0)
    (hmod : ∀ a : Fin n → M, BallModulus τ.toPreGNS (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  let : IsProbabilityMeasure (atomicLaw p atoms) := atomicLaw_probability p hp hs atoms
  obtain ⟨F,hF,hfix,hres,U,_hU,ht⟩ :=
    exists_average_fixed_cocycle e hL hR p (fun j => ρ (atoms j)) hp hs f hf
  have hFm := cesaro_limit_last_modulus τ h1 htr e hL hτ p (fun j => ρ (atoms j)) hp hs f F U ht hmod
  apply primitive_from_average f F hF hres
  intro a x
  have hh := hilbertD_harmonic τ h1 ρ (F.curryRight a) (atomicLaw p atoms)
    (average_fixed_harmonic ρ p atoms hp hs F hfix a)
  exact multiplier_of_walk τ h1 htr hfaith ρ (F.curryRight a) (atomicLaw p atoms)
    ((ballSequential_iff_modulus τ.toPreGNS (F.curryRight a)).mpr (hFm a))
    hsym time htime hmom hh hdense x
end BoundedHochschild
end
end OAI
end

theorem solution.{u_1,u_2,u_3} : type_of% @OAI.BoundedHochschild.primitive_of_walk_and_last_modulus.{u_1,u_2,u_3} := @OAI.BoundedHochschild.primitive_of_walk_and_last_modulus.{u_1,u_2,u_3}
