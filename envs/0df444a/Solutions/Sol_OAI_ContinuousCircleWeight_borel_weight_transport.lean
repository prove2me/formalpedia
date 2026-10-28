-- Prove2me | solution 1 for OAI.ContinuousCircleWeight.borel_weight_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T22:08:23.109465+00:00
-- url     : https://prove2.me/submissions/40924e26-4688-464f-be83-542c704039fe

import Mathlib
import Definitions.Def_ContinuousCircleWeight
import Definitions.Def_OAIQ2Rw000
import Definitions.Def_OAIQ2Rw001

section
-- module Solutions.OAIQ2_Rot.Compat
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Regular
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
namespace ContinuousCircleWeight

theorem regular_monomial (u : unitary ℂ) (m n : ℤ) :
    ((regularU ^ m * regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum =
      lp.single 2 (m,n) 1 := by
  ext ⟨a,b⟩
  change ((regularU ^ m : unitary RegularOperator) : RegularOperator)
    (((regularV u ^ n : unitary RegularOperator) : RegularOperator) regularVacuum) (a,b) = _
  simp only [regularU_zpow_apply, regularV_zpow_apply, regularVacuum, lp.single_apply]
  by_cases ha : a=m
  · subst a
    by_cases hb : b=n
    · subst b; simp
    · simp [hb, sub_eq_zero, Prod.mk.injEq]
  · have ham : a-m ≠ 0 := sub_ne_zero.mpr ha
    simp [ham, Prod.mk.injEq, Ne.symm ha]

theorem regular_cyclic (u : unitary ℂ) :
    (Submodule.span ℂ (Set.range (fun mn : ℤ × ℤ =>
      ((regularU ^ mn.1 * regularV u ^ mn.2 : unitary RegularOperator) : RegularOperator)
        regularVacuum))).topologicalClosure = ⊤ := by
  simp_rw [regular_monomial]
  have heq : (fun mn : ℤ × ℤ => lp.single 2 (mn.1,mn.2) (1 : ℂ)) =
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert) : ℤ × ℤ → RegularHilbert) := by
    funext mn
    rw [← (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).repr_symm_single mn]
    ext i
    simp [LinearIsometryEquiv.symm, LinearIsometryEquiv.refl, lp.single_apply]
  rw [heq]
  exact (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ RegularHilbert)).dense_span

end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TensorBasis
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uE uι uκ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators

open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
variable {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma fieldMulL2_norm_le (T : X → (E →L[ℂ] E))
    (hT : ∀ v, AEStronglyMeasurable (fun x ↦ T x v) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖T x‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖fieldMulL2 μ T hT C hC‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC0
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldMulL2_coe μ T hT C hC f,hC] with x hx hc
  rw [hx]
  exact ((T x).le_opNorm _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FiberActions
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable _root_.OAI.ContinuousCircleWeight.instCoeFunRealBorelForallCircleXReal _root_.OAI.ContinuousCircleWeight.realCutoffRange_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

lemma circleFiberBasis_coe (a b : ℤ) :
    circleFiberBasis (a,b) =ᵐ[AddCircle.haarAddCircle] fun x ↦
      fourier b x • lp.single 2 a 1 := by
  simp only [circleFiberBasis,tensorL2Basis_apply]
  filter_upwards [pureL2_coe (AddCircle.haarAddCircle (T := (1:ℝ))) (fourierBasis b) (fiberBasis a),
    coeFn_fourierLp (T := (1:ℝ)) 2 b] with x h1 h2
  simpa only [coe_fourierBasis,h2,fiberBasis_apply] using h1

lemma continuousPi_norm_le (θ : CircleX) (g : C(CircleX,ℂ)) :
    ‖continuousPi θ g‖ ≤ ‖g‖ :=
  fieldMulL2_norm_le _ _ _ _ _ (norm_nonneg _)

lemma continuous_continuousPiHom (θ : CircleX) : Continuous (continuousPiHom θ) := by
  exact (LinearMap.mkContinuous (continuousPiHom θ).toLinearMap 1
    (by
      intro g
      change ‖continuousPi θ g‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using continuousPi_norm_le θ g)).continuous

end


lemma fiberShiftL2_coe (n : ℤ) (f : CircleFiberL2) :
    fiberShiftL2 n f =ᵐ[AddCircle.haarAddCircle] fun x ↦ fiberShift n (f x) :=
  (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

lemma circleFiberBasis_ext {A B : CircleFiberOperator}
    (h : ∀ a b, A (circleFiberBasis (a,b)) = B (circleFiberBasis (a,b))) : A=B := by
  have he : A.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      B.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    apply ContinuousLinearMap.ext
    intro c
    change A (circleFiberBasis.repr.symm (lp.single 2 k c)) =
      B (circleFiberBasis.repr.symm (lp.single 2 k c))
    have hc : lp.single (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c = c•lp.single 2 k 1 := by
      simpa using lp.single_smul (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c 1
    rw [hc,map_smul,map_smul,map_smul,HilbertBasis.repr_symm_single,h k.1 k.2]
  apply ContinuousLinearMap.ext
  intro f
  simpa only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply] using
    DFunLike.congr_fun he (circleFiberBasis.repr f)

lemma continuousPi_basis (θ : CircleX) (a b : ℤ) :
    continuousPi θ (fourier 1) (circleFiberBasis (a,b)) =
      (fourier 1 (a•θ)) • circleFiberBasis (a,b+1) := by
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (fourier 1) (circleFiberBasis (a,b)),
    circleFiberBasis_coe a b,circleFiberBasis_coe a (b+1),
    Lp.coeFn_smul (fourier 1 (a•θ)) (circleFiberBasis (a,b+1))] with x h1 h2 h3 h4
  rw [h1,h2,h4]
  simp only [Pi.smul_apply,h3]
  ext k
  simp only [continuousPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hk : k=a
  · subst k
    simp only [lp.single_apply,Pi.single_eq_same,mul_one]
    rw [fourier_add]
    simp only [fourier_one, AddCircle.toCircle_add,Circle.coe_mul]
    ring
  · simp [lp.single_apply,Pi.single_eq_of_ne hk]

lemma regularMagnetic_single (u : unitary ℂ) (a b : ℤ) (c : ℂ) :
    regularMagnetic u 1 (lp.single 2 (a,b) c) =
      ((u^a : unitary ℂ) : ℂ) • lp.single 2 (a,b+1) c := by
  ext ⟨k,l⟩
  simp only [regularMagnetic_apply,one_mul,lp.coeFn_smul,Pi.smul_apply,
    lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  have he : k=a ∧ l-1=b ↔ k=a ∧ l=b+1 := by omega
  simp only [he]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · simp

lemma fourier_one_real (θ : ℝ) : fourier 1 (θ : CircleX) = (rotationScalar θ : ℂ) := by
  simp only [fourier_one,AddCircle.toCircle_apply_mk,Circle.coe_exp,div_one]
  simp only [rotationScalar,Complex.ofReal_mul,Complex.ofReal_ofNat]

lemma fourier_one_zsmul_real (θ : ℝ) (a : ℤ) :
    fourier 1 (a • (θ : CircleX)) = ((rotationScalar θ)^a : unitary ℂ) := by
  rw [fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  rw [← fourier_one, fourier_one_real, Unitary.coe_zpow]

lemma circleFiberBasis_conj_V (θ : ℝ) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) =
      continuousPi (θ : CircleX) (fourier 1) := by
  apply circleFiberBasis_ext
  intro a b
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_symm,
    HilbertBasis.repr_self]
  change circleFiberBasis.repr.symm (regularMagnetic (rotationScalar θ) 1
    (lp.single 2 (a,b) 1)) = _
  rw [regularMagnetic_single,map_smul,HilbertBasis.repr_symm_single,continuousPi_basis,
    fourier_one_zsmul_real]



end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_FunctionalCalculus
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable _root_.OAI.ContinuousCircleWeight.instCoeFunRealBorelForallCircleXReal _root_.OAI.ContinuousCircleWeight.realCutoffRange_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uι uE uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
open Set Filter
open scoped Topology

lemma norm_tendsto_zero_of_sq {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] {l : Filter ι}
    (u : ι → E) (h : Tendsto (fun i => ‖u i‖^2) l (𝓝 0)) : Tendsto (fun i => ‖u i‖) l (𝓝 0) := by
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h

lemma lpDiagonal_tendsto (d : ℕ → ℤ → ℂ) (e : ℤ → ℂ) (C : ℝ≥0)
    (hd : ∀ n k,‖d n k‖≤C) (he : ∀ k,‖e k‖≤C)
    (hlim : ∀ k,Tendsto (fun n => d n k) atTop (𝓝 (e k))) (u : FiberHilbert) :
    Tendsto (fun n => lpDiagonal (d n) C (hd n) u) atTop (𝓝 (lpDiagonal e C he u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply norm_tendsto_zero_of_sq
  have hs : Summable (fun k => (2*(C:ℝ))^2*‖u k‖^2) := by
    have := (lp.memℓp u).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using this.mul_left ((2*(C:ℝ))^2)
  have hh := tendsto_tsum_of_dominated_convergence hs (g:=fun _ : ℤ => (0:ℝ))
    (f:=fun n k => ‖(d n k-e k)*u k‖^2) (fun k => by simpa using (((hlim k).sub_const (e k)).mul_const (u k)).norm.pow 2) (Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hd n k,he k]))))
  simp only [tsum_zero] at hh
  convert hh using 1
  funext n
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal)
    (lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u)
  have hn' : ‖lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u‖^2 =
      ∑' k, ‖(lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u) k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hn
  rw [hn']
  apply tsum_congr
  intro k
  change ‖d n k*u k-e k*u k‖^2=‖(d n k-e k)*u k‖^2
  rw [sub_mul]

lemma L2_tendsto_of_dominated {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ) (b : X → ℝ)
    (hb : Integrable (fun x => b x^2) μ)
    (hu : ∀ n,∀ᵐ x ∂μ,‖u n x-v x‖≤b x)
    (hl : ∀ᵐ x ∂μ,Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto u atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply norm_tendsto_zero_of_sq
  have he (n : ℕ) : ‖u n-v‖^2=∫ x,‖u n x-v x‖^2 ∂μ := by
    rw [←inner_self_eq_norm_sq (𝕜:=ℂ),L2.inner_def,←integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) v] with x hx
    simp only [hx,inner_self_eq_norm_sq,Pi.sub_apply]
  simp_rw [he]
  convert tendsto_integral_of_dominated_convergence (fun x => b x^2)
    (fun n => ((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable v)).norm.pow 2)
    hb (fun n => (hu n).mono (fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2))
    (hl.mono (fun x hx => by simpa using (hx.sub_const (v x)).norm.pow 2)) using 1 <;> simp

lemma boundedPi_tendsto (θ : CircleX) (g : ℕ → CircleX → ℂ) (h : CircleX → ℂ)
    (hm : ∀ n,Measurable (g n)) (hhm : Measurable h) (C : ℝ≥0)
    (hg : ∀ n x,‖g n x‖≤C) (hh : ∀ x,‖h x‖≤C)
    (hl : ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (u : CircleFiberL2) :
    Tendsto (fun n => boundedPi θ (g n) (hm n) C (hg n) u) atTop (𝓝 (boundedPi θ h hhm C hh u)) := by
  have hl' : ∀ᵐ x ∂AddCircle.haarAddCircle,∀ k : ℤ,Tendsto (fun n => g n (x+k•θ)) atTop (𝓝 (h (x+k•θ))) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_add_right AddCircle.haarAddCircle (k•θ)).quasiMeasurePreserving.ae
      (p:=fun x : CircleX => Tendsto (fun n => g n x) atTop (𝓝 (h x))) hl
  apply L2_tendsto_of_dominated (AddCircle.haarAddCircle : Measure CircleX)
    (E:=FiberHilbert) (fun n => boundedPi θ (g n) (hm n) C (hg n) u)
    (boundedPi θ h hhm C hh u) (fun x => 2*(C:ℝ)*‖u x‖)
  · have hi : Integrable (fun x : CircleX => ‖u x‖^2) AddCircle.haarAddCircle :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
    have hj : Integrable (fun x : CircleX => (2*(C:ℝ))^2*‖u x‖^2) AddCircle.haarAddCircle := hi.const_mul _
    convert hj using 1
    funext x
    exact mul_pow _ _ _
  · intro n
    filter_upwards [boundedPi_coe θ (g n) (hm n) C (hg n) u,boundedPi_coe θ h hhm C hh u] with x h1 h2
    rw [h1,h2]
    apply (norm_sub_le _ _).trans
    have h3 := ((boundedPiField θ (g n) C (hg n) x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (boundedPiField_bound θ (g n) C (hg n) x) (norm_nonneg _))
    have h4 := ((boundedPiField θ h C hh x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (boundedPiField_bound θ h C hh x) (norm_nonneg _))
    linarith
  · filter_upwards [ae_all_iff.mpr (fun n => boundedPi_coe θ (g n) (hm n) C (hg n) u),boundedPi_coe θ h hhm C hh u,hl'] with x h1 h2 hx
    simp_rw [h1,h2]
    exact lpDiagonal_tendsto _ _ C (fun n k => hg n _) (fun k => hh _) hx (u x)
end

section
open Set Metric

lemma circleFunction_circle (f : C(CircleX,ℝ)) (z : Circle) :
    circleFunction f z = (f (circleIdentification.symm z) : ℂ) := by
  simp only [circleFunction,Circle.norm_coe,dite_eq_left]
  congr 2

lemma circleFunction_fourier_one (f : C(CircleX,ℝ)) (x : CircleX) :
    circleFunction f (fourier 1 x) = (f x : ℂ) := by
  rw [fourier_one,circleFunction_circle]
  have he : (AddCircle.toCircle x) = circleIdentification x := by
    exact (AddCircle.homeomorphCircle_apply _ _).symm
  rw [he,Homeomorph.symm_apply_apply]

lemma circleFunction_continuousOn (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (sphere (0:ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : Circle ↦ circleFunction f z)
  simp_rw [circleFunction_circle]
  exact Complex.continuous_ofReal.comp (f.continuous.comp circleIdentification.symm.continuous)

lemma circleFunction_continuousOn_spectrum (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (spectrum ℂ (fourier (T := (1:ℝ)) 1)) := by
  apply (circleFunction_continuousOn f).mono
  rw [ContinuousMap.spectrum_eq_range]
  rintro z ⟨x,rfl⟩
  rw [fourier_one]
  exact (AddCircle.toCircle x).property

lemma circle_cfc (f : C(CircleX,ℝ)) :
    cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) = complexCircleMap f := by
  ext x
  have he := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc (circleFunction f)
    (fourier (T := (1:ℝ)) 1) (circleFunction_continuousOn_spectrum f)
  change cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) x = (f x : ℂ)
  change (cfc (circleFunction f) (fourier (T := (1:ℝ)) 1)) x = cfc (circleFunction f) (fourier 1 x) at he
  rw [he]
  have hz : cfc (circleFunction f) (fourier 1 x) = circleFunction f (fourier 1 x) := by
    simpa only [Algebra.algebraMap_self_apply] using
      (cfc_algebraMap (A := ℂ) (fourier 1 x) (circleFunction f))
  exact hz.trans (circleFunction_fourier_one f x)

variable {A : Type uA} [CStarAlgebra A]
lemma circle_cfc_hom (φ : C(CircleX,ℂ) →⋆ₐ[ℂ] A) (hφ : Continuous φ)
    (f : C(CircleX,ℝ)) :
    φ (complexCircleMap f) = cfc (circleFunction f) (φ (fourier 1)) := by
  have hn : IsStarNormal (φ (fourier 1)) := by
    constructor
    change star (φ _) * φ _ = φ _ * star (φ _)
    rw [← map_star,← map_mul,← map_mul,mul_comm]
  rw [← circle_cfc f]
  exact φ.map_cfc _ _ (circleFunction_continuousOn_spectrum f) hφ
end

open Set Filter
open scoped Topology

lemma bounded_real_continuous_approx (g : CircleX → ℝ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    ∃ f : ℕ → C(CircleX,ℝ), (∀ n x,‖f n x‖≤C) ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  let μ : Measure CircleX := AddCircle.haarAddCircle
  have hgLp : MemLp g 2 μ := MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hg)
  have hd := ContinuousMap.toLp_denseRange ℝ μ ℝ (p:=2) (by norm_num)
  obtain ⟨u,hu,hl⟩ := mem_closure_iff_seq_limit.mp (hd (hgLp.toLp g))
  choose f hf using hu
  have hfl : Tendsto (fun n => ContinuousMap.toLp 2 μ ℝ (f n)) atTop (𝓝 (hgLp.toLp g)) := by
    simpa only [hf] using hl
  obtain ⟨ns,_hns,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfl).exists_seq_tendsto_ae
  let clip : ℝ → ℝ := fun t => max (-(C:ℝ)) (min (C:ℝ) t)
  have hclip : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  let F : ℕ → C(CircleX,ℝ) := fun n => ⟨clip ∘ f (ns n),hclip.comp (f (ns n)).continuous⟩
  refine ⟨F,?_,?_⟩
  · intro n x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨le_max_left _ _,max_le (by linarith [C.property]) (min_le_left _ _)⟩
  · filter_upwards [hns,ae_all_iff.mpr (fun n => ContinuousMap.coeFn_toLp μ (p:=2) (𝕜:=ℝ) (f (ns n))),hgLp.coeFn_toLp] with x hx hf hxg
    have hcg : clip (g x)=g x := by
      have h := abs_le.mp (hg x)
      exact max_eq_right (h.1.trans_eq (min_eq_right h.2).symm) |>.trans (min_eq_right h.2)
    have hh : Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) := by
      simpa only [hf,hxg] using hx
    simpa only [F,ContinuousMap.coe_mk,Function.comp_def,hcg] using (hclip.tendsto (g x)).comp hh

lemma boundedPi_eq_continuousPi (θ : CircleX) (g : C(CircleX,ℂ)) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    boundedPi θ g g.continuous.measurable C hg=continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedPi_coe θ g g.continuous.measurable C hg u,continuousPi_coe θ g u] with x h1 h2
  rw [h1,h2]
  ext k
  rfl

lemma commute_boundedPi_real (θ : CircleX) (B : CircleFiberOperator)
    (hB : ∀ f : C(CircleX,ℝ),Commute (continuousPi θ (complexCircleMap f)) B)
    (g : CircleX → ℝ) (hm : Measurable g) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    Commute (boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp hm) C
      (fun x => by simpa using hg x)) B := by
  obtain ⟨f,hf,hl⟩ := bounded_real_continuous_approx g hm C hg
  let F : ℕ → C(CircleX,ℂ) := fun n => complexCircleMap (f n)
  have hF (n : ℕ) (x : CircleX) : ‖F n x‖≤C := by simpa [F,complexCircleMap] using hf n x
  have hgl (x : CircleX) : ‖(g x:ℂ)‖≤C := by simpa using hg x
  have hlim (u : CircleFiberL2) : Tendsto (fun n => continuousPi θ (F n) u) atTop
      (𝓝 (boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp hm) C hgl u)) := by
    have h := boundedPi_tendsto θ (fun n x => F n x) (fun x => (g x:ℂ))
      (fun n => (F n).continuous.measurable) (Complex.measurable_ofReal.comp hm) C hF hgl
      (hl.mono (fun x hx => Complex.continuous_ofReal.continuousAt.tendsto.comp hx)) u
    simpa only [boundedPi_eq_continuousPi] using h
  change _ * B = B * _
  apply ContinuousLinearMap.ext
  intro u
  exact tendsto_nhds_unique (hlim (B u))
    (by
      have he : (fun n => continuousPi θ (F n) (B u)) = (fun n => B (continuousPi θ (F n) u)) := by
        funext n
        exact DFunLike.congr_fun (hB (f n)).eq u
      rw [he]
      exact (B.continuous.tendsto _).comp (hlim u))


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_BorelWeights
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

namespace ContinuousCircleWeight

section
open Set Filter
open scoped Topology

lemma realPi_one (θ : CircleX) : realPi θ (RealBorel.const 1)=1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ (RealBorel.const 1) u] with x hx
  rw [hx]
  ext k
  simp only [realPiField_apply,RealBorel.const,Complex.ofReal_one,one_mul]
  rfl
lemma realPi_commute (θ : CircleX) (g h : RealBorel) : Commute (realPi θ g) (realPi θ h) := by
  change _*_= _*_
  rw [←realPi_mul,←realPi_mul]
  apply realPi_congr
  exact Eventually.of_forall (fun x => mul_comm _ _)
lemma realPi_commutes (θ : CircleX) (B : CircleFiberOperator)
    (hB : ∀ f : C(CircleX,ℝ),Commute (continuousPi θ (complexCircleMap f)) B) (g : RealBorel) :
    Commute (realPi θ g) B := commute_boundedPi_real _ _ hB _ g.measurable _ g.norm_le
lemma realPi_injective (θ : CircleX) (g : RealBorel) (hg : ∀ x,g x≠0) : Function.Injective (realPi θ g) := by
  apply (injective_iff_map_eq_zero (realPi θ g)).mpr
  intro u hu
  apply Lp.ext
  filter_upwards [realPi_coe θ g u,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  rw [hu,hz] at hx
  rw [hz]
  ext k
  have h := congrArg (fun v : FiberHilbert => v k) hx
  change (0:ℂ)=(g (x+k•θ):ℂ)*u x k at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr (hg _))

lemma realPi_shift (θ : CircleX) (g : RealBorel) :
    realPi θ g*fiberShiftL2 1 = fiberShiftL2 1*realPi θ (g.shift θ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [realPi_coe θ g (fiberShiftL2 1 u),fiberShiftL2_coe 1 u,
    realPi_coe θ (g.shift θ) u,fiberShiftL2_coe 1 (realPi θ (g.shift θ) u)] with x h1 h2 h3 h4
  change (realPi θ g (fiberShiftL2 1 u)) x=(fiberShiftL2 1 (realPi θ (g.shift θ) u)) x
  rw [h1,h2,h4,h3]
  ext k
  simp only [realPiField_apply,fiberShift_apply,RealBorel.shift]
  congr 3
  rw [sub_zsmul,one_zsmul]
  abel
end

open Set Filter
open scoped Topology

lemma realCutoff_mul_inv (θ : CircleX) (g : RealBorel) (n : ℕ) :
    realPi θ g * realPi θ (realCutoffInv g n) = realPi θ (realCutoff g n) := by
  rw [←realPi_mul]
  apply realPi_congr
  apply Eventually.of_forall
  intro x
  change g x*(if (1:ℝ)/(n+1)≤g x then (g x)⁻¹ else 0)=(if (1:ℝ)/(n+1)≤g x then 1 else 0)
  split_ifs with h
  · apply mul_inv_cancel₀
    exact ne_of_gt ((one_div_pos.mpr (by positivity : (0:ℝ)<n+1)).trans_le h)
  · exact mul_zero _

lemma realCutoffRange_projection (θ : CircleX) (g : RealBorel) (n : ℕ) :
    (realCutoffRange θ g n).starProjection=realPi θ (realCutoff g n) := by
  obtain ⟨_,h⟩ := isStarProjection_iff_eq_starProjection_range.mp (realCutoff_proj θ g n)
  exact h.symm
lemma realCutoffRange_le (θ : CircleX) (g : RealBorel) (n : ℕ) :
    realCutoffRange θ g n ≤ (realPi θ g).range := by
  rintro x ⟨u,rfl⟩
  refine ⟨realPi θ (realCutoffInv g n) u,?_⟩
  exact DFunLike.congr_fun (realCutoff_mul_inv θ g n) u

lemma realPi_tendsto (θ : CircleX) (g : ℕ → RealBorel) (h : RealBorel) (C : ℝ≥0)
    (hg : ∀ n x,‖g n x‖≤C) (hh : ∀ x,‖h x‖≤C)
    (hl : ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (u : CircleFiberL2) : Tendsto (fun n => realPi θ (g n) u) atTop (𝓝 (realPi θ h u)) := by
  have hg' (n : ℕ) (x : CircleX) : ‖(g n x:ℂ)‖≤C := by simpa using hg n x
  have hh' (x : CircleX) : ‖(h x:ℂ)‖≤C := by simpa using hh x
  have he (f : RealBorel) (hf : ∀ x,‖(f x:ℂ)‖≤C) :
      boundedPi θ (fun x => (f x:ℂ)) (Complex.measurable_ofReal.comp f.measurable) C hf=realPi θ f :=
    boundedPi_congr θ _ _ _ _ _ _ _ _ (EventuallyEq.rfl)
  have hhlim := boundedPi_tendsto θ (fun n x => (g n x:ℂ)) (fun x => (h x:ℂ))
    (fun n => Complex.measurable_ofReal.comp (g n).measurable)
    (Complex.measurable_ofReal.comp h.measurable) C hg' hh'
    (hl.mono (fun x hx => Complex.continuous_ofReal.continuousAt.tendsto.comp hx)) u
  simpa only [he] using hhlim

lemma realCutoffRange_tendsto (θ : CircleX) (g : RealBorel) (hg : ∀ x,0<g x) (u : CircleFiberL2) :
    Tendsto (fun n => (realCutoffRange θ g n).starProjection u) atTop (𝓝 u) := by
  simp_rw [realCutoffRange_projection]
  have hh := realPi_tendsto θ (realCutoff g) (RealBorel.const 1) 1
    (fun n x => (realCutoff g n).norm_le x) (fun _ => by norm_num [RealBorel.const]) (Eventually.of_forall (fun x => by
      have ht : Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hev : ∀ᶠ n : ℕ in atTop,(1:ℝ)/(n+1)≤g x := (ht.eventually_le_const (hg x)).mono (fun _ hn => hn)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      exact (ite_eq_left hn).symm)) u
  simpa only [realPi_one,one_apply_eq_self] using hh
end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_TracialAction
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section

lemma rightTranslate_apply (u : unitary ℂ) (m n : ℤ) (f : RegularHilbert) (a b : ℤ) :
    rightTranslate u m n f (a,b) = (↑(u^(m*(b-n))) : ℂ)*f (a-m,b-n) := by
  change _*f (-m+a,-n+b)=_
  apply congrArg (fun i : ℤ × ℤ ↦ (↑(u^(m*(b-n))) : ℂ)*f i)
  ext <;> dsimp <;> omega

lemma rightOperator_vacuum (u : unitary ℂ) (m n : ℤ) :
    rightOperator u m n regularVacuum = lp.single 2 (m,n) (1:ℂ) := by
  ext ⟨a,b⟩
  change rightTranslate u m n regularVacuum (a,b)=_
  rw [rightTranslate_apply]
  simp only [regularVacuum,lp.single_apply]
  by_cases ha : a=m
  · subst a
    by_cases hb : b=n
    · subst b; simp
    · simp [hb,sub_eq_zero,Prod.mk.injEq]
  · have ham : a-m≠0 := sub_ne_zero.mpr ha
    simp [ham,Prod.mk.injEq,Ne.symm ha]

lemma rightOperator_U (u : unitary ℂ) (m n : ℤ) :
    Commute (regularU : RegularOperator) (rightOperator u m n) := by
  change _*_= _*_
  ext f ⟨a,b⟩
  change (regularU : RegularOperator) (rightTranslate u m n f) (a,b)=
    rightTranslate u m n ((regularU : RegularOperator) f) (a,b)
  simp only [regularU_apply,rightTranslate_apply]
  congr 2
  exact congrArg (fun i : ℤ × ℤ => f i) (Prod.ext (by dsimp; omega) rfl)

lemma rightOperator_V (u : unitary ℂ) (m n : ℤ) :
    Commute (regularV u : RegularOperator) (rightOperator u m n) := by
  change _*_= _*_
  ext f ⟨a,b⟩
  change (regularV u : RegularOperator) (rightTranslate u m n f) (a,b)=
    rightTranslate u m n ((regularV u : RegularOperator) f) (a,b)
  simp only [regularV_apply,rightTranslate_apply]
  rw [← mul_assoc,← mul_assoc,← Submonoid.coe_mul,← Submonoid.coe_mul,← zpow_add,← zpow_add]
  congr 2
  · exact congrArg (fun z : ℤ => u^z) (by ring)
  · exact congrArg (fun i : ℤ × ℤ => f i) (Prod.ext rfl (by dsimp; ring))

lemma in_regularAlgebra_commutes (u : unitary ℂ) {A : RegularOperator}
    (hA : A∈regularAlgebra u) (m n : ℤ) : Commute A (rightOperator u m n) := by
  have hr : rightOperator u m n ∈ Set.centralizer ({(regularU : RegularOperator),(regularV u : RegularOperator)} : Set RegularOperator) := by
    intro B hB
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hB
    rcases hB with rfl|rfl
    · exact (rightOperator_U u m n).eq
    · exact (rightOperator_V u m n).eq
  exact (hA _ hr).symm

lemma regular_column (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (m n : ℤ) : A (lp.single 2 (m,n) (1:ℂ)) = rightOperator u m n (A regularVacuum) := by
  rw [← rightOperator_vacuum u m n]
  exact DFunLike.congr_fun (in_regularAlgebra_commutes u hA m n).eq regularVacuum

lemma regular_adjoint_coefficient (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (m n : ℤ) : (star A) regularVacuum (m,n) =
      star ((↑(u^(-(m*n))) : ℂ) * (A regularVacuum) (-m,-n)) := by
  have he := ContinuousLinearMap.adjoint_inner_left A (lp.single 2 (m,n) (1:ℂ)) regularVacuum
  change inner ℂ ((star A) regularVacuum) (lp.single 2 (m,n) (1:ℂ))=
    inner ℂ regularVacuum (A (lp.single 2 (m,n) (1:ℂ))) at he
  rw [regular_column u hA,lp.inner_single_right,regularVacuum,lp.inner_single_left] at he
  simp only [RCLike.inner_apply'] at he
  change star ((star A) regularVacuum (m,n))*1=star (1:ℂ)*(rightTranslate u m n (A regularVacuum) (0,0)) at he
  simp only [mul_one,star_one,one_mul,rightTranslate_apply,zero_sub,mul_neg] at he
  have hh := congrArg star he
  simpa only [star_star] using hh

lemma regular_adjoint_norm_vacuum (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u) :
    ‖(star A) regularVacuum‖=‖A regularVacuum‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  calc
    (∑' i : ℤ×ℤ, ‖(star A) regularVacuum i‖^(2:ℝ≥0∞).toReal) =
      ∑' i : ℤ×ℤ, ‖A regularVacuum (-i.1,-i.2)‖^(2:ℝ≥0∞).toReal := by
      congr 1
      funext ⟨m,n⟩
      rw [regular_adjoint_coefficient u hA,norm_star,norm_mul,CStarRing.norm_coe_unitary,one_mul]
    _ = _ := (Equiv.neg (ℤ×ℤ)).tsum_eq (fun i ↦ ‖A regularVacuum i‖^(2:ℝ≥0∞).toReal)

lemma regular_vacuum_separating (u : unitary ℂ) {A : RegularOperator} (hA : A∈regularAlgebra u)
    (hzero : A regularVacuum=0) : A=0 := by
  have hc : (Submodule.span ℂ (Set.range (fun i : ℤ×ℤ ↦ lp.single 2 i (1:ℂ)))).topologicalClosure = ⊤ := by
    have hh := regular_cyclic u
    simpa only [regular_monomial,Prod.eta] using hh
  have hk : Submodule.span ℂ (Set.range (fun i : ℤ×ℤ ↦ lp.single 2 i (1:ℂ))) ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨m,n⟩,rfl⟩
    change A (lp.single 2 (m,n) (1:ℂ))=0
    rw [regular_column u hA,hzero,map_zero]
  have hk' := Submodule.topologicalClosure_minimal _ hk A.isClosed_ker
  rw [hc,top_le_iff] at hk'
  apply ContinuousLinearMap.ext
  intro x
  exact show x ∈ A.ker from hk'.symm ▸ Submodule.mem_top

end

open Set

lemma fiberConjugacy_apply (A : RegularOperator) (x : RegularHilbert) :
    fiberConjugacy A (circleFiberBasis.repr.symm x)=circleFiberBasis.repr.symm (A x) := by
  change circleFiberBasis.repr.symm (A (circleFiberBasis.repr (circleFiberBasis.repr.symm x)))=_
  rw [LinearIsometryEquiv.apply_symm_apply]
lemma fiberConjugacy_V (θ : ℝ) : fiberConjugacy (regularV (rotationScalar θ) : RegularOperator)=continuousPi (θ:CircleX) (fourier 1) := circleFiberBasis_conj_V θ

lemma commute_star_unitary {A : Type uA} [Monoid A] [StarMul A] (u : unitary A) (b : A)
    (h : Commute (u:A) b) : Commute (star (u:A)) b := by
  change star (u:A)*b=b*star (u:A)
  calc
    star (u:A)*b = star (u:A)*(b*(u:A))*star (u:A) := by simp [mul_assoc]
    _ = star (u:A)*((u:A)*b)*star (u:A) := by rw [h.eq]
    _ = b*star (u:A) := by simp [←mul_assoc]

lemma mem_regularCommutant (θ : ℝ) {B : RegularOperator}
    (hB : B∈Set.centralizer ({(regularU:RegularOperator),(regularV (rotationScalar θ):RegularOperator)} : Set RegularOperator)) :
    B∈regularCommutant θ := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro a ha
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
  rcases ha with rfl|rfl
  · exact ⟨hB _ (by simp), (commute_star_unitary regularU B (hB _ (by simp))).eq⟩
  · exact ⟨hB _ (by simp), (commute_star_unitary (regularV (rotationScalar θ)) B (hB _ (by simp))).eq⟩

lemma regularAlgebra_of_commutes (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) :
    fiberConjugacy.symm A∈regularAlgebra (rotationScalar θ) := by
  intro B hB
  have hh : Commute A (fiberConjugacy B) := hA _ ⟨B,mem_regularCommutant θ hB,rfl⟩
  apply fiberConjugacy.injective
  change fiberConjugacy (B*fiberConjugacy.symm A)=fiberConjugacy (fiberConjugacy.symm A*B)
  simpa only [map_mul,fiberConjugacy.apply_symm_apply] using hh.symm.eq

lemma realPi_fiberCommutant (θ : ℝ) (g : RealBorel) :
    ∀ B∈fiberCommutant θ,Commute (realPi (θ:CircleX) g) B := by
  rintro B ⟨b,hb,rfl⟩
  apply realPi_commutes
  intro f
  change Commute (continuousPiHom (θ:CircleX) (complexCircleMap f)) (fiberConjugacy b)
  rw [circle_cfc_hom (continuousPiHom (θ:CircleX)) (continuous_continuousPiHom _) f]
  have hv := (StarSubalgebra.mem_centralizer_iff ℂ).mp hb (regularV (rotationScalar θ)) (by simp)
  have h1 : Commute (continuousPi (θ:CircleX) (fourier 1)) (fiberConjugacy b) := by
    rw [←fiberConjugacy_V]
    change fiberConjugacy _*fiberConjugacy b=fiberConjugacy b*fiberConjugacy _
    simpa only [map_mul] using congrArg fiberConjugacy hv.1
  have h2 : Commute (star (continuousPi (θ:CircleX) (fourier 1))) (fiberConjugacy b) := by
    have conjugacy_star (operator : RegularOperator) :
        fiberConjugacy (star operator) = star (fiberConjugacy operator) :=
      fiberConjugacy.map_star' operator
    rw [←fiberConjugacy_V,←conjugacy_star]
    change fiberConjugacy _*fiberConjugacy b=fiberConjugacy b*fiberConjugacy _
    simpa only [map_mul] using congrArg fiberConjugacy hv.2
  exact h1.cfc h2 (circleFunction f)

lemma fiber_vacuum_trace (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) : ‖star A fiberVacuum‖=‖A fiberVacuum‖ := by
  have h := regular_adjoint_norm_vacuum (rotationScalar θ) (regularAlgebra_of_commutes θ A hA)
  have h1 : A fiberVacuum = circleFiberBasis.repr.symm (fiberConjugacy.symm A regularVacuum) := by
    simpa only [fiberConjugacy.apply_symm_apply,fiberVacuum] using fiberConjugacy_apply (fiberConjugacy.symm A) regularVacuum
  have h2 : star A fiberVacuum = circleFiberBasis.repr.symm (star (fiberConjugacy.symm A) regularVacuum) := by
    have conjugacy_star (operator : RegularOperator) :
        fiberConjugacy (star operator) = star (fiberConjugacy operator) :=
      fiberConjugacy.map_star' operator
    simpa only [conjugacy_star,fiberConjugacy.apply_symm_apply,fiberVacuum] using fiberConjugacy_apply (star (fiberConjugacy.symm A)) regularVacuum
  rw [h1,h2,LinearIsometryEquiv.norm_map,LinearIsometryEquiv.norm_map]
  exact h
lemma fiber_vacuum_faithful (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (hz : A fiberVacuum=0) : A=0 := by
  have h1 := fiberConjugacy_apply (fiberConjugacy.symm A) regularVacuum
  simp only [fiberConjugacy.apply_symm_apply] at h1
  have h2 : fiberConjugacy.symm A regularVacuum=0 := by
    apply circleFiberBasis.repr.symm.injective
    simpa only [map_zero] using h1.symm.trans hz
  have h3 := regular_vacuum_separating (rotationScalar θ) (regularAlgebra_of_commutes θ A hA) h2
  simpa only [fiberConjugacy.apply_symm_apply,map_zero] using congrArg fiberConjugacy h3


end ContinuousCircleWeight

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Polar
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CirclePolar

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma absOp_selfAdjoint (A : Op (H := H)) : IsSelfAdjoint (absOp A) :=
  IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

lemma absOp_square (A : Op (H := H)) : absOp A * absOp A = star A * A :=
  CFC.sqrt_mul_sqrt_self _

lemma norm_absOp (A : Op (H := H)) (x : H) : ‖absOp A x‖ = ‖A x‖ := by
  have he : inner ℂ (absOp A x) (absOp A x) = inner ℂ (A x) (A x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x ((star (absOp A) * absOp A) x) = inner ℂ x ((star A * A) x)
    rw [(absOp_selfAdjoint A).star_eq,absOp_square]
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at he
  have h : ‖absOp A x‖^2 = ‖A x‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (absOp A x),norm_nonneg (A x)]

omit [CompleteSpace H] in
lemma intoRange_dense (A : Op (H := H)) : DenseRange (intoRange A) := by
  intro x
  rw [closure_subtype]
  change x.val ∈ closure (Subtype.val '' Set.range (intoRange A))
  rw [← Set.range_comp]
  exact x.property

lemma polarCore_abs (A : Op (H := H)) (x : H) :
    polarCore A (intoRange (absOp A) x) = A x := by
  apply LinearMap.extendOfNorm_eq (intoRange_dense _)
  refine ⟨1,fun x ↦ ?_⟩
  change ‖A x‖ ≤ 1*‖absOp A x‖
  rw [one_mul,norm_absOp]

lemma polarCore_norm (A : Op (H := H)) (x : closedRange (absOp A)) :
    ‖polarCore A x‖ = ‖x‖ := by
  refine (intoRange_dense (absOp A)).induction_on (p := fun x ↦ ‖polarCore A x‖ = ‖x‖) x
    (isClosed_eq ((polarCore A).continuous.norm) continuous_norm) ?_
  intro y
  rw [polarCore_abs]
  exact (norm_absOp A y).symm

lemma polar_abs (A : Op (H := H)) : polar A * absOp A = A := by
  ext x
  change polarCore A ((closedRange (absOp A)).orthogonalProjectionOnto (absOp A x)) = A x
  have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (intoRange (absOp A) x)
  rw [show (closedRange (absOp A)).orthogonalProjectionOnto (absOp A x) = intoRange (absOp A) x from h]
  exact polarCore_abs A x

lemma polar_norm (A : Op (H := H)) (x : H) :
    ‖polar A x‖ = ‖(closedRange (absOp A)).starProjection x‖ := by
  change ‖polarCore A ((closedRange (absOp A)).orthogonalProjectionOnto x)‖ = _
  rw [polarCore_norm]
  rfl

lemma ker_absOp (A : Op (H := H)) : (absOp A).ker = A.ker := by
  ext x
  change absOp A x=0 ↔ A x=0
  simpa only [norm_eq_zero] using (show ‖absOp A x‖=0 ↔ ‖A x‖=0 by rw [norm_absOp])

lemma closedRange_absOp (A : Op (H := H)) : closedRange (absOp A) = A.kerᗮ := by
  rw [← ker_absOp A,ContinuousLinearMap.orthogonal_ker]
  have hs : ContinuousLinearMap.adjoint (absOp A) = absOp A := (absOp_selfAdjoint A).star_eq
  rw [hs]
  rfl

lemma polar_eq_zero_iff (A : Op (H := H)) (x : H) : polar A x=0 ↔ A x=0 := by
  rw [← norm_eq_zero,polar_norm,norm_eq_zero,Submodule.starProjection_apply_eq_zero_iff,
    closedRange_absOp,Submodule.orthogonal_orthogonal]
  rfl

lemma commute_absOp {A B : Op (H := H)} (h : Commute A B) (hs : Commute (star A) B) :
    Commute (absOp A) B := by
  exact (hs.mul_left h).cfcₙ_nnreal NNReal.sqrt

lemma commute_polar {A B : Op (H := H)} (h : Commute A B) (hs : Commute (star A) B) :
    Commute (polar A) B := by
  have hS := commute_absOp h hs
  have hg (x : H) (hx : x ∈ closedRange (absOp A)) : polar A (B x) = B (polar A x) := by
    apply closure_minimal (s := Set.range (absOp A)) _
      (isClosed_eq ((polar A).continuous.comp B.continuous) (B.continuous.comp (polar A).continuous)) hx
    rintro _ ⟨y,rfl⟩
    have h1 := DFunLike.congr_fun hS.eq y
    have h2 := DFunLike.congr_fun h.eq y
    have h3 z := DFunLike.congr_fun (polar_abs A) z
    change polar A (B (absOp A y)) = B (polar A (absOp A y))
    change absOp A (B y)=B (absOp A y) at h1
    change A (B y)=B (A y) at h2
    change ∀ z, polar A (absOp A z)=A z at h3
    rw [← h1,h3,h3,h2]
  have hk (x : H) (hx : x ∈ (closedRange (absOp A))ᗮ) : polar A (B x)=B (polar A x) := by
    rw [closedRange_absOp,Submodule.orthogonal_orthogonal] at hx
    change A x=0 at hx
    have hb : A (B x)=0 := by
      have he := DFunLike.congr_fun h.eq x
      change A (B x)=B (A x) at he
      rw [he,hx,map_zero]
    rw [(polar_eq_zero_iff A _).mpr hb,(polar_eq_zero_iff A _).mpr hx,map_zero]
  change polar A*B=B*polar A
  ext x
  let P := (closedRange (absOp A)).starProjection
  have hd : x=P x+(x-P x) := by abel
  change polar A (B x)=B (polar A x)
  conv_lhs => rw [hd]
  conv_rhs => rw [hd]
  simp only [map_add]
  rw [hg _ (Submodule.starProjection_apply_mem _ _),
    hk _ (Submodule.sub_starProjection_mem_orthogonal (K := closedRange (absOp A)) _)]


lemma polar_norm_le (A : Op (H := H)) (x : H) : ‖polar A x‖ ≤ ‖x‖ := by
  rw [polar_norm]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

lemma polar_opNorm_le (A : Op (H := H)) : ‖polar A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa using polar_norm_le A

lemma polar_range (A : Op (H := H)) (x : H) : polar A x ∈ closedRange A := by
  have hwithin (y : H) (hy : y ∈ closedRange (absOp A)) : polar A y ∈ closedRange A := by
    apply closure_minimal (s := Set.range (absOp A)) _
      ((Submodule.isClosed_topologicalClosure _).preimage (polar A).continuous) hy
    rintro _ ⟨z,rfl⟩
    change (polar A * absOp A) z ∈ closedRange A
    rw [polar_abs]
    exact A.toLinearMap.range.le_topologicalClosure ⟨z,rfl⟩
  let P := (closedRange (absOp A)).starProjection
  have hk : A (x-P x)=0 := by
    have hh := Submodule.sub_starProjection_mem_orthogonal (K := closedRange (absOp A)) x
    change x-P x ∈ (closedRange (absOp A))ᗮ at hh
    rw [closedRange_absOp,Submodule.orthogonal_orthogonal] at hh
    exact hh
  have he := (polar_eq_zero_iff A (x-P x)).mpr hk
  rw [map_sub,sub_eq_zero] at he
  rw [he]
  exact hwithin _ (Submodule.starProjection_apply_mem _ _)

lemma polar_range_le {A : Op (H := H)} {K : Submodule ℂ H} (hK : IsClosed (K : Set H))
    (hA : ∀ x, A x ∈ K) (x : H) : polar A x ∈ K := by
  have hle : closedRange A ≤ K := by
    apply Submodule.topologicalClosure_minimal _ _ hK
    rintro _ ⟨z,rfl⟩
    exact hA z
  exact hle (polar_range A x)

lemma polar_adjoint_annihilates {A : Op (H := H)} {K : Submodule ℂ H}
    (hK : IsClosed (K : Set H)) (hA : ∀ x, A x ∈ K) {z : H} (hz : z ∈ Kᗮ) :
    (star (polar A)) z = 0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((ContinuousLinearMap.adjoint (polar A)) z) = inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right]
  exact (Submodule.mem_orthogonal _ _).mp hz _ (polar_range_le hK hA y)

end
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma disjoint_norm_bound (P E : Submodule ℂ H) [CompleteSpace P] [CompleteSpace E]
    (v : H) (hd : Disjoint P E)
    (htrace : ‖(star (polar (Eᗮ.starProjection * P.starProjection))) v‖ =
      ‖polar (Eᗮ.starProjection * P.starProjection) v‖) :
    ‖P.starProjection v‖ ≤ ‖Eᗮ.starProjection v‖ := by
  let A := Eᗮ.starProjection * P.starProjection
  have hker : A.ker = Pᗮ := by
    ext x
    change Eᗮ.starProjection (P.starProjection x)=0 ↔ x∈Pᗮ
    rw [Submodule.starProjection_apply_eq_zero_iff,Submodule.orthogonal_orthogonal]
    constructor
    · intro hx
      have hp := (Submodule.disjoint_def.mp hd) _ (P.starProjection_apply_mem x) hx
      exact (P.starProjection_apply_eq_zero_iff).mp hp
    · intro hx
      rw [(P.starProjection_apply_eq_zero_iff).mpr hx]
      exact E.zero_mem
  have hr : closedRange (absOp A) = P := by
    rw [closedRange_absOp,hker,Submodule.orthogonal_orthogonal]
  have hA (x : H) : A x ∈ Eᗮ := Eᗮ.starProjection_apply_mem _
  have hzero : (star (polar A)) (E.starProjection v)=0 :=
    polar_adjoint_annihilates E.isClosed_orthogonal hA (by
      rw [Submodule.orthogonal_orthogonal]
      exact E.starProjection_apply_mem v)
  have hid : (star (polar A)) v = (star (polar A)) (Eᗮ.starProjection v) := by
    rw [E.starProjection_orthogonal]
    simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,hzero,sub_zero]
  have hnorm : ‖polar A v‖ = ‖P.starProjection v‖ := by
    rw [polar_norm]
    congr 1
    simp only [hr]
  calc
    _ = ‖polar A v‖ := hnorm.symm
    _ = ‖(star (polar A)) v‖ := htrace.symm
    _ = ‖(star (polar A)) (Eᗮ.starProjection v)‖ := congrArg norm hid
    _ ≤ ‖star (polar A)‖ * ‖Eᗮ.starProjection v‖ := (star (polar A)).le_opNorm _
    _ ≤ 1 * ‖Eᗮ.starProjection v‖ := by rw [norm_star]; gcongr; exact polar_opNorm_le A
    _ = _ := one_mul _

lemma exists_intersection_of_norm_lt (P E : Submodule ℂ H) [CompleteSpace P] [CompleteSpace E]
    (v : H) (htrace : ‖(star (polar (Eᗮ.starProjection * P.starProjection))) v‖ =
      ‖polar (Eᗮ.starProjection * P.starProjection) v‖)
    (hlt : ‖Eᗮ.starProjection v‖ < ‖P.starProjection v‖) :
    ∃ x : H, x∈P ∧ x∈E ∧ x≠0 := by
  by_contra! h
  have hd : Disjoint P E := Submodule.disjoint_def.mpr h
  exact (not_lt_of_ge (disjoint_norm_bound P E v hd htrace)) hlt



end CirclePolar

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_Transport
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CircleTransport

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commute_projection_of_reducing (P : Submodule ℂ H) [CompleteSpace P]
    (B : Op (H := H)) (hB : ∀ x ∈ P, B x ∈ P)
    (hs : ∀ x ∈ P, (star B) x ∈ P) : Commute P.starProjection B := by
  have ho (x : H) (hx : x∈Pᗮ) : B x∈Pᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).mp hx _ (hs y hy)
  ext x
  change P.starProjection (B x) = B (P.starProjection x)
  have hx : x=P.starProjection x+(x-P.starProjection x) := by abel
  conv_lhs => rw [hx]
  rw [map_add,map_add,
    P.starProjection_mem_subspace_eq_self ⟨_,hB _ (P.starProjection_apply_mem x)⟩,
    P.starProjection_apply_eq_zero_iff.mpr (ho _ (P.sub_starProjection_mem_orthogonal x)),add_zero]

omit [CompleteSpace H] in
lemma invariant_closure (P : Submodule ℂ H) (B : Op (H := H))
    (hB : ∀ x∈P, B x∈P) : ∀ x∈P.topologicalClosure, B x∈P.topologicalClosure := by
  intro x hx
  apply closure_minimal (s := (P : Set H)) _
    ((Submodule.isClosed_topologicalClosure P).preimage B.continuous) hx
  intro y hy
  exact P.le_topologicalClosure (hB y hy)

lemma commutes_star_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    {A : Op (H := H)} (hA : ∀ B∈C, Commute A B) : ∀ B∈C, Commute (star A) B := by
  intro B hB
  have h := (hA (star B) (star_mem hB)).star_star
  simpa using h


lemma projection_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    (P : Submodule ℂ H) [CompleteSpace P]
    (hP : ∀ B∈C, ∀ x∈P, B x∈P) : ∀ B∈C, Commute P.starProjection B := by
  intro B hB
  exact commute_projection_of_reducing P B (hP B hB) (hP (star B) (star_mem hB))

lemma polar_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    {A : Op (H := H)} (hA : ∀ B∈C, Commute A B) :
    ∀ B∈C, Commute (CirclePolar.polar A) B := by
  intro B hB
  exact CirclePolar.commute_polar (hA B hB) (commutes_star_centralizer C hA B hB)

lemma exists_cutoff_intersection (C : StarSubalgebra ℂ (Op (H := H)))
    (v : H) (htrace : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → ‖star A v‖=‖A v‖)
    (P : Submodule ℂ H) [CompleteSpace P] (hP : ∀ B∈C, Commute P.starProjection B)
    (hPv : P.starProjection v≠0) (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hE : ∀ n, ∀ B∈C, Commute (E n).starProjection B)
    (hlim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v)) :
    ∃ n, ∃ x : H, x∈P ∧ x∈E n ∧ x≠0 := by
  have ht : Filter.Tendsto (fun n => ‖(E n)ᗮ.starProjection v‖) Filter.atTop (nhds 0) := by
    simp_rw [Submodule.starProjection_orthogonal,sub_apply,ContinuousLinearMap.id_apply]
    simpa using ((tendsto_const_nhds (x := v)).sub hlim).norm
  have he : ∀ᶠ n in Filter.atTop, ‖(E n)ᗮ.starProjection v‖ < ‖P.starProjection v‖ :=
    (tendsto_order.1 ht).2 _ (norm_pos_iff.mpr hPv)
  obtain ⟨n,hn⟩ := he.exists
  refine ⟨n,CirclePolar.exists_intersection_of_norm_lt P (E n) v ?_ hn⟩
  apply htrace
  apply polar_mem_centralizer C
  intro B hB
  apply Commute.mul_left _ (hP B hB)
  rw [Submodule.starProjection_orthogonal]
  exact (Commute.one_left B).sub_left (hE n B hB)

omit [CompleteSpace H] in
lemma transportedRange_invariant (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (T S : Op (H := H)) (hT : ∀ x∈P, T x∈P) (hD : ∀ x∈D, T x∈D)
    (hAS : ∀ x : D, A ⟨T x,hD x x.property⟩ = S (A x)) :
    ∀ x∈transportedRange D P A, S x∈transportedRange D P A := by
  apply invariant_closure
  rintro y ⟨x,hx,rfl⟩
  refine ⟨⟨T x,hD x x.property⟩,hT x hx,?_⟩
  exact hAS x

lemma transportedRange_mem_centralizer (C : StarSubalgebra ℂ (Op (H := H)))
    (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hP : ∀ B∈C, ∀ x∈P, B x∈P)
    (hD : ∀ B∈C, ∀ x∈D, B x∈D)
    (hA : ∀ B, ∀ hB : B∈C, ∀ x : D, A ⟨B x,hD B hB x x.property⟩ = B (A x)) :
    ∀ B∈C, Commute (transportedRange D P A).starProjection B := by
  apply projection_mem_centralizer
  intro B hB
  exact transportedRange_invariant D P A B B (hP B hB) (hD B hB) (hA B hB)

omit [CompleteSpace H] in
lemma transportedRange_ne_bot (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hA : Function.Injective A) (E : Submodule ℂ H) (hE : E≤D)
    (x : H) (hxP : x∈P) (hxE : x∈E) (hx0 : x≠0) : transportedRange D P A ≠ ⊥ := by
  let z : D := ⟨x,hE hxE⟩
  have hz : A z ∈ transportedRange D P A :=
    Submodule.le_topologicalClosure _ ⟨z,hxP,rfl⟩
  intro hh
  rw [hh,Submodule.mem_bot] at hz
  have : z=0 := hA (by simpa using hz)
  exact hx0 (congrArg Subtype.val this)

omit [CompleteSpace H] in
lemma transportedRange_ne_top (D P : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (hsym : ∀ x y : D, inner ℂ (A x) (y : H) = inner ℂ (x : H) (A y))
    (η : H) (hη : η∈Pᗮ) (hη0 : η≠0) (hηA : η∈LinearMap.range A) :
    transportedRange D P A ≠ ⊤ := by
  obtain ⟨χ,hχ⟩ := hηA
  have hχ0 : (χ : H)≠0 := by
    intro h
    have : χ=0 := Subtype.ext h
    exact hη0 (hχ.symm.trans (by rw [this,map_zero]))
  have horth : (χ : H)∈(transportedRange D P A)ᗮ := by
    rw [transportedRange,Submodule.orthogonal_closure]
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro y ⟨x,hx,rfl⟩
    rw [hsym,hχ]
    exact (Submodule.mem_orthogonal _ _).mp hη _ hx
  intro hh
  rw [hh,Submodule.top_orthogonal_eq_bot,Submodule.mem_bot] at horth
  exact hχ0 horth


omit [CompleteSpace H] in
lemma projection_ne_zero_of_ne_bot (P : Submodule ℂ H) [CompleteSpace P] (hP : P≠⊥) :
    P.starProjection≠0 := by
  intro hh
  apply hP
  have h := Submodule.range_starProjection P
  rw [hh] at h
  simpa using h.symm

omit [CompleteSpace H] in
lemma projection_ne_one_of_ne_top (P : Submodule ℂ H) [CompleteSpace P] (hP : P≠⊤) :
    P.starProjection≠1 := by
  intro hh
  apply hP
  apply top_unique
  intro x _
  rw [← Submodule.starProjection_eq_self_iff,hh]
  rfl

omit [CompleteSpace H] in
lemma invariant_projection (P : Submodule ℂ H) [CompleteSpace P] (S : Op (H := H))
    (hS : ∀ x∈P, S x∈P) : (1-P.starProjection)*S*P.starProjection=0 := by
  ext x
  change S (P.starProjection x)-P.starProjection (S (P.starProjection x))=0
  exact sub_eq_zero.mpr (Submodule.starProjection_eq_self_iff.mpr (hS _ (P.starProjection_apply_mem x))).symm

theorem affiliated_transport (C : StarSubalgebra ℂ (Op (H := H))) (v : H)
    (htrace : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → ‖star A v‖=‖A v‖)
    (hfaith : ∀ A : Op (H := H), (∀ B∈C, Commute A B) → A v=0 → A=0)
    (D : Submodule ℂ H) (A : D →ₗ[ℂ] H) (hAinj : Function.Injective A)
    (hsym : ∀ x y : D, inner ℂ (A x) (y : H)=inner ℂ (x : H) (A y))
    (hD : ∀ B∈C, ∀ x∈D, B x∈D)
    (hA : ∀ B, ∀ hB : B∈C, ∀ x : D, A ⟨B x,hD B hB x x.property⟩=B (A x))
    (E F : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)] [∀ n, CompleteSpace (F n)]
    (hE : ∀ n, ∀ B∈C, Commute (E n).starProjection B)
    (hF : ∀ n, ∀ B∈C, Commute (F n).starProjection B)
    (hED : ∀ n, E n≤D) (hFA : ∀ n, F n≤LinearMap.range A)
    (hElim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v))
    (hFlim : Filter.Tendsto (fun n => (F n).starProjection v) Filter.atTop (nhds v))
    (P : Submodule ℂ H) [CompleteSpace P] (hPC : ∀ B∈C, Commute P.starProjection B)
    (hP0 : P≠⊥) (hP1 : P≠⊤)
    (T S : Op (H := H)) (hTP : ∀ x∈P, T x∈P) (hTD : ∀ x∈D, T x∈D)
    (hAS : ∀ x : D, A ⟨T x,hTD x x.property⟩=S (A x)) :
    ∃ q : Op (H := H), IsStarProjection q ∧ (∀ B∈C, Commute q B) ∧
      q≠0 ∧ q≠1 ∧ (1-q)*S*q=0 := by
  have hP (B : Op (H := H)) (hB : B∈C) (x : H) (hx : x∈P) : B x∈P := by
    rw [← Submodule.starProjection_eq_self_iff]
    have hh := DFunLike.congr_fun (hPC B hB).eq x
    change P.starProjection (B x)=B (P.starProjection x) at hh
    rw [hh,Submodule.starProjection_eq_self_iff.mpr hx]
  have hPv : P.starProjection v≠0 := by
    intro hh
    exact projection_ne_zero_of_ne_bot P hP0 (hfaith _ hPC hh)
  have hQc : ∀ B∈C, Commute Pᗮ.starProjection B := by
    intro B hB
    rw [Submodule.starProjection_orthogonal]
    exact (Commute.one_left B).sub_left (hPC B hB)
  have hQ0 : Pᗮ ≠ ⊥ := by
    intro hh
    have hh' := congrArg (fun Q : Submodule ℂ H => Qᗮ) hh
    rw [Submodule.orthogonal_orthogonal,Submodule.bot_orthogonal_eq_top] at hh'
    exact hP1 hh'
  have hQv : Pᗮ.starProjection v≠0 := by
    intro hh
    exact projection_ne_zero_of_ne_bot Pᗮ hQ0 (hfaith _ hQc hh)
  obtain ⟨n,x,hxP,hxE,hx0⟩ := exists_cutoff_intersection C v htrace P hPC hPv E hE hElim
  obtain ⟨m,η,hηP,hηF,hη0⟩ := exists_cutoff_intersection C v htrace Pᗮ hQc hQv F hF hFlim
  let W := transportedRange D P A
  refine ⟨W.starProjection,?_,transportedRange_mem_centralizer C D P A hP hD hA,
    projection_ne_zero_of_ne_bot W (transportedRange_ne_bot D P A hAinj (E n) (hED n) x hxP hxE hx0),
    projection_ne_one_of_ne_top W (transportedRange_ne_top D P A hsym η hηP hη0 (hFA m hηF)),
    invariant_projection W S (transportedRange_invariant D P A T S hTP hTD hAS)⟩
  exact isStarProjection_starProjection
end
open ContinuousLinearMap
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma fractionMap_apply (b c : Op (H:=H)) (hb : Function.Injective b) (x : H) :
    fractionMap b c hb ⟨b x,⟨x,rfl⟩⟩=c x := by
  change c ((LinearEquiv.ofInjective b.toLinearMap hb).symm ((LinearEquiv.ofInjective b.toLinearMap hb) x))=c x
  rw [LinearEquiv.symm_apply_apply]
omit [CompleteSpace H] in
lemma fractionMap_injective (b c : Op (H:=H)) (hb : Function.Injective b) (hc : Function.Injective c) :
    Function.Injective (fractionMap b c hb) := hc.comp (LinearEquiv.ofInjective b.toLinearMap hb).symm.injective
omit [CompleteSpace H] in
lemma fractionMap_range (b c : Op (H:=H)) (hb : Function.Injective b) :
    LinearMap.range (fractionMap b c hb)=LinearMap.range c.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_,rfl⟩
  · rintro ⟨x,rfl⟩
    exact ⟨⟨b x,⟨x,rfl⟩⟩,fractionMap_apply b c hb x⟩
lemma fractionMap_symmetric (b c : Op (H:=H)) (hb : Function.Injective b)
    (hsb : IsSelfAdjoint b) (hsc : IsSelfAdjoint c) (hbc : Commute b c)
    (x y : LinearMap.range b.toLinearMap) :
    inner ℂ (fractionMap b c hb x) (y:H)=inner ℂ (x:H) (fractionMap b c hb y) := by
  obtain ⟨u,hu⟩ := x.property
  obtain ⟨v,hv⟩ := y.property
  have hx : x=⟨b u,⟨u,rfl⟩⟩ := Subtype.ext hu.symm
  have hy : y=⟨b v,⟨v,rfl⟩⟩ := Subtype.ext hv.symm
  rw [hx,hy,fractionMap_apply,fractionMap_apply]
  have hb' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsb
  have hc' := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsc
  change inner ℂ (c u) (b v)=inner ℂ (b u) (c v)
  change inner ℂ (c.toLinearMap u) (b.toLinearMap v)=inner ℂ (b.toLinearMap u) (c.toLinearMap v)
  rw [hc',hb']
  exact congrArg (fun z => inner ℂ u z) (DFunLike.congr_fun hbc.eq v).symm

omit [CompleteSpace H] in
lemma fractionMap_intertwine (b c T S L : Op (H:=H)) (hb : Function.Injective b)
    (hT : T*b=b*L) (hS : S*c=c*L) (x : LinearMap.range b.toLinearMap) :
    fractionMap b c hb ⟨T x,fraction_domain_map b T L hT x x.property⟩=S (fractionMap b c hb x) := by
  obtain ⟨y,hy⟩ := x.property
  have hx : x=⟨b y,⟨y,rfl⟩⟩ := Subtype.ext hy.symm
  subst x
  rw [fractionMap_apply]
  have he : (⟨T (b y),fraction_domain_map b T L hT _ ⟨y,rfl⟩⟩ : LinearMap.range b.toLinearMap)=⟨b (L y),⟨L y,rfl⟩⟩ :=
    Subtype.ext (DFunLike.congr_fun hT y)
  rw [he,fractionMap_apply]
  exact (DFunLike.congr_fun hS y).symm

theorem bounded_fraction_transport (C : StarSubalgebra ℂ (Op (H:=H))) (v : H)
    (htrace : ∀ A : Op (H:=H),(∀ B∈C,Commute A B)→‖star A v‖=‖A v‖)
    (hfaith : ∀ A : Op (H:=H),(∀ B∈C,Commute A B)→A v=0→A=0)
    (b c : Op (H:=H)) (hb : Function.Injective b) (hc : Function.Injective c)
    (hsb : IsSelfAdjoint b) (hsc : IsSelfAdjoint c) (hbc : Commute b c)
    (hbC : ∀ B∈C,Commute b B) (hcC : ∀ B∈C,Commute c B)
    (E F : ℕ → Submodule ℂ H) [∀ n,CompleteSpace (E n)] [∀ n,CompleteSpace (F n)]
    (hE : ∀ n,∀ B∈C,Commute (E n).starProjection B)
    (hF : ∀ n,∀ B∈C,Commute (F n).starProjection B)
    (hEb : ∀ n,E n≤LinearMap.range b.toLinearMap)
    (hFc : ∀ n,F n≤LinearMap.range c.toLinearMap)
    (hElim : Filter.Tendsto (fun n => (E n).starProjection v) Filter.atTop (nhds v))
    (hFlim : Filter.Tendsto (fun n => (F n).starProjection v) Filter.atTop (nhds v))
    (P : Submodule ℂ H) [CompleteSpace P] (hPC : ∀ B∈C,Commute P.starProjection B)
    (hP0 : P≠⊥) (hP1 : P≠⊤)
    (T S L : Op (H:=H)) (hTP : ∀ x∈P,T x∈P) (hT : T*b=b*L) (hS : S*c=c*L) :
    ∃ q : Op (H:=H),IsStarProjection q ∧ (∀ B∈C,Commute q B) ∧ q≠0 ∧ q≠1 ∧ (1-q)*S*q=0 := by
  apply affiliated_transport C v htrace hfaith (LinearMap.range b.toLinearMap) (fractionMap b c hb)
    (fractionMap_injective b c hb hc) (fractionMap_symmetric b c hb hsb hsc hbc)
    (fun B hB => fraction_domain_map b B B (hbC B hB).symm.eq)
    (fun B hB x => fractionMap_intertwine b c B B B hb (hbC B hB).symm.eq (hcC B hB).symm.eq x)
    E F hE hF hEb _ hElim hFlim P hPC hP0 hP1 T S hTP
    (fraction_domain_map b T L hT) (fractionMap_intertwine b c T S L hb hT hS)
  intro n
  rw [fractionMap_range]
  exact hFc n


end CircleTransport

end

end OAI
end

section
-- module Solutions.OAIQ2_Rot.RotationWeights_BorelTransport
attribute [-instance] _root_.OAI.CircleCoupling.labelMeasurableSpace _root_.OAI.ContinuousCircleWeight.fiberSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace

open Filter Set
open scoped Topology

lemma fractionB_pos (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) (x : CircleX) :
    0<fractionB a ha hp x := inv_pos.mpr (by linarith [hp x])
lemma fractionC_pos (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x) (x : CircleX) :
    0<fractionC a ha hp x := div_pos (hp x) (by linarith [hp x])

lemma fractionB_relation (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    realPi θ (f.mul (fractionB a ha hp)) =
      realPi θ (((fractionB a ha hp).shift θ).mul ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))) := by
  apply realPi_congr
  filter_upwards [he] with x hx
  change f x*(1+a x)⁻¹=(1+a (x+θ))⁻¹*(f x*(1+a x)⁻¹+F x*(a x/(1+a x)))
  have h1 : 1+a x≠0 := ne_of_gt (by linarith [hp x])
  have h2 : 1+a (x+θ)≠0 := ne_of_gt (by linarith [hp (x+θ)])
  field_simp
  nlinarith [hx]

lemma fractionC_relation (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    realPi θ (F.mul (fractionC a ha hp)) =
      realPi θ (((fractionC a ha hp).shift θ).mul ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))) := by
  apply realPi_congr
  filter_upwards [he] with x hx
  change F x*(a x/(1+a x))=(a (x+θ)/(1+a (x+θ)))*(f x*(1+a x)⁻¹+F x*(a x/(1+a x)))
  have h1 : 1+a x≠0 := ne_of_gt (by linarith [hp x])
  have h2 : 1+a (x+θ)≠0 := ne_of_gt (by linarith [hp (x+θ)])
  field_simp
  nlinarith [hx]

lemma fraction_operator_relations (θ : CircleX) (f F : RealBorel) (a : CircleX → ℝ) (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+θ)=F x*a x) :
    let b := realPi θ (fractionB a ha hp)
    let c := realPi θ (fractionC a ha hp)
    let L := fiberShiftL2 1 * realPi θ ((f.mul (fractionB a ha hp)).add (F.mul (fractionC a ha hp)))
    (fiberShiftL2 1*realPi θ f)*b=b*L ∧ (fiberShiftL2 1*realPi θ F)*c=c*L := by
  dsimp only
  constructor
  · rw [mul_assoc,←realPi_mul,fractionB_relation θ f F a ha hp he,realPi_mul]
    rw [←mul_assoc,←realPi_shift,mul_assoc]
  · rw [mul_assoc,←realPi_mul,fractionC_relation θ f F a ha hp he,realPi_mul]
    rw [←mul_assoc,←realPi_shift,mul_assoc]

theorem borel_weight_transport_oai (θ : ℝ) (f F : RealBorel) (a : CircleX → ℝ)
    (ha : Measurable a) (hp : ∀ x,0<a x)
    (he : ∀ᵐ x ∂AddCircle.haarAddCircle,f x*a (x+(θ:CircleX))=F x*a x)
    (p : CircleFiberOperator) (hproj : IsStarProjection p)
    (hpc : ∀ B∈fiberCommutant θ,Commute p B) (hp0 : p≠0) (hp1 : p≠1)
    (hinv : (1-p)*(fiberShiftL2 1*realPi (θ:CircleX) f)*p=0) :
    ∃ q : CircleFiberOperator,IsStarProjection q ∧ (∀ B∈fiberCommutant θ,Commute q B) ∧
      q≠0 ∧ q≠1 ∧ (1-q)*(fiberShiftL2 1*realPi (θ:CircleX) F)*q=0 := by
  let b := fractionB a ha hp
  let c := fractionC a ha hp
  let P := p.range
  let : CompleteSpace P := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hproj.isIdempotentElem).completeSpace_coe
  have hP : P.starProjection=p := by
    obtain ⟨_,h⟩ := isStarProjection_iff_eq_starProjection_range.mp hproj
    exact h.symm
  have hP0 : P≠⊥ := by
    intro h
    apply hp0
    simpa only [h, Submodule.starProjection_bot] using hP.symm
  have hP1 : P≠⊤ := by
    intro h
    apply hp1
    simpa only [h, Submodule.starProjection_top,ContinuousLinearMap.one_def] using hP.symm
  have hTP : ∀ x∈P,(fiberShiftL2 1*realPi (θ:CircleX) f) x∈P := by
    rintro x ⟨y,rfl⟩
    have hh := DFunLike.congr_fun hinv y
    change (fiberShiftL2 1*realPi (θ:CircleX) f) (p y)-p ((fiberShiftL2 1*realPi (θ:CircleX) f) (p y))=0 at hh
    exact ⟨_,(sub_eq_zero.mp hh).symm⟩
  have hrel := fraction_operator_relations (θ:CircleX) f F a ha hp he
  apply CircleTransport.bounded_fraction_transport (fiberCommutant θ) fiberVacuum
    (fiber_vacuum_trace θ) (fiber_vacuum_faithful θ)
    (realPi (θ:CircleX) b) (realPi (θ:CircleX) c)
    (realPi_injective _ b (fun x => ne_of_gt (fractionB_pos a ha hp x)))
    (realPi_injective _ c (fun x => ne_of_gt (fractionC_pos a ha hp x)))
    (realPi_selfAdjoint _ b) (realPi_selfAdjoint _ c) (realPi_commute _ b c)
    (realPi_fiberCommutant θ b) (realPi_fiberCommutant θ c)
    (realCutoffRange (θ:CircleX) b) (realCutoffRange (θ:CircleX) c)
    (fun n B hB => by rw [realCutoffRange_projection]; exact realPi_fiberCommutant θ _ B hB)
    (fun n B hB => by rw [realCutoffRange_projection]; exact realPi_fiberCommutant θ _ B hB)
    (realCutoffRange_le _ b) (realCutoffRange_le _ c)
    (realCutoffRange_tendsto _ b (fractionB_pos a ha hp) fiberVacuum)
    (realCutoffRange_tendsto _ c (fractionC_pos a ha hp) fiberVacuum)
    P (by simpa only [hP] using hpc) hP0 hP1
    (fiberShiftL2 1*realPi (θ:CircleX) f) (fiberShiftL2 1*realPi (θ:CircleX) F) _ hTP hrel.1 hrel.2


end ContinuousCircleWeight

end

end OAI
end

theorem solution : type_of% @OAI.ContinuousCircleWeight.borel_weight_transport_oai := @OAI.ContinuousCircleWeight.borel_weight_transport_oai
