-- Prove2me | solution 1 for OAI.EuclideanRamsey.fieldCriterion_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:48:18.404705+00:00
-- url     : https://prove2.me/submissions/2a888b40-3f0f-4600-af6e-29cc0dcb81cd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Main.lean:L28-L67
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.fieldCriterion_ramsey. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorDescent ----
-- Backport the two-case eliminator from Mathlib/LinearAlgebra/TensorProduct/Defs.lean
-- at d13f23b723b8a846827a245b89c10fc7d3f11612, using the 4.33.1 eliminator.
section Lean433TensorProductCompatibility
open scoped TensorProduct
variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
namespace TensorProduct
@[elab_as_elim, induction_eliminator]
private theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z
    (by simpa only [TensorProduct.zero_tmul] using tmul (0 : M) (0 : N)) tmul add
end TensorProduct
end Lean433TensorProductCompatibility

namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace

namespace EuclideanRamsey

section Descent
variable (F : IntermediateField ℚ ℝ) {ι : Type uIndex} (b : Module.Basis ι F ℝ)

variable (φ : ℝ →ₗ[F] F)

attribute [local instance] OAI.EuclideanRamsey.tensorRing
end Descent

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

theorem fieldCriterion_realCriterion {s d : ℕ} (a : Fin s → Space d)
    (h : FieldCriterion a) : RealCriterion a := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let φ : TensorRing a →ₐ[ℚ] RealTensor :=
    Algebra.TensorProduct.map (coordinateField a).val (coordinateField a).val
  have haug (i : Fin s) (α : Option (Fin d)) :
      ((augmented a i α : Coeff a) : ℝ) = realAugmented a i α := by
    cases α <;> rfl
  have hmul (T : TensorRing a) :
      Algebra.TensorProduct.lmul' ℚ (φ T) = (multiply a T : ℝ) := by
    induction T using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp [hx,hy]
  refine ⟨fun α β => φ (P α β),?_,?_⟩
  · intro i
    have hh := congrArg φ (hP i)
    have hφ (x y : Coeff a) : φ (x ⊗ₜ[ℚ] y) = (x:ℝ) ⊗ₜ[ℚ] (y:ℝ) := rfl
    change (∑ α,∑ β,(realAugmented a i α ⊗ₜ[ℚ] (1:ℝ))*φ (P α β)*
      ((1:ℝ) ⊗ₜ[ℚ] realAugmented a i β)) = 0
    simpa only [map_sum,map_mul,map_zero,hφ,haug,OneMemClass.coe_one] using hh
  · ext α β
    change Algebra.TensorProduct.lmul' ℚ (φ (P (some α) (some β))) = _
    rw [hmul,hG]
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.SmoothingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uDomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
namespace EuclideanRamsey

lemma smoothPositivePart_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothPositivePart :=
  contDiff_id.mul expNegInvGlue.contDiff

lemma smoothPositivePart_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart (smoothPositivePart' t) t := by
  have hg : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t
  have h := (hasDerivAt_id t).mul hg
  change HasDerivAt smoothPositivePart _ t at h
  convert h using 1
  unfold smoothPositivePart'
  by_cases ht : t = 0
  · simp [ht]
  · simp only [id_eq]
    field_simp

lemma smoothPositivePart'_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart' (smoothPositivePart'' t) t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] at h
  change HasDerivAt smoothPositivePart' _ t at h
  apply h.congr_deriv
  simp [smoothPositivePart'']
  left
  ring

lemma smoothPositivePart_nonneg (t : ℝ) : 0 ≤ smoothPositivePart t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]
  · exact mul_nonneg (le_of_not_ge ht) (expNegInvGlue.nonneg t)

lemma smoothPositivePart_pos {t : ℝ} (ht : 0 < t) : 0 < smoothPositivePart t :=
  mul_pos ht (expNegInvGlue.pos_of_pos ht)

lemma smoothPositivePart_zero {t : ℝ} (ht : t ≤ 0) : smoothPositivePart t = 0 := by
  simp [smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]

lemma smoothPositivePart'_bounds (t : ℝ) :
    0 ≤ smoothPositivePart' t ∧ smoothPositivePart' t ≤ 1 := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart', expNegInvGlue.zero_of_nonpos ht]
  have ht0 : 0 < t := lt_of_not_ge ht
  constructor
  · exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)
  · unfold smoothPositivePart'
    rw [expNegInvGlue, ite_eq_right ht, show -t⁻¹ = -1 / t by ring,
      show -1 / t = -(t⁻¹) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    simpa [add_comm] using Real.add_one_le_exp (t⁻¹)

lemma smoothPositivePart''_nonneg (t : ℝ) : 0 ≤ smoothPositivePart'' t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart'', expNegInvGlue.zero_of_nonpos ht]
  · have ht0 : 0 < t := lt_of_not_ge ht
    exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)

section Radial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radialPower_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPower (E := E) a p) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    (fun x => ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _)))

lemma radialPower_hasFDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    HasFDerivAt (radialPower a p)
      ((2*p*(a+‖x‖^2)^(p-1)) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))))
  change HasFDerivAt (radialPower a p) _ x at h
  apply h.congr_fderiv
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

lemma radialPower_hessian {a : ℝ} (ha : 0 < a) (p : ℝ) (x v w : E) :
    iteratedFDeriv ℝ 2 (radialPower a p) x ![v,w] =
      4*p*(p-1)*(a+‖x‖^2)^(p-2) * inner ℝ x v * inner ℝ x w +
      2*p*(a+‖x‖^2)^(p-1) * inner ℝ v w := by
  have hg : (fun y => fderiv ℝ (radialPower a p) y) =
    (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) :=
    funext fun (y : E) => by simpa only [radialPower] using (radialPower_hasFDerivAt ha p y).fderiv
  have hs := (radialPower_hasFDerivAt ha (p-1) x).const_smul (2*p)
  have hd := hs.smul (innerSL ℝ (E := E)).hasFDerivAt
  change HasFDerivAt (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) _ x at hd
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  change ((fderiv ℝ (fun y => fderiv ℝ (radialPower a p) y) x) v) w = _
  rw [hg, hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,
    innerSL_apply_apply, Pi.smul_apply, smul_eq_mul, radialPower, show p-1-1 = p-2 by ring]
  change (2*p*(a+‖x‖^2)^(p-1))*inner ℝ v w +
    (2*p)*(2*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x v)*inner ℝ x w = _
  ring

lemma scalarComposition_hessian {f : E → ℝ} {g g' g'' : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (x v w : E) :
    iteratedFDeriv ℝ 2 (g ∘ f) x ![v,w] =
      g'' (f x) * (fderiv ℝ f x v) * (fderiv ℝ f x w) +
      g' (f x) * iteratedFDeriv ℝ 2 f x ![v,w] := by
  have hf' (y : E) := (hf.differentiable (by simp) y).hasFDerivAt
  have hG : (fun y => fderiv ℝ (g ∘ f) y) =
      (fun y => g' (f y) • fderiv ℝ f y) := by
    funext y
    exact ((hg (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hg' (f x)).comp_hasFDerivAt x (hf' x)).smul
    (hfd x).hasFDerivAt
  change HasFDerivAt (fun y => g' (f y) • fderiv ℝ f y) _ x at hd
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  change ((fderiv ℝ (fun y => fderiv ℝ (g ∘ f) y) x) v) w = _
  rw [hG, hd.fderiv]
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,  smul_eq_mul]
  simp only [show Fin.init ![v,w] 0 = v from rfl, show ![v,w] (Fin.last 1) = w from rfl, Function.comp_apply]
  ring

variable [FiniteDimensional ℝ E]

lemma radialPower_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialPower a p) x =
      p * (a+‖x‖^2)^(p-2) *
        ((Module.finrank ℝ E : ℝ)*a + (Module.finrank ℝ E + 2*p-2)*‖x‖^2) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hsum : (∑ i, inner ℝ x (e i) * inner ℝ x (e i)) = ‖x‖^2 := by
    simpa only [real_inner_comm (e _), real_inner_self_eq_norm_sq] using
      e.sum_inner_mul_inner x x
  unfold halfLaplacian
  simp_rw [radialPower_hessian ha]
  simp only [(stdOrthonormalBasis ℝ E).inner_eq_ite, ite_eq_left, mul_one, Finset.sum_add_distrib]
  have hsum' : (∑ i, 4*p*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x (e i)*inner ℝ x (e i)) =
      4*p*(p-1)*(a+‖x‖^2)^(p-2)*‖x‖^2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (1/2 : ℝ) * ((∑ i, 4*p*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x (e i)*inner ℝ x (e i)) +
    ∑ _ : Fin (Module.finrank ℝ E), 2*p*(a+‖x‖^2)^(p-1)) = _
  rw [hsum']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (a+‖x‖^2)^(p-1) = (a+‖x‖^2)^(p-2)*(a+‖x‖^2) := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add (by positivity), Real.rpow_one]
  rw [hpow]
  ring

omit [FiniteDimensional ℝ E] in
lemma radialBump_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBump (E := E) a p) :=
  smoothPositivePart_contDiff.comp ((radialPower_contDiff ha p).sub contDiff_const)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialBump_nonneg (a p : ℝ) (x : E) : 0 ≤ radialBump a p x :=
  smoothPositivePart_nonneg _

lemma radialBump_compact {a p : ℝ} (ha : 0 < a) (hp : p < 0) :
    HasCompactSupport (radialBump (E := E) a p) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) ?_
  intro x hx
  apply smoothPositivePart_zero
  have hx1 : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hq : 1 ≤ a+‖x‖^2 := by nlinarith
  exact sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos hq hp.le)

lemma radialBump_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialBump a p) x =
      smoothPositivePart' (radialPower a p x-1) * halfLaplacian (radialPower a p) x +
      2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
        ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by
  classical
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => radialPower a p y - 1) :=
    (radialPower_contDiff ha p).sub contDiff_const
  have he (v w : E) :
      iteratedFDeriv ℝ 2 (radialBump a p) x ![v,w] =
        smoothPositivePart'' (radialPower a p x-1) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x v) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x w) +
        smoothPositivePart' (radialPower a p x-1) *
          iteratedFDeriv ℝ 2 (radialPower a p) x ![v,w] := by
    change iteratedFDeriv ℝ 2 (smoothPositivePart ∘ fun y => radialPower a p y-1) x _ = _
    rw [scalarComposition_hessian hf smoothPositivePart_hasDerivAt smoothPositivePart'_hasDerivAt]
    simp only [fderiv_sub_const, (radialPower_hasFDerivAt ha p x).fderiv,
      _root_.smul_apply, innerSL_apply_apply,  smul_eq_mul]
    congr 1
    congr 1
    rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply,
      iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
    simp only [fderiv_sub_const]
  let e := stdOrthonormalBasis ℝ E
  have hsum : (∑ i, inner ℝ x (e i) * inner ℝ x (e i)) = ‖x‖^2 := by
    simpa only [real_inner_comm (e _), real_inner_self_eq_norm_sq] using
      e.sum_inner_mul_inner x x
  unfold halfLaplacian
  simp_rw [he, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  have hs : (∑ i, smoothPositivePart'' (radialPower a p x-1) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i)) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i))) =
      (4*smoothPositivePart'' (radialPower a p x-1)*p^2*((a+‖x‖^2)^(p-1))^2)*‖x‖^2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (1/2:ℝ) * ((∑ i, smoothPositivePart'' (radialPower a p x-1) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i)) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i))) + _) = _
  rw [hs]
  ring

lemma smoothPositivePart_monotone : Monotone smoothPositivePart :=
  monotone_of_hasDerivAt_nonneg smoothPositivePart_hasDerivAt
    (fun t => (smoothPositivePart'_bounds t).1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialBump_antitone_parameter {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hp : p ≤ 0) (x : E) : radialBump b p x ≤ radialBump a p x := by
  apply smoothPositivePart_monotone
  exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos
    (by positivity) (by linarith) hp) 1

lemma radialBump_negative_le {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    max (-halfLaplacian (radialBump a p) x) 0 ≤
      max (-halfLaplacian (radialPower a p) x) 0 := by
  rw [radialBump_halfLaplacian ha]
  have hb := smoothPositivePart'_bounds (radialPower a p x-1)
  have hc : 0 ≤ 2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
      ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (smoothPositivePart''_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)
  apply max_le
  · by_cases h : 0 ≤ halfLaplacian (radialPower a p) x
    · exact le_trans (by nlinarith [mul_nonneg hb.1 h]) (le_max_right _ _)
    · have : smoothPositivePart' (radialPower a p x-1) *
          halfLaplacian (radialPower a p) x ≥ halfLaplacian (radialPower a p) x :=
        by nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (neg_nonneg.mpr (le_of_not_ge h))]
      exact le_trans (by linarith) (le_max_left _ _)
  · exact le_max_right _ _

lemma smoothingExponent_neg (hn : 1 ≤ Module.finrank ℝ E) : smoothingExponent E < 0 := by
  have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
  unfold smoothingExponent
  linarith

lemma radialPower_laplacian_lower {a : ℝ} (ha : 0 < a)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E) :
    smoothingExponent E * (Module.finrank ℝ E : ℝ) * a^(smoothingExponent E-1) ≤
      halfLaplacian (radialPower a (smoothingExponent E)) x := by
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hbracket : n + 2*p-2 = -(3/2:ℝ) := by unfold p n smoothingExponent; ring
  rw [radialPower_halfLaplacian ha]
  change p*n*a^(p-1) ≤ p*(a+‖x‖^2)^(p-2)*(n*a+(n+2*p-2)*‖x‖^2)
  rw [hbracket]
  have hpow := Real.rpow_le_rpow_of_nonpos ha
    (show a ≤ a+‖x‖^2 by nlinarith [sq_nonneg ‖x‖]) (show p-2 ≤ 0 by linarith)
  have hq : 0 ≤ (a+‖x‖^2)^(p-2) := Real.rpow_nonneg (by positivity) _
  have hstep : p*n*a^(p-1) = (p*n*a)*a^(p-2) := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add ha, Real.rpow_one]
    ring
  rw [hstep]
  calc
    (p*n*a)*a^(p-2) ≤ (p*n*a)*(a+‖x‖^2)^(p-2) :=
      mul_le_mul_of_nonpos_left hpow (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hp.le hn0) ha.le)
    _ ≤ p*(a+‖x‖^2)^(p-2)*(n*a+ -(3/2:ℝ)*‖x‖^2) := by
      have := mul_nonneg (neg_nonneg.mpr hp.le) (mul_nonneg hq (sq_nonneg ‖x‖))
      nlinarith

lemma radialPower_laplacian_nonneg_outside {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E)
    (hx : (Module.finrank ℝ E + 1 : ℝ) * ε ≤ ‖x‖) :
    0 ≤ halfLaplacian (radialPower (ε^2) (smoothingExponent E)) x := by
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hbracket : n + 2*p-2 = -(3/2:ℝ) := by unfold p n smoothingExponent; ring
  rw [radialPower_halfLaplacian (sq_pos_of_pos hε)]
  change 0 ≤ p*(ε^2+‖x‖^2)^(p-2)*(n*ε^2+(n+2*p-2)*‖x‖^2)
  rw [hbracket]
  apply mul_nonneg_of_nonpos_of_nonpos
  · exact mul_nonpos_of_nonpos_of_nonneg hp.le (Real.rpow_nonneg (by positivity) _)
  · have hs : ((n+1)*ε)^2 ≤ ‖x‖^2 := sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hx
    have he : 0 ≤ ε^2 := sq_nonneg _
    have hnn : n ≤ (n+1)^2 := by nlinarith [sq_nonneg n]
    have hnn' := mul_le_mul_of_nonneg_right hnn he
    nlinarith

lemma radialBump_weighted_negative_bound {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E) :
    max (-halfLaplacian (radialBump (ε^2) (smoothingExponent E)) x) 0 * ‖x‖^2 ≤
      (Metric.closedBall (0 : E) ((Module.finrank ℝ E + 1 : ℝ)*ε)).indicator
        (fun _ => (-smoothingExponent E)*(Module.finrank ℝ E : ℝ)*
          (Module.finrank ℝ E + 1 : ℝ)^2*(ε^2)^(smoothingExponent E)) x := by
  classical
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hle := radialBump_negative_le hε2 p x
  by_cases hx : x ∈ Metric.closedBall (0 : E) ((n+1)*ε)
  · rw [Set.indicator_of_mem hx]
    have hx' : ‖x‖ ≤ (n+1)*ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hs : ‖x‖^2 ≤ ((n+1)*ε)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx'
    have hlower := radialPower_laplacian_lower hε2 hn x
    have hK : 0 ≤ (-p)*n*(ε^2)^(p-1) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr hp.le) hn0) (Real.rpow_nonneg hε2.le _)
    have hmax : max (-halfLaplacian (radialPower (ε^2) p) x) 0 ≤
        (-p)*n*(ε^2)^(p-1) := max_le (by linarith) hK
    calc
      _ ≤ ((-p)*n*(ε^2)^(p-1))*((n+1)*ε)^2 :=
        mul_le_mul (hle.trans hmax) hs (sq_nonneg _) hK
      _ = _ := by
        have hpow : (ε^2)^(p-1)*(ε^2) = (ε^2)^p := by
          calc
            _ = (ε^2)^(p-1)*(ε^2)^(1:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hε2]; congr 1; ring
        change (-p)*n*(ε^2)^(p-1)*((n+1)*ε)^2 = (-p)*n*(n+1)^2*(ε^2)^p
        rw [← hpow]
        ring
  · rw [Set.indicator_of_notMem hx]
    have hx' : (n+1)*ε ≤ ‖x‖ := by
      have := hx
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at this
      exact this.le
    have hnonneg := radialPower_laplacian_nonneg_outside hε hn x hx'
    have hzero : max (-halfLaplacian (radialPower (ε^2) p) x) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hnonneg)
    rw [hzero] at hle
    exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _)

section Integration
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma radialBump_integral_pos (hn : 1 ≤ Module.finrank ℝ E) :
    0 < ∫ x, radialBump (1/4) (smoothingExponent E) x ∂μ := by
  apply (radialBump_contDiff (E := E) (by norm_num : (0:ℝ)<1/4)
    (smoothingExponent E)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (radialBump_compact (by norm_num) (smoothingExponent_neg hn))
    (radialBump_nonneg _ _)
  apply ne_of_gt (smoothPositivePart_pos (t := radialPower (1/4) (smoothingExponent E) (0:E)-1) _)
  simp only [radialPower, norm_zero, sq, mul_zero, add_zero]
  exact sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg
    (by norm_num) (by norm_num) (smoothingExponent_neg hn))

lemma radialBump_integral_lower {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (hn : 1 ≤ Module.finrank ℝ E) :
    (∫ x, radialBump (1/4) (smoothingExponent E) x ∂μ) ≤
      ∫ x, radialBump a (smoothingExponent E) x ∂μ := by
  apply integral_mono
  · exact (radialBump_contDiff (by norm_num) _).continuous.integrable_of_hasCompactSupport
      (radialBump_compact (by norm_num) (smoothingExponent_neg hn))
  · exact (radialBump_contDiff ha _).continuous.integrable_of_hasCompactSupport
      (radialBump_compact ha (smoothingExponent_neg hn))
  · exact fun x => radialBump_antitone_parameter ha ha' (smoothingExponent_neg hn).le x

omit [MeasurableSpace E] [BorelSpace E] in
lemma radial_weight_exponent {ε : ℝ} (hε : 0 < ε) :
    ε^(Module.finrank ℝ E) * (ε^2)^(smoothingExponent E) = Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast_mul hε.le 2,
    ← Real.rpow_add hε]
  congr 1
  unfold smoothingExponent
  push_cast
  ring

lemma radialBump_integral_negative_bound {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) :
    (∫ x, max (-halfLaplacian (radialBump (ε^2) (smoothingExponent E)) x) 0 * ‖x‖^2 ∂μ) ≤
      μ.real (Metric.ball (0:E) 1) * (-smoothingExponent E) *
        (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E+2) *
        Real.sqrt ε := by
  let n : ℝ := Module.finrank ℝ E
  let p := smoothingExponent E
  let R := (n+1)*ε
  let K := (-p)*n*(n+1)^2*(ε^2)^p
  have hR : 0 ≤ R := by dsimp [R,n]; positivity
  have hI : Integrable ((Metric.closedBall (0:E) R).indicator (fun _ => K)) μ :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => mul_nonneg (le_max_right _ _) (sq_nonneg _))) hI
    (Filter.Eventually.of_forall (radialBump_weighted_negative_bound hε hn))
  refine hbound.trans_eq ?_
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
  rw [Measure.real_def, μ.addHaar_closedBall (0:E) hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hR _)]
  dsimp [R,K,n,p]
  rw [mul_pow]
  have he := radial_weight_exponent (E := E) hε
  have he' : ε^(Module.finrank ℝ E)*(ε^2)^(smoothingExponent E) = Real.sqrt ε := he
  change ((Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E)*ε^(Module.finrank ℝ E)*
    μ.real (Metric.ball (0:E) 1)) *
    ((-smoothingExponent E)*(Module.finrank ℝ E : ℝ)*(Module.finrank ℝ E + 1 : ℝ)^2*
    (ε^2)^(smoothingExponent E)) = _
  rw [pow_add, ← he']
  ring

theorem exists_radial_smoothing (hn : 1 ≤ Module.finrank ℝ E) {η : ℝ} (hη : 0 < η) :
    ∃ b : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∂μ ∧
      (∫ x, max (-halfLaplacian b x) 0 * ‖x‖^2 ∂μ) < η * ∫ x, b x ∂μ := by
  let p := smoothingExponent E
  let m := ∫ x, radialBump (1/4) p x ∂μ
  let K := μ.real (Metric.ball (0:E) 1) * (-p) * (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E+2)
  have hm : 0 < m := radialBump_integral_pos μ hn
  have hp : p < 0 := smoothingExponent_neg hn
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (ENNReal.toReal_nonneg)
      (neg_nonneg.mpr hp.le)) (Nat.cast_nonneg _)) (by positivity)
  obtain ⟨t,ht,ht'⟩ := exists_pos_mul_lt (mul_pos hη hm) (K+1)
  let δ := min t (1/2:ℝ)
  have hδ : 0 < δ := lt_min ht (by norm_num)
  have hδt : δ ≤ t := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := min_le_right _ _
  have hsmall : K*δ < η*m := by
    have := mul_le_mul_of_nonneg_left hδt (show 0 ≤ K+1 by linarith)
    nlinarith
  let ε := δ^2
  have hε : 0 < ε := sq_pos_of_pos hδ
  have hεlimit : ε^2 ≤ 1/4 := by
    have hs : δ^2 ≤ 1/4 := by nlinarith
    dsimp [ε]
    calc
      (δ^2)^2 ≤ (1/4:ℝ)^2 := (sq_le_sq₀ (sq_nonneg _) (by norm_num)).mpr hs
      _ ≤ 1/4 := by norm_num
  refine ⟨radialBump (ε^2) p, radialBump_contDiff (sq_pos_of_pos hε) p,
    radialBump_compact (sq_pos_of_pos hε) hp, radialBump_nonneg _ _, ?_, ?_⟩
  · exact hm.trans_le (radialBump_integral_lower μ (sq_pos_of_pos hε) hεlimit hn)
  · have hupper := radialBump_integral_negative_bound μ hε hn
    have hroot : Real.sqrt ε = δ := by dsimp [ε]; rw [Real.sqrt_sq hδ.le]
    change _ ≤ K*Real.sqrt ε at hupper
    rw [hroot] at hupper
    exact hupper.trans_lt (hsmall.trans_le (mul_le_mul_of_nonneg_left
      (radialBump_integral_lower μ (sq_pos_of_pos hε) hεlimit hn) hη.le))

end Integration

end Radial

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

lemma hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  have hG : (fun y => fderiv ℝ (f ∘ L) y) =
      (fun y => (fderiv ℝ f (L y)).comp L) := by
    funext y
    exact ((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h := (((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp
    (hasFDerivAt_const L x))
  dsimp only [Function.comp_def] at h
  unfold hessianB
  rw [hG, h.fderiv]
  simp

lemma hessianB_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v w : E) :
    hessianB (fun y => f y*g y) x v w =
      f x*hessianB g x v w + g x*hessianB f x v w +
      fderiv ℝ f x v*fderiv ℝ g x w + fderiv ℝ g x v*fderiv ℝ f x w := by
  have hf' (x : E) := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : E) := (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z*g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hf' x).smul (hgd x).hasFDerivAt).add
    ((hg' x).smul (hfd x).hasFDerivAt)
  unfold hessianB
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) + g • fun y => fderiv ℝ f y) x) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

lemma hessianB_prod_horizontal {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : E) :
    hessianB (fun x : E × F => f x.1*g x.2) x (v,0) (w,0) =
      g x.2*hessianB f x.1 v w := by
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => f x.1) := hf.comp contDiff_fst
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => g x.2) := hg.comp contDiff_snd
  rw [hessianB_mul hf1 hg2]
  rw [show (fun x : E×F => f x.1) = f ∘ ContinuousLinearMap.fst ℝ E F from rfl,
    show (fun x : E×F => g x.2) = g ∘ ContinuousLinearMap.snd ℝ E F from rfl,
    hessianB_linear_comp hf, hessianB_linear_comp hg]
  have hfg := ((hg.differentiable (by simp) x.2).hasFDerivAt.comp x
    (ContinuousLinearMap.snd ℝ E F).hasFDerivAt).fderiv
  change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.snd ℝ E F)) x = _ at hfg
  rw [hfg]
  simp

lemma hessianB_prod_vertical {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : F) :
    hessianB (fun x : E × F => f x.1*g x.2) x (0,v) (0,w) =
      f x.1*hessianB g x.2 v w := by
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => f x.1) := hf.comp contDiff_fst
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => g x.2) := hg.comp contDiff_snd
  rw [hessianB_mul hf1 hg2]
  rw [show (fun x : E×F => f x.1) = f ∘ ContinuousLinearMap.fst ℝ E F from rfl,
    show (fun x : E×F => g x.2) = g ∘ ContinuousLinearMap.snd ℝ E F from rfl,
    hessianB_linear_comp hf, hessianB_linear_comp hg]
  have hfg := ((hf.differentiable (by simp) x.1).hasFDerivAt.comp x
    (ContinuousLinearMap.fst ℝ E F).hasFDerivAt).fderiv
  change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.fst ℝ E F)) x = _ at hfg
  rw [hfg]
  simp

lemma hessianB_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (hessianB f) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous_fderiv (by simp)

lemma hessianB_compact {f : E → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (hessianB f) := (hf.fderiv ℝ).fderiv ℝ

lemma hessianB_apply_continuous {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v w : E) : Continuous (fun x => hessianB f x v w) :=
  ((hessianB_continuous hf).clm_apply continuous_const).clm_apply continuous_const

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

lemma bilinear_orthonormal_trace (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    ∑ i, B (e i) (e i) = ∑ j, B (f j) (f j) := by
  classical
  have hex (x y : E) : B x y = ∑ j, ∑ l,
      (inner ℝ (f j) x * inner ℝ (f l) y) * B (f j) (f l) := by
    conv_lhs => rw [← f.sum_repr x, ← f.sum_repr y]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, OrthonormalBasis.repr_apply_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_lhs => arg 2; intro i; rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hsum (l : κ) : ∑ i, inner ℝ (f j) (e i) * inner ℝ (f l) (e i) =
      if j=l then 1 else 0 := by
    simpa only [real_inner_comm (f l), f.inner_eq_ite, eq_comm] using e.sum_inner_mul_inner (f j) (f l)
  simp_rw [hsum]
  simp

end Trace

section MatrixContraction

lemma pi_basis_expansion {n : ℕ} (v : Fin n → ℝ) :
    v = ∑ j, v j • Pi.single j (1:ℝ) := by
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm

lemma bilinear_matrix_pushforward {k n : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by
  have hex (v w : Fin k → ℝ) : B v w = ∑ j, ∑ l,
      (v j*w l)*B (Pi.single j 1) (Pi.single l 1) := by
    conv_lhs => rw [pi_basis_expansion v, pi_basis_expansion w]
    simp only [map_sum, map_smul, _root_.sum_apply,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  conv_rhs => arg 2; intro a; arg 2; intro b; rw [hex]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro b; rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]; arg 2; intro j; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.DifferentialSplitting ----
namespace OAI

universe uDomain uAction uVertical uCodomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Operator
variable {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}

lemma secondOperator_continuous (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (secondOperator C v f) := by
  unfold secondOperator
  apply continuous_const.mul
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro l hl
  exact continuous_const.mul (hessianB_apply_continuous hf _ _)

lemma secondOperator_compact (C : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → E)
    {f : E → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (secondOperator C v f) := by
  apply (hessianB_compact hf).comp_left (g := fun B => (1/2:ℝ)*∑ j, ∑ l, C j l*B (v j) (v l))
  simp

end Operator

section Scale
variable (H : Type uAction) (V : Type uVertical) [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]

end Scale

section SplitDifferential
variable {k d : ℕ} {H : Type uAction} {V : Type uVertical}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma split_differential
    (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ)
    (hsplit : C = R*R.transpose+Z*C*Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] H×V) (eh : OrthonormalBasis (Fin d) ℝ H)
    (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (eh j,0))
    (hZ : ∀ j, e (fun l => Z l j) = (0,z j))
    (f : H → ℝ) (g : V → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (t : ℝ) (ht : t ≠ 0) (x : Fin k → ℝ) :
    let et := e.trans (scaleVertical H V t ht)
    let b := (fun y : H×V => f y.1*g y.2) ∘ et
    secondOperator C (fun j => Pi.single j 1) b x =
      g (et x).2 * halfLaplacian f (et x).1 +
      t^2*f (et x).1*secondOperator C z g (et x).2 := by
  dsimp only
  let et := e.trans (scaleVertical H V t ht)
  let b := (fun y : H×V => f y.1*g y.2) ∘ et
  change secondOperator C (fun j => Pi.single j 1) b x = _
  have hfg : ContDiff ℝ (⊤ : ℕ∞) (fun y : H×V => f y.1*g y.2) :=
    (hf.comp contDiff_fst).mul (hg.comp contDiff_snd)
  have hb (v w : Fin k → ℝ) : hessianB b x v w =
      hessianB (fun y : H×V => f y.1*g y.2) (et x) (et v) (et w) :=
    hessianB_linear_comp hfg et.toContinuousLinearMap x v w
  have hhr (j : Fin d) : et (fun l => R l j) = (eh j,0) := by simp [et,hR]
  have hhz (j : Fin k) : et (fun l => Z l j) = (0,t • z j) := by simp [et,hZ]
  have hhor : ∑ j, hessianB b x (fun l => R l j) (fun l => R l j) =
      g (et x).2 * ∑ j, hessianB f (et x).1 (eh j) (eh j) := by
    simp only [hb, hhr, hessianB_prod_horizontal hf hg, Finset.mul_sum]
  have hver : ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) =
      t^2*f (et x).1 * ∑ j, ∑ l, C j l*hessianB g (et x).2 (z j) (z l) := by
    simp only [hb, hhz, hessianB_prod_vertical hf hg, map_smul,
      _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    ring
  unfold secondOperator
  have hcon : ∑ j, ∑ l, C j l*hessianB b x (Pi.single j 1) (Pi.single l 1) =
      (∑ j, hessianB b x (fun l => R l j) (fun l => R l j)) +
      ∑ j, ∑ l, C j l*hessianB b x (fun a => Z a j) (fun a => Z a l) := by
    conv_lhs => rw [hsplit]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    congr 1
    · have he := bilinear_matrix_pushforward (hessianB b x) R 1
      simpa [Matrix.one_apply] using he
    · exact bilinear_matrix_pushforward (hessianB b x) Z C
  rw [hcon, hhor, hver]
  have htrace := bilinear_orthonormal_trace (hessianB f (et x).1) eh (stdOrthonormalBasis ℝ H)
  rw [htrace]
  simp only [halfLaplacian, ← hessianB_eq]
  ring

end SplitDifferential
end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

lemma haar_linear_change {E : Type uDomain} {F : Type uCodomain}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : F → ℝ, Continuous f →
      (∫ x, f (e x) ∂μ) = c * ∫ y, f y ∂ν := by
  let : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let c := (μ.map e).addHaarScalarFactor ν
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  refine ⟨c, by exact_mod_cast hc, ?_⟩
  intro f hf
  rw [← integral_map e.continuous.measurable.aemeasurable hf.aestronglyMeasurable,
    Measure.isAddLeftInvariant_eq_smul (μ.map e) ν]
  simp [c, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

lemma compact_prod_mul {E : Type uDomain} {F : Type uCodomain} [TopologicalSpace E] [TopologicalSpace F]
    [R1Space E] [R1Space F] {f : E → ℝ} {g : F → ℝ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun x : E×F => f x.1*g x.2) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.prod hg)
  rintro ⟨x,y⟩ h
  have hx : f x ≠ 0 := by intro h0; exact h (by simp [h0])
  have hy : g y ≠ 0 := by intro h0; exact h (by simp [h0])
  exact ⟨subset_closure hx, subset_closure hy⟩

end EuclideanRamsey

open MeasureTheory
namespace EuclideanRamsey

lemma product_negative_integral_bound {E : Type uDomain} {F : Type uCodomain}
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [SFinite μ] [SFinite ν]
    (f a w : E → ℝ) (g b : F → ℝ) (t : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) (hw : ∀ x, 0 ≤ w x)
    (haI : Integrable (fun x => max (-a x) 0*w x) μ)
    (hfI : Integrable (fun x => f x*w x) μ)
    (hgI : Integrable g ν) (hbI : Integrable (fun y => |b y|) ν) :
    (∫ z : E×F, max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0*w z.1 ∂μ.prod ν) ≤
      (∫ x, max (-a x) 0*w x ∂μ)*(∫ y, g y ∂ν) +
      t^2*(∫ x, f x*w x ∂μ)*(∫ y, |b y| ∂ν) := by
  have hI := (haI.mul_prod hgI).add ((hfI.mul_prod hbI).const_mul (t^2))
  have hbound (z : E×F) :
      max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0*w z.1 ≤
      (max (-a z.1) 0*w z.1)*g z.2+t^2*((f z.1*w z.1)*|b z.2|) := by
    have h : max (-(g z.2*a z.1+t^2*f z.1*b z.2)) 0 ≤
        g z.2*max (-a z.1) 0+t^2*f z.1*|b z.2| := by
      apply max_le
      · have ha := le_max_left (-a z.1) 0
        have hb := neg_le_abs (b z.2)
        nlinarith [mul_le_mul_of_nonneg_left ha (hg z.2),
          mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg t) (hf z.1))]
      · exact add_nonneg (mul_nonneg (hg z.2) (le_max_right _ _))
          (mul_nonneg (mul_nonneg (sq_nonneg t) (hf z.1)) (abs_nonneg _))
    calc
      _ ≤ (g z.2*max (-a z.1) 0+t^2*f z.1*|b z.2|)*w z.1 :=
        mul_le_mul_of_nonneg_right h (hw z.1)
      _ = _ := by ring
  refine (integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => mul_nonneg (le_max_right _ _) (hw z.1))) hI
    (Filter.Eventually.of_forall hbound)).trans_eq ?_
  change (∫ z : E×F, (max (-a z.1) 0*w z.1)*g z.2+
    t^2*((f z.1*w z.1)*|b z.2|) ∂μ.prod ν) = _
  rw [integral_add (haI.mul_prod hgI) ((hfI.mul_prod hbI).const_mul (t^2)),
    integral_const_mul, integral_prod_mul (fun x => max (-a x) 0*w x) g,
    integral_prod_mul (fun x => f x*w x) (fun y => |b y|)]
  ring

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

lemma halfLaplacian_continuous {H : Type uAction} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {f : H → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (halfLaplacian f) := by
  change Continuous (fun x => halfLaplacian f x)
  simp only [halfLaplacian, ← hessianB_eq]
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun j hj => hessianB_apply_continuous hf _ _)

lemma halfLaplacian_compact {H : Type uAction} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {f : H → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (halfLaplacian f) := by
  change HasCompactSupport (fun x => halfLaplacian f x)
  simp only [halfLaplacian, ← hessianB_eq]
  apply (hessianB_compact hf).comp_left
    (g := fun B => (1/2:ℝ)*∑ j, B (stdOrthonormalBasis ℝ H j) (stdOrthonormalBasis ℝ H j))
  simp

 theorem exists_split_smoothing {k d : ℕ} {H : Type uAction} {V : Type uVertical}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
    (hn : 1 ≤ Module.finrank ℝ H)
    (C : Matrix (Fin k) (Fin k) ℝ) (R : Matrix (Fin k) (Fin d) ℝ)
    (Z : Matrix (Fin k) (Fin k) ℝ)
    (hsplit : C = R*R.transpose+Z*C*Z.transpose)
    (e : (Fin k → ℝ) ≃L[ℝ] H×V) (eh : OrthonormalBasis (Fin d) ℝ H)
    (z : Fin k → V)
    (hR : ∀ j, e (fun l => R l j) = (eh j,0))
    (hZ : ∀ j, e (fun l => Z l j) = (0,z j))
    {η : ℝ} (hη : 0 < η) :
    ∃ b : (Fin k → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∧
      (∫ x, max (-secondOperator C (fun j => Pi.single j 1) b x) 0 * ‖(e x).1‖^2) <
        η * ∫ x, b x := by
  let μH : Measure H := Measure.addHaar
  let μV : Measure V := Measure.addHaar
  obtain ⟨f,hfs,hfc,hfp,hfm,hfsmall⟩ := exists_radial_smoothing μH hn (η := η/2) (by positivity)
  let g₀ : ContDiffBump (0:V) := ⟨1,2,by norm_num,by norm_num⟩
  let g : V → ℝ := g₀
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := g₀.contDiff
  have hgc : HasCompactSupport g := g₀.hasCompactSupport
  have hgp : ∀ y, 0 ≤ g y := g₀.nonneg'
  have hgm : 0 < ∫ y, g y ∂μV := g₀.integral_pos
  let a := halfLaplacian f
  let bV := secondOperator C z g
  have hac : Continuous a := halfLaplacian_continuous hfs
  have hak : HasCompactSupport a := halfLaplacian_compact hfc
  have hbc : Continuous bV := secondOperator_continuous C z hgs
  have hbk : HasCompactSupport bV := secondOperator_compact C z hgc
  have haI : Integrable (fun x => max (-a x) 0*‖x‖^2) μH := by
    have hk : HasCompactSupport (fun x => max (-a x) 0) :=
      hak.comp_left (g := fun r : ℝ => max (-r) 0) (by simp)
    exact ((hac.neg.max continuous_const).mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hk.mul_right
  have hfI : Integrable (fun x => f x*‖x‖^2) μH :=
    (hfs.continuous.mul (continuous_norm.pow 2)).integrable_of_hasCompactSupport hfc.mul_right
  have hgI : Integrable g μV := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hbI : Integrable (fun y => |bV y|) μV :=
    hbc.abs.integrable_of_hasCompactSupport hbk.abs
  let K := (∫ x, f x*‖x‖^2 ∂μH)*(∫ y, |bV y| ∂μV)
  have hK : 0 ≤ K := mul_nonneg
    (integral_nonneg (fun x => mul_nonneg (hfp x) (sq_nonneg _)))
    (integral_nonneg (fun y => abs_nonneg _))
  obtain ⟨t₀,ht₀,htsmall⟩ := exists_pos_mul_lt
    (mul_pos (mul_pos (show 0 < η/2 by positivity) hfm) hgm) (K+1)
  let t := min t₀ 1
  have ht : 0 < t := lt_min ht₀ zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htt₀ : t ≤ t₀ := min_le_left _ _
  have hsmall : t^2*K < (η/2)*(∫ x,f x ∂μH)*(∫ y,g y ∂μV) := by
    have h : (K+1)*t ≤ (K+1)*t₀ := mul_le_mul_of_nonneg_left htt₀ (by linarith)
    have hsq : t^2 ≤ t := by nlinarith
    have hsqK := mul_le_mul_of_nonneg_right hsq hK
    nlinarith
  let et := e.trans (scaleVertical H V t ht.ne')
  let b := (fun y : H×V => f y.1*g y.2) ∘ et
  have hfgs : ContDiff ℝ (⊤ : ℕ∞) (fun y : H×V => f y.1*g y.2) :=
    (hfs.comp contDiff_fst).mul (hgs.comp contDiff_snd)
  have hbs : ContDiff ℝ (⊤ : ℕ∞) b := hfgs.comp et.contDiff
  have hbk' : HasCompactSupport b := (compact_prod_mul hfc hgc).comp_homeomorph et.toHomeomorph
  obtain ⟨c,hc,hchange⟩ := haar_linear_change et volume (μH.prod μV)
  have hmass : (∫ x,b x) = c*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    change (∫ x, f (et x).1*g (et x).2) = _
    rw [hchange _ hfgs.continuous, integral_prod_mul]
  have hetfst (x : Fin k → ℝ) : (et x).1 = (e x).1 := rfl
  have hdiff (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      g (et x).2*a (et x).1+t^2*f (et x).1*bV (et x).2 :=
    split_differential C R Z hsplit e eh z hR hZ f g hfs hgs t ht.ne' x
  let φ : H×V → ℝ := fun y => max (-(g y.2*a y.1+t^2*f y.1*bV y.2)) 0*‖y.1‖^2
  have hφ : Continuous φ := by
    dsimp [φ]
    exact ((((hgs.continuous.comp continuous_snd).mul (hac.comp continuous_fst)).add
      ((continuous_const.mul (hfs.continuous.comp continuous_fst)).mul
        (hbc.comp continuous_snd))).neg.max continuous_const).mul ((continuous_fst.norm).pow 2)
  have hneg : (∫ x, max (-secondOperator C (fun j => Pi.single j 1) b x) 0*‖(e x).1‖^2) =
      c*∫ y, φ y ∂μH.prod μV := by
    conv_lhs => arg 2; intro x; rw [hdiff, ← hetfst]
    exact hchange φ hφ
  have hbound := product_negative_integral_bound μH μV f a (fun x => ‖x‖^2) g bV t
    hfp hgp (fun x => sq_nonneg _) haI hfI hgI hbI
  have hfinal : (∫ y,φ y ∂μH.prod μV) < η*((∫ x,f x ∂μH)*(∫ y,g y ∂μV)) := by
    have hh := mul_lt_mul_of_pos_right hfsmall hgm
    change _ < η/2 * _ * _ at hh
    rw [mul_assoc (t^2)] at hbound
    change _ ≤ _ + t^2*K at hbound
    change _ < _ at hsmall
    dsimp only [φ] at *
    nlinarith
  refine ⟨b,hbs,hbk',fun x => mul_nonneg (hfp _) (hgp _),?_,?_⟩
  · rw [hmass]; positivity
  · rw [hneg,hmass]
    nlinarith [mul_lt_mul_of_pos_left hfinal hc]

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.SmoothingMatrix ----
namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma covariance_splitting {k d : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ) (hC : C.IsSymm)
    (hU : U * C * U.transpose = 1) :
    let R := C * U.transpose
    let Z := 1 - R * U
    U * R = 1 ∧ U * Z = 0 ∧ C = R * R.transpose + Z * C * Z.transpose := by
  dsimp only
  let R := C * U.transpose
  have hR : U * R = 1 := by simpa only [R, ← Matrix.mul_assoc] using hU
  have hRt : R.transpose = U * C := by simp only [R, Matrix.transpose_mul,
    Matrix.transpose_transpose, hC.eq]
  have hRR : R.transpose * U.transpose = 1 := by
    rw [← Matrix.transpose_mul, hR, Matrix.transpose_one]
  refine ⟨hR, ?_, ?_⟩
  · change U * (1 - R * U) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]
  · change C = R * R.transpose + (1 - R * U) * C * (1 - R * U).transpose
    have ht : (1 - R * U).transpose = 1 - U.transpose * R.transpose := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
    have h1 : R * U * C = R * R.transpose := by rw [hRt, Matrix.mul_assoc]
    have h2 : C * (U.transpose * R.transpose) = R * R.transpose := by
      rw [← Matrix.mul_assoc]
    have h3 : R * R.transpose * (U.transpose * R.transpose) = R * R.transpose := by
      rw [ Matrix.mul_assoc, ← Matrix.mul_assoc R.transpose, hRR, Matrix.one_mul]
    simp only [ht, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      h1, h2, h3]
    abel

end EuclideanRamsey

open scoped BigOperators
open MeasureTheory Matrix
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open MeasureTheory Matrix
open scoped BigOperators

theorem compact_smoothing : CompactSmoothing := by
  intro k d hd C U hC hU η hη
  let R := C * U.transpose
  let Z : Matrix (Fin k) (Fin k) ℝ := 1-R*U
  obtain ⟨hUR,hUZ,hsplit⟩ := covariance_splitting C U hC hU
  change U*R=1 at hUR
  change U*Z=0 at hUZ
  change C=R*R.transpose+Z*C*Z.transpose at hsplit
  let H := EuclideanSpace ℝ (Fin d)
  let eH : H ≃ₗ[ℝ] (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv
  let u : (Fin k → ℝ) →ₗ[ℝ] H := eH.symm.toLinearMap.comp (Matrix.toLin' U)
  let r : H →ₗ[ℝ] (Fin k → ℝ) := (Matrix.toLin' R).comp eH.toLinearMap
  have hur : u.comp r = LinearMap.id := by
    apply LinearMap.ext
    intro y
    simp only [u,r,LinearMap.comp_apply,Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hUR, Matrix.one_mulVec]
    exact eH.symm_apply_apply y
  let V := LinearMap.ker u
  let e : (Fin k → ℝ) ≃L[ℝ] H×V := (rightInverseSplit u r hur).toContinuousLinearEquiv
  let eh : OrthonormalBasis (Fin d) ℝ H := EuclideanSpace.basisFun (Fin d) ℝ
  have hRv (j : Fin d) : r (eh j) = fun l => R l j := by
    change R.mulVec (eH (eh j)) = _
    have h : eH (eh j) = Pi.single j 1 := by
      change ((EuclideanSpace.basisFun (Fin d) ℝ) j).ofLp = _
      rw [EuclideanSpace.basisFun_apply]
      rfl
    rw [h, Matrix.mulVec_single]
    simp
    rfl
  have hZv (j : Fin k) : (fun l => Z l j) ∈ LinearMap.ker u := by
    rw [LinearMap.mem_ker]
    change eH.symm (U.mulVec (fun l => Z l j)) = 0
    have h : U.mulVec (fun l => Z l j) = 0 := by
      ext a
      change (U*Z) a j = 0
      rw [hUZ]; rfl
    rw [h,map_zero]
  let z : Fin k → V := fun j => ⟨fun l => Z l j,hZv j⟩
  have hR (j : Fin d) : e (fun l => R l j) = (eh j,0) := by
    rw [← hRv]
    exact rightInverseSplit_apply_R u r hur (eh j)
  have hZ (j : Fin k) : e (fun l => Z l j) = (0,z j) := by
    apply Prod.ext
    · exact hZv j
    · apply Subtype.ext
      change (fun l => Z l j) - r (u (fun l => Z l j)) = _
      rw [show u (fun l => Z l j) = 0 from hZv j,map_zero,sub_zero]
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  have hn : 1 ≤ Module.finrank ℝ H := by simpa [H] using hd
  obtain ⟨b,hbs,hbk,hbp,hbm,hsmall⟩ := exists_split_smoothing hn C R Z hsplit e eh z hR hZ hη
  refine ⟨b,hbs,hbk,hbp,hbm,?_⟩
  have hw (x : Fin k → ℝ) : ‖(e x).1‖^2 = gradientWeight U x := by
    change ‖eH.symm (U.mulVec x)‖^2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hop (x : Fin k → ℝ) : secondOperator C (fun j => Pi.single j 1) b x =
      stencilDifferential C b x := by simp only [secondOperator,stencilDifferential,hessianB_eq]
  simpa only [hw,hop] using hsmall

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.LatticeMoments ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix

open scoped TensorProduct
namespace EuclideanRamsey

section Algebra
variable {k : ℕ}

lemma monomial_sub_one_mem (γ : Lattice k) :
    AddMonoidAlgebra.single γ 1 - 1 ∈ (augmentationIdeal : Ideal (LatticeRing k)) := by
  change augmentation _ = 0
  simp

lemma mem_augmentationIdeal (x : LatticeRing k) :
    x ∈ augmentationIdeal ↔ mass x = 0 := by
  change augmentation x = 0 ↔ _
  rw [augmentation_eq_mass]

lemma augmentation_sq_le_jetOne : (augmentationIdeal : Ideal (LatticeRing k)) ^ 2 ≤ jetOne := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 := (mem_augmentationIdeal y).mp hy
  change mass (x*y) = 0 ∧ ∀ a, firstMoment (x*y) a = 0
  simp [firstMoment_mul, hx0, hy0]

lemma augmentation_cube_le_jetTwo : (augmentationIdeal : Ideal (LatticeRing k)) ^ 3 ≤ jetTwo := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 : mass y = 0 ∧ ∀ a, firstMoment y a = 0 := augmentation_sq_le_jetOne hy
  change mass (x*y) = 0 ∧ (∀ a, firstMoment (x*y) a = 0) ∧ ∀ a b, secondMoment (x*y) a b = 0
  simp [firstMoment_mul, secondMoment_mul, hx0, hy0]

lemma moments_eq_of_sub_mem_cube {x y : LatticeRing k}
    (h : x-y ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3) :
    mass x = mass y ∧ (∀ a, firstMoment x a = firstMoment y a) ∧
      ∀ a b, secondMoment x a b = secondMoment y a b := by
  have hh := augmentation_cube_le_jetTwo h
  change mass (x-y) = 0 ∧ (∀ a, firstMoment (x-y) a = 0) ∧ ∀ a b, secondMoment (x-y) a b = 0 at hh
  simpa only [mass_sub, firstMoment_sub, secondMoment_sub, sub_eq_zero] using hh

lemma quadraticStencil_moments (C : Matrix (Fin k) (Fin k) ℚ) (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [quadraticStencil, hm]
  · intro a
    simp [quadraticStencil, firstMoment_mul, hm]
  · intro a b
    simp only [quadraticStencil, secondMoment_smul, secondMoment_sum, secondMoment_mul, hm,
      hf, zero_mul, mul_zero, zero_add]
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hs : C b a = C a b := congrFun (congrFun hC a) b
    rw [hs]
    ring

end Algebra
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Discretization ----
namespace OAI

universe uDomain uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

lemma compact_taylor_bound {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x h : E,
      |f (x+h)-f x-fderiv ℝ f x h-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by
  obtain ⟨K,hK⟩ := (hf.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨K,hK0,?_⟩
  intro x h
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := f) (x := x) (y := h)
    (fun t ht => (hf.of_le (by norm_cast)).contDiffAt)
  have he : f (x+h)-f x-fderiv ℝ f x h-(1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h] =
      (1/2:ℝ)*∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h) := by
    have hvec : (fun _ : Fin 2 => h) = ![h,h] := by ext i; fin_cases i <;> rfl
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial,
      Nat.cast_one,Nat.cast_mul,inv_one,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,smul_eq_mul,hvec] at ht
    linarith
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)| ≤
      K*‖h‖^3 := by
    have ht (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        ‖(1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hm := (iteratedFDeriv ℝ 3 f (x+t • h)).le_opNorm (fun _ => h)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hm
      have hd : ‖iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 :=
        hm.trans (mul_le_mul_of_nonneg_right (hK _) (by positivity))
      have ht2 : (1-t)^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      calc
        _ ≤ 1 * (K*‖h‖^3) := mul_le_mul ht2 hd (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := K*‖h‖^3) (fun t ht' => ht t ⟨(by simpa using ht'.1 : 0 < t).le,by simpa using ht'.2⟩)
    simpa using hh
  nlinarith [mul_nonneg hK0 (pow_nonneg (norm_nonneg h) 3)]

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

lemma linear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) = ∑ j,(∑ γ ∈ S,q γ*v γ j)*L (Pi.single j 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  conv_lhs => arg 2; intro γ; rw [hv γ]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro γ hγ
  ring

lemma bilinear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) (v γ) =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  have he (γ : ι) : q γ*L (v γ) (v γ) =
      ∑ j,∑ l,q γ*v γ j*v γ l*L (Pi.single j 1) (Pi.single l 1) := by
    have hfirst := congrArg (fun a => L a (v γ)) (hv γ)
    rw [hfirst]
    simp only [map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hsecond := congrArg (fun a => L (Pi.single j 1) a) (hv γ)
    rw [hsecond]
    simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [he,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

lemma latticeSample_injective {k n : ℕ} (hn : n ≠ 0) :
    Function.Injective (@latticeSample k n) := by
  intro γ δ h
  funext j
  have he := congr_fun h j
  dsimp [latticeSample] at he
  exact_mod_cast (div_left_inj' (show (n:ℝ) ≠ 0 by exact_mod_cast hn)).mp he

lemma latticeSample_mem_grid {k n : ℕ} (hn : n ≠ 0) (γ : Fin k → ℤ) :
    latticeSample n γ ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul]
  apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
  intro j
  refine ⟨γ j,?_⟩
  change (γ j : ℝ) = (n:ℝ)*((γ j : ℝ)/n)
  field_simp

lemma grid_surjective {k n : ℕ} (hn : n ≠ 0) {x : Fin k → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ∃ γ, latticeSample n γ = x := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul] at hx
  have h := BoxIntegral.unitPartition.mem_smul_span_iff.mp hx
  choose γ hγ using h
  refine ⟨γ,?_⟩
  funext j
  simp only [latticeSample]
  have he : (γ j : ℝ) = (n:ℝ)*x j := hγ j
  rw [he]
  exact mul_div_cancel_left₀ (x j) (by exact_mod_cast hn)

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n:ℝ)⁻¹ • realLattice k), f x := by
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃
      ↑(s ∩ (n:ℝ)⁻¹ • realLattice k) := Equiv.ofBijective
    (fun γ => ⟨latticeSample n γ,γ.property,latticeSample_mem_grid hn γ.val⟩) (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact latticeSample_injective hn (congr_arg Subtype.val h)
      · intro x
        obtain ⟨γ,hγ⟩ := grid_surjective hn x.property.2
        exact ⟨⟨γ,by simpa [hγ] using x.property.1⟩,Subtype.ext hγ⟩)
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s})
    (f := fun γ => f (latticeSample n γ)) (fun γ hγ => hf hγ)]
  exact e.tsum_eq (fun x => f x)

theorem lattice_riemann {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨R,hR,hfR⟩ := hfc.exists_pos_le_norm
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hs : Function.support f ⊆ s := by
    intro x hx
    rw [show s = Metric.closedBall 0 R from rfl, Metric.mem_closedBall,dist_zero_right]
    exact le_of_lt (lt_of_not_ge (fun h => hx (hfR x h)))
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have h := tendsto_tsum_div_pow_atTop_integral s f hf Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hi : (∫ x in s,f x) = ∫ x,f x := by
    rw [← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hs]
  simp only [Fintype.card_fin,hi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lattice_tsum_eq_grid (by omega) s f hs]

lemma latticeSample_finite_support {k n : ℕ} (hn : n ≠ 0)
    {f : (Fin k → ℝ) → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ)) := by
  let b := Pi.basisFun ℝ (Fin k)
  have hb : Bornology.IsBounded ((n:ℝ) • tsupport f) :=
    (hf.isCompact.image (show Continuous (fun x : Fin k → ℝ => (n:ℝ) • x) by fun_prop)).isBounded
  have hfinite := ZSpan.setFinite_inter b hb
  let cast : (Fin k → ℤ) → (Fin k → ℝ) := fun γ j => γ j
  have hinj : Function.Injective cast := by
    intro x y h
    ext j
    have he : (x j : ℝ) = (y j : ℝ) := congr_fun h j
    exact_mod_cast he
  apply ((hfinite.preimage hinj.injOn).subset ?_)
  intro γ hγ
  have hs : latticeSample n γ ∈ tsupport f := subset_closure hγ
  constructor
  · refine ⟨latticeSample n γ,hs,?_⟩
    ext j
    change (n:ℝ)*((γ j : ℝ)/n) = (γ j : ℝ)
    field_simp
  · change cast γ ∈ Submodule.span ℤ (Set.range b)
    rw [b.mem_span_iff_repr_mem ℤ]
    intro j
    exact ⟨γ j,by simp [b,cast]⟩

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.RationalConvolution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uGroup uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

lemma bounded_grid_finite {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) :
    (s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (by exact_mod_cast hn))]
  exact ZSpan.setFinite_inter _ hs

lemma lattice_sum_perturb_bound {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) (f g : (Fin k → ℝ) → ℝ)
    (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s)
    (ε : ℝ) (hb : ∀ x, |f x-g x| ≤ ε) :
    |((∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)-
      ((∑' γ : Fin k → ℤ, g (latticeSample n γ))/(n:ℝ)^k)| ≤
      ε * ((Nat.card ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ℝ)/(n:ℝ)^k) := by
  let G := ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
  let : Fintype G := (bounded_grid_finite hn hs).fintype
  rw [lattice_tsum_eq_grid hn s f hf,lattice_tsum_eq_grid hn s g hg,
    ← sub_div,abs_div,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^k)]
  have hsum : |(∑' x : G,f x)-(∑' x : G,g x)| ≤ (Nat.card G : ℝ)*ε := by
    rw [tsum_fintype,tsum_fintype,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x : G, |f x-g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : G, ε := Finset.sum_le_sum (fun x hx => hb x)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ ((Nat.card G : ℝ)*ε)/(n:ℝ)^k := div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

theorem lattice_riemann_perturb {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (g : ℕ → (Fin k → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R)
    (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, Function.support (g n) ⊆ Metric.closedBall 0 R)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, 1 ≤ n → ∀ x, |g n x-f x| ≤ ε n) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have hc := tendsto_card_div_pow_atTop_volume s Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hlim := hε.mul hc
  rw [zero_mul] at hlim
  have hdiff : Tendsto (fun n : ℕ =>
      (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k-
      (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs,Fintype.card_fin] using
      lattice_sum_perturb_bound (by omega : n ≠ 0) Metric.isBounded_closedBall
        (g n) f (hgs n) hfs (ε n) (hbound n hn)
  convert hdiff.add (lattice_riemann hf hfc) using 1
  · ext n; ring
  · simp

end EuclideanRamsey

open scoped BigOperators Pointwise
namespace EuclideanRamsey

lemma rational_convolution_coeff {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν d : AddMonoidAlgebra ℚ G) (δ : G) :
    (ν*d).coeff δ = ∑ γ ∈ ν.coeff.support,ν.coeff γ*d.coeff (δ-γ) := by
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  change (∑ β ∈ d.coeff.support,if γ+β=δ then ν.coeff γ*d.coeff β else 0) = _
  have he (β : G) : γ+β=δ ↔ β=δ-γ := by
    constructor
    · intro h; apply eq_sub_iff_add_eq.mpr; simpa [add_comm] using h
    · intro h; rw [h]; abel
  simp only [he,Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [Finsupp.notMem_support_iff.mp h]

end EuclideanRamsey

open scoped BigOperators Topology
namespace EuclideanRamsey

lemma rational_vector_strict {ι : Type uIndex} [Fintype ι]
    (ζ N : (ι → ℝ) → ℝ) (hζ : Continuous ζ) (hN : Continuous N)
    (η : ℝ) (d : ι → ℝ) (hp : 0 < ζ d) (hn : N d < η*ζ d) :
    ∃ q : ι → ℚ, 0 < ζ (fun i => q i) ∧ N (fun i => q i) < η*ζ (fun i => q i) := by
  have hDense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) := by
    exact DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hopen : IsOpen {d : ι → ℝ | 0 < ζ d ∧ N d < η*ζ d} :=
    (isOpen_lt continuous_const hζ).inter (isOpen_lt hN (continuous_const.mul hζ))
  exact hDense.exists_mem_open hopen ⟨d,hp,hn⟩
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators Pointwise

lemma rationalize_convolution {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν : AddMonoidAlgebra ℚ G) (w : G → ℝ) (t η : ℝ)
    {a : G → ℝ} (ha : Function.HasFiniteSupport a)
    (hp : 0 < (∑' γ,a γ)/t)
    (hn : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*a (δ-γ))) 0*w δ) <
      η*((∑' γ,a γ)/t)) :
    ∃ b : AddMonoidAlgebra ℚ G,
      0 < ((b.coeff.sum fun _ q => q : ℚ):ℝ)/t ∧
      (∑' δ,max (-((ν*b).coeff δ:ℝ)) 0*w δ) <
        η*(((b.coeff.sum fun _ q => q : ℚ):ℝ)/t) := by
  classical
  let E := ha.toFinset
  let : Fintype E := inferInstance
  let K := ν.coeff.support+E
  let ext (d : E → ℝ) (γ : G) := if h : γ ∈ E then d ⟨γ,h⟩ else 0
  let ζ (d : E → ℝ) := (∑ γ : E,d γ)/t
  let N (d : E → ℝ) := ∑ δ ∈ K,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ
  have hζ : Continuous ζ := by unfold ζ; fun_prop
  have hExt (γ : G) : Continuous (fun d : E → ℝ => ext d γ) := by
    dsimp [ext]
    split_ifs <;> fun_prop
  have hN : Continuous N := by unfold N; fun_prop
  have hsum (d : E → ℝ) : ∑' γ,ext d γ = ∑ γ : E,d γ := by
    rw [tsum_eq_sum (s := E)]
    · rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro γ hγ
      simp only [ext,dite_eq_left γ.property]
    · intro γ hγ
      simp [ext,hγ]
  have hNeg (d : E → ℝ) : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ) = N d := by
    apply tsum_eq_sum
    intro δ hδ
    have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ
      have hE : δ-γ ∉ E := by
        intro h
        exact hδ (Finset.mem_add.mpr ⟨γ,hγ,δ-γ,h,by abel⟩)
      simp [ext,hE]
    simp [hz]
  let aE : E → ℝ := fun γ => a γ
  have haE : ext aE = a := by
    funext γ
    dsimp [ext,aE]
    split_ifs with h
    · rfl
    · have hγ : γ ∉ Function.support a := by
        intro hh
        exact h (ha.mem_toFinset.mpr hh)
      exact (not_not.mp hγ).symm
  have hpE : 0 < ζ aE := by
    change 0 < (∑ γ : E,aE γ)/t
    rw [← hsum aE,haE]
    exact hp
  have hnE : N aE < η*ζ aE := by
    rw [← hNeg,haE]
    change _ < η*((∑ γ : E,aE γ)/t)
    rw [← hsum aE,haE]
    exact hn
  obtain ⟨q,hq0,hqN⟩ := rational_vector_strict ζ N hζ hN η aE hpE hnE
  let b : AddMonoidAlgebra ℚ G := ∑ γ : E,AddMonoidAlgebra.single γ.val (q γ)
  have hb (γ : G) : (b.coeff γ : ℝ) = ext (fun i => (q i:ℝ)) γ := by
    simp only [b,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Rat.cast_sum]
    by_cases h : γ ∈ E
    · rw [Finset.sum_eq_single ⟨γ,h⟩]
      · simp [ext,h]
      · intro β hβ hne
        have hne' : β.val ≠ γ := fun he => hne (Subtype.ext he)
        simp [hne']
      · simp
    · have hz (β : E) : β.val ≠ γ := fun hb => h (hb ▸ β.property)
      simp [ext,h,hz]
  have hbMass : ((b.coeff.sum fun _ q => q : ℚ):ℝ) = ∑ γ : E,(q γ:ℝ) := by
    have ht : ∑' γ,(b.coeff γ:ℝ) = ((b.coeff.sum fun _ q => q : ℚ):ℝ) := by
      rw [tsum_eq_sum (s := b.coeff.support)]
      · simp [Finsupp.sum]
      · intro γ hγ; simp [Finsupp.notMem_support_iff.mp hγ]
    rw [← ht]
    simp only [hb]
    exact hsum (fun i => (q i:ℝ))
  refine ⟨b,?_,?_⟩
  · simpa only [hbMass,ζ] using hq0
  · have hc (δ : G) : ((ν*b).coeff δ:ℝ) = ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext (fun i => (q i:ℝ)) (δ-γ) := by
      rw [rational_convolution_coeff]
      simp only [Rat.cast_sum,Rat.cast_mul,hb]
    simp only [hc,hNeg,hbMass]
    exact hqN

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.StencilConvolution ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

namespace EuclideanRamsey
open scoped BigOperators

lemma stencil_taylor_uniform {ι : Type uIndex} {k : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
      |t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x| ≤ K/t := by
  obtain ⟨K,hK,hTaylor⟩ := compact_taylor_bound hb hbc
  refine ⟨∑ γ ∈ S, |q γ| *K*‖v γ‖^3,Finset.sum_nonneg (fun _ _ => by positivity),?_⟩
  intro t ht x
  have hl := linear_moment_contract S q v (fderiv ℝ b x)
  simp only [hfirst,zero_mul,Finset.sum_const_zero] at hl
  have hb' := bilinear_moment_contract S q v (hessianB b x)
  simp only [hsecond,hessianB_eq] at hb'
  let r (γ : ι) := b (x+(-t⁻¹) • v γ)-b x-
    fderiv ℝ b x ((-t⁻¹) • v γ)-
    (1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ]
  have hr (γ : ι) : |r γ| ≤ K*(t⁻¹)^3*‖v γ‖^3 := by
    have hh := hTaylor x ((-t⁻¹) • v γ)
    simpa only [r,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos ht,mul_pow,
      mul_assoc] using hh
  have hrEq : t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x =
      t^2*∑ γ ∈ S,q γ*r γ := by
    have hscale (γ : ι) : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ] =
        (t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ] := by
      simp only [← hessianB_eq,map_smul,_root_.smul_apply,smul_eq_mul]
      ring
    simp only [r,mul_sub,Finset.sum_sub_distrib,map_smul,smul_eq_mul,hscale]
    have hz : ∑ γ ∈ S,q γ*b x = 0 := by rw [← Finset.sum_mul,hzero,zero_mul]
    have h1 : ∑ γ ∈ S,q γ*(-t⁻¹*fderiv ℝ b x (v γ)) = 0 := by
      calc
        _ = -t⁻¹*(∑ γ ∈ S,q γ*fderiv ℝ b x (v γ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro γ hγ; ring
        _ = 0 := by rw [hl,mul_zero]
    have h2 : ∑ γ ∈ S,q γ*((1/2:ℝ)*((t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ])) =
        (t⁻¹)^2*stencilDifferential C b x := by
      unfold stencilDifferential
      rw [← hb']
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      ring
    rw [hz,h1,h2]
    field_simp
    ring
  rw [hrEq,abs_mul,abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *|r γ| := by
      gcongr
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ*r γ) S
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *(K*(t⁻¹)^3*‖v γ‖^3) := by
      gcongr with γ hγ
      exact hr γ
    _ = (∑ γ ∈ S,|q γ| *K*‖v γ‖^3)/t := by
      rw [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro γ hγ
      field_simp

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Topology

lemma stencilDifferential_continuous {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    Continuous (stencilDifferential C b) := by
  have hh := hb.continuous_iteratedFDeriv (m := 2) (by norm_cast)
  unfold stencilDifferential
  fun_prop

lemma stencilDifferential_support {k : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (b : (Fin k → ℝ) → ℝ) : Function.support (stencilDifferential C b) ⊆ tsupport b := by
  intro x hx
  by_contra h
  have hi : x ∉ tsupport (iteratedFDeriv ℝ 2 b) := fun hx => h (tsupport_iteratedFDeriv_subset 2 hx)
  have hz := image_eq_zero_of_notMem_tsupport hi
  exact hx (by simp [stencilDifferential,hz])

lemma stencil_weighted_riemann {ι : Type uIndex} {k d : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ,
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (latticeSample n δ+(-(n:ℝ)⁻¹) • v γ))) 0 *
        gradientWeight U (latticeSample n δ))/(n:ℝ)^k) atTop
      (𝓝 (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x)) := by
  classical
  let f := fun x => max (-stencilDifferential C b x) 0*gradientWeight U x
  let g := fun (n : ℕ) x => max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0*
    gradientWeight U x
  have hc : Continuous f := by
    have hh := stencilDifferential_continuous C hb
    unfold f gradientWeight
    fun_prop
  have hs : Function.support f ⊆ tsupport b := by
    intro x hx
    by_contra h
    have hd : stencilDifferential C b x = 0 := by
      by_contra hh
      exact h (stencilDifferential_support C b hh)
    exact hx (by simp [f,hd])
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hbc hs
  obtain ⟨r,hr,hbr⟩ := hbc.exists_pos_le_norm
  let V := ∑ γ ∈ S,‖v γ‖
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hv (γ : ι) (hγ : γ ∈ S) : ‖v γ‖ ≤ V := Finset.single_le_sum (fun _ _ => norm_nonneg _) hγ
  let R := r+V+1
  have hR : 0 < R := by dsimp [R]; linarith
  have hfr : Function.support f ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hxr : r < ‖x‖ := by dsimp [R] at h; linarith
    have hnb : x ∉ tsupport b := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hxr))] with y hy
      exact hbr y hy.le
    exact hnb (hs hx)
  have hgr (n : ℕ) : Function.support (g n) ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra h
    have hRx : R < ‖x‖ := lt_of_not_ge h
    have hz : g n x = 0 := by
      by_cases hn : n = 0
      · simp [g,hn]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hni : |(n:ℝ)⁻¹| ≤ 1 := by rw [abs_inv,abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hn1
      have hsum : ∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ) = 0 := by
        apply Finset.sum_eq_zero
        intro γ hγ
        have hnorm : r ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖ := by
          have hshift : ‖(-(n:ℝ)⁻¹) • v γ‖ ≤ V := by
            rw [norm_smul,Real.norm_eq_abs,abs_neg]
            exact (mul_le_mul_of_nonneg_right hni (norm_nonneg _)).trans (by simpa using hv γ hγ)
          have hx' : ‖x‖ ≤ ‖x+(-(n:ℝ)⁻¹) • v γ‖+‖(-(n:ℝ)⁻¹) • v γ‖ := by
            simpa only [add_sub_cancel_left] using norm_le_norm_add_norm_sub (x+(-(n:ℝ)⁻¹) • v γ) x
          dsimp [R] at hRx
          linarith
        rw [hbr _ hnorm,mul_zero]
      dsimp only [g]
      rw [hsum]
      simp
    exact hx hz
  obtain ⟨W,hW⟩ := (isCompact_closedBall (0 : Fin k → ℝ) R).exists_bound_of_continuousOn
    (show Continuous (gradientWeight U) by unfold gradientWeight; fun_prop).continuousOn
  obtain ⟨K,hK,hTaylor⟩ := stencil_taylor_uniform S q v C hzero hfirst hsecond hb hbc
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp [hR.le]))
  apply lattice_riemann_perturb f g hc hfc hR hfr hgr (fun n => K*W/(n:ℝ))
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  · intro n hn x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin k → ℝ) R
    · have hw : |gradientWeight U x| ≤ W := by simpa [Real.norm_eq_abs] using hW x hx
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have he := hTaylor n hn0 x
      have hm := abs_max_sub_max_le_abs
        (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) (-stencilDifferential C b x) 0
      have hm' : |max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (x+(-(n:ℝ)⁻¹) • v γ))) 0-
          max (-stencilDifferential C b x) 0| ≤ K/n := by
        apply hm.trans
        simpa only [neg_sub_neg,abs_sub_comm] using he
      dsimp [g,f]
      rw [← sub_mul,abs_mul]
      calc
        _ ≤ (K/n)*W := mul_le_mul hm' hw (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have hf0 : f x = 0 := by by_contra hh; exact hx (hfr hh)
      have hg0 : g n x = 0 := by by_contra hh; exact hx (hgr n hh)
      rw [hf0,hg0,sub_self,abs_zero]
      positivity

end EuclideanRamsey

namespace EuclideanRamsey
open Filter MeasureTheory
open scoped BigOperators Topology

theorem exists_discrete_smoothing {k d : ℕ} (S : Finset (Fin k → ℤ))
    (q : (Fin k → ℤ) → ℝ) (C : Matrix (Fin k) (Fin k) ℝ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*(γ j:ℝ) = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*(γ j:ℝ)*(γ l:ℝ) = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hI : 0 < ∫ x,b x)
    {η : ℝ} (hη : (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x) < η*∫ x,b x) :
    ∃ (n : ℕ) (a : (Fin k → ℤ) → ℝ), 1 ≤ n ∧ Function.HasFiniteSupport a ∧
      0 < (∑' γ,a γ)/(n:ℝ)^2 ∧
      (∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) <
        η*((∑' γ,a γ)/(n:ℝ)^2) := by
  have hZ := lattice_riemann hb.continuous hbc
  have hN := stencil_weighted_riemann S q (fun γ j => (γ j:ℝ)) C U hzero hfirst hsecond hb hbc
  have he := hN.eventually_lt (tendsto_const_nhds.mul hZ) hη
  have hp := (tendsto_const_nhds.eventually_lt hZ hI)
  obtain ⟨n,hn,hp,he⟩ := (eventually_ge_atTop 1 |>.and (hp.and he)).exists
  let a := fun γ : Fin k → ℤ => b (latticeSample n γ)
  have hnf : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : Function.HasFiniteSupport a := latticeSample_finite_support (by omega) hbc
  have hshift (δ γ : Fin k → ℤ) : latticeSample n δ+(-(n:ℝ)⁻¹) • (fun j => (γ j:ℝ)) =
      latticeSample n (δ-γ) := by
    ext j
    simp only [latticeSample,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Int.cast_sub]
    ring
  simp only [hshift] at he
  have hscale (δ : Fin k → ℤ) :
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ) =
      (n:ℝ)^2*(max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*gradientWeight U (latticeSample n δ)) := by
    rw [← mul_neg,← mul_zero ((n:ℝ)^2),← mul_max_of_nonneg _ _ (sq_nonneg (n:ℝ))]
    rw [mul_assoc, mul_zero]
  change (∑' δ,max (-((n:ℝ)^2*∑ γ ∈ S,q γ*a (δ-γ))) 0*
    gradientWeight U (latticeSample n δ))/(n:ℝ)^k < η*((∑' γ,a γ)/(n:ℝ)^k) at he
  simp only [hscale,tsum_mul_left] at he
  have hp' : 0 < ∑' γ,a γ := (div_pos_iff_of_pos_right (pow_pos hnf k)).mp hp
  refine ⟨n,a,hn,ha,div_pos hp' (sq_pos_of_pos hnf),?_⟩
  have hh : (n:ℝ)^2*(∑' δ,max (-(∑ γ ∈ S,q γ*a (δ-γ))) 0*
      gradientWeight U (latticeSample n δ)) < η*(∑' γ,a γ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos hnf k)).mp
    simpa only [mul_div_assoc] using he
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ (sq_pos_of_pos hnf)).mpr
  simpa only [mul_comm] using hh

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators

lemma cosetPushforward_mul {k : ℕ} (Λ : AddSubgroup (Lattice k)) (ν b : LatticeRing k)
    (hν : cosetPushforward Λ ν = 0) : cosetPushforward Λ (ν*b) = 0 := by
  have he : AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) ν = 0 := by
    apply AddMonoidAlgebra.coeff_injective
    exact hν
  change (AddMonoidAlgebra.mapDomain (QuotientAddGroup.mk' Λ) (ν*b)).coeff = 0
  rw [AddMonoidAlgebra.mapDomain_mul,he,zero_mul]
  rfl

theorem rational_smoothing {k d s : ℕ} (hd : 1 ≤ d)
    (Λ : Fin s → AddSubgroup (Lattice k)) (ν : LatticeRing k)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (hC : C.IsSymm) (hU : U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose = (1 : Matrix (Fin d) (Fin d) ℝ))
    (hcos : ∀ i,cosetPushforward (Λ i) ν = 0)
    (hzero : mass ν = 0) (hfirst : ∀ j,firstMoment ν j = 0)
    (hsecond : ∀ j l,secondMoment ν j l = C j l)
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ) (μ : LatticeRing k) (ζ : ℚ), 1 ≤ n ∧ 0 < ζ ∧
      (∀ i,cosetPushforward (Λ i) μ = 0) ∧ mass μ = 0 ∧
      (∀ j,firstMoment μ j = 0) ∧
      (∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l) ∧
      (∑' δ : Lattice k,max (-(μ.coeff δ:ℝ)) 0*gradientWeight U (latticeSample n δ)) < η*ζ := by
  classical
  have hC' : (C.map (Rat.cast : ℚ → ℝ)).IsSymm := by
    ext j l
    change (C l j:ℝ) = (C j l:ℝ)
    exact congrArg Rat.cast (congrFun (congrFun hC j) l)
  obtain ⟨b,hb,hbc,hb0,hbI,hbη⟩ := compact_smoothing k d hd (C.map (Rat.cast : ℚ → ℝ)) U hC' hU η hη
  have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ) = 0 := by
    exact_mod_cast hzero
  have hf (j : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ) = 0 := by
    exact_mod_cast hfirst j
  have hs (j l : Fin k) : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*(γ j:ℝ)*(γ l:ℝ) = (C j l:ℝ) := by
    exact_mod_cast hsecond j l
  obtain ⟨n,a,hn,ha,hap,han⟩ := exists_discrete_smoothing ν.coeff.support
    (fun γ => (ν.coeff γ:ℝ)) (C.map (Rat.cast : ℚ → ℝ)) U hz hf hs hb hbc hbI hbη
  obtain ⟨p,hp0,hpη⟩ := rationalize_convolution ν (fun δ => gradientWeight U (latticeSample n δ))
    ((n:ℝ)^2) η ha hap han
  let ζ : ℚ := mass p/(n:ℚ)^2
  have hζ : (ζ:ℝ) = ((mass p : ℚ):ℝ)/(n:ℝ)^2 := by simp [ζ]
  have hζ0 : 0 < ζ := by
    have hp' : (0:ℝ) < (ζ:ℝ) := by simpa only [hζ,mass] using hp0
    exact_mod_cast hp'
  refine ⟨n,ν*p,ζ,hn,hζ0,fun i => cosetPushforward_mul (Λ i) ν p (hcos i),?_,?_,?_,?_⟩
  · simp [hzero]
  · intro j
    simp [firstMoment_mul,hzero,hfirst]
  · intro j l
    simp only [secondMoment_mul,hzero,hfirst,hsecond,zero_mul,zero_add,add_zero]
    dsimp [ζ]
    ring
  · simpa only [hζ,mass] using hpη

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.AdicLifting ----
namespace OAI

universe uRing uGroup uSemigroup uModule uModuleTarget uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct
namespace EuclideanRamsey

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
open Finset

end NilpotentLog

section LogCharacter
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
  {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)

variable {G : Type uGroup} [AddCommGroup G] (χ : Multiplicative G →* R)
  (hχ : ∀ γ : G, χ (Multiplicative.ofAdd γ) - 1 ∈ I)

end LogCharacter

section LatticeLog
variable {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]

lemma rationalExtension_lattice (f : (Fin k → ℤ) →+ R) (γ : Fin k → ℤ) :
    rationalExtension f (fun j => (γ j : ℚ)) = f γ := by
  dsimp [rationalExtension]
  simp_rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
  rw [← map_sum]
  congr 1
  convert Finset.univ_sum_single γ using 1
  congr 1
  ext j
  rw [← Pi.single_smul]
  simp

end LatticeLog

section AdicLifting
variable {R : Type uRing} {M : Type uModule} {N : Type uModuleTarget} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R N]

lemma adic_kernel_lifting (I : Ideal R) (f : M →ₗ[R] N) (q : ℕ) :
    ∃ n : ℕ, ∀ x : M, f x ∈ I ^ n • (⊤ : Submodule R N) →
      ∃ y : M, f y = 0 ∧ x - y ∈ I ^ q • (⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + q, ?_⟩
  intro x hx
  have hfx : f x ∈ I ^ (k + q) • (⊤ : Submodule R N) ⊓ LinearMap.range f :=
    ⟨hx, ⟨x, rfl⟩⟩
  rw [hk (k + q) (by omega), Nat.add_sub_cancel_left] at hfx
  have hle : I ^ q • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f) ≤
      I ^ q • LinearMap.range f := smul_mono_right _ inf_le_right
  have hf' : f x ∈ I ^ q • LinearMap.range f := hle hfx
  have hm : I ^ q • LinearMap.range f = Submodule.map f (I ^ q • (⊤ : Submodule R M)) := by
    rw [Submodule.map_smul'']
    simp
  rw [hm] at hf'
  obtain ⟨z, hz, he⟩ := hf'
  refine ⟨x - z, ?_, ?_⟩
  · rw [map_sub, he, sub_self]
  · simpa using hz

end AdicLifting

section IntersectionLifting
variable {R : Type uRing} [CommRing R] [IsNoetherianRing R]
  {ι : Type uIndex} [Fintype ι] (I : Ideal R) (J : ι → Ideal R)

lemma adic_intersection_lifting (q : ℕ) :
    ∃ n : ℕ, ∀ x : R, (∀ i, x ∈ J i ⊔ I ^ n) →
      ∃ y : R, (∀ i, y ∈ J i) ∧ x - y ∈ I ^ q := by
  classical
  let f : R →ₗ[R] (∀ i, R ⧸ J i) := LinearMap.pi (fun i => Algebra.linearMap R (R ⧸ J i))
  obtain ⟨n, hn⟩ := adic_kernel_lifting I f q
  refine ⟨n, fun x hx => ?_⟩
  have hm : f x ∈ I ^ n • (⊤ : Submodule R (∀ i, R ⧸ J i)) := by
    have hz : ∀ i, ∃ z ∈ I ^ n, (Ideal.Quotient.mk (J i)) z = (Ideal.Quotient.mk (J i)) x := by
      intro i
      obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hx i)
      refine ⟨z, hz, ?_⟩
      rw [← he, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, zero_add]
    choose z hz he using hz
    have he' : f x = ∑ i, z i • Pi.single i (1 : R ⧸ J i) := by
      simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, he]
      exact (Finset.univ_sum_single _).symm
    rw [he']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top)
  obtain ⟨y, hy, hxy⟩ := hn x hm
  refine ⟨y, ?_, ?_⟩
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrFun hy i
  · simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hxy

end IntersectionLifting

section Construction
variable {k : ℕ}

lemma tensor_quotient_quadratic {S : Type uSemigroup} [CommRing S] [Algebra ℚ S]
    (V : Submodule ℚ (RationalSpace k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (f : RationalSpace k →ₗ[ℚ] S) (hf : V ≤ LinearMap.ker f)
    (hC : TensorProduct.map V.mkQ V.mkQ (matrixTensor C) = 0) :
    (∑ a, ∑ b, C a b • (f (Pi.single a 1) * f (Pi.single b 1))) = 0 := by
  let u := V.liftQ f hf
  let φ := (Algebra.TensorProduct.lmul' ℚ : S ⊗[ℚ] S →ₐ[ℚ] S).toLinearMap.comp
    (TensorProduct.map u u)
  have hh := congrArg φ hC
  simpa [φ, u, matrixTensor, LinearMap.comp_apply] using hh

lemma mem_cosetIdeal_iff (Λ : AddSubgroup (Lattice k)) (x : LatticeRing k) :
    x ∈ cosetIdeal Λ ↔ cosetPushforward Λ x = 0 := by
  change cosetMap Λ x = 0 ↔ _
  rw [← AddMonoidAlgebra.coeff_injective.eq_iff, AddMonoidAlgebra.coeff_zero]
  rfl

lemma monomial_sub_one_mem_cosetIdeal (Λ : AddSubgroup (Lattice k)) {γ : Lattice k}
    (hγ : γ ∈ Λ) : AddMonoidAlgebra.single γ 1 - 1 ∈ cosetIdeal Λ := by
  change cosetMap Λ (AddMonoidAlgebra.single γ 1 - 1) = 0
  rw [map_sub, map_one]
  simp only [cosetMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  have hh : QuotientAddGroup.mk' Λ γ = 0 := (QuotientAddGroup.eq_zero_iff γ).mpr hγ
  rw [hh]
  exact sub_self _

lemma quotient_nil_augmentation (N : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (augmentationIdeal : Ideal (LatticeRing k))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

lemma finite_order_logs (N : ℕ) :
    ∃ f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N),
      (∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal) ∧
      (∀ γ, IsNilpotent.exp (f γ) =
        (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) := by
  let q := Ideal.Quotient.mkₐ ℚ ((augmentationIdeal : Ideal (LatticeRing k)) ^ N)
  let χ : Multiplicative (Lattice k) →* (LatticeRing k ⧸ augmentationIdeal ^ N) :=
    q.toMonoidHom.comp (AddMonoidAlgebra.of ℚ (Lattice k))
  have hχ : ∀ γ : Lattice k, χ (Multiplicative.ofAdd γ) - 1 ∈
      Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal := by
    intro γ
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (monomial_sub_one_mem γ)
    simpa [χ, q, AddMonoidAlgebra.of_apply, map_sub] using h
  refine ⟨characterLogHom (quotient_nil_augmentation N) χ hχ, ?_, ?_⟩
  · intro γ
    exact characterLog_mem (quotient_nil_augmentation N) χ hχ γ
  · intro γ
    simpa [χ, q, AddMonoidAlgebra.of_apply, characterLogHom] using
      characterLog_exp (quotient_nil_augmentation N) χ hχ γ

lemma log_quadratic_mod_coset (N : ℕ) (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1))
    (Λ : AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (hC : quotientTensor Λ (matrixTensor C) = 0)
    (l : Fin k → LatticeRing k)
    (hl : ∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) :
    quadraticStencil C l ∈ cosetIdeal Λ ⊔ augmentationIdeal ^ N := by
  let J := cosetIdeal Λ ⊔ (augmentationIdeal : Ideal (LatticeRing k)) ^ N
  let ψ := Ideal.Quotient.factorₐ ℚ (show augmentationIdeal ^ N ≤ J from le_sup_right)
  let g := ψ.toLinearMap.comp (rationalExtension f)
  have hgγ : ∀ γ ∈ Λ, g (rationalize γ) = 0 := by
    intro γ hγ
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf γ)
    change ψ (rationalExtension f (rationalize γ)) = 0
    rw [show rationalize γ = (fun j => (γ j : ℚ)) from rfl, rationalExtension_lattice]
    apply (nil_exp_eq_one_iff (hn.map ψ)).mp
    rw [← hn.map_exp ψ, hfexp]
    change (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1) = 1
    have hm : AddMonoidAlgebra.single γ (1 : ℚ) - 1 ∈ J :=
      Ideal.mem_sup_left (monomial_sub_one_mem_cosetIdeal Λ hγ)
    have hz : (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1 - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hg : latticeSpan Λ ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    exact hgγ γ hγ
  have hquad := tensor_quotient_quadratic (latticeSpan Λ) C g hg hC
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ ℚ J) (quadraticStencil C l) = 0
  have hlj : ∀ a, (Ideal.Quotient.mkₐ ℚ J) (l a) = g (Pi.single a 1) := by
    intro a
    change ψ ((Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a)) =
      ψ (rationalExtension f (Pi.single a 1))
    rw [hl, rationalExtension_single]
  simp only [quadraticStencil, map_smul, map_sum, map_mul, hlj, hquad, smul_zero]

lemma finite_order_log_lifts (N : ℕ) (hN : 2 ≤ N)
    (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) :
    ∃ l : Fin k → LatticeRing k,
      (∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) ∧
      (∀ a, mass (l a) = 0) ∧
      (∀ a b, firstMoment (l a) b = if a = b then 1 else 0) := by
  classical
  let I : Ideal (LatticeRing k) := augmentationIdeal
  let q := Ideal.Quotient.mk (I ^ N)
  let M := Ideal.map q I
  have hex : ∀ a : Fin k, ∃ x ∈ I, q x = f (Pi.single a 1) := by
    intro a
    exact (Ideal.mem_map_iff_of_surjective q (Ideal.Quotient.mk_surjective)).mp (hf _)
  choose l hlI hl using hex
  refine ⟨l, hl, fun a => (mem_augmentationIdeal _).mp (hlI a), ?_⟩
  have hker : RingHom.ker q = I ^ N := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hpre : Ideal.comap q (Ideal.map q (I ^ 2)) = I ^ 2 := by
    rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right hN)
  intro a b
  let z : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1
  have hdiff : l a - z ∈ I ^ 2 := by
    rw [← hpre]
    change q (l a - z) ∈ Ideal.map q (I ^ 2)
    rw [Ideal.map_pow]
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf (Pi.single a 1))
    have hr : IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1) ∈ M ^ 2 :=
      nil_exp_sub_one_sub_mem hn (hf _)
    have hre : q (l a - z) = -(IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1)) := by
      rw [hfexp, map_sub, hl]
      dsimp [z, q]
      rw [map_sub, map_one]
      ring
    rw [hre]
    exact (M ^ 2).neg_mem hr
  have hj := augmentation_sq_le_jetOne hdiff
  have hjb := hj.2 b
  simp only [firstMoment_sub, sub_eq_zero] at hjb
  rw [hjb]
  simp [z, Pi.single_apply, eq_comm]

theorem finite_lattice_identity : FiniteLatticeIdentity := by
  intro k s hk hs Λ C hCs hC
  let I : Ideal (LatticeRing k) := augmentationIdeal
  obtain ⟨n, hn⟩ := adic_intersection_lifting I (fun i => cosetIdeal (Λ i)) 3
  let N := n + 3
  obtain ⟨f, hf, hfexp⟩ := finite_order_logs (k := k) N
  obtain ⟨l, hl, hm, hfirst⟩ := finite_order_log_lifts N (by omega) f hf hfexp
  have hx : ∀ i, quadraticStencil C l ∈ cosetIdeal (Λ i) ⊔ I ^ n := by
    intro i
    apply (sup_le_sup_left (α := Ideal (LatticeRing k))
      (Ideal.pow_le_pow_right (show n ≤ N by omega)) (cosetIdeal (Λ i)))
    exact log_quadratic_mod_coset N f hf hfexp (Λ i) C (hC i) l hl
  obtain ⟨y, hy, hxy⟩ := hn (quadraticStencil C l) hx
  have he := moments_eq_of_sub_mem_cube hxy
  have hM := quadraticStencil_moments C hCs l hm hfirst
  refine ⟨y, fun i => (mem_cosetIdeal_iff _ _).mp (hy i), ?_, ?_, ?_⟩
  · exact he.1.symm.trans hM.1
  · intro a
    exact (he.2.1 a).symm.trans (hM.2.1 a)
  · intro a b
    exact (he.2.2 a b).symm.trans (hM.2.2 a b)

end Construction

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.TensorPresentation ----
-- TensorProduct.inductionOn (the Lean 4.34 two-case eliminator) is already backported in the imported
-- module OAI.Combinatorics.EuclideanRamsey.TensorDescent.

namespace OAI

universe uVector

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct RealInnerProductSpace
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct BigOperators

lemma arrayEvaluation_affineArray {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray T) = TensorProduct.map (rowEvaluation a i) (rowEvaluation a i) T := by
  induction T using TensorProduct.inductionOn with
  | tmul w z =>
    simp only [arrayEvaluation,LinearMap.coe_mk,AddHom.coe_mk,affineArray_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,TensorProduct.map_tmul,
      rowEvaluation,TensorProduct.sum_tmul,TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  | add x y hx hy => simp [hx,hy]

lemma affineArray_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) (α β : Option (Fin d)) :
    affineArray (TensorProduct.comm ℚ _ _ T) α β = TensorProduct.comm ℚ ℝ ℝ (affineArray T β α) := by
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]

lemma arrayEvaluation_comm {s d : ℕ} (a : Fin s → Space d) (i : Fin s)
    (T : AffineVector d ⊗[ℚ] AffineVector d) :
    arrayEvaluation a i (affineArray (TensorProduct.comm ℚ _ _ T)) =
      TensorProduct.comm ℚ ℝ ℝ (arrayEvaluation a i (affineArray T)) := by
  simp only [arrayEvaluation_affineArray]
  induction T using TensorProduct.inductionOn with
  | tmul w z => simp
  | add x y hx hy => simp [hx,hy]

lemma spatialMultiply_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) :
    spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ T)) =
      (spatialMultiply (affineArray T)).transpose := by
  ext α β
  change Algebra.TensorProduct.lmul' ℚ (affineArray (TensorProduct.comm ℚ _ _ T) (some α) (some β)) =
    Algebra.TensorProduct.lmul' ℚ (affineArray T (some β) (some α))
  rw [affineArray_comm]
  generalize affineArray T (some β) (some α) = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [mul_comm]
  | add x y hx hy => simp [hx,hy]

end EuclideanRamsey

open scoped TensorProduct BigOperators
namespace EuclideanRamsey

theorem exists_symmetric_tensor_presentation {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (T : W ⊗[ℚ] W) :
    ∃ (k : ℕ) (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ), C.IsSymm ∧
      (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
        (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
  classical
  obtain ⟨S,hS⟩ := TensorProduct.exists_finset T
  let w : (↥S ⊕ ↥S) → W := Sum.elim (fun z : ↥S => z.val.1) (fun z : ↥S => z.val.2)
  let C : (↥S ⊕ ↥S) → (↥S ⊕ ↥S) → ℚ := fun j l => match j,l with
    | .inl i,.inr j => if i=j then 1/2 else 0
    | .inr i,.inl j => if i=j then 1/2 else 0
    | _,_ => 0
  have hC : Matrix.IsSymm C := by
    ext j l
    change C l j = C j l
    cases j <;> cases l <;> dsimp only [C]
    all_goals simp only [eq_comm]
  have hs : (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
      (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
    simp only [Fintype.sum_sum_type,C,w,zero_smul,Finset.sum_const_zero,zero_add,add_zero,
      ite_smul,Sum.elim_inl,Sum.elim_inr,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    rw [hS]
    simp only [map_sum,TensorProduct.comm_tmul,smul_add,Finset.smul_sum]
    rw [Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.1 ⊗ₜ[ℚ] z.2)),
      Finset.sum_subtype S (p := fun z => z ∈ S) (F := inferInstance) (fun _ => Iff.rfl) (fun z => (1/2:ℚ) • (z.2 ⊗ₜ[ℚ] z.1))]
  let e := Fintype.equivFin (↥S ⊕ ↥S)
  refine ⟨Fintype.card (↥S ⊕ ↥S), fun j => w (e.symm j), fun j l => C (e.symm j) (e.symm l),?_,?_⟩
  · ext j l
    exact congrFun (congrFun hC (e.symm j)) (e.symm l)
  · change (∑ j,∑ l,C (e.symm j) (e.symm l) • (w (e.symm j) ⊗ₜ[ℚ] w (e.symm l))) = _
    calc
      _ = ∑ j : Fin (Fintype.card (↥S ⊕ ↥S)),∑ l : ↥S ⊕ ↥S,
          C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l) := by
        apply Finset.sum_congr rfl
        intro j _
        exact Equiv.sum_comp e.symm (fun l => C (e.symm j) l • (w (e.symm j) ⊗ₜ[ℚ] w l))
      _ = _ := (Equiv.sum_comp e.symm (fun j => ∑ l,C j l • (w j ⊗ₜ[ℚ] w l))).trans hs

end EuclideanRamsey

open scoped TensorProduct
namespace EuclideanRamsey

end EuclideanRamsey
namespace EuclideanRamsey
open scoped TensorProduct

lemma rational_lattice_kernel {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ) :
    latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) = f.ker := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨γ,hγ,rfl⟩
    exact hγ
  · intro x hx
    let A : Matrix Unit (Fin k) ℚ := fun _ j => x j
    let γ : Lattice k := fun j => A.num () j
    have hden : (A.den:ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    have he : (rationalize γ : RationalSpace k) = (A.den:ℚ) • x := by
      ext j
      have hm := A.num_div_den () j
      change (A.num () j:ℚ)/(A.den:ℚ) = x j at hm
      change (A.num () j:ℚ) = (A.den:ℚ)*x j
      exact ((div_eq_iff hden).mp hm).trans (mul_comm _ _)
    have hγ : γ ∈ AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize) := by
      change f (rationalize γ) = 0
      rw [he,map_smul]
      exact smul_eq_zero_of_right _ hx
    have hm : rationalize γ ∈ latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) :=
      Submodule.subset_span ⟨γ,hγ,rfl⟩
    have := Submodule.smul_mem (latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)))
      (A.den:ℚ)⁻¹ hm
    simpa only [he,smul_smul,inv_mul_cancel₀ hden,one_smul] using this

lemma quotientTensor_zero_of_evaluation {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ)
    (T : RationalSpace k ⊗[ℚ] RationalSpace k) (hT : TensorProduct.map f f T = 0) :
    quotientTensor (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) T = 0 := by
  classical
  change TensorProduct.map _ _ T = 0
  rw [rational_lattice_kernel]
  let e := f.quotKerEquivRange
  let j : (RationalSpace k ⧸ f.ker) →ₗ[ℚ] ℝ := f.range.subtype.comp e.toLinearMap
  have hj : Function.Injective j := f.range.subtype_injective.comp e.injective
  obtain ⟨r,hr⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hpre : j.comp f.ker.mkQ = f := by
    ext x
    rfl
  have htmp : TensorProduct.map j j (TensorProduct.map f.ker.mkQ f.ker.mkQ T) = 0 := by
    rw [← LinearMap.comp_apply,← TensorProduct.map_comp,hpre,hT]
  have hback := congrArg (TensorProduct.map r r) htmp
  simpa only [map_zero,← LinearMap.comp_apply,← TensorProduct.map_comp,← LinearMap.comp_assoc,hr,LinearMap.id_comp,TensorProduct.map_id,
    LinearMap.id_apply] using hback

end EuclideanRamsey

namespace EuclideanRamsey
open scoped TensorProduct BigOperators

lemma matrixTensor_map_family {k : ℕ} {W : Type uVector} [AddCommGroup W] [Module ℚ W]
    (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ) :
    TensorProduct.map (Fintype.linearCombination ℚ w) (Fintype.linearCombination ℚ w) (matrixTensor C) =
      ∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l) := by
  simp [matrixTensor,Fintype.linearCombination_apply,TensorProduct.map_tmul]

lemma spatialMultiply_family {k d : ℕ} (w : Fin k → AffineVector d)
    (C : Matrix (Fin k) (Fin k) ℚ) :
    spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) =
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose := by
  ext α β
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,spatialMultiply,
    LinearMap.coe_mk]
  change (∑ j, ∑ l, (C j l:ℝ)*(w j (some α)*w l (some β))) = _
  change _ = ∑ l, (∑ j, w j (some α) * (C j l : ℝ)) * w l (some β)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realCriterion_lattice {s d : ℕ} (a : Fin s → Space d) (hd : 1 ≤ d)
    (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : Matrix (Fin k) (Fin k) ℚ),
      1 ≤ k ∧ C.IsSymm ∧
      (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)) * (C.map (Rat.cast : ℚ → ℝ)) *
        (show Matrix (Fin d) (Fin k) ℝ from fun α j => w j (some α)).transpose = (1 : Matrix (Fin d) (Fin d) ℝ) ∧
      ∀ i,quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by
  classical
  obtain ⟨P,hP,hG⟩ := h
  let T : AffineVector d ⊗[ℚ] AffineVector d := affineArray.symm P
  have hT : affineArray T = P := affineArray.apply_symm_apply P
  obtain ⟨k,w,C,hC,hrep⟩ := exists_symmetric_tensor_presentation T
  have hs : spatialMultiply (affineArray (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l))) = 1 := by
    rw [hrep,map_smul,map_add,map_smul,map_add,spatialMultiply_comm,hT,hG]
    ext α β
    simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hh : α = β <;> norm_num [hh,eq_comm,Rat.smul_def]
  have hU := (spatialMultiply_family w C).symm.trans hs
  have hk : 1 ≤ k := by
    by_contra hh
    have hk : k = 0 := by omega
    subst k
    have he := congrFun (congrFun hU ⟨0,by omega⟩) ⟨0,by omega⟩
    simp [Matrix.mul_apply] at he
  refine ⟨k,w,C,hk,hC,hU,?_⟩
  intro i
  apply quotientTensor_zero_of_evaluation
  rw [TensorProduct.map_comp,LinearMap.comp_apply,matrixTensor_map_family]
  rw [← arrayEvaluation_affineArray,hrep,map_smul,map_add,map_smul,map_add,
    arrayEvaluation_comm,hT,hP,map_zero,add_zero,smul_zero]

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.SignedRows ----
namespace OAI

universe uAlpha uBeta

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators

open scoped BigOperators
namespace EuclideanRamsey

lemma integerize_finsupp {α : Type uAlpha} (f : α →₀ ℚ) :
    ∃ (M : ℕ) (z : α →₀ ℤ), 0 < M ∧ ∀ a, (z a:ℚ) = M*f a := by
  classical
  let A : Matrix Unit ↥f.support ℚ := fun _ a => f a
  let z := f.mapRange (fun q => Int.floor ((A.den:ℚ)*q)) (by simp)
  refine ⟨A.den,z,Nat.pos_of_ne_zero A.den_ne_zero,?_⟩
  intro a
  by_cases ha : a∈f.support
  · have he := A.num_div_den () ⟨a,ha⟩
    have hd : (A.den:ℚ) ≠ 0 := by exact_mod_cast A.den_ne_zero
    have hn : (A.num () ⟨a,ha⟩:ℚ) = (A.den:ℚ)*f a := by
      exact ((div_eq_iff hd).mp he).trans (mul_comm _ _)
    simp only [z,Finsupp.mapRange_apply,← hn,Int.floor_intCast]
  · simp [z,Finsupp.notMem_support_iff.mp ha]

lemma integerize_finsupp_real {α : Type uAlpha} (f : α →₀ ℚ) :
    ∃ (M : ℕ) (z : α →₀ ℤ), 0 < M ∧ ∀ a, (z a:ℝ) = M*(f a:ℝ) := by
  obtain ⟨M,z,hM,hz⟩ := integerize_finsupp f
  exact ⟨M,z,hM,fun a => by exact_mod_cast hz a⟩

lemma positiveCount_cast {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (positiveCount z a : ℝ) = max (z a:ℝ) 0 := by
  change ((z a).toNat:ℝ) = _
  exact_mod_cast Int.toNat_eq_max (z a)
lemma negativeCount_cast {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (negativeCount z a : ℝ) = max (-(z a:ℝ)) 0 := by
  change ((-(z a)).toNat:ℝ) = _
  exact_mod_cast Int.toNat_eq_max (-(z a))

lemma count_difference {α : Type uAlpha} (z : α →₀ ℤ) (a : α) :
    (positiveCount z a : ℝ)-(negativeCount z a:ℝ) = z a := by
  rw [positiveCount_cast,negativeCount_cast]
  by_cases h : 0 ≤ (z a:ℝ)
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
  · have h := le_of_not_ge h
    rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]
    ring

lemma sum_multiset_elements {α : Type uAlpha} {β : Type uBeta} [DecidableEq α] [AddCommMonoid β]
    (m : Multiset α) (f : α → β) : (∑ x : m, f x) = (m.map f).sum := by
  change ((Finset.univ : Finset m).val.map (fun x : m => f x)).sum = _
  rw [Multiset.map_univ]

lemma sum_count_elements {α : Type uAlpha} [DecidableEq α] (c : α →₀ ℕ) (f : α → ℝ) :
    (∑ x : c.toMultiset, f x) = c.sum (fun a n => (n:ℝ)*f a) := by
  rw [sum_multiset_elements,Finsupp.toMultiset_map,Finsupp.sum_toMultiset,
    Finsupp.sum_mapDomain_index]
  · simp only [nsmul_eq_mul]
  · intro a; simp
  · intro a n m; simp [add_smul]

lemma multiset_map_equiv {α : Type uAlpha} {β : Type uBeta} [DecidableEq α] [DecidableEq β]
    (m n : Multiset α) (f : α → β) (h : m.map f = n.map f) :
    ∃ e : m ≃ n, ∀ x : m, f (e x) = f x := by
  let e := (m.mapEquiv f).trans ((Multiset.cast h).trans (n.mapEquiv f).symm)
  refine ⟨e,?_⟩
  intro x
  have ht := (n.mapEquiv f).apply_symm_apply ((Multiset.cast h) (m.mapEquiv f x))
  have hh := congrArg (fun y : n.map f => (y : β)) ht
  simp only [Multiset.mapEquiv_apply] at hh
  change f (e x) = (m.mapEquiv f x : β) at hh
  exact hh.trans (Multiset.mapEquiv_apply m f x)

lemma count_difference_finsupp {α : Type uAlpha} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) :
    (positiveCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) -
      (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
      (M:ℝ) • f.mapRange (Rat.cast : ℚ → ℝ) (by simp) := by
  ext a
  simp only [Finsupp.sub_apply,Finsupp.mapRange_apply,Finsupp.smul_apply,smul_eq_mul]
  exact (count_difference z a).trans (hz a)

lemma equal_count_pushforward {α : Type uAlpha} {β : Type uBeta} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → β) (hg : f.mapDomain g = 0) :
    (positiveCount z).mapDomain g = (negativeCount z).mapDomain g := by
  apply Finsupp.mapRange_injective (Nat.cast : ℕ → ℝ) (by simp) Nat.cast_injective
  apply sub_eq_zero.mp
  rw [← Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Nat.cast_add x y),
    ← Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Nat.cast_add x y),
    ← Finsupp.mapDomain_sub,count_difference_finsupp f M z hz,
    Finsupp.mapDomain_smul,Finsupp.mapDomain_mapRange g _ _ _ (fun x y => Rat.cast_add x y),hg]
  simp

lemma equal_evaluated_multisets {α : Type uAlpha} {β : Type uBeta} (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → β) (hg : f.mapDomain g = 0) :
    (positiveCount z).toMultiset.map g = (negativeCount z).toMultiset.map g := by
  simp only [Finsupp.toMultiset_map,equal_count_pushforward f M z hz g hg]

lemma sum_counts_difference {α : Type uAlpha} [DecidableEq α]
    (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → ℝ) :
    (∑ x : (positiveCount z).toMultiset,g x) -
      (∑ x : (negativeCount z).toMultiset,g x) =
      M*f.sum (fun a q => (q:ℝ)*g a) := by
  rw [sum_count_elements,sum_count_elements]
  have hs := congrArg (fun c : α →₀ ℝ => c.sum (fun a q => q*g a))
    (count_difference_finsupp f M z hz)
  rw [Finsupp.sum_sub_index (fun a b c => sub_mul b c (g a)),
    Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_smul_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp)] at hs
  rw [hs]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

lemma sum_counts_negative {α : Type uAlpha} [DecidableEq α]
    (f : α →₀ ℚ) (M : ℕ) (z : α →₀ ℤ)
    (hz : ∀ a,(z a:ℝ) = M*(f a:ℝ)) (g : α → ℝ) :
    (∑ x : (negativeCount z).toMultiset,g x) =
      M*f.sum (fun a q => max (-(q:ℝ)) 0*g a) := by
  have he : (negativeCount z).mapRange (Nat.cast : ℕ → ℝ) (by simp) =
      (M:ℝ) • f.mapRange (fun q : ℚ => max (-(q:ℝ)) 0) (by simp) := by
    ext a
    simp only [Finsupp.mapRange_apply,Finsupp.smul_apply,smul_eq_mul,
      negativeCount_cast,hz,← mul_neg, mul_max_of_nonneg _ _ (Nat.cast_nonneg M),mul_zero]
  rw [sum_count_elements]
  have hs := congrArg (fun c : α →₀ ℝ => c.sum (fun a q => q*g a)) he
  rw [Finsupp.sum_mapRange_index (by intro a; simp),
    Finsupp.sum_smul_index (by intro a; simp),
    Finsupp.sum_mapRange_index (by intro a; simp)] at hs
  rw [hs]
  simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]

end EuclideanRamsey

namespace EuclideanRamsey
open Matrix

theorem normalized_signed_rows {α : Type} [DecidableEq α] {d s : ℕ} (hs : 0 < s)
    (a : Fin s → Fin d → ℝ) (v : α → ℝ) (g : α → Fin d → ℝ)
    (f : α →₀ ℚ) (ζ η : ℝ) (hζ : 0 < ζ)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (τ : Type) (_ : Fintype τ) (vp vn : τ → ℝ) (U V : Matrix (Fin d) τ ℝ),
      U*U.transpose-V*V.transpose=1 ∧ (V*V.transpose).trace < η ∧
      ∀ i,∃ σ : Equiv.Perm τ,∀ x,
        vn (σ x)+∑ j,a i j*V j (σ x) = vp x+∑ j,a i j*U j x := by
  classical
  obtain ⟨M,z,hM,hz⟩ := integerize_finsupp_real f
  let m := (positiveCount z).toMultiset
  let n := (negativeCount z).toMultiset
  have hh (i : Fin s) : ∃ e : m ≃ n,∀ x : m,
      v (e x)+∑ j,a i j*g (e x) j = v x+∑ j,a i j*g x j :=
    multiset_map_equiv m n _ (equal_evaluated_multisets f M z hz _ (heval i))
  choose e he using hh
  let e₀ := e ⟨0,hs⟩
  let c := (Real.sqrt ((M:ℝ)*ζ))⁻¹
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hsq : c^2*((M:ℝ)*ζ)=1 := by
    dsimp [c]
    rw [inv_pow,Real.sq_sqrt (by positivity),inv_mul_cancel₀ (by positivity)]
  have hc : 0 ≤ c^2 := sq_nonneg _
  let U : Matrix (Fin d) m ℝ := fun j x => c*g x j
  let V : Matrix (Fin d) m ℝ := fun j x => c*g (e₀ x) j
  have hu (j l : Fin d) : (U*U.transpose) j l = c^2*∑ x : m,g x j*g x l := by
    change (∑ x : m,(c*g x j)*(c*g x l)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hv (j l : Fin d) : (V*V.transpose) j l = c^2*∑ x : n,g x j*g x l := by
    change (∑ x : m,(c*g (e₀ x) j)*(c*g (e₀ x) l)) = _
    rw [← e₀.sum_comp (fun x : n => g x j*g x l),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  refine ⟨m,inferInstance,(fun x => c*v x),(fun x => c*v (e₀ x)),U,V,?_,?_,?_⟩
  · ext j l
    simp only [Matrix.sub_apply,hu,hv,← mul_sub]
    have hm' := sum_counts_difference f M z hz (fun x => g x j*g x l)
    change (∑ x : m,g x j*g x l)-(∑ x : n,g x j*g x l) = _ at hm'
    rw [hm']
    have hm := hmom j l
    simp only [mul_assoc] at hm
    rw [hm]
    calc c^2*((M:ℝ)*(ζ*(if j=l then 1 else 0))) =
        (c^2*((M:ℝ)*ζ))*(if j=l then 1 else 0) := by ring
      _ = _ := by simp [hsq,Matrix.one_apply]
  · have ht : (V*V.transpose).trace = c^2*(M:ℝ)*
        f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) := by
      change (∑ j,(V*V.transpose) j j) = _
      simp only [hv,← Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← pow_two]
      have hn' := sum_counts_negative f M z hz (fun x => ∑ j,(g x j)^2)
      change (∑ x : n,∑ j,(g x j)^2) = _ at hn'
      rw [hn']
      ring
    rw [ht]
    have hc' : 0 < c^2*(M:ℝ) := by
      have hc0 : c ≠ 0 := by dsimp [c]; positivity
      exact mul_pos (sq_pos_of_ne_zero hc0) hMp
    calc c^2*(M:ℝ)*_ < c^2*(M:ℝ)*(η*ζ) := mul_lt_mul_of_pos_left hneg hc'
      _ = (c^2*((M:ℝ)*ζ))*η := by ring
      _ = η := by rw [hsq,one_mul]
  · intro i
    refine ⟨(e i).trans e₀.symm,?_⟩
    intro x
    have he' := congrArg (fun r : ℝ => c*r) (he i x)
    simpa [U,V,Equiv.trans_apply,e₀,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using he'
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.GramCompletion ----
namespace OAI

universe uIndex uRow uColor

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
namespace EuclideanRamsey
lemma trace_gram_complement {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (η : ℝ) (hη : B.trace ≤ η) :
    (η • (1 : Matrix ι ι ℝ)-B).PosSemidef := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) hB.1.eigenvectorUnitary
  have he (i : ι) : hB.1.eigenvalues i ≤ η := by
    apply le_trans _ hη
    rw [hB.1.trace_eq_sum_eigenvalues]
    simpa using (Finset.single_le_sum (fun j _ => hB.eigenvalues_nonneg j) (Finset.mem_univ i))
  have hD : (diagonal (fun i => η-hB.1.eigenvalues i)).PosSemidef :=
    posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (he i))
  have hd : e (diagonal (fun i => η-hB.1.eigenvalues i)) = η • 1-B := by
    have hr : diagonal (fun i => η-hB.1.eigenvalues i) =
        η • (1 : Matrix ι ι ℝ)-diagonal hB.1.eigenvalues := by
      ext i j
      by_cases h : i=j <;> simp [h]
    rw [hr,map_sub,map_smul,map_one]
    congr 1
    exact hB.1.spectral_theorem.symm
  rw [← hd]
  exact hD.mul_mul_conjTranspose_same _

lemma exists_gram_sqrt {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosSemidef) :
    ∃ R : Matrix ι ι ℝ,R*R.transpose=P := by
  let R := CFC.sqrt P
  have hr : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  refine ⟨R,?_⟩
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial,hr.1.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.nonneg

lemma gram_fromCols {ι : Type uIndex} {τ : Type uRow} {κ : Type uColor} [Fintype τ] [Fintype κ]
    (U : Matrix ι τ ℝ) (R : Matrix ι κ ℝ) :
    (U.fromCols R)*(U.fromCols R).transpose = U*U.transpose+R*R.transpose := by
  ext i j
  simp [Matrix.mul_apply,Matrix.fromCols,Matrix.transpose_apply,Fintype.sum_sum_type]

theorem complete_gram_pair {d : ℕ} {τ : Type uRow} [Fintype τ]
    (U V : Matrix (Fin d) τ ℝ) (η : ℝ) (hη : 0 < η)
    (hdiff : U*U.transpose-V*V.transpose=1)
    (htrace : (V*V.transpose).trace < η) :
    ∃ R : Matrix (Fin d) (Fin d) ℝ,
      let c := (Real.sqrt (1+η))⁻¹
      (c • (U.fromCols R))*(c • (U.fromCols R)).transpose=1 ∧
      (c • (V.fromCols R))*(c • (V.fromCols R)).transpose=
        (η/(1+η)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hB : (V*V.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose V
  obtain ⟨R,hR⟩ := exists_gram_sqrt _ (trace_gram_complement _ hB η htrace.le)
  refine ⟨R,?_⟩
  dsimp only
  have he (A : Matrix (Fin d) τ ℝ) :
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R)*
      ((Real.sqrt (1+η))⁻¹ • A.fromCols R).transpose =
      (1/(1+η)) • (A*A.transpose+R*R.transpose) := by
    rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,gram_fromCols]
    congr 1
    rw [← _root_.mul_inv_rev,← sq,Real.sq_sqrt (by linarith)]
    simp
  rw [he,he,hR]
  have hU : U*U.transpose+(η • 1-V*V.transpose)=(1+η) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [add_smul,one_smul,← hdiff]
    abel
  rw [hU,smul_smul,one_div_mul_cancel (by linarith : 1+η ≠ 0),one_smul]
  constructor
  · rfl
  · have hv : V*V.transpose+(η • 1-V*V.transpose)=η • (1 : Matrix (Fin d) (Fin d) ℝ) := by abel
    rw [hv,smul_smul]
    congr 1
    ring
end EuclideanRamsey

namespace EuclideanRamsey
open Matrix
lemma row_gram_distance {d : ℕ} {τ : Type uRow} [Fintype τ]
    (v : τ → ℝ) (U : Matrix (Fin d) τ ℝ) (q : ℝ)
    (hU : U*U.transpose=q • (1 : Matrix (Fin d) (Fin d) ℝ))
    (a b : Fin d → ℝ) :
    (∑ x,((v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x))^2) =
      q*(∑ j,(a j-b j)^2) := by
  have he (x : τ) : (v x+∑ j,a j*U j x)-(v x+∑ j,b j*U j x) =
      (U.transpose *ᵥ (a-b)) x := by
    simp only [Matrix.mulVec,Matrix.transpose_apply,dotProduct,Pi.sub_apply,
      mul_sub,Finset.sum_sub_distrib]
    simp only [mul_comm]
    ring
  simp only [he,pow_two]
  change (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) = _
  have hquad : (U.transpose *ᵥ (a-b)) ⬝ᵥ (U.transpose *ᵥ (a-b)) =
      (a-b) ⬝ᵥ ((U*U.transpose) *ᵥ (a-b)) := by
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec (a-b) U]
    congr 1
    exact (Matrix.vecMul_transpose U.transpose (a-b)).symm
  rw [hquad,hU,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul]
  simp only [smul_eq_mul,dotProduct,Pi.sub_apply]

theorem two_scale_of_signed_rows {α : Type} [DecidableEq α] {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (a : Fin s → EuclideanSpace ℝ (Fin d))
    (v : α → ℝ) (g : α → Fin d → ℝ) (f : α →₀ ℚ)
    (ζ η : ℝ) (hζ : 0 < ζ) (hη : 0 < η)
    (heval : ∀ i,f.mapDomain (fun x => v x+∑ j,a i j*g x j)=0)
    (hmom : ∀ j l,f.sum (fun x q => (q:ℝ)*g x j*g x l)=ζ*(if j=l then 1 else 0))
    (hneg : f.sum (fun x q => max (-(q:ℝ)) 0*(∑ j,(g x j)^2)) < η*ζ) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f' g' : Fin s → EuclideanSpace ℝ (Fin ℓ)),
      (∀ i j,‖f' i-f' j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g' i-g' j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g' i (σ x)=f' i x := by
  classical
  obtain ⟨τ,hτ,vp,vn,U,V,hdiff,htrace,hperm⟩ :=
    normalized_signed_rows hs (fun i j => a i j) v g f ζ η hζ heval hmom hneg
  let := hτ
  obtain ⟨R,hR1,hR2⟩ := complete_gram_pair U V η hη hdiff htrace
  let c := (Real.sqrt (1+η))⁻¹
  let Up := c • U.fromCols R
  let Un := c • V.fromCols R
  let cp : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vp (fun _ => 0) x
  let cn : τ ⊕ Fin d → ℝ := fun x => c*Sum.elim vn (fun _ => 0) x
  let ip (i : Fin s) (x : τ ⊕ Fin d) := cp x+∑ j,a i j*Up j x
  let ineg (i : Fin s) (x : τ ⊕ Fin d) := cn x+∑ j,a i j*Un j x
  have hperm' (i : Fin s) : ∃ σ : Equiv.Perm (τ ⊕ Fin d),∀ x,ineg i (σ x)=ip i x := by
    obtain ⟨σ,hσ⟩ := hperm i
    refine ⟨Equiv.sumCongr σ (Equiv.refl _),?_⟩
    intro x
    cases x with
    | inl x =>
      have h := congrArg (fun r : ℝ => c*r) (hσ x)
      simpa [ineg,ip,cn,cp,Up,Un,Finset.mul_sum,mul_add,mul_assoc,mul_comm,mul_left_comm] using h
    | inr x => simp [ineg,ip,cn,cp,Up,Un]
  let ℓ := Fintype.card (τ ⊕ Fin d)
  let e := Fintype.equivFin (τ ⊕ Fin d)
  let fp (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ip i (e.symm x))
  let fn (i : Fin s) : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun x => ineg i (e.symm x))
  have hd' : Nonempty (τ ⊕ Fin d) := ⟨Sum.inr ⟨0,hd⟩⟩
  refine ⟨ℓ,Fintype.card_pos_iff.mpr hd',fp,fn,?_,?_,?_⟩
  · intro i j
    have h := row_gram_distance cp Up 1 (by simpa only [one_smul] using hR1) (a i) (a j)
    rw [one_mul] at h
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fp,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ip i x-ip j x)^2)]
    exact h
  · intro i j
    have h := row_gram_distance cn Un (η/(1+η)) hR2 (a i) (a j)
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs,fn,WithLp.ofLp_sub,
      Pi.sub_apply]
    rw [e.symm.sum_comp (fun x => (ineg i x-ineg j x)^2)]
    exact h
  · intro i
    obtain ⟨σ,hσ⟩ := hperm' i
    refine ⟨e.symm.trans (σ.trans e),?_⟩
    intro x
    simpa [fp,fn,Equiv.trans_apply] using hσ (e.symm x)
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators
lemma evaluation_coset_pushforward {k : ℕ} (φ : Lattice k →+ ℝ)
    (μ : LatticeRing k) (hμ : cosetPushforward φ.ker μ=0) (n : ℝ) :
    μ.coeff.mapDomain (fun x => φ x/n)=0 := by
  let f := QuotientAddGroup.lift φ.ker φ le_rfl
  have he : (fun x => φ x/n) = (fun y => f y/n) ∘ QuotientAddGroup.mk' φ.ker := by
    funext x
    rfl
  rw [he,Finsupp.mapDomain_comp]
  change Finsupp.mapDomain _ (cosetPushforward φ.ker μ) = 0
  rw [hμ,Finsupp.mapDomain_zero]

lemma lattice_affine_evaluation {k d s : ℕ} (a : Fin s → Space d)
    (w : Fin k → AffineVector d) (i : Fin s) (γ : Lattice k) (n : ℝ) :
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)) (rationalize γ)/n =
      (∑ j,(γ j:ℝ)/n*w j none)+
        ∑ α,a i α*(∑ j,(γ j:ℝ)/n*w j (some α)) := by
  simp only [LinearMap.comp_apply,Fintype.linearCombination_apply,map_sum,map_smul,
    rationalize,AddMonoidHom.coe_mk,Rat.smul_def,rowEvaluation,LinearMap.coe_mk,
    AddHom.coe_mk,Fintype.sum_option,realAugmented,one_mul]
  change (∑ j,(γ j:ℝ)*(w j none+∑ α,a i α*w j (some α)))/n = _
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma scaled_second_moment {k d : ℕ} (μ : LatticeRing k) (n : ℕ)
    (C : Matrix (Fin k) (Fin k) ℚ) (U : Matrix (Fin d) (Fin k) ℝ)
    (ζ : ℚ) (hsecond : ∀ j l,secondMoment μ j l/(n:ℚ)^2 = ζ*C j l)
    (α β : Fin d) :
    μ.coeff.sum (fun γ q => (q:ℝ)*(∑ j,U α j*latticeSample n γ j)*
      (∑ l,U β l*latticeSample n γ l)) =
      (ζ:ℝ)*(U*(C.map (Rat.cast : ℚ → ℝ))*U.transpose) α β := by
  have hm (j l : Fin k) : ∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*latticeSample n γ j*latticeSample n γ l = (ζ:ℝ)*(C j l:ℝ) := by
    have h := congrArg (Rat.cast : ℚ → ℝ) (hsecond j l)
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul,secondMoment,
      Finsupp.sum,Rat.cast_sum,Rat.cast_intCast] at h
    rw [← h,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp only [latticeSample]
    ring
  simp only [Finsupp.sum,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  have hr (j l : Fin k) : (∑ γ ∈ μ.coeff.support,
      (μ.coeff γ:ℝ)*(U α j*latticeSample n γ j)*(U β l*latticeSample n γ l)) =
      U α j*U β l*((ζ:ℝ)*(C j l:ℝ)) := by
    rw [← hm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    ring
  simp only [hr]
  change _ = (ζ:ℝ)*(∑ l,(∑ j,U α j*(C j l:ℝ))*U β l)
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem realCriterion_two_scale {s d : ℕ} (a : Fin s → Space d)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (h : RealCriterion a) (η : ℝ) (hη : 0 < η) :
    ∃ (ℓ : ℕ),1 ≤ ℓ ∧ ∃ (f g : Fin s → Space ℓ),
      (∀ i j,‖f i-f j‖^2=‖a i-a j‖^2) ∧
      (∀ i j,‖g i-g j‖^2=(η/(1+η))*‖a i-a j‖^2) ∧
      ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x := by
  classical
  obtain ⟨k,w,C,hk,hC,hU,hquot⟩ := realCriterion_lattice a hd h
  let U : Matrix (Fin d) (Fin k) ℝ := fun α j => w j (some α)
  let φ (i : Fin s) : Lattice k →+ ℝ :=
    ((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize
  let Λ (i : Fin s) := (φ i).ker
  obtain ⟨ν,hcos,hzero,hfirst,hsecond⟩ :=
    finite_lattice_identity k s hk hs Λ C hC hquot
  obtain ⟨n,μ,ζ,hn,hζ,hcos,_,_,hmom,hneg⟩ :=
    rational_smoothing hd Λ ν C U hC hU hcos hzero hfirst hsecond η hη
  let v (γ : Lattice k) : ℝ := ∑ j,(γ j:ℝ)/(n:ℝ)*w j none
  let g (γ : Lattice k) (α : Fin d) : ℝ := ∑ j,U α j*latticeSample n γ j
  have heval (i : Fin s) : μ.coeff.mapDomain (fun γ => v γ+∑ α,a i α*g γ α)=0 := by
    have he := evaluation_coset_pushforward (φ i) μ (hcos i) (n:ℝ)
    have heq : (fun γ => φ i γ/(n:ℝ)) = (fun γ => v γ+∑ α,a i α*g γ α) := by
      funext γ
      simpa only [φ,v,g,U,latticeSample,mul_comm,AddMonoidHom.comp_apply,LinearMap.toAddMonoidHom_coe] using lattice_affine_evaluation a w i γ (n:ℝ)
    rwa [heq] at he
  have hmoment (α β : Fin d) : μ.coeff.sum (fun γ q => (q:ℝ)*g γ α*g γ β) =
      (ζ:ℝ)*(if α=β then 1 else 0) := by
    have he := scaled_second_moment μ n C U ζ hmom α β
    rw [hU] at he
    exact he
  have hnegative : μ.coeff.sum (fun γ q => max (-(q:ℝ)) 0*(∑ α,(g γ α)^2)) < η*(ζ:ℝ) := by
    rw [tsum_eq_sum (s := μ.coeff.support)] at hneg
    · exact hneg
    · intro γ hγ
      have hz := Finsupp.notMem_support_iff.mp hγ
      simp [hz]
  exact two_scale_of_signed_rows hd hs a v g μ.coeff (ζ:ℝ) η
    (by exact_mod_cast hζ) hη heval hmoment hnegative

end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.FiniteEuclidean ----
-- Lean 4.34 name of Finsupp.mapDomain_apply (same arguments) in Mathlib 0df444a.
namespace OAI

universe uValue

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped BigOperators RealInnerProductSpace
namespace EuclideanRamsey

namespace FiniteEuclidean
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

lemma embed_outside (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (n : ℕ) (hn : d≤n) :
    coords (embed d x) n=0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i,rfl⟩
  exact (not_le_of_gt i.isLt) hn

lemma inner_block_ne (i j : ℕ) (hij : i≠j) (x y : FiniteEuclidean) :
    ⟪block i x,block j y⟫=0 := by
  change product (block i x) (block j y)=0
  unfold product
  change ((coords x).mapDomain (Nat.pair i)).sum
    (fun n r => r*((coords y).mapDomain (Nat.pair j)) n)=0
  rw [Finsupp.sum_mapDomain_index_inj (fun _ _ h => (Nat.pair_eq_pair.mp h).2)]
  apply Finset.sum_eq_zero
  intro n hn
  dsimp only
  rw [Finsupp.mapDomain_of_notMem_range]
  · simp
  · rintro ⟨m,hm⟩
    exact hij (Nat.pair_eq_pair.mp hm).1.symm

lemma norm_sum_blocks {n : ℕ} (x : Fin n → FiniteEuclidean) :
    ‖∑ i : Fin n,block i (x i)‖^2=∑ i,‖x i‖^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sum_inner]
  rw [Finset.sum_eq_single i]
  · exact (block i).inner_map_map _ _ |>.trans (real_inner_self_eq_norm_sq _)
  · intro j _ hji
    exact inner_block_ne j i (fun he => hji (Fin.ext he)) _ _
  · simp

lemma flatten_distance (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖flatten l-flatten k‖^2 = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  have he : flatten l-flatten k = ∑ i : Fin l.length,block i (l.get i-k.get (i.cast h)) := by
    unfold flatten
    have hk : (∑ i : Fin k.length,block i (k.get i))=
        ∑ i : Fin l.length,block i (k.get (i.cast h)) := by
      exact Fintype.sum_equiv (finCongr h).symm _ _ (by intro i; rfl)
    rw [hk,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (map_sub (block i) _ _).symm
  rw [he,norm_sum_blocks]
end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

lemma norm_unit (n : ℕ) : ‖unit n‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_sq]
  simp [unit,coords]
lemma inner_unit (x : FiniteEuclidean) (n : ℕ) : ⟪x,unit n⟫=coords x n := by
  rw [real_inner_comm]
  change product (unit n) x=coords x n
  simp [product,unit,coords]

lemma common_vertex (r : ℝ) (hr : 0 < r) (x y : FiniteEuclidean) (hxy : ‖y-x‖≤2*r) :
    ∃ z : FiniteEuclidean,‖z-x‖=r ∧ ‖z-y‖=r := by
  classical
  let v := y-x
  obtain ⟨n,hn⟩ := (coords v).support.exists_notMem
  have hz : coords v n=0 := Finsupp.notMem_support_iff.mp hn
  let e := unit n
  have he : ‖e‖=1 := norm_unit n
  have hv : ⟪v,e⟫=0 := by simpa [e] using (inner_unit v n).trans hz
  let t := Real.sqrt (r^2-‖v‖^2/4)
  have ht0 : 0≤r^2-‖v‖^2/4 := by
    have hv0 := norm_nonneg v
    change ‖v‖≤2*r at hxy
    nlinarith [sq_nonneg (2*r-‖v‖)]
  have ht : t^2=r^2-‖v‖^2/4 := Real.sq_sqrt ht0
  refine ⟨x+(1/2:ℝ)•v+t•e,?_,?_⟩
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-x=(1/2:ℝ)•v+t•e := by abel
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,sq_abs,mul_pow]
    nlinarith
  · apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
    have heq : x+(1/2:ℝ)•v+t•e-y=(-(1/2):ℝ)•v+t•e := by
      have : y=x+v := by dsimp [v]; abel
      rw [this]
      module
    rw [heq,norm_add_sq_real]
    rw [norm_smul,norm_smul,he,real_inner_smul_left,real_inner_smul_right,hv]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs]
    nlinarith

lemma unit_distance_constant {Y : Type uValue} (r : ℝ) (hr : 0 < r)
    (f : FiniteEuclidean → Y) (hf : ∀ x y,‖x-y‖=r → f x=f y) (x y : FiniteEuclidean) :
    f x=f y := by
  have hsmall (x y : FiniteEuclidean) (h : ‖y-x‖≤2*r) : f x=f y := by
    obtain ⟨z,hz,hz'⟩ := common_vertex r hr x y h
    exact (hf z x hz).symm.trans (hf z y hz')
  have hl : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro x
    refine ⟨Metric.ball x (2*r),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro y hy
    exact (hsmall x y (by exact (show ‖y-x‖<2*r by simpa only [Metric.mem_ball,dist_eq_norm] using hy).le)).symm
  exact hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ y)
end FiniteEuclidean
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathFractions ----
namespace OAI

universe uGroup uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open scoped BigOperators
namespace EuclideanRamsey
section Fractions
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i≠j) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  obtain ⟨c,hc,d,hd,rfl⟩ := ht
  obtain ⟨b,hb,hi,hj⟩ := hM i j hij v hv
  have hcomm : Commute (v*b) (c*d⁻¹) := by
    ext l
    by_cases hli : l=i
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hi]; simp
    by_cases hlj : l=j
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hj]; simp
    · have hh := hs l hli hlj
      change v l*b l*(c l*(d l)⁻¹) = (c l*(d l)⁻¹)*(v l*b l)
      change c l*(d l)⁻¹=1 at hh
      rw [hh]; simp
  refine ⟨u*b*c,M.mul_mem (M.mul_mem hu hb) hc,(v*b)*d,M.mul_mem (M.mul_mem hv hb) hd,?_⟩
  have he : u*v⁻¹ = (u*b)*(v*b)⁻¹ := by group
  rw [he,mul_assoc,hcomm.inv_left.eq]
  group
end Fractions
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

namespace GradedPaths
variable (P : GradedPaths ι G)
lemma bounded_tuple_list (l : List ι) (z : ι → G) (c : ι → ℕ)
    (h : ∀ i∈l,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction ((l.map (fun i => Pi.mulSingle i (z i))).prod) ((l.map c).sum) := by
  induction l with
  | nil => simpa using P.bounded_one
  | cons i l ih =>
    have ht := (P.bounded_mul_single (ih (by intro j hj; exact h j (by simp [hj]))) i (h i (by simp)))
    have he : (l.map (fun j => Pi.mulSingle j (z j))).prod*Pi.mulSingle i (z i)=
        Pi.mulSingle i (z i)*(l.map (fun j => Pi.mulSingle j (z j))).prod := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      by_cases hji : j=i
      · subst j; exact Commute.refl _
      · ext k
        by_cases hki : k=i
        · subst k; simp [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
        · simp [Pi.mulSingle_eq_of_ne hki]
    simpa [he,Nat.add_comm] using ht
end GradedPaths
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.DerivedFractions ----
namespace OAI

universe uGroup uIndex uColor uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped commutatorElement
variable {G : Type uGroup} [Group G]

lemma derived_le (N : Subgroup G) [N.Normal] (n : ℕ) : Derived N n ≤ N := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Subgroup.commutator_le_left _ _).trans ih

lemma restrict_diagonal {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (f : κ → ι)
    (h : HasDiagonal M) : HasDiagonal (M.map (restrictionHom f)) := by
  intro g
  exact ⟨fun _ => g,h g,rfl⟩
lemma restrict_pairInverse {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (f : κ → ι)
    (hf : Function.Injective f) (h : PairInverse M) : PairInverse (M.map (restrictionHom f)) := by
  rintro i j hij v ⟨v,hv,rfl⟩
  obtain ⟨b,hb,hi,hj⟩ := h (f i) (f j) (fun he => hij (hf he)) v hv
  exact ⟨restrictionHom f b,⟨b,hb,rfl⟩,hi,hj⟩
lemma restrict_pairCoverage {ι : Type uIndex} {κ : Type uColor} (M : Submonoid (ι → G)) (N : Subgroup G)
    (f : κ → ι) (hf : Function.Injective f) (h : PairCoverage M N) :
    PairCoverage (M.map (restrictionHom f)) N := by
  intro i j hij a ha b hb
  obtain ⟨z,hz,hi,hj⟩ := h (f i) (f j) (fun he => hij (hf he)) a ha b hb
  exact ⟨restrictionHom f z,⟨z,hz,rfl⟩,hi,hj⟩

lemma lift_restricted_fraction {ι : Type uIndex} {κ : Type uColor} [DecidableEq ι] [DecidableEq κ]
    (M : Submonoid (ι → G)) (f : κ → ι) (z : κ → G)
    (h : RightFraction (M.map (restrictionHom f)) z) :
    ∃ z' : ι → G,RightFraction M z' ∧ ∀ j,z' (f j)=z j := by
  obtain ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,he⟩ := h
  refine ⟨u*v⁻¹,⟨u,hu,v,hv,rfl⟩,?_⟩
  intro j
  exact (congrFun he j).symm

lemma pair_commutator_fraction {ι : Type uIndex} [DecidableEq ι]
    (M : Submonoid (ι → G)) (hM : PairInverse M)
    (i j k : ι) (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (z t : ι → G) (hz : RightFraction M z) (ht : RightFraction M t)
    (hsz : ∀ l,l≠i → l≠j → z l=1) (hst : ∀ l,l≠i → l≠k → t l=1) :
    RightFraction M (Pi.mulSingle i ⁅z i,t i⁆) := by
  have hzi : ∀ l,l≠i → l≠j → z⁻¹ l=1 := by simpa only [Pi.inv_apply,inv_eq_one] using hsz
  have hti : ∀ l,l≠i → l≠k → t⁻¹ l=1 := by simpa only [Pi.inv_apply,inv_eq_one] using hst
  have h := ((hz.mul_pair hM ht i k hik hst).mul_pair hM hz.inv i j hij hzi).mul_pair hM ht.inv i k hik hti
  have he : z*t*z⁻¹*t⁻¹=Pi.mulSingle i ⁅z i,t i⁆ := by
    ext l
    by_cases hli : l=i
    · subst l; simp [commutatorElement_def]
    · by_cases hlj : l=j
      · subst l
        have hh := hst j hli hjk
        simp [hh,Pi.mulSingle_eq_of_ne hli]
      · have hh := hsz l hli hlj
        simp [hh,Pi.mulSingle_eq_of_ne hli]
  rwa [he] at h

lemma fraction_card_le_two {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    (M : Submonoid (ι → G)) (N : Subgroup G) (hd : HasDiagonal M)
    (hc : PairCoverage M N) (hcard : Fintype.card ι ≤ 2) (i : ι) :
    N ≤ singleFractions M hd i := by
  intro a ha
  change RightFraction M (Pi.mulSingle i a)
  by_cases h : ∃ j : ι,j≠i
  · obtain ⟨j,hji⟩ := h
    obtain ⟨z,hz,hzi,hzj⟩ := hc i j (Ne.symm hji) a ha 1 N.one_mem
    have he : z=Pi.mulSingle i a := by
      ext l
      by_cases hli : l=i
      · subst l; simpa using hzi
      · have hlj : l=j := by
          by_contra hlj
          have hh : 3 ≤ Fintype.card ι := by
            have hs : ({i,j,l} : Finset ι).card ≤ Fintype.card ι := Finset.card_le_univ _
            simpa [hji,Ne.symm hji,hli,Ne.symm hli,hlj,Ne.symm hlj] using hs
          omega
        subst l
        simpa [Pi.mulSingle_eq_of_ne hli] using hzj
    exact ⟨z,hz,1,M.one_mem,by simpa using he.symm⟩
  · have he : (fun _ : ι => a)=Pi.mulSingle i a := by
      ext l
      have hl : l=i := by by_contra hh; exact h ⟨l,hh⟩
      simp [hl]
    exact ⟨_,hd a,1,M.one_mem,by simpa using he.symm⟩

theorem derived_subset_single (N : Subgroup G) [N.Normal] (n : ℕ) :
    ∀ (ι : Type uIndex) [Fintype ι] [DecidableEq ι] (M : Submonoid (ι → G))
      (hd : HasDiagonal M) (_hi : PairInverse M) (_hc : PairCoverage M N),
      Fintype.card ι ≤ n+2 → ∀ i,Derived N n ≤ singleFractions M hd i := by
  induction n with
  | zero =>
    intro ι _ _ M hd hi hc hcard i
    exact fraction_card_le_two M N hd hc hcard i
  | succ n ih =>
    intro ι _ _ M hd hi hc hcard i
    by_cases hsmall : Fintype.card ι ≤ 2
    · exact (derived_le N _).trans (fraction_card_le_two M N hd hc hsmall i)
    obtain ⟨j,hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
    have hek : ∃ k : ι,k≠i ∧ k≠j := by
      by_contra hh
      have he : (Finset.univ : Finset ι) ⊆ {i,j} := by
        intro k _
        by_cases hki : k=i
        · simp [hki]
        · have hkj : k=j := by by_contra hkj; exact hh ⟨k,hki,hkj⟩
          simp [hkj]
      have hh := Finset.card_le_card he
      have hh' : Fintype.card ι ≤ 2 := hh.trans (Finset.card_insert_le _ _ |>.trans (by simp))
      exact hsmall hh'
    obtain ⟨k,hki,hkj⟩ := hek
    change ⁅Derived N n,Derived N n⁆ ≤ _
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have lift (j : ι) (hji : j≠i) (a : G) (ha : a∈Derived N n) :
        ∃ z : ι → G,RightFraction M z ∧ z i=a ∧ ∀ l,l≠i → l≠j → z l=1 := by
      let κ := {l : ι // l≠j}
      let f : κ → ι := Subtype.val
      let M' := M.map (restrictionHom f)
      let i' : κ := ⟨i,Ne.symm hji⟩
      have hf : Function.Injective f := Subtype.val_injective
      have hκ : Fintype.card κ ≤ n+2 := by
        have hh := Fintype.card_subtype_lt (p:=fun l : ι => l≠j) (x:=j) (by simp)
        change Fintype.card κ < Fintype.card ι at hh
        omega
      have he := ih κ M' (restrict_diagonal M f hd) (restrict_pairInverse M f hf hi)
        (restrict_pairCoverage M N f hf hc) hκ i' ha
      obtain ⟨z,hz,he⟩ := lift_restricted_fraction M f (Pi.mulSingle i' a) he
      refine ⟨z,hz,?_,?_⟩
      · simpa [i',f] using he i'
      · intro l hli hlj
        have hh := he ⟨l,hlj⟩
        have hn : (⟨l,hlj⟩ : κ) ≠ i' := by intro he; exact hli (Subtype.mk.inj he)
        simpa [f,Pi.mulSingle_eq_of_ne hn] using hh
    obtain ⟨z,hz,hzi,hsz⟩ := lift j hji a ha
    obtain ⟨t,ht,hti,hst⟩ := lift k hki b hb
    have hh := pair_commutator_fraction M hi i j k (Ne.symm hji) (Ne.symm hki)
      (Ne.symm hkj) z t hz ht hsz hst
    change RightFraction M (Pi.mulSingle i ⁅a,b⁆)
    simpa only [hzi,hti] using hh
end EuclideanRamsey

namespace EuclideanRamsey
variable {X : Type uPoint} {G : Type uGroup} [Group G]
lemma letter_difference_mem (x y : X) : FreeGroup.of x*(FreeGroup.of y)⁻¹∈AugKernel X := by
  change freeAugmentation X _=1
  simp [freeAugmentation]

lemma augmentation_kernel_le (x₀ : X) (Q : Subgroup (FreeGroup X)) [Q.Normal]
    (h : ∀ x y,(QuotientGroup.mk' Q) (FreeGroup.of x)=(QuotientGroup.mk' Q) (FreeGroup.of y)) :
    AugKernel X≤Q := by
  let q := QuotientGroup.mk' Q
  let t := q (FreeGroup.of x₀)
  let cy : Multiplicative ℤ →* (FreeGroup X ⧸ Q) :=
    { toFun := fun n => t^(Multiplicative.toAdd n)
      map_one' := by simp
      map_mul' := by intro a b; exact zpow_add t _ _ }
  have he : q=cy.comp (freeAugmentation X) := by
    apply FreeGroup.ext_hom
    intro x
    simpa [cy,freeAugmentation,t,q] using h x x₀
  intro g hg
  apply (QuotientGroup.eq_one_iff _).mp
  change q g=1
  rw [he,MonoidHom.comp_apply]
  change freeAugmentation X g=1 at hg
  rw [hg,map_one]
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathWords ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex}

lemma UnitWords.path {a : ι → FiniteEuclidean} {w n} (h : UnitWords a w n) : Path a w n := by
  induction h with
  | diag g => simpa only [Nat.cast_zero] using (Path.diag (a:=a) g)
  | copy b hb =>
    simpa only [Nat.cast_one] using (Path.copy (a:=a) (u:=1) b ⟨zero_le_one,by intro i j; simp [hb i j]⟩)
  | mul _ _ ihu ihv => simpa only [Nat.cast_add] using ihu.mul ihv
lemma pairLeft_edge (a : ι → FiniteEuclidean) (i j : ι) (hij : i≠j)
    (x y : FiniteEuclidean) (hxy : ‖x-y‖=‖a i-a j‖) :
    FreeGroup.of x*(FreeGroup.of y)⁻¹∈pairLeft a i j hij := by
  obtain ⟨b,hbi,hbj,hb⟩ := extend_pair_E a i j x y (by
    simpa only [norm_sub_rev y x,norm_sub_rev (a j) (a i)] using hxy)
  have hcopy : (FreeGroup.of x,FreeGroup.of y)∈pairGroup a i j hij := by
    refine ⟨(fun k => FreeGroup.of (b k)),⟨1,UnitWords.copy b hb⟩,?_⟩
    exact Prod.ext (congrArg FreeGroup.of hbi) (congrArg FreeGroup.of hbj)
  have h := (pairGroup a i j hij).mul_mem hcopy (pairGroup_diag a i j hij (FreeGroup.of y)⁻¹)
  simpa [pairLeft,MonoidHom.inl_apply] using h

lemma unit_pair_coverage (a : ι → FiniteEuclidean) (ha : Function.Injective a) :
    PairCoverage (unitGraded a).monoid (AugKernel FiniteEuclidean) := by
  intro i j hij g hg h hh
  have hr : 0<‖a i-a j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he => hij (ha he)))
  have hle : AugKernel FiniteEuclidean≤pairLeft a i j hij := by
    apply augmentation_kernel_le 0
    intro x y
    apply FiniteEuclidean.unit_distance_constant _ hr
      (fun z => (QuotientGroup.mk' (pairLeft a i j hij)) (FreeGroup.of z))
    intro x y hxy
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using pairLeft_edge a i j hij x y hxy
  have hleft : (g,1)∈pairGroup a i j hij := hle hg
  have hright : (1,h)∈pairGroup a i j hij := by
    have h := (pairGroup a i j hij).mul_mem (pairGroup_diag a i j hij h)
      (hle ((AugKernel FiniteEuclidean).inv_mem hh))
    simpa using h
  have hp := (pairGroup a i j hij).mul_mem hleft hright
  have hp' : (g,h)∈(unitGraded a).monoid.map (pairHom i j) := by
    change (g,h)∈pairGroup a i j hij
    simpa using hp
  obtain ⟨v,hv,hv'⟩ := hp'
  exact ⟨v,hv,congrArg Prod.fst hv',congrArg Prod.snd hv'⟩
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
lemma stringEnergy_append (l k l' k' : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy (l++l') (k++k')=stringEnergy l k+stringEnergy l' k' := by
  induction l generalizing k with
  | nil => have hk : k=[] := List.length_eq_zero_iff.mp h.symm; subst k; simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simp only [List.cons_append,stringEnergy,ih k h,add_assoc]

lemma stringEnergy_eq_sum (l k : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy l k = ∑ i : Fin l.length,‖l.get i-k.get (i.cast h)‖^2 := by
  induction l generalizing k with
  | nil => simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      have h' : l.length=k.length := Nat.add_right_cancel h
      change _ = ∑ i : Fin (l.length+1), ‖(x::l).get i-(y::k).get (i.cast h)‖^2
      rw [Fin.sum_univ_succ]
      simpa only [stringEnergy,List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,
        Fin.val_zero,Fin.val_succ,Fin.val_cast] using congrArg (fun t => ‖x-y‖^2+t) (ih k h')

lemma flatten_energy (l k : List FiniteEuclidean) (h : l.length=k.length) :
    ‖FiniteEuclidean.flatten l-FiniteEuclidean.flatten k‖^2=stringEnergy l k := by
  rw [FiniteEuclidean.flatten_distance l k h,stringEnergy_eq_sum l k h]

variable {ι : Type uIndex}
lemma StringFamily.common (a : ι → FiniteEuclidean) (x : Strings) :
    StringFamily a 0 (fun _ => x) := by constructor <;> intros <;> simp [stringEnergy_self]
lemma StringFamily.single {a : ι → FiniteEuclidean} {u : ℝ} {b : ι → FiniteEuclidean}
    (h : CopyPath a u b) : StringFamily a u (fun i => FreeMonoid.of (b i)) := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro i j
  change ‖b i-b j‖^2+0=u*‖a i-a j‖^2
  simpa only [add_zero] using h.2 i j
lemma StringFamily.mul {a : ι → FiniteEuclidean} {u v : ℝ} {x y : ι → Strings}
    (hx : StringFamily a u x) (hy : StringFamily a v y) : StringFamily a (u+v) (x*y) := by
  refine ⟨?_,?_⟩
  · intro i j
    change ((x i).toList++(y i).toList).length=((x j).toList++(y j).toList).length
    simp only [List.length_append,hx.1 i j,hy.1 i j]
  · intro i j
    change stringEnergy ((x i).toList++(y i).toList) ((x j).toList++(y j).toList)=_
    rw [stringEnergy_append _ _ _ _ (hx.1 i j),hx.2,hy.2,add_mul]
lemma StringFamily.congruent {a : ι → FiniteEuclidean} {x : ι → Strings}
    (h : StringFamily a 1 x) :
    ∀ i j,‖FiniteEuclidean.flatten (x i).toList-FiniteEuclidean.flatten (x j).toList‖=‖a i-a j‖ := by
  intro i j
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [flatten_energy _ _ (h.1 i j),h.2,one_mul]
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings ----
namespace OAI

universe uModule uIndex uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open Filter
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
end Ultrafilters

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
lemma choose [Finite ι] (q : UltraColumn ι M) (p : ι → M → Prop)
    (h : ∀ i,∀ᶠ x in (q.value i : Filter M),p i x) :
    ∃ x : ι → M,q.Realizes x ∧ ∀ i,p i (x i) := by
  cases q with
  | common U =>
    have hh : ∀ᶠ x in (U : Filter M),∀ i,p i x := Filter.eventually_all.mpr h
    obtain ⟨x,hx⟩ := hh.exists
    exact ⟨fun _ => x,⟨x,fun _ => rfl⟩,hx⟩
  | principal x =>
    refine ⟨x,rfl,?_⟩
    intro i
    simpa [value] using h i

theorem simultaneously_realize [Finite ι] [Monoid M] (qs : List (UltraColumn ι M))
    (B : ι → Set M)
    (h : letI := ultrafilterMonoid (M:=M)
      ∀ i,B i ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M)) :
    ∃ xs : List (ι → M), List.Forall₂ Realizes qs xs ∧
      ∀ i, (xs.map (fun x => x i)).prod ∈ B i := by
  let := ultrafilterMonoid (M:=M)
  induction qs generalizing B with
  | nil =>
    refine ⟨[],.nil,?_⟩
    intro i
    have hi := h i
    change B i ∈ (pure (1:M) : Ultrafilter M) at hi
    simpa using hi
  | cons q qs ih =>
    have hh (i : ι) : ∀ᶠ x in (q.value i : Filter M),
        {y | x*y∈B i} ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M) := by
      have hi := h i
      change ∀ᶠ z in ((q.value i)*(qs.map (fun q => q.value i)).prod : Ultrafilter M), z∈B i at hi
      exact (Ultrafilter.eventually_mul _ _ _).mp hi
    obtain ⟨x,hx,hxB⟩ := q.choose _ hh
    obtain ⟨xs,hxs,hB⟩ := ih (fun i => {y | x i*y∈B i}) hxB
    refine ⟨x::xs,.cons hx hxs,?_⟩
    intro i
    simpa using hB i
end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

lemma ColumnPath.realizes {a : ι → FiniteEuclidean} {qs u} (h : ColumnPath a qs u)
    (xs : List (ι → Strings)) (hx : List.Forall₂ UltraColumn.Realizes qs xs) :
    StringFamily a u (fun i => (xs.map (fun x => x i)).prod) := by
  induction h generalizing xs with
  | nil =>
    cases hx
    simpa using StringFamily.common a 1
  | common U =>
    cases hx with
    | cons hx hn =>
      cases hn
      obtain ⟨x,hx⟩ := hx
      simpa [hx] using StringFamily.common a x
  | copy b hb =>
    cases hx with
    | cons hx hn =>
      cases hn
      change _ = _ at hx
      subst hx
      simpa using StringFamily.single hb
  | @append p q u v _ _ ihp ihq =>
    have hp : List.Forall₂ UltraColumn.Realizes p (xs.take p.length) := by
      have hh := List.forall₂_take p.length hx
      simpa only [List.take_left] using hh
    have hq : List.Forall₂ UltraColumn.Realizes q (xs.drop p.length) := by
      have hh := List.forall₂_drop p.length hx
      simpa only [List.drop_left] using hh
    have hmul := (ihp (xs.take p.length) hp).mul (ihq (xs.drop p.length) hq)
    have he : (fun i => ((xs.take p.length).map (fun x => x i)).prod) *
        (fun i => ((xs.drop p.length).map (fun x => x i)).prod) =
        (fun i => (xs.map (fun x => x i)).prod) := by
      funext i
      simp only [Pi.mul_apply,← List.prod_append,← List.map_append,List.take_append_drop]
    rwa [he] at hmul

lemma Path.expand {a : ι → FiniteEuclidean} {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p) :
    ∃ qs : List (UltraColumn ι Strings),ColumnPath a qs u ∧
      (letI := ultrafilterMonoid (M:=Strings); ∀ i,(qs.map (fun q => q.value i)).prod=Ψ (w i)) := by
  let := ultrafilterMonoid (M:=Strings)
  induction h with
  | diag g => exact ⟨[.common (Ψ g)],.common _,by intro i; simp [UltraColumn.value]⟩
  | @copy u b hb =>
    refine ⟨[.common p,.principal (fun i => FreeMonoid.of (b i)),.common p],?_,?_⟩
    · simpa using (ColumnPath.common p).append ((ColumnPath.copy b hb).append (.common p))
    · intro i
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,UltraColumn.value,mul_one,hgen,mul_assoc]
  | @mul w v u t hu hv ihu ihv =>
    obtain ⟨qs,hqs,hqe⟩ := ihu
    obtain ⟨rs,hrs,hre⟩ := ihv
    refine ⟨qs++rs,hqs.append hrs,?_⟩
    intro i
    simp only [List.map_append,List.prod_append,hqe,hre,Pi.mul_apply]
    exact (Ψ.map_mul _ _).symm

lemma ColumnPath.flatten {α : Type uAlpha} {a : ι → FiniteEuclidean} (l : List α)
    (qs : α → List (UltraColumn ι Strings)) (u : α → ℝ)
    (h : ∀ j∈l,ColumnPath a (qs j) (u j)) :
    ColumnPath a ((l.map qs).flatten) ((l.map u).sum) := by
  induction l with
  | nil => simpa using (ColumnPath.nil (a:=a))
  | cons j l ih =>
    simpa only [List.map_cons,List.flatten_cons,List.sum_cons] using
      (h j (by simp)).append (ih (fun k hk => h k (by simp [hk])))

lemma flattened_ultra_product {α : Type uAlpha} (l : List α) (qs : α → List (UltraColumn ι Strings))
    (U : α → ι → Ultrafilter Strings)
    (h : letI := ultrafilterMonoid (M:=Strings); ∀ j∈l,∀ i,((qs j).map (fun q => q.value i)).prod=U j i) :
    letI := ultrafilterMonoid (M:=Strings)
    ∀ i,(((l.map qs).flatten).map (fun q => q.value i)).prod=(l.map (fun j => U j i)).prod := by
  let := ultrafilterMonoid (M:=Strings)
  intro i
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,List.prod_append,List.prod_cons]
    rw [h j (by simp) i,ih (fun k hk => h k (by simp [hk]))]
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathSynchronization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {a : ι → FiniteEuclidean}

lemma Path.scale {w lmb} (h : Path a w lmb) (c : ℝ) (hc : 0 ≤ c) :
    Path a (fun i => scaleGroup c (w i)) (c*lmb) := by
  induction h with
  | diag g => simpa using (Path.diag (a:=a) (scaleGroup c g))
  | @copy u b hb =>
    have hcopy : CopyPath a (c*u) (fun i => Real.sqrt c • b i) := by
      refine ⟨mul_nonneg hc hb.1,?_⟩
      intro i j
      rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hc,hb.2]
      ring
    simpa only [scaleGroup,FreeGroup.map.of] using Path.copy _ hcopy
  | mul _ _ ihu ihv => simpa only [map_mul,Pi.mul_apply,Pi.mul_def,mul_add] using ihu.mul ihv

lemma Path.list_prod {α : Type uAlpha} (l : List α) (w : α → ι → LetterGroup) (u : α → ℝ)
    (h : ∀ j∈l,Path a (w j) (u j)) :
    Path a ((l.map w).prod) ((l.map u).sum) := by
  induction l with
  | nil => simpa only [List.map_nil,List.prod_nil,List.sum_nil,Pi.one_def] using (Path.diag (a:=a) 1)
  | cons j l ih =>
    simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
      (h j (by simp)).mul (ih (fun k hk => h k (by simp [hk])))

lemma synchronized_chain {w : ι → LetterGroup} {ρ : ℝ} (hp : Path a w 1)
    (hm : Path a w ρ) (hρ : ρ < 1) (v : ℕ → ℝ) (n : ℕ)
    (hv0 : v 0=1) (hvn : v n=ρ) (hv : ∀ j,j<n → v (j+1)≤v j) :
    ∃ W,∀ k,k≤n → Path a W (v k) := by
  let c (j : ℕ) := (v j-v (j+1))/(1-ρ)
  have hc : ∀ j,j<n → 0 ≤ c j := fun j hj => div_nonneg (sub_nonneg.mpr (hv j hj)) (by linarith)
  let ww (j : ℕ) : ι → LetterGroup := fun i => scaleGroup (c j) (w i)
  refine ⟨((List.range n).map ww).prod,?_⟩
  intro k hk
  let u (j : ℕ) := if j<k then c j*ρ else c j
  have hpaths : ∀ j∈List.range n,Path a (ww j) (u j) := by
    intro j hj
    have hj' : j<n := List.mem_range.mp hj
    dsimp [u]
    split_ifs
    · exact hm.scale (c j) (hc j hj')
    · simpa using hp.scale (c j) (hc j hj')
  have hs : ∑ j∈Finset.range n,u j=v k := by
    rw [← Finset.sum_range_add_sum_Ico u hk]
    have hleft : ∑ j∈Finset.range k,u j=ρ*((v 0-v k)/(1-ρ)) := by
      calc
        _ = (∑ j∈Finset.range k,(v j-v (j+1)))/(1-ρ)*ρ := by
          simp only [u,c,Finset.sum_div,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [ite_eq_left (Finset.mem_range.mp hj)]
        _ = _ := by rw [Finset.sum_range_sub']; ring
    have hright : ∑ j∈Finset.Ico k n,u j=(v k-v n)/(1-ρ) := by
      calc
        _ = (∑ j∈Finset.Ico k n,(v j-v (j+1)))/(1-ρ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [u,c,ite_eq_right (not_lt_of_ge (Finset.mem_Ico.mp hj).1)]
        _ = _ := by
          congr 1
          rw [Finset.sum_Ico_eq_sub _ hk,Finset.sum_range_sub',Finset.sum_range_sub']
          ring
    rw [hleft,hright,hv0,hvn]
    field_simp [ne_of_gt (show 0 < 1-ρ by linarith)]
    ring
  have hp' := Path.list_prod (List.range n) ww u hpaths
  have he' : ((List.range n).map u).sum=∑ j∈Finset.range n,u j := by
    have hr : (List.range n).toFinset=Finset.range n := by ext j; simp
    simpa only [hr] using (List.sum_toFinset u (List.nodup_range (n:=n))).symm
  rwa [he',hs] at hp'

theorem synchronize_paths (n : ℕ) (hn : 1 ≤ n) {w : ι → LetterGroup} {lmb μ : ℝ}
    (hp : Path a w lmb) (hm : Path a w μ) (hlmb : 0 < lmb)
    (hratio : μ/lmb < 1/(n:ℝ)) :
    ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path a W (1/(t:ℝ)) := by
  let ρ := μ/lmb
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
  have hρ : ρ<1 := lt_of_lt_of_le hratio (by exact (div_le_one hn').mpr (by exact_mod_cast hn))
  have hnorm : Path a (fun i => scaleGroup lmb⁻¹ (w i)) 1 := by
    simpa [inv_mul_cancel₀ hlmb.ne'] using hp.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  have hnorm' : Path a (fun i => scaleGroup lmb⁻¹ (w i)) ρ := by
    simpa [ρ,div_eq_mul_inv,mul_comm] using hm.scale lmb⁻¹ (inv_nonneg.mpr hlmb.le)
  let v (j : ℕ) : ℝ := if j<n then 1/(j+1:ℕ) else ρ
  obtain ⟨W,hW⟩ := synchronized_chain hnorm hnorm' hρ v n (by simp [v]; omega)
    (by simp [v]) (by
      intro j hj
      dsimp [v]
      rw [ite_eq_left hj]
      split_ifs with hj'
      · apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (by omega : j+1≤j+1+1)
      · have he : j+1=n := by omega
        simpa [he,ρ] using hratio.le)
  refine ⟨W,?_⟩
  intro t ht htn
  have ht0 : t-1<n := by omega
  have h := hW (t-1) (by omega)
  simpa only [v,ite_eq_left ht0,show t-1+1=t by omega] using h
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.CornerGroup ----
namespace OAI

universe uSemigroup

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter

open Set
namespace EuclideanRamsey

theorem exists_group_corner {S : Type uSemigroup} [Nonempty S] [Semigroup S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) :
    ∃ p : S, p*p=p ∧ ∀ y : S, p*y=y → y*p=y →
      ∃ v : S, p*v=v ∧ v*p=v ∧ v*y=p := by
  let ideals : Set (Set S) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y∈N → x*y∈N}
  have hmin : ∃ N, Minimal (· ∈ ideals) N := by
    refine zorn_superset _ fun c hcs hchain => ?_
    refine ⟨⋂₀ c, ⟨isClosed_sInter (fun N hN => (hcs hN).1), ?_, ?_⟩,
      fun N hN => Set.sInter_subset_of_mem hN⟩
    · obtain rfl | hcn := c.eq_empty_or_nonempty
      · simp
      convert! @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        _ _ _ hcn.coe_sort ((↑) : c → Set S) ?_ ?_ ?_ ?_
      · exact Set.sInter_eq_iInter
      · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
      · exact fun N => (hcs N.prop).2.1
      · exact fun N => (hcs N.prop).1.isCompact
      · exact fun N => (hcs N.prop).1
    · intro x y hy
      exact Set.mem_sInter.mpr fun N hN => (hcs hN).2.2 x y (Set.mem_sInter.mp hy N hN)
  obtain ⟨N,hN⟩ := hmin
  have hprincipal (y : S) (hy : y∈N) : Set.range (·*y) = N := by
    apply hN.eq_of_subset
    · refine ⟨isCompact_range (hc y) |>.isClosed, ⟨y*y,y,rfl⟩, ?_⟩
      rintro a _ ⟨b,rfl⟩
      exact ⟨a*b,mul_assoc a b y⟩
    · rintro _ ⟨a,rfl⟩
      exact hN.prop.2.2 a y hy
  obtain ⟨p,hpN,hp⟩ := exists_idempotent_in_compact_subsemigroup hc N
    hN.prop.2.1 hN.prop.1.isCompact (fun x _ y hy => hN.prop.2.2 x y hy)
  refine ⟨p,hp,?_⟩
  intro y hpy hyp
  have hyN : y∈N := hyp ▸ hN.prop.2.2 y p hpN
  have hpr : p ∈ Set.range (·*y) := hprincipal y hyN ▸ hpN
  obtain ⟨v,hv⟩ := hpr
  change v*y=p at hv
  refine ⟨p*v*p,?_,?_,?_⟩
  · simp only [← mul_assoc,hp]
  · simp only [mul_assoc,hp]
  · calc
      (p*v*p)*y = p*v*(p*y) := mul_assoc _ _ _
      _ = p*(v*y) := by rw [hpy,mul_assoc]
      _ = p := by rw [hv,hp]

namespace Corner
variable {S : Type uSemigroup} [Semigroup S] {p : S}
end Corner
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.ColoringCompactness ----
namespace OAI

universe uModule uColor

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

lemma ultraColor_spec {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) :
    {x | c x=ultraColor c U}∈U := (exists_ultra_color U c).choose_spec

lemma exists_corner_map : ∃ (p : Ultrafilter Strings) (Ψ : LetterGroup →ₙ* Ultrafilter Strings),
    ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p := by
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨p,hp,hi⟩ := exists_group_corner (S:=Ultrafilter Strings) Ultrafilter.continuous_mul_left
  let := Corner.group hp hi
  let letter (z : FiniteEuclidean) : Corner p :=
    ⟨p*(pure (FreeMonoid.of z))*p,by
      constructor
      · simp only [← mul_assoc,hp]
      · simp only [mul_assoc,hp]⟩
  let ψ : LetterGroup →* Corner p := FreeGroup.lift letter
  let v : Corner p →ₙ* Ultrafilter Strings := { toFun := Subtype.val, map_mul' _ _ := rfl }
  refine ⟨p,v.comp ψ.toMulHom,?_⟩
  intro z
  change (ψ (FreeGroup.of z)).val=_
  exact congrArg (fun x : Corner p => x.val) (FreeGroup.lift_apply_of (f:=letter) (x:=z))

theorem paths_monochromatic {s : ℕ} (a : Fin s → FiniteEuclidean)
    (hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ))
    {κ : Type uColor} [Finite κ] (c : FiniteEuclidean → κ) :
    ∃ b : Fin s → FiniteEuclidean,(∀ i j,‖b i-b j‖=‖a i-a j‖) ∧
      ∃ k : κ,∀ i,c (b i)=k := by
  classical
  let := ultrafilterMonoid (M:=Strings)
  obtain ⟨β,hβ,hHJ⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin s) κ
  let := hβ
  obtain ⟨w,lmb,μ,hp,hm,hlmb,hratio⟩ := hpaths (Fintype.card β+1) (by omega)
  obtain ⟨W,hW⟩ := synchronize_paths (Fintype.card β+1) (by omega) hp hm hlmb hratio
  obtain ⟨p,Ψ,hgen⟩ := exists_corner_map
  let coloring : Strings → κ := fun x => c (FiniteEuclidean.flatten x.toList)
  let L : List β := Finset.univ.toList
  let C : (β → Fin s) → κ := fun x => ultraColor coloring ((L.map (fun j => Ψ (W (x j)))).prod)
  obtain ⟨line,k,hline⟩ := hHJ C
  let S : Finset β := Finset.univ.filter (fun j => line.idxFun j=none)
  let t := S.card
  have ht : 1 ≤ t := by
    apply Finset.card_pos.mpr
    obtain ⟨j,hj⟩ := line.proper
    exact ⟨j,by simp [S,hj]⟩
  have htn : t ≤ Fintype.card β+1 := le_trans (Finset.card_le_univ S) (Nat.le_succ _)
  obtain ⟨qs,hqs,hqe⟩ := (hW t ht htn).expand Ψ p hgen
  let q (j : β) : List (UltraColumn (Fin s) Strings) :=
    (line.idxFun j).elim qs (fun i => [.common (Ψ (W i))])
  let u (j : β) : ℝ := if line.idxFun j=none then 1/(t:ℝ) else 0
  have hcol : ∀ j∈L,ColumnPath a (q j) (u j) := by
    intro j _
    cases he : line.idxFun j with
    | none => simpa [q,u,he] using hqs
    | some i => simpa [q,u,he] using (ColumnPath.common (a:=a) (Ψ (W i)))
  have hprod : ∀ j∈L,∀ i,((q j).map (fun q => q.value i)).prod=Ψ (W (line i j)) := by
    intro j _ i
    cases he : line.idxFun j with
    | none => simpa [q,he,Combinatorics.Line.coe_apply] using hqe i
    | some x => simp [q,he,Combinatorics.Line.coe_apply,UltraColumn.value]
  have hweight : (L.map u).sum=1 := by
    have he : (L.map u).sum=∑ j,u j := by
      simp [L]
    rw [he]
    change (∑ j,if line.idxFun j=none then 1/(t:ℝ) else 0)=1
    rw [← Finset.sum_filter]
    change (∑ j∈S,1/(t:ℝ))=1
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (t:ℝ)*(1/(t:ℝ))=1
    exact mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega))
  have hfull : ColumnPath a ((L.map q).flatten) 1 := by
    convert ColumnPath.flatten L q u hcol using 1
    exact hweight.symm
  have hmem : ∀ i,{x : Strings | coloring x=k}∈
      ((((L.map q).flatten).map (fun q => q.value i)).prod : Ultrafilter Strings) := by
    intro i
    rw [flattened_ultra_product L q (fun j i => Ψ (W (line i j))) hprod i]
    have hk := ultraColor_spec coloring ((L.map (fun j => Ψ (W (line i j)))).prod)
    change {x | coloring x=C (line i)}∈_ at hk
    rwa [hline i] at hk
  obtain ⟨xs,hxs,hxB⟩ := UltraColumn.simultaneously_realize ((L.map q).flatten)
    (fun _ => {x : Strings | coloring x=k}) hmem
  let b (i : Fin s) := FiniteEuclidean.flatten ((xs.map (fun x => x i)).prod : Strings).toList
  refine ⟨b,(hfull.realizes xs hxs).congruent,k,?_⟩
  exact hxB
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open Filter
open scoped BigOperators
lemma embed_truncate (x : FiniteEuclidean) (d : ℕ)
    (h : ∀ n∈(coords x).support,n<d) : embed d (truncate d x)=x := by
  apply Finsupp.ext
  intro n
  change coords (embed d (truncate d x)) n=coords x n
  by_cases hn : n<d
  · exact embed_apply d (truncate d x) ⟨n,hn⟩
  · rw [embed_outside d _ n (by omega)]
    exact (Finsupp.notMem_support_iff.mp (fun hm => hn (h n hm))).symm

lemma eventually_embed_truncate (x : FiniteEuclidean) :
    ∀ᶠ d : ℕ in atTop,embed (d+1) (truncate (d+1) x)=x := by
  filter_upwards [eventually_ge_atTop ((coords x).support.sup id)] with d hd
  apply embed_truncate
  intro n hn
  have h := Finset.le_sup (f:=id) hn
  dsimp only [id_eq] at h
  omega
end FiniteEuclidean

theorem finite_coloring_compactness {s : ℕ} (a : Fin s → FiniteEuclidean) (r : ℕ)
    (h : ∀ c : FiniteEuclidean → Fin r,∃ b : Fin s → FiniteEuclidean,
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k) :
    ∃ D : ℕ,1≤D ∧ ∀ c : EuclideanSpace ℝ (Fin D) → Fin r,
      ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
  classical
  by_contra hbad
  have hc : ∀ n : ℕ,∃ c : EuclideanSpace ℝ (Fin (n+1)) → Fin r,
      ¬ ∃ b : Fin s → EuclideanSpace ℝ (Fin (n+1)),
        (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by
    intro n
    by_contra hh
    push Not at hh
    exact hbad ⟨n+1,by omega,hh⟩
  choose c hc using hc
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  let C : FiniteEuclidean → Fin r := fun z => ultraColor
    (fun n => c n (FiniteEuclidean.truncate (n+1) z)) U
  obtain ⟨b,hb,k,hbk⟩ := h C
  have hcolor : ∀ᶠ n in (U : Filter ℕ),∀ i,c n (FiniteEuclidean.truncate (n+1) (b i))=k := by
    apply Filter.eventually_all.mpr
    intro i
    have hh := ultraColor_spec (fun n => c n (FiniteEuclidean.truncate (n+1) (b i))) U
    change ∀ᶠ n in (U : Filter ℕ),c n (FiniteEuclidean.truncate (n+1) (b i))=C (b i) at hh
    rwa [hbk i] at hh
  have he : ∀ᶠ n in (U : Filter ℕ),∀ i,FiniteEuclidean.embed (n+1)
      (FiniteEuclidean.truncate (n+1) (b i))=b i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (Ultrafilter.of_le Filter.atTop) (FiniteEuclidean.eventually_embed_truncate (b i))
  obtain ⟨n,hn,hcol⟩ := (he.and hcolor).exists
  apply hc n
  refine ⟨fun i => FiniteEuclidean.truncate (n+1) (b i),?_,k,hcol⟩
  intro i j
  rw [← (FiniteEuclidean.embed (n+1)).norm_map, map_sub,hn i,hn j,hb]
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.NormalCost ----
namespace OAI

universe uGroup uAction uPoint uAlpha

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators commutatorElement
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

lemma SameOrbit.refl (x : X) : SameOrbit (H:=H) x x := ⟨1,one_smul _ _⟩
lemma SameOrbit.symm {x y : X} (h : SameOrbit (H:=H) x y) : SameOrbit (H:=H) y x := by
  obtain ⟨h,rfl⟩ := h
  exact ⟨h⁻¹,inv_smul_smul h x⟩
lemma SameOrbit.trans {x y z : X} (h : SameOrbit (H:=H) x y) (h' : SameOrbit (H:=H) y z) :
    SameOrbit (H:=H) x z := by
  obtain ⟨h,rfl⟩ := h
  obtain ⟨g,rfl⟩ := h'
  exact ⟨g*h,mul_smul _ _ _⟩
lemma SameOrbit.smul (x : X) (h : H) : SameOrbit (H:=H) x (h•x) := ⟨h,rfl⟩

namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)
omit [L.Normal] in
lemma list_bound (l : List G) (h : ∀ g∈l,g∈L) :
    c.cost l.prod ≤ (l.map c.cost).sum := by
  induction l with
  | nil => simp [c.one]
  | cons g l ih =>
    have hg := h g (by simp)
    have hl : ∀ x∈l,x∈L := fun x hx => h x (by simp [hx])
    exact (c.mul g hg l.prod (L.list_prod_mem hl)).trans (by simpa using add_le_add_left (ih hl) (c.cost g))
omit [L.Normal] in
lemma list_bound_const (l : List G) (h : ∀ g∈l,g∈L) (B : ℝ) (hB : ∀ g∈l,c.cost g≤B) :
    c.cost l.prod ≤ (l.length:ℝ)*B := by
  refine (c.list_bound l h).trans ?_
  induction l with
  | nil => simp
  | cons g l ih =>
    have hh := ih (fun x hx => h x (by simp [hx])) (fun x hx => hB x (by simp [hx]))
    simpa [Nat.cast_add,Nat.cast_one,add_mul,add_comm] using add_le_add (hB g (by simp)) hh

lemma product_difference {α : Type uAlpha} (l : List α) (a b : α → G)
    (h : ∀ j∈l,a j*(b j)⁻¹∈L) :
    (l.map a).prod*((l.map b).prod)⁻¹∈L ∧
    c.cost ((l.map a).prod*((l.map b).prod)⁻¹) ≤
      (l.map (fun j => c.cost (a j*(b j)⁻¹))).sum := by
  induction l with
  | nil => simp [c.one,L.one_mem]
  | cons j l ih =>
    obtain ⟨hm,hc⟩ := ih (fun k hk => h k (by simp [hk]))
    have hj := h j (by simp)
    let z := (l.map a).prod*((l.map b).prod)⁻¹
    have he : (a j*(l.map a).prod)*(b j*(l.map b).prod)⁻¹ =
        (a j*z*(a j)⁻¹)*(a j*(b j)⁻¹) := by dsimp [z]; group
    have hz : a j*z*(a j)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hm _
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he]
    refine ⟨L.mul_mem hz hj,?_⟩
    exact (c.mul _ hz _ hj).trans (by rw [c.conj z hm]; linarith)
end NormalCost

lemma product_difference_mem {N : Subgroup G} [N.Normal] {α : Type uAlpha}
    (l : List α) (a b : α → G) (h : ∀ j∈l,a j*(b j)⁻¹∈N) :
    (l.map a).prod*((l.map b).prod)⁻¹∈N := by
  let q := QuotientGroup.mk' N
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((l.map a).prod*((l.map b).prod)⁻¹)=1
  rw [map_mul,map_inv,mul_inv_eq_one]
  simp only [map_list_prod,List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv] using h j hj

omit [Group H] in
lemma groupList_mem [Fintype H] (h : H) : h∈groupList H := by
  classical
  simp [groupList]
omit [Group H] in
lemma groupList_length [Fintype H] : (groupList H).length=Fintype.card H := by
  classical
  simp [groupList]
lemma groupList_mul_perm [Fintype H] (h : H) :
    ((groupList H).map (·*h)).Perm (groupList H) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
    (Finset.nodup_toList _)).mpr
  intro g
  simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,iff_true]
  exact ⟨g*h⁻¹,by group⟩

lemma orbitAverage_preserves [Fintype H] (N : Subgroup G) [N.Normal]
    (w : X → G) (x y : X)
    (h : ∀ g : H,w (g•x)*(w (g•y))⁻¹∈N) :
    orbitAverage (H:=H) w x*(orbitAverage (H:=H) w y)⁻¹∈N :=
  product_difference_mem _ _ _ (fun g _ => h g)

lemma orbitAverage_derived [Fintype H] (N : Subgroup G) [N.Normal]
    (w : X → G) (x y : X) (horbit : SameOrbit (H:=H) x y)
    (hw : ∀ g : H,w (g•x)∈N) :
    orbitAverage (H:=H) w x*(orbitAverage (H:=H) w y)⁻¹∈⁅N,N⁆ := by
  obtain ⟨h,rfl⟩ := horbit
  let q := QuotientGroup.mk' ⁅N,N⁆
  rw [← div_eq_mul_inv]
  apply QuotientGroup.eq_iff_div_mem.mp
  change q (orbitAverage (H:=H) w x)=q (orbitAverage (H:=H) w (h•x))
  simp only [orbitAverage,map_list_prod,List.map_map]
  have hp := (groupList_mul_perm h).map (fun g => q (w (g•x)))
  simp only [List.map_map,Function.comp_def,mul_smul] at hp
  symm
  apply hp.prod_eq'
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro g k
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.commutator_mem_commutator (by simpa only [mul_smul] using hw (g*h))
      (by simpa only [mul_smul] using hw (k*h)))
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.OrbitAveraging ----
namespace OAI

universe uGroup uAction uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

namespace OrbitWords
variable {letter : X → G} {w : X → G} {m : ℕ}
lemma reindex (hw : OrbitWords (H:=H) letter w m) (g : H) :
    OrbitWords (H:=H) letter (fun x => w (g•x)) m := by
  induction hw with
  | diag a => exact .diag a
  | point h => simpa only [mul_smul] using (point (letter:=letter) (h*g))
  | mul _ _ ihu ihv => exact .mul ihu ihv
lemma normalize (hw : OrbitWords (H:=H) letter w m) (a : G) :
    OrbitWords (H:=H) letter (fun x => w x*a) m := by
  simpa only [Nat.add_zero,Pi.mul_def] using hw.mul (.diag a)
lemma average [Fintype H] (hw : OrbitWords (H:=H) letter w m) :
    OrbitWords (H:=H) letter (orbitAverage (H:=H) w) (Fintype.card H*m) := by
  have aux (l : List H) : OrbitWords (H:=H) letter
      (fun x => (l.map (fun h => w (h•x))).prod) (l.length*m) := by
    induction l with
    | nil => simpa using (diag (letter:=letter) (H:=H) 1)
    | cons h l ih => simpa [Nat.add_mul,add_comm,Pi.mul_def] using (hw.reindex h).mul ih
  change OrbitWords letter (fun x => ((groupList H).map (fun h => w (h•x))).prod) _
  simpa only [groupList_length] using aux (groupList H)
end OrbitWords

lemma orbitIn_normalize {N : Subgroup G} {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) (a : G) : OrbitIn (H:=H) N (fun y => w y*a) x := by
  intro y z hy hz
  simpa only [_root_.mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hw y z hy hz

lemma orbitIn_average [Fintype H] {N : Subgroup G} [N.Normal] {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N (orbitAverage (H:=H) w) x := by
  intro y z hy hz
  apply orbitAverage_preserves
  intro g
  exact hw _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g))

lemma orbitBound_normalize {L : Subgroup G} {c : NormalCost L} {w : X → G} {b : ℝ} {x : X}
    (hw : OrbitBound (H:=H) c w b x) (a : G) :
    OrbitBound (H:=H) c (fun y => w y*a) b x := by
  refine ⟨orbitIn_normalize hw.1 a,?_⟩
  intro y z hy hz
  simpa only [_root_.mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hw.2 y z hy hz

lemma orbitBound_average [Fintype H] {L : Subgroup G} [L.Normal] {c : NormalCost L}
    {w : X → G} {b : ℝ} {x : X} (hw : OrbitBound (H:=H) c w b x) :
    OrbitBound (H:=H) c (orbitAverage (H:=H) w) (Fintype.card H*b) x := by
  refine ⟨orbitIn_average hw.1,?_⟩
  intro y z hy hz
  refine (c.product_difference (groupList H) (fun g => w (g•y)) (fun g => w (g•z))
    (fun g _ => hw.1 _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g)))).2.trans ?_
  have hh : ∀ g∈groupList H,c.cost (w (g•y)*(w (g•z))⁻¹)≤b := fun g _ =>
    hw.2 _ _ (hy.trans (SameOrbit.smul y g)) (hz.trans (SameOrbit.smul z g))
  calc
    _ ≤ ((groupList H).map (fun _ => b)).sum := List.sum_le_sum hh
    _ = _ := by simp [List.map_const',groupList_length,List.sum_replicate, nsmul_eq_mul]

lemma orbitIn_raise [Fintype H] (N : Subgroup G) [N.Normal] {w : X → G} {x : X}
    (hw : OrbitIn (H:=H) N w x) :
    OrbitIn (H:=H) ⁅N,N⁆ (orbitAverage (H:=H) (fun y => w y*(w x)⁻¹)) x := by
  intro y z hy hz
  apply orbitAverage_derived N
  · exact hy.symm.trans hz
  · intro g
    exact hw _ _ (hy.trans (SameOrbit.smul y g)) (SameOrbit.refl x)

lemma contraction_bound [Fintype H] {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (x y : X) (hxy : SameOrbit (H:=H) x y) (B : ℝ)
    (hm : ∀ z,SameOrbit (H:=H) x z → w z∈L)
    (hb : ∀ z,SameOrbit (H:=H) x z → c.cost (w z)≤B) :
    orbitAverage (H:=H) w y*(w x)⁻¹∈L ∧
    c.cost (orbitAverage (H:=H) w y*(w x)⁻¹) ≤ (Fintype.card H-1:ℝ)*B := by
  obtain ⟨g,hg⟩ := hxy.symm
  obtain ⟨p,q,he⟩ := List.mem_iff_append.mp (groupList_mem g)
  let a := (p.map (fun h => w (h•y))).prod
  let b := (q.map (fun h => w (h•y))).prod
  have hmem (h : H) : w (h•y)∈L := hm _ (hxy.trans (SameOrbit.smul y h))
  have hcost (h : H) : c.cost (w (h•y))≤B := hb _ (hxy.trans (SameOrbit.smul y h))
  have ha : a∈L := L.list_prod_mem (by simpa using fun h (_ : h∈p) => hmem h)
  have hb' : b∈L := L.list_prod_mem (by simpa using fun h (_ : h∈q) => hmem h)
  have hc : w x*b*(w x)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hb' _
  have hid : orbitAverage (H:=H) w y*(w x)⁻¹=a*(w x*b*(w x)⁻¹) := by
    simp [orbitAverage,he,hg,a,b,List.prod_append,mul_assoc]
  rw [hid]
  refine ⟨L.mul_mem ha hc,?_⟩
  have hca : c.cost a≤(p.length:ℝ)*B  := by
    simpa only [List.length_map] using c.list_bound_const (p.map (fun h => w (h•y)))
      (by simpa using fun h (_ : h∈p) => hmem h) B
      (by simpa using fun h (_ : h∈p) => hcost h)
  have hcb : c.cost b≤(q.length:ℝ)*B  := by
    simpa only [List.length_map] using c.list_bound_const (q.map (fun h => w (h•y)))
      (by simpa using fun h (_ : h∈q) => hmem h) B
      (by simpa using fun h (_ : h∈q) => hcost h)
  have hn : (Fintype.card H:ℝ)=(p.length:ℝ)+1+(q.length:ℝ) := by
    have := congrArg List.length he
    rw [groupList_length] at this
    exact_mod_cast (by simpa [List.length_append,add_assoc,add_comm,add_left_comm] using this)
  calc
    _ ≤ c.cost a+c.cost b := by simpa [c.conj b hb'] using c.mul a ha _ hc
    _ ≤ _ := by rw [hn]; nlinarith
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H]

namespace Evolution
variable {w v u : X → G} {m n k : ℕ}
lemma trans (h : Evolution (H:=H) w m v n) (h' : Evolution (H:=H) v n u k) :
    Evolution (H:=H) w m u k := by
  induction h' with
  | refl => exact h
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average
lemma words {letter : X → G} (h : Evolution (H:=H) w m v n)
    (hw : OrbitWords (H:=H) letter w m) : OrbitWords (H:=H) letter v n := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact ih.normalize a
  | average _ ih => exact ih.average
lemma positive (h : Evolution (H:=H) w m v n) (hm : 0 < m) : 0 < n := by
  induction h with
  | refl => exact hm
  | normalize _ _ ih => exact ih
  | average _ ih => exact Nat.mul_pos Fintype.card_pos ih
lemma orbitIn (h : Evolution (H:=H) w m v n) {N : Subgroup G} [N.Normal] {x : X}
    (hw : OrbitIn (H:=H) N w x) : OrbitIn (H:=H) N v x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact orbitIn_normalize ih a
  | average _ ih => exact orbitIn_average ih
lemma orbitBound (h : Evolution (H:=H) w m v n) {L : Subgroup G} [L.Normal]
    {c : NormalCost L} {δ : ℝ} {x : X} (hw : OrbitBound (H:=H) c w (δ*m) x) :
    OrbitBound (H:=H) c v (δ*n) x := by
  induction h with
  | refl => exact hw
  | normalize _ a ih => exact orbitBound_normalize ih a
  | average _ ih =>
    simpa only [Nat.cast_mul,mul_left_comm] using orbitBound_average ih
end Evolution

lemma evolve_finite [Fintype X] (w : X → G) (m : ℕ)
    (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k},Evolution (H:=H) v n u k → ∀ x,Good x v n → Good x u k)
    (improve : ∀ {v n},Evolution (H:=H) w m v n → ∀ x,
      ∃ u k,Evolution (H:=H) v n u k ∧ Good x u k) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,Good x v n := by
  classical
  have aux (t : Finset X) : ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x∈t,Good x v n := by
    induction t using Finset.induction_on with
    | empty => exact ⟨w,m,.refl _ _,by simp⟩
    | @insert x t hx ih =>
      obtain ⟨v,n,hev,hv⟩ := ih
      obtain ⟨u,k,heu,hu⟩ := improve hev x
      refine ⟨u,k,hev.trans heu,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hu
      · exact preserve heu y (hv y hy)
  simpa using aux Finset.univ

lemma orbit_raise_depth (N : Subgroup G) [N.Normal] (r : ℕ) (w : X → G) (m : ℕ)
    (x : X) (hw : OrbitIn (H:=H) N w x) :
    ∃ v n,Evolution (H:=H) w m v n ∧ OrbitIn (H:=H) (Derived N r) v x := by
  induction r with
  | zero => exact ⟨w,m,.refl _ _,hw⟩
  | succ r ih =>
    obtain ⟨v,n,hev,hv⟩ := ih
    exact ⟨_,_,(hev.normalize (v x)⁻¹).average,orbitIn_raise (Derived N r) hv⟩

lemma all_orbits_derived [Fintype X] (N : Subgroup G) [N.Normal] (r : ℕ)
    (w : X → G) (m : ℕ) (hw : ∀ x,OrbitIn (H:=H) N w x) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,OrbitIn (H:=H) (Derived N r) v x := by
  apply evolve_finite w m (fun x v _ => OrbitIn (H:=H) (Derived N r) v x)
  · intro v n u k he x hx
    exact he.orbitIn hx
  · intro v n he x
    exact orbit_raise_depth N r v n x (he.orbitIn (hw x))

lemma contraction_iterate {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (m : ℕ) (x : X) (B : ℝ)
    (hm : ∀ y,SameOrbit (H:=H) x y → w y∈L)
    (hb : ∀ y,SameOrbit (H:=H) x y → c.cost (w y)≤B) (k : ℕ) :
    ∃ v,Evolution (H:=H) w m v ((Fintype.card H)^k*m) ∧
      (∀ y,SameOrbit (H:=H) x y → v y∈L) ∧
      ∀ y,SameOrbit (H:=H) x y → c.cost (v y)≤B*(Fintype.card H-1:ℝ)^k := by
  induction k with
  | zero => exact ⟨w,by simpa using (Evolution.refl (H:=H) w m),hm,by simpa using hb⟩
  | succ k ih =>
    obtain ⟨v,hev,hm,hb⟩ := ih
    refine ⟨fun y => orbitAverage (H:=H) v y*(v x)⁻¹,?_,?_,?_⟩
    · convert hev.average.normalize (v x)⁻¹ using 1 ; simp [pow_succ,mul_left_comm,mul_comm]
    · intro y hy
      exact (contraction_bound c v x y hy _ hm hb).1
    · intro y hy
      convert (contraction_bound c v x y hy _ hm hb).2 using 1 ; ring

lemma contraction_rate (h m : ℕ) (hh : 0 < h) (hm : 0 < m) (B δ : ℝ) (hB : 0≤B) (hδ : 0 < δ) :
    ∃ k : ℕ,2*(B*(h-1:ℝ)^k)≤δ*((h^k*m:ℕ):ℝ) := by
  have hh' : (0:ℝ)<h := by exact_mod_cast hh
  have hm' : (0:ℝ)< m := by exact_mod_cast hm
  have hb : 0 < 2*B+1 := by positivity
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ*m/(2*B+1) by positivity) (show (h-1:ℝ)/h<1 by rw [div_lt_one hh']; linarith)
  refine ⟨k,?_⟩
  rw [div_pow,div_lt_iff₀ (pow_pos hh' _)] at hk
  have hk' := (lt_div_iff₀ hb).mp (show (h-1:ℝ)^k/(h:ℝ)^k < δ*m/(2*B+1) by
    rw [div_lt_iff₀ (pow_pos hh' _)]; exact hk)
  have hnon : 0 ≤ (h-1:ℝ)^k/(h:ℝ)^k := by
    apply div_nonneg (pow_nonneg _ _) (pow_nonneg hh'.le _)
    have : (1:ℝ)≤h := by exact_mod_cast hh
    linarith
  have hsmall : 2*B*((h-1:ℝ)^k/(h:ℝ)^k) ≤ δ*m := by nlinarith
  have he := (div_le_iff₀ (pow_pos hh' k)).mp (by
    simpa only [← mul_div_assoc] using hsmall)
  simpa only [Nat.cast_mul,Nat.cast_pow] using (show 2*(B*(h-1:ℝ)^k)≤δ*((h:ℝ)^k*m) by nlinarith [he])
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H] [Fintype X]

lemma orbit_make_small {L : Subgroup G} [L.Normal] (c : NormalCost L)
    (w : X → G) (m : ℕ) (hm : 0 < m) (x : X)
    (hw : OrbitIn (H:=H) L w x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v n,Evolution (H:=H) w m v n ∧ OrbitBound (H:=H) c v (δ*n) x := by
  classical
  let w₀ : X → G := fun y => w y*(w x)⁻¹
  let B : ℝ := ∑ y,c.cost (w₀ y)
  have hB : 0≤B := Finset.sum_nonneg (fun y _ => c.nonneg _)
  have hmem : ∀ y,SameOrbit (H:=H) x y → w₀ y∈L :=
    fun y hy => hw y x hy (SameOrbit.refl x)
  have hbound : ∀ y,SameOrbit (H:=H) x y → c.cost (w₀ y)≤B := by
    intro y _
    exact Finset.single_le_sum (fun z _ => c.nonneg _) (Finset.mem_univ y)
  obtain ⟨k,hk⟩ := contraction_rate (Fintype.card H) m Fintype.card_pos hm B δ hB hδ
  obtain ⟨v,hev,hvm,hvb⟩ := contraction_iterate c w₀ m x B hmem hbound k
  refine ⟨v,(Fintype.card H)^k*m,(Evolution.normalize (.refl w m) (w x)⁻¹).trans hev,?_,?_⟩
  · intro y z hy hz
    exact L.mul_mem (hvm y hy) (L.inv_mem (hvm z hz))
  · intro y z hy hz
    have hcm := c.mul (v y) (hvm y hy) (v z)⁻¹ (L.inv_mem (hvm z hz))
    rw [c.inv _ (hvm z hz)] at hcm
    exact hcm.trans ((add_le_add (hvb y hy) (hvb z hz)).trans (by linarith))

theorem finite_group_averaging (N : Subgroup G) [N.Normal] (r : ℕ)
    (c : NormalCost (Derived N r)) (letter : X → G)
    (hletter : ∀ x y,letter x*(letter y)⁻¹∈N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : X → G) (m : ℕ),OrbitWords (H:=H) letter w m ∧ 0 < m ∧
      ∀ x y,SameOrbit (H:=H) x y →
        w x*(w y)⁻¹∈Derived N r ∧ c.cost (w x*(w y)⁻¹)≤δ*m := by
  have hstart : OrbitWords (H:=H) letter letter 1 := by
    simpa only [one_smul] using (OrbitWords.point (letter:=letter) (1:H))
  obtain ⟨v,n,hev,hv⟩ := all_orbits_derived (H:=H) N r letter 1 (fun _ _ _ _ _ => hletter _ _)
  have hn : 0 < n := hev.positive Nat.zero_lt_one
  obtain ⟨w,m,hew,hw⟩ := evolve_finite v n (fun x w m => OrbitBound (H:=H) c w (δ*m) x)
    (by intro _ _ _ _ he x hx; exact he.orbitBound hx)
    (by
      intro u k he x
      exact orbit_make_small c u k (he.positive hn) x (he.orbitIn (hv x)) δ hδ)
  refine ⟨w,m,hew.words (hev.words hstart),hew.positive hn,?_⟩
  intro x y hxy
  exact ⟨(hw x).1 x y (SameOrbit.refl x) hxy,(hw x).2 x y (SameOrbit.refl x) hxy⟩
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.CorrectionPaths ----
namespace OAI

universe uGroup uIndex uAction uPoint

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [Fintype ι] [DecidableEq ι]
namespace GradedPaths
variable (P : GradedPaths ι G) (L : Subgroup G) [L.Normal]
variable (hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i)

omit [Fintype ι] in
lemma prod_single_eq (l : List ι) (hl : l.Nodup) (g : ι → G) (i : ι) :
    ((l.map (fun j => Pi.mulSingle j (g j))).prod) i=if i∈l then g i else 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hj,hl⟩ := List.nodup_cons.mp hl
    rw [List.map_cons,List.prod_cons,Pi.mul_apply,ih hl]
    by_cases h : i=j
    · subst j; simp [hj]
    · simp [h]

include hL in
omit [L.Normal] in
lemma bounded_tuple (g : ι → G) (hg : ∀ i,g i∈L) :
    P.BoundedFraction g (∑ i,P.singleCost i (g i)) := by
  classical
  have hb := P.bounded_tuple_list (Finset.univ.toList) g (fun i => P.singleCost i (g i))
    (fun i _ => P.singleCost_bounded i (hL i (hg i)))
  have he : ((Finset.univ.toList.map (fun i => Pi.mulSingle i (g i))).prod)=g := by
    ext i
    simpa using prod_single_eq Finset.univ.toList (Finset.nodup_toList _) g i
  rw [he] at hb
  simpa using hb

omit [L.Normal] in
lemma correction_cost (g : ι → G) (hg : ∀ i,g i∈L) (B : ℝ)
    (hc : ∀ i,(P.normalCost L hL).cost (g i)≤B) :
    ∃ u v m n,P.Holds u m ∧ P.Holds v n ∧ g=u*v⁻¹ ∧
      (m+n:ℕ)≤(Fintype.card ι:ℝ)*B := by
  obtain ⟨u,v,m,n,hu,hv,he,hn⟩ := P.bounded_tuple L hL g hg
  refine ⟨u,v,m,n,hu,hv,he,?_⟩
  calc
    ((m+n:ℕ):ℝ) ≤ ∑ i,(P.singleCost i (g i):ℝ) := by exact_mod_cast hn
    _ ≤ ∑ i,B := Finset.sum_le_sum (fun i _ =>
      (Nat.cast_le.mpr (P.single_le_maxCost i (g i))).trans (hc i))
    _ = _ := by simp
end GradedPaths
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {H : Type uAction} {X : Type uPoint} [Fintype ι] [DecidableEq ι]
variable [Group H] [MulAction H X] [Fintype H] [Fintype X]

omit [Fintype ι] [DecidableEq ι] [Fintype H] [Fintype X] in
lemma OrbitWords.path {a : ι → FiniteEuclidean} (z : X → FiniteEuclidean)
    (f : ι → X) (q : ℝ) (hq : ∀ h : H,CopyPath a q (fun i => z (h • f i)))
    {w : X → LetterGroup} {m : ℕ} (hw : OrbitWords (H:=H) (fun x => FreeGroup.of (z x)) w m) :
    Path a (fun i => w (f i)) (q*m) := by
  induction hw with
  | diag g => simpa using (Path.diag (a:=a) g)
  | point h => simpa using (Path.copy (a:=a) _ (hq h))
  | mul _ _ ihu ihv => simpa only [Nat.cast_add,mul_add,Pi.mul_def] using ihu.mul ihv

theorem averaged_equal_endpoints (a : ι → FiniteEuclidean) (ha : Function.Injective a)
    (z : X → FiniteEuclidean) (f g : ι → X) (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ)
    (hf : ∀ h : H,CopyPath a 1 (fun i => z (h • f i)))
    (hg : ∀ h : H,CopyPath a q (fun i => z (h • g i)))
    (horbit : ∀ i,SameOrbit (H:=H) (f i) (g i)) :
    ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧ 0 < lmb ∧ 0 ≤ μ ∧
      μ/lmb ≤ q+(Fintype.card ι:ℝ)*δ := by
  let N := AugKernel FiniteEuclidean
  let L := Derived N (Fintype.card ι-2)
  let P := unitGraded a
  have hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i := by
    apply derived_subset_single N (Fintype.card ι-2) ι P.monoid P.diagonal
      (unit_pair_inverse a) (unit_pair_coverage a ha)
    omega
  let c := P.normalCost L hL
  obtain ⟨w,m,hw,hm,hwm⟩ := finite_group_averaging (H:=H) N (Fintype.card ι-2)
    c (fun x => FreeGroup.of (z x)) (fun x y => letter_difference_mem (z x) (z y)) δ hδ
  let Dp : ι → LetterGroup := fun i => w (f i)
  let Dm : ι → LetterGroup := fun i => w (g i)
  have hp : Path a Dp (m:ℝ) := by simpa using hw.path z f 1 hf
  have hn : Path a Dm (q*m) := hw.path z g q hg
  let r : ι → LetterGroup := Dp⁻¹*Dm
  have hrc : ∀ i,r i∈L ∧ c.cost (r i) ≤ δ*m := by
    intro i
    obtain ⟨hmem,hcost⟩ := hwm (f i) (g i) (horbit i)
    have he : r i=(w (f i))⁻¹*(w (f i)*(w (g i))⁻¹)⁻¹*((w (f i))⁻¹)⁻¹ := by
      dsimp [r,Dp,Dm]; group
    rw [he]
    refine ⟨(inferInstance : L.Normal).conj_mem _ (L.inv_mem hmem) _,?_⟩
    rw [c.conj _ (L.inv_mem hmem),c.inv _ hmem]
    exact hcost
  obtain ⟨u,v,b,e,hu,hv,he,hbe⟩ := P.correction_cost L hL r (fun i => (hrc i).1)
    (δ*m) (fun i => (hrc i).2)
  have heq : Dp*u=Dm*v := by
    have ht := congrArg (fun t => Dp*t*v) he
    simpa [r,mul_assoc] using ht.symm
  have h₁ : Path a (Dp*u) ((m:ℝ)+b) := hp.mul (UnitWords.path hu)
  have h₂ : Path a (Dp*u) (q*m+e) := by rw [heq]; exact hn.mul (UnitWords.path hv)
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hb : (0:ℝ) ≤ b := Nat.cast_nonneg _
  have he' : (0:ℝ) ≤ e := Nat.cast_nonneg _
  refine ⟨_,_,_,h₁,h₂,by positivity,by positivity,?_⟩
  apply (div_le_iff₀ (by positivity : (0:ℝ) < m+b)).mpr
  have hc' : (b:ℝ)+e ≤ (Fintype.card ι:ℝ)*(δ*m) := by simpa only [Nat.cast_add] using hbe
  have hcd : 0 ≤ (Fintype.card ι:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
  nlinarith
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators

lemma permute_mul {ℓ : ℕ} (σ τ : Equiv.Perm (Fin ℓ)) (x : EuclideanSpace ℝ (Fin ℓ)) :
    permute (σ*τ) x=permute σ (permute τ x) := by ext j; rfl
theorem permutation_equal_endpoints {s d ℓ : ℕ} (a : Fin s → EuclideanSpace ℝ (Fin d))
    (ha : Function.Injective a) (f g : Fin s → EuclideanSpace ℝ (Fin ℓ))
    (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ)
    (hf : ∀ i j,‖f i-f j‖^2=‖a i-a j‖^2)
    (hg : ∀ i j,‖g i-g j‖^2=q*‖a i-a j‖^2)
    (hperm : ∀ i,∃ σ : Equiv.Perm (Fin ℓ),∀ x,g i (σ x)=f i x) :
    ∃ w lmb μ,Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧ 0 < lmb ∧ 0 ≤ μ ∧ μ/lmb ≤ q+s*δ := by
  classical
  choose σ hσ using hperm
  let H := Equiv.Perm (Fin ℓ)
  let X := H×Fin s
  let : MulAction H X :=
    { smul := fun h x => (h*x.1,x.2)
      one_smul := by intro x; exact Prod.ext (one_mul _) rfl
      mul_smul := by intro h k x; exact Prod.ext (mul_assoc _ _ _) rfl }
  let z : X → FiniteEuclidean := fun x => FiniteEuclidean.embed ℓ (permute x.1 (f x.2))
  have hσ' (i : Fin s) : permute (σ i) (f i)=g i := by
    ext j
    simpa using (hσ i ((σ i).symm j)).symm
  have hcopy (h : H) (i : Fin s) :
      z (h • ((σ i,i):X))=FiniteEuclidean.embed ℓ (permute h (g i)) := by
    change FiniteEuclidean.embed ℓ (permute (h*σ i) (f i))=_
    rw [permute_mul,hσ']
  have ht := averaged_equal_endpoints (H:=H) (X:=X) (fun i => FiniteEuclidean.embed d (a i))
    ((FiniteEuclidean.embed d).injective.comp ha) z (fun i => (1,i)) (fun i => (σ i,i))
    q δ hq hδ
  simp only [Fintype.card_fin] at ht
  apply ht
  · intro h
    refine ⟨zero_le_one,?_⟩
    intro i j
    change ‖FiniteEuclidean.embed ℓ (permute (h*1) (f i))-
      FiniteEuclidean.embed ℓ (permute (h*1) (f j))‖^2=_
    simp only [mul_one,← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map,one_mul]
    exact hf i j
  · intro h
    refine ⟨hq.le,?_⟩
    intro i j
    dsimp only
    rw [hcopy h i,hcopy h j]
    simp only [← map_sub,LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]
    exact hg i j
  · intro i
    exact ⟨σ i,by change (σ i*1,i)=(σ i,i); simp⟩
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Main ----
namespace OAI

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey

theorem fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by
  have hreal := fieldCriterion_realCriterion a h
  have hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,
      Path (fun i => FiniteEuclidean.embed d (a i)) w lmb ∧
      Path (fun i => FiniteEuclidean.embed d (a i)) w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ) := by
    intro n hn
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hs' : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
    let η : ℝ := 1/(4*n)
    let δ : ℝ := 1/(4*n*s)
    have hη : 0<η := by dsimp [η]; positivity
    have hδ : 0<δ := by dsimp [δ]; positivity
    obtain ⟨ℓ,hℓ,f,g,hf,hg,hperm⟩ := realCriterion_two_scale a hd (by omega) hreal η hη
    have hq : 0<η/(1+η) := div_pos hη (by linarith)
    obtain ⟨w,lmb,μ,hp,hm,hlmb,hμ,hr⟩ :=
      permutation_equal_endpoints a ha f g (η/(1+η)) δ hq hδ hf hg hperm
    refine ⟨w,lmb,μ,hp,hm,hlmb,lt_of_le_of_lt hr ?_⟩
    have hq' : η/(1+η)<η := (div_lt_iff₀ (by linarith : 0<1+η)).mpr (by nlinarith)
    have he : η+(s:ℝ)*δ=1/(2*n) := by
      dsimp [η,δ]
      field_simp
      ring
    have hhalf : (1:ℝ)/(2*n)<1/n := by
      apply one_div_lt_one_div_of_lt hn'
      nlinarith
    rw [← he] at hhalf
    linarith
  intro r hr
  obtain ⟨D,hD,hmono⟩ := finite_coloring_compactness
    (fun i => FiniteEuclidean.embed d (a i)) r
    (fun c => paths_monochromatic _ hpaths c)
  refine ⟨D,hD,?_⟩
  intro c
  obtain ⟨b,hb,k,hk⟩ := hmono c
  refine ⟨b,?_,k,hk⟩
  intro i j
  rw [dist_eq_norm,dist_eq_norm,hb,← map_sub,LinearIsometry.norm_map]

end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.fieldCriterion_ramsey := @_root_.OAI.EuclideanRamsey.fieldCriterion_ramsey
