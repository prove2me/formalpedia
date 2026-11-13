-- Prove2me | solution 1 for OAI.KadisonKastler.tomiyama_corner_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:41:01.171319+00:00
-- url     : https://prove2.me/submissions/20f485f8-df63-408e-b3f9-3630ffb349cb

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Module
import Definitions.Def_Q260K000
import Definitions.Def_Q260K007

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaNormGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm geometry used in the projection theorem

A quadratic norm bound at the identity of a corner forces the real
first-order term to vanish.  This is the elementary norm argument in
Tomiyama's proof, separated from any operator-field representation.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.tomiyamaOrder
local instance tomiyamaStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem le_zero_of_inverse_bounds (a b : B)
    (h : ∀ n : ℕ, a ≤ (((n : ℝ) + 1)⁻¹) • b) : a ≤ 0 := by
  have ht : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹) • b) atTop (𝓝 (0 : B)) := by
    simpa only [one_div, zero_smul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const b)
  exact ge_of_tendsto ht (Eventually.of_forall h)

private theorem corner_real_term_nonpos (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    x + star x ≤ 0 := by
  have hps : p * star x = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hxp
  have hsp : star x * p = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpx
  have hstep (t : ℝ) (ht : 0 < t) : x + star x ≤ t • (C • p) := by
    let z := p + t • x
    have hpz : p * z = z := by
      dsimp [z]
      rw [mul_add, mul_smul_comm, hp.isIdempotentElem.eq, hpx]
    have hzp : z * p = z := by
      dsimp [z]
      rw [add_mul, smul_mul_assoc, hp.isIdempotentElem.eq, hxp]
    have hpsz : p * star z = star z := by
      simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hzp
    have hb : star z * z ≤ (1 + C * t ^ 2) • (1 : B) := by
      calc
        star z * z ≤ algebraMap ℝ B (‖z‖ ^ 2) :=
          CStarAlgebra.star_mul_le_algebraMap_norm_sq
        _ ≤ (1 + C * t ^ 2) • (1 : B) := by
          rw [Algebra.algebraMap_eq_smul_one]
          exact smul_le_smul_of_nonneg_right (h t) zero_le_one
    have hb' := hp.isSelfAdjoint.conjugate_le_conjugate hb
    have hleft : p * (star z * z) * p = star z * z := by
      rw [← mul_assoc p, hpsz, mul_assoc, hzp]
    have hright : p * ((1 + C * t ^ 2) • (1 : B)) * p =
        (1 + C * t ^ 2) • p := by
      rw [mul_smul_comm, mul_one, smul_mul_assoc, hp.isIdempotentElem.eq]
    rw [hleft, hright] at hb'
    have hexpand : star z * z =
        p + t • (x + star x) + t ^ 2 • (star x * x) := by
      simp only [z, star_add, star_smul, star_trivial, hp.isSelfAdjoint.star_eq,
        add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        hp.isIdempotentElem.eq, hpx, hsp]
      module
    rw [hexpand] at hb'
    have hquad : (0 : B) ≤ t ^ 2 • (star x * x) :=
      smul_nonneg (sq_nonneg t) (star_mul_self_nonneg x)
    have hle : p + t • (x + star x) ≤ (1 + C * t ^ 2) • p :=
      (le_add_of_nonneg_right hquad).trans hb'
    have hsplit : (1 + C * t ^ 2) • p = p + t • (t • (C • p)) := by
      module
    rw [hsplit] at hle
    exact (smul_le_smul_iff_of_pos_left ht).mp ((add_le_add_iff_left p).mp hle)
  apply le_zero_of_inverse_bounds (x + star x) (C • p)
  intro n
  exact hstep _ (inv_pos.mpr (by positivity))

/-- A quadratic norm bound at a projection makes a corner element
skew-adjoint. This also applies to the zero corner. -/
theorem corner_skewAdjoint_of_quadratic_bound (p x : B) (hp : IsStarProjection p)
    (hpx : p * x = x) (hxp : x * p = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖p + t • x‖ ^ 2 ≤ 1 + C * t ^ 2) :
    star x = -x := by
  have hle := corner_real_term_nonpos p x hp hpx hxp C h
  have hneg := corner_real_term_nonpos p (-x) hp
    (by rw [mul_neg, hpx]) (by rw [neg_mul, hxp]) C (fun t => by
      simpa only [smul_neg, neg_smul, neg_sq] using h (-t))
  have hge : 0 ≤ x + star x := by
    simpa only [star_neg, ← neg_add, neg_nonpos] using hneg
  have he : x + star x = 0 := le_antisymm hle hge
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm])

/-- Applying the tangent argument to the imaginary multiple detects
self-adjointness using only the norm. -/
theorem isSelfAdjoint_of_quadratic_norm_bound (x : B) (C : ℝ)
    (h : ∀ t : ℝ, ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    IsSelfAdjoint x := by
  have hs := corner_skewAdjoint_of_quadratic_bound 1 (Complex.I • x)
    (IsStarProjection.one B) (one_mul _) (mul_one _) C h
  have he : (-Complex.I) • star x = (-Complex.I) • x := by
    simpa only [star_smul, Complex.star_def, Complex.conj_I, neg_smul] using hs
  exact (smul_right_injective B (neg_ne_zero.mpr Complex.I_ne_zero)) he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `normSubLeMaxCompat` (port compat, absent from our Mathlib). -/
private theorem normSubLeMaxCompat_p0 {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have hsa : IsSelfAdjoint (a - b) :=
    (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have h := IsSelfAdjoint.norm_le_max_of_le_of_le (a := -b) (b := a) (x := a - b)
    (by rw [le_sub_iff_add_le]; simpa using ha) (sub_le_self a hb) hsa
  rwa [norm_neg, max_comm] at h

/-! # Positivity of unital contractions

This is the first step of the norm-one projection argument.  Positivity
and adjoint preservation are derived from the norm bound and the unit.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaSourceOrder_r165b4c_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaSourceStarOrder_r165b4c_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
attribute [local instance] OAI.KadisonKastler.tomiyamaTargetOrder
local instance tomiyamaTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem cstar_norm_one_le (A : Type*) [CStarAlgebra A] : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖star (1 : A) * (1 : A)‖ = ‖(1 : A)‖ * ‖(1 : A)‖ :=
    CStarRing.norm_star_mul_self
  simp only [star_one, one_mul] at h
  nlinarith [norm_nonneg (1 : A)]

private theorem norm_imaginary_perturbation_sq (x : A) (hx : IsSelfAdjoint x) (t : ℝ) :
    ‖1 + t • (Complex.I • x)‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
  have he : star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x)) =
      1 + t ^ 2 • (star x * x) := by
    simp only [star_add, star_one, star_smul, star_trivial, Complex.star_def,
      Complex.conj_I, hx.star_eq, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm]
    match_scalars
    all_goals ring_nf
    all_goals norm_num [Complex.I_sq]
  calc
    ‖1 + t • (Complex.I • x)‖ ^ 2 =
        ‖star (1 + t • (Complex.I • x)) * (1 + t • (Complex.I • x))‖ := by
      rw [CStarRing.norm_star_mul_self, pow_two]
    _ = ‖1 + t ^ 2 • (star x * x)‖ := congrArg norm he
    _ ≤ ‖(1 : A)‖ + ‖t ^ 2 • (star x * x)‖ := norm_add_le _ _
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        CStarRing.norm_star_mul_self]
      nlinarith [cstar_norm_one_le A]

/-- A unital complex-linear contraction preserves self-adjointness. -/
theorem unital_contraction_isSelfAdjoint (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1)
    (x : A) (hx : IsSelfAdjoint x) : IsSelfAdjoint (P x) := by
  apply isSelfAdjoint_of_quadratic_norm_bound (P x) (‖x‖ ^ 2)
  intro t
  have he : P (1 + t • (Complex.I • x)) = 1 + t • (Complex.I • P x) := by
    rw [map_add, h1, P.map_smul_of_tower, map_smul]
  calc
    ‖1 + t • (Complex.I • P x)‖ ^ 2 = ‖P (1 + t • (Complex.I • x))‖ ^ 2 := by rw [he]
    _ ≤ ‖1 + t • (Complex.I • x)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hP _) 2
    _ ≤ 1 + ‖x‖ ^ 2 * t ^ 2 := norm_imaginary_perturbation_sq x hx t

/-- A unital complex-linear contraction is positive. -/
theorem unital_contraction_nonneg (P : A →L[ℂ] B)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (h1 : P 1 = 1)
    (x : A) (hx : 0 ≤ x) : 0 ≤ P x := by
  by_cases hx0 : x = 0
  · simp only [hx0, map_zero, le_refl]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  let y := ‖x‖⁻¹ • x
  have hy : 0 ≤ y := smul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hx
  have hyn : ‖y‖ ≤ 1 := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hn, le_refl]
  have hs := unital_contraction_isSelfAdjoint P hP h1 y hy.isSelfAdjoint
  have hdiff : ‖1 - P y‖ ≤ 1 := by
    rw [← h1, ← map_sub]
    exact (hP _).trans ((normSubLeMaxCompat_p0
      (show (0 : A) ≤ 1 from zero_le_one) hy).trans
        (max_le (cstar_norm_one_le A) hyn))
  have hle : 1 - P y ≤ (1 : B) := by
    apply ((IsSelfAdjoint.one B).sub hs).le_algebraMap_norm_self.trans
    rw [Algebra.algebraMap_eq_smul_one]
    simpa only [one_smul] using
      (smul_le_smul_of_nonneg_right hdiff (show (0 : B) ≤ 1 from zero_le_one))
  have hpy : 0 ≤ P y := (sub_le_self_iff _).mp hle
  have he : P x = ‖x‖ • P y := by
    rw [← P.map_smul_of_tower]
    congr 1
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [he]
  exact smul_nonneg (norm_nonneg _) hpy

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The projection part of Tomiyama's theorem

A unital contractive retraction onto a C-star subalgebra respects left
and right multiplication by projections in that subalgebra.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance tomiyamaProjectionSourceOrder_r165b4c_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaProjectionSourceStarOrder_r165b4c_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
attribute [local instance] OAI.KadisonKastler.tomiyamaProjectionTargetOrder
local instance tomiyamaProjectionTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hfix in
private theorem tomiyama_map_one : P 1 = 1 := by
  simpa only [map_one] using hfix 1

include hP hfix

private theorem tomiyama_mono {x y : A} (hxy : x ≤ y) : P x ≤ P y := by
  rw [← sub_nonneg, ← map_sub]
  exact unital_contraction_nonneg P hP (tomiyama_map_one φ P hfix) _ (sub_nonneg.mpr hxy)

/-- Positivity ensures that the image of a diagonal corner stays in that
corner. -/
theorem tomiyama_corner_supported_oai (e : B) (he : IsStarProjection e) (x : A) :
    e * P (φ e * x * φ e) * e = P (φ e * x * φ e) := by
  have hbasic (x : A) (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1) :
      e * P (φ e * x * φ e) * e = P (φ e * x * φ e) := by
    have heφ := he.map φ
    have hpos : 0 ≤ φ e * x * φ e := by
      simpa only [heφ.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hx (φ e)
    have hupper : φ e * x * φ e ≤ φ e := by
      have ht := heφ.isSelfAdjoint.conjugate_le_conjugate
        ((CStarAlgebra.norm_le_one_iff_of_nonneg x hx).mp hxn)
      simpa only [mul_one, heφ.isIdempotentElem.eq] using ht
    have himg : 0 ≤ P (φ e * x * φ e) :=
      unital_contraction_nonneg P hP (tomiyama_map_one φ P hfix) _ hpos
    have hi : P (φ e * x * φ e) ≤ e := by
      simpa only [hfix] using tomiyama_mono φ P hP hfix hupper
    exact he.conjugate_of_nonneg_of_le himg hi
  have hx : x ∈ Submodule.span ℂ ({a : A | 0 ≤ a} ∩ Metric.closedBall 0 1) := by
    rw [CStarAlgebra.span_nonneg_inter_unitClosedBall]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hbasic y hy.1 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy.2)
  | zero => simp only [mul_zero, zero_mul, map_zero]
  | add y z hy hz hiy hiz =>
    simp only [mul_add, add_mul, map_add, hiy, hiz]
  | smul c y hy hiy =>
    simp only [mul_smul_comm, smul_mul_assoc, map_smul, hiy]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.tomiyama_corner_supported_oai.{u_1, u_2} := @OAI.KadisonKastler.tomiyama_corner_supported_oai.{u_1, u_2}
