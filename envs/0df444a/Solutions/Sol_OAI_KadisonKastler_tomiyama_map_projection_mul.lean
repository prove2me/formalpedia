-- Prove2me | solution 1 for OAI.KadisonKastler.tomiyama_map_projection_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:40:59.989238+00:00
-- url     : https://prove2.me/submissions/3c6bdebb-8717-44cb-9352-9c980b0227ba

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Module
import Definitions.Def_Q260K007
import Theorems.Thm_OAI_KadisonKastler_tomiyama_corner_supported

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaNormGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaCornerGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Orthogonal-corner norm calculations

These are the elementary norm estimates behind Tomiyama's projection
argument. They do not assume positivity or a representation of the algebra.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Compression by a star projection is contractive. -/
theorem norm_projection_compression_le (e x : A) (he : IsStarProjection e) :
    ‖e * x * e‖ ≤ ‖x‖ := by
  calc
    ‖e * x * e‖ ≤ ‖e * x‖ * ‖e‖ := norm_mul_le _ _
    _ ≤ (‖e‖ * ‖x‖) * ‖e‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 := by
      gcongr <;> exact IsStarProjection.norm_le e he
    _ = ‖x‖ := by ring

/-- Two mutually orthogonal operator blocks have the maximum norm. -/
theorem norm_add_eq_max_of_orthogonal_products (a b : A)
    (hab : star a * b = 0) (hab' : a * star b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hp : (star a * a) * (star b * b) = 0 := by
    calc
      (star a * a) * (star b * b) = star a * (a * star b) * b := by simp only [mul_assoc]
      _ = 0 := by rw [hab', mul_zero, zero_mul]
  have he : ‖a + b‖ ^ 2 = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
    calc
      ‖a + b‖ ^ 2 = ‖star (a + b) * (a + b)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖star a * a + star b * b‖ := by
        congr 1
        simp only [star_add, add_mul, mul_add, hab, hba, add_zero, zero_add]
      _ = max ‖star a * a‖ ‖star b * b‖ :=
        (IsSelfAdjoint.star_mul_self a).norm_add_eq_max (IsSelfAdjoint.star_mul_self b) hp
      _ = max (‖a‖ ^ 2) (‖b‖ ^ 2) := by
        rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self, pow_two, pow_two]
  rcases le_total ‖a‖ ‖b‖ with h | h
  · rw [max_eq_right h]
    rw [max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg b]
  · rw [max_eq_left h]
    rw [max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h 2)] at he
    nlinarith [norm_nonneg (a + b), norm_nonneg a]

/-- The norm estimate also holds with two different projections. -/
theorem norm_two_projection_compression_le (e f x : A)
    (he : IsStarProjection e) (hf : IsStarProjection f) :
    ‖e * x * f‖ ≤ ‖x‖ := by
  calc
    ‖e * x * f‖ ≤ ‖e * x‖ * ‖f‖ := norm_mul_le _ _
    _ ≤ (‖e‖ * ‖x‖) * ‖f‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖x‖) * 1 := by
      gcongr
      · exact IsStarProjection.norm_le e he
      · exact IsStarProjection.norm_le f hf
    _ = ‖x‖ := by ring

/-- An upper and a lower off-diagonal block have maximum norm. -/
theorem norm_add_eq_max_opposite_corners (e a b : A) (he : IsSelfAdjoint e)
    (hea : e * a = a) (hae : a * e = 0)
    (heb : e * b = 0) (hbe : b * e = b) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  have hsa : star a * e = star a := by
    simpa only [star_mul, he.star_eq] using congrArg star hea
  have hsb : e * star b = star b := by
    simpa only [star_mul, he.star_eq] using congrArg star hbe
  apply norm_add_eq_max_of_orthogonal_products
  · calc
      star a * b = (star a * e) * b := by rw [hsa]
      _ = 0 := by rw [mul_assoc, heb, mul_zero]
  · calc
      a * star b = a * (e * star b) := by rw [hsb]
      _ = 0 := by rw [← mul_assoc, hae, zero_mul]

/-- A zero product with a projection gives a quadratic perturbation bound. -/
theorem norm_projection_add_sq_le (e z : A) (he : IsStarProjection e)
    (hze : z * e = 0) (t : ℝ) :
    ‖e + t • z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
  have hes : e * star z = 0 := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq, star_zero] using congrArg star hze
  have hprod : (e + t • z) * star (e + t • z) = e + t ^ 2 • (z * star z) := by
    simp only [star_add, star_smul, star_trivial, he.isSelfAdjoint.star_eq,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hze, hes, smul_zero,
      he.isIdempotentElem.eq, add_zero, zero_add]
    module
  calc
    ‖e + t • z‖ ^ 2 = ‖(e + t • z) * star (e + t • z)‖ := by
      rw [CStarRing.norm_self_mul_star, pow_two]
    _ = ‖e + t ^ 2 • (z * star z)‖ := congrArg norm hprod
    _ ≤ ‖e‖ + ‖t ^ 2 • (z * star z)‖ := norm_add_le _ _
    _ ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
        CStarRing.norm_self_mul_star]
      nlinarith [IsStarProjection.norm_le e he]

/-- The left-product version follows by adjoints. -/
theorem norm_projection_add_sq_le' (e z : A) (he : IsStarProjection e)
    (hez : e * z = 0) (t : ℝ) :
    ‖e + t • z‖ ^ 2 ≤ 1 + ‖z‖ ^ 2 * t ^ 2 := by
  have hz : star z * e = 0 := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq, star_zero] using congrArg star hez
  have h := norm_projection_add_sq_le e (star z) he hz t
  have hn : ‖e + t • star z‖ = ‖e + t • z‖ := by
    simpa only [star_add, star_smul, star_trivial, he.isSelfAdjoint.star_eq] using
      (norm_star (e + t • z))
  simpa only [hn, norm_star] using h

/-- Testing both real and imaginary perturbations forces a compressed
first-order term to vanish. -/
theorem corner_eq_zero_of_quadratic_bounds (e x : A) (he : IsStarProjection e)
    (hex : e * x = x) (hxe : x * e = x) (C : ℝ)
    (h : ∀ t : ℝ, ‖e + t • x‖ ^ 2 ≤ 1 + C * t ^ 2)
    (hi : ∀ t : ℝ, ‖e + t • (Complex.I • x)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    x = 0 := by
  have hs := corner_skewAdjoint_of_quadratic_bound e x he hex hxe C h
  have hsi := corner_skewAdjoint_of_quadratic_bound e (Complex.I • x) he
    (by rw [mul_smul_comm, hex]) (by rw [smul_mul_assoc, hxe]) C hi
  have hself : star x = x := by
    apply smul_right_injective A (neg_ne_zero.mpr Complex.I_ne_zero)
    simpa only [star_smul, Complex.star_def, Complex.conj_I, neg_smul] using hsi
  have htwo : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    calc
      x + x = star x + x := congrArg (· + x) hself.symm
      _ = 0 := by rw [hs, neg_add_cancel]
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance tomiyamaProjectionSourceOrder_r049771_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaProjectionSourceStarOrder_r049771_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
attribute [local instance] OAI.KadisonKastler.tomiyamaProjectionTargetOrder
local instance tomiyamaProjectionTargetStarOrder_r049771_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hP hfix

private theorem tomiyama_compressed_zero_of_bounds (e : B) (he : IsStarProjection e)
    (z : A) (C : ℝ)
    (hb : ∀ t : ℝ, ‖φ e + t • z‖ ^ 2 ≤ 1 + C * t ^ 2)
    (hi : ∀ t : ℝ, ‖φ e + t • (Complex.I • z)‖ ^ 2 ≤ 1 + C * t ^ 2) :
    e * P z * e = 0 := by
  have hbound (a : A) (t : ℝ) :
      ‖e + t • (e * P a * e)‖ ≤ ‖φ e + t • a‖ := by
    calc
      ‖e + t • (e * P a * e)‖ = ‖e * P (φ e + t • a) * e‖ := by
        rw [map_add, P.map_smul_of_tower, hfix, mul_add, add_mul,
          mul_smul_comm, smul_mul_assoc, he.isIdempotentElem.eq,
          he.isIdempotentElem.eq]
      _ ≤ ‖P (φ e + t • a)‖ := norm_projection_compression_le e _ he
      _ ≤ ‖φ e + t • a‖ := hP _
  apply corner_eq_zero_of_quadratic_bounds e _ he
    (by rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq])
    (by simp only [mul_assoc, he.isIdempotentElem.eq]) C
  · intro t
    exact (pow_le_pow_left₀ (norm_nonneg _) (hbound z t) 2).trans (hb t)
  · intro t
    have hn := hbound (Complex.I • z) t
    simp only [map_smul, mul_smul_comm, smul_mul_assoc] at hn
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (hi t)

/-- A source block orthogonal on the right has zero diagonal image. -/
theorem tomiyama_compressed_zero_of_mul_right_zero (e : B) (he : IsStarProjection e)
    (z : A) (hz : z * φ e = 0) : e * P z * e = 0 := by
  apply tomiyama_compressed_zero_of_bounds φ P hP hfix e he z (‖z‖ ^ 2)
  · exact norm_projection_add_sq_le (φ e) z (he.map φ) hz
  · intro t
    have hi : (Complex.I • z) * φ e = 0 := by rw [smul_mul_assoc, hz, smul_zero]
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      norm_projection_add_sq_le (φ e) (Complex.I • z) (he.map φ) hi t

/-- The analogous statement for a source block orthogonal on the left. -/
theorem tomiyama_compressed_zero_of_mul_left_zero (e : B) (he : IsStarProjection e)
    (z : A) (hz : φ e * z = 0) : e * P z * e = 0 := by
  apply tomiyama_compressed_zero_of_bounds φ P hP hfix e he z (‖z‖ ^ 2)
  · exact norm_projection_add_sq_le' (φ e) z (he.map φ) hz
  · intro t
    have hi : φ e * (Complex.I • z) = 0 := by rw [mul_smul_comm, hz, smul_zero]
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      norm_projection_add_sq_le' (φ e) (Complex.I • z) (he.map φ) hi t

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TomiyamaBimodule
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bimodule identities for projections

The opposite-corner norm comparison completes the algebraic part of
Tomiyama's theorem. The last theorem extends the identities whenever the
target is the norm closure of the span of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hP hfix

private theorem tomiyama_no_reverse_block (e : B) (he : IsStarProjection e)
    (z : A) (hel : φ e * z = z) (her : z * φ e = 0) :
    (1 - e) * P z * e = 0 := by
  let w := (1 - e) * P z * e
  have hew : e * w = 0 := by
    dsimp [w]
    rw [← mul_assoc, ← mul_assoc, he.mul_one_sub_self, zero_mul, zero_mul]
  have hwe : w * e = w := by
    dsimp [w]
    rw [mul_assoc, he.isIdempotentElem.eq]
  by_contra hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let t : ℝ := (‖z‖ + 1) / ‖w‖
  have ht : 0 ≤ t := div_nonneg (by positivity) hwn.le
  have htw : t * ‖w‖ = ‖z‖ + 1 := div_mul_cancel₀ _ hwn.ne'
  have hnorm : ‖z + t • φ w‖ ≤ ‖z‖ + 1 := by
    rw [norm_add_eq_max_opposite_corners (φ e) z (t • φ w)
      (he.map φ).isSelfAdjoint hel her]
    · apply max_le
      · linarith
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        exact (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le φ w) ht).trans htw.le
    · rw [mul_smul_comm, ← map_mul, hew, map_zero, smul_zero]
    · rw [smul_mul_assoc, ← map_mul, hwe]
  have hcomp : (1 - e) * (P z + t • w) * e = (1 + t) • w := by
    have hqw : (1 - e) * w = w := by
      dsimp [w]
      rw [← mul_assoc, ← mul_assoc, he.one_sub.isIdempotentElem.eq]
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hqw, hwe]
    change w + t • w = (1 + t) • w
    module
  have hlow : (1 + t) * ‖w‖ ≤ ‖z‖ + 1 := by
    calc
      (1 + t) * ‖w‖ = ‖(1 + t) • w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 + t)]
      _ = ‖(1 - e) * (P z + t • w) * e‖ := congrArg norm hcomp.symm
      _ ≤ ‖P z + t • w‖ := norm_two_projection_compression_le _ _ _ he.one_sub he
      _ = ‖P (z + t • φ w)‖ := by rw [map_add, P.map_smul_of_tower, hfix]
      _ ≤ ‖z + t • φ w‖ := hP _
      _ ≤ ‖z‖ + 1 := hnorm
  nlinarith

/-- Retractions preserve the orientation of off-diagonal blocks. -/
theorem tomiyama_offDiagonal (e : B) (he : IsStarProjection e)
    (z : A) (hel : φ e * z = z) (her : z * φ e = 0) :
    P z = e * P z * (1 - e) := by
  have hd₁ := tomiyama_compressed_zero_of_mul_right_zero φ P hP hfix e he z her
  have hqz : φ (1 - e) * z = 0 := by
    rw [map_sub, map_one, sub_mul, one_mul, hel, sub_self]
  have hd₂ := tomiyama_compressed_zero_of_mul_left_zero φ P hP hfix
    (1 - e) he.one_sub z hqz
  have hr := tomiyama_no_reverse_block φ P hP hfix e he z hel her
  have hsplit : P z = e * P z * e + e * P z * (1 - e) +
      (1 - e) * P z * e + (1 - e) * P z * (1 - e) := by noncomm_ring
  simpa only [hd₁, hd₂, hr, zero_add, add_zero] using hsplit

/-- Left multiplication by any projection in the target commutes with the
contractive retraction. -/
theorem tomiyama_map_projection_mul_oai (e : B) (he : IsStarProjection e) (x : A) :
    P (φ e * x) = e * P x := by
  let q := 1 - e
  have hφ : φ e * φ e = φ e := by rw [← map_mul, he.isIdempotentElem.eq]
  have hq : IsStarProjection q := he.one_sub
  have hφq : φ q * φ q = φ q := by rw [← map_mul, hq.isIdempotentElem.eq]
  have heq : φ e * φ q = 0 := by rw [← map_mul, he.mul_one_sub_self, map_zero]
  have hqe : φ q * φ e = 0 := by rw [← map_mul, he.one_sub_mul_self, map_zero]
  let a := P (φ e * x * φ e)
  let b := P (φ e * x * φ q)
  let c := P (φ q * x * φ e)
  let d := P (φ q * x * φ q)
  have ha : e * a = a := by
    have hs := tomiyama_corner_supported φ P hP hfix e he x
    dsimp [a]
    calc
      e * P (φ e * x * φ e) = e * (e * P (φ e * x * φ e) * e) := congrArg (e * ·) hs.symm
      _ = P (φ e * x * φ e) := by rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq, hs]
  have hb : e * b = b := by
    have hs := tomiyama_offDiagonal φ P hP hfix e he (φ e * x * φ q)
      (by rw [← mul_assoc, ← mul_assoc, hφ])
      (by rw [mul_assoc, hqe, mul_zero])
    dsimp [b]
    calc
      e * P (φ e * x * φ q) = e * (e * P (φ e * x * φ q) * q) := congrArg (e * ·) hs
      _ = P (φ e * x * φ q) := by
        rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq]
        exact hs.symm
  have hc : e * c = 0 := by
    have hs := tomiyama_offDiagonal φ P hP hfix q hq (φ q * x * φ e)
      (by rw [← mul_assoc, ← mul_assoc, hφq])
      (by rw [mul_assoc, heq, mul_zero])
    dsimp [c]
    rw [hs]
    change e * (q * P (φ q * x * φ e) * (1 - q)) = 0
    rw [← mul_assoc, ← mul_assoc]
    have heq' : e * q = 0 := he.mul_one_sub_self
    rw [heq', zero_mul, zero_mul]
  have hd : e * d = 0 := by
    have hs := tomiyama_corner_supported φ P hP hfix q hq x
    dsimp [d]
    rw [← hs, ← mul_assoc, ← mul_assoc]
    have heq' : e * q = 0 := he.mul_one_sub_self
    rw [heq', zero_mul, zero_mul]
  have hsplit : x = φ e * x * φ e + φ e * x * φ q +
      φ q * x * φ e + φ q * x * φ q := by
    dsimp [q]
    rw [map_sub, map_one]
    noncomm_ring
  have hPx : P x = a + b + c + d := by rw [hsplit, map_add, map_add, map_add]
  have hleft : φ e * x = φ e * x * φ e + φ e * x * φ q := by
    dsimp [q]
    rw [map_sub, map_one]
    noncomm_ring
  rw [hleft, map_add, hPx, mul_add, mul_add, mul_add, ha, hb, hc, hd, add_zero, add_zero]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.tomiyama_map_projection_mul_oai.{u_1, u_2} := @OAI.KadisonKastler.tomiyama_map_projection_mul_oai.{u_1, u_2}
