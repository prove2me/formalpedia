-- Prove2me | solution 1 for GlobalTheory.HeckeTwoSum.exists_norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:41.660802+00:00
-- url     : https://prove2.me/submissions/daa9ccc5-96d7-466f-af0e-4035444baf61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeries
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_exists_den
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoSum
theorem _root_.solution (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ν ∈ I, ν ≠ 0 → κ ≤ |((Algebra.norm ℚ ν : ℚ) : ℝ)| := by
  obtain ⟨d, hd, hdI⟩ := GlobalTheory.HeckeTwo.APart.exists_den I
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine ⟨|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)|⁻¹, inv_pos.2 hNd, fun ν hν hν0 => ?_⟩
  obtain ⟨x, hx⟩ := hdI ν hν
  have e1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ ν := by
    rw [Algebra.coe_norm_int, hx, map_mul]
  have hxz : (Algebra.norm ℤ x : ℤ) ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at e1
    have h1 : Algebra.norm ℚ (d : F) ≠ 0 := (Algebra.norm_ne_zero_iff).2 hd'
    have h2 : Algebra.norm ℚ ν ≠ 0 := (Algebra.norm_ne_zero_iff).2 hν0
    exact mul_ne_zero h1 h2 e1.symm
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hxz
  have e2 : ((Algebra.norm ℤ x : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hNd).le
  rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hNd.ne', one_mul] at this
end GlobalTheory.HeckeTwoSum
