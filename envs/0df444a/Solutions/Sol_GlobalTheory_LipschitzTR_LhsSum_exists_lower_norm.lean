-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.LhsSum.exists_lower_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:19:50.346681+00:00
-- url     : https://prove2.me/submissions/009b5965-1e89-427b-ade8-f1e43c519802

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Theorems.Thm_GlobalTheory_LipschitzTR_LhsSum_one_le_abs_prod_int
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
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LipschitzTR.LhsSum
theorem _root_.solution [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a ∈ M, a ≠ 0 → ν ≤ |∏ τ : F →+* ℝ, τ a| := by
  obtain ⟨d, hd, hint⟩ := M.isFractional
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hP : 0 < |∏ τ : F →+* ℝ, τ (d : F)| :=
    abs_pos.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero τ).2 hd0)
  refine ⟨1 / |∏ τ : F →+* ℝ, τ (d : F)|, by positivity, fun a ha ha0 => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : F) = (d : F) * a := by
    rw [← Algebra.smul_def]; exact hy
  have hy0 : y ≠ 0 := by
    intro h; apply mul_ne_zero hd0 ha0; rw [← hy', h]; simp
  have h1 := one_le_abs_prod_int y hy0
  rw [hy'] at h1
  simp only [map_mul, Finset.prod_mul_distrib, abs_mul] at h1
  rw [div_le_iff₀ hP]
  linarith [mul_comm (|∏ τ : F →+* ℝ, τ (d : F)|) (|∏ τ : F →+* ℝ, τ a|)]
end GlobalTheory.LipschitzTR.LhsSum
