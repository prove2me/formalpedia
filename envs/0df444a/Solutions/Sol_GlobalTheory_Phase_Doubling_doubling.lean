-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.doubling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:52:00.836793+00:00
-- url     : https://prove2.me/submissions/955e8918-e7b1-4c62-a1e4-7b8150882eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
import Theorems.Thm_GlobalTheory_Phase_Doubling_isSB_dup
import Theorems.Thm_GlobalTheory_Phase_Doubling_pv_dup
import Theorems.Thm_GlobalTheory_Phase_Doubling_blk_siegel
import Theorems.Thm_GlobalTheory_Phase_Doubling_blk_inv
import Theorems.Thm_GlobalTheory_Phase_Doubling_thS_dup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
namespace GlobalTheory.Phase.Doubling
theorem _root_.solution : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  intro n g φ
  refine ⟨pv_dup, fun h h' => h ?_, isSB_dup, fun u => ?_, fun τ hτ =>
    ⟨blk_siegel hτ, fun h ζ => thS_dup h hτ ζ, blk_inv τ⟩⟩
  · funext a
    have := congrFun h' (glue a a)
    rw [dup_apply, rowM_glue_zero, rowM_glue_one] at this
    exact mul_self_eq_zero.1 this
  · funext x
    simp only [dup_apply, Pi.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.Phase.Doubling
