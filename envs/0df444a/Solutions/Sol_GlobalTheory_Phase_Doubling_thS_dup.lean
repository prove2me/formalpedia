-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.thS_dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:11.356023+00:00
-- url     : https://prove2.me/submissions/bcf2a407-4164-4f80-971e-1b12134fcf88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
import Theorems.Thm_GlobalTheory_Phase_Doubling_expo_row
import Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_norm_thetaTerm


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
theorem _root_.solution {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin 2 → Fin n × Fin g → ℂ) :
    thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i)) := by
  have s0 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 0 (k, i))
  have s1 := GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm (Fin n) (Fin g) φ h τ hτ
    (fun k i => ζ 1 (k, i))
  unfold thS
  rw [tsum_mul_tsum_of_summable_norm s0 s1, ← (rowEquiv n g).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [Fin.sum_univ_two, expo_row, expo_row, mul_add, Complex.exp_add, dup_apply]
  simp only [rowEquiv, Equiv.coe_fn_mk]
  ring
end GlobalTheory.Phase.Doubling
