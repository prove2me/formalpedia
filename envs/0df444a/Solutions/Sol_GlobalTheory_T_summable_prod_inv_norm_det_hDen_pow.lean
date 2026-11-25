-- Prove2me | solution 1 for GlobalTheory.T.summable_prod_inv_norm_det_hDen_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:14.630817+00:00
-- url     : https://prove2.me/submissions/c3191358-a0ab-4582-9e28-eab4fb27c21b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Theorems.Thm_GlobalTheory_SW_summable_eis_majorant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), 4 * N < n → ∀ (c : ℕ) (rep : Lag E N → M2 E N), 0 < c → (∀ U, rep U ∈ UU E N ∧ Den c (rep U) ∧ botSpan (rep U) = U.1) → Summable fun U : Lag E N => ∏ τ : Ψ, (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ := by
  first | exact @GlobalTheory.SW.summable_eis_majorant | exact GlobalTheory.SW.summable_eis_majorant | (intros; apply GlobalTheory.SW.summable_eis_majorant <;> assumption)
end _root_.GlobalTheory.T
