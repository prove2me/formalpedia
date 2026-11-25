-- Prove2me | solution 1 for GlobalTheory.T.tendsto_thH_pushZ_atTop_thH_dropF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:30.452133+00:00
-- url     : https://prove2.me/submissions/b9b7675f-1aab-497d-b6b8-c3feb628635b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Theorems.Thm_GlobalTheory_SW_thH_siegel_operator


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
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ), IsSB φ → IsSB (dropF φ) ∧ ∀ Z ∈ Hn Ψ (N + 1), dropZ Ψ Z ∈ Hn Ψ N ∧ (∀ t : ℝ, 0 ≤ t → pushZ Ψ Z (Pi.single 0 1) t ∈ Hn Ψ (N + 1)) ∧ ∀ z z' : CM Ψ n (N + 1), Tendsto (fun t : ℝ => thH Ψ φ (pushZ Ψ Z (Pi.single 0 1) t) z z') atTop (𝓝 (thH Ψ (dropF φ) (dropZ Ψ Z) (fun τ => (z τ).submatrix id Fin.succ) (fun τ => (z' τ).submatrix id Fin.succ))) := by
  first | exact @GlobalTheory.SW.thH_siegel_operator | exact GlobalTheory.SW.thH_siegel_operator | (intros; apply GlobalTheory.SW.thH_siegel_operator <;> assumption)
end _root_.GlobalTheory.T
