-- Prove2me | solution 1 for GlobalTheory.T.isHeat_thH_of_isSB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:29.324205+00:00
-- url     : https://prove2.me/submissions/af9cfa2c-2031-4fd0-ac06-6fb7ea5fa4a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThHStatement
import Theorems.Thm_GlobalTheory_SW_isHeat_thH


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  first | exact @GlobalTheory.SW.isHeat_thH | exact GlobalTheory.SW.isHeat_thH | (intros; apply GlobalTheory.SW.isHeat_thH <;> assumption)
end _root_.GlobalTheory.T
