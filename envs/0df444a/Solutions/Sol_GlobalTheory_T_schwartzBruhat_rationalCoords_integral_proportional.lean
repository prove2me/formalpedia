-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_rationalCoords_integral_proportional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:46:15.012872+00:00
-- url     : https://prove2.me/submissions/a67ce88b-1322-4a0b-b12a-882c22fedf66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Theorems.Thm_GlobalTheory_SW_haar_ofQ_proportional


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  first | exact @GlobalTheory.SW.haar_ofQ_proportional | exact GlobalTheory.SW.haar_ofQ_proportional | (intros; apply GlobalTheory.SW.haar_ofQ_proportional <;> assumption)
end _root_.GlobalTheory.T
