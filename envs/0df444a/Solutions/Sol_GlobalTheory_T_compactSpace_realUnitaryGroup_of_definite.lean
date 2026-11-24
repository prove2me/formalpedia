-- Prove2me | solution 1 for GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:05:39.62717+00:00
-- url     : https://prove2.me/submissions/06a58ef1-015a-436d-8d71-a427aa8f9911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefiniteStatement
import Theorems.Thm_GlobalTheory_FinCovol_compactSpace_unitary_of_definite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  first | exact @GlobalTheory.FinCovol.compactSpace_unitary_of_definite | exact GlobalTheory.FinCovol.compactSpace_unitary_of_definite | (intros; apply GlobalTheory.FinCovol.compactSpace_unitary_of_definite <;> assumption)
end _root_.GlobalTheory.T
