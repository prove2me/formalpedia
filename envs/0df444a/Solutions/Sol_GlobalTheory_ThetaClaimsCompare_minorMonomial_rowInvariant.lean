-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_rowInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:49.001806+00:00
-- url     : https://prove2.me/submissions/271ad5af-135b-46d2-b457-dd6dafc0095d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_rowShift_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (a : T → ℕ → ℕ) : RowInv r n k (minorsP r n col k a) := by
  intro σ i i' hi t
  simp only [minorsP, map_prod, map_pow, rowShift_minor r n k col σ i i' hi t]
end GlobalTheory.ThetaClaimsCompare
