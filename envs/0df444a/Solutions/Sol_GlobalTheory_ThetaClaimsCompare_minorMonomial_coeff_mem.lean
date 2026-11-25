-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:00.702558+00:00
-- url     : https://prove2.me/submissions/bbe306ae-cfff-41f0-bebe-d619f3f9b1e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_map

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
theorem _root_.solution (a : T → ℕ → ℕ) (O : Subring k) (m : Letter T r n →₀ ℕ) :
    (minorsP r n col k a).coeff m ∈ O := by
  rw [← minorMonomial_map, coeff_map]
  exact intCast_mem O _
end GlobalTheory.ThetaClaimsCompare
