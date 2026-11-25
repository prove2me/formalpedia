-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:56.275854+00:00
-- url     : https://prove2.me/submissions/e1a331f5-0d20-4094-97cc-e58397257e3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos

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
theorem _root_.solution (a : T → ℕ → ℕ) :
    MvPolynomial.map (Int.castRingHom k) (minorsP r n col ℤ a) = minorsP r n col k a := by
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 i j
  simp
end GlobalTheory.ThetaClaimsCompare
