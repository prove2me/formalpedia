-- Prove2me | solution 1 for GlobalTheory.T.generalLinear_transitive_on_lattices_over_DVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:39.659471+00:00
-- url     : https://prove2.me/submissions/1d3c1288-45b5-4a39-985e-f757ebb6f433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GeneralLinearTransitiveOnLatticesOverDVR
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_GeneralLinearTransitiveOnLatticesOverDVRStatement
import Theorems.Thm_GlobalTheory_LatHecke_gl_transitive_lattices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatHecke
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ), (∀ L : Lat O K r, ∃ g : GL (Fin r) K, glMap g (std O K r).1 = L.1) ∧ ∀ (g : GL (Fin r) K) (L : Lat O K r), (glMap g L.1).IsLattice K := by
  first | exact @GlobalTheory.LatHecke.gl_transitive_lattices | exact GlobalTheory.LatHecke.gl_transitive_lattices | (intros; apply GlobalTheory.LatHecke.gl_transitive_lattices <;> assumption)
end _root_.GlobalTheory.T
