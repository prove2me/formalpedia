-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:07.552601+00:00
-- url     : https://prove2.me/submissions/c4525e16-2311-47bc-b2f0-9aa09eef0c2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLattice
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Theorems.Thm_GlobalTheory_LatOrb_isIntegral_of_mapsTo_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  first | exact @GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | exact GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | (intros; apply GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice <;> assumption)
end _root_.GlobalTheory.T
