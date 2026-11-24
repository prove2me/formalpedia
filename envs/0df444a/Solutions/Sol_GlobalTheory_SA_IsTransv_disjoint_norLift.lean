-- Prove2me | solution 1 for GlobalTheory.SA.IsTransv.disjoint_norLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:39.190808+00:00
-- url     : https://prove2.me/submissions/86fd36e5-07c6-4322-9b1c-babbc8f4fe13

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_norLift_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.SA
namespace IsTransv
theorem _root_.solution {F F' : FlagD H r} (h : IsTransv F F') :
    Disjoint (norLift F F') (norLift F' F) := by
  rw [disjoint_iff, norLift_inf]; exact h.2.eq_bot
end IsTransv
end GlobalTheory.SA
