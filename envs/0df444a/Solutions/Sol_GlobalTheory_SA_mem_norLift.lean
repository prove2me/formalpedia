-- Prove2me | solution 1 for GlobalTheory.SA.mem_norLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:10:24.503399+00:00
-- url     : https://prove2.me/submissions/6d174cf5-9b74-4597-976e-d5c1d8c9aadb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre

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
theorem _root_.solution (F F' : FlagD H r) (y : V) :
    y ∈ norLift F F' ↔ y ∈ V0 F F' ∧ y ∈ perp H (xPlus F) := Iff.rfl
end GlobalTheory.SA
