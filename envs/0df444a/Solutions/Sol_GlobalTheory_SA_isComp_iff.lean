-- Prove2me | solution 1 for GlobalTheory.SA.isComp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:10.995327+00:00
-- url     : https://prove2.me/submissions/ccaeebd2-79e1-4f80-bef1-0238965f9cae

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
theorem _root_.solution (F F' : FlagD H r) (u : V) (a a' : K) :
    IsComp F F' u a a' ↔ ∃ ξ ∈ F.X, ∃ ξ' ∈ F'.X, u = ξ + a • F.z + ξ' + a' • F'.z := by
  rw [IsComp, Submodule.mem_sup]
  refine exists_congr fun ξ => and_congr_right fun _ => exists_congr fun ξ' => and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [add_right_comm ξ, h]; abel
  · rintro rfl; abel
end GlobalTheory.SA
