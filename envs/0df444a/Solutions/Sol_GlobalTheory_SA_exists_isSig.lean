-- Prove2me | solution 1 for GlobalTheory.SA.exists_isSig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:28.658376+00:00
-- url     : https://prove2.me/submissions/128d5c39-c9df-49fe-8caa-bb180d5861b0

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_exists_isComp_iff

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
theorem _root_.solution {F F' : FlagD H r} {y y' : V} (hy : y ∈ norLift F F') (hy' : y' ∈ norLift F' F) :
    ∃ a a', IsSig F F' y y' a a' := by
  obtain ⟨a, a', h⟩ := (exists_isComp_iff F F' (y - y')).2 (sub_mem hy.1 (jointSpan_comm F F' ▸ hy'.1))
  exact ⟨a, a', hy, hy', h⟩
end GlobalTheory.SA
