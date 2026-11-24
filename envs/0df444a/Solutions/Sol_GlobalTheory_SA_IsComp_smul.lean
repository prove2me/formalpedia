-- Prove2me | solution 1 for GlobalTheory.SA.IsComp.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:22.92644+00:00
-- url     : https://prove2.me/submissions/0b7353c5-3118-4ced-b11f-79c27f823feb

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
namespace IsComp
theorem _root_.solution {F F' : FlagD H r} {u : V} {a a' : K} (h : IsComp F F' u a a') (c : K) :
    IsComp F F' (c • u) (c * a) (c * a') := by
  unfold IsComp at *
  convert Submodule.smul_mem _ c h using 1
  rw [smul_sub, smul_sub, mul_smul, mul_smul]
end IsComp
end GlobalTheory.SA
