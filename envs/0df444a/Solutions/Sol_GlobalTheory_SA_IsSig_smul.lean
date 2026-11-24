-- Prove2me | solution 1 for GlobalTheory.SA.IsSig.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:22.774083+00:00
-- url     : https://prove2.me/submissions/cc313a53-46d0-4213-bbe2-403e124ffb9b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_IsComp_smul

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
namespace IsSig
theorem _root_.solution {F F' : FlagD H r} {y y' : V} {a a' : K} (h : IsSig F F' y y' a a') (c : K) :
    IsSig F F' (c • y) (c • y') (c * a) (c * a') :=
  ⟨Submodule.smul_mem _ c h.1, Submodule.smul_mem _ c h.2.1, by rw [← smul_sub]; exact h.2.2.smul c⟩
end IsSig
end GlobalTheory.SA
