-- Prove2me | solution 1 for GlobalTheory.SA.isUnimod_ofHSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:13.55137+00:00
-- url     : https://prove2.me/submissions/454f8d18-9b25-40c8-a0a8-693db899f47e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_HermLat_isUnimod_iff


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
namespace GlobalTheory.SA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (Λ : Submodule (NumberField.RingOfIntegers E) S.V) :
    IsUnimod (ofHSpace S) Λ ↔ Submodule.IsLattice E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ :=
  isUnimod_iff _ _
end GlobalTheory.SA
