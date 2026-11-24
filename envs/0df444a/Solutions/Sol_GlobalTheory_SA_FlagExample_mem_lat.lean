-- Prove2me | solution 1 for GlobalTheory.SA.FlagExample.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:21.260573+00:00
-- url     : https://prove2.me/submissions/8473f7e3-2c82-49e3-80c0-eb3ae470c924

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
open GlobalTheory.SA.FlagExample
open NumberField Formalism.BasicNotions.Examples₂
variable (E : Type) [Field E] [NumberField E] [StarRing E]
namespace GlobalTheory.SA.FlagExample
theorem _root_.solution (x : (wittSpace E 2 1).V) :
    x ∈ (wittSpace E 2 1).L0 ↔ ∀ i, co E x i ∈ Set.range (algebraMap (𝓞 E) E) :=
  (Pi.basisFun E (Fin 5)).mem_span_iff_repr_mem (𝓞 E) (co E x)
end GlobalTheory.SA.FlagExample
