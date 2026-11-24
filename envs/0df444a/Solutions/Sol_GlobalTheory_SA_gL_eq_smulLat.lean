-- Prove2me | solution 1 for GlobalTheory.SA.gL_eq_smulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:32.806128+00:00
-- url     : https://prove2.me/submissions/ee9d008c-2335-42d4-8f3f-7f9641bbfca5

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_mem_smulLat
import Theorems.Thm_GlobalTheory_SA_int_smul_eq
import Theorems.Thm_GlobalTheory_SA_mem_gL


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
theorem _root_.solution {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (g : ℕ) :
    gL Λ g = smulLat (g : NumberField.RingOfIntegers E) Λ := by
  ext x
  rw [mem_gL, mem_smulLat]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [int_smul_eq]
  rfl
end GlobalTheory.SA
