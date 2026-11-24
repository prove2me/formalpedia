-- Prove2me | solution 1 for GlobalTheory.SA.eq_zero_of_smul_z_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:52.388795+00:00
-- url     : https://prove2.me/submissions/8ce360eb-877c-4167-99e7-b9120372fd9e

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_form_flag_vector_self
import Theorems.Thm_GlobalTheory_SA_X_le_perp_xPlus

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
theorem _root_.solution (F : FlagD H r) {a : K} (h : a • F.z ∈ F.X) : a = 0 := by
  have h1 := ((mem_perp_xPlus F _).1 (X_le_perp_xPlus F h)).2
  rw [map_smul, LinearMap.smul_apply, form_flag_vector_self, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_right (neg_ne_zero.2 F.hT)
end GlobalTheory.SA
