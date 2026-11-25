-- Prove2me | solution 1 for GlobalTheory.HL.Model.eich_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:45.901402+00:00
-- url     : https://prove2.me/submissions/c5dd2392-e4dc-4a87-9c78-9e51c2c391ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_sub_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_sub_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_symm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (L : LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E} (h : IsHerm L H)
    (x u : Fin n → E) (s : E) (hxx : hf L H x x = 0) (hux : hf L H u x = 0)
    (hs : s + L.cj s = hf L H u u) (v w : Fin n → E) :
    hf L H (eich L H x u s v) (eich L H x u s w) = hf L H v w := by
  have hxu : hf L H x u = 0 := by rw [hf_symm L h u x, hux, map_zero]
  have hxw : hf L H x w = L.cj (hf L H w x) := hf_symm L h w x
  have huw : hf L H u w = L.cj (hf L H w u) := hf_symm L h w u
  simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hf_add_right, hf_sub_right,
    hf_smul_right, hxx, hux, hxu, hxw, huw]
  linear_combination (-(hf L H v x * L.cj (hf L H w x))) * hs
end GlobalTheory.HL.Model
