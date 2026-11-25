-- Prove2me | solution 1 for GlobalTheory.HL.Model.eich_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:44:41.102659+00:00
-- url     : https://prove2.me/submissions/29fd17e3-deca-4610-91f9-c37e44b87526

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_sub_left
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_left
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
    (hs : s + L.cj s = hf L H u u) (v : Fin n → E) :
    eich L H x (-u) (L.cj s) (eich L H x u s v) = v := by
  have hxu : hf L H x u = 0 := by rw [hf_symm L h u x, hux, map_zero]
  have hneg : hf L H (eich L H x u s v) (-u) = -hf L H (eich L H x u s v) u := by
    simp [hf, map_neg, Finset.sum_neg_distrib]
  have h1 : hf L H (eich L H x u s v) x = hf L H v x := by
    simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hxx, hux]
    ring
  have h2 : hf L H (eich L H x u s v) u = hf L H v u - hf L H v x * hf L H u u := by
    simp only [eich, hf_add_left, hf_sub_left, hf_smul_left, hxu]
    ring
  have e : eich L H x (-u) (L.cj s) (eich L H x u s v) = eich L H x u s v +
      hf L H (eich L H x u s v) (-u) • x - hf L H (eich L H x u s v) x • (-u + L.cj s • x) := rfl
  rw [e, hneg, h1, h2]
  funext i
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (-(hf L H v x * x i)) * hs
end GlobalTheory.HL.Model
