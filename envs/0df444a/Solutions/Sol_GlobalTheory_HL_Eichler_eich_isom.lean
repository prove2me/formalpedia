-- Prove2me | solution 1 for GlobalTheory.HL.Eichler.eich_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:54.061304+00:00
-- url     : https://prove2.me/submissions/61c96b4c-d5bf-4cd5-85d4-b15009b9b1fc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.Eichler
theorem _root_.solution {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (x u : Fin n → E) (s : E)
    (hx : hf L Hm x x = 0) (hu : hf L Hm u x = 0) (hs : s + L.cj s = hf L Hm u u) (v w : Fin n → E) :
    hf L Hm (eich L Hm x u s v) (eich L Hm x u s w) = hf L Hm v w := by
  have hu' : hf L Hm x u = 0 := by rw [← hf_cj L h, hu, map_zero]
  simp only [eich, hf_add_l, hf_sub_l, hf_smul_l, hf_add_r, hf_sub_r, hf_smul_r, hx, hu, hu', ← hs,
    hf_cj L h]
  ring
end GlobalTheory.HL.Eichler
