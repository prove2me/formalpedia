-- Prove2me | solution 1 for GlobalTheory.HL.Eichler.eichler_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:30:41.498549+00:00
-- url     : https://prove2.me/submissions/fb782689-6bc6-4ce8-8e76-e820e432ddc0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_l
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_inv
import Theorems.Thm_GlobalTheory_HL_Eichler_eich_isom
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
namespace GlobalTheory.HL.Eichler
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (x u : Fin n → E) (s : E), hf L Hm x x = 0 → hf L Hm u x = 0 → s + L.cj s = hf L Hm u u → ∃ g ∈ isomG L Hm, (∀ v, g v = eich L Hm x u s v) ∧ ∀ v, g⁻¹ v = eich L Hm x (-u) (L.cj s) v := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH x u s hx hu hs
  have h1 := eich_inv L hH.1 x u s hx hu hs
  have h2 := eich_inv L hH.1 x (-u) (L.cj s) hx (by rw [hf_neg_l, hu, neg_zero])
    (by rw [L.cj_cj, hf_neg_l, hf_neg_r, neg_neg, add_comm, hs])
  simp only [neg_neg, L.cj_cj] at h2
  refine ⟨{ eichL L Hm x u s with
      invFun := eich L Hm x (-u) (L.cj s)
      left_inv := h1
      right_inv := h2 }, ?_, fun _ => rfl, fun _ => rfl⟩
  exact fun v w => eich_isom L hH.1 x u s hx hu hs v w
end GlobalTheory.HL.Eichler
