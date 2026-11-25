-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.cont_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:58:54.742439+00:00
-- url     : https://prove2.me/submissions/e820c29d-ab48-4e80-bf97-cb356a4cba62

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_cont_eq
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
namespace GlobalTheory.HL.ContModel
theorem _root_.solution {W : Type} [AddCommGroup W] {W0 A : AddSubgroup W}
    (h1 : A.relIndex W0 ≠ 0) (h2 : W0.relIndex A ≠ 0) : cont W0 (A : Set W) = relVol W0 A := by
  have him : (QuotientAddGroup.mk : W → W ⧸ A) '' (A : Set W) = {0} := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff x).2 hx
    · rintro rfl
      exact ⟨0, A.zero_mem, rfl⟩
  have hg : GoodSub W0 A (A : Set W) :=
    ⟨h1, h2, fun x hx a ha => A.add_mem hx ha, by rw [him]; exact Set.finite_singleton _⟩
  rw [cont_eq hg, him]
  simp
end GlobalTheory.HL.ContModel
