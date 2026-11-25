-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.sigMass_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:49:36.676664+00:00
-- url     : https://prove2.me/submissions/5231fddf-ddda-4d2b-b958-6ad2c864f997

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_smul_inf_of_fix
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (Λ0 Mh : Submodule L.O (Fin n → E)) :
    sigMass L Hm ⊤ Λ0 Mh = if IsSD L Hm Mh then 1 else 0 := by
  have hb : fixG L Hm ⊤ = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨_, _, h2⟩
    rw [Subgroup.mem_bot]
    ext v i
    have : g v = v := sub_eq_zero.1 (by simpa using h2 v trivial)
    simp [this]
  have hv : ∀ Λ, invVol (fixG L Hm ⊤ ⊓ stabL L Λ0) (fixG L Hm ⊤ ⊓ stabL L Λ) = 1 := by
    intro Λ
    rw [hb]; simp [invVol]
  have hout : ∀ Λ : Submodule L.O (Fin n → E),
      (Quotient.mk _ Λ : MulAction.orbitRel.Quotient (fixG L Hm ⊤) (Submodule L.O (Fin n → E))).out = Λ := by
    intro Λ
    have h := Quotient.mk_out (s := MulAction.orbitRel (fixG L Hm ⊤) (Submodule L.O (Fin n → E))) Λ
    obtain ⟨g, hg⟩ := h
    have := smul_inf_of_fix L Hm ⊤ g Λ
    simp only [Submodule.restrictScalars_top, inf_top_eq] at this
    exact hg.symm.trans this
  unfold sigMass
  rw [tsum_eq_single (Quotient.mk _ Mh)]
  · rw [hout, hv]; simp
  · intro o ho
    rw [if_neg]
    rintro ⟨_, h⟩
    apply ho
    simp only [Submodule.restrictScalars_top, inf_top_eq] at h
    rw [← h, Quotient.out_eq]
end GlobalTheory.HL.ContModel
