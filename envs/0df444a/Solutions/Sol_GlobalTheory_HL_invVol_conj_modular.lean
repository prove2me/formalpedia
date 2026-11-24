-- Prove2me | solution 1 for GlobalTheory.HL.invVol_conj_modular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:43.702962+00:00
-- url     : https://prove2.me/submissions/f539724a-a69a-43c9-b6cc-13da839ef5c7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HaarInvVolumeConjModularCharacter
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {G : Type} [Group G] (H K : Subgroup G), K ≤ H → (∀ h ∈ H, K.relIndex (MulAut.conj h • K) ≠ 0 ∧ (MulAut.conj h • K).relIndex K ≠ 0) → (∀ a ∈ H, ∀ b ∈ H, invVol K (MulAut.conj (a * b) • K) = invVol K (MulAut.conj a • K) * invVol K (MulAut.conj b • K)) ∧ (∀ a ∈ H, 0 < invVol K (MulAut.conj a • K)) ∧ (∀ α : G ≃* G, K.map α.toMonoidHom = K → ∀ a ∈ H, invVol K (MulAut.conj (α a) • K) = invVol K (MulAut.conj a • K)) ∧ ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H, invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' ∧ (MulAut.conj a • K' = K' → invVol K (MulAut.conj a • K) = 1) := by
  intro G _ H K _ hc
  have e : ∀ (g : G) (A B : Subgroup G),
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun g A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have key : ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H,
      invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' := by
    intro K' h1 h2 a ha
    have p1 : K.relIndex (MulAut.conj a • K') ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (hc a ha).1 (by rw [e]; exact h1)
    have p2 : (MulAut.conj a • K').relIndex K ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (by rw [e]; exact h2) (hc a ha).2
    rw [(invVol_mul_pos_le_conj K (MulAut.conj a • K) _ (hc a ha).1 (hc a ha).2 p1 p2).1,
      (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.2.2 a]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [map_mul, mul_smul]
    exact key _ (hc b hb).1 (hc b hb).2 a ha
  · intro a ha
    exact (invVol_mul_pos_le_conj K _ _ (hc a ha).1 (hc a ha).2 (hc a ha).1 (hc a ha).2).2.1
  · intro α hα a _
    have h1 : (MulAut.conj a • K).map α.toMonoidHom
        = MulAut.conj (α a) • K.map α.toMonoidHom := by
      change (K.map (MulAut.conj a).toMonoidHom).map α.toMonoidHom
        = (K.map α.toMonoidHom).map (MulAut.conj (α a)).toMonoidHom
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [hα] at h1
    have f : ∀ A B : Subgroup G,
        (A.map α.toMonoidHom).relIndex (B.map α.toMonoidHom) = A.relIndex B := fun A B =>
      Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom) A B α.injective
    have f1 := f K (MulAut.conj a • K)
    have f2 := f (MulAut.conj a • K) K
    rw [hα, h1] at f1 f2
    rw [invVol, invVol, f1, f2]
  · intro K' h1 h2 a ha
    refine ⟨key K' h1 h2 a ha, fun h => ?_⟩
    have k := key K' h1 h2 a ha
    rw [h] at k
    have pos := (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.1
    exact mul_right_cancel₀ pos.ne' (by rw [← k, one_mul])
end GlobalTheory.HL
