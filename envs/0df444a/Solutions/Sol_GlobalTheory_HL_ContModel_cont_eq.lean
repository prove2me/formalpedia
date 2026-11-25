-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.cont_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:41.406593+00:00
-- url     : https://prove2.me/submissions/ab77b8a1-1238-4697-9191-1942bffc53c3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Theorems.Thm_GlobalTheory_HL_ContModel_relVol_of_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.ContModel
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
private theorem ncard_image_mk_eq_mul_relIndex_of_le {W : Type} [AddCommGroup W] {A B : AddSubgroup W} (h : B ≤ A)
    {S : Set W} (hS : ∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) :
    ((QuotientAddGroup.mk : W → W ⧸ B) '' S).ncard =
      ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard * B.relIndex A := by
  set Ab : AddSubgroup (W ⧸ B) := A.map (QuotientAddGroup.mk' B) with hAb
  set T : Set ((W ⧸ B) ⧸ Ab) :=
    (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) '' ((QuotientAddGroup.mk : W → W ⧸ B) '' S) with hT
  have hpre : (QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T =
      (QuotientAddGroup.mk : W → W ⧸ B) '' S := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hz⟩
      induction y using QuotientAddGroup.induction_on with
      | H w =>
        rw [QuotientAddGroup.eq, hAb, AddSubgroup.mem_map] at hz
        obtain ⟨a, ha, hax⟩ := hz
        have hax' : ((a : W) : W ⧸ B) = -((x : W) : W ⧸ B) + (w : W ⧸ B) := hax
        refine ⟨x + a, hS x hx a ha, ?_⟩
        rw [QuotientAddGroup.mk_add, hax']
        abel
    · intro hy
      exact ⟨y, hy, rfl⟩
  have e1 : Nat.card ((QuotientAddGroup.mk : W ⧸ B → (W ⧸ B) ⧸ Ab) ⁻¹' T) = Nat.card Ab * Nat.card T :=
    (Nat.card_congr (QuotientAddGroup.preimageMkEquivAddSubgroupProdSet Ab T)).trans (Nat.card_prod _ _)
  have e2 : Nat.card Ab = B.relIndex A := by
    rw [hAb, ← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
      QuotientAddGroup.ker_mk']
  have e3 : ((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard = T.ncard := by
    rw [← Set.ncard_image_of_injective T (QuotientAddGroup.quotientQuotientEquivQuotient B A h).injective]
    congr 1
    rw [hT, Set.image_image, Set.image_image]
    rfl
  rw [← hpre, ← Nat.card_coe_set_eq, e1, e2, e3, Nat.card_coe_set_eq, mul_comm]
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
end GlobalTheory.HL.ContModel
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
open ValuativeRel
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.ContModel
namespace _root_.GlobalTheory.HL.ContModel
theorem _root_.solution {W : Type} [AddCommGroup W]
    {W0 A : AddSubgroup W} {S : Set W} (hA : _root_.GlobalTheory.HL.GoodSub W0 A S) :
    _root_.GlobalTheory.HL.cont W0 S =
      (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * _root_.GlobalTheory.HL.relVol W0 A := by
  have hS : _root_.GlobalTheory.HL.IsCO W0 S := ⟨A, hA⟩
  rw [_root_.GlobalTheory.HL.cont, dif_pos hS]
  have hA' : _root_.GlobalTheory.HL.GoodSub W0 hS.choose S := hS.choose_spec
  have hB : (A ⊓ hS.choose).relIndex W0 ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hA.1 hA'.1
  rw [_root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hB,
    _root_.GlobalTheory.HL.ContModel.relVol_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hB,
    ← mul_assoc, ← mul_assoc]
  congr 1
  exact_mod_cast (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_right : A ⊓ hS.choose ≤ hS.choose) hA'.2.2.1).symm.trans
    (ncard_image_mk_eq_mul_relIndex_of_le (inf_le_left : A ⊓ hS.choose ≤ A) hA.2.2.1)
end _root_.GlobalTheory.HL.ContModel
end GlobalTheory.HL.ContModel
