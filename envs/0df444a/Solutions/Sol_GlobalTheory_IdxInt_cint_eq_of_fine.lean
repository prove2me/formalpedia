-- Prove2me | solution 1 for GlobalTheory.IdxInt.cint_eq_of_fine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:32:37.214367+00:00
-- url     : https://prove2.me/submissions/ff38d5da-cfca-45c3-876e-a38fe3793f5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
namespace GlobalTheory.IdxInt
open scoped Pointwise Classical in
open Function in
private lemma quotientEquivProdOfLE_apply_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (h : C ≤ B)
    (c : W ⧸ C) : ((AddSubgroup.quotientEquivProdOfLE h) c).1 = ((Quotient.out c : W) : W ⧸ B) := by
  conv_lhs => rw [← QuotientAddGroup.out_eq' c]
  rfl
open scoped Pointwise Classical in
open Function in
private lemma finsum_prod_fst_eq_card_mul {X Y : Type} [Finite Y] (g : X → ℂ) (hg : (support g).Finite) :
    ∑ᶠ p : X × Y, g p.1 = (Nat.card Y : ℂ) * ∑ᶠ x, g x := by
  have := Fintype.ofFinite Y
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ),
    finsum_eq_sum_of_support_subset (s := hg.toFinset), Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    show ∑ _y : Y, g x = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro x hx
    simpa using hx
  · intro p hp
    simpa using hp
open scoped Pointwise Classical in
open Function in
private lemma support_quotient_out_finite_of_image_finite {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩
open scoped Pointwise Classical in
open Function in
private lemma finsum_quotient_out_eq_relIndex_mul_of_le {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (hCB : C ≤ B)
    (hidx : C.relIndex B ≠ 0) (φ : W → ℂ) (hinv : ∀ w b : W, b ∈ B → φ (w + b) = φ w)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    ∑ᶠ c : W ⧸ C, φ (Quotient.out c) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  have hcls : ∀ c : W ⧸ C, φ (Quotient.out c) =
      φ (Quotient.out ((AddSubgroup.quotientEquivProdOfLE hCB) c).1) := by
    intro c
    rw [quotientEquivProdOfLE_apply_fst]
    obtain ⟨b, hb⟩ : ∃ b ∈ B, Quotient.out ((Quotient.out c : W) : W ⧸ B) = Quotient.out c + b := by
      refine ⟨-(Quotient.out c) + Quotient.out ((Quotient.out c : W) : W ⧸ B), ?_, by abel⟩
      exact QuotientAddGroup.leftRel_apply.mp (Quotient.exact' (QuotientAddGroup.out_eq' _).symm)
    rw [hb.2, hinv _ _ hb.1]
  rw [finsum_congr hcls, finsum_comp_equiv (AddSubgroup.quotientEquivProdOfLE hCB)
      (f := fun p => φ (Quotient.out p.1)), finsum_prod_fst_eq_card_mul _ (support_quotient_out_finite_of_image_finite φ hφ)]
  rfl
open scoped Pointwise Classical in
open Function in
private lemma finsum_out_div_relIndex_eq_of_le {W : Type} [AddCommGroup W] {A B C : AddSubgroup W}
    {φ : W → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) / (C.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  rw [finsum_quotient_out_eq_relIndex_mul_of_le hCB hidx φ hinv hsupp, ← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA,
    Nat.cast_mul, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hidx)]
end GlobalTheory.IdxInt
end

set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt
open scoped Pointwise Classical
open Function
namespace GlobalTheory.IdxInt
namespace _root_.GlobalTheory.IdxInt
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ),
    _root_.GlobalTheory.IdxInt.Fine A φ B → _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  intro W _ A B φ hB
  have h : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dif_pos h]
  have hB0 := h.choose_spec
  have hidx : (B ⊓ h.choose).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB0.2.1
  rw [← finsum_out_div_relIndex_eq_of_le hB0 inf_le_right hidx, finsum_out_div_relIndex_eq_of_le hB inf_le_left hidx]
end _root_.GlobalTheory.IdxInt
end GlobalTheory.IdxInt
