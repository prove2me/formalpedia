-- Prove2me | solution 1 for GlobalTheory.IdxInt.Lin.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:04:45.146588+00:00
-- url     : https://prove2.me/submissions/b66c25d7-a56e-4fd8-9d7b-1dc18275924c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBound
import Theorems.Thm_GlobalTheory_IdxInt_cint_eq_of_fine

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
namespace GlobalTheory.IdxInt.Lin
variable {W : Type} [AddCommGroup W]
open scoped Pointwise Classical in
open Function in
private lemma quotientEquivProdOfLE_mk_fst {W : Type} [AddCommGroup W] {C B : AddSubgroup W}
    (h : C ≤ B) (w : W) : ((AddSubgroup.quotientEquivProdOfLE h) (w : W ⧸ C)).1 = (w : W ⧸ B) :=
  rfl
open scoped Pointwise Classical in
open Function in
private lemma Fine_of_le_of_relIndex_ne_zero {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  have hfin : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hidx
  refine ⟨hCB.trans hBA, hC, fun w b hb => hinv w b (hCB hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
  rw [quotientEquivProdOfLE_mk_fst]
  exact ⟨w, hw, rfl⟩
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma exists_fine_fine_of_nice_nice {W : Type} [AddCommGroup W] {A : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Nice A φ) (hψ : _root_.GlobalTheory.IdxInt.Nice A ψ) :
    ∃ C, _root_.GlobalTheory.IdxInt.Fine A φ C ∧ _root_.GlobalTheory.IdxInt.Fine A ψ C := by
  obtain ⟨B, hB⟩ := hφ
  obtain ⟨B', hB'⟩ := hψ
  have hidx : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1
  exact ⟨B ⊓ B', Fine_of_le_of_relIndex_ne_zero hB inf_le_left hidx, Fine_of_le_of_relIndex_ne_zero hB' inf_le_right hidx⟩
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma Fine_add {W : Type} [AddCommGroup W] {A C : AddSubgroup W} {φ ψ : W → ℂ}
    (hφ : _root_.GlobalTheory.IdxInt.Fine A φ C) (hψ : _root_.GlobalTheory.IdxInt.Fine A ψ C) :
    _root_.GlobalTheory.IdxInt.Fine A (φ + ψ) C := by
  refine ⟨hφ.1, hφ.2.1, fun w b hb => by simp only [Pi.add_apply, hφ.2.2.1 w b hb, hψ.2.2.1 w b hb], ?_⟩
  refine (hφ.2.2.2.union hψ.2.2.2).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  rcases Function.support_add φ ψ hw with h | h
  · exact Or.inl ⟨w, h, rfl⟩
  · exact Or.inr ⟨w, h, rfl⟩
open scoped Pointwise Classical in
open Function in
private lemma finite_support_quotient_out_of_finite_image {W : Type} [AddCommGroup W] {B : AddSubgroup W} (φ : W → ℂ)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    (support fun c : W ⧸ B => φ (Quotient.out c)).Finite := by
  refine hφ.subset fun c hc => ⟨Quotient.out c, hc, QuotientAddGroup.out_eq' c⟩
end GlobalTheory.IdxInt.Lin
end

set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Lin
variable {W : Type} [AddCommGroup W]
open scoped Pointwise Classical
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Lin
namespace _root_.GlobalTheory.IdxInt.Lin
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A (fun w => c * φ w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => c * φ w) = c * _root_.GlobalTheory.IdxInt.cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).re ∧ (_root_.GlobalTheory.IdxInt.cint A (_root_.GlobalTheory.IdxInt.ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, _root_.GlobalTheory.IdxInt.Nice A (φ i)) → _root_.GlobalTheory.IdxInt.Nice A (fun w => ∑ i ∈ s, φ i w) ∧ _root_.GlobalTheory.IdxInt.cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, _root_.GlobalTheory.IdxInt.cint A (φ i) := by
  intro W _ A
  have hadd : ∀ φ ψ : W → ℂ, _root_.GlobalTheory.IdxInt.Nice A φ → _root_.GlobalTheory.IdxInt.Nice A ψ → _root_.GlobalTheory.IdxInt.Nice A (φ + ψ) ∧ _root_.GlobalTheory.IdxInt.cint A (φ + ψ) = _root_.GlobalTheory.IdxInt.cint A φ + _root_.GlobalTheory.IdxInt.cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖_root_.GlobalTheory.IdxInt.cint A φ‖ ≤ (_root_.GlobalTheory.IdxInt.cint A ψ).re) := by
    intro φ ψ hφ hψ
    obtain ⟨C, hφC, hψC⟩ := exists_fine_fine_of_nice_nice hφ hψ
    have hsum := Fine_add hφC hψC
    have hfφ := finite_support_quotient_out_of_finite_image φ hφC.2.2.2
    have hfψ := finite_support_quotient_out_of_finite_image ψ hψC.2.2.2
    refine ⟨⟨C, hsum⟩, ?_, fun hle => ?_⟩
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hsum, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC,
        _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC, ← add_div]
      simp only [Pi.add_apply]
      rw [finsum_add_distrib hfφ hfψ]
    · rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hφC, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A C _ hψC,
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        finsum_eq_sum_of_support_subset (s := (hfφ.union hfψ).toFinset) _ (by simp),
        norm_div, Complex.norm_natCast, Complex.div_natCast_re, Complex.re_sum]
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hle _)
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c φ hφ
    obtain ⟨B, hB⟩ := hφ
    have hc : _root_.GlobalTheory.IdxInt.Fine A (fun w => c * φ w) B :=
      ⟨hB.1, hB.2.1, fun w b hb => by simp only [hB.2.2.1 w b hb],
        hB.2.2.2.subset (Set.image_mono (Function.support_mul_subset_right _ _))⟩
    refine ⟨⟨B, hc⟩, ?_⟩
    rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hc, _root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
      ← mul_finsum, mul_div_assoc]
  · intro P
    by_cases h : _root_.GlobalTheory.IdxInt.Nice A (_root_.GlobalTheory.IdxInt.ind P)
    · obtain ⟨B, hB⟩ := h
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B _ hB,
        finsum_eq_sum _ (finite_support_quotient_out_of_finite_image _ hB.2.2.2), Complex.div_natCast_re, Complex.div_natCast_im,
        Complex.re_sum, Complex.im_sum]
      refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _), ?_⟩
      · unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
      · rw [Finset.sum_eq_zero fun i _ => ?_, zero_div]
        unfold _root_.GlobalTheory.IdxInt.ind
        split_ifs <;> simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dif_neg h]
      simp
  · intro ι s φ hs
    induction s using Finset.induction_on with
    | empty =>
      have h0 : _root_.GlobalTheory.IdxInt.Fine A (fun _ : W => (0 : ℂ)) A :=
        ⟨le_rfl, by simp [AddSubgroup.relIndex_self], fun _ _ _ => rfl, by simp⟩
      simp only [Finset.sum_empty]
      refine ⟨⟨A, h0⟩, ?_⟩
      rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A A _ h0]
      simp
    | insert i s hi ih =>
      have hi' := hs i (Finset.mem_insert_self i s)
      have ih' := ih fun j hj => hs j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      obtain ⟨hn, he, -⟩ := hadd (φ i) (fun w => ∑ j ∈ s, φ j w) hi' ih'.1
      exact ⟨hn, he.trans (by rw [ih'.2])⟩
end _root_.GlobalTheory.IdxInt.Lin
end GlobalTheory.IdxInt.Lin
