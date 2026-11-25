-- Prove2me | solution 1 for GlobalTheory.IdxInt.Transport.cint_map_and_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:00.108564+00:00
-- url     : https://prove2.me/submissions/783a7e9a-893e-442e-a167-de6f5cfd6b8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
namespace GlobalTheory.IdxInt.Transport
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma apply_out_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hφ : ∀ w b, b ∈ B → φ (w + b) = φ w) (y : W) :
    φ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) = φ y := by
  have h : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) : W ⧸ B) =
      QuotientAddGroup.mk y := Quotient.out_eq _
  rw [QuotientAddGroup.eq] at h
  have := hφ (Quotient.out (QuotientAddGroup.mk y : W ⧸ B)) _ h
  rw [add_neg_cancel_left] at this
  exact this.symm
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_map_addEquiv_and_finsum_eq (e : W ≃+ W') {A B : AddSubgroup W}
    {φ : W' → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A (fun w => φ (e w)) B) :
    _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom) φ (B.map e.toAddMonoidHom) ∧
      (∑ᶠ c : W' ⧸ B.map e.toAddMonoidHom, φ (Quotient.out c)) =
        ∑ᶠ c : W ⧸ B, φ (e (Quotient.out c)) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  have hφ' : ∀ w b, b ∈ B.map e.toAddMonoidHom → φ (w + b) = φ w := by
    rintro w _ ⟨b, hb, rfl⟩
    have := hφ (e.symm w) b hb
    simpa using this
  let q : W ⧸ B ≃+ W' ⧸ B.map e.toAddMonoidHom := QuotientAddGroup.congr _ _ e rfl
  have hq : ∀ y : W, q (QuotientAddGroup.mk y) = QuotientAddGroup.mk (e y) := fun _ => rfl
  refine ⟨⟨AddSubgroup.map_mono hBA, ?_, hφ', ?_⟩, ?_⟩
  · rw [AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hBi
  · refine (hsupp.image q).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨QuotientAddGroup.mk (e.symm y), ⟨e.symm y, by simpa using hy, rfl⟩, ?_⟩
    rw [hq, AddEquiv.apply_symm_apply]
  · rw [← finsum_comp_equiv q.toEquiv]
    refine finsum_congr fun c => ?_
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    change φ (Quotient.out (q (QuotientAddGroup.mk y))) = _
    rw [hq, apply_out_mk_eq_of_invariant hφ', apply_out_mk_eq_of_invariant (φ := fun w => φ (e w)) hφ]
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma map_symm_map_addEquiv (e : W ≃+ W') (A : AddSubgroup W) :
    (A.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = A := by
  ext x
  simp
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_of_le_and_finsum_eq_relIndex_mul {A B C : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex B ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ C ∧
      (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) =
        (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  obtain ⟨hBA, hBi, hφ, hsupp⟩ := hB
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hC
  let e := AddSubgroup.quotientEquivProdOfLE hCB
  have he : ∀ y : W, (e (QuotientAddGroup.mk y)).1 = QuotientAddGroup.mk y := fun _ => rfl
  have hφC : ∀ w b, b ∈ C → φ (w + b) = φ w := fun w b hb => hφ w b (hCB hb)
  have hcomp : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [he, apply_out_mk_eq_of_invariant hφC, apply_out_mk_eq_of_invariant hφ]
  set T : Set (W ⧸ B) := (fun w : W => (w : W ⧸ B)) '' Function.support φ with hT
  have hgT : Function.support (fun c : W ⧸ B => φ (Quotient.out c)) ⊆ T := by
    intro c hc
    refine ⟨Quotient.out c, hc, ?_⟩
    exact Quotient.out_eq c
  refine ⟨⟨hCB.trans hBA, ?_, hφC, ?_⟩, ?_⟩
  · rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA]
    exact mul_ne_zero hC hBi
  · refine ((hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
      e.injective.injOn).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨?_, Set.mem_univ _⟩
    rw [he]
    exact ⟨y, hy, rfl⟩
  · rw [finsum_congr hcomp,
      finsum_comp_equiv e (f := fun p : (W ⧸ B) × (B ⧸ C.addSubgroupOf B) => φ (Quotient.out p.1))]
    rw [finsum_curry _ ?_]
    · haveI := Fintype.ofFinite (B ⧸ C.addSubgroupOf B)
      simp only [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [mul_finsum]
      congr 1
      funext a
      rw [AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    · exact (hsupp.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).subset
        fun p hp => ⟨hgT hp, Set.mem_univ _⟩
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma finsum_out_div_relIndex_eq_inf_of_fine {A B₁ B₂ : AddSubgroup W} {φ : W → ℂ}
    (h₁ : _root_.GlobalTheory.IdxInt.Fine A φ B₁) (h₂ : _root_.GlobalTheory.IdxInt.Fine A φ B₂) :
    (∑ᶠ c : W ⧸ B₁, φ (Quotient.out c)) / (B₁.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ (B₁ ⊓ B₂), φ (Quotient.out c)) / ((B₁ ⊓ B₂).relIndex A : ℂ) := by
  have hle : B₁ ⊓ B₂ ≤ B₁ := inf_le_left
  have hprod := AddSubgroup.relIndex_mul_relIndex (B₁ ⊓ B₂) B₁ A hle h₁.1
  have hA : (B₁ ⊓ B₂).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h₁.2.1 h₂.2.1
  have hi : (B₁ ⊓ B₂).relIndex B₁ ≠ 0 := by
    rw [← hprod] at hA
    exact left_ne_zero_of_mul hA
  rw [(Fine_of_le_and_finsum_eq_relIndex_mul h₁ hle hi).2, ← hprod, Nat.cast_mul,
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hi)]
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma cint_eq_finsum_div_relIndex_of_fine {A B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) :
    _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  have hnice : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dif_pos hnice, finsum_out_div_relIndex_eq_inf_of_fine hnice.choose_spec hB,
    finsum_out_div_relIndex_eq_inf_of_fine hB hnice.choose_spec, inf_comm]
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] in
private lemma Fine_inf_of_relIndex_ne_zero {A A' B : AddSubgroup W} {φ : W → ℂ}
    (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (h₂ : A'.relIndex A ≠ 0) (h₁ : A.relIndex A' ≠ 0) :
    _root_.GlobalTheory.IdxInt.Fine A φ (B ⊓ A') ∧ _root_.GlobalTheory.IdxInt.Fine A' φ (B ⊓ A') := by
  have hBA : B ≤ A := hB.1
  have hCA : (B ⊓ A').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 h₂
  have hi : (B ⊓ A').relIndex B ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') B A inf_le_left hBA] at h
    exact left_ne_zero_of_mul h
  have hfine := (Fine_of_le_and_finsum_eq_relIndex_mul hB inf_le_left hi).1
  refine ⟨hfine, inf_le_right, ?_, hfine.2.2⟩
  have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hBA
  have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
    have h := hCA
    rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
    exact left_ne_zero_of_mul h
  rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
    AddSubgroup.inf_relIndex_right]
  exact mul_ne_zero hD h₁
end GlobalTheory.IdxInt.Transport
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Transport
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
open scoped Pointwise Classical
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
namespace GlobalTheory.IdxInt.Transport
namespace _root_.GlobalTheory.IdxInt.Transport
theorem _root_.solution : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'], (∀ (e : W ≃+ W') (A : AddSubgroup W) (φ : W' → ℂ), (_root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔ _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))) ∧ _root_.GlobalTheory.IdxInt.cint (A.map e.toAddMonoidHom) φ = _root_.GlobalTheory.IdxInt.cint A (fun w => φ (e w))) ∧ ∀ (A A' : AddSubgroup W) (φ : W → ℂ), A.relIndex A' ≠ 0 → A'.relIndex A ≠ 0 → (_root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ) ∧ _root_.GlobalTheory.IdxInt.cint A' φ * (A.relIndex A' : ℂ) = _root_.GlobalTheory.IdxInt.cint A φ * (A'.relIndex A : ℂ) := by
  intro W _ W' _
  refine ⟨fun e A φ => ?_, fun A A' φ h₁ h₂ => ?_⟩
  · have hiff : _root_.GlobalTheory.IdxInt.Nice (A.map e.toAddMonoidHom) φ ↔
        _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w)) := by
      constructor
      · rintro ⟨B', hB'⟩
        have hB'' : _root_.GlobalTheory.IdxInt.Fine (A.map e.toAddMonoidHom)
            (fun w => (fun w => φ (e w)) (e.symm w)) B' := by simpa using hB'
        have h := (Fine_map_addEquiv_and_finsum_eq e.symm (φ := fun w => φ (e w)) hB'').1
        rw [map_symm_map_addEquiv] at h
        exact ⟨_, h⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_map_addEquiv_and_finsum_eq e hB).1⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A (fun w => φ (e w))
    · obtain ⟨B, hB⟩ := hN
      rw [cint_eq_finsum_div_relIndex_of_fine hB, cint_eq_finsum_div_relIndex_of_fine (Fine_map_addEquiv_and_finsum_eq e hB).1,
        (Fine_map_addEquiv_and_finsum_eq e hB).2, AddSubgroup.relIndex_map_map_of_injective _ _ e.injective]
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dif_neg hN, dif_neg (hiff.not.mpr hN)]
  · have hiff : _root_.GlobalTheory.IdxInt.Nice A φ ↔ _root_.GlobalTheory.IdxInt.Nice A' φ := by
      constructor
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₂ h₁).2⟩
      · rintro ⟨B, hB⟩
        exact ⟨_, (Fine_inf_of_relIndex_ne_zero hB h₁ h₂).2⟩
    refine ⟨hiff, ?_⟩
    by_cases hN : _root_.GlobalTheory.IdxInt.Nice A φ
    · obtain ⟨B, hB⟩ := hN
      have hC := Fine_inf_of_relIndex_ne_zero hB h₂ h₁
      have hCD : B ⊓ A' ≤ A ⊓ A' := inf_le_inf_right A' hB.1
      have hD : (B ⊓ A').relIndex (A ⊓ A') ≠ 0 := by
        have h := hC.1.2.1
        rw [← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left] at h
        exact left_ne_zero_of_mul h
      rw [cint_eq_finsum_div_relIndex_of_fine hC.1, cint_eq_finsum_div_relIndex_of_fine hC.2,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A' hCD inf_le_right,
        ← AddSubgroup.relIndex_mul_relIndex (B ⊓ A') (A ⊓ A') A hCD inf_le_left,
        AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_left]
      have hD' : ((B ⊓ A').relIndex (A ⊓ A') : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
      have h₁' : (A.relIndex A' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₁
      have h₂' : (A'.relIndex A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h₂
      push_cast
      field_simp
    · unfold _root_.GlobalTheory.IdxInt.cint
      rw [dif_neg hN, dif_neg (hiff.not.mp hN)]
      simp
end _root_.GlobalTheory.IdxInt.Transport
end GlobalTheory.IdxInt.Transport
