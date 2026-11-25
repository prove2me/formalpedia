-- Prove2me | solution 1 for GlobalTheory.IdxInt.cint_eq_mean_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:41:04.296445+00:00
-- url     : https://prove2.me/submissions/ffcf97bc-138e-4251-95ff-5eef37ec52e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqOfFineSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentatives
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
namespace GlobalTheory.IdxInt
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma eq_of_mem_finset_of_mk_eq {A B : AddSubgroup W} {R : Finset W}
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B)
    {x y : W} (hx : x ∈ R) (hy : y ∈ R) (h : (x : W ⧸ B) = y) : x = y := by
  have hxy : -x + y ∈ B := QuotientAddGroup.eq.mp h
  obtain ⟨z, _, hz⟩ := hR y (hRA y hy)
  have h1 := hz y ⟨hy, by simp⟩
  have h2 := hz x ⟨hx, by rwa [sub_eq_neg_add]⟩
  exact h2.trans h1.symm
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma exists_mem_finset_mk_eq_of_mem {A B : AddSubgroup W} {R : Finset W}
    (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) {w : W} (hw : w ∈ A) :
    ∃ x ∈ R, (x : W ⧸ B) = w := by
  obtain ⟨x, ⟨hx, hwx⟩, _⟩ := hR w hw
  refine ⟨x, hx, QuotientAddGroup.eq.mpr ?_⟩
  rw [← sub_eq_neg_add]
  exact hwx
open scoped Pointwise Classical in
variable {W : Type} [AddCommGroup W] in
private lemma apply_eq_of_quotient_mk_eq_of_invariant {B : AddSubgroup W} {φ : W → ℂ}
    (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) {u v : W} (h : (u : W ⧸ B) = v) : φ u = φ v := by
  have hb : -u + v ∈ B := QuotientAddGroup.eq.mp h
  have := hinv u (-u + v) hb
  rwa [add_neg_cancel_left, eq_comm] at this
end GlobalTheory.IdxInt
end

set_option autoImplicit false
open GlobalTheory.IdxInt
open scoped Pointwise Classical
open GlobalTheory GlobalTheory.IdxInt
open scoped Pointwise Classical
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt
namespace _root_.GlobalTheory.IdxInt
theorem _root_.solution {W : Type} [AddCommGroup W]
    (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W)
    (hBA : B ≤ A) (hinv : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (hsupp : ∀ w, w ∉ A → φ w = 0)
    (hRA : ∀ w ∈ R, w ∈ A) (hR : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) :
    _root_.GlobalTheory.IdxInt.Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧
      _root_.GlobalTheory.IdxInt.cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  have hmemA : ∀ w, φ w ≠ 0 → w ∈ A := fun w hw => by
    by_contra h
    exact hw (hsupp w h)
  have hcard : (R.card : ℕ) = B.relIndex A := by
    let f : R → A ⧸ B.addSubgroupOf A := fun x => ((⟨x.1, hRA x.1 x.2⟩ : A) : A ⧸ B.addSubgroupOf A)
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        have h' : -(⟨x, hRA x hx⟩ : A) + ⟨y, hRA y hy⟩ ∈ B.addSubgroupOf A :=
          QuotientAddGroup.eq.mp h
        rw [AddSubgroup.mem_addSubgroupOf] at h'
        have h'' : -x + y ∈ B := by simpa using h'
        exact Subtype.ext (eq_of_mem_finset_of_mk_eq hRA hR hx hy (QuotientAddGroup.eq.mpr h''))
      · intro c
        induction c using QuotientAddGroup.induction_on with
        | H a =>
          obtain ⟨x, ⟨hx, hax⟩, _⟩ := hR a.1 a.2
          refine ⟨⟨x, hx⟩, QuotientAddGroup.eq.mpr ?_⟩
          rw [AddSubgroup.mem_addSubgroupOf]
          have : -x + a.1 ∈ B := by rwa [← sub_eq_neg_add]
          simpa using this
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← Nat.card_congr (Equiv.ofBijective f hf),
      Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : R.card ≠ 0 := by
    obtain ⟨x, ⟨hx, _⟩, _⟩ := hR 0 A.zero_mem
    exact Finset.card_ne_zero_of_mem hx
  have hfine : _root_.GlobalTheory.IdxInt.Fine A φ B := by
    unfold _root_.GlobalTheory.IdxInt.Fine
    refine ⟨hBA, hcard ▸ hne, fun w b hb => hinv w b hb, ?_⟩
    refine (R.finite_toSet.image (QuotientAddGroup.mk : W → W ⧸ B)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hxw⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA w hw)
    exact ⟨x, hx, hxw⟩
  refine ⟨hfine, hcard, ?_⟩
  have hsum : ∑ᶠ c : W ⧸ B, φ (Quotient.out c) = ∑ w ∈ R, φ w := by
    rw [finsum_eq_sum_of_support_subset (s := R.image (QuotientAddGroup.mk : W → W ⧸ B)) _ ?_]
    · rw [Finset.sum_image (fun x hx y hy h => eq_of_mem_finset_of_mk_eq hRA hR hx hy h)]
      exact Finset.sum_congr rfl fun x _ => apply_eq_of_quotient_mk_eq_of_invariant hinv (QuotientAddGroup.out_eq' _)
    · intro c hc
      obtain ⟨x, hx, hxc⟩ := exists_mem_finset_mk_eq_of_mem hR (hmemA _ hc)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, hxc.trans (QuotientAddGroup.out_eq' c)⟩
  rw [_root_.GlobalTheory.IdxInt.cint_eq_of_fine A B φ hfine, hsum, ← hcard]
end _root_.GlobalTheory.IdxInt
end GlobalTheory.IdxInt
