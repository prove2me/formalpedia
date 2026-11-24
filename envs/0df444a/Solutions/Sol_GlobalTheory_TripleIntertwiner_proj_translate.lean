-- Prove2me | solution 1 for GlobalTheory.TripleIntertwiner.proj_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:05.642664+00:00
-- url     : https://prove2.me/submissions/2dbb4407-f8fa-4bb0-8f16-0388bcd2929b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mem
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_mk
import Theorems.Thm_GlobalTheory_TripleIntertwiner_rep_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]
variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}
namespace GlobalTheory.TripleIntertwiner
theorem _root_.solution (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0)
    {A₀ A : AddSubgroup V}
    [Fintype (A ⧸ A₀.addSubgroupOf A)] (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (f : F) (hf : ∀ x ∈ A, W x f = f) (v : V) (hv : ∀ l ∈ A₀, c l v = 1 ∧ c v l = 1) :
    ∑ q : A ⧸ A₀.addSubgroupOf A, W (rep q) (W v f) =
      (if v ∈ A then (A₀.relIndex A : ℂ) else 0) • f := by
  split_ifs with h
  · rw [hf v h, Finset.sum_congr rfl (g := fun _ => f) (fun q _ => hf _ (rep_mem q)), Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul, ← Nat.card_eq_fintype_card]
    rfl
  · let χ : V → ℂ := fun x => c x v / c v x
    have hχ : ∀ x y, χ (x + y) = χ x * χ y := by
      intro x y; simp only [χ, H.2.1, H.2.2.1, mul_div_mul_comm]
    have hW : ∀ x ∈ A, W x (W v f) = χ x • W v f := by
      intro x hx
      have h1 := H.1 v x f
      rw [hf x hx] at h1
      rw [H.1, h1, smul_smul, add_comm]
      simp only [χ]
      rw [div_mul_cancel₀ _ (H.2.2.2 _ _)]
    obtain ⟨x₀, hx₀, hne⟩ : ∃ x ∈ A, c x v ≠ c v x := by
      by_contra hh
      push_neg at hh
      exact h (hsd v hh)
    have hp : ∀ x l, l ∈ A₀ → χ (x + l) = χ x := by
      intro x l hl
      rw [hχ]; simp only [χ]; rw [(hv l hl).1, (hv l hl).2]; simp
    have hsum : ∑ q : A ⧸ A₀.addSubgroupOf A, χ (rep q) = 0 := by
      let q₀ : A ⧸ A₀.addSubgroupOf A := QuotientAddGroup.mk ⟨x₀, hx₀⟩
      have e := Equiv.sum_comp (Equiv.addLeft q₀) (fun q => χ (rep q))
      have e2 : ∀ q, χ (rep (Equiv.addLeft q₀ q)) = χ x₀ * χ (rep q) := by
        intro q
        obtain ⟨l, -, hl, h3⟩ := rep_add q₀ q
        obtain ⟨l', -, hl', h4⟩ := rep_mk (B := A₀) (⟨x₀, hx₀⟩ : A)
        show χ (rep (q₀ + q)) = _
        rw [h3, hp _ _ hl, hχ, h4, hp _ _ hl']
      simp only [e2, ← Finset.mul_sum] at e
      have h1 : χ x₀ - 1 ≠ 0 := by
        simp only [χ]
        rw [sub_ne_zero, Ne, div_eq_one_iff_eq (H.2.2.2 _ _)]
        exact hne
      have : (χ x₀ - 1) * ∑ q : A ⧸ A₀.addSubgroupOf A, χ (rep q) = 0 := by
        rw [sub_mul, e]; ring
      exact (mul_eq_zero.mp this).resolve_left h1
    rw [Finset.sum_congr rfl (fun q _ => hW _ (rep_mem q)), ← Finset.sum_smul, hsum, zero_smul, zero_smul]
end GlobalTheory.TripleIntertwiner
