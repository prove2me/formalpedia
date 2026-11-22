-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.ordered_pairs_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:04.227778+00:00
-- url     : https://prove2.me/submissions/3da66919-bbf4-422d-9edd-ce1a217b7322

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Expurgation
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Calibration

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {N : ℕ} : ∀ A : Finset (Fin N),
    ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).card = A.card.choose 2 := by
  classical
  intro A
  rw [← Finset.card_powersetCard 2 A]
  refine Finset.card_bij (fun uv _ => ({uv.1, uv.2} : Finset (Fin N))) ?_ ?_ ?_
  · intro uv huv
    simp only [Finset.mem_filter, Finset.mem_product] at huv
    rw [Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair (ne_of_lt huv.2)⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact huv.1.1
    · exact huv.1.2
  · intro uv₁ h₁ uv₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_product] at h₁ h₂
    have hm1 : uv₁.1 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
      rw [← heq]; simp
    have hm2 : uv₁.2 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
      rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
    rcases hm1 with h11 | h12 <;> rcases hm2 with h21 | h22
    · exfalso; exact (ne_of_lt h₁.2) (h11.trans h21.symm)
    · exact Prod.ext h11 h22
    · exfalso
      have hlt1 : uv₁.1 < uv₁.2 := h₁.2
      have hlt2 : uv₂.1 < uv₂.2 := h₂.2
      rw [h12, h21] at hlt1
      exact lt_asymm hlt1 hlt2
    · exfalso; exact (ne_of_lt h₁.2) (h12.trans h22.symm)
  · intro T hT
    rw [Finset.mem_powersetCard] at hT
    rcases Finset.card_eq_two.mp hT.2 with ⟨a, b, hab, rfl⟩
    have ha : a ∈ A := hT.1 (by simp)
    have hb : b ∈ A := hT.1 (by simp)
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · refine ⟨(a, b), ?_, rfl⟩
      simp [ha, hb, hlt]
    · exact absurd rfl hab
    · refine ⟨(b, a), ?_, Finset.pair_comm b a⟩
      simp [ha, hb, hgt]
end HighDimSteinerSpanners.Proofs.CSP
