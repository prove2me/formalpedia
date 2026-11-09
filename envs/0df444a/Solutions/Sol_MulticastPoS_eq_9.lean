-- Prove2me | solution 1 for MulticastPoS.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:28:33.470316+00:00
-- url     : https://prove2.me/submissions/f409b967-f2a8-4738-8eda-ddee4bb39c25

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_walkCount

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace Aux_MPoS9

theorem hmono : Monotone harmonic := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ]
  have : (0 : ℚ) ≤ (↑(n + 1))⁻¹ := inv_nonneg.mpr (by positivity)
  linarith

theorem hsub (a b : ℕ) : harmonic (a + b) ≤ harmonic a + harmonic b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, harmonic_succ, harmonic_succ]
    have h : ((↑(a + b + 1) : ℚ))⁻¹ ≤ ((↑(b + 1) : ℚ))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact_mod_cast (by omega : b + 1 ≤ a + b + 1)
    linarith

end Aux_MPoS9

open MulticastPoS in
theorem solution :
    (∀ a b : ℕ, (harmonic (a + b) : ℝ) ≤ harmonic a + harmonic b) ∧
    (∀ {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s m : ι → V),
      (∀ e ∈ G.edgeSet, 0 ≤ c e) →
      ∀ (L : ∀ i, G.Walk (s i) (m i)) (D : ∀ i, G.Walk (m i) t) (R : ι → Finset (Sym2 V)),
      (∀ i, R i ⊆ ((L i).edges ++ (D i).edges).toFinset) →
      potential (game G c t s) R ≤
        (∑ f, c f * (harmonic (walkCount L f) : ℝ)) +
          (∑ f, c f * (harmonic (walkCount D f) : ℝ))) := by
  refine ⟨fun a b => by exact_mod_cast Aux_MPoS9.hsub a b, ?_⟩
  intro V ι _ _ _ _ G c t s m hc L D R hR
  have hpot : potential (game G c t s) R = ∑ e, c e * (harmonic (load R e) : ℝ) := by
    unfold potential
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show c e / (x : ℝ) = c e * ((x : ℝ))⁻¹
    ring
  have hload : ∀ e, load R e ≤ walkCount L e + walkCount D e := by
    intro e
    unfold load walkCount
    calc (Finset.univ.filter fun i => e ∈ R i).card
        ≤ ((Finset.univ.filter fun i => e ∈ (L i).edges) ∪
            (Finset.univ.filter fun i => e ∈ (D i).edges)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := hR i hi
          rw [List.mem_toFinset, List.mem_append] at this
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          exact this
      _ ≤ _ := Finset.card_union_le _ _
  rw [hpot, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases he : e ∈ G.edgeSet
  · have h1 : (harmonic (load R e) : ℝ) ≤ harmonic (walkCount L e) + harmonic (walkCount D e) := by
      have := (Aux_MPoS9.hmono (hload e)).trans (Aux_MPoS9.hsub _ _)
      exact_mod_cast this
    have := mul_le_mul_of_nonneg_left h1 (hc e he)
    linarith
  · have hL0 : walkCount L e = 0 := by
      unfold walkCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact he ((L i).edges_subset_edgeSet hi)
    have hD0 : walkCount D e = 0 := by
      unfold walkCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact he ((D i).edges_subset_edgeSet hi)
    have hl0 : load R e = 0 := by have := hload e; omega
    rw [hL0, hD0, hl0]
    simp
