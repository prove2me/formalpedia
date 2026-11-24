-- Prove2me | solution 1 for LefebvreVariations.sidorenko_star
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:09:53.715798+00:00
-- url     : https://prove2.me/submissions/2536a7bd-02df-4be9-b112-5fef1fac3246

import Mathlib
import Definitions.Def_TenChallenges_Sidorenko

set_option autoImplicit false

open SimpleGraph

namespace LefebvreVariations

/-- Homomorphisms `K_{1,t} → G` are a centre `v` and a `t`-tuple of neighbours of `v`. -/
private def starHomEquiv (t : ℕ) {V : Type} (G : SimpleGraph V) :
    {f : Unit ⊕ Fin t → V //
      ∀ ⦃a b : Unit ⊕ Fin t⦄, (completeBipartiteGraph Unit (Fin t)).Adj a b → G.Adj (f a) (f b)} ≃
      Σ v : V, (Fin t → G.neighborSet v) where
  toFun f := ⟨f.1 (Sum.inl ()), fun i => ⟨f.1 (Sum.inr i), f.2 (by simp)⟩⟩
  invFun p := ⟨Sum.elim (fun _ => p.1) (fun i => (p.2 i).1), by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;> simp at h ⊢
    · exact (p.2 b).2
    · exact ((p.2 a).2).symm⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rcases x with x | x <;> rfl
  right_inv p := by rfl

/-- Homomorphisms `K_2 → G` are oriented edges. -/
private def edgeHomEquiv {V : Type} (G : SimpleGraph V) :
    {f : Fin 2 → V //
      ∀ ⦃a b : Fin 2⦄, (completeGraph (Fin 2)).Adj a b → G.Adj (f a) (f b)} ≃
      Σ v : V, G.neighborSet v where
  toFun f := ⟨f.1 0, ⟨f.1 1, f.2 (by decide)⟩⟩
  invFun p := ⟨![p.1, p.2.1], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢
    · exact p.2.2
    · exact p.2.2.symm⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    fin_cases x <;> rfl
  right_inv p := by rfl

private lemma card_star_homs (t : ℕ) {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    Nat.card {f : Unit ⊕ Fin t → V //
      ∀ ⦃a b : Unit ⊕ Fin t⦄, (completeBipartiteGraph Unit (Fin t)).Adj a b → G.Adj (f a) (f b)} =
      ∑ v, G.degree v ^ t := by
  rw [Nat.card_congr (starHomEquiv t G), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, card_neighborSet_eq_degree]

private lemma card_edge_homs {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card {f : Fin 2 → V //
      ∀ ⦃a b : Fin 2⦄, (completeGraph (Fin 2)).Adj a b → G.Adj (f a) (f b)} =
      ∑ v, G.degree v := by
  rw [Nat.card_congr (edgeHomEquiv G), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [card_neighborSet_eq_degree]

private lemma card_edges_star (t : ℕ) :
    Nat.card (completeBipartiteGraph Unit (Fin t)).edgeSet = t := by
  rw [Nat.card_coe_set_eq, Set.ncard_def, encard_edgeSet_completeBipartiteGraph]
  simp

/-- Power-mean inequality in the form needed. -/
private lemma power_mean {V : Type} [Fintype V] [Nonempty V] (d : V → ℝ) (hd : ∀ v, 0 ≤ d v)
    (t : ℕ) :
    ((∑ v, d v) / (Fintype.card V : ℝ) ^ 2) ^ t ≤
      (∑ v, d v ^ t) / (Fintype.card V : ℝ) ^ (1 + t) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rcases t with _ | m
  · simp [hn.ne']
  · have key := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := d)
      (fun i _ => hd i) m
    simp only [Finset.card_univ] at key
    have heq : ((∑ v, d v) / (Fintype.card V : ℝ) ^ 2) ^ (m + 1) =
        ((∑ v, d v) ^ (m + 1) / (Fintype.card V : ℝ) ^ m) /
          (Fintype.card V : ℝ) ^ (1 + (m + 1)) := by
      rw [div_pow, div_div, ← pow_mul, ← pow_add]
      congr 2
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right key (by positivity)

end LefebvreVariations

open LefebvreVariations SimpleGraph

theorem solution (t : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    SidorenkoFor (completeBipartiteGraph Unit (Fin t)) G := by
  classical
  unfold SidorenkoFor homDensity
  rw [card_star_homs t G, card_edge_homs G, card_edges_star t]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.cast_sum, Nat.cast_pow]
  exact power_mean (fun v => (G.degree v : ℝ)) (fun v => by positivity) t
