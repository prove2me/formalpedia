-- Prove2me | solution 1 for HeldKarp.Ascent.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:45:09.067686+00:00
-- url     : https://prove2.me/submissions/ef06da62-67f7-42dc-b0df-4306a652ed58

import Mathlib.Tactic
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
open HeldKarp.Ascent
open scoped BigOperators
noncomputable section

private theorem weights_bdd {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) :
    BddBelow {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ x = lagrWeight c π G} := by
  classical
  apply (Set.finite_range (lagrWeight c π)).bddBelow.mono
  rintro x ⟨G, hG, rfl⟩
  exact ⟨G, rfl⟩

private theorem bound_le_lagr {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) : oneTreeBound c π ≤ lagrWeight c π G :=
  csInf_le (weights_bdd c π) ⟨G, hG, rfl⟩

private theorem min_lagr_eq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) : oneTreeBound c π = lagrWeight c π G := by
  apply le_antisymm (bound_le_lagr c π G hG.1)
  unfold oneTreeBound
  refine le_csInf ?_ ?_
  · exact ⟨lagrWeight c π G, G, hG.1, rfl⟩
  · rintro x ⟨G', hG', rfl⟩
    exact hG.2 G' hG'

private theorem ascent_ineq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) :
    oneTreeBound c πbar - oneTreeBound c π ≤ ∑ i, (πbar i - π i) * degExcess G i := by
  have hb := bound_le_lagr c πbar G hG.1
  rw [min_lagr_eq c π G hG]
  unfold lagrWeight at hb ⊢
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  linarith

theorem _root_.solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) (t : ℝ) (ht : 0 < t)
    (ht' : t < 2 * (oneTreeBound c πbar - oneTreeBound c π) / ∑ i, (degExcess G i) ^ 2) :
    ∑ i, (πbar i - (π i + t * degExcess G i)) ^ 2 < ∑ i, (πbar i - π i) ^ 2 := by
  have hv0 : 0 ≤ ∑ i, (degExcess G i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv : 0 < ∑ i, (degExcess G i)^2 := by
    by_contra hno
    have hz : (∑ i, (degExcess G i)^2) = 0 := le_antisymm (le_of_not_gt hno) hv0
    rw [hz, div_zero] at ht'
    linarith
  have hstep := (lt_div_iff₀ hv).mp ht'
  have ha := ascent_ineq c πbar π G hG
  have heq : (∑ i, (πbar i - (π i+t*degExcess G i))^2) =
      (∑ i, (πbar i-π i)^2) - 2*t*(∑ i, (πbar i-π i)*degExcess G i) + t^2*(∑ i, (degExcess G i)^2) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  have hh := mul_lt_mul_of_pos_left hstep ht
  have hh' := mul_le_mul_of_nonneg_left ha ht.le
  nlinarith
