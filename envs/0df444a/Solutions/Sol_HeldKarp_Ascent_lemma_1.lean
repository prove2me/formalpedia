-- Prove2me | solution 1 for HeldKarp.Ascent.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:45:08.298186+00:00
-- url     : https://prove2.me/submissions/f837f44b-8ae9-467f-8492-c5fcc39001ac

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
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G)
    (hw : oneTreeBound c π ≤ oneTreeBound c πbar) :
    oneTreeBound c πbar - oneTreeBound c π ≤ ∑ i, (πbar i - π i) * degExcess G i ∧
      0 ≤ oneTreeBound c πbar - oneTreeBound c π := by
  exact ⟨ascent_ineq c πbar π G hG, sub_nonneg.mpr hw⟩
