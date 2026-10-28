-- Prove2me | solution 1 for LookaheadAPI.LeastSquares.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:37:54.647953+00:00
-- url     : https://prove2.me/submissions/c3e2bc48-5322-4566-b310-763da857cad1

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace Aux_LA_eq34

theorem sup'_add {A : Type*} (s : Finset A) (H : s.Nonempty) (f : A → ℝ) (d : ℝ) :
    s.sup' H (fun a => f a + d) = s.sup' H f + d := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun a ha => by linarith [Finset.le_sup' f ha])
  · have : s.sup' H f ≤ s.sup' H (fun a => f a + d) - d :=
      Finset.sup'_le _ _ (fun a ha => by
        have := Finset.le_sup' (fun a => f a + d) ha
        linarith)
    linarith

end Aux_LA_eq34

open LookaheadAPI.LeastSquares FoundationsML.ReinforcementLearning in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) :
    (∀ (μ : S → A) (c : ℝ) (J : S → ℝ),
      bellmanOp M (J + fun _ => c) = bellmanOp M J + (fun _ => M.α * c) ∧
      policyOp M μ (J + fun _ => c) = policyOp M μ J + (fun _ => M.α * c)) ∧
    (∀ (μ : S → A) (J J' : S → ℝ), J ≤ J' →
      bellmanOp M J ≤ bellmanOp M J' ∧ policyOp M μ J ≤ policyOp M μ J') := by
  have hrow : ∀ (s : S) (a : A) (J : S → ℝ) (c : ℝ),
      ∑ j : S, M.P s a j * (J j + c) = ∑ j : S, M.P s a j * J j + c := by
    intro s a J c
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      (M.kernel s a).2, one_mul]
  have hmono : ∀ (s : S) (a : A) (J J' : S → ℝ), J ≤ J' →
      ∑ j : S, M.P s a j * J j ≤ ∑ j : S, M.P s a j * J' j := by
    intro s a J J' h
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) ((M.kernel s a).1 j))
  refine ⟨fun μ c J => ⟨?_, ?_⟩, fun μ J J' h => ⟨?_, ?_⟩⟩
  · funext s
    simp only [bellmanOp, BellmanOperator, Pi.add_apply, hrow]
    rw [← Aux_LA_eq34.sup'_add]
    congr 1
    funext a
    ring
  · funext s
    simp only [policyOp, Pi.add_apply]
    rw [hrow]
    ring
  · intro s
    simp only [bellmanOp, BellmanOperator]
    apply Finset.sup'_le _ _
    intro a ha
    refine le_trans ?_ (Finset.le_sup' _ ha)
    have := hmono s a J J' h
    nlinarith [M.α_pos]
  · intro s
    simp only [policyOp]
    have := hmono s (μ s) J J' h
    nlinarith [M.α_pos]
