-- Prove2me | solution 1 for HeldKarp.Gap.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:52:28.462409+00:00
-- url     : https://prove2.me/submissions/6db6eaf1-6454-4795-b5da-a48df34b1aa6

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction

open Classical
open HeldKarp.Ascent
open HeldKarp.Gap

theorem g69g_lift_eq {n : ℕ} (π : Fin n → ℝ) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    Sym2.lift ⟨fun i j => π i + π j, fun i j => add_comm (π i) (π j)⟩ e =
      ∑ v, if v ∈ e then π v else 0 := by
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mk_isDiag_iff] at he
    rw [Sym2.lift_mk]
    have : ∀ v : Fin n, (if v ∈ s(a, b) then π v else 0) =
        (if a = v then π v else 0) + (if b = v then π v else 0) := by
      intro v
      by_cases ha : v = a
      · subst ha; simp [Ne.symm he, he]
      · by_cases hb : v = b
        · subst hb; simp [ha, Ne.symm ha]
        · simp [Sym2.mem_iff, ha, hb, Ne.symm ha, Ne.symm hb]
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem g69g_weight_shift {n : ℕ} (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) :
    weight (shift c π) G = weight c G + ∑ v, π v * (G.degree v : ℝ) := by
  unfold weight shift
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_congr rfl (fun e he => g69g_lift_eq π e
    (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

theorem solution {n : ℕ} (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (C : SimpleGraph (Fin n)) (hC : IsTour C)
    (hmin : ∀ H : SimpleGraph (Fin n), IsTour H → weight c C ≤ weight c H) :
    ∀ H : SimpleGraph (Fin n), IsTour H → weight (shift c π) C ≤ weight (shift c π) H := by
  intro H hH
  rw [g69g_weight_shift, g69g_weight_shift]
  have e1 : ∀ v, (C.degree v : ℝ) = (H.degree v : ℝ) := by
    intro v; rw [hC.2 v, hH.2 v]
  simp_rw [e1]
  linarith [hmin H hH]
