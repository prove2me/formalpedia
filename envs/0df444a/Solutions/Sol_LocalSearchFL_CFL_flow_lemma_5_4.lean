-- Prove2me | solution 1 for LocalSearchFL.CFL.flow_lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:34:13.219402+00:00
-- url     : https://prove2.me/submissions/ff50669e-f43a-4734-9669-8042025c6056

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

namespace LocalSearchFL.CFL

theorem aux_fl54_key {Cl : Type} [Fintype Cl] {m k : ℕ} (a : Cl → Fin m) (b : Cl → Fin k)
    (g : Fin m → Fin k → ℝ) :
    ∑ s, ∑ o, ((Finset.univ.filter (fun j => a j = s ∧ b j = o)).card : ℝ) * g s o =
      ∑ j, g (a j) (b j) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl (fun o _ => Finset.sum_comm)) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  simp [ite_and]

theorem aux_fl54_one {Cl : Type} [Fintype Cl] {k : ℕ} (b : Cl → Fin k) (h : Fin k → ℝ) :
    ∑ j, h (b j) = ∑ o, ((Finset.univ.filter (fun j => b j = o)).card : ℝ) * h o := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

end LocalSearchFL.CFL

open LocalSearchFL.CFL

theorem solution {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X O : CFLSol Cl Fa u) :
    ∃ x : Fin X.n → Fin O.n → ℕ,
      (∀ s, ∑ o, x s o = (X.nbhd s).card) ∧
      ∑ s, ∑ o, (x s o : ℝ) * (I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ)) ≤
        costS I X + costS I O + costF f O := by
  refine ⟨fun s o => (Finset.univ.filter (fun j => X.σ j = s ∧ O.σ j = o)).card, ?_, ?_⟩
  · intro s
    rw [CFLSol.nbhd, Finset.card_eq_sum_card_fiberwise (f := O.σ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [Finset.filter_filter]
  · push_cast
    rw [aux_fl54_key X.σ O.σ
      (fun s o => I.cf (X.loc s) (O.loc o) + f (O.loc o) / (u (O.loc o) : ℝ))]
    simp only [Finset.sum_add_distrib]
    have h1 : ∑ j, I.cf (X.loc (X.σ j)) (O.loc (O.σ j)) ≤ costS I X + costS I O := by
      unfold costS
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      unfold MetricInstance.cf MetricInstance.c
      calc I.d (Sum.inr (X.loc (X.σ j))) (Sum.inr (O.loc (O.σ j)))
          ≤ I.d (Sum.inr (X.loc (X.σ j))) (Sum.inl j) + I.d (Sum.inl j) (Sum.inr (O.loc (O.σ j))) :=
            I.triangle _ _ _
        _ = _ := by rw [I.symm (Sum.inr _) (Sum.inl j)]
    have h2 : ∑ j, f (O.loc (O.σ j)) / (u (O.loc (O.σ j)) : ℝ) ≤ costF f O := by
      rw [aux_fl54_one O.σ (fun o => f (O.loc o) / (u (O.loc o) : ℝ))]
      unfold costF
      refine Finset.sum_le_sum (fun o _ => ?_)
      have hc := O.cap o
      have hpos : (0 : ℝ) < u (O.loc o) := by exact_mod_cast hu _
      have hc' : ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) ≤ u (O.loc o) := by
        exact_mod_cast hc
      calc ((Finset.univ.filter (fun j => O.σ j = o)).card : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ))
          ≤ (u (O.loc o) : ℝ) * (f (O.loc o) / (u (O.loc o) : ℝ)) :=
            mul_le_mul_of_nonneg_right hc' (div_nonneg (hf _) hpos.le)
        _ = f (O.loc o) := by field_simp
    linarith
