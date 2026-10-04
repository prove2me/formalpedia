-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_4
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:27:30.866567+00:00
-- url     : https://prove2.me/submissions/5a9ab78d-0e5c-427f-8ac4-d2717f8d1b2f

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MeasureTheory ProbabilityTheory MDPFinance.InfiniteHorizonApplications

namespace CasinoCex

noncomputable def C0 : CasinoMarket where
  B := 0
  p := 1 / 2
  hp0 := by norm_num
  hp1 := by norm_num

theorem vpi_one (π : ℕ → Fin (C0.B + 1) → ℕ) (n : ℕ) : C0.VpiSeq π n 0 = 1 := by
  cases n with
  | zero => simp [CasinoMarket.VpiSeq, C0]
  | succ n => simp [CasinoMarket.VpiSeq, C0]

end CasinoCex

open CasinoCex in
theorem solution : ¬ (∀ (Mk : CasinoMarket) (hp : Mk.p = 1 / 2),
    (∀ x : Fin (Mk.B + 1), Mk.Jinf x = (x.1 : ℝ) / Mk.B) ∧
      ∀ f : Fin (Mk.B + 1) → ℕ, (∀ x : Fin (Mk.B + 1), 0 < x.1 → 0 < f x) →
        ∀ x, Mk.Jinfpi f x = Mk.Jinf x) := by
  intro h
  have H := (h C0 rfl).1 0
  have hJ : C0.Jinf 0 = 1 := by
    unfold CasinoMarket.Jinf
    simp only [vpi_one, ciSup_const]
  rw [hJ] at H
  have : ((0 : Fin (C0.B + 1)).1 : ℝ) / (C0.B : ℝ) = 0 := by simp
  rw [this] at H
  norm_num at H

#print axioms solution
