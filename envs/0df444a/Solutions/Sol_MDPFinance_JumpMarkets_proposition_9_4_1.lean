-- Prove2me | solution 1 for MDPFinance.JumpMarkets.proposition_9_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:16:56.718168+00:00
-- url     : https://prove2.me/submissions/ae86de20-31d0-4bb4-aac5-5e1925e305c6

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_TradeExecution

open MeasureTheory

namespace B5e0006fAux

lemma integral_rate (lam L : ℝ) (hL : 0 ≤ L) :
    ∫ s in Set.Ioo (0 : ℝ) L, lam * Real.exp (-lam * s) = 1 - Real.exp (-lam * L) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -Real.exp (-lam * s))]
  · simp
    ring
  · intro x _
    have h1 : HasDerivAt (fun s => -lam * s) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    have h2 := h1.exp.neg
    exact h2.congr_deriv (by ring)
  · exact (by fun_prop : Continuous fun s => lam * Real.exp (-lam * s)).intervalIntegrable _ _

lemma integral_bound (lam L K : ℝ) (hlam : 0 ≤ lam) (hL : 0 ≤ L) (g : ℝ → ℝ)
    (hg0 : ∀ s, 0 ≤ g s) (hgK : ∀ s, g s ≤ K) :
    ∫ s in Set.Ioo (0 : ℝ) L, lam * Real.exp (-lam * s) * g s
      ≤ (1 - Real.exp (-lam * L)) * K := by
  have hint : IntegrableOn (fun s => lam * Real.exp (-lam * s) * K) (Set.Ioo (0 : ℝ) L) := by
    exact ((by fun_prop : Continuous fun s => lam * Real.exp (-lam * s) * K).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  calc ∫ s in Set.Ioo (0 : ℝ) L, lam * Real.exp (-lam * s) * g s
      ≤ ∫ s in Set.Ioo (0 : ℝ) L, lam * Real.exp (-lam * s) * K := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun s =>
            mul_nonneg (mul_nonneg hlam (Real.exp_pos _).le) (hg0 s)
        · exact hint
        · exact Filter.Eventually.of_forall fun s =>
            mul_le_mul_of_nonneg_left (hgK s) (mul_nonneg hlam (Real.exp_pos _).le)
    _ = (1 - Real.exp (-lam * L)) * K := by
        rw [integral_mul_const, integral_rate lam L hL]

lemma integral_nonneg' (lam L : ℝ) (hlam : 0 ≤ lam) (g : ℝ → ℝ) (hg0 : ∀ s, 0 ≤ g s) :
    0 ≤ ∫ s in Set.Ioo (0 : ℝ) L, lam * Real.exp (-lam * s) * g s :=
  integral_nonneg fun s => mul_nonneg (mul_nonneg hlam (Real.exp_pos _).le) (hg0 s)

end B5e0006fAux

open MDPFinance.JumpMarkets in
theorem solution (M : MDPFinance.JumpMarkets.TradeExecution) :
    M.IsBoundingFunction (1 - Real.exp (-M.lam * M.T)) ∧
    1 - Real.exp (-M.lam * M.T) < 1 := by
  have hlam := M.lam_pos.le
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp a ha
    have ht : 0 ≤ M.T - p.1 := by
      have := (Set.mem_prod.mp hp).1
      linarith [this.2]
    have h1 := B5e0006fAux.integral_bound M.lam (M.T - p.1) (M.C p.2) hlam ht
      (fun s => M.C (a.val s)) (fun s => M.C_nonneg _) (fun s => M.C_strictMono.monotone (ha s))
    have h0 := B5e0006fAux.integral_nonneg' M.lam (M.T - p.1) hlam
      (fun s => M.C (a.val s)) (fun s => M.C_nonneg _)
    have hC := M.C_nonneg p.2
    have he := Real.exp_pos (-M.lam * (M.T - p.1))
    unfold TradeExecution.c
    rw [abs_of_nonneg (add_nonneg h0 (mul_nonneg he.le hC))]
    nlinarith
  · intro p hp a ha
    have hmem := (Set.mem_prod.mp hp).1
    have ht : 0 ≤ M.T - p.1 := by linarith [hmem.2]
    have h1 := B5e0006fAux.integral_bound M.lam (M.T - p.1) (M.C p.2) hlam ht
      (fun s => M.C (p.2 - a.val s)) (fun s => M.C_nonneg _)
      (fun s => M.C_strictMono.monotone (Nat.sub_le _ _))
    have hC := M.C_nonneg p.2
    have hexp : Real.exp (-M.lam * M.T) ≤ Real.exp (-M.lam * (M.T - p.1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hmem.1]
    calc _ ≤ (1 - Real.exp (-M.lam * (M.T - p.1))) * M.C p.2 := h1
      _ ≤ (1 - Real.exp (-M.lam * M.T)) * M.C p.2 :=
          mul_le_mul_of_nonneg_right (by linarith) hC
  · linarith [Real.exp_pos (-M.lam * M.T)]
