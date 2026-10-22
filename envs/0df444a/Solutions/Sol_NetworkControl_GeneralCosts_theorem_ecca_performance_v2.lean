-- Prove2me | solution 1 for NetworkControl.GeneralCosts.theorem_ecca_performance_v2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:23:47.371503+00:00
-- url     : https://prove2.me/submissions/62dcf1fe-1c7a-4181-99d6-504a57ade68e

import Mathlib
import Definitions.Def_NetworkControl_GeneralCosts_eccaAdmitted
import Definitions.Def_NetworkControl_GeneralCosts_virtualPowerQueue

namespace NetworkControl.GeneralCosts

noncomputable def eccaStep (u d : ℝ) : ℝ × ℝ :=
  (max (u - (if d < u then 2 else 0)) 0 + (if u ≤ 10 then 3 else 0),
   max (d - 1) 0 + (if d < u then 2 else 0))

noncomputable def eccaSt : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 => eccaStep (eccaSt t).1 (eccaSt t).2

noncomputable def eccaP (t : ℕ) : Fin 2 → ℝ :=
  if (eccaSt t).2 < (eccaSt t).1 then ![0, 2] else ![0, 0]

lemma ecca_st_nonneg (t : ℕ) : 0 ≤ (eccaSt t).1 ∧ 0 ≤ (eccaSt t).2 := by
  induction t with
  | zero => simp [eccaSt]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [eccaSt, eccaStep]
    constructor
    · have : 0 ≤ (if (eccaSt n).1 ≤ 10 then (3:ℝ) else 0) := by split_ifs <;> norm_num
      have := le_max_right ((eccaSt n).1 - (if (eccaSt n).2 < (eccaSt n).1 then (2:ℝ) else 0)) 0
      linarith
    · have : 0 ≤ (if (eccaSt n).2 < (eccaSt n).1 then (2:ℝ) else 0) := by split_ifs <;> norm_num
      have := le_max_right ((eccaSt n).2 - 1) 0
      linarith

lemma ecca_vpq (t : ℕ) : virtualPowerQueue eccaP 1 t = (eccaSt t).2 := by
  induction t with
  | zero => simp [virtualPowerQueue, eccaSt]
  | succ n ih =>
    simp only [virtualPowerQueue, ih, eccaSt, eccaStep, eccaP, Fin.sum_univ_two]
    split_ifs <;> simp

theorem ecca_core_neg : ¬ (∀
    {L : ℕ} {Chan : Type}
    (V Rhat Pmax Pav β : ℝ) (hV : 0 ≤ V) (hRhat : 0 ≤ Rhat) (hPmax : 0 < Pmax)
    (hPav : 0 < Pav) (hPavLtPmax : Pav < Pmax) (hβ : 0 < β)
    (A : ℕ → Fin L → ℝ) (hA0 : ∀ t i, 0 ≤ A t i) (hAle : ∀ t i, A t i ≤ Rhat)
    (S : ℕ → Chan)
    (C : (Fin L → ℝ) → Chan → Fin L → ℝ)
    (hCnonneg : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), 0 ≤ C P s i)
    (hCbeta : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), (∀ j, 0 ≤ P j) →
      (∑ j : Fin L, P j) ≤ Pmax → C P s i ≤ C (Function.update P i 0) s i + β * P i)
    (U : ℕ → Fin L → ℝ) (hU0 : ∀ i : Fin L, U 0 i = 0)
    (P : ℕ → Fin L → ℝ) (hPnonneg : ∀ t : ℕ, ∀ i : Fin L, 0 ≤ P t i)
    (hPbudget : ∀ t : ℕ, (∑ i : Fin L, P t i) ≤ Pmax)
    (D : ℕ → ℝ) (hDeq : ∀ t : ℕ, D t = virtualPowerQueue P Pav t)
    (hPopt : ∀ t : ℕ, ∀ P' : Fin L → ℝ, (∀ i : Fin L, 0 ≤ P' i) → (∑ i : Fin L, P' i) ≤ Pmax →
      (∑ i : Fin L, (U t i * C P' (S t) i - D t * P' i))
        ≤ ∑ i : Fin L, (U t i * C (P t) (S t) i - D t * (P t) i))
    (hUrec : ∀ t : ℕ, ∀ i : Fin L,
      U (t + 1) i = max (U t i - C (P t) (S t) i) 0 + eccaAdmitted (U t i) V (A t i)),
    (∀ t : ℕ, ∀ i : Fin L, U t i ≤ V + Rhat) ∧
      (∀ t : ℕ, D t ≤ β * V + β * Rhat + Pmax) ∧
      (∀ t0 T : ℕ, (∑ τ ∈ Finset.range T, ∑ i : Fin L, P (t0 + τ) i)
        ≤ Pav * (T : ℝ) + (β * V + β * Rhat + Pmax))) := by
  intro h
  have key := (@h 2 PUnit 10 3 2 1 (1/10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => ![3, 0]) (by intro t i; fin_cases i <;> simp) (by intro t i; fin_cases i <;> simp)
    (fun _ => PUnit.unit)
    (fun P _ => ![max (P 1) 0, 0])
    (by intro P s i; fin_cases i <;> simp)
    (by
      intro P s i hP hs
      fin_cases i
      · simp [Function.update]; exact hP 0
      · simp [Function.update]; exact hP 1)
    (fun t => ![(eccaSt t).1, 0])
    (by intro i; fin_cases i <;> simp [eccaSt])
    eccaP
    (by
      intro t i
      unfold eccaP
      split_ifs <;> fin_cases i <;> simp)
    (by
      intro t
      unfold eccaP
      split_ifs <;> simp [Fin.sum_univ_two])
    (fun t => (eccaSt t).2)
    (fun t => (ecca_vpq t).symm)
    (by
      intro t P' hP' hs
      have hd := (ecca_st_nonneg t).2
      simp only [Fin.sum_univ_two]
      unfold eccaP
      rw [Fin.sum_univ_two] at hs
      have h0 := hP' 0
      have h1 := hP' 1
      rw [max_eq_left h1]
      split_ifs with hlt
      · simp
        nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (show (0:ℝ) ≤ 2 - P' 1 by linarith), mul_nonneg hd h0]
      · simp
        rw [not_lt] at hlt
        nlinarith [mul_nonneg (sub_nonneg.2 hlt) h1, mul_nonneg hd h0])
    (by
      clear h
      intro t i
      fin_cases i
      · by_cases hc : (eccaSt t).1 ≤ 10 <;> by_cases hd : (eccaSt t).2 < (eccaSt t).1 <;>
          simp [eccaSt, eccaStep, eccaP, eccaAdmitted, hc, hd]
      · simp [eccaAdmitted])).2.1 4
  simp [eccaSt, eccaStep] at key
  norm_num at key

end NetworkControl.GeneralCosts

open NetworkControl.GeneralCosts

theorem solution : ¬ (∀
    {L : ℕ} {Chan : Type}
    (V Rhat Pmax Pav β : ℝ) (hV : 0 ≤ V) (hRhat : 0 ≤ Rhat) (hPmax : 0 < Pmax)
    (hPav : 0 < Pav) (hPavLtPmax : Pav < Pmax) (hβ : 0 < β)
    (A : ℕ → Fin L → ℝ) (hA0 : ∀ t i, 0 ≤ A t i) (hAle : ∀ t i, A t i ≤ Rhat)
    (S : ℕ → Chan)
    (C : (Fin L → ℝ) → Chan → Fin L → ℝ)
    (hCnonneg : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), 0 ≤ C P s i)
    (hCbeta : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), (∀ j, 0 ≤ P j) →
      (∑ j : Fin L, P j) ≤ Pmax → C P s i ≤ C (Function.update P i 0) s i + β * P i)
    (U : ℕ → Fin L → ℝ) (hU0 : ∀ i : Fin L, U 0 i = 0)
    (P : ℕ → Fin L → ℝ) (hPnonneg : ∀ t : ℕ, ∀ i : Fin L, 0 ≤ P t i)
    (hPbudget : ∀ t : ℕ, (∑ i : Fin L, P t i) ≤ Pmax)
    (D : ℕ → ℝ) (hDeq : ∀ t : ℕ, D t = virtualPowerQueue P Pav t)
    (hPopt : ∀ t : ℕ, ∀ P' : Fin L → ℝ, (∀ i : Fin L, 0 ≤ P' i) → (∑ i : Fin L, P' i) ≤ Pmax →
      (∑ i : Fin L, (U t i * C P' (S t) i - D t * P' i))
        ≤ ∑ i : Fin L, (U t i * C (P t) (S t) i - D t * (P t) i))
    (hUrec : ∀ t : ℕ, ∀ i : Fin L,
      U (t + 1) i = max (U t i - C (P t) (S t) i) 0 + eccaAdmitted (U t i) V (A t i)),
    (∀ t : ℕ, ∀ i : Fin L, U t i ≤ V + Rhat) ∧
      (∀ t : ℕ, D t ≤ β * V + β * Rhat + Pmax) ∧
      (∀ t0 T : ℕ, (∑ τ ∈ Finset.range T, ∑ i : Fin L, P (t0 + τ) i)
        ≤ Pav * (T : ℝ) + (β * V + β * Rhat + Pmax))) := ecca_core_neg
