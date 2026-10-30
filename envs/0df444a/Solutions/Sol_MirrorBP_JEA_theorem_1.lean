-- Prove2me | solution 1 for MirrorBP.JEA.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:39:49.241635+00:00
-- url     : https://prove2.me/submissions/4a0ff093-1808-43aa-90f6-6299cf792c84

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP
import Theorems.Thm_MirrorBP_JEA_proposition_2

namespace MirrorBP.JEA.Thm1Aux

open Finset MirrorBP.JEA

/-- The per-period payoff is at most one in absolute value, so the expected payoff over `n`
periods is at most `n` in absolute value. -/
theorem abs_expPayoffFrom_le {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (phi : ℕ → Ty → ℝ) (π : Policy P D) :
    ∀ n t h q, (∀ s, t ≤ s → s < t + n → IsRate (phi s)) →
      |expPayoffFrom w phi π n t h q| ≤ n := by
  intro n
  induction n with
  | zero => intro t h q _; simp [expPayoffFrom]
  | succ n ih =>
    intro t h q hr
    rw [expPayoffFrom]
    have hrt := hr t le_rfl (by omega)
    have key : ∀ τ, |∑ d, π.act t h q τ d *
        (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))|
          ≤ ((n : ℝ) + 1) := by
      intro τ
      calc _ ≤ ∑ d, |π.act t h q τ d *
            (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))| :=
              abs_sum_le_sum_abs _ _
        _ ≤ ∑ d, π.act t h q τ d * ((n : ℝ) + 1) := by
          apply sum_le_sum
          intro d _
          rw [abs_mul, abs_of_nonneg (π.nonneg _ _ _ _ _)]
          by_cases hf : Feasible P D τ q d
          · apply mul_le_mul_of_nonneg_left _ (π.nonneg _ _ _ _ _)
            have hp : |pay w τ d| ≤ 1 := by
              rcases d with _ | ⟨j, k⟩
              · simp [pay]
              · exact hw τ j hf.1 k hf.2.1
            have he := ih (t + 1) (h ++ [(q, τ, d)]) (step q d)
              (fun s hs1 hs2 => hr s (by omega) (by omega))
            calc _ ≤ |pay w τ d| + |expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d)| :=
                  abs_add_le _ _
              _ ≤ 1 + n := add_le_add hp he
              _ = n + 1 := by ring
          · rw [π.feasible _ _ _ _ _ hf]; simp
        _ = (n : ℝ) + 1 := by rw [← sum_mul, π.sum_one, one_mul]
    push_cast
    calc _ ≤ ∑ τ, |phi t τ * ∑ d, π.act t h q τ d *
          (pay w τ d + expPayoffFrom w phi π n (t + 1) (h ++ [(q, τ, d)]) (step q d))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ τ, phi t τ * ((n : ℝ) + 1) := by
          apply sum_le_sum
          intro τ _
          rw [abs_mul, abs_of_nonneg (hrt.1 τ)]
          exact mul_le_mul_of_nonneg_left (key τ) (hrt.1 τ)
      _ = (n : ℝ) + 1 := by rw [← sum_mul, hrt.2, one_mul]


/-- Choice of the batch size `ΔT` (Appendix D, proof of Theorem 4): from the bound of
Proposition 2 for every `0 < ΔT < T`, derive the bound of Theorem 1. -/
theorem choose_batch (C2 m eta L : ℝ) (T K : ℕ) (hm2 : 2 ≤ m) (hK1 : (1 : ℝ) ≤ K) (hT : 0 < T)
    (hη : 2 ≤ T → 0 ≤ eta) (htriv : L ≤ 2)
    (hprop : ∀ ΔT : ℕ, 0 < ΔT → ΔT < T →
      L ≤ C2 * m * ((K : ℝ) / ΔT) + C2 * m ^ 2 / K + ΔT * m * eta) :
    L ≤ (2 * max C2 0 + 2) * m * ((K : ℝ) / T + Real.sqrt (eta * K))
      + (2 * max C2 0 + 2) * m ^ 2 / K := by
  obtain ⟨C', hC'⟩ : ∃ C', C' = max C2 0 := ⟨_, rfl⟩
  rw [← hC']
  have hC'0 : 0 ≤ C' := hC' ▸ le_max_right _ _
  have hC2 : C2 ≤ C' := hC' ▸ le_max_left _ _
  obtain ⟨C, hCdef⟩ : ∃ C, C = 2 * C' + 2 := ⟨_, rfl⟩
  rw [← hCdef]
  have hKpos : (0 : ℝ) < K := by linarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hC2' : (2 : ℝ) ≤ C := by linarith
  have hCm : (4 : ℝ) ≤ C * m := by nlinarith
  have hsq0 : 0 ≤ Real.sqrt (eta * K) := Real.sqrt_nonneg _
  have hterm3 : 0 ≤ C * m ^ 2 / K := by positivity
  have hKT0 : 0 ≤ (K : ℝ) / T := by positivity
  by_cases hc1 : (T : ℝ) ≤ K
  · have : 1 ≤ (K : ℝ) / T := by rw [le_div_iff₀ hTpos]; linarith
    have : 4 ≤ C * m * ((K : ℝ) / T + Real.sqrt (eta * K)) := by nlinarith
    linarith
  push Not at hc1
  by_cases hc2 : 1 ≤ eta * K
  · have : 1 ≤ Real.sqrt (eta * K) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hc2
    have : 4 ≤ C * m * ((K : ℝ) / T + Real.sqrt (eta * K)) := by nlinarith
    linarith
  push Not at hc2
  have hT2 : 2 ≤ T := by
    have : (1 : ℝ) < T := by linarith
    have : 1 < T := by exact_mod_cast this
    omega
  have hT1r : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hT2r : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hT1pos : (0 : ℝ) < (T : ℝ) - 1 := by linarith
  have hKT1 : (K : ℝ) / ((T : ℝ) - 1) ≤ 2 * ((K : ℝ) / T) := by
    rw [div_le_iff₀ hT1pos]
    rw [show 2 * ((K : ℝ) / T) * ((T : ℝ) - 1) = K * (2 * (T - 1) / T) by field_simp]
    have : (1 : ℝ) ≤ 2 * ((T : ℝ) - 1) / T := by
      rw [le_div_iff₀ hTpos]; linarith
    nlinarith
  have heta0 : 0 ≤ eta := hη hT2
  rcases heta0.lt_or_eq with heta | heta
  · obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (eta * K) := ⟨_, rfl⟩
    rw [← hsdef]
    have hspos : 0 < s := hsdef ▸ Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = eta * K := hsdef ▸ Real.sq_sqrt (by positivity)
    obtain ⟨y, hydef⟩ : ∃ y, y = Real.sqrt (K / eta) := ⟨_, rfl⟩
    have hypos : 0 < y := hydef ▸ Real.sqrt_pos.mpr (by positivity)
    have hys : y * s = K := by
      rw [hydef, hsdef, ← Real.sqrt_mul (by positivity)]
      rw [show (K : ℝ) / eta * (eta * K) = K ^ 2 by field_simp]
      exact Real.sqrt_sq hKpos.le
    have hs1 : s < 1 := by
      rw [hsdef, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by positivity) hc2
    have hy1 : 1 < y := by nlinarith
    obtain ⟨n, hndef⟩ : ∃ n, n = ⌊y⌋₊ := ⟨_, rfl⟩
    have hn1 : 1 ≤ n := hndef ▸ Nat.le_floor (by simpa using hy1.le)
    have hny : (n : ℝ) ≤ y := hndef ▸ Nat.floor_le hypos.le
    have hny2 : y < n + 1 := hndef ▸ Nat.lt_floor_add_one y
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨ΔT, hΔdef⟩ : ∃ ΔT, ΔT = min (T - 1) n := ⟨_, rfl⟩
    have hΔ1 : 0 < ΔT := by rw [hΔdef]; exact lt_min (by omega) (by omega)
    have hΔT : ΔT < T := by rw [hΔdef]; exact lt_of_le_of_lt (min_le_left _ _) (by omega)
    have hbound := hprop ΔT hΔ1 hΔT
    have hΔpos : (0 : ℝ) < ΔT := by exact_mod_cast hΔ1
    have hΔn : (ΔT : ℝ) ≤ n := by rw [hΔdef]; exact_mod_cast (min_le_right _ _)
    have hKΔ : (K : ℝ) / ΔT ≤ 2 * ((K : ℝ) / T) + 2 * s := by
      rcases le_total (T - 1) n with hle | hle
      · have : ΔT = T - 1 := hΔdef ▸ min_eq_left hle
        rw [this, hT1r]
        linarith
      · have : ΔT = n := hΔdef ▸ min_eq_right hle
        rw [this]
        have hKn : (K : ℝ) / n ≤ 2 * s := by
          rw [div_le_iff₀ hnpos]
          have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          have : y ≤ 2 * n := by linarith
          have := mul_le_mul_of_nonneg_right this hspos.le
          linarith
        linarith
    have hΔη : (ΔT : ℝ) * eta ≤ s := by
      have h1 : (ΔT : ℝ) * eta ≤ y * eta := mul_le_mul_of_nonneg_right (le_trans hΔn hny) heta.le
      have h2' : y * eta = s := by
        have : y * eta * s = s * s := by
          calc y * eta * s = (y * s) * eta := by ring
            _ = K * eta := by rw [hys]
            _ = s ^ 2 := by rw [hs2]; ring
            _ = s * s := by ring
        exact mul_right_cancel₀ hspos.ne' this
      linarith
    have e1 : C2 * m * ((K : ℝ) / ΔT) ≤ C' * m * ((K : ℝ) / ΔT) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hC2 (by linarith)
    have e2 : C2 * m ^ 2 / K ≤ C * m ^ 2 / K := by
      apply div_le_div_of_nonneg_right _ hKpos.le
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e3 : C' * m * ((K : ℝ) / ΔT) ≤ C' * m * (2 * ((K : ℝ) / T) + 2 * s) :=
      mul_le_mul_of_nonneg_left hKΔ (by positivity)
    have e4 : (ΔT : ℝ) * m * eta ≤ m * s := by
      have := mul_le_mul_of_nonneg_left hΔη (show (0 : ℝ) ≤ m by linarith)
      linarith
    have e6 : C' * m * (2 * ((K : ℝ) / T) + 2 * s) + m * s
        ≤ C * m * ((K : ℝ) / T + s) := by
      have h1 : 0 ≤ m * ((K : ℝ) / T) := by positivity
      have h2 : 0 ≤ m * s := by positivity
      rw [hCdef]
      linarith
    linarith
  · subst heta
    have hbound := hprop (T - 1) (by omega) (by omega)
    rw [hT1r] at hbound
    have e1 : C2 * m * ((K : ℝ) / ((T : ℝ) - 1)) ≤ C' * m * ((K : ℝ) / ((T : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hC2 (by linarith)
    have e2 : C2 * m ^ 2 / K ≤ C * m ^ 2 / K := by
      apply div_le_div_of_nonneg_right _ hKpos.le
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e3 : C' * m * ((K : ℝ) / ((T : ℝ) - 1)) ≤ C' * m * (2 * ((K : ℝ) / T)) :=
      mul_le_mul_of_nonneg_left hKT1 (by positivity)
    have e4 : C' * m * (2 * ((K : ℝ) / T)) ≤ C * m * ((K : ℝ) / T + Real.sqrt (0 * K)) := by
      simp only [zero_mul, Real.sqrt_zero, add_zero]
      have : 0 ≤ m * ((K : ℝ) / T) := by positivity
      rw [hCdef]
      linarith
    simp only [mul_zero, add_zero] at hbound
    linarith

end MirrorBP.JEA.Thm1Aux

open Finset MirrorBP.JEA

theorem solution :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T : ℕ) (eta : ℝ) (K : ℕ)
        (sel : (V → ℕ) → Ty → V × V),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        VariesSlowly phi T eta →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ π : Policy P D, ∀ q ∈ StateSpace V K, ∀ q' ∈ StateSpace V K,
          (expPayoff w phi π T q
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q') / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / T + Real.sqrt (eta * K))
              + C * (Fintype.card V : ℝ) ^ 2 / K := by
  obtain ⟨C2, c2, N, h2⟩ := MirrorBP.JEA.proposition_2
  refine ⟨2 * max C2 0 + 2, max c2 1, N, ?_⟩
  intro V Ty _ _ _ _ P D w phi T eta K sel hm hP hD hw hT hrate hα hvar hK hsel π q hq q' hq'
  have hm2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : (2 : ℕ) ≤ Fintype.card V := hm
    exact_mod_cast this
  have hαpos : 0 < alphaMin P D phi T := by
    unfold alphaMin
    have hne : (range T).Nonempty := ⟨0, by simp [hT]⟩
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro t ht
    exact hα t (by simpa using ht)
  have hx1 : 1 ≤ (Fintype.card V : ℝ) + 1 / alphaMin P D phi T := by
    have : 0 < 1 / alphaMin P D phi T := by positivity
    linarith
  have hxN := one_le_pow₀ (n := N) hx1
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) * 1 ≤ max c2 1 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N :=
      mul_le_mul (le_max_right _ _) hxN zero_le_one (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hK2 : c2 * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ K :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hK
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hAb := Thm1Aux.abs_expPayoffFrom_le P D w hw phi π T 0 [] q
      (fun s _ hs => hrate s (by omega))
  have hBb := Thm1Aux.abs_expPayoffFrom_le P D w hw phi
      (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T 0 [] q'
      (fun s _ hs => hrate s (by omega))
  have htriv : (expPayoff w phi π T q
      - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q') / T ≤ 2 := by
    rw [div_le_iff₀ hTpos]
    have h1 := (abs_le.mp hAb).2
    have h2 := (abs_le.mp hBb).1
    unfold expPayoff
    linarith
  have hη : 2 ≤ T → 0 ≤ eta := by
    intro hT2
    have hT1pos : (0 : ℝ) < (T : ℝ) - 1 := by
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT2
      linarith
    have hs : 0 ≤ ∑ t ∈ range (T - 1), ∑ τ, |phi (t + 1) τ - phi t τ| := by positivity
    have := le_trans hs hvar
    by_contra hneg
    push Not at hneg
    have : ((T : ℝ) - 1) * eta < 0 := mul_neg_of_pos_of_neg hT1pos hneg
    linarith
  exact Thm1Aux.choose_batch C2 _ eta _ T K hm2 hK1 hT hη htriv
    (fun ΔT h1 h2' => h2 V Ty P D w phi T eta K sel ΔT hm hP hD hw hT hrate hα hvar hK2 h1 h2'
      hsel π q hq q' hq')
