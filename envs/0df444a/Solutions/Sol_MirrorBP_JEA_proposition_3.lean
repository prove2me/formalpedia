-- Prove2me | solution 1 for MirrorBP.JEA.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:54:19.102658+00:00
-- url     : https://prove2.me/submissions/607fee3b-e275-4554-976c-32f57c871a25

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP
import Theorems.Thm_MirrorBP_JEA_lemma_1
import Theorems.Thm_MirrorBP_JEA_lemma_3

namespace MirrorBP.JEA.Prop3Aux

open Finset MirrorBP.JEA

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

theorem fMBP_strictMono (m : ℕ) (hm : 0 < m) : StrictMonoOn (fMBP m) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold fMBP
  have h1 : b ^ (-(1 / 2 : ℝ)) < a ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_lt_rpow_of_neg ha hab (by norm_num)
  have h2 : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  nlinarith

theorem fMBP_contDiff (m : ℕ) : ContDiffOn ℝ 1 (fMBP m) (Set.Ioi 0) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  unfold fMBP
  exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hx))

/-- The antiderivative `F₁(x) = −2√m √x` of the congestion function (8). -/
noncomputable def F1 (m : ℕ) (x : ℝ) : ℝ := -2 * Real.sqrt m * Real.sqrt x

theorem F1_deriv (m : ℕ) (x : ℝ) (hx : 0 < x) : HasDerivAt (F1 m) (fMBP m x) x := by
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul (-2 * Real.sqrt m)
  have e : fMBP m x = -2 * Real.sqrt m * (1 / (2 * Real.sqrt x)) := by
    unfold fMBP
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
    have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    field_simp
  rw [e]
  exact h

theorem Kt_pos (m K : ℕ) (hK : 1 ≤ K) : 0 < Kt m K := by
  unfold Kt
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have : 0 ≤ (m : ℝ) * Real.sqrt K := by positivity
  linarith

theorem qbar_pos (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (j : V) : 0 < qbar K q j := by
  unfold qbar
  have : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have : (0 : ℝ) ≤ q j := by positivity
  exact div_pos (by linarith) (Kt_pos _ K hK)

theorem qbar_sum (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (hq : q ∈ StateSpace V K) :
    ∑ j, qbar K q j = 1 := by
  unfold qbar
  rw [← sum_div, sum_add_distrib, div_eq_one_iff_eq (Kt_pos _ K hK).ne']
  simp only [StateSpace, Set.mem_setOf_eq] at hq
  unfold Kt
  rw [sum_const, card_univ, nsmul_eq_mul]
  congr 1
  exact_mod_cast hq

theorem Fpot_bounds (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (hq : q ∈ StateSpace V K)
    (hV : 0 < Fintype.card V) :
    -2 * (Fintype.card V : ℝ) ≤ Fpot (F1 (Fintype.card V)) (qbar K q) ∧
      Fpot (F1 (Fintype.card V)) (qbar K q) ≤ 0 := by
  have hm : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hV
  set m : ℝ := (Fintype.card V : ℝ)
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hsm2 : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  unfold Fpot F1
  constructor
  · -- √x ≤ (x + 1/m) √m / 2
    have key : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ≤ (x + 1 / m) * Real.sqrt m / 2 := by
      intro x hx
      have hsx := Real.sq_sqrt hx
      have h0 : 0 ≤ (Real.sqrt x * Real.sqrt m - 1) ^ 2 := sq_nonneg _
      have : (x + 1 / m) * Real.sqrt m / 2 * Real.sqrt m = (x * m + 1) / 2 := by
        rw [show (x + 1 / m) * Real.sqrt m / 2 * Real.sqrt m
          = (x + 1 / m) * (Real.sqrt m * Real.sqrt m) / 2 by ring, hsm2]
        field_simp
      have hxm : Real.sqrt x * Real.sqrt m ≤ (x * m + 1) / 2 := by nlinarith
      rw [← this] at hxm
      exact le_of_mul_le_mul_right hxm hsm
    have hsum : ∑ j, Real.sqrt (qbar K q j) ≤ Real.sqrt m := by
      calc ∑ j, Real.sqrt (qbar K q j) ≤ ∑ j, (qbar K q j + 1 / m) * Real.sqrt m / 2 :=
            sum_le_sum fun j _ => key _ (qbar_pos K hK q j).le
        _ = Real.sqrt m := by
            rw [← sum_div, ← sum_mul, sum_add_distrib, qbar_sum K hK q hq]
            simp only [sum_const, card_univ, nsmul_eq_mul]
            field_simp
            ring
    have : ∑ j, -2 * Real.sqrt m * Real.sqrt (qbar K q j)
        = -2 * Real.sqrt m * ∑ j, Real.sqrt (qbar K q j) := by rw [mul_sum]
    rw [this]
    nlinarith
  · apply sum_nonpos
    intro j _
    have : 0 ≤ Real.sqrt (qbar K q j) := Real.sqrt_nonneg _
    nlinarith

theorem mbpDecision_feasible (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ)
    (q : V → ℕ) (τ : Ty) : Feasible P D τ q (mbpDecision w f K sel q τ) := by
  unfold mbpDecision
  split_ifs with h
  · exact ⟨(hmem q τ).1, (hmem q τ).2, h.2⟩
  · trivial

theorem step_mem (P D : Ty → Finset V) (K : ℕ) (τ : Ty) (q : V → ℕ) (d : Decision V)
    (hf : Feasible P D τ q d) (hq : q ∈ StateSpace V K) : step q d ∈ StateSpace V K := by
  rcases d with _ | ⟨j, k⟩
  · simpa [step] using hq
  · have hj : 0 < q j := hf.2.2
    simp only [StateSpace, Set.mem_setOf_eq] at hq ⊢
    simp only [step, Pi.add_apply, Pi.sub_apply]
    rw [sum_add_distrib, Finset.sum_tsub_distrib]
    · simp [Finset.sum_pi_single', hq]
      have : q j ≤ ∑ i, q i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (mem_univ j)
      omega
    · intro i _
      by_cases hij : i = j
      · subst hij; simp; omega
      · simp [Pi.single_apply, hij]

theorem mbp_succ (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ)
    (phi : ℕ → Ty → ℝ) (n t : ℕ) (h : History V Ty) (q : V → ℕ) :
    expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) (n + 1) t h q
      = ∑ τ, phi t τ * (pay w τ (mbpDecision w f K sel q τ)
          + expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1)
              (h ++ [(q, τ, mbpDecision w f K sel q τ)]) (step q (mbpDecision w f K sel q τ))) := by
  rw [expPayoffFrom]
  apply sum_congr rfl
  intro τ _
  congr 1
  simp [mbpPolicy]

/-- Lyapunov telescoping (proof of Proposition 3): the one-period drift bound summed over `n`
periods. -/
theorem telescope (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f F₁ : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ)
    (phi : ℕ → Ty → ℝ) (T : ℕ) (A M ε : ℝ)
    (hrate : ∀ t < T, IsRate (phi t))
    (hlow : ∀ q ∈ StateSpace V K, -M ≤ Fpot F₁ (qbar K q))
    (hstep : ∀ t < T, ∀ q ∈ StateSpace V K,
      Wspp P D w (phi t) - ∑ τ, phi t τ * pay w τ (mbpDecision w f K sel q τ)
        ≤ A * (Fpot F₁ (qbar K q)
            - ∑ τ, phi t τ * Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + ε)
    (hA : 0 ≤ A) :
    ∀ n t h q, t + n ≤ T → q ∈ StateSpace V K →
      ∑ s ∈ range n, Wspp P D w (phi (t + s))
          - expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n t h q
        ≤ A * Fpot F₁ (qbar K q) + A * M + n * ε := by
  intro n
  induction n with
  | zero =>
    intro t h q _ hq
    simp only [range_zero, sum_empty, expPayoffFrom, sub_zero, Nat.cast_zero, zero_mul, add_zero]
    have := mul_le_mul_of_nonneg_left (hlow q hq) hA
    linarith
  | succ n ih =>
    intro t h q htn hq
    rw [mbp_succ, sum_range_succ']
    have hrt := hrate t (by omega)
    set dec := fun τ => mbpDecision w f K sel q τ
    have hst := hstep t (by omega) q hq
    have hih : ∀ τ, ∑ s ∈ range n, Wspp P D w (phi (t + 1 + s))
        - expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1) (h ++ [(q, τ, dec τ)])
            (step q (dec τ))
        ≤ A * Fpot F₁ (qbar K (step q (dec τ))) + A * M + n * ε := fun τ =>
      ih (t + 1) _ _ (by omega) (step_mem P D K τ q _ (mbpDecision_feasible P D w f K sel hmem q τ) hq)
    -- average the inductive bound against phi t
    have havg : ∑ τ, phi t τ * (∑ s ∈ range n, Wspp P D w (phi (t + 1 + s))
        - expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1) (h ++ [(q, τ, dec τ)])
            (step q (dec τ)))
        ≤ ∑ τ, phi t τ * (A * Fpot F₁ (qbar K (step q (dec τ))) + A * M + n * ε) :=
      sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hih τ) (hrt.1 τ)
    have e1 : ∑ τ, phi t τ * (∑ s ∈ range n, Wspp P D w (phi (t + 1 + s))
        - expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1) (h ++ [(q, τ, dec τ)])
            (step q (dec τ)))
        = ∑ s ∈ range n, Wspp P D w (phi (t + 1 + s))
          - ∑ τ, phi t τ * expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1)
              (h ++ [(q, τ, dec τ)]) (step q (dec τ)) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hrt.2, one_mul]
    have e2 : ∑ τ, phi t τ * (A * Fpot F₁ (qbar K (step q (dec τ))) + A * M + n * ε)
        = A * ∑ τ, phi t τ * Fpot F₁ (qbar K (step q (dec τ))) + A * M + n * ε := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hrt.2, one_mul, mul_sum]
      congr 2
      apply sum_congr rfl; intro τ _; ring
    have e3 : ∑ τ, phi t τ * (pay w τ (dec τ)
        + expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1) (h ++ [(q, τ, dec τ)])
            (step q (dec τ)))
        = ∑ τ, phi t τ * pay w τ (dec τ)
          + ∑ τ, phi t τ * expPayoffFrom w phi (mbpPolicy P D w f K sel hmem) n (t + 1)
              (h ++ [(q, τ, dec τ)]) (step q (dec τ)) := by
      simp only [mul_add, sum_add_distrib]
    have e4 : ∑ s ∈ range n, Wspp P D w (phi (t + (s + 1)))
        = ∑ s ∈ range n, Wspp P D w (phi (t + 1 + s)) := by
      apply sum_congr rfl; intro s _; rw [show t + (s + 1) = t + 1 + s by ring]
    simp only [Nat.add_zero] at *
    rw [e3, e4]
    push_cast
    linarith

end MirrorBP.JEA.Prop3Aux

open Finset MirrorBP.JEA

theorem solution :
    ∃ C : ℝ, ∃ c : ℝ, ∃ N : ℕ,
      ∀ (V Ty : Type) [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
        (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (phi : ℕ → Ty → ℝ) (T K : ℕ)
        (sel : (V → ℕ) → Ty → V × V),
        1 < Fintype.card V → (∀ τ, (P τ).Nonempty) → (∀ τ, (D τ).Nonempty) →
        (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1) →
        0 < T → (∀ t < T, IsRate (phi t)) → (∀ t < T, 0 < alphaConn P D (phi t)) →
        c * ((Fintype.card V : ℝ) + 1 / alphaMin P D phi T) ^ N ≤ (K : ℝ) →
        ∀ hsel : IsArgmaxSel P D w (fMBP (Fintype.card V)) K sel,
        ∀ q' ∈ StateSpace V K,
          (1 / (T : ℝ)) * ∑ t ∈ range T, Wspp P D w (phi t)
              - expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q' / T
            ≤ C * (Fintype.card V : ℝ) * ((K : ℝ) / T) + C * (Fintype.card V : ℝ) ^ 2 / K := by
  obtain ⟨C3, hC3, c3, N3, h3⟩ := MirrorBP.JEA.lemma_3
  refine ⟨C3 + 4, max c3 1, N3 + 2, ?_⟩
  intro V Ty _ _ _ _ P D w phi T K sel hm hP hD hw hT hrate hα hK hsel q' hq'
  have hV : 0 < Fintype.card V := by omega
  have hm2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
    have : (2 : ℕ) ≤ Fintype.card V := hm
    exact_mod_cast this
  have hne : (range T).Nonempty := ⟨0, by simp [hT]⟩
  have hαpos : 0 < alphaMin P D phi T := by
    unfold alphaMin
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro t ht
    exact hα t (by simpa using ht)
  have hαle : ∀ t < T, alphaMin P D phi T ≤ alphaConn P D (phi t) := by
    intro t ht
    unfold alphaMin
    rw [dif_pos hne]
    exact Finset.inf'_le _ (by simpa using ht)
  set m : ℝ := (Fintype.card V : ℝ) with hmdef
  set x : ℝ := m + 1 / alphaMin P D phi T with hxdef
  have hxm : m ≤ x := by
    have : 0 < 1 / alphaMin P D phi T := by positivity
    linarith
  have hx1 : 1 ≤ x := by linarith
  have hxN : 1 ≤ x ^ N3 := one_le_pow₀ hx1
  have hxN2 : x ^ N3 ≤ x ^ (N3 + 2) := pow_le_pow_right₀ hx1 (by omega)
  have hc1 : (1 : ℝ) ≤ max c3 1 := le_max_right _ _
  have hKm : m ^ 2 ≤ K := by
    have h1 : m ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hxm 2
    have h2 : x ^ 2 ≤ x ^ (N3 + 2) := by
      rw [pow_add]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ x by linarith) 2]
    have h3' : x ^ (N3 + 2) ≤ max c3 1 * x ^ (N3 + 2) := by
      have : 0 ≤ x ^ (N3 + 2) := by positivity
      nlinarith
    linarith
  have hK1r : (1 : ℝ) ≤ K := by nlinarith
  have hK1 : 1 ≤ K := by exact_mod_cast hK1r
  have hKpos : (0 : ℝ) < K := by linarith
  -- the threshold of Lemma 3 holds in every period
  have hKt : ∀ t < T, c3 * (m + 1 / alphaConn P D (phi t)) ^ N3 ≤ (K : ℝ) := by
    intro t ht
    have hb : m + 1 / alphaConn P D (phi t) ≤ x := by
      have := one_div_le_one_div_of_le hαpos (hαle t ht)
      linarith
    have hb0 : 0 ≤ m + 1 / alphaConn P D (phi t) := by
      have := hα t ht
      positivity
    calc c3 * (m + 1 / alphaConn P D (phi t)) ^ N3
        ≤ max c3 1 * (m + 1 / alphaConn P D (phi t)) ^ N3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hb0 _)
      _ ≤ max c3 1 * x ^ N3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb _) (by linarith)
      _ ≤ max c3 1 * x ^ (N3 + 2) := mul_le_mul_of_nonneg_left hxN2 (by linarith)
      _ ≤ K := hK
  have hKtpos := Prop3Aux.Kt_pos (Fintype.card V) K hK1
  -- one-period drift bound (Lemmas 1 and 3)
  have hstep : ∀ t < T, ∀ q ∈ StateSpace V K,
      Wspp P D w (phi t) - ∑ τ, phi t τ * pay w τ (mbpDecision w (fMBP (Fintype.card V)) K sel q τ)
        ≤ Kt (Fintype.card V) K * (Fpot (Prop3Aux.F1 (Fintype.card V)) (qbar K q)
            - ∑ τ, phi t τ * Fpot (Prop3Aux.F1 (Fintype.card V))
                (qbar K (step q (mbpDecision w (fMBP (Fintype.card V)) K sel q τ))))
          + C3 * m ^ 2 / Kt (Fintype.card V) K := by
    intro t ht q hq
    obtain ⟨B, hB, hB2⟩ := h3 V Ty P D w (phi t) K q hm hP hD hw (hrate t ht) (hα t ht) (hKt t ht) hq
    have l1 := MirrorBP.JEA.lemma_1 P D w hm hP hD hw (phi t) (hrate t ht) K hK1 q hq
      (fMBP (Fintype.card V)) (Prop3Aux.F1 (Fintype.card V)) (Prop3Aux.fMBP_strictMono _ hV)
      (Prop3Aux.fMBP_contDiff _) (Prop3Aux.F1_deriv _) sel hsel B hB
    linarith
  have tel := Prop3Aux.telescope P D w (fMBP (Fintype.card V)) (Prop3Aux.F1 (Fintype.card V)) K sel
    hsel.mem phi T (Kt (Fintype.card V) K) (2 * m) (C3 * m ^ 2 / Kt (Fintype.card V) K) hrate
    (fun q hq => (Prop3Aux.Fpot_bounds K hK1 q hq hV).1.trans' (by linarith))
    hstep hKtpos.le T 0 [] q' (by simp) hq'
  have hF0 := (Prop3Aux.Fpot_bounds K hK1 q' hq' hV).2
  simp only [zero_add] at tel
  -- Kt ≤ 2K and the last term
  have hKt2 : Kt (Fintype.card V) K ≤ 2 * K := by
    unfold Kt
    have hs : m ≤ Real.sqrt K := Real.le_sqrt_of_sq_le hKm
    have : m * Real.sqrt K ≤ Real.sqrt K * Real.sqrt K :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hKpos.le] at this
    rw [← hmdef]
    linarith
  have hKtK : (K : ℝ) ≤ Kt (Fintype.card V) K := by
    unfold Kt
    have : 0 ≤ (Fintype.card V : ℝ) * Real.sqrt K := by positivity
    linarith
  have hε : C3 * m ^ 2 / Kt (Fintype.card V) K ≤ C3 * m ^ 2 / K :=
    div_le_div_of_nonneg_left (by positivity) hKpos hKtK
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set Sw := ∑ t ∈ range T, Wspp P D w (phi t)
  set E := expPayoff w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem) T q'
  have hE : E = expPayoffFrom w phi (mbpPolicy P D w (fMBP (Fintype.card V)) K sel hsel.mem)
      T 0 [] q' := rfl
  rw [← hE] at tel
  have hmain : Sw - E ≤ 4 * m * K + T * (C3 * m ^ 2 / K) := by
    have a1 : Kt (Fintype.card V) K * Fpot (Prop3Aux.F1 (Fintype.card V)) (qbar K q') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hKtpos.le hF0
    have a2 : Kt (Fintype.card V) K * (2 * m) ≤ 2 * K * (2 * m) :=
      mul_le_mul_of_nonneg_right hKt2 (by linarith)
    have a3 : (T : ℝ) * (C3 * m ^ 2 / Kt (Fintype.card V) K) ≤ T * (C3 * m ^ 2 / K) :=
      mul_le_mul_of_nonneg_left hε hTpos.le
    linarith
  have e : 1 / (T : ℝ) * Sw - E / T = (Sw - E) / T := by field_simp
  rw [e, div_le_iff₀ hTpos]
  have r1 : (4 * m * K + T * (C3 * m ^ 2 / K))
      ≤ ((C3 + 4) * m * ((K : ℝ) / T) + (C3 + 4) * m ^ 2 / K) * T := by
    have : ((C3 + 4) * m * ((K : ℝ) / T) + (C3 + 4) * m ^ 2 / K) * T
        = (C3 + 4) * m * K + T * ((C3 + 4) * m ^ 2 / K) := by field_simp
    rw [this]
    have b1 : 4 * m * K ≤ (C3 + 4) * m * K := by
      have : 0 ≤ C3 * m * K := by positivity
      nlinarith
    have b2 : T * (C3 * m ^ 2 / K) ≤ T * ((C3 + 4) * m ^ 2 / K) := by
      apply mul_le_mul_of_nonneg_left _ hTpos.le
      apply div_le_div_of_nonneg_right _ hKpos.le
      nlinarith [sq_nonneg m]
    linarith
  linarith
