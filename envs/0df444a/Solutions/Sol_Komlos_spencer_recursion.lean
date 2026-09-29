-- Prove2me | solution 1 for Komlos.spencer_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-11T03:44:46.014807+00:00
-- url     : https://prove2.me/submissions/b4c320e9-ee57-4585-9715-91d2418288c6

import Mathlib
import Definitions.Def_Komlos_model

open Finset Real

namespace SpencerRec

/-! ### Numerical facts -/

lemma log64_eq : Real.log 64 = 6 * Real.log 2 := by
  rw [show (64:ℝ) = 2 ^ (6:ℕ) by norm_num, Real.log_pow]
  norm_num

lemma log64_lb : (4:ℝ) ≤ Real.log 64 := by
  rw [log64_eq]; linarith [Real.log_two_gt_d9]

lemma log64_ub : Real.log 64 ≤ 41589 / 10000 := by
  rw [log64_eq]; linarith [Real.log_two_lt_d9]

lemma exp_five_ge : (146.41:ℝ) ≤ Real.exp 5 := by
  have h : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hpow : Real.exp 5 = Real.exp 1 ^ (5:ℕ) := by
    rw [show (5:ℝ) = ((5:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [hpow]
  have h2 : (7.389:ℝ) ≤ Real.exp 1 ^ (2:ℕ) := by nlinarith
  have h4 : (54.59:ℝ) ≤ Real.exp 1 ^ (4:ℕ) := by nlinarith [h2, pow_pos hpos 2, sq_nonneg (Real.exp 1)]
  nlinarith [h4, h, pow_pos hpos 4]

lemma exp_two_half_ge : (12.1:ℝ) ≤ Real.exp (5/2) := by
  have hpos : (0:ℝ) < Real.exp (5/2) := Real.exp_pos _
  have hsq : Real.exp (5/2) * Real.exp (5/2) = Real.exp 5 := by
    rw [← Real.exp_add]; norm_num
  by_contra hcon
  push_neg at hcon
  nlinarith [exp_five_ge, hsq, hpos]

lemma exp_twelve_half_ge : (254976:ℝ) ≤ Real.exp (25/2) := by
  have hpow : Real.exp (25/2) = Real.exp (5/2) ^ (5:ℕ) := by
    rw [show (25/2:ℝ) = ((5:ℕ):ℝ) * (5/2) by norm_num, Real.exp_nat_mul]
  rw [hpow]
  calc (254976:ℝ) ≤ (12.1:ℝ) ^ (5:ℕ) := by norm_num
    _ ≤ Real.exp (5/2) ^ (5:ℕ) := pow_le_pow_left₀ (by norm_num) exp_two_half_ge 5

/-! ### The bound function and its monotonicity -/

/-- The discrepancy budget for an active set of size `t` inside a ground set of size `N`. -/
noncomputable def Bd (N : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt t * (587 / 100 + (53 / 50) * Real.logb 64 (N / t))

lemma Bd_zero (N : ℝ) : Bd N 0 = 0 := by
  simp [Bd]

lemma mono_bound (N u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ N) :
    Real.sqrt u * (587 / 100 + (53 / 50) * Real.logb 64 (N / u))
      ≤ Real.sqrt v * (587 / 100 + (53 / 50) * Real.logb 64 (N / v)) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hN0 : 0 < N := lt_of_lt_of_le hv0 hv
  have hL1 : (4:ℝ) ≤ Real.log 64 := log64_lb
  have hLpos : (0:ℝ) < Real.log 64 := by linarith
  set d : ℝ := Real.log v - Real.log u with hd
  have hd0 : 0 ≤ d := by
    rw [hd, sub_nonneg]
    exact Real.log_le_log hu huv
  have hsv : Real.sqrt v = Real.sqrt u * Real.exp (d / 2) := by
    have hvu : v = u * Real.exp d := by
      rw [hd, Real.exp_sub, Real.exp_log hu, Real.exp_log hv0]
      field_simp
    rw [hvu, Real.sqrt_mul hu.le]
    congr 1
    have hhalf : Real.exp d = (Real.exp (d / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [hhalf, Real.sqrt_sq (Real.exp_pos _).le]
  set Y : ℝ := Real.logb 64 (N / v) with hY
  have hY0 : 0 ≤ Y := by
    rw [hY]
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_div_iff₀ hv0]; linarith
  have hXY : Real.logb 64 (N / u) = Y + d / Real.log 64 := by
    rw [hY, Real.logb, Real.logb,
      Real.log_div (ne_of_gt hN0) (ne_of_gt hu), Real.log_div (ne_of_gt hN0) (ne_of_gt hv0), hd]
    field_simp
    ring
  rw [hXY, hsv]
  have hsu : (0:ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hstep : 587 / 100 + (53 / 50) * (Y + d / Real.log 64)
      ≤ Real.exp (d / 2) * (587 / 100 + (53 / 50) * Y) := by
    have hexp : 1 + d / 2 ≤ Real.exp (d / 2) := by linarith [Real.add_one_le_exp (d / 2)]
    have hbase : (0:ℝ) ≤ 587 / 100 + (53 / 50) * Y := by nlinarith
    have hdL : d / Real.log 64 ≤ d / 4 := by
      rw [← sub_nonneg]
      have hsplit : d / 4 - d / Real.log 64 = d * (Real.log 64 - 4) / (4 * Real.log 64) := by
        field_simp
      rw [hsplit]
      exact div_nonneg (mul_nonneg hd0 (by linarith)) (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hexp hbase
    nlinarith [hmul, hdL, hd0, hY0, mul_nonneg hY0 hd0]
  calc Real.sqrt u * (587 / 100 + (53 / 50) * (Y + d / Real.log 64))
      ≤ Real.sqrt u * (Real.exp (d / 2) * (587 / 100 + (53 / 50) * Y)) :=
        mul_le_mul_of_nonneg_left hstep hsu.le
    _ = Real.sqrt u * Real.exp (d / 2) * (587 / 100 + (53 / 50) * Y) := by ring

/-- The entropy budget holds for the schedule `ν = 5 + (23/25) log_64 (N/s)`. -/
lemma budget_ok (N s : ℝ) (hs : 0 < s) (hsN : s ≤ N) :
    N * (2 * Real.exp (-((5 + (23/25) * Real.logb 64 (N / s)) ^ 2) / 2)
        * (3 * (5 + (23/25) * Real.logb 64 (N / s)) ^ 2 / 4 + 2))
      ≤ (2 / 3) * (1 / 64 : ℝ) ^ 2 * s := by
  have hN : (0:ℝ) < N := lt_of_lt_of_le hs hsN
  set X : ℝ := Real.logb 64 (N / s) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_div_iff₀ hs]; linarith
  have hLub : Real.log 64 ≤ 41589 / 10000 := log64_ub
  have hLlb : (4:ℝ) ≤ Real.log 64 := log64_lb
  -- `N = s * exp (log 64 * X)`
  have hNs : N = s * Real.exp (Real.log 64 * X) := by
    have h1 : (64:ℝ) ^ X = N / s :=
      Real.rpow_logb (by norm_num) (by norm_num) (div_pos hN hs)
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 64)] at h1
    rw [h1]
    field_simp
  set nu : ℝ := 5 + (23/25) * X with hnu
  set P : ℝ := 3 * nu ^ 2 / 4 + 2 with hP
  set u : ℝ := (4411/10000) * X + (529/1250) * X ^ 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hPpos : 0 < P := by rw [hP, hnu]; positivity
  -- the exponent
  have hexpo : Real.log 64 * X - nu ^ 2 / 2 ≤ -(25/2) - u := by
    rw [hnu, hu]
    nlinarith [hX0, hLub]
  set Q : ℝ := Real.exp (Real.log 64 * X - nu ^ 2 / 2) with hQ
  have hQpos : 0 < Q := Real.exp_pos _
  have hQu : Q * (1 + u) ≤ 1 / 254976 := by
    have h1 : Q ≤ Real.exp (-(25/2) - u) := Real.exp_le_exp.mpr hexpo
    have h2 : Real.exp (-(25/2) - u) = Real.exp (-(25/2)) * Real.exp (-u) := by
      rw [sub_eq_add_neg, Real.exp_add]
    have h3 : Real.exp (-u) * (1 + u) ≤ 1 := by
      have h4 : (1 + u) ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have h5 : Real.exp (-u) * Real.exp u = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-u), h4, h5]
    have h6 : Real.exp (-(25/2)) ≤ 1 / 254976 := by
      have h7 : (254976:ℝ) ≤ Real.exp (25/2) := exp_twelve_half_ge
      rw [Real.exp_neg]
      rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num
      linarith
    calc Q * (1 + u) ≤ Real.exp (-(25/2)) * Real.exp (-u) * (1 + u) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = Real.exp (-(25/2)) * (Real.exp (-u) * (1 + u)) := by ring
      _ ≤ Real.exp (-(25/2)) * 1 :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg _)
      _ ≤ 1 / 254976 := by rw [mul_one]; exact h6
  have hPu : 12288 * P ≤ 254976 * (1 + u) := by
    rw [hP, hnu, hu]
    nlinarith [hX0, sq_nonneg X]
  -- combine
  have hprod : Q * (1 + u) * (12288 * P) ≤ (1 / 254976) * (254976 * (1 + u)) :=
    mul_le_mul hQu hPu (by positivity) (by norm_num)
  have hfin : 12288 * (Q * P) ≤ 1 := by
    have hu1 : (0:ℝ) < 1 + u := by linarith
    have hstep : 12288 * (Q * P) * (1 + u) ≤ 1 * (1 + u) := by nlinarith [hprod]
    exact le_of_mul_le_mul_right hstep hu1
  have hgoal : N * (2 * Real.exp (-(nu ^ 2) / 2) * P) = 2 * s * (Q * P) := by
    have hq : Q = Real.exp (Real.log 64 * X) * Real.exp (-(nu ^ 2) / 2) := by
      rw [hQ, ← Real.exp_add]; congr 1; ring
    rw [hNs, hq]; ring
  rw [hgoal]
  nlinarith [hfin, hs]

/-- The one-step bookkeeping inequality. -/
lemma step_ineq (s : ℝ) (X : ℝ) (hX : 0 ≤ X) :
    (5 + (23/25) * X) * Real.sqrt s + (Real.sqrt s / 8) * (587/100 + (53/50) * (X + 1))
      ≤ Real.sqrt s * (587/100 + (53/50) * X) := by
  nlinarith [Real.sqrt_nonneg s, hX]

/-- The recursion: repeatedly partially colour, until nothing is left. -/
theorem main (n : ℕ) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (pcl : ∀ (n : ℕ) (A : Fin n → Fin n → ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∀ (T : Finset (Fin n)), 0 < T.card → ∀ θ ν : ℝ, 0 < θ → θ ≤ 1 / 2 → 2 ≤ ν →
        (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2))
            ≤ (2 / 3) * θ ^ 2 * (T.card : ℝ) →
        ∃ χ : Fin n → ℝ,
          (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
          (∀ j, j ∉ T → χ j = 0) ∧
          (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => χ j ≠ 0)).card : ℝ) ∧
          (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt (T.card : ℝ))) :
    ∀ t : ℕ, ∀ T : Finset (Fin n), T.card = t →
      ∃ χ : Fin n → ℝ, (∀ j ∈ T, χ j = 1 ∨ χ j = -1) ∧ (∀ j, j ∉ T → χ j = 0) ∧
        ∀ i, |∑ j ∈ T, A i j * χ j| ≤ Bd (n : ℝ) t := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro T hT
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      have hTe : T = ∅ := Finset.card_eq_zero.mp hT
      refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
      · intro j hj
        rw [hTe] at hj
        exact absurd hj (Finset.notMem_empty j)
      · intro i
        rw [hTe, Bd_zero]
        simp
    · have hTcard : 0 < T.card := by rw [hT]; exact hpos
      have hts : (0:ℝ) < (t:ℝ) := by exact_mod_cast hpos
      have htn : (t:ℝ) ≤ (n:ℝ) := by
        have hle : T.card ≤ n := by simpa using Finset.card_le_univ T
        rw [← hT]; exact_mod_cast hle
      have hcast : ((T.card : ℕ) : ℝ) = (t:ℝ) := by rw [hT]
      set X : ℝ := Real.logb 64 ((n:ℝ) / (t:ℝ)) with hX
      have hX0 : 0 ≤ X := by
        rw [hX]
        refine Real.logb_nonneg (by norm_num) ?_
        rw [le_div_iff₀ hts]; linarith
      set nu : ℝ := 5 + (23/25) * X with hnu
      have hnu2 : (2:ℝ) ≤ nu := by rw [hnu]; nlinarith
      have hbud : (n : ℝ) * (2 * Real.exp (-(nu ^ 2) / 2) * (3 * nu ^ 2 / 4 + 2))
          ≤ (2 / 3) * (1/64 : ℝ) ^ 2 * (T.card : ℝ) := by
        rw [hcast, hnu, hX]
        exact budget_ok (n:ℝ) (t:ℝ) hts htn
      obtain ⟨χ₁, hval₁, hzero₁, hcount₁, hdisc₁⟩ :=
        pcl n A h01 T hTcard (1/64) nu (by norm_num) (by norm_num) hnu2 hbud
      set T' : Finset (Fin n) := T.filter (fun j => χ₁ j = 0) with hT'def
      have hT'sub : T' ⊆ T := by rw [hT'def]; exact Finset.filter_subset _ _
      have hcompl : (T.filter (fun j => χ₁ j ≠ 0)).card + T'.card = T.card := by
        rw [hT'def]
        have hfe : T.filter (fun j => χ₁ j = 0) = T.filter (fun j => ¬ (χ₁ j ≠ 0)) := by
          refine Finset.filter_congr (fun j _ => ?_)
          simp
        rw [hfe]
        exact Finset.card_filter_add_card_filter_not (s := T) (fun j => χ₁ j ≠ 0)
      have hT'card : (T'.card : ℝ) ≤ (t:ℝ) / 64 := by
        have h1 : ((T.filter (fun j => χ₁ j ≠ 0)).card : ℝ) + (T'.card : ℝ) = (t:ℝ) := by
          rw [← hcast]; exact_mod_cast hcompl
        have h2 := hcount₁
        rw [hcast] at h2
        linarith
      have hT'lt : T'.card < t := by
        have hlt : (T'.card : ℝ) < (t:ℝ) := by linarith
        exact_mod_cast hlt
      obtain ⟨χ₂, hval₂, hzero₂, hdisc₂⟩ := ih T'.card hT'lt T' rfl
      refine ⟨fun j => χ₁ j + χ₂ j, ?_, ?_, ?_⟩
      · intro j hj
        by_cases hz : χ₁ j = 0
        · have hjT' : j ∈ T' := by
            rw [hT'def]; exact Finset.mem_filter.mpr ⟨hj, hz⟩
          rcases hval₂ j hjT' with h | h
          · left; simp [hz, h]
          · right; simp [hz, h]
        · have hjT' : j ∉ T' := by
            rw [hT'def]
            intro hc
            exact hz (Finset.mem_filter.mp hc).2
          have h2 := hzero₂ j hjT'
          rcases hval₁ j with h | h | h
          · left; simp [h, h2]
          · right; simp [h, h2]
          · exact absurd h hz
      · intro j hj
        have h1 := hzero₁ j hj
        have h2 := hzero₂ j (fun hc => hj (hT'sub hc))
        simp [h1, h2]
      · intro i
        have hsub : ∑ j ∈ T', A i j * χ₂ j = ∑ j ∈ T, A i j * χ₂ j :=
          Finset.sum_subset hT'sub (fun x _ hx => by rw [hzero₂ x hx]; ring)
        have hsplit : ∑ j ∈ T, A i j * (χ₁ j + χ₂ j)
            = (∑ j ∈ T, A i j * χ₁ j) + ∑ j ∈ T', A i j * χ₂ j := by
          rw [hsub, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        have h1 : |∑ j ∈ T, A i j * χ₁ j| ≤ nu * Real.sqrt (t:ℝ) := by
          have hd := hdisc₁ i
          rwa [hcast] at hd
        have h2 : |∑ j ∈ T', A i j * χ₂ j| ≤ Bd (n:ℝ) T'.card := hdisc₂ i
        have hsq8 : Real.sqrt ((t:ℝ)/64) = Real.sqrt (t:ℝ) / 8 := by
          have h64 : ((t:ℝ)/64) = (t:ℝ) * (1/8:ℝ)^2 := by ring
          rw [h64, Real.sqrt_mul (le_of_lt hts), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/8)]
          ring
        have htne : (t:ℝ) ≠ 0 := ne_of_gt hts
        have hnt0 : (0:ℝ) < (n:ℝ)/(t:ℝ) := div_pos (lt_of_lt_of_le hts htn) hts
        have hself : Real.logb 64 (64:ℝ) = 1 := by
          simp
        have hlogb : Real.logb 64 ((n:ℝ) / ((t:ℝ)/64)) = X + 1 := by
          have hrw : (n:ℝ) / ((t:ℝ)/64) = ((n:ℝ)/(t:ℝ)) * 64 := by
            field_simp
          rw [hrw, Real.logb_mul (ne_of_gt hnt0) (by norm_num), hself, hX]
        have h3 : Bd (n:ℝ) T'.card
            ≤ (Real.sqrt (t:ℝ) / 8) * (587/100 + (53/50) * (X + 1)) := by
          rcases Nat.eq_zero_or_pos T'.card with hz | hz
          · rw [hz, Bd_zero]
            have : (0:ℝ) ≤ Real.sqrt (t:ℝ) / 8 := by positivity
            nlinarith [hX0, Real.sqrt_nonneg (t:ℝ)]
          · have hupos : (0:ℝ) < (T'.card : ℝ) := by exact_mod_cast hz
            have hvle : (t:ℝ)/64 ≤ (n:ℝ) := by linarith
            have hmb := mono_bound (n:ℝ) (T'.card : ℝ) ((t:ℝ)/64) hupos hT'card hvle
            rw [hsq8, hlogb] at hmb
            exact hmb
        have h4 := step_ineq (t:ℝ) X hX0
        have h5 : Bd (n:ℝ) t = Real.sqrt (t:ℝ) * (587/100 + (53/50) * X) := by
          rw [Bd, ← hX]
        rw [hsplit, h5]
        calc |(∑ j ∈ T, A i j * χ₁ j) + ∑ j ∈ T', A i j * χ₂ j|
            ≤ |∑ j ∈ T, A i j * χ₁ j| + |∑ j ∈ T', A i j * χ₂ j| := abs_add_le _ _
          _ ≤ nu * Real.sqrt (t:ℝ) + (Real.sqrt (t:ℝ) / 8) * (587/100 + (53/50) * (X + 1)) := by
              linarith
          _ ≤ Real.sqrt (t:ℝ) * (587/100 + (53/50) * X) := by rw [hnu]; linarith [h4]

end SpencerRec

theorem solution
    (pcl : ∀ (n : ℕ) (A : Fin n → Fin n → ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∀ (T : Finset (Fin n)), 0 < T.card → ∀ θ ν : ℝ, 0 < θ → θ ≤ 1 / 2 → 2 ≤ ν →
        (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2))
            ≤ (2 / 3) * θ ^ 2 * (T.card : ℝ) →
        ∃ χ : Fin n → ℝ,
          (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
          (∀ j, j ∉ T → χ j = 0) ∧
          (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => χ j ≠ 0)).card : ℝ) ∧
          (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt (T.card : ℝ)))
    (fin : ∀ (n : ℕ), 0 < n → ∀ (A : Fin n → Fin n → ℝ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      ∀ (T : Finset (Fin n)),
        ∃ χ : Fin n → ℝ,
          (∀ j, j ∈ T → (χ j = 1 ∨ χ j = -1)) ∧
          (∀ j, j ∉ T → χ j = 0) ∧
          (∀ i, |∑ j ∈ T, A i j * χ j|
              ≤ Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n))))
    (n : ℕ) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, Komlos.IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n := by
  obtain ⟨χ, hval, hzero, hdisc⟩ :=
    SpencerRec.main n A h01 pcl n Finset.univ (by simp)
  refine ⟨χ, fun i => hval i (Finset.mem_univ i), ?_⟩
  intro i
  refine le_trans (hdisc i) ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp [SpencerRec.Bd]
  · have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
    have hdiv : ((n:ℝ)) / ((n:ℝ)) = 1 := div_self (ne_of_gt hn)
    rw [SpencerRec.Bd, hdiv, Real.logb_one]
    nlinarith [Real.sqrt_nonneg (n:ℝ)]
