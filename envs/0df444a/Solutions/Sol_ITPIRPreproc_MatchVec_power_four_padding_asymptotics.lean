-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.power_four_padding_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:03.838635+00:00
-- url     : https://prove2.me/submissions/9e0a311f-ae96-4502-86e1-46420a98f893

import Definitions.Def_ITPIRPreproc_MatchVec_PowerFourPadding

open scoped ENNReal
open Filter Topology

namespace ITPIRPreproc.MatchVec

private lemma padHeight_tendsto : Tendsto padHeight atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨4 ^ b, fun n hn => ?_⟩
  have hmono := Nat.clog_mono_right 4 hn
  rw [Nat.clog_pow 4 b (by norm_num)] at hmono
  exact hmono.trans (le_max_right _ _)

private lemma le_padLength (n : ℕ) : n ≤ padLength n := by
  have h := Nat.le_pow_clog (b := 4) (by norm_num) n
  exact h.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

private lemma padLength_le (n : ℕ) (hn : 1 ≤ n) : padLength n ≤ 64 * n := by
  by_cases hc : Nat.clog 4 n ≤ 3
  · have hsmall : n ≤ 64 := by
      calc
        n ≤ 4 ^ Nat.clog 4 n := Nat.le_pow_clog (by norm_num) n
        _ ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hc
        _ = 64 := by norm_num
    simp [padLength, padHeight, max_eq_left hc]
    omega
  · have hc' : 3 < Nat.clog 4 n := Nat.lt_of_not_ge hc
    have hn4 : 4 < n := by
      by_contra! hle
      have : Nat.clog 4 n ≤ 1 := Nat.clog_le_of_le_pow (by
        calc n ≤ 4 := hle
             _ = 4 ^ 1 := by norm_num)
      omega
    have hk : 0 < Nat.clog 4 n := Nat.clog_pos (by norm_num) (by omega)
    have hprev : 4 ^ (Nat.clog 4 n - 1) < n := by
      by_contra! hle
      have := Nat.clog_le_of_le_pow (b := 4) hle
      omega
    have hmax : padHeight n = Nat.clog 4 n := max_eq_right (by omega)
    rw [padLength, hmax]
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hk'] at hprev ⊢
    simp only [Nat.succ_sub_one, pow_succ] at hprev ⊢
    omega

private lemma main_rpow_bound {η : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |η (padHeight n)| ≤ B) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (padLength n : ℝ) ^ (a + η (padHeight n)) ≤
      (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (a + |η (padHeight n)|) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ padLength n := hn.trans (le_padLength n)
  have hNR : (1 : ℝ) ≤ padLength n := by exact_mod_cast hN
  have hNupR : (padLength n : ℝ) ≤ 64 * n := by exact_mod_cast padLength_le n hn
  have hexp : a + η (padHeight n) ≤ a + |η (padHeight n)| := by
    linarith [le_abs_self (η (padHeight n))]
  calc
    (padLength n : ℝ) ^ (a + η (padHeight n))
        ≤ (padLength n : ℝ) ^ (a + |η (padHeight n)|) :=
      Real.rpow_le_rpow_of_exponent_le hNR hexp
    _ ≤ ((64 : ℝ) * n) ^ (a + |η (padHeight n)|) := by
      apply Real.rpow_le_rpow (by positivity) hNupR
      positivity
    _ = (64 : ℝ) ^ (a + |η (padHeight n)|) * (n : ℝ) ^ (a + |η (padHeight n)|) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    _ ≤ (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (a + |η (padHeight n)|) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have := hB n
        linarith)

private lemma length_overhead_bound {η : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |η (padHeight n)| ≤ B) (n : ℕ) (hn : 1 ≤ n) :
    (padLength n : ℝ) ≤
      (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (1 + |η (padHeight n)|) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNupR : (padLength n : ℝ) ≤ 64 * n := by exact_mod_cast padLength_le n hn
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h64 : (64 : ℝ) ≤ (64 : ℝ) ^ (1 + B) := by
    calc
      (64 : ℝ) = 64 ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ 64 ^ (1 + B) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hnpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + |η (padHeight n)|) := by
    calc
      (n : ℝ) = n ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ n ^ (1 + |η (padHeight n)|) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith [abs_nonneg (η (padHeight n))])
  calc
    (padLength n : ℝ) ≤ 64 * n := hNupR
    _ ≤ (64 : ℝ) ^ (1 + B) * n := by gcongr
    _ ≤ (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (1 + |η (padHeight n)|) := by
      gcongr

private lemma quarter_rpow_bound {η : ℕ → ℝ} {B : ℝ}
    (hB : ∀ n, |η (padHeight n)| ≤ B)
    (a : ℝ) (ha : (1 : ℝ) / 4 ≤ a) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤
      (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (a + |η (padHeight n)|) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hR : (1 : ℝ) ≤ (64 : ℝ) ^ (1 + B) := by
    calc
      (1 : ℝ) = 64 ^ (0 : ℝ) := by norm_num
      _ ≤ 64 ^ (1 + B) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    (n : ℝ) ^ ((1 : ℝ) / 4) ≤ (n : ℝ) ^ (a + |η (padHeight n)|) := by
      apply Real.rpow_le_rpow_of_exponent_le hnR
      linarith [abs_nonneg (η (padHeight n))]
    _ = 1 * (n : ℝ) ^ (a + |η (padHeight n)|) := by ring
    _ ≤ (64 : ℝ) ^ (1 + B) * (n : ℝ) ^ (a + |η (padHeight n)|) := by
      exact mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg (by positivity) _)

end ITPIRPreproc.MatchVec

open ITPIRPreproc.MatchVec

/-- Proof of the real-asymptotic child of the power-of-four padding reduction. -/
theorem solution
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0)) (K : ℝ) (c : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
        BudgetLE
          (adapterBudget A n (powerFourBudget K c η (padHeight n) lam))
          (targetBudget C c ε n lam) := by
  let ε : ℕ → ℝ := fun n => |η (padHeight n)|
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hη.comp padHeight_tendsto).abs
  have hbdd : BddAbove (Set.range ε) :=
    (Metric.isBounded_range_of_tendsto ε hε).bddAbove
  rcases hbdd with ⟨B, hB⟩
  have hB' : ∀ n, |η (padHeight n)| ≤ B := by
    intro n
    exact hB ⟨n, rfl⟩
  let R : ℝ := (64 : ℝ) ^ (1 + B)
  let Q : ℝ := A * |K| * R + A * R + |K| * R + 8 * |K|
  let C : ℝ := 3 * Q
  refine ⟨ε, hε, C, ?_⟩
  intro n lam hn hlam
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  have hA0 : 0 ≤ A := by linarith
  have hR : 1 ≤ R := by
    dsimp [R]
    calc
      (1 : ℝ) = 64 ^ (0 : ℝ) := by norm_num
      _ ≤ 64 ^ (1 + B) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlamR : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hlampow : (1 : ℝ) ≤ (lam : ℝ) ^ c := one_le_pow₀ hlamR
  have hmain (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
      (padLength n : ℝ) ^ (a + η (padHeight n)) ≤ R * (n : ℝ) ^ (a + ε n) :=
    main_rpow_bound hB' a ha ha1 n hn
  have hlength : (padLength n : ℝ) ≤ R * (n : ℝ) ^ (1 + ε n) :=
    length_overhead_bound hB' n hn
  have hquarter (a : ℝ) (ha : (1 : ℝ) / 4 ≤ a) :
      (n : ℝ) ^ ((1 : ℝ) / 4) ≤ R * (n : ℝ) ^ (a + ε n) :=
    quarter_rpow_bound hB' a ha n hn
  simp only [padLength] at hmain hlength
  have hsigned (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
      K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (a + η (padHeight n)) ≤
        (|K| * R) * (n : ℝ) ^ (a + ε n) := by
    calc
      K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (a + η (padHeight n))
          ≤ |K| * (R * (n : ℝ) ^ (a + ε n)) := by
        apply mul_le_mul (le_abs_self K) (hmain a ha ha1)
        · exact Real.rpow_nonneg (by positivity) _
        · exact abs_nonneg K
      _ = (|K| * R) * (n : ℝ) ^ (a + ε n) := by ring
  have hQmul (x : ℝ) (hx : 0 ≤ x) : Q * x ≤ C * x := by
    dsimp [C]
    nlinarith [mul_nonneg hQ0 hx]
  have hmainTerm (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
      A * (K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (a + η (padHeight n)) * (lam : ℝ) ^ c) ≤
        Q * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by
    calc
      A * (K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (a + η (padHeight n)) * (lam : ℝ) ^ c)
          = A * (K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (a + η (padHeight n))) * (lam : ℝ) ^ c := by ring
      _ ≤ A * ((|K| * R) * (n : ℝ) ^ (a + ε n)) * (lam : ℝ) ^ c := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hsigned a ha ha1) hA0
      _ = (A * |K| * R) * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by ring
      _ ≤ Q * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        dsimp [Q]
        have h1 : 0 ≤ A * R := by positivity
        have h2 : 0 ≤ |K| * R := by positivity
        have h3 : 0 ≤ 8 * |K| := by positivity
        nlinarith
  have hlengthTerm :
      A * ((4 ^ padHeight n : ℕ) : ℝ) ≤
        Q * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c := by
    calc
      A * ((4 ^ padHeight n : ℕ) : ℝ) ≤ A * (R * (n : ℝ) ^ (1 + ε n)) := by gcongr
      _ = (A * R) * (n : ℝ) ^ (1 + ε n) * 1 := by ring
      _ ≤ (A * R) * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c := by gcongr
      _ ≤ Q * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        dsimp [Q]
        have h1 : 0 ≤ A * |K| * R := by positivity
        have h2 : 0 ≤ |K| * R := by positivity
        have h3 : 0 ≤ 8 * |K| := by positivity
        nlinarith
  have hquarterTerm (a : ℝ) (ha : (1 : ℝ) / 4 ≤ a) :
      A * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Q * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by
    calc
      A * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ A * (R * (n : ℝ) ^ (a + ε n)) := by
        gcongr
        exact hquarter a ha
      _ = (A * R) * (n : ℝ) ^ (a + ε n) * 1 := by ring
      _ ≤ (A * R) * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by gcongr
      _ ≤ Q * (n : ℝ) ^ (a + ε n) * (lam : ℝ) ^ c := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        dsimp [Q]
        have h1 : 0 ≤ A * |K| * R := by positivity
        have h2 : 0 ≤ |K| * R := by positivity
        have h3 : 0 ≤ 8 * |K| := by positivity
        nlinarith
  have honline :
      K * (lam : ℝ) * ((4 ^ padHeight n : ℕ) : ℝ) ^ (η (padHeight n)) ≤
        C * (lam : ℝ) * (n : ℝ) ^ (ε n) := by
    calc
      K * (lam : ℝ) * ((4 ^ padHeight n : ℕ) : ℝ) ^ (η (padHeight n))
          = (lam : ℝ) * (K * ((4 ^ padHeight n : ℕ) : ℝ) ^ (0 + η (padHeight n))) := by ring
      _ ≤ (lam : ℝ) * ((|K| * R) * (n : ℝ) ^ (0 + ε n)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsigned 0 (by norm_num) (by norm_num)
      _ = (|K| * R) * ((lam : ℝ) * (n : ℝ) ^ (ε n)) := by simp only [zero_add]; ring
      _ ≤ Q * ((lam : ℝ) * (n : ℝ) ^ (ε n)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [Q]
        have h1 : 0 ≤ A * |K| * R := by positivity
        have h2 : 0 ≤ A * R := by positivity
        have h3 : 0 ≤ 8 * |K| := by positivity
        nlinarith
      _ ≤ C * ((lam : ℝ) * (n : ℝ) ^ (ε n)) := hQmul _ (by positivity)
      _ = C * (lam : ℝ) * (n : ℝ) ^ (ε n) := by ring
  have hsqrt :
      Real.sqrt ((4 ^ padHeight n : ℕ) : ℝ) ≤ 8 * Real.sqrt n := by
    calc
      Real.sqrt ((4 ^ padHeight n : ℕ) : ℝ) ≤ Real.sqrt ((64 : ℝ) * n) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast padLength_le n hn
      _ = Real.sqrt 64 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
      _ = 8 * Real.sqrt n := by norm_num
  have hoffline :
      K * Real.sqrt ((4 ^ padHeight n : ℕ) : ℝ) ≤ C * Real.sqrt n := by
    by_cases hK : 0 ≤ K
    · calc
        K * Real.sqrt ((4 ^ padHeight n : ℕ) : ℝ) ≤ K * (8 * Real.sqrt n) := by gcongr
        _ = (8 * |K|) * Real.sqrt n := by rw [abs_of_nonneg hK]; ring
        _ ≤ Q * Real.sqrt n := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          dsimp [Q]
          have h1 : 0 ≤ A * |K| * R := by positivity
          have h2 : 0 ≤ A * R := by positivity
          have h3 : 0 ≤ |K| * R := by positivity
          nlinarith
        _ ≤ C * Real.sqrt n := hQmul _ (Real.sqrt_nonneg _)
    · have hK' : K ≤ 0 := le_of_not_ge hK
      have hneg : K * Real.sqrt ((4 ^ padHeight n : ℕ) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK' (Real.sqrt_nonneg _)
      exact hneg.trans (mul_nonneg hQ0 (Real.sqrt_nonneg _) |>.trans (hQmul _ (Real.sqrt_nonneg _)))
  refine ⟨?_, ?_, honline, hoffline, ?_, ?_, ?_⟩
  · dsimp [adapterBudget, powerFourBudget, targetBudget]
    calc
      _ ≤ Q * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c +
            Q * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c +
            Q * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c :=
        add_le_add (add_le_add (hmainTerm 1 (by norm_num) (by norm_num)) hlengthTerm)
          (hquarterTerm 1 (by norm_num))
      _ = C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c := by dsimp [C]; ring
  all_goals dsimp [adapterBudget, powerFourBudget, targetBudget]
  all_goals
    calc
      _ ≤ Q * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c +
            Q * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c :=
        add_le_add (hmainTerm ((1 : ℝ) / 2) (by norm_num) (by norm_num))
          (hquarterTerm ((1 : ℝ) / 2) (by norm_num))
      _ = 2 * (Q * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c) := by ring
      _ ≤ 3 * (Q * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c) := by
        apply mul_le_mul_of_nonneg_right (by norm_num)
        positivity
      _ = C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c := by dsimp [C]; ring
