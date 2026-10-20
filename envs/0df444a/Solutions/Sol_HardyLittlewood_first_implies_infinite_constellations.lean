-- Prove2me | solution 1 for HardyLittlewood.first_implies_infinite_constellations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:00:30.311613+00:00
-- url     : https://prove2.me/submissions/059c00c8-3ad9-4fad-8786-b4280442540a

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

open HardyLittlewood

lemma hl_pow_upper (n : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (1 - x) ^ n ≤ 1 - n * x + (n:ℝ)^2 * x^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hx : 0 ≤ 1 - x := by linarith
    have := mul_le_mul_of_nonneg_right ih hx
    push_cast
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg (n:ℝ)) (pow_nonneg h0 3), Nat.cast_nonneg (α := ℝ) n]

/-- the Euler factor of the singular series -/
lemma hl_term_bound (K : ℕ) (q : ℝ) (hq : 2 * K ≤ q) (hq3 : 3 ≤ q) :
    |(1 - K / q) / (1 - 1 / q) ^ K - 1| ≤ 2 * (K:ℝ)^2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  set x := 1 / q with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hq0]; linarith
  have hKx : K * x ≤ 1/2 := by
    rw [hx, mul_one_div, div_le_iff₀ hq0]; linarith
  have hKq : (K:ℝ) / q = K * x := by rw [hx]; ring
  rw [hKq]
  have hB : 1 - K * x ≤ (1 - x) ^ K := by
    have := one_add_mul_le_pow (show (-2:ℝ) ≤ -x by linarith) K
    rw [show (1:ℝ) + -x = 1 - x by ring, show (1:ℝ) + K * -x = 1 - K*x by ring] at this
    exact this
  have hU := hl_pow_upper K x hx0 hx1
  have hD : 0 < (1 - x) ^ K := by linarith
  have hD2 : 1/2 ≤ (1 - x) ^ K := by linarith
  rw [div_sub_one hD.ne', abs_div, abs_of_pos hD, div_le_iff₀ hD]
  have hx2 : x ^ 2 = 1 / q ^ 2 := by rw [hx]; ring
  rw [← hx2]
  rw [abs_of_nonpos (by linarith)]
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg (K:ℝ)) (sq_nonneg x)]

lemma hl_ssp {k : ℕ} (m : Fin k.succ → ℕ)
    (hinj : Function.Injective m) (hadm : IsAdmissibleTuple m) :
    0 < singularSeriesConstant m := by
  unfold singularSeriesConstant
  set Q := {q : ℕ // q.Prime ∧ 3 ≤ q}
  set f : Q → ℝ := fun q => (1 - (numResidues (q : ℕ) m : ℝ) / ((q : ℕ) : ℝ)) /
      (1 - 1 / ((q : ℕ) : ℝ)) ^ k.succ with hf
  -- positivity of each factor
  have hw_lt : ∀ q : Q, numResidues (q : ℕ) m < (q : ℕ) := by
    intro ⟨q, hq, hq3⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hns : ¬ Function.Surjective (fun i : Fin k.succ => (m i : ZMod q)) := by
      intro hs
      apply hadm q hq
      intro y
      have h2 : (2 : ZMod q) ≠ 0 := by
        intro h0
        have : ((2:ℕ) : ZMod q) = 0 := by exact_mod_cast h0
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      obtain ⟨i, hi⟩ := hs (y * 2⁻¹)
      refine ⟨i, ?_⟩
      simp only at hi ⊢
      rw [hi]; field_simp
    unfold numResidues
    have hne : Set.range (fun i : Fin k.succ => (m i : ZMod q)) ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]
      intro h; apply hns; intro y
      have : y ∈ Set.range (fun i : Fin k.succ => (m i : ZMod q)) := by rw [h]; trivial
      exact this
    have := Set.ncard_lt_ncard hne
    rw [Set.ncard_univ, Nat.card_zmod] at this
    exact this
  have hpos : ∀ q : Q, 0 < f q := by
    intro q
    have hq3 : (3:ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast q.2.2
    have hw : (numResidues (q : ℕ) m : ℝ) < ((q:ℕ):ℝ) := by exact_mod_cast hw_lt q
    have h1 : 0 < 1 - (numResidues (q : ℕ) m : ℝ) / ((q : ℕ) : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; exact hw
    have h2 : 0 < 1 - 1 / ((q : ℕ) : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    positivity
  -- for large q, w = k+1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, m i < M := ⟨Finset.univ.sup m + 1, fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ i))⟩
  have hw_eq : ∀ q : Q, M ≤ (q : ℕ) → numResidues (q : ℕ) m = k.succ := by
    intro ⟨q, hq, hq3⟩ hMq
    unfold numResidues
    rw [Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j hij
    simp only at hij
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (lt_of_lt_of_le (hM i) hMq),
      Nat.mod_eq_of_lt (lt_of_lt_of_le (hM j) hMq)] at hij
    exact hinj hij
  -- summability of f - 1
  have hsum : Summable (fun q : Q => f q - 1) := by
    have hg : Summable (fun q : Q => 2 * ((k.succ:ℕ):ℝ)^2 * (1 / ((q:ℕ):ℝ) ^ 2)) := by
      apply Summable.mul_left
      exact (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective
    refine Summable.of_norm_bounded_eventually hg ?_
    have hfin : {q : Q | ¬ (M + 2 * k.succ ≤ (q:ℕ))}.Finite := by
      apply Set.Finite.of_finite_image (f := fun q : Q => (q : ℕ)) _ Subtype.val_injective.injOn
      apply (Set.finite_Iio (M + 2 * k.succ)).subset
      rintro _ ⟨q, hq, rfl⟩
      simp only [Set.mem_setOf_eq, not_le] at hq
      exact hq
    filter_upwards [Filter.eventually_cofinite.mpr hfin] with q hq
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [hw_eq q (by omega)]
    apply hl_term_bound
    · have : ((2 * k.succ : ℕ) : ℝ) ≤ ((q:ℕ):ℝ) := by exact_mod_cast (by omega : 2 * k.succ ≤ (q:ℕ))
      push_cast at this ⊢; linarith
    · exact_mod_cast q.2.2
  have hlog : Summable (fun q : Q => Real.log (f q)) := by
    have := Real.summable_log_one_add_of_summable hsum
    simpa using this
  have := Real.rexp_tsum_eq_tprod hpos hlog
  rw [← this]
  positivity

lemma hl_integ (k : ℕ) :
    Filter.Tendsto (fun n => ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1))
      Filter.atTop Filter.atTop := by
  -- lower bound (n-2)/(log n)^(k+1)
  have hlow : ∀ n : ℝ, 3 ≤ n → ((n:ℝ) - 2) / (Real.log n) ^ (k+1) ≤
      ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1) := by
    intro n hn
    have hn' : (3:ℝ) ≤ n := hn
    have hcont : ContinuousOn (fun t : ℝ => 1 / (Real.log t) ^ (k + 1)) (Set.uIcc 2 n) := by
      rw [Set.uIcc_of_le (by linarith)]
      apply ContinuousOn.div continuousOn_const
      · exact (Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_Icc] at hx; simp; linarith [hx.1])).pow _
      · intro x hx; simp only [Set.mem_Icc] at hx
        have : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
        positivity
    have h1 : ∫ t in (2:ℝ)..(n:ℝ), (1 / (Real.log n) ^ (k+1)) ≤
        ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ (k + 1) := by
      apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hcont.intervalIntegrable)
      intro x hx
      have hx0 : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ hx0.le (Real.log_le_log (by linarith [hx.1]) hx.2) _
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    calc ((n:ℝ) - 2) / (Real.log n) ^ (k+1) = ((n:ℝ) - 2) * (1 / (Real.log n) ^ (k+1)) := by ring
      _ ≤ _ := h1
  have hlim : Filter.Tendsto (fun x : ℝ => (x - 2) / (Real.log x) ^ (k+1)) Filter.atTop Filter.atTop := by
    have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) (k+1) one_ne_zero
    have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x ^ (k+1) / (1 * x + -2) := by
      filter_upwards [Filter.eventually_gt_atTop 3] with x hx
      have : 0 < Real.log x := Real.log_pos (by linarith)
      have : 0 < 1 * x + -2 := by linarith
      positivity
    have h2 := (tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩).inv_tendsto_nhdsGT_zero
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 3] with x hx
    simp only [Pi.inv_apply, inv_div]; ring_nf
  refine Filter.tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  exact hlow n hn

theorem solution {k : ℕ} (m : Fin k.succ → ℕ)
    (hm0 : m 0 = 0) (hinj : Function.Injective m) (hadm : IsAdmissibleTuple m)
    (h : firstHardyLittlewoodFor m) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ IsPrimeConstellation m p := by
  have hC := hl_ssp m hinj hadm
  have hasy := h hm0 hinj
  unfold AsymptoticTo at hasy
  set G : ℕ → ℝ := fun n => singularSeriesConstant m * ∫ t in (2:ℝ)..(n:ℝ), 1 / (Real.log t) ^ k.succ
    with hG
  have hGt : Filter.Tendsto G Filter.atTop Filter.atTop :=
    ((hl_integ k).comp tendsto_natCast_atTop_atTop).const_mul_atTop hC
  have hft : Filter.Tendsto (fun n => (primeTupleCounting m n : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ (hGt.atTop_div_const (by norm_num : (0:ℝ) < 2))
    filter_upwards [hasy.bound (by norm_num : (0:ℝ) < 1/2), hGt.eventually_gt_atTop 0] with n hn hpos
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hn
    have := (abs_le.mp hn).1
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, hn⟩ := (hft.eventually_gt_atTop (N : ℝ)).exists
  have hsub : {p : ℕ | p ≤ n ∧ IsAdmissiblePrimeConstellation m p} ⊆ Set.Iio N := by
    intro p ⟨_, hpc, _⟩
    by_contra hp
    exact hcon p (not_lt.mp hp) hpc
  have hle := Set.ncard_le_ncard hsub (Set.finite_Iio N)
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range] at hle
  have : (primeTupleCounting m n : ℝ) ≤ N := by exact_mod_cast hle
  linarith

