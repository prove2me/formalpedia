-- Prove2me | solution 1 for ImprovedLinBandits.UCBDelta.ucb_delta_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T15:53:01.587482+00:00
-- url     : https://prove2.me/submissions/85177580-d961-4a1a-9320-e4e2db2e23e0

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_ImprovedLinBandits_UCBDelta_IsUCBDeltaRun

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace P00f7927a


lemma log_lb (N k m : ℕ) (hk : 0 < k) (h : (2:ℝ) ^ m ≤ (1 + (N:ℝ)) ^ k) :
    (m:ℝ) / k * Real.log 2 ≤ Real.log (1 + (N:ℝ)) := by
  have h1 : Real.log ((2:ℝ) ^ m) ≤ Real.log ((1 + (N:ℝ)) ^ k) :=
    Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h1
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith

lemma core (N : ℕ) (hN : 3 ≤ N) (L : ℝ) (hL : Real.log 2 ≤ L) :
    ((N:ℝ) - 2) * (1 + N) / (N:ℝ) ^ 2 * (2 + 8 * L + 4 * Real.log (1 + N))
      + (2 + 8 * L + 4 * Real.log (1 + N)) / 2 - 8 * Real.log (1 + N)
      + 16 * Real.log 2 - 8 + 16 / N - 16 * L ≤ 0 := by
  have l2a := Real.log_two_gt_d9
  have l2b := Real.log_two_lt_d9
  have hℓ0 : 0 ≤ Real.log (1 + (N:ℝ)) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  by_cases hbig : 11 ≤ N
  · have hN' : (11:ℝ) ≤ N := by exact_mod_cast hbig
    have hNpos : (0:ℝ) < N := by linarith
    have hq : ((N:ℝ) - 2) * (1 + N) / (N:ℝ) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hq0 : 0 ≤ ((N:ℝ) - 2) * (1 + N) / (N:ℝ) ^ 2 := by
      apply div_nonneg _ (by positivity); nlinarith
    have hB : 0 ≤ 2 + 8 * L + 4 * Real.log (1 + N) := by nlinarith
    have hqB : ((N:ℝ) - 2) * (1 + N) / (N:ℝ) ^ 2 * (2 + 8 * L + 4 * Real.log (1 + N))
        ≤ 2 + 8 * L + 4 * Real.log (1 + N) := by
      calc _ ≤ 1 * (2 + 8 * L + 4 * Real.log (1 + N)) := mul_le_mul_of_nonneg_right hq hB
        _ = _ := one_mul _
    have hℓ : (7:ℝ) / 2 * Real.log 2 ≤ Real.log (1 + (N:ℝ)) := by
      have := log_lb N 2 7 (by norm_num) (by nlinarith)
      simpa using this
    have h16 : 16 / (N:ℝ) ≤ 16 / 11 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
    linarith
  · have hN2 : N ≤ 10 := by omega
    interval_cases N
    · have h := log_lb 3 1 2 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 4 4 9 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 5 2 5 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 6 3 8 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 7 1 3 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 8 1 3 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 9 4 13 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith
    · have h := log_lb 10 3 10 (by norm_num) (by norm_num)
      norm_num at h ⊢; nlinarith

/-- The case `N ≥ 3`. -/
lemma ana_big (x : ℝ) (hx : 2 ≤ x) (N : ℕ) (hN : 3 ≤ N) (u : ℝ) (hu : 0 < u)
    (h : u * (N:ℝ) ^ 2 ≤ (1 + N) * (2 + 8 * Real.log x + 4 * Real.log (1 + N))) :
    ((N:ℝ) - 2) * u + 8 * Real.log u ≤ 16 * Real.log 2 + 16 * Real.log x := by
  set L := Real.log x with hLdef
  set ℓ := Real.log (1 + (N:ℝ)) with hℓdef
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hx
  have l2a := Real.log_two_gt_d9
  have hN' : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  set B := 2 + 8 * L + 4 * ℓ with hBdef
  have hB : 0 < B := by rw [hBdef]; linarith
  set U := (1 + (N:ℝ)) * B / (N:ℝ) ^ 2 with hUdef
  have hU : 0 < U := by positivity
  have huU : u ≤ U := by rw [hUdef, le_div_iff₀ (by positivity)]; linarith
  have h1 : ((N:ℝ) - 2) * u ≤ ((N:ℝ) - 2) * U :=
    mul_le_mul_of_nonneg_left huU (by linarith)
  have h2 : Real.log u ≤ Real.log U := Real.log_le_log hu huU
  have h2' : Real.log U = ℓ + Real.log B - 2 * Real.log N := by
    rw [hUdef, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hB.ne',
      Real.log_pow]
    push_cast; ring
  have h3 : Real.log B ≤ 4 * Real.log 2 + B / 16 - 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < B / 16 by positivity)
    rw [Real.log_div hB.ne' (by norm_num), show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this; linarith
  have h4 : ℓ - Real.log N ≤ 1 / N := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + (N:ℝ)) / N by positivity)
    rw [Real.log_div (by positivity) hNpos.ne'] at this
    have e : (1 + (N:ℝ)) / N - 1 = 1 / N := by field_simp; ring
    rw [e] at this; exact this
  have hc := core N hN L hL
  have e2 : ((N:ℝ) - 2) * U = ((N:ℝ) - 2) * (1 + N) / (N:ℝ) ^ 2 * B := by
    rw [hUdef]; ring
  have e3 : (16:ℝ) / N = 16 * (1 / N) := by ring
  rw [← hℓdef, ← hBdef] at hc
  linarith

lemma ana_arm (x Δ : ℝ) (hx : 2 ≤ x) (hΔ : 0 < Δ) (m : ℕ)
    (hm : m ≤ 1 ∨ ∃ N : ℕ, 1 ≤ N ∧ m = N + 1 ∧
      Δ ^ 2 * (N:ℝ) ^ 2 ≤ (1 + N) * (2 + 8 * Real.log x + 4 * Real.log (1 + N))) :
    Δ * m ≤ 3 * Δ + 16 / Δ * Real.log (2 * x / Δ) := by
  have hL : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have l2a := Real.log_two_gt_d9
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Δ ^ 2 := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hudef]; positivity
  rw [← hudef] at hm
  have hlogΔ : Real.log Δ = Real.log u / 2 := by
    rw [hudef, Real.log_pow]; push_cast; ring
  have hK : Real.log (2 * x / Δ) = Real.log 2 + Real.log x - Real.log u / 2 := by
    rw [Real.log_div (by positivity) hΔ.ne', Real.log_mul (by norm_num) (by positivity), hlogΔ]
  -- reduce to `(m - 3) u + 8 log u ≤ 16 log 2 + 16 log x`
  suffices hs : ((m:ℝ) - 3) * u + 8 * Real.log u ≤ 16 * Real.log 2 + 16 * Real.log x by
    rw [hK]
    have : Δ * m - 3 * Δ ≤ 16 / Δ * (Real.log 2 + Real.log x - Real.log u / 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hΔ]
      have : (Δ * m - 3 * Δ) * Δ = ((m:ℝ) - 3) * u := by rw [hudef]; ring
      rw [this]; linarith
    linarith
  rcases hm with hm | ⟨N, hN1, rfl, hN⟩
  · have hm' : (m:ℝ) ≤ 1 := by exact_mod_cast hm
    have h := Real.log_le_sub_one_of_pos (show 0 < u / 4 by positivity)
    rw [Real.log_div hu.ne' (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h
    nlinarith
  · push_cast
    rcases Nat.lt_or_ge N 3 with hN3 | hN3
    · interval_cases N
      · have h := Real.log_le_sub_one_of_pos (show 0 < u / 8 by positivity)
        rw [Real.log_div hu.ne' (by norm_num), show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
        norm_num at h hN ⊢
        nlinarith
      · -- u ≤ 4 x^2
        have hx1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
        have h3 : Real.log (1 + ((2:ℕ):ℝ)) ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + ((2:ℕ):ℝ) by norm_num)
          norm_num at this ⊢; linarith
        have hu4 : u ≤ 4 * x ^ 2 := by
          push_cast at hN h3
          nlinarith
        have hlu : Real.log u ≤ Real.log (4 * x ^ 2) := Real.log_le_log hu hu4
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
          show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlu
        push_cast at hlu
        norm_num
        linarith
    · have := ana_big x hx N hN3 u hu (by linarith [hN])
      linarith



lemma keyK {Ω : Type} {m mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (hm : m ≤ mΩ) {X : Ω → ℝ} (hX : Measurable X)
    (hsg : HasCondSubgaussianMGF m hm X 1 P) (lam : ℝ) {W : Ω → ℝ≥0∞} (hW : Measurable[m] W) :
    ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * X ω)) ∂P
      ≤ ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) * ∫⁻ ω, W ω ∂P := by
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (lam * X ω)) with hfdef
  have hf : Measurable f := by
    rw [hfdef]; exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hX.const_mul lam))
  have hint : Integrable (fun ω => Real.exp (lam * X ω)) P := hsg.integrable_exp_mul lam
  have hle : (P.withDensity f).trim hm
      ≤ (ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) • P).trim hm := by
    rw [Measure.le_iff]
    intro s hs
    rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply f (hm s hs),
      Measure.smul_apply, smul_eq_mul]
    rw [hfdef, ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
    rw [← setIntegral_condExp hm hint hs]
    have h1 : ∫ ω in s, (P[fun ω => Real.exp (lam * X ω) | m]) ω ∂P
        ≤ ∫ ω in s, Real.exp (lam ^ 2 / 2) ∂P := by
      apply setIntegral_mono_ae integrable_condExp.integrableOn (integrableOn_const)
      filter_upwards [hsg.ae_condExp_le lam] with ω hω
      simpa using hω
    rw [setIntegral_const, smul_eq_mul] at h1
    calc ENNReal.ofReal (∫ ω in s, (P[fun ω => Real.exp (lam * X ω) | m]) ω ∂P)
        ≤ ENNReal.ofReal (P.real s * Real.exp (lam ^ 2 / 2)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) * P s := by
        rw [ENNReal.ofReal_mul measureReal_nonneg, measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top P s), mul_comm]
  calc ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (lam * X ω)) ∂P
      = ∫⁻ ω, W ω ∂(P.withDensity f) := by
        rw [lintegral_withDensity_eq_lintegral_mul P hf (hW.mono hm le_rfl)]
        congr 1; ext ω; simp [hfdef, mul_comm]
    _ = ∫⁻ ω, W ω ∂((P.withDensity f).trim hm) := (lintegral_trim hm hW).symm
    _ ≤ ∫⁻ ω, W ω ∂((ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) • P).trim hm) :=
        lintegral_mono' hle le_rfl
    _ = ∫⁻ ω, W ω ∂(ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) • P) := lintegral_trim hm hW
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) * ∫⁻ ω, W ω ∂P := by
        rw [lintegral_smul_measure, smul_eq_mul]

lemma mix_lb (S N : ℝ) (hN : 0 ≤ N) :
    ENNReal.ofReal (Real.exp (S ^ 2 / (2 * (1 + N))) / Real.sqrt (1 + N)) ≤
      ∫⁻ lam, ENNReal.ofReal (Real.exp (lam * S - lam ^ 2 / 2 * N)) ∂(gaussianReal 0 1) := by
  have hN1 : 0 < 1 + N := by linarith
  set v : ℝ≥0 := ⟨(1 + N)⁻¹, by positivity⟩ with hv
  have hvr : (v : ℝ) = (1 + N)⁻¹ := rfl
  have hvpos : (0:ℝ) < v := by rw [hvr]; positivity
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hvpos; simp at hvpos
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) (by fun_prop)]
  have hpt : ∀ lam : ℝ, (gaussianPDF 0 1 * fun lam => ENNReal.ofReal (Real.exp (lam * S - lam ^ 2 / 2 * N))) lam
      = ENNReal.ofReal (Real.sqrt v) *
          (gaussianPDF 0 v lam * ENNReal.ofReal (Real.exp (S * lam))) := by
    intro lam
    simp only [Pi.mul_apply, gaussianPDF]
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
    have e1 : Real.sqrt (2 * Real.pi * (v:ℝ)) = Real.sqrt (2 * Real.pi) * Real.sqrt v :=
      Real.sqrt_mul (by positivity) _
    have hsv : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 hvpos
    have hs2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    rw [e1, mul_inv, hvr]
    have ee : Real.exp (-lam ^ 2 / 2) * Real.exp (lam * S - lam ^ 2 / 2 * N)
        = Real.exp (-lam ^ 2 / (2 * (1 + N)⁻¹)) * Real.exp (S * lam) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
    rw [← hvr]
    calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-lam ^ 2 / 2) * Real.exp (lam * S - lam ^ 2 / 2 * N)
        = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-lam ^ 2 / 2) * Real.exp (lam * S - lam ^ 2 / 2 * N)) := by ring
      _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-lam ^ 2 / (2 * (v:ℝ))) * Real.exp (S * lam)) := by
        rw [ee, hvr]
      _ = _ := by field_simp
  rw [lintegral_congr hpt, lintegral_const_mul _ (by fun_prop)]
  have h2 : ∫⁻ lam, gaussianPDF 0 v lam * ENNReal.ofReal (Real.exp (S * lam))
      = ∫⁻ lam, ENNReal.ofReal (Real.exp (S * lam)) ∂(gaussianReal 0 v) := by
    rw [gaussianReal_of_var_ne_zero 0 hv0,
      lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 v) (by fun_prop)]
    rfl
  rw [h2, ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal S)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  have hmgf : ∫ lam, Real.exp (S * lam) ∂(gaussianReal 0 v) = Real.exp (v * S ^ 2 / 2) := by
    have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) S
    simpa [mgf] using this
  rw [hmgf, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply le_of_eq
  congr 1
  rw [hvr, Real.sqrt_inv, div_eq_mul_inv, mul_comm]
  congr 2
  field_simp


lemma ville_sum {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} (ℱ : Filtration ℕ mΩ)
    (Z : ℕ → Ω → ℝ≥0∞) (hZ0 : ∫⁻ ω, Z 0 ω ∂P ≤ 1)
    (hstep : ∀ (n : ℕ) (E : Set Ω), MeasurableSet[ℱ n] E →
      ∫⁻ ω in E, Z (n + 1) ω ∂P ≤ ∫⁻ ω in E, Z n ω ∂P)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet[ℱ n] (A n))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Z t ω ∂P ≤ 1 := by
  let C : ℕ → Set Ω := fun n => {ω | ∀ t < n, ω ∉ A t}
  have hC : ∀ n, MeasurableSet[ℱ n] (C (n + 1)) := by
    intro n
    have : C (n + 1) = ⋂ t ∈ Finset.range (n + 1), (A t)ᶜ := by
      ext ω; simp [C]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun t ht => ?_)
    have htn : t ≤ n := by simp at ht; omega
    exact ((ℱ.mono htn) _ (hA t)).compl
  have key : ∀ n, ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Z t ω ∂P + ∫⁻ ω in C n, Z n ω ∂P ≤ 1 := by
    intro n
    induction n with
    | zero =>
      have : C 0 = Set.univ := by ext ω; simp [C]
      simp [this, hZ0]
    | succ n ih =>
      have hsplit : C n = A n ∪ C (n + 1) := by
        ext ω
        simp only [C, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro h
          by_cases hA' : ω ∈ A n
          · exact Or.inl hA'
          · right
            intro t ht
            rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h' | h'
            · exact h t h'
            · subst h'; exact hA'
        · rintro (h | h)
          · intro t ht hmem
            exact Set.disjoint_left.1 (hdisj (ne_of_lt ht)) hmem h
          · intro t ht
            exact h t (Nat.lt_succ_of_lt ht)
      have hdisj' : Disjoint (A n) (C (n + 1)) :=
        Set.disjoint_left.2 (fun ω h1 h2 => h2 n (Nat.lt_succ_self n) h1)
      have hmC : MeasurableSet (C (n + 1)) := ℱ.le n _ (hC n)
      rw [Finset.sum_range_succ]
      calc ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Z t ω ∂P + ∫⁻ ω in A n, Z n ω ∂P
            + ∫⁻ ω in C (n + 1), Z (n + 1) ω ∂P
          ≤ ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Z t ω ∂P + ∫⁻ ω in A n, Z n ω ∂P
            + ∫⁻ ω in C (n + 1), Z n ω ∂P := by
            exact add_le_add le_rfl (hstep n _ (hC n))
        _ = ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Z t ω ∂P + ∫⁻ ω in C n, Z n ω ∂P := by
            rw [add_assoc, ← lintegral_union hmC hdisj', ← hsplit]
        _ ≤ 1 := ih
  exact le_trans le_self_add (key n)

/-- the noise sum of arm `j` over rounds `1, …, t` -/
noncomputable def Sj {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ) (j : Fin d)
    (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range t, if I (s + 1) ω = j then η (s + 1) ω else 0

noncomputable def Nj {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (j : Fin d) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.range t, if I (s + 1) ω = j then (1:ℝ) else 0

noncomputable def Mc {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ) (j : Fin d)
    (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (Sj I η j t ω ^ 2 / (2 * (1 + Nj I j t ω))) / Real.sqrt (1 + Nj I j t ω)

noncomputable def Zl {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ) (j : Fin d)
    (lam : ℝ) (t : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * Sj I η j t ω - lam ^ 2 / 2 * Nj I j t ω))

lemma Nj_eq {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (j : Fin d) (t : ℕ) (ω : Ω) :
    Nj I j t ω = (ImprovedLinBandits.UCBDelta.pullCount I j t ω : ℝ) := by
  unfold Nj ImprovedLinBandits.UCBDelta.pullCount
  rw [Finset.sum_boole]

lemma Nj_nonneg {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (j : Fin d) (t : ℕ) (ω : Ω) :
    0 ≤ Nj I j t ω := by
  rw [Nj_eq]; positivity

lemma Sj_succ {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ) (j : Fin d)
    (t : ℕ) (ω : Ω) :
    Sj I η j (t + 1) ω = Sj I η j t ω + (if I (t + 1) ω = j then η (t + 1) ω else 0) := by
  simp only [Sj, Finset.sum_range_succ]

lemma Nj_succ {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (j : Fin d) (t : ℕ) (ω : Ω) :
    Nj I j (t + 1) ω = Nj I j t ω + (if I (t + 1) ω = j then (1:ℝ) else 0) := by
  simp only [Nj, Finset.sum_range_succ]

lemma Zl_succ {Ω : Type} {d : ℕ} (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ) (j : Fin d)
    (lam : ℝ) (n : ℕ) (ω : Ω) :
    Zl I η j lam (n + 1) ω = Zl I η j lam n ω *
      (if I (n + 1) ω = j then ENNReal.ofReal (Real.exp (lam * η (n + 1) ω)) *
        ENNReal.ofReal (Real.exp (-(lam ^ 2 / 2))) else 1) := by
  unfold Zl
  rw [Sj_succ, Nj_succ]
  by_cases h : I (n + 1) ω = j
  · rw [if_pos h, if_pos h, if_pos h]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  · rw [if_neg h, if_neg h, if_neg h]
    simp

section meas
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {d : ℕ} (ℱ : Filtration ℕ mΩ)
  {I : ℕ → Ω → Fin d} {η : ℕ → Ω → ℝ}

lemma meas_Sj (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1))) (j : Fin d) (t : ℕ) :
    Measurable[ℱ t] (Sj I η j t) := by
  unfold Sj
  refine Finset.measurable_sum _ (fun s hs => ?_)
  have hst : s + 1 ≤ t := by simp at hs; omega
  refine Measurable.ite ?_ ((hη s).mono (ℱ.mono hst) le_rfl) measurable_const
  exact ((hI s).mono (ℱ.mono (by omega)) le_rfl) (measurableSet_singleton j)

lemma meas_Nj (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1))) (j : Fin d) (t : ℕ) :
    Measurable[ℱ t] (Nj I j t) := by
  unfold Nj
  refine Finset.measurable_sum _ (fun s hs => ?_)
  have hst : s + 1 ≤ t := by simp at hs; omega
  refine Measurable.ite ?_ measurable_const measurable_const
  exact ((hI s).mono (ℱ.mono (by omega)) le_rfl) (measurableSet_singleton j)

lemma meas_Mc (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1))) (j : Fin d) (t : ℕ) :
    Measurable[ℱ t] (Mc I η j t) := by
  have h1 := meas_Sj ℱ hI hη j t
  have h2 := meas_Nj ℱ hI j t
  unfold Mc
  exact ((h1.pow_const 2).div (measurable_const.mul (measurable_const.add h2))).exp.div
    (measurable_const.add h2).sqrt

lemma meas_Zl (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1))) (j : Fin d) (lam : ℝ) (t : ℕ) :
    Measurable[ℱ t] (Zl I η j lam t) := by
  have h1 := meas_Sj ℱ hI hη j t
  have h2 := meas_Nj ℱ hI j t
  unfold Zl
  exact ENNReal.measurable_ofReal.comp ((h1.const_mul lam).sub (h2.const_mul _)).exp

lemma step_Zl [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    (j : Fin d) (lam : ℝ) (n : ℕ) (E : Set Ω) (hE : MeasurableSet[ℱ n] E) :
    ∫⁻ ω in E, Zl I η j lam (n + 1) ω ∂P ≤ ∫⁻ ω in E, Zl I η j lam n ω ∂P := by
  set g : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(lam ^ 2 / 2))) with hg
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam ^ 2 / 2)) with he
  have hge : e * g = 1 := by
    rw [he, hg, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  set W : Ω → ℝ≥0∞ :=
    E.indicator (fun ω => Zl I η j lam n ω * (if I (n + 1) ω = j then g else 0)) with hWdef
  set W' : Ω → ℝ≥0∞ :=
    E.indicator (fun ω => Zl I η j lam n ω * (if I (n + 1) ω = j then 0 else 1)) with hW'def
  have hZn : Measurable[ℱ n] (Zl I η j lam n) := meas_Zl ℱ hI hη j lam n
  have hset : MeasurableSet[ℱ n] {ω | I (n + 1) ω = j} := hI n (measurableSet_singleton j)
  have hW : Measurable[ℱ n] W :=
    (hZn.mul (Measurable.ite hset measurable_const measurable_const)).indicator hE
  have hW' : Measurable[ℱ n] W' :=
    (hZn.mul (Measurable.ite hset measurable_const measurable_const)).indicator hE
  have hEm : MeasurableSet E := ℱ.le n E hE
  have eq1 : E.indicator (Zl I η j lam (n + 1)) =
      fun ω => W ω * ENNReal.ofReal (Real.exp (lam * η (n + 1) ω)) + W' ω := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [hWdef, hW'def, Set.indicator_of_mem hω, Zl_succ]
      by_cases h : I (n + 1) ω = j
      · rw [if_pos h, if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h, if_neg h]; ring
    · simp [hWdef, hW'def, hω]
  have eq2 : E.indicator (Zl I η j lam n) = fun ω => e * W ω + W' ω := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [hWdef, hW'def, Set.indicator_of_mem hω]
      by_cases h : I (n + 1) ω = j
      · rw [if_pos h, if_pos h]
        calc Zl I η j lam n ω = Zl I η j lam n ω * (e * g) := by rw [hge, mul_one]
          _ = _ := by ring
      · rw [if_neg h, if_neg h]; ring
    · simp [hWdef, hW'def, hω]
  rw [← lintegral_indicator hEm, ← lintegral_indicator hEm, eq1, eq2,
    lintegral_add_right _ (hW'.mono (ℱ.le n) le_rfl),
    lintegral_add_right _ (hW'.mono (ℱ.le n) le_rfl),
    lintegral_const_mul _ (hW.mono (ℱ.le n) le_rfl)]
  gcongr
  exact keyK (ℱ.le n) ((hη n).mono (ℱ.le (n + 1)) le_rfl) (hsg n) lam hW

lemma arm_ville [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    (j : Fin d) (c : ℝ) (hc : 0 < c) :
    P {ω | ∃ t, c ≤ Mc I η j t ω} ≤ ENNReal.ofReal (1 / c) := by
  set A : ℕ → Set Ω := fun t => {ω | c ≤ Mc I η j t ω ∧ ∀ s < t, Mc I η j s ω < c} with hAdef
  have hMc : ∀ t, Measurable[ℱ t] (Mc I η j t) := meas_Mc ℱ hI hη j
  have hA : ∀ t, MeasurableSet[ℱ t] (A t) := by
    intro t
    have : A t = {ω | c ≤ Mc I η j t ω} ∩ ⋂ s ∈ Finset.range t, {ω | Mc I η j s ω < c} := by
      ext ω; simp [A]
    rw [this]
    refine (measurableSet_le measurable_const (hMc t)).inter
      (Finset.measurableSet_biInter _ fun s hs => ?_)
    have hst : s ≤ t := by simp at hs; omega
    exact measurableSet_lt ((hMc s).mono (ℱ.mono hst) le_rfl) measurable_const
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro s t hst
    rcases lt_or_gt_of_ne hst with h | h
    · exact Set.disjoint_left.2 fun ω h1 h2 => absurd h1.1 (not_le.2 (h2.2 s h))
    · exact Set.disjoint_left.2 fun ω h1 h2 => absurd h2.1 (not_le.2 (h1.2 t h))
  have hsub : {ω | ∃ t, c ≤ Mc I η j t ω} ⊆ ⋃ t, A t := by
    intro ω hω
    classical
    exact Set.mem_iUnion.2 ⟨Nat.find hω, Nat.find_spec hω,
      fun s hs => not_le.1 (Nat.find_min hω hs)⟩
  have hunc : ∀ t, Measurable (fun p : Ω × ℝ => Zl I η j p.2 t p.1) := by
    intro t
    have hS := (meas_Sj ℱ hI hη j t).mono (ℱ.le t) le_rfl
    have hN := (meas_Nj ℱ hI j t).mono (ℱ.le t) le_rfl
    unfold Zl
    exact ENNReal.measurable_ofReal.comp ((measurable_snd.mul (hS.comp measurable_fst)).sub
      (((measurable_snd.pow_const 2).div_const 2).mul (hN.comp measurable_fst))).exp
  have hZ0 : ∀ lam, ∫⁻ ω, Zl I η j lam 0 ω ∂P ≤ 1 := by
    intro lam; simp [Zl, Sj, Nj]
  have hville : ∀ lam n, ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Zl I η j lam t ω ∂P ≤ 1 :=
    fun lam n => ville_sum ℱ (fun t => Zl I η j lam t) (hZ0 lam)
      (fun n E hE => step_Zl ℱ hI hη hsg j lam n E hE) A hA hdisj n
  have hsum : ∀ n, ∑ t ∈ Finset.range n, ENNReal.ofReal c * P (A t) ≤ 1 := by
    intro n
    calc ∑ t ∈ Finset.range n, ENNReal.ofReal c * P (A t)
        ≤ ∑ t ∈ Finset.range n,
            ∫⁻ ω in A t, ∫⁻ lam, Zl I η j lam t ω ∂(gaussianReal 0 1) ∂P := by
          gcongr with t ht
          rw [← setLIntegral_const]
          refine le_trans (setLIntegral_mono' ((ℱ.le t) _ (hA t))
            (g := fun ω => ENNReal.ofReal (Mc I η j t ω))
            (fun ω hω => ENNReal.ofReal_le_ofReal hω.1)) ?_
          exact lintegral_mono (fun ω => mix_lb _ _ (Nj_nonneg I j t ω))
      _ = ∑ t ∈ Finset.range n,
            ∫⁻ lam, ∫⁻ ω in A t, Zl I η j lam t ω ∂P ∂(gaussianReal 0 1) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact lintegral_lintegral_swap ((hunc t).aemeasurable)
      _ = ∫⁻ lam, ∑ t ∈ Finset.range n, ∫⁻ ω in A t, Zl I η j lam t ω ∂P
            ∂(gaussianReal 0 1) := by
          rw [lintegral_finsetSum']
          intro t _
          exact (Measurable.lintegral_prod_left' (hunc t)).aemeasurable
      _ ≤ ∫⁻ lam, 1 ∂(gaussianReal 0 1) := lintegral_mono fun lam => hville lam n
      _ = 1 := by simp
  have hU : P (⋃ t, A t) = ∑' t, P (A t) := measure_iUnion hdisj (fun t => (ℱ.le t) _ (hA t))
  have htot : ENNReal.ofReal c * P (⋃ t, A t) ≤ 1 := by
    rw [hU, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_of_sum_range_le hsum
  calc P {ω | ∃ t, c ≤ Mc I η j t ω} ≤ P (⋃ t, A t) := measure_mono hsub
    _ ≤ (ENNReal.ofReal c)⁻¹ := by rw [ENNReal.le_inv_iff_mul_le, mul_comm]; exact htot
    _ = ENNReal.ofReal (1 / c) := by rw [one_div, ENNReal.ofReal_inv_of_pos hc]

end meas


section det
open ImprovedLinBandits.UCBDelta
variable {Ω : Type} {d : ℕ} {μ : Fin d → ℝ} {I : ℕ → Ω → Fin d} {η : ℕ → Ω → ℝ}

lemma pullCount_succ' (j : Fin d) (n : ℕ) (ω : Ω) :
    pullCount I j (n + 1) ω = pullCount I j n ω + (if I (n + 1) ω = j then 1 else 0) := by
  unfold pullCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]

lemma empMean_sub (i : Fin d) (t : ℕ) (ω : Ω) (hN : 1 ≤ pullCount I i t ω) :
    empMean μ η I i t ω - μ i = Sj I η i t ω / (pullCount I i t ω : ℝ) := by
  unfold empMean
  have hsum : ∑ s ∈ (Finset.range t).filter (fun s => I (s + 1) ω = i),
      (μ (I (s + 1) ω) + η (s + 1) ω) = (pullCount I i t ω : ℝ) * μ i + Sj I η i t ω := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    · unfold Sj
      rw [Finset.sum_filter]
  rw [hsum]
  have hNpos : (0:ℝ) < pullCount I i t ω := by exact_mod_cast hN
  field_simp
  ring

lemma good_sq (i : Fin d) (t : ℕ) (ω : Ω) (x : ℝ) (hx : 0 < x) (hgood : Mc I η i t ω < x) :
    Sj I η i t ω ^ 2 < (1 + Nj I i t ω) * (2 * Real.log x + Real.log (1 + Nj I i t ω)) := by
  have hN1 : 0 < 1 + Nj I i t ω := by linarith [Nj_nonneg I i t ω]
  unfold Mc at hgood
  rw [div_lt_iff₀ (Real.sqrt_pos.2 hN1)] at hgood
  have h := Real.log_lt_log (Real.exp_pos _) hgood
  rw [Real.log_exp, Real.log_mul hx.ne' (Real.sqrt_pos.2 hN1).ne', Real.log_sqrt hN1.le,
    div_lt_iff₀ (by positivity)] at h
  nlinarith

lemma conf_sq (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (hx : 1 ≤ (d:ℝ) / δ) (N : ℕ) (hN : 1 ≤ N) :
    confRadius d δ N ^ 2 * (N:ℝ) ^ 2 =
      (1 + N) * (1 + 2 * Real.log ((d:ℝ) / δ) + Real.log (1 + N)) := by
  unfold confRadius
  have hN1 : (0:ℝ) < 1 + N := by positivity
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log ((d:ℝ) * Real.sqrt (1 + (N:ℝ)) / δ)
      = Real.log ((d:ℝ) / δ) + Real.log (1 + N) / 2 := by
    rw [show (d:ℝ) * Real.sqrt (1 + (N:ℝ)) / δ = ((d:ℝ) / δ) * Real.sqrt (1 + (N:ℝ)) by ring,
      Real.log_mul (by positivity) (Real.sqrt_pos.2 hN1).ne', Real.log_sqrt hN1.le]
  have hL : 0 ≤ Real.log ((d:ℝ) / δ) := Real.log_nonneg hx
  have hℓ : 0 ≤ Real.log (1 + (N:ℝ)) := Real.log_nonneg (by linarith)
  rw [hlog, Real.sq_sqrt (by positivity)]
  field_simp
  ring

lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

lemma C1 (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (hx : 1 ≤ (d:ℝ) / δ)
    (hrun : IsUCBDeltaRun d δ μ η I) (ω : Ω)
    (hgood : ∀ i t, Mc I η i t ω < (d:ℝ) / δ) (k : Fin d) (hk : bestMean μ = μ k)
    (j : Fin d) (t : ℕ) (hIt : I (t + 1) ω = j) (hN : 1 ≤ pullCount I j t ω)
    (hΔ : 0 < gap μ j) :
    gap μ j ^ 2 * (pullCount I j t ω : ℝ) ^ 2 ≤ (1 + (pullCount I j t ω : ℝ)) *
      (2 + 8 * Real.log ((d:ℝ) / δ) + 4 * Real.log (1 + (pullCount I j t ω : ℝ))) := by
  have hxpos : (0:ℝ) < (d:ℝ) / δ := by linarith
  have hall : ∀ i, pullCount I i t ω ≠ 0 := by
    intro i hi
    have := (hrun ω t).1 ⟨i, hi⟩
    rw [hIt] at this; omega
  have hsel := (hrun ω t).2 hall k
  rw [hIt] at hsel
  have hNk : 1 ≤ pullCount I k t ω := Nat.one_le_iff_ne_zero.2 (hall k)
  -- the best arm
  have ek := empMean_sub (μ := μ) (η := η) k t ω hNk
  have gk := good_sq k t ω _ hxpos (hgood k t)
  have ck := conf_sq hd hδ hx (pullCount I k t ω) hNk
  rw [Nj_eq] at gk
  -- the chosen arm
  have ej := empMean_sub (μ := μ) (η := η) j t ω hN
  have gj := good_sq j t ω _ hxpos (hgood j t)
  have cj := conf_sq hd hδ hx (pullCount I j t ω) hN
  rw [Nj_eq] at gj
  set L := Real.log ((d:ℝ) / δ) with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hx
  set Nk : ℝ := (pullCount I k t ω : ℝ) with hNkdef
  set Nn : ℝ := (pullCount I j t ω : ℝ) with hNndef
  have hNkpos : 0 < Nk := by rw [hNkdef]; exact_mod_cast hNk
  have hNnpos : 0 < Nn := by rw [hNndef]; exact_mod_cast hN
  set Rk := confRadius d δ (pullCount I k t ω) with hRk
  set Rj := confRadius d δ (pullCount I j t ω) with hRj
  have hRk0 : 0 ≤ Rk := Real.sqrt_nonneg _
  have hRj0 : 0 ≤ Rj := Real.sqrt_nonneg _
  have hℓk : 0 ≤ Real.log (1 + Nk) := Real.log_nonneg (by linarith)
  have hℓj : 0 ≤ Real.log (1 + Nn) := Real.log_nonneg (by linarith)
  set Sk := Sj I η k t ω with hSk
  set Sn := Sj I η j t ω with hSn
  set ek' := empMean μ η I k t ω - μ k with hek'
  set en := empMean μ η I j t ω - μ j with hen
  -- (μ k - emp k) < Rk
  have hk1 : ek' ^ 2 * Nk ^ 2 = Sk ^ 2 := by
    rw [ek]; field_simp
  have hk2 : ek' ^ 2 * Nk ^ 2 < Rk ^ 2 * Nk ^ 2 := by
    rw [hk1, ck]; linarith
  have hk3 : ek' ^ 2 < Rk ^ 2 := lt_of_mul_lt_mul_right hk2 (by positivity)
  have hk4 : -ek' < Rk := by
    have := (abs_lt.1 (abs_lt_of_sq_lt_sq hk3 hRk0)).1
    linarith
  -- the gap bound
  have hj1 : en ^ 2 * Nn ^ 2 = Sn ^ 2 := by
    rw [ej]; field_simp
  have hgap : gap μ j = μ k - μ j := by unfold gap; rw [hk]
  have hlt : gap μ j < en + Rj := by
    rw [hgap, hen]; rw [hek'] at hk4; linarith
  have hsq : gap μ j ^ 2 ≤ 2 * en ^ 2 + 2 * Rj ^ 2 :=
    le_trans (pow_lt_pow_left₀ hlt hΔ.le two_ne_zero).le (sq_add_le_two en Rj)
  have hfin : gap μ j ^ 2 * Nn ^ 2 ≤ (2 * en ^ 2 + 2 * Rj ^ 2) * Nn ^ 2 :=
    mul_le_mul_of_nonneg_right hsq (by positivity)
  have e2 : (2 * en ^ 2 + 2 * Rj ^ 2) * Nn ^ 2 = 2 * Sn ^ 2 +
      2 * ((1 + Nn) * (1 + 2 * L + Real.log (1 + Nn))) := by
    rw [← cj, ← hj1]; ring
  rw [e2] at hfin
  linarith

lemma count_bound (j : Fin d) (ω : Ω) (cond : ℕ → Prop)
    (hC : ∀ t, I (t + 1) ω = j → 1 ≤ pullCount I j t ω → cond (pullCount I j t ω)) :
    ∀ n, pullCount I j n ω ≤ 1 ∨ ∃ N, 1 ≤ N ∧ pullCount I j n ω = N + 1 ∧ cond N := by
  intro n
  induction n with
  | zero => left; simp [pullCount]
  | succ n ih =>
    rw [pullCount_succ']
    by_cases h : I (n + 1) ω = j
    · rw [if_pos h]
      rcases Nat.eq_zero_or_pos (pullCount I j n ω) with h0 | h0
      · left; omega
      · right; exact ⟨pullCount I j n ω, h0, rfl, hC n h h0⟩
    · rw [if_neg h, add_zero]; exact ih

lemma det (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hrun : IsUCBDeltaRun d δ μ η I) (ω : Ω)
    (hgood : ∀ i t, Mc I η i t ω < (d:ℝ) / δ) (n : ℕ) :
    pseudoRegret μ I n ω ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
      (3 * gap μ i + 16 / gap μ i * Real.log (2 * (d : ℝ) / (gap μ i * δ))) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨k, hk⟩ := Finite.exists_max μ
  have hbest : bestMean μ = μ k :=
    le_antisymm (ciSup_le hk) (le_ciSup (Finite.bddAbove_range μ) k)
  have hgap0 : ∀ i, 0 ≤ gap μ i := fun i => by
    unfold gap; rw [hbest]; linarith [hk i]
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hx1 : (1:ℝ) ≤ (d:ℝ) / δ := by
    rw [le_div_iff₀ hδ]
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdec : pseudoRegret μ I n ω = ∑ j, gap μ j * (pullCount I j n ω : ℝ) := by
    show ∑ t ∈ Finset.range n, gap μ (I (t + 1) ω) = _
    rw [← Finset.sum_fiberwise' (Finset.range n) (fun t => I (t + 1) ω) (gap μ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [hdec, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < gap μ i)]
  have hzero : ∑ j ∈ Finset.univ.filter (fun i => ¬ 0 < gap μ i),
      gap μ j * (pullCount I j n ω : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have h1 := (Finset.mem_filter.1 hj).2
    have : gap μ j = 0 := le_antisymm (not_lt.1 h1) (hgap0 j)
    rw [this, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun j hj => ?_
  have hΔ := (Finset.mem_filter.1 hj).2
  have hjk : j ≠ k := by
    rintro rfl
    unfold gap at hΔ; rw [hbest] at hΔ; simp at hΔ
  have hd2 : 2 ≤ d := by
    have h1 := j.isLt
    have h2 := k.isLt
    have h3 : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    omega
  have hx2 : (2:ℝ) ≤ (d:ℝ) / δ := by
    rw [le_div_iff₀ hδ]
    have : (2:ℝ) ≤ d := by exact_mod_cast hd2
    nlinarith
  have hcnt := count_bound (I := I) j ω
    (fun N => gap μ j ^ 2 * (N:ℝ) ^ 2 ≤ (1 + (N:ℝ)) *
      (2 + 8 * Real.log ((d:ℝ) / δ) + 4 * Real.log (1 + (N:ℝ))))
    (fun t hIt hN => C1 hd hδ hx1 hrun ω hgood k hbest j t hIt hN hΔ) n
  have h := ana_arm ((d:ℝ) / δ) (gap μ j) hx2 hΔ (pullCount I j n ω) hcnt
  have harg : 2 * ((d:ℝ) / δ) / gap μ j = 2 * (d:ℝ) / (gap μ j * δ) := by
    field_simp
  rw [harg] at h
  exact h

end det

end P00f7927a

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta in
theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (ℱ : Filtration ℕ mΩ)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {δ : ℝ} (hδ : 0 < δ) (hrun : IsUCBDeltaRun d δ μ η I) :
    P {ω | ∃ n : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
            (3 * gap μ i + 16 / gap μ i * Real.log (2 * (d : ℝ) / (gap μ i * δ)))
          < pseudoRegret μ I n ω}
      ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd
  have hxpos : (0:ℝ) < (d:ℝ) / δ := by positivity
  have hsub : {ω | ∃ n : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
            (3 * gap μ i + 16 / gap μ i * Real.log (2 * (d : ℝ) / (gap μ i * δ)))
          < pseudoRegret μ I n ω}
      ⊆ ⋃ j, {ω | ∃ t, (d:ℝ) / δ ≤ P00f7927a.Mc I η j t ω} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    obtain ⟨n, hn⟩ := hω
    exact absurd (P00f7927a.det hd hδ hδ1 hrun ω hcon n) (not_le.2 hn)
  calc _ ≤ P (⋃ j, {ω | ∃ t, (d:ℝ) / δ ≤ P00f7927a.Mc I η j t ω}) := measure_mono hsub
    _ ≤ ∑ j, P {ω | ∃ t, (d:ℝ) / δ ≤ P00f7927a.Mc I η j t ω} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (1 / ((d:ℝ) / δ)) :=
        Finset.sum_le_sum fun j _ => P00f7927a.arm_ville ℱ hI hη hsg j _ hxpos
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp
