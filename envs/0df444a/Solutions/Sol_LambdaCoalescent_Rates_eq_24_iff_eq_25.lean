-- Prove2me | solution 1 for LambdaCoalescent.Rates.eq_24_iff_eq_25
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:06:39.938621+00:00
-- url     : https://prove2.me/submissions/f7e33d6b-901e-4c08-a9a7-430442d79c56

import Definitions.Def_LambdaCoalescent_Rates_Setting



namespace LambdaCoalescent.Rates

open MeasureTheory Filter Topology Finset
open scoped CompactlySupported

section Hausdorff

theorem iter_rec (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (M : ℕ) :
    ∀ i j, μ i j = ∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2) := by
  induction M with
  | zero => intro i j; simp
  | succ M ih =>
    intro i j
    rw [Nat.sum_antidiagonal_succ]
    have e1 : ∀ p ∈ antidiagonal M, ((M+1).choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2) =
        (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          (M.choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2) := by
      intro p _
      rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
      congr 2; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib]
    have e2 : ((M+1).choose 0 : ℝ) * μ (i + 0) (j + (M+1)) +
        (∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          ∑ p ∈ antidiagonal M, (M.choose (p.1+1) : ℝ) * μ (i + (p.1+1)) (j + p.2)) =
        ∑ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + 1 + p.1) (j + p.2) +
          ∑ p ∈ antidiagonal (M+1), (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2) := by
      rw [Nat.sum_antidiagonal_succ (f := fun p => (M.choose p.1 : ℝ) * μ (i + p.1) (j + p.2))]
      simp only [Nat.choose_zero_right, Nat.cast_one]
      ring
    rw [e2, Nat.sum_antidiagonal_succ']
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_add]
    rw [← ih (i+1) j]
    have e3 : ∀ p ∈ antidiagonal M, (M.choose p.1 : ℝ) * μ (i + p.1) (j + (p.2 + 1)) =
        (M.choose p.1 : ℝ) * μ (i + p.1) (j + 1 + p.2) := by
      intro p _; congr 2; ring
    rw [Finset.sum_congr rfl e3, ← ih i (j+1), ← h]

theorem cast_descFactorial_prod (k i : ℕ) :
    (k.descFactorial i : ℝ) = ∏ r ∈ range i, ((k : ℝ) - r) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih, Nat.cast_mul]
    rcases le_or_gt i k with hik | hik
    · rw [Nat.cast_sub hik]; ring
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 hik]; simp

theorem choose_mul_desc (N i a : ℕ) (h : i + a ≤ N) :
    N.choose (i + a) * (i + a).descFactorial i = N.descFactorial i * (N - i).choose a := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have := Nat.choose_mul (n := N) (k := i + a) (s := i) (by omega)
  rw [show i + a - i = a by omega] at this
  calc N.choose (i + a) * (i.factorial * (i + a).choose i)
      = i.factorial * (N.choose (i + a) * (i + a).choose i) := by ring
    _ = i.factorial * (N.choose i * (N - i).choose a) := by rw [this]
    _ = _ := by ring

theorem moment_identity (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1))
    (N i : ℕ) (hi : i ≤ N) :
    ∑ k ∈ range (N+1), (N.choose k : ℝ) * μ k (N - k) * (k.descFactorial i : ℝ) =
      (N.descFactorial i : ℝ) * μ i 0 := by
  rw [iter_rec μ h (N - i) i 0, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  rw [show N + 1 = i + (N - i + 1) by omega, sum_range_add]
  have hz : ∑ k ∈ range i, (N.choose k : ℝ) * μ k (N - k) *
      (k.descFactorial i : ℝ) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    rw [(Nat.descFactorial_eq_zero_iff_lt).2 (mem_range.1 hk)]; simp
  rw [hz, zero_add]
  refine sum_congr rfl fun a ha => ?_
  have ha' := mem_range.1 ha
  have hc := choose_mul_desc N i a (by omega)
  have hc' : (N.choose (i + a) : ℝ) * ((i + a).descFactorial i : ℝ) =
      (N.descFactorial i : ℝ) * ((N - i).choose a : ℝ) := by exact_mod_cast hc
  dsimp only
  rw [zero_add, show N - (i + a) = N - i - a by omega]
  linear_combination μ (i + a) (N - i - a) * hc'

noncomputable def wt (μ : ℕ → ℕ → ℝ) (N k : ℕ) : ℝ := (N.choose k : ℝ) * μ k (N - k)

noncomputable def LN (μ : ℕ → ℕ → ℝ) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ∑ k ∈ range (N+1), wt μ N k * g (k / N)

theorem wt_nonneg (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (N k : ℕ) : 0 ≤ wt μ N k :=
  mul_nonneg (Nat.cast_nonneg _) (hμ _ _)

theorem wt_sum (μ : ℕ → ℕ → ℝ) (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
    (N : ℕ) : ∑ k ∈ range (N+1), wt μ N k = 1 := by
  have := moment_identity μ h N 0 (Nat.zero_le _)
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, one_mul, h00] at this
  exact this

theorem prodbound (i : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) (hN : 0 < N)
    (hiN : 2 * i ≤ N) :
    |x ^ i - ∏ r ∈ range i, (x - r / N) / (1 - r / N)| ≤ 2 * i * i / N ∧
      |∏ r ∈ range i, (x - r / N) / (1 - r / N)| ≤ 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hi2 : 2 * (i:ℝ) ≤ N := by exact_mod_cast (by omega : 2 * i ≤ N)
    have hden : (1:ℝ) / 2 ≤ 1 - i / N := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
      have : (i:ℝ) / N ≤ 1 / 2 := by rw [div_le_iff₀ hNr]; linarith
      linarith
    have hdpos : 0 < 1 - (i:ℝ) / N := by linarith
    set y := (x - i / N) / (1 - i / N) with hy
    have hy1 : |y| ≤ 1 := by
      rw [hy, abs_div, abs_of_pos hdpos, div_le_one hdpos, abs_le]
      constructor
      · have : (i:ℝ) / N ≤ 1 / 2 := by rw [div_le_iff₀ hNr]; linarith
        linarith
      · linarith
    have hxy : |x - y| ≤ 2 * i / N := by
      have : x - y = (i / N) * (1 - x) / (1 - i / N) := by
        rw [hy, eq_div_iff hdpos.ne', sub_mul, div_mul_cancel₀ _ hdpos.ne']; ring
      rw [this, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ i / N), abs_of_nonneg (by linarith : 0 ≤ 1 - x)]
      have h1 : (i:ℝ) / N * (1 - x) ≤ i / N := by
        have : 0 ≤ (i:ℝ) / N := by positivity
        nlinarith
      have h2 : (i:ℝ) / N ≤ 2 * i / N * (1 - i / N) := by
        have : 0 ≤ (i:ℝ) / N := by positivity
        rw [show 2 * (i:ℝ) / N = 2 * (i / N) by ring]
        nlinarith
      linarith
    rw [prod_range_succ, pow_succ]
    set P := ∏ r ∈ range i, (x - r / N) / (1 - r / N)
    constructor
    · have : x ^ i * x - P * y = (x ^ i - P) * x + P * (x - y) := by ring
      rw [this]
      calc |(x ^ i - P) * x + P * (x - y)| ≤ |(x ^ i - P) * x| + |P * (x - y)| := abs_add_le _ _
        _ ≤ 2 * i * i / N + 2 * i / N := by
          rw [abs_mul, abs_mul]
          gcongr
          · calc |x ^ i - P| * |x| ≤ |x ^ i - P| * 1 := by
                  gcongr; rw [abs_of_nonneg hx0]; exact hx1
              _ ≤ _ := by rw [mul_one]; exact ih1
          · calc |P| * |x - y| ≤ 1 * |x - y| := by gcongr
              _ ≤ _ := by rw [one_mul]; exact hxy
        _ ≤ 2 * ((i:ℕ) + 1 : ℕ) * ((i:ℕ) + 1 : ℕ) / N := by
          rw [← add_div, div_le_div_iff_of_pos_right hNr]
          push_cast
          nlinarith
    · rw [abs_mul]
      calc |P| * |y| ≤ 1 * 1 := by gcongr
        _ = 1 := by ring

theorem grid_prod (k i N : ℕ) (hiN : i ≤ N) (hN : 0 < N) :
    ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N) =
      (k.descFactorial i : ℝ) / (N.descFactorial i : ℝ) := by
  rw [cast_descFactorial_prod, cast_descFactorial_prod, ← prod_div_distrib]
  refine prod_congr rfl fun r hr => ?_
  have hr' : r < N := by have := mem_range.1 hr; omega
  have hNr : (N:ℝ) ≠ 0 := by positivity
  have hNr2 : (N:ℝ) - r ≠ 0 := by
    have : (r:ℝ) < N := by exact_mod_cast hr'
    linarith
  field_simp

theorem mono_bound (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
    (i N : ℕ) (hN : 0 < N) (hiN : 2 * i ≤ N) :
    |LN μ N (fun x => x ^ i) - μ i 0| ≤ 2 * i * i / N := by
  have hD : (N.descFactorial i : ℝ) ≠ 0 := by
    have : N.descFactorial i ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
    exact_mod_cast this
  have hmom := moment_identity μ h N i (by omega)
  have hμi : μ i 0 = ∑ k ∈ range (N+1), wt μ N k *
      ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N) := by
    have : μ i 0 = (∑ k ∈ range (N+1), (N.choose k : ℝ) * μ k (N - k) *
        (k.descFactorial i : ℝ)) / (N.descFactorial i : ℝ) := by
      rw [hmom]; field_simp
    rw [this, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [grid_prod k i N (by omega) hN, wt]
    ring
  rw [hμi, LN, ← sum_sub_distrib]
  calc |∑ k ∈ range (N+1), (wt μ N k * ((k:ℝ) / N) ^ i - wt μ N k *
        ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N))|
      ≤ ∑ k ∈ range (N+1), |wt μ N k * ((k:ℝ) / N) ^ i - wt μ N k *
        ∏ r ∈ range i, (((k:ℝ) / N) - r / N) / (1 - r / N)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (N+1), wt μ N k * (2 * i * i / N) := by
      refine sum_le_sum fun k hk => ?_
      have hk' : k ≤ N := by have := mem_range.1 hk; omega
      have hx0 : (0:ℝ) ≤ k / N := by positivity
      have hx1 : (k:ℝ) / N ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hk'
      rw [← mul_sub, abs_mul, abs_of_nonneg (wt_nonneg μ hμ N k)]
      gcongr
      · exact wt_nonneg μ hμ N k
      · exact (prodbound i _ hx0 hx1 N hN hiN).1
    _ = 2 * i * i / N := by rw [← sum_mul, wt_sum μ h h00, one_mul]

theorem mono_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (i : ℕ) :
    Tendsto (fun N => LN μ N (fun x => x ^ i)) atTop (𝓝 (μ i 0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 * i * i : ℝ))
  filter_upwards [eventually_ge_atTop (2 * i + 1)] with N hN
  rw [Real.norm_eq_abs]
  exact mono_bound μ hμ h h00 i N (by omega) (by omega)

abbrev I01 : Set ℝ := Set.Icc (0:ℝ) 1

noncomputable def LF (μ : ℕ → ℕ → ℝ) (N : ℕ) (f : C(I01, ℝ)) : ℝ :=
  ∑ k ∈ range (N+1), wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))

theorem LF_eq (μ : ℕ → ℕ → ℝ) (N : ℕ) (f : C(I01, ℝ)) (g : ℝ → ℝ)
    (hfg : ∀ y : I01, f y = g y) : LF μ N f = LN μ N g := by
  unfold LF LN
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by have := mem_range.1 hk; omega
  have hmem : (k:ℝ) / N ∈ I01 := by
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · rw [div_le_one (by exact_mod_cast h0)]; exact_mod_cast hk'
  rw [Set.projIcc_of_mem _ hmem, hfg]

theorem LF_add (μ : ℕ → ℕ → ℝ) (N : ℕ) (f g : C(I01, ℝ)) :
    LF μ N (f + g) = LF μ N f + LF μ N g := by
  simp only [LF, ContinuousMap.add_apply, mul_add, sum_add_distrib]

theorem LF_sub (μ : ℕ → ℕ → ℝ) (N : ℕ) (f g : C(I01, ℝ)) :
    LF μ N (f - g) = LF μ N f - LF μ N g := by
  simp only [LF, ContinuousMap.sub_apply, mul_sub, sum_sub_distrib]

theorem LF_smul (μ : ℕ → ℕ → ℝ) (N : ℕ) (c : ℝ) (f : C(I01, ℝ)) :
    LF μ N (c • f) = c * LF μ N f := by
  simp only [LF, ContinuousMap.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun k _ => by ring

theorem LF_nonneg (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (N : ℕ) (f : C(I01, ℝ))
    (hf : ∀ y, 0 ≤ f y) : 0 ≤ LF μ N f :=
  sum_nonneg fun k _ => mul_nonneg (wt_nonneg μ hμ N k) (hf _)

theorem LF_abs_le (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (N : ℕ) (f : C(I01, ℝ)) :
    |LF μ N f| ≤ ‖f‖ := by
  unfold LF
  calc |∑ k ∈ range (N+1), wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))|
      ≤ ∑ k ∈ range (N+1), |wt μ N k * f (Set.projIcc 0 1 zero_le_one ((k:ℝ) / N))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (N+1), wt μ N k * ‖f‖ := by
      refine sum_le_sum fun k _ => ?_
      rw [abs_mul, abs_of_nonneg (wt_nonneg μ hμ N k)]
      gcongr
      · exact wt_nonneg μ hμ N k
      · exact (Real.norm_eq_abs _ ▸ f.norm_coe_le_norm _)
    _ = ‖f‖ := by rw [← sum_mul, wt_sum μ h h00, one_mul]

theorem LF_poly_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (p : Polynomial ℝ) :
    Tendsto (fun N => LF μ N (p.toContinuousMapOn I01)) atTop
      (𝓝 (∑ d ∈ range (p.natDegree + 1), p.coeff d * μ d 0)) := by
  have e : ∀ N, LF μ N (p.toContinuousMapOn I01) =
      ∑ d ∈ range (p.natDegree + 1), p.coeff d * LN μ N (fun x => x ^ d) := by
    intro N
    rw [LF_eq μ N _ (fun x => p.eval x) (fun y => rfl)]
    unfold LN
    simp_rw [Polynomial.eval_eq_sum_range, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => sum_congr rfl fun k _ => by ring
  simp_rw [e]
  exact tendsto_finset_sum _ fun d _ => (mono_tendsto μ hμ h h00 d).const_mul _

theorem LF_cauchy (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (f : C(I01, ℝ)) :
    CauchySeq (fun N => LF μ N f) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hf : f ∈ (polynomialFunctions I01).topologicalClosure := by
    rw [polynomialFunctions_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hf
  obtain ⟨b, hb, hfb⟩ := hf (ε / 3) (by positivity)
  rw [polynomialFunctions_coe] at hb
  obtain ⟨p, rfl⟩ := hb
  have hc := (LF_poly_tendsto μ hμ h h00 p).cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨N0, hN0⟩ := hc (ε / 3) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have h1 := hN0 n hn
  rw [Real.dist_eq] at h1 ⊢
  rw [dist_eq_norm] at hfb
  have a1 := LF_abs_le μ hμ h h00 n (f - Polynomial.toContinuousMapOnAlgHom I01 p)
  have a2 := LF_abs_le μ hμ h h00 N0 (f - Polynomial.toContinuousMapOnAlgHom I01 p)
  rw [LF_sub] at a1 a2
  have : Polynomial.toContinuousMapOnAlgHom I01 p = p.toContinuousMapOn I01 := rfl
  rw [this] at a1 a2 hfb
  set A := LF μ n f
  set B := LF μ n (p.toContinuousMapOn I01)
  set C := LF μ N0 (p.toContinuousMapOn I01)
  set D := LF μ N0 f
  have h3 := abs_add_three (A - B) (B - C) (C - D)
  rw [show A - B + (B - C) + (C - D) = A - D by ring] at h3
  calc |A - D| < ε / 3 + ε / 3 + ε / 3 := by rw [abs_sub_comm D C] at a2; linarith
    _ = ε := by ring

noncomputable def LamF (μ : ℕ → ℕ → ℝ) (f : C(I01, ℝ)) : ℝ :=
  limUnder atTop (fun N => LF μ N f)

theorem LamF_tendsto (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) (f : C(I01, ℝ)) :
    Tendsto (fun N => LF μ N f) atTop (𝓝 (LamF μ f)) := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (LF_cauchy μ hμ h h00 f)
  unfold LamF
  exact tendsto_nhds_limUnder ⟨a, ha⟩

section LamFProps
variable (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1)
include hμ h h00

theorem LamF_add (f g : C(I01, ℝ)) : LamF μ (f + g) = LamF μ f + LamF μ g := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (f + g)) ?_
  simp_rw [LF_add]
  exact (LamF_tendsto μ hμ h h00 f).add (LamF_tendsto μ hμ h h00 g)

theorem LamF_sub (f g : C(I01, ℝ)) : LamF μ (f - g) = LamF μ f - LamF μ g := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (f - g)) ?_
  simp_rw [LF_sub]
  exact (LamF_tendsto μ hμ h h00 f).sub (LamF_tendsto μ hμ h h00 g)

theorem LamF_smul (c : ℝ) (f : C(I01, ℝ)) : LamF μ (c • f) = c * LamF μ f := by
  refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 (c • f)) ?_
  simp_rw [LF_smul]
  exact (LamF_tendsto μ hμ h h00 f).const_mul c

theorem LamF_nonneg (f : C(I01, ℝ)) (hf : ∀ y, 0 ≤ f y) : 0 ≤ LamF μ f :=
  ge_of_tendsto' (LamF_tendsto μ hμ h h00 f) fun N => LF_nonneg μ hμ N f hf

end LamFProps

noncomputable def gfun (i j : ℕ) : C(I01, ℝ) :=
  ⟨fun y => (y:ℝ) ^ i * (1 - (y:ℝ)) ^ j, by fun_prop⟩

theorem LamF_g (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) :
    ∀ j i, LamF μ (gfun i j) = μ i j := by
  intro j
  induction j with
  | zero =>
    intro i
    refine tendsto_nhds_unique (LamF_tendsto μ hμ h h00 _) ?_
    have e : ∀ N, LF μ N (gfun i 0) = LN μ N (fun x => x ^ i) :=
      fun N => LF_eq μ N _ _ (fun y => by simp [gfun])
    simp_rw [e]
    exact mono_tendsto μ hμ h h00 i
  | succ j ih =>
    intro i
    have e : gfun i (j+1) = gfun i j - gfun (i+1) j := by
      ext y; simp only [gfun, ContinuousMap.coe_mk, ContinuousMap.sub_apply]; ring
    rw [e, LamF_sub μ hμ h h00, ih, ih, h i j]
    ring

noncomputable def LamC (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) (h00 : μ 0 0 = 1) :
    C_c(I01, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => LamF μ f.toContinuousMap
      map_add' := fun f g => LamF_add μ hμ h h00 f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => LamF_smul μ hμ h h00 c f.toContinuousMap }
    (fun f hf => LamF_nonneg μ hμ h h00 _ (fun y => by
      have := CompactlySupportedContinuousMap.le_def.1 hf y
      simpa using this))

theorem hausdorff_exists (μ : ℕ → ℕ → ℝ) (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1)
    (h : ∀ i j, μ i j = μ (i+1) j + μ i (j+1)) :
    ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by
  set Λp := LamC μ hμ h h00
  set ν := RealRMK.rieszMeasure Λp
  have hg : ∀ i j, ∫ y, ((y:ℝ) ^ i * (1 - (y:ℝ)) ^ j) ∂ν = μ i j := by
    intro i j
    have := RealRMK.integral_rieszMeasure Λp
      (CompactlySupportedContinuousMap.continuousMapEquiv (gfun i j))
    rw [← LamF_g μ hμ h h00 j i]
    exact this
  have hν1 : ν Set.univ = 1 := by
    have := hg 0 0
    simp only [pow_zero, mul_one, integral_const, smul_eq_mul, h00] at this
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
    exact this
  refine ⟨ν.map Subtype.val, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ, hν1]
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc.compl]
    have : (Subtype.val ⁻¹' (Set.Icc (0:ℝ) 1)ᶜ : Set I01) = ∅ := by
      ext y; simp [y.2]
    rw [this, measure_empty]
  · intro i j
    rw [integral_map measurable_subtype_coe.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), hg]

theorem eq_24_iff_eq_25_core (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1) :
    (∀ i j, μ i j = μ (i + 1) j + μ i (j + 1)) ↔
      ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by
  constructor
  · exact hausdorff_exists μ hμ h00
  · rintro ⟨F, hF, hF0, hmom⟩ i j
    have hres : F.restrict (Set.Icc (0:ℝ) 1) = F := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hF0
    have hint : ∀ a b : ℕ, Integrable (fun x : ℝ => x ^ a * (1 - x) ^ b) F := by
      intro a b
      rw [← hres]
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    rw [hmom, hmom, hmom, ← integral_add (hint _ _) (hint _ _)]
    congr 1
    funext x
    ring

end Hausdorff

end LambdaCoalescent.Rates

open LambdaCoalescent.Rates
open MeasureTheory

theorem solution (μ : ℕ → ℕ → ℝ)
    (hμ : ∀ i j, 0 ≤ μ i j) (h00 : μ 0 0 = 1) :
    (∀ i j, μ i j = μ (i + 1) j + μ i (j + 1)) ↔
      ∃ F : Measure ℝ, IsProbabilityMeasure F ∧ F (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
        ∀ i j, μ i j = ∫ x, x ^ i * (1 - x) ^ j ∂F := by
  exact eq_24_iff_eq_25_core μ hμ h00
