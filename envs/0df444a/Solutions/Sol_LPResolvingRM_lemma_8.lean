-- Prove2me | solution 1 for LPResolvingRM.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:23:09.841194+00:00
-- url     : https://prove2.me/submissions/c37cc3d8-b6a4-40a5-82ee-1e26b8e0c1f8

import Mathlib

open MeasureTheory ProbabilityTheory

lemma hoeff_fin {d : ℕ} (q : Fin d → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (x : Fin d → ℝ) (hx : ∀ j, x j ∈ Set.Icc (-1:ℝ) 1) (u : ℝ) (hu : 0 < u) :
    ∑ j, q j * Real.exp (u * (x j - ∑ i, q i * x i)) ≤ Real.exp (u ^ 2 / 2) := by
  set μ : Measure (Fin d) := ∑ j, (ENNReal.ofReal (q j)) • Measure.dirac j with hμ
  have hint : ∀ f : Fin d → ℝ, ∫ a, f a ∂μ = ∑ j, q j * f j := by
    intro f
    rw [hμ, integral_finset_sum_measure (fun j _ => by
      apply Integrable.smul_measure (integrable_dirac enorm_lt_top) ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl; intro j _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq0 j), smul_eq_mul]
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq0 j), hq1, ENNReal.ofReal_one]
  set m := ∑ i, q i * x i with hm
  set X : Fin d → ℝ := fun j => x j - m with hX
  have hmean : μ[X] = 0 := by
    rw [hint]; simp only [hX, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul, hm]
    ring
  have hb : ∀ᵐ j ∂μ, X j ∈ Set.Icc (-1 - m) (1 - m) := by
    filter_upwards with j
    exact ⟨by simp only [hX]; linarith [(hx j).1], by simp only [hX]; linarith [(hx j).2]⟩
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero (μ := μ) (X := X)
    (Measurable.of_discrete).aemeasurable hb hmean hu
  rw [mgf, hint] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  have : ‖(1 - m) - (-1 - m)‖₊ = 2 := by
    rw [show (1 - m) - (-1 - m) = (2:ℝ) by ring]; simp
  rw [this]; norm_num

def sg (b : Bool) : ℝ := if b then 1 else -1

lemma count_sum {t d : ℕ} (ω : Fin t → Fin d) (x : Fin d → ℝ) :
    ∑ j, x j * ((Finset.univ.filter fun s => ω s = j).card : ℝ) = ∑ s, x (ω s) := by
  have : ∀ j, x j * ((Finset.univ.filter fun s => ω s = j).card : ℝ) =
      ∑ s ∈ Finset.univ.filter (fun s => ω s = j), x (ω s) := by
    intro j
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
      Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [this]
  exact Finset.sum_fiberwise Finset.univ ω (fun s => x (ω s))

lemma Y_eq {t d : ℕ} (ht0 : (0:ℝ) < t) (q : Fin d → ℝ) (ω : Fin t → Fin d) (σ : Fin d → Bool) :
    ∑ j, sg (σ j) * (((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j) =
      (∑ s, sg (σ (ω s))) / t - ∑ j, q j * sg (σ j) := by
  rw [← count_sum ω (fun j => sg (σ j)), Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

lemma exp_form {t d : ℕ} (ht0 : (0:ℝ) < t) (q : Fin d → ℝ) (ε : ℝ) (ω : Fin t → Fin d)
    (σ : Fin d → Bool) :
    Real.exp (-(t * ε ^ 2)) * ∏ s, Real.exp (ε * (sg (σ (ω s)) - ∑ j, q j * sg (σ j))) =
      Real.exp ((t * ε) * (∑ j, sg (σ j) * (((Finset.univ.filter fun s => ω s = j).card : ℝ) / t
        - q j) - ε)) := by
  rw [← Real.exp_sum, ← Real.exp_add, Y_eq ht0 q ω σ]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma ind_le {t d : ℕ} (ht0 : (0:ℝ) < t) (q : Fin d → ℝ) (ε : ℝ) (hε : 0 < ε) (ω : Fin t → Fin d) :
    (if ε ≤ ∑ j, |((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j| then (1:ℝ) else 0) ≤
      ∑ σ : Fin d → Bool, Real.exp (-(t * ε ^ 2)) *
        ∏ s, Real.exp (ε * (sg (σ (ω s)) - ∑ j, q j * sg (σ j))) := by
  simp_rw [exp_form ht0 q ε ω]
  split_ifs with hcond
  · let σ0 : Fin d → Bool := fun j =>
      decide (0 ≤ ((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j)
    have hsel : ∑ j, sg (σ0 j) * (((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j) =
        ∑ j, |((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j| := by
      apply Finset.sum_congr rfl; intro j _
      simp only [σ0, sg]
      split_ifs with h
      · rw [abs_of_nonneg (by simpa using h)]; ring
      · rw [abs_of_neg (by simpa using h)]; ring
    refine le_trans ?_ (Finset.single_le_sum (fun σ _ => (Real.exp_pos _).le) (Finset.mem_univ σ0))
    rw [hsel]; apply Real.one_le_exp
    exact mul_nonneg (by positivity) (by linarith)
  · exact Finset.sum_nonneg (fun σ _ => (Real.exp_pos _).le)

lemma factor {t d : ℕ} (q : Fin d → ℝ) (g : Fin d → ℝ) :
    ∑ ω : Fin t → Fin d, (∏ s, q (ω s)) * ∏ s, g (ω s) = (∑ j, q j * g j) ^ t := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  apply Finset.sum_congr rfl; intro ω _
  rw [← Finset.prod_mul_distrib]

theorem solution {d : ℕ} (q : Fin d → ℝ) (hq_sum : ∑ j, q j = 1) (hq : ∀ j, 0 < q j ∧ q j < 1)
    (t : ℕ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∑ ω : Fin t → Fin d, (∏ s, q (ω s)) *
        (if ε ≤ ∑ j, |((Finset.univ.filter fun s => ω s = j).card : ℝ) / t - q j| then 1 else 0)
      ≤ 2 ^ d * Real.exp (-(t * ε ^ 2 / 2)) := by
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hP : ∀ ω : Fin t → Fin d, 0 ≤ ∏ s, q (ω s) :=
    fun ω => Finset.prod_nonneg (fun s _ => (hq (ω s)).1.le)
  calc _ ≤ ∑ ω : Fin t → Fin d, (∏ s, q (ω s)) * ∑ σ : Fin d → Bool, Real.exp (-(t * ε ^ 2)) *
          ∏ s, Real.exp (ε * (sg (σ (ω s)) - ∑ j, q j * sg (σ j))) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (ind_le ht0 q ε hε ω) (hP ω))
    _ = ∑ σ : Fin d → Bool, Real.exp (-(t * ε ^ 2)) *
          (∑ j, q j * Real.exp (ε * (sg (σ j) - ∑ i, q i * sg (σ i)))) ^ t := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro σ _
        rw [← factor q (fun j => Real.exp (ε * (sg (σ j) - ∑ i, q i * sg (σ i)))), Finset.mul_sum]
        apply Finset.sum_congr rfl; intro ω _
        ring
    _ ≤ ∑ _σ : Fin d → Bool, Real.exp (-(t * ε ^ 2)) * Real.exp (ε ^ 2 / 2) ^ t := by
        apply Finset.sum_le_sum; intro σ _
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => mul_nonneg (hq j).1.le
          (Real.exp_pos _).le))
        exact hoeff_fin q (fun j => (hq j).1.le) hq_sum (fun j => sg (σ j))
          (fun j => by simp only [sg]; split_ifs <;> norm_num) ε hε
    _ = 2 ^ d * Real.exp (-(t * ε ^ 2 / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        push_cast
        congr 1
        ring
