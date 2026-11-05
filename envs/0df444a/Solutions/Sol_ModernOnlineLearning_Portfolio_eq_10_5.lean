-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.eq_10_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:06:13.383257+00:00
-- url     : https://prove2.me/submissions/6599b5b3-5216-488d-82f3-588b62913337

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
import Theorems.Thm_mme_fintype_fixed_fiber_function_card
set_option autoImplicit false

open MeasureTheory ModernOnlineLearning.Portfolio

theorem beta_nat_aux (b : ℕ) : ∀ (a : ℕ) (L : ℝ),
    ∫ x in (0:ℝ)..L, x ^ a * (L - x) ^ b =
      L ^ (a + b + 1) * (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  induction b with
  | zero =>
    intro a L
    simp only [pow_zero, mul_one, integral_pow, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [Nat.factorial_succ]
    have : (0:ℝ) ^ (a + 1) = 0 := by simp
    rw [this]; push_cast
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ b ih =>
    intro a L
    have e : (fun x : ℝ => x ^ a * (L - x) ^ (b + 1)) =
        fun x => L * (x ^ a * (L - x) ^ b) - x ^ (a + 1) * (L - x) ^ b := by
      funext x; ring
    rw [e, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), intervalIntegral.integral_const_mul,
      ih a L, ih (a + 1) L]
    rw [show a + 1 + b + 1 = a + (b + 1) + 1 by ring, show a + (b + 1) + 1 = (a + b + 1) + 1 by ring]
    rw [Nat.factorial_succ (a + b + 1), Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    have h1 : ((a + b + 1).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((a + b + 1 : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem measurableSet_simplex_aux (n : ℕ) :
    MeasurableSet {y : Fin n → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} := by
  measurability

theorem inner_lint_aux (a b : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∫⁻ x : ℝ, Set.indicator (Set.Icc 0 L) (fun x => ENNReal.ofReal (x ^ a * (L - x) ^ b)) x =
      ENNReal.ofReal (L ^ (a + b + 1) * (a.factorial : ℝ) * (b.factorial : ℝ) /
        ((a + b + 1).factorial : ℝ)) := by
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL, beta_nat_aux]
  · exact (by fun_prop : Continuous fun x : ℝ => x ^ a * (L - x) ^ b).integrableOn_Icc
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have := hx.1; have : 0 ≤ L - x := by linarith [hx.2]
    simp only [Pi.zero_apply]; positivity

theorem dirichlet_lint_aux : ∀ (n : ℕ) (a : Fin n → ℕ) (b : ℕ),
    ∫⁻ y : Fin n → ℝ, Set.indicator {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}
      (fun y => ENNReal.ofReal ((∏ i, y i ^ a i) * (1 - ∑ i, y i) ^ b)) y =
    ENNReal.ofReal ((∏ i, ((a i).factorial : ℝ)) * (b.factorial : ℝ) /
      ((∑ i, a i) + b + n).factorial) := by
  intro n
  induction n with
  | zero =>
    intro a b
    rw [lintegral_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, one_mul, sub_zero,
      one_pow, mul_one, zero_add, add_zero, ENNReal.ofReal_one]
    rw [div_self (by positivity), ENNReal.ofReal_one, Set.indicator_of_mem (by simp)]
    rw [MeasureTheory.volume_pi, Measure.pi_univ]; simp
  | succ n ih =>
    intro a b
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n) with he
    have hmp : MeasurePreserving e.symm (volume : Measure (ℝ × (Fin n → ℝ))) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)).symm e
    set f : (Fin (n+1) → ℝ) → ENNReal := Set.indicator {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}
      (fun y => ENNReal.ofReal ((∏ i, y i ^ a i) * (1 - ∑ i, y i) ^ b)) with hf
    have hfm : Measurable f := by
      apply Measurable.indicator _ (measurableSet_simplex_aux _)
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding f]
    rw [Measure.volume_eq_prod, lintegral_prod_symm' (fun p => f (e.symm p)) (hfm.comp e.symm.measurable)]
    set D : Set (Fin n → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} with hD
    have hpt : ∀ (y' : Fin n → ℝ) (x : ℝ), f (e.symm (x, y')) =
        Set.indicator D (fun y => ENNReal.ofReal (∏ i, y i ^ a (Fin.castSucc i))) y' *
        Set.indicator (Set.Icc 0 (1 - ∑ i, y' i))
          (fun x => ENNReal.ofReal (x ^ a (Fin.last n) * ((1 - ∑ i, y' i) - x) ^ b)) x := by
      intro y' x
      have hs : e.symm (x, y') = Fin.snoc y' x := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_last']
        rfl
      rw [hs, hf]
      by_cases h1 : y' ∈ D
      · by_cases h2 : x ∈ Set.Icc 0 (1 - ∑ i, y' i)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem]
          · rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (h1.1 i) _)]
            congr 1
            simp only [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
              Fin.snoc_last]
            ring
          · simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
              Fin.sum_univ_castSucc]
            exact ⟨⟨h1.1, h2.1⟩, by linarith [h2.2]⟩
        · rw [Set.indicator_of_notMem h2, mul_zero, Set.indicator_of_notMem]
          simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
            Fin.sum_univ_castSucc]
          rintro ⟨⟨_, hx⟩, hsum⟩
          exact h2 ⟨hx, by linarith⟩
      · rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem]
        simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
          Fin.sum_univ_castSucc]
        rintro ⟨⟨hy, hx⟩, hsum⟩
        exact h1 ⟨hy, by linarith⟩
    simp_rw [hpt]
    have hB : ∀ y' : Fin n → ℝ,
        ∫⁻ x, Set.indicator D (fun y => ENNReal.ofReal (∏ i, y i ^ a (Fin.castSucc i))) y' *
          Set.indicator (Set.Icc 0 (1 - ∑ i, y' i))
            (fun x => ENNReal.ofReal (x ^ a (Fin.last n) * ((1 - ∑ i, y' i) - x) ^ b)) x =
        Set.indicator D (fun y => ENNReal.ofReal ((∏ i, y i ^ a (Fin.castSucc i)) *
            (1 - ∑ i, y i) ^ (a (Fin.last n) + b + 1))) y' *
          ENNReal.ofReal ((a (Fin.last n)).factorial * (b.factorial : ℝ) /
            ((a (Fin.last n) + b + 1).factorial : ℝ)) := by
      intro y'
      rw [lintegral_const_mul]
      swap
      · exact Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop)) measurableSet_Icc
      by_cases h1 : y' ∈ D
      · have hL : 0 ≤ 1 - ∑ i, y' i := by linarith [h1.2]
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1, inner_lint_aux _ _ _ hL,
          ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => pow_nonneg (h1.1 i) _),
          ← ENNReal.ofReal_mul (by
            have := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => pow_nonneg (h1.1 i) (a (Fin.castSucc i))
            positivity)]
        congr 1
        ring
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1, zero_mul, zero_mul]
    simp_rw [hB]
    rw [lintegral_mul_const]
    swap
    · exact Measurable.indicator (ENNReal.measurable_ofReal.comp (by fun_prop))
        (measurableSet_simplex_aux _)
    rw [ih, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    rw [show (∑ i : Fin n, a (Fin.castSucc i)) + (a (Fin.last n) + b + 1) + n =
      (∑ i : Fin n, a (Fin.castSucc i)) + a (Fin.last n) + b + (n + 1) by ring]
    have h1 : ((a (Fin.last n) + b + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp

theorem prod_split_aux {d : ℕ} (hd : 1 ≤ d) {M : Type} [CommMonoid M] (h : Fin d → M) :
    ∏ i, h i = (∏ k : Fin (d - 1), h ⟨k, lt_of_lt_of_le k.2 (Nat.sub_le d 1)⟩) *
      h ⟨d - 1, Nat.sub_lt (by omega) one_pos⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]; rfl

theorem sum_split_aux {d : ℕ} (hd : 1 ≤ d) (h : Fin d → ℕ) :
    ∑ i, h i = (∑ k : Fin (d - 1), h ⟨k, lt_of_lt_of_le k.2 (Nat.sub_le d 1)⟩) +
      h ⟨d - 1, Nat.sub_lt (by omega) one_pos⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]; rfl

theorem monomial_eq_aux {d T : ℕ} (j : Fin T → Fin d) (u : Fin d → ℝ) :
    sequenceMonomial j u =
      ∏ i, u i ^ ((Finset.univ.filter (fun t : Fin T => j t = i)).card) := by
  unfold sequenceMonomial
  rw [← Fintype.prod_fiberwise' j u]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype]

theorem solution {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (j : Fin T → Fin d) :
    (∫ p, sequenceMonomial j p ∂uniformPrior d) =
      1 / (((T + d - 1).choose (d - 1) : ℕ) : ℝ) /
        ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ) := by
  have hd1 : 1 ≤ d := by omega
  set N : Fin d → ℕ := fun i => (Finset.univ.filter (fun t : Fin T => j t = i)).card with hN
  set a : Fin (d - 1) → ℕ := fun k => N ⟨k, lt_of_lt_of_le k.2 (Nat.sub_le d 1)⟩ with ha
  set b : ℕ := N ⟨d - 1, Nat.sub_lt (by omega) one_pos⟩ with hb
  have hg : ∀ y : Fin (d - 1) → ℝ, sequenceMonomial j (chartPortfolio d y) =
      (∏ k, y k ^ a k) * (1 - ∑ k, y k) ^ b := by
    intro y
    rw [monomial_eq_aux, prod_split_aux hd1]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp [chartPortfolio, a, N]
    · simp [chartPortfolio, b, N]
  have hcont : Continuous (sequenceMonomial (d := d) j) := by
    unfold sequenceMonomial; fun_prop
  rw [uniformPrior, integral_map (measurable_chartPortfolio d).aemeasurable
    hcont.aestronglyMeasurable, integral_smul_measure]
  simp_rw [hg]
  have hnn : 0 ≤ᵐ[volume.restrict (chartDomain d)]
      fun y : Fin (d - 1) → ℝ => (∏ k, y k ^ a k) * (1 - ∑ k, y k) ^ b := by
    rw [Filter.EventuallyLE, ae_restrict_iff' (measurableSet_chartDomain d)]
    refine Filter.Eventually.of_forall fun y hy => ?_
    have h1 : 0 ≤ 1 - ∑ k, y k := by linarith [hy.2]
    simp only [Pi.zero_apply]
    exact mul_nonneg (Finset.prod_nonneg fun k _ => pow_nonneg (hy.1 k) _) (pow_nonneg h1 _)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (by fun_prop : Continuous fun y : Fin (d - 1) → ℝ =>
      (∏ k, y k ^ a k) * (1 - ∑ k, y k) ^ b).aestronglyMeasurable]
  rw [← lintegral_indicator (measurableSet_chartDomain d)]
  rw [show chartDomain d = {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} from rfl]
  rw [dirichlet_lint_aux (d - 1) a b]
  -- arithmetic
  have hsumN : ∑ i, N i = T := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin T)))
      (t := (Finset.univ : Finset (Fin d))) (f := j) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hab : (∑ k, a k) + b = T := by rw [← hsumN, sum_split_aux hd1]
  have hP : (∏ k, ((a k).factorial : ℝ)) * (b.factorial : ℝ) = ∏ i, ((N i).factorial : ℝ) := by
    rw [prod_split_aux hd1 (fun i => ((N i).factorial : ℝ))]
  rw [hab, hP]
  -- the type class
  have hcard : (typeClass (d := d) (T := T) (sequenceType j)).card =
      T.factorial / ∏ i, (N i).factorial := by
    have h := mme_fintype_fixed_fiber_function_card j
    simp only [Fintype.card_fin, Fintype.card_subtype] at h
    rw [← h, typeClass]
    have hT0 : (T : ℝ) ≠ 0 := by positivity
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro g _
    simp only [sequenceType, funext_iff, div_left_inj' hT0, Nat.cast_inj]
  have hdvd : ∏ i, (N i).factorial ∣ T.factorial := by
    have := Nat.prod_factorial_dvd_factorial_sum Finset.univ N
    rwa [hsumN] at this
  have hPpos : 0 < ∏ i, (N i).factorial := Finset.prod_pos fun i _ => Nat.factorial_pos _
  rw [hcard, Nat.cast_div hdvd (by exact_mod_cast hPpos.ne')]
  have hC := Nat.choose_mul_factorial_mul_factorial (show d - 1 ≤ T + d - 1 by omega)
  rw [show T + d - 1 - (d - 1) = T by omega] at hC
  have hC' : ((T + d - 1).factorial : ℝ) =
      ((T + d - 1).choose (d - 1) : ℝ) * ((d - 1).factorial : ℝ) * (T.factorial : ℝ) := by
    exact_mod_cast hC.symm
  rw [show T + (d - 1) = T + d - 1 by omega, hC']
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, smul_eq_mul]
  push_cast
  have h1 : ((T + d - 1).choose (d - 1) : ℝ) ≠ 0 := by
    have : 0 < (T + d - 1).choose (d - 1) := Nat.choose_pos (by omega)
    positivity
  have h2 : ((d - 1).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (T.factorial : ℝ) ≠ 0 := by positivity
  have h4 : (∏ i, ((N i).factorial : ℝ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _; positivity
  field_simp
