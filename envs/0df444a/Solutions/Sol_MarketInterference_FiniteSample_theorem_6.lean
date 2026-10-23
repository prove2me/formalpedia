-- Prove2me | solution 1 for MarketInterference.FiniteSample.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T20:25:45.94399+00:00
-- url     : https://prove2.me/submissions/a2b235fa-11e5-4e49-8eaa-37d673c3649b

import Definitions.Def_MarketInterference_FiniteSample_Experiment

namespace MarketInterference.FiniteSample.Mk6

open MeasureTheory ProbabilityTheory Real
open MarketInterference.FluidBias MarketInterference.FiniteSample

noncomputable def pw (m : ℝ) (k : ℕ) : ℝ := exp (-m) * m ^ k / (k.factorial : ℝ)

lemma pw_nonneg {m : ℝ} (hm : 0 ≤ m) (k : ℕ) : 0 ≤ pw m k := by
  unfold pw; positivity

lemma pw_succ (m : ℝ) (k : ℕ) : pw m (k + 1) * ((k : ℝ) + 1) = m * pw m k := by
  unfold pw
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasDerivAt_pw {m : ℝ} (hm : 0 < m) (k : ℕ) :
    HasDerivAt (fun x => pw x k) (pw m k * ((k : ℝ) / m - 1)) m := by
  have h : HasDerivAt (fun x => pw x k) _ m :=
    (((hasDerivAt_neg m).exp).mul (hasDerivAt_pow k m)).div_const (k.factorial : ℝ)
  refine h.congr_deriv ?_
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold pw
  rcases k with _ | j
  · simp
  · push_cast
    rw [pow_succ]
    field_simp
    ring

lemma integral_eq_tsum {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) :
    ∫ x, f x ∂μ = ∑' x, μ.real {x} * f x := by
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  rw [integral_sum_dirac (fun a => measure_ne_top μ _)]
  rfl

instance poisLaw_isProb {n : ℕ} (m : Fin n → ℝ) : IsProbabilityMeasure (poisLaw m) := by
  unfold poisLaw; infer_instance

lemma poisLaw_real_singleton {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (d : Fin n → ℕ) :
    (poisLaw m).real {d} = ∏ i, pw (m i) (d i) := by
  unfold poisLaw
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← measureReal_def, poissonMeasure_real_singleton, Real.coe_toNNReal _ (hm i)]
  rfl

lemma summable_pwprod {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) :
    Summable (fun d : Fin n → ℕ => ∏ i, pw (m i) (d i)) := by
  have h := integral_eq_tsum (poisLaw m) (fun _ => (1 : ℝ))
  by_contra hns
  have : ¬ Summable (fun d : Fin n → ℕ => (poisLaw m).real {d} * 1) := by
    simpa [poisLaw_real_singleton m hm] using hns
  rw [tsum_eq_zero_of_not_summable this] at h
  simp at h

lemma obj_bound {nd ns : ℕ} {I E : Type} [Fintype E] (N : Network nd ns I E) (τ : ℝ)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ τ * N.k e) :
    |obj N x| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  unfold obj
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul, abs_of_nonneg (hx e).1]
  exact mul_le_mul_of_nonneg_left (hx e).2 (abs_nonneg _)

lemma Phi_bound {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I] (N : Network nd ns I E)
    {τ : ℝ} (hτ : 0 ≤ τ) (d : Fin nd → ℝ) (s : Fin ns → ℝ) :
    |Phi N τ d s| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
  have hB : 0 ≤ ∑ e, |N.v e| * (τ * N.k e) :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (mul_nonneg hτ (N.k_nonneg e))
  unfold Phi
  set S := obj N '' {x | Feasible N τ d s x}
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]; simpa using hB
  · have hb : ∀ y ∈ S, |y| ≤ ∑ e, |N.v e| * (τ * N.k e) := by
      rintro y ⟨x, hx, rfl⟩
      exact obj_bound N τ x hx.1
    have hbdd : BddAbove S := ⟨_, fun y hy => (abs_le.1 (hb y hy)).2⟩
    rw [abs_le]
    constructor
    · obtain ⟨y, hy⟩ := h
      exact (abs_le.1 (hb y hy)).1.trans (le_csSup hbdd hy)
    · exact csSup_le h fun y hy => (abs_le.1 (hb y hy)).2

lemma sh_injective {n : ℕ} (i : Fin n) :
    Function.Injective (fun d : Fin n → ℕ => d + Pi.single i 1) := add_left_injective _

lemma mem_range_sh {n : ℕ} (i : Fin n) (d : Fin n → ℕ) (h : d i ≠ 0) :
    d ∈ Set.range (fun d : Fin n → ℕ => d + Pi.single i 1) := by
  refine ⟨d - Pi.single i 1, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [Pi.single_apply, hj]

lemma prod_pw_sh {n : ℕ} (m : Fin n → ℝ) (d : Fin n → ℕ) (i : Fin n) :
    (∏ j, pw (m j) ((d + Pi.single i 1 : Fin n → ℕ) j)) * ((d i : ℝ) + 1) = m i * ∏ j, pw (m j) (d j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => pw (m j) (d j)) (Finset.mem_univ i)]
  have : ∏ j ∈ Finset.univ.erase i, pw (m j) ((d + Pi.single i 1 : Fin n → ℕ) j) =
      ∏ j ∈ Finset.univ.erase i, pw (m j) (d j) :=
    Finset.prod_congr rfl fun j hj => by simp [Pi.single_apply, Finset.ne_of_mem_erase hj]
  rw [this]
  simp only [Pi.add_apply, Pi.single_eq_same]
  have h := pw_succ (m i) (d i)
  linear_combination (∏ j ∈ Finset.univ.erase i, pw (m j) (d j)) * h

lemma cast_sh {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    (fun j => (((d + Pi.single i 1 : Fin n → ℕ) j : ℕ) : ℝ)) = (fun j => (d j : ℝ)) + Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

lemma stein {α : Type*} (σ : α → α) (hσ : Function.Injective σ) (w c H : α → ℝ) (m : ℝ)
    (hc : ∀ a, c a ≠ 0 → a ∈ Set.range σ) (hw : ∀ a, w (σ a) * c (σ a) = m * w a) :
    ∑' a, w a * c a * H a = m * ∑' a, w a * H (σ a) := by
  rw [← tsum_mul_left, ← hσ.tsum_eq (f := fun a => w a * c a * H a)]
  · congr 1; funext a
    have := hw a
    linear_combination H (σ a) * this
  · intro a ha
    apply hc
    intro h0; apply ha; simp [h0]

lemma pw_two_pow_le {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (k : ℕ) :
    pw m k * 2 ^ k ≤ (2 * M) ^ k / (k.factorial : ℝ) := by
  unfold pw
  have h1 : exp (-m) ≤ 1 := by rw [exp_le_one_iff]; linarith
  have h2 : m ^ k ≤ M ^ k := pow_le_pow_left₀ hm hmM k
  have h3 : exp (-m) * m ^ k ≤ M ^ k := by
    calc exp (-m) * m ^ k ≤ 1 * M ^ k :=
          mul_le_mul h1 h2 (pow_nonneg hm _) zero_le_one
      _ = M ^ k := one_mul _
  rw [mul_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
  calc exp (-m) * m ^ k * 2 ^ k ≤ M ^ k * 2 ^ k := by gcongr
    _ = 2 ^ k * M ^ k := by ring

lemma prod_pw_le {n : ℕ} (m M : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (hmM : ∀ i, m i ≤ M i)
    (d : Fin n → ℕ) :
    (∏ i, pw (m i) (d i)) * ∏ i, (2 : ℝ) ^ (d i) ≤
      ∏ i, (2 * M i) ^ (d i) / ((d i).factorial : ℝ) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _ => mul_nonneg (pw_nonneg (hm i) _) (by positivity))
    fun i _ => pw_two_pow_le (hm i) (hmM i) _

lemma one_le_prod_two_pow {n : ℕ} (d : Fin n → ℕ) : (1 : ℝ) ≤ ∏ i, (2 : ℝ) ^ (d i) := by
  have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ)) (g := fun i => (2 : ℝ) ^ (d i))
    (fun _ _ => zero_le_one) (fun i _ => one_le_pow₀ one_le_two)
  simpa using this

lemma succ_le_prod_two_pow {n : ℕ} (d : Fin n → ℕ) (i : Fin n) :
    (d i : ℝ) + 1 ≤ ∏ j, (2 : ℝ) ^ (d j) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have h1 : (d i : ℝ) + 1 ≤ 2 ^ (d i) := by
    have : d i + 1 ≤ 2 ^ (d i) := Nat.lt_two_pow_self
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ ∏ j ∈ Finset.univ.erase i, (2 : ℝ) ^ (d j) := by
    have := Finset.prod_le_prod (s := Finset.univ.erase i) (f := fun _ => (1 : ℝ))
      (g := fun j => (2 : ℝ) ^ (d j)) (fun _ _ => zero_le_one) (fun j _ => one_le_pow₀ one_le_two)
    simpa using this
  nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (d i)]

lemma summable_E {n : ℕ} (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) :
    Summable (fun d : Fin n → ℕ => ∏ i, (2 * M i) ^ (d i) / ((d i).factorial : ℝ)) := by
  have h := (summable_pwprod (fun i => 2 * M i) (fun i => by linarith [hM i])).mul_left
    (∏ i, exp (2 * M i))
  refine h.congr fun d => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold pw
  rw [show exp (2 * M i) * (exp (-(2 * M i)) * (2 * M i) ^ (d i) / ((d i).factorial : ℝ)) =
    (exp (2 * M i) * exp (-(2 * M i))) * ((2 * M i) ^ (d i) / ((d i).factorial : ℝ)) by ring,
    ← exp_add]
  simp

lemma E_nonneg {n : ℕ} (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (d : Fin n → ℕ) :
    0 ≤ ∏ i, (2 * M i) ^ (d i) / ((d i).factorial : ℝ) :=
  Finset.prod_nonneg fun i _ => by have := hM i; positivity

lemma summable_bound {α β : Type*} (f : α → ℝ) (g : β → ℝ) (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) (F : α × β → ℝ) (C : ℝ)
    (hF : ∀ z, |F z| ≤ C * (f z.1 * g z.2)) : Summable F :=
  Summable.of_norm_bounded ((hf.mul_of_nonneg hg hf0 hg0).mul_left C) (fun z => by simpa using hF z)

instance marketLaw_isProb {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ η : ℝ) :
    IsProbabilityMeasure (marketLaw lam beta pi τ η) := by
  unfold marketLaw; infer_instance

instance experimentLaw_isProb {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ) :
    IsProbabilityMeasure (experimentLaw lam beta pi ρ τ) := by
  unfold experimentLaw; infer_instance

lemma superpos {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ)
    (h1 : ∀ i, 0 ≤ (1 - ρ) * lam i * τ) (h2 : ∀ i, 0 ≤ ρ * (lam i + beta i) * τ) :
    (experimentLaw lam beta pi ρ τ).map (fun w => (w.1.1 + w.1.2, w.2)) =
      marketLaw lam beta pi τ ρ := by
  unfold experimentLaw marketLaw
  have hmap : (fun w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) => (w.1.1 + w.1.2, w.2)) =
      Prod.map (fun p : (Fin nd → ℕ) × (Fin nd → ℕ) => p.1 + p.2) id := rfl
  rw [hmap, ← Measure.map_prod_map _ _ Measurable.of_discrete measurable_id, Measure.map_id]
  congr 1
  unfold poisLaw
  rw [← (measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin nd)
    (fun i => poissonMeasure (Real.toNNReal ((1 - ρ) * lam i * τ)))
    (fun i => poissonMeasure (Real.toNNReal (ρ * (lam i + beta i) * τ)))).map_eq,
    Measure.map_map Measurable.of_discrete (MeasurableEquiv.measurable _)]
  have hc : (fun p : (Fin nd → ℕ) × (Fin nd → ℕ) => p.1 + p.2) ∘
      (MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin nd)) =
      fun x i => (fun q : ℕ × ℕ => q.1 + q.2) (x i) := by
    funext x i; rfl
  have hconv : ∀ i, ((poissonMeasure (Real.toNNReal ((1 - ρ) * lam i * τ))).prod
      (poissonMeasure (Real.toNNReal (ρ * (lam i + beta i) * τ)))).map
        (fun q : ℕ × ℕ => q.1 + q.2) =
      poissonMeasure (Real.toNNReal ((lam i + ρ * beta i) * τ)) := by
    intro i
    change (poissonMeasure _ ∗ poissonMeasure _) = _
    rw [poissonMeasure_conv_poissonMeasure, ← Real.toNNReal_add (h1 i) (h2 i)]
    congr 2; ring
  have : ∀ i, SigmaFinite (((poissonMeasure (Real.toNNReal ((1 - ρ) * lam i * τ))).prod
      (poissonMeasure (Real.toNNReal (ρ * (lam i + beta i) * τ)))).map
        (fun q : ℕ × ℕ => q.1 + q.2)) := fun i => by rw [hconv i]; infer_instance
  rw [hc]
  refine (Measure.pi_map_pi (f := fun _ (q : ℕ × ℕ) => q.1 + q.2)
    (fun i => Measurable.of_discrete.aemeasurable)).trans ?_
  congr 1; funext i; exact hconv i

lemma hasDerivAt_pw_aff (l b τ η : ℝ) (k : ℕ) (h : b ≠ 0 → 0 < (l + η * b) * τ) :
    HasDerivAt (fun x => pw ((l + x * b) * τ) k)
      (b * τ * (pw ((l + η * b) * τ) k * ((k : ℝ) / ((l + η * b) * τ) - 1))) η := by
  by_cases hb : b = 0
  · subst hb; simp only [mul_zero, add_zero, zero_mul]; exact hasDerivAt_const _ _
  · have h1 : HasDerivAt (fun x => (l + x * b) * τ) (b * τ) η := by
      have := (((hasDerivAt_id η).mul_const b).const_add l).mul_const τ
      simpa using this
    have := (hasDerivAt_pw (h hb) k).comp η h1
    exact this.congr_deriv (by ring)

noncomputable def Wd {nd : ℕ} (lam beta : Fin nd → ℝ) (τ η : ℝ) (d : Fin nd → ℕ) : ℝ :=
  ∏ i, pw ((lam i + η * beta i) * τ) (d i)

noncomputable def Ws {ns : ℕ} (pi : Fin ns → ℝ) (τ : ℝ) (s : Fin ns → ℕ) : ℝ :=
  ∏ j, pw (pi j * τ) (s j)

noncomputable def Lf {nd : ℕ} (lam beta : Fin nd → ℝ) (τ η : ℝ) (d : Fin nd → ℕ) : ℝ :=
  ∑ i, beta i * τ * ((d i : ℝ) / ((lam i + η * beta i) * τ) - 1)

lemma hasDerivAt_Wd {nd : ℕ} (lam beta : Fin nd → ℝ) (τ η : ℝ) (d : Fin nd → ℕ)
    (h : ∀ i, beta i ≠ 0 → 0 < (lam i + η * beta i) * τ) :
    HasDerivAt (fun x => Wd lam beta τ x d) (Wd lam beta τ η d * Lf lam beta τ η d) η := by
  unfold Wd Lf
  have := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => hasDerivAt_pw_aff (lam i) (beta i) τ η (d i) (h i))
  refine this.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
  ring

lemma abs_div_sub_one_le (d μ : ℝ) (hd : 0 ≤ d) (hμ : 0 ≤ μ) :
    |d / μ - 1| ≤ (1 / μ + 1) * (d + 1) := by
  have h1 : 0 ≤ 1 / μ := by positivity
  have h2 : d / μ = (1 / μ) * d := by ring
  rw [abs_le, h2]
  constructor <;> nlinarith [mul_nonneg h1 hd]

lemma Lf_bound {nd : ℕ} (lam beta : Fin nd → ℝ) (τ η : ℝ) (hτ : 0 < τ) (a : Fin nd → ℝ)
    (ha : ∀ i, beta i ≠ 0 → 0 < a i ∧ a i ≤ (lam i + η * beta i) * τ) (d : Fin nd → ℕ) :
    |Lf lam beta τ η d| ≤ (∑ i, |beta i| * τ * (1 / a i + 1)) * ∏ i, (2 : ℝ) ^ (d i) := by
  unfold Lf
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases hb : beta i = 0
  · simp [hb]
  · obtain ⟨ha0, hamu⟩ := ha i hb
    have hmu : 0 < (lam i + η * beta i) * τ := ha0.trans_le hamu
    have hd : (0 : ℝ) ≤ d i := Nat.cast_nonneg _
    have h1 : |(d i : ℝ) / ((lam i + η * beta i) * τ) - 1| ≤ (1 / a i + 1) * ((d i : ℝ) + 1) := by
      refine (abs_div_sub_one_le _ _ hd hmu.le).trans ?_
      gcongr
    rw [abs_mul, abs_mul, abs_of_pos hτ]
    calc |beta i| * τ * |(d i : ℝ) / ((lam i + η * beta i) * τ) - 1|
        ≤ |beta i| * τ * ((1 / a i + 1) * ((d i : ℝ) + 1)) := by gcongr
      _ ≤ |beta i| * τ * ((1 / a i + 1) * ∏ j, (2 : ℝ) ^ (d j)) := by
          have := succ_le_prod_two_pow d i
          have : 0 ≤ 1 / a i + 1 := by have := ha0.le; positivity
          gcongr
      _ = |beta i| * τ * (1 / a i + 1) * ∏ j, (2 : ℝ) ^ (d j) := by ring

lemma Wd_nonneg {nd : ℕ} (lam beta : Fin nd → ℝ) (τ η : ℝ)
    (hm : ∀ i, 0 ≤ (lam i + η * beta i) * τ) (d : Fin nd → ℕ) : 0 ≤ Wd lam beta τ η d :=
  Finset.prod_nonneg fun i _ => pw_nonneg (hm i) _

lemma Ws_nonneg {ns : ℕ} (pi : Fin ns → ℝ) (τ : ℝ) (hs : ∀ j, 0 ≤ pi j * τ) (s : Fin ns → ℕ) :
    0 ≤ Ws pi τ s :=
  Finset.prod_nonneg fun j _ => pw_nonneg (hs j) _

lemma summable_Ws {ns : ℕ} (pi : Fin ns → ℝ) (τ : ℝ) (hs : ∀ j, 0 ≤ pi j * τ) :
    Summable (Ws pi τ) :=
  summable_pwprod (fun j => pi j * τ) hs

/-- generic summability on the market space -/
lemma summable_mkt {nd ns : ℕ} (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ η : ℝ)
    (M : Fin nd → ℝ) (hm : ∀ i, 0 ≤ (lam i + η * beta i) * τ)
    (hmM : ∀ i, (lam i + η * beta i) * τ ≤ M i) (hs : ∀ j, 0 ≤ pi j * τ)
    (Y : (Fin nd → ℕ) × (Fin ns → ℕ) → ℝ) (C : ℝ)
    (hY : ∀ z, |Y z| ≤ C * ∏ i, (2 : ℝ) ^ (z.1 i)) :
    Summable (fun z => Wd lam beta τ η z.1 * Ws pi τ z.2 * Y z) := by
  have hM : ∀ i, 0 ≤ M i := fun i => (hm i).trans (hmM i)
  refine summable_bound _ _ (summable_E M hM) (summable_Ws pi τ hs) (E_nonneg M hM)
    (Ws_nonneg pi τ hs) _ C fun z => ?_
  have hW := Wd_nonneg lam beta τ η hm z.1
  have hS := Ws_nonneg pi τ hs z.2
  have hle := prod_pw_le (fun i => (lam i + η * beta i) * τ) M hm hmM z.1
  have hC : 0 ≤ C := by
    have h1 := one_le_prod_two_pow z.1
    nlinarith [abs_nonneg (Y z), hY z]
  rw [abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hS]
  calc Wd lam beta τ η z.1 * Ws pi τ z.2 * |Y z|
      ≤ Wd lam beta τ η z.1 * Ws pi τ z.2 * (C * ∏ i, (2 : ℝ) ^ (z.1 i)) := by gcongr; exact hY z
    _ = C * ((Wd lam beta τ η z.1 * ∏ i, (2 : ℝ) ^ (z.1 i)) * Ws pi τ z.2) := by ring
    _ ≤ C * ((∏ i, (2 * M i) ^ (z.1 i) / ((z.1 i).factorial : ℝ)) * Ws pi τ z.2) := by
        gcongr; exact hle

noncomputable def Wp {n : ℕ} (m : Fin n → ℝ) (d : Fin n → ℕ) : ℝ := ∏ i, pw (m i) (d i)

lemma Wp_nonneg {n : ℕ} (m : Fin n → ℝ) (hm : ∀ i, 0 ≤ m i) (d : Fin n → ℕ) : 0 ≤ Wp m d :=
  Finset.prod_nonneg fun i _ => pw_nonneg (hm i) _

lemma summable_exp {nd ns : ℕ} (mc mt : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ : ℝ)
    (hc : ∀ i, 0 ≤ mc i) (ht : ∀ i, 0 ≤ mt i) (hs : ∀ j, 0 ≤ pi j * τ)
    (Y : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ) (C : ℝ)
    (hY : ∀ w, |Y w| ≤ C * ((∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i))) :
    Summable (fun w => Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * Y w) := by
  have hf := (summable_E mc hc).mul_of_nonneg (summable_E mt ht) (E_nonneg mc hc) (E_nonneg mt ht)
  refine summable_bound _ _ hf (summable_Ws pi τ hs)
    (fun p => mul_nonneg (E_nonneg mc hc p.1) (E_nonneg mt ht p.2))
    (Ws_nonneg pi τ hs) _ C fun w => ?_
  have hW1 := Wp_nonneg mc hc w.1.1
  have hW2 := Wp_nonneg mt ht w.1.2
  have hS := Ws_nonneg pi τ hs w.2
  have hle1 := prod_pw_le mc mc hc (fun _ => le_rfl) w.1.1
  have hle2 := prod_pw_le mt mt ht (fun _ => le_rfl) w.1.2
  have hC : 0 ≤ C := by
    have h1 := one_le_prod_two_pow w.1.1
    have h2 := one_le_prod_two_pow w.1.2
    nlinarith [abs_nonneg (Y w), hY w, mul_le_mul h1 h2 zero_le_one (by linarith)]
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW1, abs_of_nonneg hW2, abs_of_nonneg hS]
  calc Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * |Y w|
      ≤ Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 *
          (C * ((∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i))) := by gcongr; exact hY w
    _ = C * (((Wp mc w.1.1 * ∏ i, (2 : ℝ) ^ (w.1.1 i)) *
          (Wp mt w.1.2 * ∏ i, (2 : ℝ) ^ (w.1.2 i))) * Ws pi τ w.2) := by ring
    _ ≤ C * (((∏ i, (2 * mc i) ^ (w.1.1 i) / ((w.1.1 i).factorial : ℝ)) *
          (∏ i, (2 * mt i) ^ (w.1.2 i) / ((w.1.2 i).factorial : ℝ))) * Ws pi τ w.2) := by
        have := E_nonneg mc hc w.1.1
        gcongr
        · exact hle1
        · exact hle2

variable {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]

noncomputable def Gf (N : Network nd ns I E) (τ : ℝ) (z : (Fin nd → ℕ) × (Fin ns → ℕ)) : ℝ :=
  (1 / τ) * Phi N τ (fun i => (z.1 i : ℝ)) (fun j => (z.2 j : ℝ))

lemma Psi_eq (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ η : ℝ)
    (hm : ∀ i, 0 ≤ (lam i + η * beta i) * τ) (hs : ∀ j, 0 ≤ pi j * τ) :
    PsiTau N lam beta pi τ η = ∑' z, Wd lam beta τ η z.1 * Ws pi τ z.2 * Gf N τ z := by
  unfold PsiTau
  rw [integral_eq_tsum]
  congr 1; funext z
  unfold marketLaw
  rw [show ({z} : Set ((Fin nd → ℕ) × (Fin ns → ℕ))) = {z.1} ×ˢ {z.2} by simp,
    measureReal_prod_prod, poisLaw_real_singleton (fun i => (lam i + η * beta i) * τ) hm,
    poisLaw_real_singleton (fun j => pi j * τ) hs]
  rfl

lemma mkt_tsum (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (τ η : ℝ)
    (hm : ∀ i, 0 ≤ (lam i + η * beta i) * τ) (hs : ∀ j, 0 ≤ pi j * τ)
    (F : (Fin nd → ℕ) × (Fin ns → ℕ) → ℝ) :
    ∫ z, F z ∂(marketLaw lam beta pi τ η) = ∑' z, Wd lam beta τ η z.1 * Ws pi τ z.2 * F z := by
  rw [integral_eq_tsum]
  congr 1; funext z
  unfold marketLaw
  rw [show ({z} : Set ((Fin nd → ℕ) × (Fin ns → ℕ))) = {z.1} ×ˢ {z.2} by simp,
    measureReal_prod_prod, poisLaw_real_singleton (fun i => (lam i + η * beta i) * τ) hm,
    poisLaw_real_singleton (fun j => pi j * τ) hs]
  rfl

lemma exp_tsum (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ)
    (hc : ∀ i, 0 ≤ (1 - ρ) * lam i * τ) (ht : ∀ i, 0 ≤ ρ * (lam i + beta i) * τ)
    (hs : ∀ j, 0 ≤ pi j * τ) (F : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ) :
    ∫ w, F w ∂(experimentLaw lam beta pi ρ τ) =
      ∑' w, Wp (fun i => (1 - ρ) * lam i * τ) w.1.1 * Wp (fun i => ρ * (lam i + beta i) * τ) w.1.2 *
        Ws pi τ w.2 * F w := by
  rw [integral_eq_tsum]
  congr 1; funext w
  unfold experimentLaw
  rw [show ({w} : Set (((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ))) =
      ({w.1.1} ×ˢ {w.1.2}) ×ˢ {w.2} by simp,
    measureReal_prod_prod, measureReal_prod_prod,
    poisLaw_real_singleton (fun i => (1 - ρ) * lam i * τ) hc,
    poisLaw_real_singleton (fun i => ρ * (lam i + beta i) * τ) ht,
    poisLaw_real_singleton (fun j => pi j * τ) hs]
  rfl

lemma Gf_bound (N : Network nd ns I E) {τ : ℝ} (hτ : 0 < τ) (z : (Fin nd → ℕ) × (Fin ns → ℕ)) :
    |Gf N τ z| ≤ (1 / τ) * ∑ e, |N.v e| * (τ * N.k e) := by
  unfold Gf
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / τ)]
  gcongr
  exact Phi_bound N hτ.le _ _

lemma deriv_main (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hlb : ∀ i, 0 ≤ lam i + beta i) (hp : ∀ j, 0 ≤ pi j)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (PsiTau N lam beta pi τ)
      (∑' z, Wd lam beta τ ρ z.1 * Lf lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z) ρ := by
  set c0 := min (ρ / 2) ((1 - ρ) / 2) with hc0def
  have hc0 : 0 < c0 := lt_min (by linarith) (by linarith)
  set t := Set.Ioo (ρ / 2) ((1 + ρ) / 2) with htdef
  have hρt : ρ ∈ t := ⟨by linarith, by linarith⟩
  have ht01 : ∀ η ∈ t, 0 < η ∧ η < 1 := fun η h => ⟨by linarith [h.1], by linarith [h.2]⟩
  have hct : ∀ η ∈ t, c0 ≤ η ∧ c0 ≤ 1 - η := fun η h =>
    ⟨(min_le_left _ _).trans (by linarith [h.1]), (min_le_right _ _).trans (by linarith [h.2])⟩
  set M : Fin nd → ℝ := fun i => (2 * lam i + beta i) * τ with hMdef
  set a : Fin nd → ℝ := fun i => c0 * (2 * lam i + beta i) * τ with hadef
  have hs : ∀ j, 0 ≤ pi j * τ := fun j => mul_nonneg (hp j) hτ.le
  have hμ0 : ∀ η, 0 ≤ η → η ≤ 1 → ∀ i, 0 ≤ (lam i + η * beta i) * τ := by
    intro η h0 h1 i
    have : lam i + η * beta i = (1 - η) * lam i + η * (lam i + beta i) := by ring
    rw [this]
    exact mul_nonneg (add_nonneg (mul_nonneg (by linarith) (hl i)) (mul_nonneg h0 (hlb i))) hτ.le
  have hμM : ∀ η, 0 ≤ η → η ≤ 1 → ∀ i, (lam i + η * beta i) * τ ≤ M i := by
    intro η h0 h1 i
    have e1 : lam i + η * beta i = (1 - η) * lam i + η * (lam i + beta i) := by ring
    have : lam i + η * beta i ≤ 2 * lam i + beta i := by
      rw [e1]; nlinarith [mul_nonneg h0 (hl i), mul_nonneg (by linarith : 0 ≤ 1 - η) (hlb i)]
    exact mul_le_mul_of_nonneg_right this hτ.le
  have hpos2 : ∀ i, beta i ≠ 0 → 0 < 2 * lam i + beta i := by
    intro i hb
    by_contra hc
    have h1 := hl i; have h2 := hlb i
    apply hb; linarith
  have ha : ∀ η ∈ t, ∀ i, beta i ≠ 0 → 0 < a i ∧ a i ≤ (lam i + η * beta i) * τ := by
    intro η hη i hb
    refine ⟨mul_pos (mul_pos hc0 (hpos2 i hb)) hτ, ?_⟩
    have e1 : lam i + η * beta i = (1 - η) * lam i + η * (lam i + beta i) := by ring
    have : c0 * (2 * lam i + beta i) ≤ lam i + η * beta i := by
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_right (hct η hη).1 (hlb i),
        mul_le_mul_of_nonneg_right (hct η hη).2 (hl i)]
    exact mul_le_mul_of_nonneg_right this hτ.le
  have hM0 : ∀ i, 0 ≤ M i := fun i => (hμ0 0 le_rfl zero_le_one i).trans (hμM 0 le_rfl zero_le_one i)
  set B := ∑ e, |N.v e| * (τ * N.k e) with hBdef
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (mul_nonneg hτ.le (N.k_nonneg e))
  set K := ∑ i, |beta i| * τ * (1 / a i + 1) with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by
    by_cases hb : beta i = 0
    · simp [hb]
    · have := (ha ρ hρt i hb).1; positivity
  -- the tsum derivative
  have hmain : HasDerivAt (fun η => ∑' z, Wd lam beta τ η z.1 * Ws pi τ z.2 * Gf N τ z)
      (∑' z, Wd lam beta τ ρ z.1 * Lf lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z) ρ := by
    refine hasDerivAt_tsum_of_isPreconnected
      (u := fun z => (1 / τ * B * K) * ((∏ i, (2 * M i) ^ (z.1 i) / ((z.1 i).factorial : ℝ)) *
        Ws pi τ z.2))
      (g := fun z η => Wd lam beta τ η z.1 * Ws pi τ z.2 * Gf N τ z)
      (g' := fun z η => Wd lam beta τ η z.1 * Lf lam beta τ η z.1 * Ws pi τ z.2 * Gf N τ z)
      (t := t) (y₀ := ρ) ?_ isOpen_Ioo isPreconnected_Ioo ?_ ?_ hρt ?_ hρt
    · exact ((summable_E M hM0).mul_of_nonneg (summable_Ws pi τ hs) (E_nonneg M hM0)
        (Ws_nonneg pi τ hs)).mul_left _
    · intro z η hη
      have h1 := hasDerivAt_Wd lam beta τ η z.1 fun i hb => (ha η hη i hb).1.trans_le (ha η hη i hb).2
      exact (h1.mul_const _).mul_const _
    · intro z η hη
      have h01 := ht01 η hη
      have hW := Wd_nonneg lam beta τ η (hμ0 η h01.1.le h01.2.le) z.1
      have hS := Ws_nonneg pi τ hs z.2
      have hL := Lf_bound lam beta τ η hτ a (ha η hη) z.1
      have hG := Gf_bound N hτ z
      have hle := prod_pw_le (fun i => (lam i + η * beta i) * τ) M (hμ0 η h01.1.le h01.2.le)
        (hμM η h01.1.le h01.2.le) z.1
      have hP := one_le_prod_two_pow z.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hS]
      calc Wd lam beta τ η z.1 * |Lf lam beta τ η z.1| * Ws pi τ z.2 * |Gf N τ z|
          ≤ Wd lam beta τ η z.1 * (K * ∏ i, (2 : ℝ) ^ (z.1 i)) * Ws pi τ z.2 * (1 / τ * B) := by
            gcongr
        _ = (1 / τ * B * K) * ((Wd lam beta τ η z.1 * ∏ i, (2 : ℝ) ^ (z.1 i)) * Ws pi τ z.2) := by
            ring
        _ ≤ _ := by
            have : 0 ≤ 1 / τ * B * K := by positivity
            gcongr
            exact hle
    · refine summable_mkt lam beta pi τ ρ M (hμ0 ρ hρ0.le hρ1.le) (hμM ρ hρ0.le hρ1.le) hs _
        (1 / τ * B) fun z => ?_
      have hP := one_le_prod_two_pow z.1
      have hG := Gf_bound N hτ z
      have : 0 ≤ 1 / τ * B := by positivity
      nlinarith
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hρt] with η hη
  have h01 := ht01 η hη
  exact Psi_eq N lam beta pi τ η (hμ0 η h01.1.le h01.2.le) hs

lemma claimA (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hlb : ∀ i, 0 ≤ lam i + beta i) (hp : ∀ j, 0 ≤ pi j)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    ∑' z, Wd lam beta τ ρ z.1 * Lf lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z =
      ∑ i, beta i * ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ), Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
        (Phi N τ ((fun j => (z.1 j : ℝ)) + Pi.single i 1) (fun j => (z.2 j : ℝ)) -
          Phi N τ (fun j => (z.1 j : ℝ)) (fun j => (z.2 j : ℝ))) := by
  have hs : ∀ j, 0 ≤ pi j * τ := fun j => mul_nonneg (hp j) hτ.le
  have hm : ∀ i, 0 ≤ (lam i + ρ * beta i) * τ := by
    intro i
    have : lam i + ρ * beta i = (1 - ρ) * lam i + ρ * (lam i + beta i) := by ring
    rw [this]
    exact mul_nonneg (add_nonneg (mul_nonneg (by linarith) (hl i)) (mul_nonneg hρ0.le (hlb i))) hτ.le
  set B := ∑ e, |N.v e| * (τ * N.k e) with hBdef
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (mul_nonneg hτ.le (N.k_nonneg e))
  have hGB : 0 ≤ 1 / τ * B := by positivity
  have SM := fun (Y : (Fin nd → ℕ) × (Fin ns → ℕ) → ℝ) (C : ℝ)
    (hY : ∀ z, |Y z| ≤ C * ∏ i, (2 : ℝ) ^ (z.1 i)) =>
    summable_mkt lam beta pi τ ρ (fun i => (lam i + ρ * beta i) * τ) hm (fun _ => le_rfl) hs Y C hY
  have hsplit : ∀ z : (Fin nd → ℕ) × (Fin ns → ℕ),
      Wd lam beta τ ρ z.1 * Lf lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z =
      ∑ i, beta i * τ * (Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
        (Gf N τ z * ((z.1 i : ℝ) / ((lam i + ρ * beta i) * τ) - 1))) := by
    intro z; unfold Lf
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [tsum_congr hsplit]
  rw [Summable.tsum_finsetSum (fun i _ => ?_)]
  swap
  · refine (SM _ (1 / τ * B * (1 / ((lam i + ρ * beta i) * τ) + 1)) fun z => ?_).mul_left _
    have hG := Gf_bound N hτ z
    have hP := succ_le_prod_two_pow z.1 i
    have hd := abs_div_sub_one_le (z.1 i : ℝ) _ (Nat.cast_nonneg _) (hm i)
    have h1 : 0 ≤ 1 / ((lam i + ρ * beta i) * τ) + 1 := by have := hm i; positivity
    rw [abs_mul]
    calc |Gf N τ z| * |(z.1 i : ℝ) / ((lam i + ρ * beta i) * τ) - 1|
        ≤ (1 / τ * B) * ((1 / ((lam i + ρ * beta i) * τ) + 1) * ((z.1 i : ℝ) + 1)) := by
          gcongr
      _ ≤ (1 / τ * B) * ((1 / ((lam i + ρ * beta i) * τ) + 1) * ∏ j, (2 : ℝ) ^ (z.1 j)) := by
          gcongr
      _ = _ := by ring
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left]
  by_cases hb : beta i = 0
  · simp [hb]
  have hμ : 0 < (lam i + ρ * beta i) * τ := by
    have hpos2 : 0 < 2 * lam i + beta i := by
      by_contra hc
      have h1 := hl i; have h2 := hlb i
      apply hb; linarith
    have : lam i + ρ * beta i = (1 - ρ) * lam i + ρ * (lam i + beta i) := by ring
    rw [this]
    have h1 := hl i; have h2 := hlb i
    have : 0 < (1 - ρ) * lam i + ρ * (lam i + beta i) := by
      rcases h1.lt_or_eq with h | h
      · have := mul_pos (by linarith : (0:ℝ) < 1 - ρ) h
        have := mul_nonneg hρ0.le h2
        linarith
      · have h3 : 0 < lam i + beta i := by linarith
        have := mul_pos hρ0 h3
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ρ) h1
        linarith
    exact mul_pos this hτ
  set μ := (lam i + ρ * beta i) * τ with hμdef
  let σ : (Fin nd → ℕ) × (Fin ns → ℕ) → (Fin nd → ℕ) × (Fin ns → ℕ) :=
    fun z => (z.1 + Pi.single i 1, z.2)
  have hσ : Function.Injective σ := fun z1 z2 h => by
    simp only [σ, Prod.mk.injEq] at h
    exact Prod.ext (sh_injective i h.1) h.2
  have hstein := stein σ hσ (fun z => Wd lam beta τ ρ z.1 * Ws pi τ z.2) (fun z => (z.1 i : ℝ))
    (Gf N τ) μ (fun z hz => by
      obtain ⟨d', hd'⟩ := mem_range_sh i z.1 (by exact_mod_cast hz)
      exact ⟨(d', z.2), Prod.ext hd' rfl⟩)
    (fun z => by
      have h := prod_pw_sh (fun j => (lam j + ρ * beta j) * τ) z.1 i
      beta_reduce at h
      simp only [Wd, σ]
      rw [show (((z.1 + Pi.single i 1 : Fin nd → ℕ) i : ℕ) : ℝ) = (z.1 i : ℝ) + 1 by simp]
      linear_combination Ws pi τ z.2 * h)
  beta_reduce at hstein
  have hA : Summable (fun z => Wd lam beta τ ρ z.1 * Ws pi τ z.2 * (z.1 i : ℝ) * Gf N τ z) := by
    refine (SM (fun z => (z.1 i : ℝ) * Gf N τ z) (1 / τ * B) fun z => ?_).congr fun z => by ring
    have hG := Gf_bound N hτ z
    have hP := succ_le_prod_two_pow z.1 i
    rw [abs_mul, Nat.abs_cast]
    calc (z.1 i : ℝ) * |Gf N τ z| ≤ ((z.1 i : ℝ) + 1) * (1 / τ * B) := by
          gcongr
          · linarith
      _ ≤ (∏ j, (2 : ℝ) ^ (z.1 j)) * (1 / τ * B) := by gcongr
      _ = _ := by ring
  have hB' : Summable (fun z => Wd lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z) := by
    refine SM _ (1 / τ * B) fun z => ?_
    have hG := Gf_bound N hτ z
    have hP := one_le_prod_two_pow z.1
    nlinarith
  have hC : Summable (fun z => Wd lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ (σ z)) := by
    refine SM _ (1 / τ * B) fun z => ?_
    have hG := Gf_bound N hτ (σ z)
    have hP := one_le_prod_two_pow z.1
    nlinarith
  have e1 : ∑' z, Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
      (Gf N τ z * ((z.1 i : ℝ) / μ - 1)) =
      (1 / μ) * ∑' z, Wd lam beta τ ρ z.1 * Ws pi τ z.2 * (z.1 i : ℝ) * Gf N τ z -
        ∑' z, Wd lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z := by
    rw [← tsum_mul_left, ← Summable.tsum_sub (hA.mul_left _) hB']
    exact tsum_congr fun z => by ring
  have e2 : ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ), Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
      (Phi N τ ((fun j => (z.1 j : ℝ)) + Pi.single i 1) (fun j => (z.2 j : ℝ)) -
          Phi N τ (fun j => (z.1 j : ℝ)) (fun j => (z.2 j : ℝ))) =
      τ * ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ), Wd lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ (σ z) -
        τ * ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ), Wd lam beta τ ρ z.1 * Ws pi τ z.2 * Gf N τ z := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_sub (hC.mul_left _) (hB'.mul_left _)]
    refine tsum_congr fun z => ?_
    simp only [Gf, σ]
    rw [cast_sh]
    field_simp
  rw [e1, e2, hstein]
  field_simp

lemma superpos_tsum (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ) (ρ τ : ℝ)
    (hc : ∀ i, 0 ≤ (1 - ρ) * lam i * τ) (ht : ∀ i, 0 ≤ ρ * (lam i + beta i) * τ)
    (hs : ∀ j, 0 ≤ pi j * τ) (hm : ∀ i, 0 ≤ (lam i + ρ * beta i) * τ)
    (F : (Fin nd → ℕ) × (Fin ns → ℕ) → ℝ) :
    ∑' w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ),
      Wp (fun i => (1 - ρ) * lam i * τ) w.1.1 * Wp (fun i => ρ * (lam i + beta i) * τ) w.1.2 *
        Ws pi τ w.2 * F (w.1.1 + w.1.2, w.2) =
      ∑' z, Wd lam beta τ ρ z.1 * Ws pi τ z.2 * F z := by
  rw [← exp_tsum lam beta pi ρ τ hc ht hs (fun w => F (w.1.1 + w.1.2, w.2)),
    ← mkt_tsum lam beta pi τ ρ hm hs F, ← superpos lam beta pi ρ τ hc ht,
    integral_map Measurable.of_discrete.aemeasurable AEStronglyMeasurable.of_discrete]

lemma cast_sh_t {n : ℕ} (dc dt : Fin n → ℕ) (i : Fin n) :
    (fun j => ((dc j + (dt + Pi.single i 1 : Fin n → ℕ) j : ℕ) : ℝ)) =
      (fun j => ((dc j + dt j : ℕ) : ℝ)) + Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; ring
  · simp [hj]

lemma cast_sh_c {n : ℕ} (dc dt : Fin n → ℕ) (i : Fin n) :
    (fun j => (((dc + Pi.single i 1 : Fin n → ℕ) j + dt j : ℕ) : ℝ)) =
      (fun j => ((dc j + dt j : ℕ) : ℝ)) + Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp; ring
  · simp [hj]

lemma Aminus_sh (N : Network nd ns I E) (τ : ℝ) (x : Fin nd → ℝ) (s : Fin ns → ℝ) (i : Fin nd) :
    Aminus N τ (x + Pi.single i 1) s i = Phi N τ (x + Pi.single i 1) s - Phi N τ x s := by
  unfold Aminus
  rw [add_sub_cancel_right]

lemma claimB (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hl : ∀ i, 0 ≤ lam i) (hlb : ∀ i, 0 ≤ lam i + beta i) (hp : ∀ j, 0 ≤ pi j)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    ∫ z, SPest N ρ τ z.1.1 z.1.2 z.2 ∂(experimentLaw lam beta pi ρ τ) =
      ∑ i, beta i * ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ), Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
        (Phi N τ ((fun j => (z.1 j : ℝ)) + Pi.single i 1) (fun j => (z.2 j : ℝ)) -
          Phi N τ (fun j => (z.1 j : ℝ)) (fun j => (z.2 j : ℝ))) := by
  have hs : ∀ j, 0 ≤ pi j * τ := fun j => mul_nonneg (hp j) hτ.le
  have hc : ∀ i, 0 ≤ (1 - ρ) * lam i * τ := fun i =>
    mul_nonneg (mul_nonneg (by linarith) (hl i)) hτ.le
  have ht : ∀ i, 0 ≤ ρ * (lam i + beta i) * τ := fun i =>
    mul_nonneg (mul_nonneg hρ0.le (hlb i)) hτ.le
  have hm : ∀ i, 0 ≤ (lam i + ρ * beta i) * τ := by
    intro i
    have : lam i + ρ * beta i = (1 - ρ) * lam i + ρ * (lam i + beta i) := by ring
    rw [this]
    exact mul_nonneg (add_nonneg (mul_nonneg (by linarith) (hl i)) (mul_nonneg hρ0.le (hlb i))) hτ.le
  set B := ∑ e, |N.v e| * (τ * N.k e) with hBdef
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (mul_nonneg hτ.le (N.k_nonneg e))
  set mc : Fin nd → ℝ := fun i => (1 - ρ) * lam i * τ with hmc
  set mt : Fin nd → ℝ := fun i => ρ * (lam i + beta i) * τ with hmt
  rw [exp_tsum lam beta pi ρ τ hc ht hs]
  have hAb : ∀ (i : Fin nd) (w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ)),
      |Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i| ≤ 2 * B := by
    intro i w
    unfold Aminus
    have h1 := Phi_bound N hτ.le (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ))
    have h2 := Phi_bound N hτ.le ((fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) - Pi.single i 1)
      (fun j => (w.2 j : ℝ))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have SE := fun (Y : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ) (C : ℝ)
    (hY : ∀ w, |Y w| ≤ C * ((∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i))) =>
    summable_exp mc mt pi τ hc ht hs Y C hY
  have hSt : ∀ i, Summable (fun w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) =>
      Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * (w.1.2 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i) := by
    intro i
    refine (SE (fun w => (w.1.2 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i) (2 * B)
        fun w => ?_).congr fun w => by ring
    have h1 := hAb i w
    have hP1 := one_le_prod_two_pow w.1.1
    have hP2 := succ_le_prod_two_pow w.1.2 i
    rw [abs_mul, Nat.abs_cast]
    have h0 : (0 : ℝ) ≤ (w.1.2 i : ℝ) := Nat.cast_nonneg _
    have hPP : (w.1.2 i : ℝ) ≤ (∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i) := by
      nlinarith
    calc (w.1.2 i : ℝ) * |Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i|
        ≤ ((∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i)) * (2 * B) := by gcongr
      _ = _ := by ring
  have hSc : ∀ i, Summable (fun w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) =>
      Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * (w.1.1 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i) := by
    intro i
    refine (SE (fun w => (w.1.1 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i) (2 * B)
        fun w => ?_).congr fun w => by ring
    have h1 := hAb i w
    have hP1 := succ_le_prod_two_pow w.1.1 i
    have hP2 := one_le_prod_two_pow w.1.2
    rw [abs_mul, Nat.abs_cast]
    have h0 : (0 : ℝ) ≤ (w.1.1 i : ℝ) := Nat.cast_nonneg _
    have hPP : (w.1.1 i : ℝ) ≤ (∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i) := by
      nlinarith
    calc (w.1.1 i : ℝ) * |Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i|
        ≤ ((∏ i, (2 : ℝ) ^ (w.1.1 i)) * ∏ i, (2 : ℝ) ^ (w.1.2 i)) * (2 * B) := by gcongr
      _ = _ := by ring
  have hsplit : ∀ w : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ),
      Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * SPest N ρ τ w.1.1 w.1.2 w.2 =
      ∑ i, (1 / τ) * ((1 / ρ) * (Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * (w.1.2 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i) -
        (1 / (1 - ρ)) * (Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2 * (w.1.1 i : ℝ) *
        Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i)) := by
    intro w
    unfold SPest
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [tsum_congr hsplit, Summable.tsum_finsetSum (fun i _ =>
    (((hSt i).mul_left _).sub ((hSc i).mul_left _)).mul_left _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, Summable.tsum_sub ((hSt i).mul_left _) ((hSc i).mul_left _), tsum_mul_left,
    tsum_mul_left]
  let We : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ :=
    fun w => Wp mc w.1.1 * Wp mt w.1.2 * Ws pi τ w.2
  let H : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ :=
    fun w => Aminus N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ)) i
  let V : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) → ℝ :=
    fun w => Phi N τ ((fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) + Pi.single i 1)
      (fun j => (w.2 j : ℝ)) - Phi N τ (fun j => ((w.1.1 j + w.1.2 j : ℕ) : ℝ)) (fun j => (w.2 j : ℝ))
  let σt : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) →
      ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) :=
    fun w => ((w.1.1, w.1.2 + Pi.single i 1), w.2)
  let σc : ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) →
      ((Fin nd → ℕ) × (Fin nd → ℕ)) × (Fin ns → ℕ) :=
    fun w => ((w.1.1 + Pi.single i 1, w.1.2), w.2)
  have hσt : Function.Injective σt := fun w1 w2 h => by
    simp only [σt, Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.1.1 (sh_injective i h.1.2)) h.2
  have hσc : Function.Injective σc := fun w1 w2 h => by
    simp only [σc, Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext (sh_injective i h.1.1) h.1.2) h.2
  have st := stein σt hσt We (fun w => (w.1.2 i : ℝ)) H (mt i)
    (fun w hw => by
      obtain ⟨d', hd'⟩ := mem_range_sh i w.1.2 (by exact_mod_cast hw)
      exact ⟨((w.1.1, d'), w.2), Prod.ext (Prod.ext rfl hd') rfl⟩)
    (fun w => by
      have h := prod_pw_sh mt w.1.2 i
      simp only [We, σt, Wp]
      rw [show (((w.1.2 + Pi.single i 1 : Fin nd → ℕ) i : ℕ) : ℝ) = (w.1.2 i : ℝ) + 1 by simp]
      linear_combination (∏ j, pw (mc j) (w.1.1 j)) * Ws pi τ w.2 * h)
  have sc := stein σc hσc We (fun w => (w.1.1 i : ℝ)) H (mc i)
    (fun w hw => by
      obtain ⟨d', hd'⟩ := mem_range_sh i w.1.1 (by exact_mod_cast hw)
      exact ⟨((d', w.1.2), w.2), Prod.ext (Prod.ext hd' rfl) rfl⟩)
    (fun w => by
      have h := prod_pw_sh mc w.1.1 i
      simp only [We, σc, Wp]
      rw [show (((w.1.1 + Pi.single i 1 : Fin nd → ℕ) i : ℕ) : ℝ) = (w.1.1 i : ℝ) + 1 by simp]
      linear_combination (∏ j, pw (mt j) (w.1.2 j)) * Ws pi τ w.2 * h)
  have hHt : ∀ w, H (σt w) = V w := fun w => by
    simp only [H, σt, V]
    rw [cast_sh_t, Aminus_sh]
  have hHc : ∀ w, H (σc w) = V w := fun w => by
    simp only [H, σc, V]
    rw [cast_sh_c, Aminus_sh]
  simp only [hHt, hHc] at st sc
  change (1 / τ) * ((1 / ρ) * ∑' w, We w * (w.1.2 i : ℝ) * H w -
    (1 / (1 - ρ)) * ∑' w, We w * (w.1.1 i : ℝ) * H w) = _
  rw [st, sc]
  have hsup := superpos_tsum lam beta pi ρ τ hc ht hs hm
    (fun z => Phi N τ ((fun j => (z.1 j : ℝ)) + Pi.single i 1) (fun j => (z.2 j : ℝ)) -
      Phi N τ (fun j => (z.1 j : ℝ)) (fun j => (z.2 j : ℝ)))
  have hV : ∑' w, We w * V w = ∑' z : (Fin nd → ℕ) × (Fin ns → ℕ),
      Wd lam beta τ ρ z.1 * Ws pi τ z.2 *
      (Phi N τ ((fun j => (z.1 j : ℝ)) + Pi.single i 1) (fun j => (z.2 j : ℝ)) -
        Phi N τ (fun j => (z.1 j : ℝ)) (fun j => (z.2 j : ℝ))) := by
    rw [← hsup]
    rfl
  rw [hV]
  simp only [hmc, hmt]
  have h1 : (1 - ρ) ≠ 0 := by linarith
  have h2 : ρ ≠ 0 := hρ0.ne'
  have h3 : τ ≠ 0 := hτ.ne'
  field_simp
  ring

theorem theorem_6' {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (PsiTau N lam beta pi τ)
      (∫ z, SPest N ρ τ z.1.1 z.1.2 z.2 ∂(experimentLaw lam beta pi ρ τ)) ρ := by
  have hl : ∀ i, 0 ≤ lam i := fun i => hlam i
  have hlb : ∀ i, 0 ≤ lam i + beta i := fun i => by simpa using hlamb i
  have hp : ∀ j, 0 ≤ pi j := fun j => hpi j
  rw [claimB N lam beta pi hl hlb hp ρ hρ0 hρ1 τ hτ,
    ← claimA N lam beta pi hl hlb hp ρ hρ0 hρ1 τ hτ]
  exact deriv_main N lam beta pi hl hlb hp ρ hρ0 hρ1 τ hτ

end MarketInterference.FiniteSample.Mk6

namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

theorem theorem_6 {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (PsiTau N lam beta pi τ)
      (∫ z, SPest N ρ τ z.1.1 z.1.2 z.2 ∂(experimentLaw lam beta pi ρ τ)) ρ :=
  Mk6.theorem_6' N lam beta pi hlam hlamb hpi ρ hρ0 hρ1 τ hτ

end MarketInterference.FiniteSample


-- Platform entry point: restates the target verbatim.
namespace MarketInterference.FiniteSample

open MeasureTheory ProbabilityTheory

theorem _root_.solution {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : 0 ≤ lam) (hlamb : 0 ≤ lam + beta) (hpi : 0 ≤ pi)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (PsiTau N lam beta pi τ)
      (∫ z, SPest N ρ τ z.1.1 z.1.2 z.2 ∂(experimentLaw lam beta pi ρ τ)) ρ := by
  apply @MarketInterference.FiniteSample.theorem_6 <;> assumption

end MarketInterference.FiniteSample
