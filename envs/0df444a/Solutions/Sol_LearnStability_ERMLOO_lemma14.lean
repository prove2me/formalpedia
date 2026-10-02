-- Prove2me | solution 1 for LearnStability.ERMLOO.lemma14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:08:03.157154+00:00
-- url     : https://prove2.me/submissions/40ee6d4b-e37e-4e6e-9bb1-49b4ce22b96c

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

/-! e4d182d4 LearnStability.ERMLOO.lemma14 (Shalev-Shwartz, Shamir, Srebro, Sridharan 2010, Lemma 14).
Pointwise, with `X = F(A S) - F_S(A S)`, `a = F_S(A S) - min F_S ≥ 0` and `h` with
`F(h) < F* + η/2`: `|X| ≤ X + 2 (a + |F_S(h) - F(h)| + η/2)`. Integrate and use
`E|F_S(h) - F(h)| ≤ B/√m` (second moment `≤ B²/m` by independence of the coordinates). -/

set_option autoImplicit false

namespace LearnStability.ERMLOO.L14Proof

open MeasureTheory LearnStability.ERMLOO

variable {H Z : Type*} [MeasurableSpace Z]

lemma abs_empRisk_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : |empRisk f S h| ≤ B := by
  unfold empRisk
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hP.bounded h (S i)
    _ = B * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

lemma bddBelow_empRisk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ}
    (hm : 1 ≤ m) (S : Fin m → Z) : BddBelow (Set.range fun h => empRisk f S h) :=
  ⟨-B, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_empRisk_le hP hm S h)).1⟩

lemma ermValue_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : ermValue f S ≤ empRisk f S h :=
  ciInf_le (bddBelow_empRisk hP hm S) h

lemma neg_le_ermValue [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) : -B ≤ ermValue f S :=
  le_ciInf fun h => (abs_le.mp (abs_empRisk_le hP hm S h)).1

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma abs_risk_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : |risk f D h| ≤ B := by
  unfold risk
  have := norm_integral_le_of_norm_le_const (μ := D) (f := f h) (C := B)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hP.bounded h z)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma measurable_empRisk_rule {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    (m : ℕ) : Measurable (fun S : Fin m → Z => empRisk f S (A m S)) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hA m).comp (measurable_id.prodMk (measurable_pi_apply i))

lemma measurable_risk_rule {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    (D : Measure Z) [SFinite D] (m : ℕ) : Measurable (fun S : Fin m → Z => risk f D (A m S)) :=
  ((hA m).stronglyMeasurable.integral_prod_right' (ν := D)).measurable

lemma measurable_empRisk_const {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (m : ℕ)
    (h : H) : Measurable (fun S : Fin m → Z => empRisk f S h) := by
  unfold empRisk
  exact Measurable.div_const
    (Finset.measurable_sum _ fun i _ => (hP.measurable h).comp (measurable_pi_apply i)) _

lemma B_nonneg [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (D : Measure Z) [IsProbabilityMeasure D] : 0 ≤ B := by
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have h1 := measure_univ (μ := D)
    rw [Measure.eq_zero_of_isEmpty D] at h1
    simp at h1
  exact (abs_nonneg _).trans (hP.bounded (Classical.arbitrary H) (Classical.arbitrary Z))

lemma opt_le_risk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : optRisk f D ≤ risk f D h :=
  ciInf_le ⟨-B, by rintro _ ⟨g, rfl⟩; exact (abs_le.mp (abs_risk_le hP D g)).1⟩ h

lemma sq_integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have hi1 : Integrable (fun x => |g x|) μ :=
    integrable_of_abs_le hg.abs C fun x => by rw [abs_abs]; exact hC x
  have hi2 : Integrable (fun x => (g x) ^ 2) μ :=
    integrable_of_abs_le (hg.pow_const 2) (C ^ 2) fun x => by
      have h1 := hC x
      have h0 := abs_nonneg (g x)
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith
  set a := ∫ x, |g x| ∂μ with ha
  have h0 : 0 ≤ ∫ x, (|g x| - a) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : (fun x => (|g x| - a) ^ 2) = fun x => (g x) ^ 2 - (2 * a) * |g x| + a ^ 2 := by
    funext x
    rw [sub_sq, sq_abs]
    ring
  have hi3 : Integrable (fun x => (g x) ^ 2 - (2 * a) * |g x|) μ := hi2.sub (hi1.const_mul _)
  rw [e, integral_add hi3 (integrable_const _),
    integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const] at h0
  have hu : μ.real Set.univ = 1 := by simp
  rw [hu, one_smul, ← ha] at h0
  nlinarith

/-- The variance of a single loss is at most `B²`. -/
lemma var_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) :
    ∫ z, (f h z - risk f D h) * (f h z - risk f D h) ∂D ≤ B ^ 2 := by
  set r := risk f D h with hr
  have hfi : Integrable (f h) D := integrable_of_abs_le (hP.measurable h) B (hP.bounded h)
  have hff : Integrable (fun z => f h z * f h z) D :=
    integrable_of_abs_le ((hP.measurable h).mul (hP.measurable h)) (B * B) fun z => by
      rw [abs_mul]
      exact mul_le_mul (hP.bounded h z) (hP.bounded h z) (abs_nonneg _)
        ((abs_nonneg _).trans (hP.bounded h z))
  have e : (fun z => (f h z - r) * (f h z - r)) =
      fun z => (f h z * f h z - (2 * r) * f h z) + r ^ 2 := by
    funext z; ring
  have hint : ∫ z, f h z ∂D = r := rfl
  have i1 : Integrable (fun z => f h z * f h z - (2 * r) * f h z) D := hff.sub (hfi.const_mul _)
  have i2 : Integrable (fun z => (2 * r) * f h z) D := hfi.const_mul _
  rw [e, integral_add i1 (integrable_const _),
    integral_sub hff i2, integral_const_mul, hint, integral_const]
  have hu : D.real Set.univ = 1 := by simp
  rw [hu, one_smul]
  have hb : ∫ z, f h z * f h z ∂D ≤ B ^ 2 := by
    have := integral_mono hff (integrable_const (B ^ 2)) (μ := D) (fun z => by
      have h1 := abs_le.mp (hP.bounded h z)
      show f h z * f h z ≤ B ^ 2
      nlinarith)
    simpa using this
  nlinarith [sq_nonneg r]

lemma second_moment {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, (empRisk f S h - risk f D h) ^ 2 ∂(Measure.pi fun _ : Fin m => D) ≤ B ^ 2 / m := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hYm : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f h (S i) - risk f D h) := fun i =>
    ((hP.measurable h).comp (measurable_pi_apply i)).sub_const _
  have hYb : ∀ (i : Fin m) (S : Fin m → Z), |f h (S i) - risk f D h| ≤ 2 * B := by
    intro i S
    calc |f h (S i) - risk f D h| ≤ |f h (S i)| + |risk f D h| := abs_sub _ _
      _ ≤ B + B := add_le_add (hP.bounded _ _) (abs_risk_le hP D h)
      _ = 2 * B := by ring
  have hB0 : ∀ (i : Fin m) (S : Fin m → Z), 0 ≤ 2 * B := fun i S =>
    (abs_nonneg _).trans (hYb i S)
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m => D)
    (X := fun _ : Fin m => fun z : Z => f h z - risk f D h)
    (fun _ => ((hP.measurable h).sub_const _).aemeasurable)
  have h0 : ∀ i : Fin m, ∫ S : Fin m → Z, (f h (S i) - risk f D h)
      ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i
    have hi : Integrable (fun S : Fin m → Z => f h (S i)) (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le ((hP.measurable h).comp (measurable_pi_apply i)) B
        fun S => hP.bounded _ _
    rw [integral_sub hi (integrable_const _),
      integral_comp_eval (hP.measurable h).aestronglyMeasurable]
    simp [risk]
  have hoff : ∀ i j : Fin m, i ≠ j → ∫ S : Fin m → Z,
      (f h (S i) - risk f D h) * (f h (S j) - risk f D h)
        ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i j hij
    have hI := hind.indepFun hij
    have := hI.integral_mul_eq_mul_integral (hYm i).aestronglyMeasurable
      (hYm j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0 i, zero_mul]
  have hdiag : ∀ i : Fin m, ∫ S : Fin m → Z,
      (f h (S i) - risk f D h) * (f h (S i) - risk f D h)
        ∂(Measure.pi fun _ : Fin m => D) ≤ B ^ 2 := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin m => D) (i := i)
      (f := fun z => (f h z - risk f D h) * (f h z - risk f D h))
      (((hP.measurable h).sub_const _).mul ((hP.measurable h).sub_const _)).aestronglyMeasurable]
    exact var_le hP D h
  have hI2 : ∀ i j : Fin m, Integrable (fun S : Fin m → Z =>
      (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) (Measure.pi fun _ : Fin m => D) :=
    fun i j => integrable_of_abs_le ((hYm i).mul (hYm j)) ((2 * B) * (2 * B)) fun S => by
      rw [abs_mul]
      exact mul_le_mul (hYb i S) (hYb j S) (abs_nonneg _) (hB0 i S)
  have hexp : ∀ S : Fin m → Z, (empRisk f S h - risk f D h) ^ 2 =
      (∑ i, ∑ j, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) / (m:ℝ) ^ 2 := by
    intro S
    have e1 : empRisk f S h - risk f D h = (∑ i, (f h (S i) - risk f D h)) / m := by
      unfold empRisk
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [e1, div_pow, sq (∑ i, _), Finset.sum_mul_sum]
  calc ∫ S, (empRisk f S h - risk f D h) ^ 2 ∂(Measure.pi fun _ : Fin m => D)
      = ∫ S, (∑ i, ∑ j, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)) / (m:ℝ) ^ 2
          ∂(Measure.pi fun _ : Fin m => D) := by
        congr 1
        funext S
        exact hexp S
    _ = (∑ i, ∑ j, ∫ S : Fin m → Z, (f h (S i) - risk f D h) * (f h (S j) - risk f D h)
          ∂(Measure.pi fun _ : Fin m => D)) / (m:ℝ) ^ 2 := by
        rw [integral_div, integral_finsetSum _ (fun i _ => integrable_finsetSum _
          fun j _ => hI2 i j)]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI2 i j
    _ ≤ (∑ i : Fin m, ∑ j : Fin m, if i = j then B ^ 2 else 0) / (m:ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          exact hdiag i
        · rw [if_neg hij, hoff i j hij]
    _ = B ^ 2 / m := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma abs_moment {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D) ≤
      B / Real.sqrt m := by
  have : Nonempty H := ⟨h⟩
  have hB := B_nonneg hP D
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have h1 := sq_integral_abs_le (μ := Measure.pi fun _ : Fin m => D)
    (g := fun S : Fin m → Z => empRisk f S h - risk f D h)
    ((measurable_empRisk_const hP m h).sub_const _) (2 * B) (fun S => by
      have a1 := abs_empRisk_le hP hm S h
      have a2 := abs_risk_le hP D h
      calc |empRisk f S h - risk f D h| ≤ |empRisk f S h| + |risk f D h| := abs_sub _ _
        _ ≤ B + B := add_le_add a1 a2
        _ = 2 * B := by ring)
  have h2 := second_moment hP D hm h
  have h3 : (B / Real.sqrt m) ^ 2 = B ^ 2 / m := by
    rw [div_pow, Real.sq_sqrt hm'.le]
  have h4 : 0 ≤ B / Real.sqrt m := by positivity
  have h5 : (∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D)) ^ 2
      ≤ (B / Real.sqrt m) ^ 2 := by
    rw [h3]
    exact h1.trans h2
  exact (sq_le_sq₀ (integral_nonneg fun S => abs_nonneg _) h4).mp h5

lemma main [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (herm : MeasurableERMValue f)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    (εerm εoag : ℕ → ℝ)
    (hAERM : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) {m : ℕ} (hm : 1 ≤ m) :
    ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(sampleLaw D m)
      ≤ εoag m + 2 * εerm m + 2 * B / Real.sqrt m := by
  have hE := hAERM m hm
  have hO := hoag m hm
  unfold sampleLaw at hE hO ⊢
  set μ := Measure.pi fun _ : Fin m => D with hμ
  have hR : Integrable (fun S : Fin m → Z => risk f D (A m S)) μ :=
    integrable_of_abs_le (measurable_risk_rule hA D m) B fun _ => abs_risk_le hP D _
  have hEm : Integrable (fun S : Fin m → Z => empRisk f S (A m S)) μ :=
    integrable_of_abs_le (measurable_empRisk_rule hA m) B fun S => abs_empRisk_le hP hm S _
  have hV : Integrable (fun S : Fin m → Z => ermValue f S) μ :=
    integrable_of_abs_le (herm m) B fun S => by
      rw [abs_le]
      exact ⟨neg_le_ermValue hP hm S, (ermValue_le hP hm S (Classical.arbitrary H)).trans
        (abs_le.mp (abs_empRisk_le hP hm S _)).2⟩
  have hX : Integrable (fun S : Fin m → Z => risk f D (A m S) - empRisk f S (A m S)) μ :=
    hR.sub hEm
  have hG : Integrable (fun S : Fin m → Z => empRisk f S (A m S) - ermValue f S) μ :=
    hEm.sub hV
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨h, hh⟩ : ∃ h, risk f D h < optRisk f D + η / 2 :=
    exists_lt_of_ciInf_lt (f := fun h => risk f D h) (a := optRisk f D + η / 2)
      (show optRisk f D < optRisk f D + η / 2 by linarith)
  have hpt : ∀ S : Fin m → Z, |risk f D (A m S) - empRisk f S (A m S)| ≤
      (risk f D (A m S) - empRisk f S (A m S)) +
        2 * ((empRisk f S (A m S) - ermValue f S) + (|empRisk f S h - risk f D h| + η / 2)) := by
    intro S
    have l0 := ermValue_le hP hm S (A m S)
    have l1 := ermValue_le hP hm S h
    have l2 := opt_le_risk hP D (A m S)
    have l3 := le_abs_self (empRisk f S h - risk f D h)
    have l4 := abs_nonneg (empRisk f S h - risk f D h)
    rcases abs_cases (risk f D (A m S) - empRisk f S (A m S)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      linarith
  have hWa : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h|) μ :=
    ((integrable_of_abs_le (measurable_empRisk_const hP m h) B
      fun S => abs_empRisk_le hP hm S h).sub (integrable_const _)).abs
  have hW : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h| + η / 2) μ :=
    hWa.add (integrable_const _)
  have hGW : Integrable (fun S : Fin m → Z => (empRisk f S (A m S) - ermValue f S) +
      (|empRisk f S h - risk f D h| + η / 2)) μ := hG.add hW
  have hGW2 : Integrable (fun S : Fin m → Z => 2 * ((empRisk f S (A m S) - ermValue f S) +
      (|empRisk f S h - risk f D h| + η / 2))) μ := hGW.const_mul 2
  have hint : ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂μ ≤
      ∫ S, ((risk f D (A m S) - empRisk f S (A m S)) +
        2 * ((empRisk f S (A m S) - ermValue f S) + (|empRisk f S h - risk f D h| + η / 2))) ∂μ :=
    integral_mono hX.abs (hX.add hGW2) hpt
  rw [integral_add hX hGW2, integral_const_mul, integral_add hG hW,
    integral_add hWa (integrable_const _), integral_const] at hint
  have hu : μ.real Set.univ = 1 := by simp [hμ]
  rw [hu, one_smul] at hint
  have hm2 := abs_moment hP D hm h
  have hO' := (le_abs_self _).trans hO
  have e : 2 * B / Real.sqrt m = 2 * (B / Real.sqrt m) := by ring
  rw [e]
  linarith

end LearnStability.ERMLOO.L14Proof

open LearnStability.ERMLOO MeasureTheory in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εerm εoag : ℕ → ℝ)
    (hAERM : IsAERM f A D εerm) (hoag : OnAverageGeneralizes f A D εoag) :
    Generalizes f A D (fun m => εoag m + 2 * εerm m + 2 * B / Real.sqrt m) := by
  intro m hm
  exact L14Proof.main hf herm hA D εerm εoag hAERM hoag hm
