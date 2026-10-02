-- Prove2me | solution 1 for LearnStability.Characterization.lemma16_main_converse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:36:03.128046+00:00
-- url     : https://prove2.me/submissions/a1d1ef17-63d0-4c36-aa1d-337f95bce43e

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties

/-! 36f6a5d4 LearnStability.Characterization.lemma16_main_converse (SSSS 2010, Lemma 16).
Consistency of `A` under the empirical distribution of `S` gives
`F* - F_S(ĥ_S) ≤ ε + avg_τ (risk - empRisk)(A(S∘τ))`; for each `τ`, the coordinates outside
`range τ` are a mean-zero sum whose second moment is `≤ m B²` (resampling one coordinate);
`E[F_S(ĥ_S)] ≤ F*` handles the other sign. -/

set_option autoImplicit false

namespace LearnStability.Characterization.L16Proof

open MeasureTheory Filter Topology LearnStability.Characterization

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
    {m k : ℕ} {φ : (Fin m → Z) → (Fin k → Z)} (hφ : Measurable φ) :
    Measurable (fun S : Fin m → Z => empRisk f S (A k (φ S))) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hA k).comp (hφ.prodMk (measurable_pi_apply i))

lemma measurable_risk_rule {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A)
    (D : Measure Z) [SFinite D] (m : ℕ) : Measurable (fun S : Fin m → Z => risk f D (A m S)) :=
  ((hA m).stronglyMeasurable.integral_prod_right' (ν := D)).measurable

lemma integral_empRisk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, empRisk f S h ∂(Measure.pi fun _ : Fin m => D) = risk f D h := by
  have hm' : (m:ℝ) ≠ 0 := by
    have : (0:ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hi : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f h (S i))
      (Measure.pi fun _ : Fin m => D) := fun i =>
    integrable_of_abs_le ((hP.measurable h).comp (measurable_pi_apply i)) B
      fun S => hP.bounded _ _
  have h1 : ∀ i : Fin m, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = risk f D h :=
    fun i => integral_comp_eval (hP.measurable h).aestronglyMeasurable
  have hsum : ∫ S, ∑ i, f h (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hi i
  unfold empRisk
  rw [integral_div, hsum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel_left₀ _ hm']

/-! ### Exchangeability of product measures -/


lemma perm_mp {ι : Type*} [Fintype ι] (D : Measure Z) [SigmaFinite D] (π : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → Z => fun i => x (π i)) (Measure.pi fun _ => D)
      (Measure.pi fun _ => D) := by
  have hmeas : Measurable (fun x : ι → Z => fun i => x (π i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (π i)
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → Z => fun i => x (π i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => s (π.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      have := h (π.symm i)
      simpa using this
    · intro h i
      have := h (π i)
      simpa using this
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp π.symm (fun i => D (s i))


lemma swap_mp {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D] (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Z) × Z => (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) ((Measure.pi fun _ : Fin m => D).prod D) := by
  set J := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin m) => Z) with hJdef
  have hJs : MeasurePreserving J.symm ((Measure.pi fun _ : Fin m => D).prod D)
      (Measure.pi fun _ : Option (Fin m) => D) :=
    ⟨J.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin m) => D)⟩
  have hJ : MeasurePreserving J (Measure.pi fun _ : Option (Fin m) => D)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    MeasurePreserving.symm J.symm hJs
  have hσ := perm_mp D (Equiv.swap (none : Option (Fin m)) (some i))
  have hc := hJ.comp (hσ.comp hJs)
  convert hc using 1
  funext p
  obtain ⟨x, rfl⟩ := J.surjective p
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · show Function.update (fun j => x (some j)) i (x none) =
      fun j => x (Equiv.swap none (some i) (some j))
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Equiv.swap_apply_def, hj]
  · show x (some i) = x (Equiv.swap none (some i) none)
    simp

noncomputable def gap (f : H → Z → ℝ) (A : Rule H Z) {m k : ℕ} (S : Fin m → Z)
    (τ : Fin k → Fin m) : ℝ :=
  empRisk f S (A k (fun j => S (τ j))) - ermValue f S

lemma gap_nonneg {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) {A : Rule H Z}
    {m k : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) (τ : Fin k → Fin m) : 0 ≤ gap f A S τ :=
  sub_nonneg.mpr (ermValue_le hP hm S _)

lemma unif_real_singleton {m : ℕ} [Nonempty (Fin m)] (i : Fin m) :
    (PMF.uniformOfFintype (Fin m)).toMeasure.real {i} = (m:ℝ)⁻¹ := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma pi_unif_real_singleton {m k : ℕ} [Nonempty (Fin m)] (τ : Fin k → Fin m) :
    (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure).real {τ}
      = ((m:ℝ)⁻¹) ^ k := by
  have : ({τ} : Set (Fin k → Fin m)) = Set.univ.pi (fun j => {τ j}) := by
    ext x
    simp [funext_iff]
  rw [measureReal_def, this, Measure.pi_pi, ENNReal.toReal_prod]
  have h1 : ∀ j : Fin k, ((PMF.uniformOfFintype (Fin m)).toMeasure {τ j}).toReal = (m:ℝ)⁻¹ :=
    fun j => unif_real_singleton (τ j)
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma risk_empMeasure (f : H → Z → ℝ) (hf : ∀ h, Measurable (f h)) {m : ℕ} [Nonempty (Fin m)]
    (S : Fin m → Z) (h : H) :
    risk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) h = empRisk f S h := by
  unfold risk empRisk
  rw [integral_map (measurable_of_countable S).aemeasurable (hf h).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite (μ := (PMF.uniformOfFintype (Fin m)).toMeasure))]
  simp only [unif_real_singleton, smul_eq_mul]
  rw [← Finset.mul_sum, inv_mul_eq_div]

/-- Consistency of `A` under the empirical distribution of `S`. -/
lemma empirical_consistency [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) {εc : ℕ → ℝ} (hc : UniversallyConsistent f A εc)
    {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (S : Fin m → Z) :
    ∑ τ : Fin k → Fin m, gap f A S τ ≤ (m:ℝ) ^ k * εc k := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hSm : Measurable S := measurable_of_countable S
  have : IsProbabilityMeasure ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) :=
    Measure.isProbabilityMeasure_map hSm.aemeasurable
  have hrisk : ∀ h : H, risk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) h
      = empRisk f S h := fun h => risk_empMeasure f hP.measurable S h
  have hopt : optRisk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) = ermValue f S := by
    unfold optRisk ermValue
    exact congrArg iInf (funext hrisk)
  have hcons := hc ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) inferInstance k hk
  unfold sampleLaw at hcons
  simp only [hrisk, hopt] at hcons
  have hpi : (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure.map S) =
      (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure).map
        (fun τ j => S (τ j)) :=
    (Measure.pi_map_pi (fun _ => hSm.aemeasurable)).symm
  have hmeasT : Measurable (fun T : Fin k → Z => empRisk f S (A k T) - ermValue f S) := by
    refine Measurable.sub_const ?_ _
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ => (hA k).comp (measurable_id.prodMk measurable_const)
  rw [hpi, integral_map (measurable_of_countable (fun τ : Fin k → Fin m => fun j => S (τ j))).aemeasurable
    hmeasT.aestronglyMeasurable] at hcons
  rw [integral_fintype (Integrable.of_finite
    (μ := Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin m)).toMeasure))] at hcons
  simp only [pi_unif_real_singleton, smul_eq_mul] at hcons
  rw [← Finset.mul_sum] at hcons
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have e : ∑ τ : Fin k → Fin m, gap f A S τ =
      (m:ℝ) ^ k * ((m:ℝ)⁻¹ ^ k * ∑ τ : Fin k → Fin m, gap f A S τ) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hmpos.ne', one_pow, one_mul]
  rw [e]
  exact mul_le_mul_of_nonneg_left hcons (by positivity)

/-! ### Resampling one coordinate -/

lemma resample (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (i : Fin m)
    {g : (Fin m → Z) → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂(Measure.pi fun _ : Fin m => D) =
      ∫ x, (∫ z, g (Function.update x i z) ∂D) ∂(Measure.pi fun _ : Fin m => D) := by
  have hmp := swap_mp D i
  have hG : Integrable (fun p : (Fin m → Z) × Z => g p.1)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    integrable_of_abs_le (hg.comp measurable_fst) C fun p => hC p.1
  have hmeasU : Measurable (fun p : (Fin m → Z) × Z => Function.update p.1 i p.2) :=
    measurable_fst.comp hmp.measurable
  have hU : Integrable (fun p : (Fin m → Z) × Z => g (Function.update p.1 i p.2))
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    integrable_of_abs_le (hg.comp hmeasU) C fun p => hC _
  have h1 : ∫ p, g p.1 ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ x, g x ∂(Measure.pi fun _ : Fin m => D) := by
    rw [integral_prod _ hG]
    simp
  have h2 : ∫ p, g (Function.update p.1 i p.2) ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ p, g p.1 ∂((Measure.pi fun _ : Fin m => D).prod D) := by
    have h := integral_map (μ := (Measure.pi fun _ : Fin m => D).prod D)
      hmp.measurable.aemeasurable (f := fun p : (Fin m → Z) × Z => g p.1)
      (by rw [hmp.map_eq]; exact (hg.comp measurable_fst).aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  have h3 : ∫ p, g (Function.update p.1 i p.2) ∂((Measure.pi fun _ : Fin m => D).prod D) =
      ∫ x, (∫ z, g (Function.update x i z) ∂D) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_prod _ hU
  rw [← h1, ← h2, h3]

lemma var_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) :
    ∫ z, (risk f D h - f h z) * (risk f D h - f h z) ∂D ≤ B ^ 2 := by
  have hb : ∀ z, f h z ^ 2 ≤ B ^ 2 := fun z =>
    sq_le_sq' (abs_le.mp (hP.bounded h z)).1 (abs_le.mp (hP.bounded h z)).2
  have hi : Integrable (f h) D := integrable_of_abs_le (hP.measurable h) B (hP.bounded h)
  have hi2 : Integrable (fun z => f h z ^ 2) D :=
    integrable_of_abs_le ((hP.measurable h).pow_const 2) (B ^ 2) fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact hb z
  have e : (fun z => (risk f D h - f h z) * (risk f D h - f h z)) =
      fun z => (risk f D h ^ 2 - 2 * risk f D h * f h z) + f h z ^ 2 := by
    funext z; ring
  have hr : ∫ z, f h z ∂D = risk f D h := rfl
  have hB : ∫ z, f h z ^ 2 ∂D ≤ B ^ 2 := by
    have := integral_mono hi2 (integrable_const (B ^ 2)) hb
    simpa using this
  rw [e, integral_add (f := fun z => risk f D h ^ 2 - 2 * risk f D h * f h z)
      (g := fun z => f h z ^ 2) ((integrable_const _).sub (hi.const_mul _)) hi2,
    integral_sub (f := fun _ => risk f D h ^ 2) (g := fun z => 2 * risk f D h * f h z)
      (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul, hr]
  simp only [probReal_univ, one_smul]
  nlinarith [sq_nonneg (risk f D h)]

/-! ### The per-`τ` deviation sum -/

noncomputable def Yv (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) {m k : ℕ}
    (τ : Fin k → Fin m) (i : Fin m) (S : Fin m → Z) : ℝ :=
  risk f D (A k (fun j => S (τ j))) - f (A k (fun j => S (τ j))) (S i)

noncomputable def Tv (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) {m k : ℕ}
    (τ : Fin k → Fin m) (S : Fin m → Z) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => i ∉ Finset.univ.image τ), Yv f A D τ i S

lemma measurable_Yv {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z)
    [SFinite D] {m k : ℕ} (τ : Fin k → Fin m) (i : Fin m) : Measurable (Yv f A D τ i) := by
  have hφ : Measurable (fun S : Fin m → Z => fun j => S (τ j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (τ j)
  exact ((measurable_risk_rule hA D k).comp hφ).sub ((hA k).comp (hφ.prodMk (measurable_pi_apply i)))

lemma abs_Yv_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (A : Rule H Z)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (τ : Fin k → Fin m) (i : Fin m)
    (S : Fin m → Z) : |Yv f A D τ i S| ≤ 2 * B := by
  unfold Yv
  have h1 := abs_risk_le hP D (A k (fun j => S (τ j)))
  have h2 := hP.bounded (A k (fun j => S (τ j))) (S i)
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma measurable_Tv {f : H → Z → ℝ} {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z)
    [SFinite D] {m k : ℕ} (τ : Fin k → Fin m) : Measurable (Tv f A D τ) := by
  unfold Tv
  exact Finset.measurable_sum _ fun i _ => measurable_Yv hA D τ i

lemma abs_Tv_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (A : Rule H Z)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (τ : Fin k → Fin m)
    (S : Fin m → Z) : |Tv f A D τ S| ≤ m * (2 * B) := by
  unfold Tv
  calc |∑ i ∈ Finset.univ.filter (fun i => i ∉ Finset.univ.image τ), Yv f A D τ i S|
      ≤ ∑ i ∈ Finset.univ.filter (fun i => i ∉ Finset.univ.image τ), |Yv f A D τ i S| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, |Yv f A D τ i S| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _i : Fin m, 2 * B := Finset.sum_le_sum fun i _ => abs_Yv_le hP A D τ i S
    _ = m * (2 * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [MeasurableSpace Z] in
lemma comp_update_of_notMem {m k : ℕ} (τ : Fin k → Fin m) {j : Fin m}
    (hj : j ∉ Finset.univ.image τ) (S : Fin m → Z) (z : Z) :
    (fun l => Function.update S j z (τ l)) = fun l => S (τ l) := by
  funext l
  have : τ l ≠ j := fun h => hj (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, h⟩)
  exact Function.update_of_ne this _ _

lemma integral_Yv_mul_eq_zero {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {m k : ℕ} (τ : Fin k → Fin m) {j l : Fin m} (hj : j ∉ Finset.univ.image τ) (hjl : l ≠ j) :
    ∫ S, Yv f A D τ j S * Yv f A D τ l S ∂(Measure.pi fun _ : Fin m => D) = 0 := by
  rw [resample D j (g := fun S => Yv f A D τ j S * Yv f A D τ l S)
    ((measurable_Yv hA D τ j).mul (measurable_Yv hA D τ l)) (2 * B * (2 * B))
    (fun S => by
      rw [abs_mul]
      exact mul_le_mul (abs_Yv_le hP A D τ j S) (abs_Yv_le hP A D τ l S) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_Yv_le hP A D τ j S)))]
  refine (integral_congr_ae (ae_of_all _ fun S => ?_)).trans (integral_zero _ _)
  have e1 : ∀ z, Yv f A D τ j (Function.update S j z) =
      risk f D (A k (fun t => S (τ t))) - f (A k (fun t => S (τ t))) z := by
    intro z
    unfold Yv
    rw [comp_update_of_notMem τ hj S z, Function.update_self]
  have e2 : ∀ z, Yv f A D τ l (Function.update S j z) = Yv f A D τ l S := by
    intro z
    unfold Yv
    rw [comp_update_of_notMem τ hj S z, Function.update_of_ne hjl]
  simp only [e1, e2]
  have hi : Integrable (f (A k (fun t => S (τ t)))) D :=
    integrable_of_abs_le (hP.measurable _) B (hP.bounded _)
  rw [integral_mul_const, integral_sub (integrable_const _) hi, integral_const]
  have hr : ∫ z, f (A k (fun t => S (τ t))) z ∂D = risk f D (A k (fun t => S (τ t))) := rfl
  rw [hr]
  simp

lemma integral_Yv_sq_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {m k : ℕ} (τ : Fin k → Fin m) {j : Fin m} (hj : j ∉ Finset.univ.image τ) :
    ∫ S, Yv f A D τ j S * Yv f A D τ j S ∂(Measure.pi fun _ : Fin m => D) ≤ B ^ 2 := by
  rw [resample D j (g := fun S => Yv f A D τ j S * Yv f A D τ j S)
    ((measurable_Yv hA D τ j).mul (measurable_Yv hA D τ j)) (2 * B * (2 * B))
    (fun S => by
      rw [abs_mul]
      exact mul_le_mul (abs_Yv_le hP A D τ j S) (abs_Yv_le hP A D τ j S) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_Yv_le hP A D τ j S)))]
  have e1 : ∀ S z, Yv f A D τ j (Function.update S j z) =
      risk f D (A k (fun t => S (τ t))) - f (A k (fun t => S (τ t))) z := by
    intro S z
    unfold Yv
    rw [comp_update_of_notMem τ hj S z, Function.update_self]
  simp only [e1]
  calc ∫ S, (∫ z, (risk f D (A k (fun t => S (τ t))) - f (A k (fun t => S (τ t))) z) *
        (risk f D (A k (fun t => S (τ t))) - f (A k (fun t => S (τ t))) z) ∂D)
        ∂(Measure.pi fun _ : Fin m => D)
      ≤ ∫ _S, B ^ 2 ∂(Measure.pi fun _ : Fin m => D) :=
        integral_mono_of_nonneg (ae_of_all _ fun S => integral_nonneg fun z => mul_self_nonneg _)
          (integrable_const _) (ae_of_all _ fun S => var_le hP D _)
    _ = B ^ 2 := by simp

lemma integral_Tv_sq_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {m k : ℕ} (τ : Fin k → Fin m) :
    ∫ S, Tv f A D τ S * Tv f A D τ S ∂(Measure.pi fun _ : Fin m => D) ≤ m * B ^ 2 := by
  set J := Finset.univ.filter (fun i : Fin m => i ∉ Finset.univ.image τ) with hJ
  have hint : ∀ j l : Fin m, Integrable (fun S => Yv f A D τ j S * Yv f A D τ l S)
      (Measure.pi fun _ : Fin m => D) := fun j l =>
    integrable_of_abs_le ((measurable_Yv hA D τ j).mul (measurable_Yv hA D τ l)) (2 * B * (2 * B))
      (fun S => by
        rw [abs_mul]
        exact mul_le_mul (abs_Yv_le hP A D τ j S) (abs_Yv_le hP A D τ l S) (abs_nonneg _)
          ((abs_nonneg _).trans (abs_Yv_le hP A D τ j S)))
  have e : (fun S => Tv f A D τ S * Tv f A D τ S) =
      fun S => ∑ j ∈ J, ∑ l ∈ J, Yv f A D τ j S * Yv f A D τ l S := by
    funext S
    unfold Tv
    rw [Finset.sum_mul_sum]
  rw [e, integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun l _ => hint j l)]
  have inner : ∀ j ∈ J, ∫ S, ∑ l ∈ J, Yv f A D τ j S * Yv f A D τ l S
      ∂(Measure.pi fun _ : Fin m => D) ≤ B ^ 2 := by
    intro j hjJ
    have hj : j ∉ Finset.univ.image τ := (Finset.mem_filter.mp hjJ).2
    rw [integral_finsetSum _ (fun l _ => hint j l),
      Finset.sum_eq_single_of_mem j hjJ (fun l _ hne => integral_Yv_mul_eq_zero hP hA D τ hj hne)]
    exact integral_Yv_sq_le hP hA D τ hj
  calc ∑ j ∈ J, ∫ S, ∑ l ∈ J, Yv f A D τ j S * Yv f A D τ l S ∂(Measure.pi fun _ : Fin m => D)
      ≤ ∑ _j ∈ J, B ^ 2 := Finset.sum_le_sum inner
    _ = J.card * B ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ m * B ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
        have : J.card ≤ m := by
          have := Finset.card_le_univ J
          rwa [Fintype.card_fin] at this
        exact_mod_cast this

lemma integral_abs_Tv_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (hB : 0 ≤ B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {m k : ℕ} (hm : 1 ≤ m) (τ : Fin k → Fin m) :
    ∫ S, |Tv f A D τ S| ∂(Measure.pi fun _ : Fin m => D) ≤ B * Real.sqrt m := by
  rcases hB.eq_or_lt with hB0 | hBpos
  · have h0 : ∀ S, Tv f A D τ S = 0 := fun S => by
      have := abs_Tv_le hP A D τ S
      rw [← hB0, mul_zero, mul_zero] at this
      exact abs_nonpos_iff.mp this
    simp [h0, ← hB0]
  · have hm' : (0:ℝ) < m := by exact_mod_cast hm
    set c := B * Real.sqrt m with hc
    have hcpos : 0 < c := mul_pos hBpos (Real.sqrt_pos.mpr hm')
    have hc2 : c ^ 2 = m * B ^ 2 := by
      rw [hc, mul_pow, Real.sq_sqrt hm'.le]; ring
    have hpt : ∀ S, |Tv f A D τ S| ≤ (Tv f A D τ S * Tv f A D τ S + c ^ 2) / (2 * c) := by
      intro S
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|Tv f A D τ S| - c), sq_abs (Tv f A D τ S)]
    have hTm := measurable_Tv hA D τ
    have hiT2 : Integrable (fun S => Tv f A D τ S * Tv f A D τ S)
        (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le (hTm.mul hTm) (m * (2 * B) * (m * (2 * B))) (fun S => by
        rw [abs_mul]
        exact mul_le_mul (abs_Tv_le hP A D τ S) (abs_Tv_le hP A D τ S) (abs_nonneg _)
          ((abs_nonneg _).trans (abs_Tv_le hP A D τ S)))
    have hiA : Integrable (fun S => |Tv f A D τ S|) (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le hTm.abs (m * (2 * B)) (fun S => by
        rw [abs_abs]; exact abs_Tv_le hP A D τ S)
    calc ∫ S, |Tv f A D τ S| ∂(Measure.pi fun _ : Fin m => D)
        ≤ ∫ S, (Tv f A D τ S * Tv f A D τ S + c ^ 2) / (2 * c)
            ∂(Measure.pi fun _ : Fin m => D) :=
          integral_mono hiA ((hiT2.add (integrable_const _)).div_const _) hpt
      _ = (∫ S, Tv f A D τ S * Tv f A D τ S ∂(Measure.pi fun _ : Fin m => D) + c ^ 2)
            / (2 * c) := by
          rw [integral_div, integral_add hiT2 (integrable_const _), integral_const]
          simp
      _ ≤ (m * B ^ 2 + c ^ 2) / (2 * c) := by
          gcongr
          exact integral_Tv_sq_le hP hA D τ
      _ = c := by
          rw [← hc2]
          field_simp
          ring

/-! ### Pointwise split -/

lemma risk_sub_empRisk_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (A : Rule H Z)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hm : 1 ≤ m) (τ : Fin k → Fin m)
    (S : Fin m → Z) :
    risk f D (A k (fun j => S (τ j))) - empRisk f S (A k (fun j => S (τ j)))
      ≤ (k * (2 * B) + |Tv f A D τ S|) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set h := A k (fun j => S (τ j)) with hh
  have e : risk f D h - empRisk f S h = (∑ i, Yv f A D τ i S) / m := by
    unfold empRisk Yv
    rw [← hh, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hm'.le
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ Finset.univ.image τ)]
  have h1 : ∑ i ∈ Finset.univ.filter (fun i => i ∈ Finset.univ.image τ), Yv f A D τ i S
      ≤ k * (2 * B) := by
    have hcard : (Finset.univ.filter (fun i : Fin m => i ∈ Finset.univ.image τ)).card ≤ k := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.card_image_le.trans (by simp)
    calc ∑ i ∈ Finset.univ.filter (fun i => i ∈ Finset.univ.image τ), Yv f A D τ i S
        ≤ (Finset.univ.filter (fun i : Fin m => i ∈ Finset.univ.image τ)).card • (2 * B) :=
          Finset.sum_le_card_nsmul _ _ _ fun i _ => (abs_le.mp (abs_Yv_le hP A D τ i S)).2
      _ ≤ k * (2 * B) := by
          rw [nsmul_eq_mul]
          have hB : 0 ≤ 2 * B := (abs_nonneg _).trans (abs_Yv_le hP A D τ ⟨0, hm⟩ S)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ i ∈ Finset.univ.image τ), Yv f A D τ i S
      ≤ |Tv f A D τ S| := le_abs_self _
  linarith

/-! ### Assembly -/

lemma pointwise_bound [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) {εc : ℕ → ℝ} (hc : UniversallyConsistent f A εc)
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (S : Fin m → Z) :
    optRisk f D - ermValue f S ≤
      εc k + (∑ τ : Fin k → Fin m, (k * (2 * B) + |Tv f A D τ S|)) / m / (m:ℝ) ^ k := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hN : (0:ℝ) < (m:ℝ) ^ k := by positivity
  have hcons := empirical_consistency hP hA hc hm hk S
  have hbdd : BddBelow (Set.range (risk f D)) :=
    ⟨-B, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_risk_le hP D h)).1⟩
  have each : ∀ τ : Fin k → Fin m, optRisk f D - ermValue f S ≤
      gap f A S τ + (k * (2 * B) + |Tv f A D τ S|) / m := by
    intro τ
    have h1 : optRisk f D ≤ risk f D (A k (fun j => S (τ j))) := ciInf_le hbdd _
    have h2 := risk_sub_empRisk_le hP A D hm τ S
    unfold gap
    linarith
  have hsum := Finset.sum_le_sum (fun τ (_ : τ ∈ (Finset.univ : Finset (Fin k → Fin m))) => each τ)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div] at hsum
  push_cast at hsum
  have key : (m:ℝ) ^ k * (optRisk f D - ermValue f S) ≤
      (m:ℝ) ^ k * εc k + (∑ τ : Fin k → Fin m, (k * (2 * B) + |Tv f A D τ S|)) / m := by
    linarith
  have := div_le_div_of_nonneg_right key hN.le
  rwa [mul_div_cancel_left₀ _ hN.ne', add_div, mul_div_cancel_left₀ _ hN.ne'] at this

theorem main [Nonempty H] (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D]
    (m m' : ℕ) (hm'2 : 2 ≤ m') (hm'm : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤
      2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by
  have hm : 1 ≤ m := by omega
  have hk : 1 ≤ m' := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hN : (0:ℝ) < (m:ℝ) ^ m' := by positivity
  have hZ : Nonempty Z := by
    rcases isEmpty_or_nonempty Z with hZ | hZ
    · exfalso
      have h1 := measure_univ (μ := D)
      rw [Set.univ_eq_empty_iff.mpr hZ, measure_empty] at h1
      exact zero_ne_one h1
    · exact hZ
  have hB : 0 ≤ B :=
    (abs_nonneg _).trans (hP.bounded (Classical.arbitrary H) (Classical.arbitrary Z))
  have hc0 : (0:ℝ) ≤ m' * (2 * B) := by positivity
  unfold sampleLaw
  have hεnn : 0 ≤ εcons m' := by
    have h := empirical_consistency hP hA hcons hm hk (fun _ : Fin m => Classical.arbitrary Z)
    have h0 : 0 ≤ ∑ τ : Fin m' → Fin m, gap f A (fun _ : Fin m => Classical.arbitrary Z) τ :=
      Finset.sum_nonneg fun τ _ => gap_nonneg hP hm _ τ
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hN hneg
    linarith
  set Q : (Fin m → Z) → ℝ := fun S =>
    εcons m' + (∑ τ : Fin m' → Fin m, (m' * (2 * B) + |Tv f A D τ S|)) / m / (m:ℝ) ^ m'
    with hQ
  have hpt : ∀ S, optRisk f D - ermValue f S ≤ Q S := fun S =>
    pointwise_bound hP hA hcons D hm hk S
  have hQnn : ∀ S, 0 ≤ Q S := fun S =>
    add_nonneg hεnn (div_nonneg (div_nonneg
      (Finset.sum_nonneg fun τ _ => add_nonneg hc0 (abs_nonneg _)) hm'.le) hN.le)
  have habs : ∀ S, |ermValue f S - optRisk f D| ≤ (ermValue f S - optRisk f D) + 2 * Q S := by
    intro S
    have h1 := hpt S
    have h2 := hQnn S
    rcases le_total 0 (ermValue f S - optRisk f D) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  have hermI : Integrable (fun S => ermValue f S) (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le (hP.measurable_ermValue m) B (fun S => abs_le.mpr
      ⟨neg_le_ermValue hP hm S, (ermValue_le hP hm S (Classical.arbitrary H)).trans
        (abs_le.mp (abs_empRisk_le hP hm S _)).2⟩)
  have hXI : Integrable (fun S => ermValue f S - optRisk f D) (Measure.pi fun _ : Fin m => D) :=
    hermI.sub (integrable_const _)
  have hTI : ∀ τ : Fin m' → Fin m, Integrable (fun S => |Tv f A D τ S|)
      (Measure.pi fun _ : Fin m => D) := fun τ =>
    integrable_of_abs_le (measurable_Tv hA D τ).abs (m * (2 * B))
      (fun S => by rw [abs_abs]; exact abs_Tv_le hP A D τ S)
  have hSumI : Integrable (fun S => ∑ τ : Fin m' → Fin m, (m' * (2 * B) + |Tv f A D τ S|))
      (Measure.pi fun _ : Fin m => D) :=
    integrable_finsetSum _ fun τ _ => (integrable_const _).add (hTI τ)
  have hQI : Integrable Q (Measure.pi fun _ : Fin m => D) :=
    (integrable_const _).add ((hSumI.div_const _).div_const _)
  have hempI : ∀ h, Integrable (fun S => empRisk f S h) (Measure.pi fun _ : Fin m => D) :=
    fun h => integrable_of_abs_le (by
      unfold empRisk
      exact (Finset.measurable_sum _ fun i _ => (hP.measurable h).comp
        (measurable_pi_apply i)).div_const _) B (fun S => abs_empRisk_le hP hm S h)
  have hEX : ∫ S, (ermValue f S - optRisk f D) ∂(Measure.pi fun _ : Fin m => D) ≤ 0 := by
    rw [integral_sub hermI (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    have : ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D) ≤ optRisk f D :=
      le_ciInf fun h => (integral_mono hermI (hempI h) (fun S => ermValue_le hP hm S h)).trans_eq
        (integral_empRisk hP D hm h)
    linarith
  have hEQ : ∫ S, Q S ∂(Measure.pi fun _ : Fin m => D) ≤
      εcons m' + (m' * (2 * B) + B * Real.sqrt m) / m := by
    simp only [hQ]
    rw [integral_add (integrable_const _) ((hSumI.div_const _).div_const _), integral_const,
      integral_div, integral_div,
      integral_finsetSum (f := fun τ S => m' * (2 * B) + |Tv f A D τ S|) _
        (fun τ _ => (integrable_const _).add (hTI τ))]
    simp only [probReal_univ, one_smul]
    have hb : ∑ τ : Fin m' → Fin m, ∫ S, (m' * (2 * B) + |Tv f A D τ S|)
        ∂(Measure.pi fun _ : Fin m => D) ≤ (m:ℝ) ^ m' * (m' * (2 * B) + B * Real.sqrt m) := by
      calc ∑ τ : Fin m' → Fin m, ∫ S, (m' * (2 * B) + |Tv f A D τ S|)
            ∂(Measure.pi fun _ : Fin m => D)
          ≤ ∑ _τ : Fin m' → Fin m, (m' * (2 * B) + B * Real.sqrt m) :=
            Finset.sum_le_sum fun τ _ => by
              rw [integral_add (integrable_const _) (hTI τ), integral_const]
              simp only [probReal_univ, one_smul]
              linarith [integral_abs_Tv_le hP hB hA D hm τ]
        _ = (m:ℝ) ^ m' * (m' * (2 * B) + B * Real.sqrt m) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have : (∑ τ : Fin m' → Fin m, ∫ S, (m' * (2 * B) + |Tv f A D τ S|)
        ∂(Measure.pi fun _ : Fin m => D)) / m / (m:ℝ) ^ m' ≤
        (m' * (2 * B) + B * Real.sqrt m) / m := by
      calc _ ≤ ((m:ℝ) ^ m' * (m' * (2 * B) + B * Real.sqrt m)) / m / (m:ℝ) ^ m' := by
            gcongr
        _ = (m' * (2 * B) + B * Real.sqrt m) / m := by
            field_simp
    linarith
  have hsp : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  have e1 : B * Real.sqrt m / m = B / Real.sqrt m := by
    rw [div_eq_div_iff hm'.ne' hsp.ne', mul_assoc, hs]
  have hm'2r : (2:ℝ) ≤ m' := by exact_mod_cast hm'2
  have e2 : (m':ℝ) * (2 * B) / m ≤ B * (m':ℝ) ^ 2 / m :=
    div_le_div_of_nonneg_right (by nlinarith) hm'.le
  have e3 : 2 * B / Real.sqrt m = 2 * (B / Real.sqrt m) := mul_div_assoc _ _ _
  have e4 : 2 * B * (m':ℝ) ^ 2 / m = 2 * (B * (m':ℝ) ^ 2 / m) := by
    rw [mul_assoc, mul_div_assoc]
  have e5 : (m' * (2 * B) + B * Real.sqrt m) / m = m' * (2 * B) / m + B * Real.sqrt m / m :=
    add_div _ _ _
  calc ∫ S, |ermValue f S - optRisk f D| ∂(Measure.pi fun _ : Fin m => D)
      ≤ ∫ S, ((ermValue f S - optRisk f D) + 2 * Q S) ∂(Measure.pi fun _ : Fin m => D) :=
        integral_mono hXI.abs (hXI.add (hQI.const_mul 2)) habs
    _ = ∫ S, (ermValue f S - optRisk f D) ∂(Measure.pi fun _ : Fin m => D)
          + 2 * ∫ S, Q S ∂(Measure.pi fun _ : Fin m => D) := by
        rw [integral_add hXI (hQI.const_mul 2), integral_const_mul]
    _ ≤ 2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by
        rw [e3, e4]
        rw [e5, e1] at hEQ
        nlinarith

end LearnStability.Characterization.L16Proof

open LearnStability.Characterization MeasureTheory in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D]
    (m m' : ℕ) (hm'2 : 2 ≤ m') (hm'm : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m) ≤
      2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by
  exact L16Proof.main f B hP A hA εcons hcons D m m' hm'2 hm'm
