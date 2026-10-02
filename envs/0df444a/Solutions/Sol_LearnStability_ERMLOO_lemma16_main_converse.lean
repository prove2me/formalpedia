-- Prove2me | solution 1 for LearnStability.ERMLOO.lemma16_main_converse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:49:27.675951+00:00
-- url     : https://prove2.me/submissions/9d80d54c-7962-4496-8804-b01237f2de27

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting
import Definitions.Def_LearnStability_ERMLOO_RuleProperties

/-! f4fdbe56 LearnStability.ERMLOO.lemma16_main_converse.
Upper side: `F_S(ĥ_S) ≤ F_S(h)` for a near-optimal `h`, and `E|F_S(h) - F(h)| ≤ B/√m` (variance).
Lower side: consistency of `A` under the empirical distribution `D_S` bounds the average over
all `σ : Fin k → Fin m` of `F_S(A(S∘σ))` by `F_S(ĥ_S) + ε(k)`; for every `σ` and every
coordinate `i ∉ range σ`, `z_i` is independent of `S∘σ`, so `E[f(A(S∘σ)); z_i] ≥ F*`. -/

set_option autoImplicit false

namespace LearnStability.ERMLOO.L16Proof

open MeasureTheory Filter Topology ProbabilityTheory LearnStability.ERMLOO

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

lemma abs_ermValue_le [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {m : ℕ} (hm : 1 ≤ m) (S : Fin m → Z) : |ermValue f S| ≤ B := by
  obtain ⟨h0⟩ := ‹Nonempty H›
  have h1 := ermValue_le hP hm S h0
  have h2 := (abs_le.mp (abs_empRisk_le hP hm S h0)).2
  have h3 := neg_le_ermValue hP hm S
  exact abs_le.mpr ⟨h3, h1.trans h2⟩

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

lemma bddBelow_risk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] : BddBelow (Set.range fun h => risk f D h) :=
  ⟨-B, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_risk_le hP D h)).1⟩

lemma optRisk_le_risk {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : optRisk f D ≤ risk f D h :=
  ciInf_le (bddBelow_risk hP D) h

lemma abs_optRisk_le [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (D : Measure Z) [IsProbabilityMeasure D] : |optRisk f D| ≤ B := by
  obtain ⟨h0⟩ := ‹Nonempty H›
  refine abs_le.mpr ⟨le_ciInf fun h => (abs_le.mp (abs_risk_le hP D h)).1, ?_⟩
  exact (optRisk_le_risk hP D h0).trans (abs_le.mp (abs_risk_le hP D h0)).2

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

lemma unif_real_singleton {m : ℕ} [Nonempty (Fin m)] (i : Fin m) :
    (PMF.uniformOfFintype (Fin m)).toMeasure.real {i} = (m:ℝ)⁻¹ := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast]

lemma risk_empMeasure (f : H → Z → ℝ) (hf : ∀ h, Measurable (f h)) {m : ℕ} [Nonempty (Fin m)]
    (S : Fin m → Z) (h : H) :
    risk f ((PMF.uniformOfFintype (Fin m)).toMeasure.map S) h = empRisk f S h := by
  unfold risk empRisk
  rw [integral_map (measurable_of_countable S).aemeasurable (hf h).aestronglyMeasurable,
    integral_fintype (Integrable.of_finite (μ := (PMF.uniformOfFintype (Fin m)).toMeasure))]
  simp only [unif_real_singleton, smul_eq_mul]
  rw [← Finset.mul_sum, inv_mul_eq_div]

/-- Consistency of `A` under the empirical distribution of `S`, averaged form. -/
lemma empirical_consistency [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) {εc : ℕ → ℝ} (hc : UniversallyConsistent f A εc)
    {n k : ℕ} (hk : 1 ≤ k) (S : Fin (n + 1) → Z) :
    ∫ τ, empRisk f S (A k (fun j => S (τ j)))
        ∂(Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin (n + 1))).toMeasure)
      ≤ ermValue f S + εc k := by
  have hSm : Measurable S := measurable_of_countable S
  have : IsProbabilityMeasure ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map S) :=
    Measure.isProbabilityMeasure_map hSm.aemeasurable
  have hrisk : ∀ h : H, risk f ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map S) h
      = empRisk f S h := fun h => risk_empMeasure f hP.measurable S h
  have hopt : optRisk f ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map S) = ermValue f S := by
    unfold optRisk ermValue
    exact congrArg iInf (funext hrisk)
  have hcons := hc ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map S) inferInstance k hk
  unfold sampleLaw at hcons
  simp only [hrisk, hopt] at hcons
  have hpi : (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin (n + 1))).toMeasure.map S) =
      (Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin (n + 1))).toMeasure).map
        (fun τ j => S (τ j)) :=
    (Measure.pi_map_pi (fun _ => hSm.aemeasurable)).symm
  have hmeasT : Measurable (fun T : Fin k → Z => empRisk f S (A k T) - ermValue f S) := by
    refine Measurable.sub_const ?_ _
    unfold empRisk
    refine Measurable.div_const ?_ _
    exact Finset.measurable_sum _ fun i _ => (hA k).comp (measurable_id.prodMk measurable_const)
  rw [hpi, integral_map (measurable_of_countable (fun τ : Fin k → Fin (n + 1) => fun j => S (τ j))).aemeasurable
    hmeasT.aestronglyMeasurable] at hcons
  rw [integral_sub (Integrable.of_finite) (integrable_const _), integral_const] at hcons
  simp only [probReal_univ, one_smul] at hcons
  linarith

/-- Independence: a coordinate outside the range of `σ` is a fresh test point. -/
lemma coord_ge [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {n k : ℕ} (σ : Fin k → Fin (n + 1)) (i : Fin (n + 1)) (hσ : ∀ j, σ j ≠ i) :
    optRisk f D ≤ ∫ S, f (A k (fun j => S (σ j))) (S i) ∂(Measure.pi fun _ : Fin (n + 1) => D) := by
  have hex : ∀ j, ∃ t, i.succAbove t = σ j := fun j => Fin.exists_succAbove_eq (hσ j)
  choose τ hτ using hex
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i with he
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) i
  let Φ : Z × (Fin n → Z) → ℝ := fun p => f (A k (fun j => p.2 (τ j))) p.1
  have hΦm : Measurable Φ := by
    have h0 : Measurable (fun p : Z × (Fin n → Z) => ((fun j => p.2 (τ j)), p.1)) := by
      fun_prop
    have := (hA k).comp h0
    exact this
  have hΦi : Integrable Φ (D.prod (Measure.pi fun _ : Fin n => D)) :=
    integrable_of_abs_le hΦm B fun p => hP.bounded _ _
  have hcomp : ∀ S : Fin (n + 1) → Z, f (A k (fun j => S (σ j))) (S i) = Φ (e S) := by
    intro S
    simp only [Φ, he, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      Fin.removeNth, ← hτ]
  simp_rw [hcomp]
  rw [mp.integral_comp' (g := Φ), integral_prod_symm Φ hΦi]
  have hin : ∀ y : Fin n → Z, ∫ x, Φ (x, y) ∂D = risk f D (A k (fun j => y (τ j))) := fun y => rfl
  simp_rw [hin]
  have hmeas : Measurable (fun y : Fin n → Z => risk f D (A k (fun j => y (τ j)))) :=
    (measurable_risk_rule hA D k).comp (measurable_pi_lambda _ fun j => measurable_pi_apply (τ j))
  have hint : Integrable (fun y : Fin n → Z => risk f D (A k (fun j => y (τ j))))
      (Measure.pi fun _ : Fin n => D) :=
    integrable_of_abs_le hmeas B fun y => abs_risk_le hP D _
  calc optRisk f D = ∫ _y : Fin n → Z, optRisk f D ∂(Measure.pi fun _ : Fin n => D) := by
        simp
    _ ≤ _ := integral_mono (integrable_const _) hint fun y => optRisk_le_risk hP D _

/-- Per-`σ` lower bound. -/
lemma sigma_ge [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    {A : Rule H Z} (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    {n k : ℕ} (σ : Fin k → Fin (n + 1)) :
    optRisk f D - 2 * B * k / (n + 1 : ℕ) ≤
      ∫ S, empRisk f S (A k (fun j => S (σ j))) ∂(Measure.pi fun _ : Fin (n + 1) => D) := by
  set μ := Measure.pi fun _ : Fin (n + 1) => D
  set F := optRisk f D
  have hB : 0 ≤ B := (abs_nonneg _).trans (abs_optRisk_le hP D)
  have hF := abs_le.mp (abs_optRisk_le hP D)
  have hm : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmeas : ∀ i : Fin (n + 1), Measurable (fun S : Fin (n + 1) → Z =>
      f (A k (fun j => S (σ j))) (S i)) := fun i => by
    have h0 : Measurable (fun S : Fin (n + 1) → Z => ((fun j => S (σ j)), S i)) := by
      fun_prop
    have := (hA k).comp h0
    exact this
  have hint : ∀ i : Fin (n + 1), Integrable (fun S : Fin (n + 1) → Z =>
      f (A k (fun j => S (σ j))) (S i)) μ := fun i =>
    integrable_of_abs_le (hmeas i) B fun S => hP.bounded _ _
  set s := Finset.univ.image σ
  have hs : s.card ≤ k := by
    calc s.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  have hterm : ∀ i : Fin (n + 1), F - (if i ∈ s then F + B else 0) ≤
      ∫ S, f (A k (fun j => S (σ j))) (S i) ∂μ := by
    intro i
    by_cases hi : i ∈ s
    · rw [if_pos hi]
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun S : Fin (n + 1) → Z => f (A k (fun j => S (σ j))) (S i)) (C := B)
        (ae_of_all _ fun S => by rw [Real.norm_eq_abs]; exact hP.bounded _ _)
      rw [Real.norm_eq_abs] at this
      simp only [probReal_univ, mul_one] at this
      have := (abs_le.mp this).1
      linarith
    · rw [if_neg hi, sub_zero]
      refine coord_ge hP hA D σ i fun j hj => hi ?_
      rw [← hj]
      exact Finset.mem_image_of_mem σ (Finset.mem_univ j)
  have hsum : ∑ i : Fin (n + 1), (F - (if i ∈ s then F + B else 0)) ≤
      ∑ i : Fin (n + 1), ∫ S, f (A k (fun j => S (σ j))) (S i) ∂μ :=
    Finset.sum_le_sum fun i _ => hterm i
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hE : ∫ S, empRisk f S (A k (fun j => S (σ j))) ∂μ =
      (∑ i : Fin (n + 1), ∫ S, f (A k (fun j => S (σ j))) (S i) ∂μ) / (n + 1 : ℕ) := by
    unfold empRisk
    rw [integral_div, integral_finsetSum _ fun i _ => hint i]
  rw [hE, le_div_iff₀ hm]
  have hcard : (s.card : ℝ) ≤ k := by exact_mod_cast hs
  have hFB : 0 ≤ F + B := by linarith
  have hk0 : (0:ℝ) ≤ k := by positivity
  have e1 : (optRisk f D - 2 * B * k / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ)
      = F * ((n + 1 : ℕ) : ℝ) - 2 * B * k := by
    field_simp
    ring
  rw [e1]
  have h2 : (s.card : ℝ) * (F + B) ≤ k * (2 * B) := by
    apply mul_le_mul hcard (by linarith) hFB hk0
  push_cast at hsum ⊢
  nlinarith

/-- Lower side: `F* - E[F_S(ĥ_S)] ≤ ε(k) + 2Bk/m`. -/
lemma lower [Nonempty H] {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B)
    (herm : MeasurableERMValue f) {A : Rule H Z} (hA : MeasurableRule f A) {εc : ℕ → ℝ}
    (hc : UniversallyConsistent f A εc) (D : Measure Z) [IsProbabilityMeasure D]
    {n k : ℕ} (hk : 1 ≤ k) :
    optRisk f D - 2 * B * k / (n + 1 : ℕ) - εc k ≤
      ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin (n + 1) => D) := by
  set μ := Measure.pi fun _ : Fin (n + 1) => D
  set P := Measure.pi fun _ : Fin k => (PMF.uniformOfFintype (Fin (n + 1))).toMeasure
  let G : (Fin (n + 1) → Z) → (Fin k → Fin (n + 1)) → ℝ :=
    fun S τ => empRisk f S (A k (fun j => S (τ j)))
  have hGm : Measurable (Function.uncurry G) := by
    refine measurable_from_prod_countable_left fun τ => ?_
    exact measurable_empRisk_rule hA (measurable_pi_lambda _ fun j => measurable_pi_apply (τ j))
  have hGi : Integrable (Function.uncurry G) (μ.prod P) :=
    integrable_of_abs_le hGm B fun p => abs_empRisk_le hP (by omega) _ _
  have hI : Integrable (fun S => ∫ τ, G S τ ∂P) μ := hGi.integral_prod_left
  have hEi : Integrable (fun S : Fin (n + 1) → Z => ermValue f S) μ :=
    integrable_of_abs_le (herm (n + 1)) B fun S => abs_ermValue_le hP (by omega) S
  have h1 : ∫ S, ∫ τ, G S τ ∂P ∂μ ≤ ∫ S, (ermValue f S + εc k) ∂μ :=
    integral_mono hI (hEi.add (integrable_const _)) fun S =>
      empirical_consistency hP hA hc hk S
  rw [integral_add hEi (integrable_const _), integral_const] at h1
  simp only [probReal_univ, one_smul] at h1
  rw [integral_integral_swap hGi] at h1
  have h2 : ∫ _τ, (optRisk f D - 2 * B * k / (n + 1 : ℕ)) ∂P ≤ ∫ τ, ∫ S, G S τ ∂μ ∂P :=
    integral_mono (integrable_const _) Integrable.of_finite fun τ => sigma_ge hP hA D τ
  rw [integral_const] at h2
  simp only [probReal_univ, one_smul] at h2
  linarith

/-- Upper side ingredient: `E|F_S(h) - F(h)| ≤ B/√m`. -/
lemma dev_le {f : H → Z → ℝ} {B : ℝ} (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (hB : 0 ≤ B) {n : ℕ} (h : H) :
    ∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin (n + 1) => D)
      ≤ B / Real.sqrt (n + 1 : ℕ) := by
  set μ := Measure.pi fun _ : Fin (n + 1) => D
  set m : ℝ := ((n + 1 : ℕ) : ℝ) with hmdef
  have hm : 0 < m := by positivity
  set Y : Fin (n + 1) → (Fin (n + 1) → Z) → ℝ := fun i S => f h (S i)
  have hYm : ∀ i, Measurable (Y i) := fun i => (hP.measurable h).comp (measurable_pi_apply i)
  have hYb : ∀ i S, |Y i S| ≤ B := fun i S => hP.bounded _ _
  set W : (Fin (n + 1) → Z) → ℝ := ∑ i, Y i with hW
  have hWapp : ∀ S, W S = ∑ i, f h (S i) := fun S => by simp [hW, Y, Finset.sum_apply]
  have hWm : Measurable W := by
    have : W = fun S => ∑ i, f h (S i) := funext hWapp
    rw [this]
    exact Finset.measurable_sum _ fun i _ => hYm i
  have hWb : ∀ S, |W S| ≤ m * B := by
    intro S
    rw [hWapp]
    calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + 1), B := Finset.sum_le_sum fun i _ => hP.bounded h (S i)
      _ = m * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- mean of W
  have hEW : ∫ S, W S ∂μ = m * risk f D h := by
    simp_rw [hWapp]
    rw [integral_finsetSum _ fun i _ => integrable_of_abs_le (hYm i) B (hYb i)]
    have h1 : ∀ i : Fin (n + 1), ∫ S, f h (S i) ∂μ = risk f D h :=
      fun i => integral_comp_eval (hP.measurable h).aestronglyMeasurable
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- variance of W
  have hYL : ∀ i, MemLp (Y i) 2 μ := fun i =>
    MemLp.of_bound (hYm i).aestronglyMeasurable B
      (ae_of_all _ fun S => by rw [Real.norm_eq_abs]; exact hYb i S)
  have hind : iIndepFun Y μ :=
    iIndepFun_pi (X := fun _ : Fin (n + 1) => f h) (fun _ => (hP.measurable h).aemeasurable)
  have hVar : variance W μ ≤ m * B ^ 2 := by
    rw [hW, IndepFun.variance_sum (fun i _ => hYL i)
      (fun i _ j _ hij => hind.indepFun hij)]
    calc ∑ i, variance (Y i) μ ≤ ∑ _i : Fin (n + 1), B ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (variance_le_expectation_sq (hYm i).aestronglyMeasurable).trans ?_
          have := norm_integral_le_of_norm_le_const (μ := μ) (f := (Y i) ^ 2) (C := B ^ 2)
            (ae_of_all _ fun S => by
              rw [Real.norm_eq_abs, Pi.pow_apply, abs_pow]
              exact pow_le_pow_left₀ (abs_nonneg _) (hYb i S) 2)
          rw [Real.norm_eq_abs] at this
          simp only [probReal_univ, mul_one] at this
          exact (le_abs_self _).trans this
      _ = m * B ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [variance_eq_integral hWm.aemeasurable, hEW] at hVar
  -- Jensen: (E|U|)^2 ≤ E U^2
  set U : (Fin (n + 1) → Z) → ℝ := fun S => |W S - m * risk f D h| with hU
  have hUm : Measurable U := (hWm.sub_const _).abs
  have hUb : ∀ S, |U S| ≤ m * B + m * B := by
    intro S
    rw [hU, abs_abs]
    calc |W S - m * risk f D h| ≤ |W S| + |m * risk f D h| := abs_sub _ _
      _ ≤ m * B + m * B := by
          rw [abs_mul, abs_of_pos hm]
          gcongr
          · exact hWb S
          · exact abs_risk_le hP D h
  have hUL : MemLp U 2 μ := MemLp.of_bound hUm.aestronglyMeasurable (m * B + m * B)
    (ae_of_all _ fun S => by rw [Real.norm_eq_abs]; exact hUb S)
  have hvU := variance_nonneg U μ
  rw [variance_eq_sub hUL] at hvU
  have hU2 : ∫ S, (U ^ 2) S ∂μ = ∫ S, (W S - m * risk f D h) ^ 2 ∂μ := by
    congr 1
    funext S
    simp [hU, sq_abs]
  have hsq : (∫ S, U S ∂μ) ^ 2 ≤ m * B ^ 2 := by
    have : (∫ S, U S ∂μ) ^ 2 ≤ ∫ S, (U ^ 2) S ∂μ := by linarith
    linarith
  have hU0 : 0 ≤ ∫ S, U S ∂μ := integral_nonneg fun S => abs_nonneg _
  have hEU : ∫ S, U S ∂μ ≤ Real.sqrt m * B := by
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul hm.le]
    exact Real.le_sqrt_of_sq_le hsq
  -- conclude
  have hpt : ∀ S, |empRisk f S h - risk f D h| = U S / m := by
    intro S
    rw [hU]
    simp only
    rw [← abs_of_pos hm, ← abs_div, abs_of_pos hm]
    congr 1
    unfold empRisk
    rw [hWapp]
    field_simp
    rw [hmdef]
    ring
  simp_rw [hpt]
  rw [integral_div]
  have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  have hs0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  rw [div_le_div_iff₀ hm hs0]
  calc (∫ S, U S ∂μ) * Real.sqrt m ≤ Real.sqrt m * B * Real.sqrt m :=
        mul_le_mul_of_nonneg_right hEU hs0.le
    _ = B * m := by rw [mul_comm (Real.sqrt m) B, mul_assoc, hsm]

theorem main' {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D] (m m' : ℕ) (hm'₁ : 2 ≤ m') (hm'₂ : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m)
      ≤ 2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold sampleLaw
  set μ := Measure.pi fun _ : Fin (n + 1) => D
  set F := optRisk f D
  have hB : 0 ≤ B := (abs_nonneg _).trans (abs_optRisk_le hf D)
  have hm : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  -- εcons m' ≥ 0
  have hε0 : 0 ≤ εcons m' := by
    have := hcons D inferInstance m' (by omega)
    refine le_trans ?_ this
    exact integral_nonneg fun S => sub_nonneg.mpr (optRisk_le_risk hf D _)
  have hlow := lower hf herm hA hcons D (n := n) (k := m') (by omega)
  have hEi : Integrable (fun S : Fin (n + 1) → Z => ermValue f S) μ :=
    integrable_of_abs_le (herm (n + 1)) B fun S => abs_ermValue_le hf (by omega) S
  have hkey : ∀ δ > 0, ∫ S, |ermValue f S - F| ∂μ ≤
      2 * εcons m' + 2 * B / Real.sqrt (n + 1 : ℕ) + 2 * B * (m' : ℝ) ^ 2 / (n + 1 : ℕ)
        + 2 * δ := by
    intro δ hδ
    have hlt : F < F + δ := by linarith
    obtain ⟨h, hh⟩ := exists_lt_of_ciInf_lt (f := fun h => risk f D h) hlt
    have hdev := dev_le hf D hB (n := n) h
    have hpt : ∀ S : Fin (n + 1) → Z, |ermValue f S - F| ≤
        2 * |empRisk f S h - risk f D h| + 2 * δ - (ermValue f S - F) := by
      intro S
      have h1 := ermValue_le hf (by omega) S h
      have h2 := le_abs_self (empRisk f S h - risk f D h)
      rcases le_total 0 (ermValue f S - F) with hx | hx
      · rw [abs_of_nonneg hx]; linarith
      · rw [abs_of_nonpos hx]; linarith [abs_nonneg (empRisk f S h - risk f D h)]
    have hdi : Integrable (fun S : Fin (n + 1) → Z => |empRisk f S h - risk f D h|) μ := by
      refine integrable_of_abs_le ?_ (2 * B) fun S => ?_
      · refine (Measurable.sub_const ?_ _).abs
        unfold empRisk
        exact Measurable.div_const (Finset.measurable_sum _ fun i _ =>
          (hf.measurable h).comp (measurable_pi_apply i)) _
      · rw [abs_abs]
        calc |empRisk f S h - risk f D h| ≤ |empRisk f S h| + |risk f D h| := abs_sub _ _
          _ ≤ B + B := add_le_add (abs_empRisk_le hf (by omega) S h) (abs_risk_le hf D h)
          _ = 2 * B := by ring
    have hxi : Integrable (fun S : Fin (n + 1) → Z => |ermValue f S - F|) μ :=
      (hEi.sub (integrable_const _)).abs
    have hR : Integrable (fun S : Fin (n + 1) → Z =>
        2 * |empRisk f S h - risk f D h| + 2 * δ - (ermValue f S - F)) μ :=
      ((hdi.const_mul 2).add (integrable_const _)).sub (hEi.sub (integrable_const _))
    have h1 := integral_mono hxi hR hpt
    have hA1 : Integrable (fun S : Fin (n + 1) → Z =>
        2 * |empRisk f S h - risk f D h| + 2 * δ) μ := (hdi.const_mul 2).add (integrable_const _)
    have hA2 : Integrable (fun S : Fin (n + 1) → Z => ermValue f S - F) μ :=
      hEi.sub (integrable_const _)
    have hA3 : Integrable (fun S : Fin (n + 1) → Z => 2 * |empRisk f S h - risk f D h|) μ :=
      hdi.const_mul 2
    rw [integral_sub hA1 hA2, integral_add hA3 (integrable_const _), integral_const_mul,
      integral_sub hEi (integrable_const _), integral_const, integral_const] at h1
    simp only [probReal_univ, one_smul] at h1
    have h3 : 2 * B * (m' : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ 2 * B * (m' : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hm.le
      have : (1:ℝ) ≤ m' := by exact_mod_cast (show 1 ≤ m' by omega)
      have h5 : (m':ℝ) ≤ (m':ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h5 (by linarith : (0:ℝ) ≤ 2 * B)
      linarith
    have h4 : 2 * B / Real.sqrt ((n + 1 : ℕ) : ℝ) = 2 * (B / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
      ring
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := hkey (ε / 2) (by linarith)
  linarith
end LearnStability.ERMLOO.L16Proof

open MeasureTheory LearnStability.ERMLOO in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hf : StandingAssumptions f B) (herm : MeasurableERMValue f)
    (A : Rule H Z) (hA : MeasurableRule f A) (εcons : ℕ → ℝ)
    (hcons : UniversallyConsistent f A εcons)
    (D : Measure Z) [IsProbabilityMeasure D] (m m' : ℕ) (hm'₁ : 2 ≤ m') (hm'₂ : 2 * m' ≤ m) :
    ∫ S, |ermValue f S - optRisk f D| ∂(sampleLaw D m)
      ≤ 2 * εcons m' + 2 * B / Real.sqrt m + 2 * B * (m' : ℝ) ^ 2 / m := by
  exact LearnStability.ERMLOO.L16Proof.main' f B hf herm A hA εcons hcons D m m' hm'₁ hm'₂
