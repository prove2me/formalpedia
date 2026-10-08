-- Prove2me | solution 1 for ImprovedLinBandits.UCBDelta.confidence_intervals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T16:33:49.692238+00:00
-- url     : https://prove2.me/submissions/dbb5b7ed-2e45-4b61-9512-daf661e72526

/- Written by Codex. Gaussian-mixture helpers credited to Nickrobbins95,
accepted submission 85177580-d961-4a1a-9320-e4e2db2e23e0. -/
import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel


/- Gaussian-mixture and first-crossing helpers reused from Nickrobbins95's
accepted submission 85177580-d961-4a1a-9320-e4e2db2e23e0.
The source is preserved in work/ucbdelta/accepted-root-source.lean. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace UcbDeltaReuse
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


end det
end UcbDeltaReuse

set_option autoImplicit false
open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta UcbDeltaReuse
open scoped ENNReal NNReal

lemma ucbdelta_good_confidence {Ω : Type} {d : ℕ} (hd : 0 < d)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hx : 1 ≤ (d : ℝ) / δ)
    (i : Fin d) (t : ℕ) (ω : Ω) (hN : 0 < pullCount I i t ω)
    (hg : Mc I η i t ω < (d : ℝ) / δ) :
    |empMean μ η I i t ω - μ i| < confRadius d δ (pullCount I i t ω) := by
  have hNp : (0 : ℝ) < pullCount I i t ω := by exact_mod_cast hN
  have hxpos : (0 : ℝ) < (d : ℝ) / δ := lt_of_lt_of_le zero_lt_one hx
  have hS := good_sq i t ω ((d : ℝ) / δ) hxpos hg
  rw [Nj_eq] at hS
  have hc := conf_sq hd hδ hx (pullCount I i t ω) (by omega)
  have hS' : Sj I η i t ω ^ 2 <
      confRadius d δ (pullCount I i t ω) ^ 2 * (pullCount I i t ω : ℝ) ^ 2 := by
    rw [hc]
    nlinarith
  have he : (empMean μ η I i t ω - μ i) ^ 2 * (pullCount I i t ω : ℝ) ^ 2 =
      Sj I η i t ω ^ 2 := by
    rw [empMean_sub i t ω (by omega)]
    field_simp
  rw [← he] at hS'
  have hsq : (empMean μ η I i t ω - μ i) ^ 2 <
      confRadius d δ (pullCount I i t ω) ^ 2 :=
    (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hNp)).mp hS'
  have hc0 : 0 ≤ confRadius d δ (pullCount I i t ω) := Real.sqrt_nonneg _
  nlinarith [sq_abs (empMean μ η I i t ω - μ i), abs_nonneg (empMean μ η I i t ω - μ i)]

lemma ucbdelta_confidence_checked
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ (i : Fin d) (t : ℕ), 0 < pullCount I i t ω ∧
        confRadius d δ (pullCount I i t ω) < |empMean μ η I i t ω - μ i|}
      ≤ ENNReal.ofReal δ := by
  classical
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  by_cases hd : 0 < d
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hxpos : (0 : ℝ) < (d : ℝ) / δ := by positivity
    have hx : 1 ≤ (d : ℝ) / δ := (le_div_iff₀ hδ).2 (by linarith)
    have hsub : {ω | ∃ (i : Fin d) (t : ℕ), 0 < pullCount I i t ω ∧
          confRadius d δ (pullCount I i t ω) < |empMean μ η I i t ω - μ i|}
        ⊆ ⋃ j, {ω | ∃ t, (d : ℝ) / δ ≤ Mc I η j t ω} := by
      intro ω hω
      obtain ⟨i, t, hN, hb⟩ := hω
      refine Set.mem_iUnion.2 ⟨i, t, ?_⟩
      by_contra hg
      have hg' : Mc I η i t ω < (d : ℝ) / δ := lt_of_not_ge hg
      exact (not_lt_of_ge (ucbdelta_good_confidence hd μ I η hδ hx i t ω hN hg').le) hb
    calc _ ≤ P (⋃ j, {ω | ∃ t, (d : ℝ) / δ ≤ Mc I η j t ω}) := measure_mono hsub
      _ ≤ ∑ j, P {ω | ∃ t, (d : ℝ) / δ ≤ Mc I η j t ω} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin d, ENNReal.ofReal (1 / ((d : ℝ) / δ)) :=
          Finset.sum_le_sum fun j _ => arm_ville ℱ hI hη hsg j _ hxpos
      _ = ENNReal.ofReal δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          field_simp
  · have hd0 : d = 0 := by omega
    subst d
    simp


theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ (i : Fin d) (t : ℕ), 0 < pullCount I i t ω ∧
        confRadius d δ (pullCount I i t ω) < |empMean μ η I i t ω - μ i|}
      ≤ ENNReal.ofReal δ := by
  exact ucbdelta_confidence_checked ℱ μ I η hI hη hsg hδ

#print axioms solution
