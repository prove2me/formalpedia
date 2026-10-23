-- Prove2me | solution 1 for InfoGen.Gibbs.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T09:18:50.784016+00:00
-- url     : https://prove2.me/submissions/ae579d10-821f-4d4b-8c46-691d0a78d447

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGenCor2Aux

open LearnStability.Characterization (sampleLaw risk empRisk)

lemma integral_mem_Icc' {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {g : α → ℝ} {a b : ℝ} (hg : AEMeasurable g ν) (h : ∀ x, g x ∈ Set.Icc a b) :
    ∫ x, g x ∂ν ∈ Set.Icc a b := by
  have hi : Integrable g ν := Integrable.of_mem_Icc a b hg (ae_of_all _ h)
  constructor
  · calc a = ∫ _x, a ∂ν := by simp
      _ ≤ ∫ x, g x ∂ν := integral_mono (integrable_const _) hi (fun x => (h x).1)
  · calc ∫ x, g x ∂ν ≤ ∫ _x, b ∂ν := integral_mono hi (integrable_const _) (fun x => (h x).2)
      _ = b := by simp

lemma meas_int_countable {S W : Type*} [MeasurableSpace S] [MeasurableSpace W] [Countable W]
    [MeasurableSingletonClass W] (Q : Measure W) [SFinite Q] {g : S → W → ℝ}
    (hg : ∀ w, Measurable fun s => g s w) : Measurable fun s => ∫ w, g s w ∂Q := by
  have hj : Measurable (fun p : S × W => g p.1 p.2) :=
    measurable_from_prod_countable_left (f := fun p : S × W => g p.1 p.2) hg
  exact (hj.stronglyMeasurable.integral_prod_right' (ν := Q)).measurable

lemma empRisk_mem {Z W : Type*} (ℓ : W → Z → ℝ) (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0:ℝ) 1)
    {n : ℕ} (hn : 0 < n) (s : Fin n → Z) (w : W) : empRisk ℓ s w ∈ Set.Icc (0:ℝ) 1 := by
  unfold empRisk
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : ∑ i, ℓ w (s i) ≤ n := by
    calc ∑ i, ℓ w (s i) ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum fun i _ => (hℓ01 w (s i)).2
      _ = n := by simp
  exact ⟨div_nonneg (Finset.sum_nonneg fun i _ => (hℓ01 w (s i)).1) hn'.le, (div_le_one hn').2 h1⟩

lemma hoeff {Z W : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : W → Z → ℝ) (hℓw : ∀ w, Measurable (ℓ w)) (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0:ℝ) 1)
    {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 < β) (w : W) :
    ∫ s, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) ∂(sampleLaw μ n) ≤
      Real.exp (β ^ 2 / (8 * n)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = β / n := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; exact div_pos hβ hn'
  have hprod : ∀ s : Fin n → Z, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) =
      ∏ i, Real.exp (t * (risk ℓ μ w - ℓ w (s i))) := by
    intro s
    rw [← Real.exp_sum]
    congr 1
    unfold empRisk
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ht]
    field_simp
  have hint : Integrable (ℓ w) μ := Integrable.of_mem_Icc 0 1 (hℓw w).aemeasurable
    (ae_of_all _ (hℓ01 w))
  have h1 : ∀ _i : Fin n, ∫ z, Real.exp (t * (risk ℓ μ w - ℓ w z)) ∂μ ≤ Real.exp (t ^ 2 / 8) := by
    intro _i
    have hc : ∫ z, (risk ℓ μ w - ℓ w z) ∂μ = 0 := by
      rw [integral_sub (integrable_const _) hint]
      simp [risk]
    have := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero
      (X := fun z => risk ℓ μ w - ℓ w z) (μ := μ) (a := risk ℓ μ w - 1) (b := risk ℓ μ w)
      (t := t) ((measurable_const.sub (hℓw w)).aemeasurable)
      (ae_of_all _ fun z => ⟨by linarith [(hℓ01 w z).2], by linarith [(hℓ01 w z).1]⟩) hc htpos
    unfold mgf at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [sub_sub_cancel]
    norm_num
    ring
  calc ∫ s, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) ∂(sampleLaw μ n)
      = ∫ s, ∏ i, Real.exp (t * (risk ℓ μ w - ℓ w (s i))) ∂(Measure.pi fun _ : Fin n => μ) := by
        unfold sampleLaw
        exact integral_congr_ae (ae_of_all _ fun s => hprod s)
    _ = ∏ i : Fin n, ∫ z, Real.exp (t * (risk ℓ μ w - ℓ w z)) ∂μ :=
        integral_fintype_prod_eq_prod (fun (_ : Fin n) z => Real.exp (t * (risk ℓ μ w - ℓ w z)))
    _ ≤ ∏ _i : Fin n, Real.exp (t ^ 2 / 8) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun z => (Real.exp_pos _).le)
          (fun i _ => h1 i)
    _ = Real.exp (β ^ 2 / (8 * n)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul, ht]
        congr 1
        field_simp

lemma marg {Z W : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ℓ : W → Z → ℝ) (hℓw : ∀ w, Measurable (ℓ w)) (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0:ℝ) 1)
    {n : ℕ} (hn : 0 < n) (w : W) :
    ∫ s, empRisk ℓ s w ∂(sampleLaw μ n) = risk ℓ μ w := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hev : ∀ i : Fin n, ∫ s, ℓ w (s i) ∂(sampleLaw μ n) = risk ℓ μ w := by
    intro i
    unfold sampleLaw risk
    have hmp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => μ) i
    have h := integral_map (μ := Measure.pi fun _ : Fin n => μ) (f := ℓ w)
      (measurable_pi_apply i).aemeasurable
      (by rw [hmp.map_eq]; exact (hℓw w).aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  have hint : ∀ i : Fin n, Integrable (fun s : Fin n → Z => ℓ w (s i)) (sampleLaw μ n) := by
    intro i
    haveI : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
    exact Integrable.of_mem_Icc 0 1 ((hℓw w).comp (measurable_pi_apply i)).aemeasurable
      (ae_of_all _ fun s => hℓ01 w (s i))
  unfold empRisk
  rw [integral_div, integral_finsetSum _ (fun i _ => hint i)]
  simp only [hev, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end InfoGenCor2Aux

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization InfoGen.Gibbs in
theorem solution {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ))
    (hℓ01 : ∀ w z, ℓ w z ∈ Set.Icc (0 : ℝ) 1)
    (Q : Measure W) [IsProbabilityMeasure Q]
    (β : ℝ) (hβ : 0 < β) (wo : W)
    (hwo : ∀ w, risk ℓ μ wo ≤ risk ℓ μ w)
    (hQ : Q {wo} ≠ 0) :
    (∫ p, risk ℓ μ p.2 ∂(sampleLaw μ n ⊗ₘ gibbsKernel ℓ Q β)) ≤
      (⨅ w, risk ℓ μ w) + 1 / β * Real.log (1 / (Q {wo}).toReal) +
        β / (2 * (n : ℝ)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hℓw : ∀ w, Measurable (ℓ w) := fun w => hℓ.comp measurable_prodMk_left
  have hP : IsProbabilityMeasure (sampleLaw μ n) := by unfold sampleLaw; infer_instance
  have hrisk : ∀ w, risk ℓ μ w ∈ Set.Icc (0:ℝ) 1 := fun w =>
    InfoGenCor2Aux.integral_mem_Icc' μ (hℓw w).aemeasurable (hℓ01 w)
  have hemp : ∀ w, Measurable fun s : Fin n → Z => empRisk ℓ s w := fun w => by
    unfold empRisk
    exact (Finset.measurable_sum _ fun i _ => (hℓw w).comp (measurable_pi_apply i)).div_const _
  have hempm := InfoGenCor2Aux.empRisk_mem ℓ hℓ01 hn
  -- abbreviations
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → Z) → W → ℝ, E = fun s w => Real.exp (-β * empRisk ℓ s w) :=
    ⟨_, rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : (Fin n → Z) → ℝ, Zs = fun s => ∫ w, E s w ∂Q := ⟨_, rfl⟩
  have hEv : ∀ s w, E s w = Real.exp (-β * empRisk ℓ s w) := fun s w => by rw [hE]
  have hZv : ∀ s, Zs s = ∫ w, E s w ∂Q := fun s => by rw [hZs]
  have hEpos : ∀ s w, 0 < E s w := fun s w => by rw [hEv]; exact Real.exp_pos _
  have hEle : ∀ s w, E s w ≤ 1 := fun s w => by
    rw [hEv, Real.exp_le_one_iff]
    have := (hempm s w).1
    nlinarith
  have hEm : ∀ w, Measurable fun s => E s w := fun w => by
    simp only [hEv]; exact ((hemp w).const_mul (-β)).exp
  have hEint : ∀ s, Integrable (E s) Q := fun s =>
    Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun w => ⟨(hEpos s w).le, hEle s w⟩)
  have hZpos : ∀ s, 0 < Zs s := fun s => by
    rw [hZv]
    have he : (fun w => E s w) = fun w => Real.exp (-β * empRisk ℓ s w) := funext (hEv s)
    have hi : Integrable (fun w => Real.exp (-β * empRisk ℓ s w)) Q := by
      rw [← he]; exact hEint s
    have h := integral_exp_pos (μ := Q) (f := fun w => -β * empRisk ℓ s w) hi
    rw [he]; exact h
  have hZm : Measurable Zs := by
    have := InfoGenCor2Aux.meas_int_countable Q hEm
    rw [hZs]; exact this
  have hfm : Measurable (Function.uncurry fun s w => ENNReal.ofReal (E s w / Zs s)) :=
    measurable_from_prod_countable_left fun w => ((hEm w).div hZm).ennreal_ofReal
  have hκ : ∀ s, gibbsKernel ℓ Q β s = Q.withDensity (fun w => ENNReal.ofReal (E s w / Zs s)) := by
    intro s
    have h := ProbabilityTheory.Kernel.withDensity_apply (ProbabilityTheory.Kernel.const (Fin n → Z) Q) hfm s
    rw [ProbabilityTheory.Kernel.const_apply] at h
    subst hE hZs
    exact h
  have hdiv_int : ∀ s, Integrable (fun w => E s w / Zs s) Q := fun s => (hEint s).div_const _
  haveI hMk : IsMarkovKernel (gibbsKernel (n := n) ℓ Q β) := ⟨fun s => ⟨by
    rw [hκ s, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hdiv_int s)
        (ae_of_all _ fun w => div_nonneg (hEpos s w).le (hZpos s).le),
      integral_div, ← hZv s, div_self (hZpos s).ne', ENNReal.ofReal_one]⟩⟩
  -- integrals against the Gibbs kernel
  have hkint : ∀ s (g : W → ℝ), ∫ w, g w ∂(gibbsKernel ℓ Q β s) =
      ∫ w, E s w / Zs s * g w ∂Q := by
    intro s g
    rw [hκ s, integral_withDensity_eq_integral_toReal_smul
      (measurable_of_countable _) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1; funext w
    rw [ENNReal.toReal_ofReal (div_nonneg (hEpos s w).le (hZpos s).le), smul_eq_mul]
  obtain ⟨A, hA⟩ : ∃ A : (Fin n → Z) → ℝ, A = fun s => ∫ w, risk ℓ μ w ∂(gibbsKernel ℓ Q β s) :=
    ⟨_, rfl⟩
  have hAv : ∀ s, A s = ∫ w, risk ℓ μ w ∂(gibbsKernel ℓ Q β s) := fun s => by rw [hA]
  have hAm : Measurable A := by
    have : A = fun s => ∫ w, E s w / Zs s * risk ℓ μ w ∂Q := by
      funext s; rw [hAv, hkint]
    rw [this]
    exact InfoGenCor2Aux.meas_int_countable Q fun w => ((hEm w).div hZm).mul_const _
  have hAmem : ∀ s, A s ∈ Set.Icc (0:ℝ) 1 := fun s => by
    rw [hAv]
    exact InfoGenCor2Aux.integral_mem_Icc' _ (measurable_of_countable _).aemeasurable hrisk
  obtain ⟨M, hM⟩ : ∃ M : (Fin n → Z) → ℝ,
      M = fun s => ∫ w, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) ∂Q := ⟨_, rfl⟩
  have hMv : ∀ s, M s = ∫ w, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) ∂Q := fun s => by
    rw [hM]
  have hMm : Measurable M := by
    rw [hM]
    exact InfoGenCor2Aux.meas_int_countable Q fun w =>
      ((measurable_const.sub (hemp w)).const_mul β).exp
  have hMmem : ∀ s, M s ∈ Set.Icc 0 (Real.exp β) := fun s => by
    rw [hMv]
    refine InfoGenCor2Aux.integral_mem_Icc' _ (measurable_of_countable _).aemeasurable ?_
    intro w
    refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
    have h1 := (hrisk w).2
    have h2 := (hempm s w).1
    nlinarith
  -- per-sample bound
  set q : ℝ := (Q {wo}).toReal with hq_def
  have hqpos : 0 < q := ENNReal.toReal_pos hQ (measure_ne_top _ _)
  have hqle : q ≤ 1 := by
    rw [hq_def]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hqpos.le hqle
  have hZge : ∀ s, q * E s wo ≤ Zs s := by
    intro s
    have h1 := setIntegral_le_integral (s := {wo}) (hEint s)
      (ae_of_all _ fun w => (hEpos s w).le)
    rw [integral_singleton, smul_eq_mul, measureReal_def] at h1
    rw [hZv]; exact h1
  have hJ1 : ∀ s, Real.exp (β * A s) ≤ M s / Zs s := by
    intro s
    have hJ := ConvexOn.map_integral_le (μ := gibbsKernel ℓ Q β s)
      (f := fun w => β * risk ℓ μ w) (g := Real.exp) (s := Set.univ) convexOn_exp
      Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
      ((Integrable.of_mem_Icc 0 1 (measurable_of_countable _).aemeasurable
        (ae_of_all _ hrisk)).const_mul β)
      (Integrable.of_mem_Icc 0 (Real.exp β) (measurable_of_countable _).aemeasurable
        (ae_of_all _ fun w => ⟨(Real.exp_pos _).le, by
          simp only [Function.comp_apply]
          exact Real.exp_le_exp.2 (by nlinarith [(hrisk w).2])⟩))
    simp only [integral_const_mul] at hJ
    rw [hAv]
    refine hJ.trans (le_of_eq ?_)
    rw [hkint, hMv, ← integral_div]
    congr 1; funext w
    rw [hEv, div_mul_eq_mul_div, ← Real.exp_add]
    congr 2; ring
  have hX : ∀ s, Real.exp (β * A s - β * empRisk ℓ s wo + Real.log q) ≤ M s := by
    intro s
    have e1 : Real.exp (β * A s - β * empRisk ℓ s wo + Real.log q) =
        Real.exp (β * A s) * (q * E s wo) := by
      rw [hEv, show β * A s - β * empRisk ℓ s wo + Real.log q =
        β * A s + (-β * empRisk ℓ s wo + Real.log q) by ring, Real.exp_add, Real.exp_add,
        Real.exp_log hqpos]
      ring
    rw [e1]
    have hM0 : 0 ≤ M s := (hMmem s).1
    calc Real.exp (β * A s) * (q * E s wo) ≤ M s / Zs s * (q * E s wo) :=
          mul_le_mul_of_nonneg_right (hJ1 s) (mul_nonneg hqpos.le (hEpos s wo).le)
      _ ≤ M s / Zs s * Zs s :=
          mul_le_mul_of_nonneg_left (hZge s) (div_nonneg hM0 (hZpos s).le)
      _ = M s := div_mul_cancel₀ _ (hZpos s).ne'
  -- Jensen over the sample
  have hXm : Measurable fun s => β * A s - β * empRisk ℓ s wo + Real.log q :=
    ((hAm.const_mul β).sub ((hemp wo).const_mul β)).add_const _
  have hXmem : ∀ s, β * A s - β * empRisk ℓ s wo + Real.log q ∈
      Set.Icc (Real.log q - β) β := fun s => by
    have h1 := hAmem s; have h2 := hempm s wo
    constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hXint : Integrable (fun s => β * A s - β * empRisk ℓ s wo + Real.log q) (sampleLaw μ n) :=
    Integrable.of_mem_Icc _ _ hXm.aemeasurable (ae_of_all _ hXmem)
  have hJ2 := ConvexOn.map_integral_le (μ := sampleLaw μ n)
    (f := fun s => β * A s - β * empRisk ℓ s wo + Real.log q) (g := Real.exp) (s := Set.univ)
    convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hXint
    (Integrable.of_mem_Icc 0 (Real.exp β) (hXm.exp).aemeasurable
      (ae_of_all _ fun s => ⟨(Real.exp_pos _).le, by
        simp only [Function.comp_apply]; exact Real.exp_le_exp.2 (hXmem s).2⟩))
  have hMint : Integrable M (sampleLaw μ n) :=
    Integrable.of_mem_Icc _ _ hMm.aemeasurable (ae_of_all _ hMmem)
  have hEM : ∫ s, M s ∂(sampleLaw μ n) ≤ Real.exp (β ^ 2 / (8 * n)) := by
    have hFm : Measurable (fun p : (Fin n → Z) × W =>
        Real.exp (β * (risk ℓ μ p.2 - empRisk ℓ p.1 p.2))) :=
      measurable_from_prod_countable_left
        (f := fun p : (Fin n → Z) × W => Real.exp (β * (risk ℓ μ p.2 - empRisk ℓ p.1 p.2)))
        fun w => by dsimp only; exact ((measurable_const.sub (hemp w)).const_mul β).exp
    have hFint : Integrable (Function.uncurry fun (s : Fin n → Z) (w : W) =>
        Real.exp (β * (risk ℓ μ w - empRisk ℓ s w))) ((sampleLaw μ n).prod Q) :=
      Integrable.of_mem_Icc 0 (Real.exp β) hFm.aemeasurable (ae_of_all _ fun p => by
        refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩
        have h1 := (hrisk p.2).2
        have h2 := (hempm p.1 p.2).1
        nlinarith)
    simp only [hMv]
    rw [integral_integral_swap hFint]
    calc ∫ w, ∫ s, Real.exp (β * (risk ℓ μ w - empRisk ℓ s w)) ∂(sampleLaw μ n) ∂Q
        ≤ ∫ _w, Real.exp (β ^ 2 / (8 * n)) ∂Q :=
          integral_mono_of_nonneg (ae_of_all _ fun w => integral_nonneg fun s => (Real.exp_pos _).le)
            (integrable_const _)
            (ae_of_all _ fun w => InfoGenCor2Aux.hoeff μ ℓ hℓw hℓ01 hn hβ w)
      _ = Real.exp (β ^ 2 / (8 * n)) := by simp
  have hfinal : β * ∫ s, A s ∂(sampleLaw μ n) - β * risk ℓ μ wo + Real.log q ≤
      β ^ 2 / (8 * n) := by
    have hAint : Integrable A (sampleLaw μ n) :=
      Integrable.of_mem_Icc 0 1 hAm.aemeasurable (ae_of_all _ hAmem)
    have hEint2 : Integrable (fun s => empRisk ℓ s wo) (sampleLaw μ n) :=
      Integrable.of_mem_Icc 0 1 (hemp wo).aemeasurable (ae_of_all _ fun s => hempm s wo)
    have hI : ∫ s, (β * A s - β * empRisk ℓ s wo + Real.log q) ∂(sampleLaw μ n) =
        β * ∫ s, A s ∂(sampleLaw μ n) - β * risk ℓ μ wo + Real.log q := by
      have hi2 : Integrable (fun s => β * A s) (sampleLaw μ n) := hAint.const_mul β
      have hi3 : Integrable (fun s => β * empRisk ℓ s wo) (sampleLaw μ n) := hEint2.const_mul β
      have hi1 : Integrable (fun s => β * A s - β * empRisk ℓ s wo) (sampleLaw μ n) :=
        hi2.sub hi3
      rw [integral_add hi1 (integrable_const _), integral_sub hi2 hi3, integral_const_mul,
        integral_const_mul, InfoGenCor2Aux.marg μ ℓ hℓw hℓ01 hn wo]
      simp
    rw [← hI, ← Real.exp_le_exp]
    refine hJ2.trans (le_trans ?_ hEM)
    exact integral_mono (Integrable.of_mem_Icc 0 (Real.exp β) (hXm.exp).aemeasurable
        (ae_of_all _ fun s => ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (hXmem s).2⟩)) hMint
        (fun s => hX s)
  -- conclude
  have hcpi : Integrable (fun p : (Fin n → Z) × W => risk ℓ μ p.2)
      (sampleLaw μ n ⊗ₘ gibbsKernel ℓ Q β) :=
    Integrable.of_mem_Icc 0 1
      (((measurable_of_countable (risk ℓ μ)).comp measurable_snd).aemeasurable)
      (ae_of_all _ fun p => hrisk p.2)
  rw [MeasureTheory.Measure.integral_compProd hcpi]
  simp only
  have hIA : ∫ a, ∫ b, risk ℓ μ b ∂(gibbsKernel ℓ Q β a) ∂(sampleLaw μ n) =
      ∫ s, A s ∂(sampleLaw μ n) := by
    congr 1; funext s; rw [hAv]
  rw [hIA]
  haveI : Nonempty W := ⟨wo⟩
  have hinf : risk ℓ μ wo ≤ ⨅ w, risk ℓ μ w := le_ciInf hwo
  have hlog : Real.log (1 / q) = - Real.log q := by rw [one_div, Real.log_inv]
  rw [hlog]
  have h8 : β / (8 * n) ≤ β / (2 * n) :=
    div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)
  have key : ∫ s, A s ∂(sampleLaw μ n) - risk ℓ μ wo + 1 / β * Real.log q ≤ β / (8 * n) := by
    have hb : β * (∫ s, A s ∂(sampleLaw μ n) - risk ℓ μ wo + 1 / β * Real.log q) ≤
        β * (β / (8 * n)) := by
      have e : β * (∫ s, A s ∂(sampleLaw μ n) - risk ℓ μ wo + 1 / β * Real.log q) =
          β * ∫ s, A s ∂(sampleLaw μ n) - β * risk ℓ μ wo + Real.log q := by
        field_simp
      have e2 : β * (β / (8 * n)) = β ^ 2 / (8 * n) := by ring
      rw [e, e2]; exact hfinal
    exact le_of_mul_le_mul_left hb hβ
  have : 1 / β * -Real.log q = -(1 / β * Real.log q) := by ring
  rw [this]
  linarith
