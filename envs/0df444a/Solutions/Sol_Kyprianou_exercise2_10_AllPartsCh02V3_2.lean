-- Prove2me | solution 2 for Kyprianou.exercise2_10_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T23:25:06.608427+00:00
-- url     : https://prove2.me/submissions/9f9b8af7-b730-484c-ae23-d29909b625e8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Theorems.Thm_Kyprianou_poissonRandomMeasureExists

open MeasureTheory ProbabilityTheory Filter Complex Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Exercise210Helpers

/-! ### Section 0: Core definitions, independence helpers, product sum, and Lévy integral split -/

private noncomputable def innerRd {d : ℕ} (θ x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, θ i * x i

private noncomputable def normRd {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ))

private lemma normRd_sq {d : ℕ} (x : Fin d → ℝ) :
    normRd x ^ (2 : ℕ) = ∑ i : Fin d, x i ^ (2 : ℕ) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma normRd_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ normRd x :=
  Real.sqrt_nonneg _

private lemma normRd_eq_zero_iff {d : ℕ} (x : Fin d → ℝ) :
    normRd x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsq : ∑ i : Fin d, x i ^ (2 : ℕ) = 0 := by
      have := congrArg (fun r : ℝ => r ^ (2 : ℕ)) h
      simpa [normRd_sq] using this
    ext i
    have hi : x i ^ (2 : ℕ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hsq i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · rintro rfl
    simp [normRd]

private lemma measurable_innerRd {d : ℕ} (θ : Fin d → ℝ) :
    Measurable (innerRd θ) :=
  Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)

private lemma continuous_innerRd {d : ℕ} (θ : Fin d → ℝ) :
    Continuous (innerRd θ) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

private lemma measurable_normRd {d : ℕ} :
    Measurable (normRd (d := d)) :=
  Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)

private lemma abs_coord_le_normRd {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    |x i| ≤ normRd x := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))

private lemma innerRd_sq_le {d : ℕ} (θ x : Fin d → ℝ) :
    innerRd θ x ^ (2 : ℕ) ≤ (∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ)) := by
  simpa [innerRd] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) θ x

private lemma norm_one_sub_exp_I_add_I_le (u : ℝ) :
    ‖(1 : ℂ) - Complex.exp (Complex.I * (u : ℂ)) + Complex.I * (u : ℂ)‖ ≤ u ^ (2 : ℕ) / 2 := by
  have h1 : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ |t| := by
    intro t
    have hftc : Complex.exp (Complex.I * (t : ℂ)) - 1 =
        ∫ s in (0 : ℝ)..t, Complex.I * Complex.exp (Complex.I * (s : ℂ)) := by
      have hderiv : ∀ s : ℝ,
          HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
            (Complex.I * Complex.exp (Complex.I * (s : ℂ))) s := by
        intro s
        have hlin : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I s := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul Complex.I
        simpa [mul_comm] using hlin.cexp
      have hcont : Continuous (fun s : ℝ => Complex.I * Complex.exp (Complex.I * (s : ℂ))) := by
        fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
        (fun s _ => hderiv s) (hcont.intervalIntegrable 0 t)
      simpa using this.symm
    rw [hftc]
    have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) t,
        ‖Complex.I * Complex.exp (Complex.I * (s : ℂ))‖ ≤ (1 : ℝ) := by
      intro s _
      rw [norm_mul, Complex.norm_I, one_mul, mul_comm, Complex.norm_exp_ofReal_mul_I]
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa [Real.norm_eq_abs] using hint
  have hftc2 : Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ) =
      ∫ t in (0 : ℝ)..u, Complex.I * (Complex.exp (Complex.I * (t : ℂ)) - 1) := by
    have hderiv : ∀ t : ℝ,
        HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)) - 1 - Complex.I * (r : ℂ))
          (Complex.I * (Complex.exp (Complex.I * (t : ℂ)) - 1)) t := by
      intro t
      have hlin : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I
      have hexp : HasDerivAt (fun r : ℝ => Complex.exp (Complex.I * (r : ℂ)))
          (Complex.I * Complex.exp (Complex.I * (t : ℂ))) t := by
        simpa [mul_comm] using hlin.cexp
      have hsub := (hexp.sub_const 1).sub hlin
      have hrew : Complex.I * Complex.exp (Complex.I * (t : ℂ)) - Complex.I =
          Complex.I * (Complex.exp (Complex.I * (t : ℂ)) - 1) := by ring
      rwa [hrew] at hsub
    have hcont : Continuous (fun t : ℝ => Complex.I * (Complex.exp (Complex.I * (t : ℂ)) - 1)) := by
      fun_prop
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := u)
      (fun t _ => hderiv t) (hcont.intervalIntegrable 0 u)
    simpa using this.symm
  have hneg : (1 : ℂ) - Complex.exp (Complex.I * (u : ℂ)) + Complex.I * (u : ℂ) =
      -(Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)) := by ring
  rw [hneg, norm_neg, hftc2]
  have hbound2 : ∀ t : ℝ, ‖Complex.I * (Complex.exp (Complex.I * (t : ℂ)) - 1)‖ ≤ |t| := by
    intro t
    rw [norm_mul, Complex.norm_I, one_mul]
    exact h1 t
  rcases le_total 0 u with hu | hu
  · have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hu
      (Filter.Eventually.of_forall fun t _ => hbound2 t)
      (continuous_abs.intervalIntegrable (μ := volume) 0 u)
    have hcongr : ∫ t in (0 : ℝ)..u, |t| = ∫ t in (0 : ℝ)..u, t :=
      intervalIntegral.integral_congr fun t ht => abs_of_nonneg (by
        rw [Set.uIcc_of_le hu] at ht; exact ht.1)
    rw [hcongr, integral_id] at hle
    simpa using hle
  · rw [intervalIntegral.integral_symm, norm_neg]
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hu
      (Filter.Eventually.of_forall fun t _ => hbound2 t)
      (continuous_abs.intervalIntegrable (μ := volume) u 0)
    have hcongr : ∫ t in u..(0 : ℝ), |t| = ∫ t in u..(0 : ℝ), -t :=
      intervalIntegral.integral_congr fun t ht => abs_of_nonpos (by
        rw [Set.uIcc_of_le hu] at ht; exact ht.2)
    rw [hcongr, intervalIntegral.integral_neg, integral_id] at hle
    simpa [neg_div, neg_neg] using hle

/-- Bundled `ℝ^d`-valued càdlàg Lévy process with measurable marginals. -/
private structure RdLevyProcess (d : ℕ) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  X : ℝ≥0 → Ω → (Fin d → ℝ)
  measurable : ∀ t : ℝ≥0, Measurable (X t)
  cadlag : ∀ᵐ ω ∂P,
    (∀ t : ℝ≥0, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ l : Fin d → ℝ,
      Tendsto (fun s => X s ω) (nhdsWithin t (Set.Iio t)) (nhds l)
  start_zero : ∀ᵐ ω ∂P, X 0 ω = 0
  indep_increments : ∀ (s t : ℝ≥0), s ≤ t →
    ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance)
      (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (X u) inferInstance) P
  stationary_increments : ∀ (s t : ℝ≥0), s ≤ t →
    P.map (fun ω => X t ω - X s ω) = P.map (X (t - s))

/-! #### General σ-algebra independence lemmas -/

private lemma indep_sup_sup_of_indep {Ω : Type*} {m₁ n₁ m₂ n₂ : MeasurableSpace Ω}
    [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hm₁ : m₁ ≤ m0) (hn₁ : n₁ ≤ m0) (hm₂ : m₂ ≤ m0) (hn₂ : n₂ ≤ m0)
    (h1 : Indep m₁ n₁ P) (h2 : Indep m₂ n₂ P)
    (h12 : Indep (m₁ ⊔ n₁) (m₂ ⊔ n₂) P) :
    Indep (m₁ ⊔ m₂) (n₁ ⊔ n₂) P := by
  let pM : Set (Set Ω) := {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧ s = A ∩ B}
  let pN : Set (Set Ω) := {s | ∃ C D, MeasurableSet[n₁] C ∧ MeasurableSet[n₂] D ∧ s = C ∩ D}
  have hpM_pi : IsPiSystem pM := by
    rintro _ ⟨A₁, B₁, hA₁, hB₁, rfl⟩ _ ⟨A₂, B₂, hA₂, hB₂, rfl⟩ _
    exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by ext ω; simp [and_left_comm, and_assoc]⟩
  have hpN_pi : IsPiSystem pN := by
    rintro _ ⟨C₁, D₁, hC₁, hD₁, rfl⟩ _ ⟨C₂, D₂, hC₂, hD₂, rfl⟩ _
    exact ⟨C₁ ∩ C₂, D₁ ∩ D₂, hC₁.inter hC₂, hD₁.inter hD₂, by ext ω; simp [and_left_comm, and_assoc]⟩
  have hgenM : m₁ ⊔ m₂ = MeasurableSpace.generateFrom pM := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro s hs
        exact MeasurableSpace.measurableSet_generateFrom ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
      · intro s hs
        exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, s, MeasurableSet.univ, hs, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, B, hA, hB, rfl⟩
      exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) A hA).inter ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) B hB)
  have hgenN : n₁ ⊔ n₂ = MeasurableSpace.generateFrom pN := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro s hs
        exact MeasurableSpace.measurableSet_generateFrom ⟨s, Set.univ, hs, MeasurableSet.univ, by simp⟩
      · intro s hs
        exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, s, MeasurableSet.univ, hs, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨C, D, hC, hD, rfl⟩
      exact ((le_sup_left : n₁ ≤ n₁ ⊔ n₂) C hC).inter ((le_sup_right : n₂ ≤ n₁ ⊔ n₂) D hD)
  refine @IndepSets.indep Ω (m₁ ⊔ m₂) (n₁ ⊔ n₂) m0 P _ pM pN
    (sup_le hm₁ hm₂) (sup_le hn₁ hn₂) hpM_pi hpN_pi hgenM hgenN ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨A, B, hA, hB, rfl⟩ ⟨C, D, hC, hD, rfl⟩
  have hAC : MeasurableSet[m₁ ⊔ n₁] (A ∩ C) :=
    ((le_sup_left : m₁ ≤ m₁ ⊔ n₁) A hA).inter ((le_sup_right : n₁ ≤ m₁ ⊔ n₁) C hC)
  have hBD : MeasurableSet[m₂ ⊔ n₂] (B ∩ D) :=
    ((le_sup_left : m₂ ≤ m₂ ⊔ n₂) B hB).inter ((le_sup_right : n₂ ≤ m₂ ⊔ n₂) D hD)
  have hA' : MeasurableSet[m₁ ⊔ n₁] A := (le_sup_left : m₁ ≤ m₁ ⊔ n₁) A hA
  have hB' : MeasurableSet[m₂ ⊔ n₂] B := (le_sup_left : m₂ ≤ m₂ ⊔ n₂) B hB
  have hC' : MeasurableSet[m₁ ⊔ n₁] C := (le_sup_right : n₁ ≤ m₁ ⊔ n₁) C hC
  have hD' : MeasurableSet[m₂ ⊔ n₂] D := (le_sup_right : n₂ ≤ m₂ ⊔ n₂) D hD
  have hset : (A ∩ B) ∩ (C ∩ D) = (A ∩ C) ∩ (B ∩ D) := by ext ω; simp [and_left_comm, and_assoc]
  rw [ProbabilityTheory.Indep_iff] at h1 h2 h12
  rw [hset, h12 (A ∩ C) (B ∩ D) hAC hBD, h1 A C hA hC, h2 B D hB hD,
    h12 A B hA' hB', h12 C D hC' hD']
  ring

private lemma indep_prod_fst_snd {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    Indep (MeasurableSpace.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁) inferInstance)
      (MeasurableSpace.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂) inferInstance) (P₁.prod P₂) := by
  rw [ProbabilityTheory.Indep_iff]
  rintro _ _ ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩
  have h1 : Prod.fst ⁻¹' s₁ = s₁ ×ˢ (Set.univ : Set Ω₂) := by ext ⟨a, b⟩; simp
  have h2 : Prod.snd ⁻¹' s₂ = (Set.univ : Set Ω₁) ×ˢ s₂ := by ext ⟨a, b⟩; simp
  have h12 : (Prod.fst ⁻¹' s₁) ∩ (Prod.snd ⁻¹' s₂) = s₁ ×ˢ s₂ := by ext ⟨a, b⟩; simp
  rw [h12, h1, h2, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

private lemma indep_comap_of_map {Ω₁ Ω₂ : Type*} {m n : MeasurableSpace Ω₂}
    [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {f : Ω₁ → Ω₂} (hf : Measurable f)
    (hmap : P₁.map f = P₂)
    (hm : m ≤ mΩ₂) (hn : n ≤ mΩ₂) (h : Indep m n P₂) :
    Indep (m.comap f) (n.comap f) P₁ := by
  rw [ProbabilityTheory.Indep_iff] at h ⊢
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  rw [← Set.preimage_inter, ← Measure.map_apply hf ((hm A hA).inter (hn B hB)),
    ← Measure.map_apply hf (hm A hA), ← Measure.map_apply hf (hn B hB), hmap]
  exact h A B hA hB

private lemma indep_past_of_finset {E : Type*} [MeasurableSpace E] {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → E} (hXmeas : ∀ t, Measurable (X t))
    {s : ℝ≥0} {Y : Ω → E} (hYmeas : Measurable Y)
    (hfin : ∀ (p : ℕ) (u : Fin p → ℝ≥0), (∀ j, u j ≤ s) →
      IndepFun Y (fun ω (j : Fin p) => X (u j) ω) P) :
    Indep (MeasurableSpace.comap Y inferInstance)
      (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (X u) inferInstance) P := by
  let pY : Set (Set Ω) := {S | ∃ A : Set E, MeasurableSet A ∧ S = Y ⁻¹' A}
  let pPast : Set (Set Ω) :=
    {S | ∃ (F : Finset ℝ≥0) (_ : ∀ u ∈ F, u ≤ s) (B : ℝ≥0 → Set E),
      (∀ u ∈ F, MeasurableSet (B u)) ∧ S = ⋂ u ∈ F, X u ⁻¹' B u}
  have hpY_pi : IsPiSystem pY := by
    rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩ _
    exact ⟨A₁ ∩ A₂, hA₁.inter hA₂, rfl⟩
  have hpPast_pi : IsPiSystem pPast := by
    classical
    rintro _ ⟨F₁, hF₁, B₁, hB₁, rfl⟩ _ ⟨F₂, hF₂, B₂, hB₂, rfl⟩ _
    have hB_inter : ∀ u ∈ F₁ ∪ F₂,
        MeasurableSet ((if u ∈ F₁ then B₁ u else Set.univ) ∩ (if u ∈ F₂ then B₂ u else Set.univ)) := by
      intro u _
      refine MeasurableSet.inter ?_ ?_
      · by_cases h1 : u ∈ F₁
        · rw [if_pos h1]; exact hB₁ u h1
        · rw [if_neg h1]; exact MeasurableSet.univ
      · by_cases h2 : u ∈ F₂
        · rw [if_pos h2]; exact hB₂ u h2
        · rw [if_neg h2]; exact MeasurableSet.univ
    refine ⟨F₁ ∪ F₂, fun u hu => (Finset.mem_union.mp hu).elim (hF₁ u) (hF₂ u),
      fun u => (if u ∈ F₁ then B₁ u else Set.univ) ∩ (if u ∈ F₂ then B₂ u else Set.univ),
      hB_inter, ?_⟩
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩ u _
      refine ⟨?_, ?_⟩
      · by_cases hu1 : u ∈ F₁
        · simpa [hu1] using h1 u hu1
        · simp [hu1]
      · by_cases hu2 : u ∈ F₂
        · simpa [hu2] using h2 u hu2
        · simp [hu2]
    · intro h
      refine ⟨fun u hu1 => ?_, fun u hu2 => ?_⟩
      · simpa [hu1] using (h u (Finset.mem_union_left F₂ hu1)).1
      · simpa [hu2] using (h u (Finset.mem_union_right F₁ hu2)).2
  have hgenY : MeasurableSpace.comap Y inferInstance = MeasurableSpace.generateFrom pY := by
    apply le_antisymm
    · rintro _ ⟨A, hA, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom ⟨A, hA, rfl⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, hA, rfl⟩
      exact ⟨A, hA, rfl⟩
  let mPast : MeasurableSpace Ω := ⨆ u ∈ Set.Iic s, MeasurableSpace.comap (X u) inferInstance
  have hgenPast : mPast = MeasurableSpace.generateFrom pPast := by
    apply le_antisymm
    · refine iSup₂_le fun u hu => ?_
      rintro _ ⟨B, hB, rfl⟩
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨{u}, fun v hv => by rw [Finset.mem_singleton.mp hv]; exact hu,
         fun _ => B, fun _ _ => hB, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨F, hF, B, hB, rfl⟩
      refine @MeasurableSet.biInter _ _ mPast _ (F : Set ℝ≥0) (Finset.countable_toSet F) fun u hu => ?_
      have hle_u : MeasurableSpace.comap (X u) inferInstance ≤ mPast :=
        le_iSup₂_of_le u (hF u hu) le_rfl
      exact hle_u (X u ⁻¹' B u) ⟨B u, hB u hu, rfl⟩
  have hmPast_le : mPast ≤ mΩ := iSup₂_le fun u _ => (hXmeas u).comap_le
  refine @IndepSets.indep Ω _ mPast mΩ P _ pY pPast hYmeas.comap_le hmPast_le hpY_pi hpPast_pi hgenY hgenPast ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨A, hA, rfl⟩ ⟨F, hF, B, hB, rfl⟩
  let e : Fin F.card ≃ F := (Fintype.equivFinOfCardEq (Fintype.card_coe F)).symm
  let u : Fin F.card → ℝ≥0 := fun j => (e j).1
  have hu : ∀ j, u j ≤ s := fun j => hF (e j).1 (e j).2
  have hind := hfin F.card u hu
  let C : Set (Fin F.card → E) := Set.univ.pi (fun j => B (u j))
  have hC : MeasurableSet C := MeasurableSet.univ_pi fun j => hB (u j) (e j).2
  have hpre : (⋂ v ∈ F, X v ⁻¹' B v) = (fun ω (j : Fin F.card) => X (u j) ω) ⁻¹' C := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, C, Set.mem_univ_pi]
    constructor
    · intro h j; exact h (e j).1 (e j).2
    · intro h v hv
      have := h (e.symm ⟨v, hv⟩)
      simpa [u] using this
  rw [hpre]
  exact hind.measure_inter_preimage_eq_mul A C hA hC

/-! #### Product-space sum of two independent `ℝ^d`-valued càdlàg Lévy processes -/

private noncomputable def sum_two_indep_rdLevy {d : ℕ}
    {Ω₁ Ω₂ : Type} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (L₁ : RdLevyProcess d Ω₁ P₁) (L₂ : RdLevyProcess d Ω₂ P₂) :
    RdLevyProcess d (Ω₁ × Ω₂) (P₁.prod P₂) where
  X := fun t ω => L₁.X t ω.1 + L₂.X t ω.2
  measurable := fun t =>
    ((L₁.measurable t).comp measurable_fst).add ((L₂.measurable t).comp measurable_snd)
  cadlag := by
    have h1 := Measure.quasiMeasurePreserving_fst (μ := P₁) (ν := P₂) |>.ae L₁.cadlag
    have h2 := Measure.quasiMeasurePreserving_snd (μ := P₁) (ν := P₂) |>.ae L₂.cadlag
    filter_upwards [h1, h2] with ω ⟨h1r, h1l⟩ ⟨h2r, h2l⟩
    refine ⟨fun t => (h1r t).add (h2r t), fun t ht => ?_⟩
    obtain ⟨l₁, hl₁⟩ := h1l t ht
    obtain ⟨l₂, hl₂⟩ := h2l t ht
    exact ⟨l₁ + l₂, hl₁.add hl₂⟩
  start_zero := by
    have h1 := Measure.quasiMeasurePreserving_fst (μ := P₁) (ν := P₂) |>.ae L₁.start_zero
    have h2 := Measure.quasiMeasurePreserving_snd (μ := P₁) (ν := P₂) |>.ae L₂.start_zero
    filter_upwards [h1, h2] with ω h1 h2
    simp [h1, h2]
  indep_increments := by
    intro s t hst
    have hmap_fst : (P₁.prod P₂).map Prod.fst = P₁ := by simp [Measure.map_fst_prod]
    have hmap_snd : (P₁.prod P₂).map Prod.snd = P₂ := by simp [Measure.map_snd_prod]
    have h1 := indep_comap_of_map measurable_fst hmap_fst
      ((L₁.measurable t).sub (L₁.measurable s)).comap_le
      (iSup₂_le fun u _ => (L₁.measurable u).comap_le)
      (L₁.indep_increments s t hst)
    have h2 := indep_comap_of_map measurable_snd hmap_snd
      ((L₂.measurable t).sub (L₂.measurable s)).comap_le
      (iSup₂_le fun u _ => (L₂.measurable u).comap_le)
      (L₂.indep_increments s t hst)
    have hm₁_le_fst :
        (MeasurableSpace.comap (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) inferInstance).comap Prod.fst ≤
        MeasurableSpace.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁) mΩ₁ :=
      MeasurableSpace.comap_mono ((L₁.measurable t).sub (L₁.measurable s)).comap_le
    have hn₁_le_fst :
        (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (L₁.X u) inferInstance).comap Prod.fst ≤
        MeasurableSpace.comap (Prod.fst : Ω₁ × Ω₂ → Ω₁) mΩ₁ :=
      MeasurableSpace.comap_mono (iSup₂_le fun u _ => (L₁.measurable u).comap_le)
    have hm₂_le_snd :
        (MeasurableSpace.comap (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) inferInstance).comap Prod.snd ≤
        MeasurableSpace.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂) mΩ₂ :=
      MeasurableSpace.comap_mono ((L₂.measurable t).sub (L₂.measurable s)).comap_le
    have hn₂_le_snd :
        (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (L₂.X u) inferInstance).comap Prod.snd ≤
        MeasurableSpace.comap (Prod.snd : Ω₁ × Ω₂ → Ω₂) mΩ₂ :=
      MeasurableSpace.comap_mono (iSup₂_le fun u _ => (L₂.measurable u).comap_le)
    have h12 := indep_of_indep_of_le_left
      (indep_of_indep_of_le_right (indep_prod_fst_snd P₁ P₂) (sup_le hm₂_le_snd hn₂_le_snd))
      (sup_le hm₁_le_fst hn₁_le_fst)
    have hsup := indep_sup_sup_of_indep
      (hm₁_le_fst.trans measurable_fst.comap_le)
      (hn₁_le_fst.trans measurable_fst.comap_le)
      (hm₂_le_snd.trans measurable_snd.comap_le)
      (hn₂_le_snd.trans measurable_snd.comap_le)
      h1 h2 h12
    refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hsup ?_) ?_
    · refine iSup₂_le fun u hu => ?_
      have hle1 : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₁.X u ω.1) inferInstance ≤
          (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₁.X v) inferInstance).comap Prod.fst ⊔
          (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₂.X v) inferInstance).comap Prod.snd := by
        calc MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₁.X u ω.1) inferInstance
            = (MeasurableSpace.comap (L₁.X u) inferInstance).comap Prod.fst :=
                (MeasurableSpace.comap_comp).symm
          _ ≤ (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₁.X v) inferInstance).comap Prod.fst :=
                MeasurableSpace.comap_mono (le_iSup₂_of_le u hu le_rfl)
          _ ≤ _ := le_sup_left
      have hle2 : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₂.X u ω.2) inferInstance ≤
          (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₁.X v) inferInstance).comap Prod.fst ⊔
          (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₂.X v) inferInstance).comap Prod.snd := by
        calc MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₂.X u ω.2) inferInstance
            = (MeasurableSpace.comap (L₂.X u) inferInstance).comap Prod.snd :=
                (MeasurableSpace.comap_comp).symm
          _ ≤ (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (L₂.X v) inferInstance).comap Prod.snd :=
                MeasurableSpace.comap_mono (le_iSup₂_of_le u hu le_rfl)
          _ ≤ _ := le_sup_right
      exact (@Measurable.add _ _ _ _ _ _ _ _ (Measurable.of_comap_le hle1) (Measurable.of_comap_le hle2)).comap_le
    · have heq : (fun ω : Ω₁ × Ω₂ => (L₁.X t ω.1 + L₂.X t ω.2) - (L₁.X s ω.1 + L₂.X s ω.2)) =
          fun ω => (L₁.X t ω.1 - L₁.X s ω.1) + (L₂.X t ω.2 - L₂.X s ω.2) := by
        funext ω; ext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [heq]
      have hle1 : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₁.X t ω.1 - L₁.X s ω.1) inferInstance ≤
          (MeasurableSpace.comap (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) inferInstance).comap Prod.fst ⊔
          (MeasurableSpace.comap (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) inferInstance).comap Prod.snd := by
        have hc : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₁.X t ω.1 - L₁.X s ω.1) inferInstance =
            (MeasurableSpace.comap (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) inferInstance).comap Prod.fst := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hc]; exact le_sup_left
      have hle2 : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₂.X t ω.2 - L₂.X s ω.2) inferInstance ≤
          (MeasurableSpace.comap (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) inferInstance).comap Prod.fst ⊔
          (MeasurableSpace.comap (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) inferInstance).comap Prod.snd := by
        have hc : MeasurableSpace.comap (fun ω : Ω₁ × Ω₂ => L₂.X t ω.2 - L₂.X s ω.2) inferInstance =
            (MeasurableSpace.comap (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) inferInstance).comap Prod.snd := by
          rw [MeasurableSpace.comap_comp]; rfl
        rw [hc]; exact le_sup_right
      exact (@Measurable.add _ _ _ _ _ _ _ _ (Measurable.of_comap_le hle1) (Measurable.of_comap_le hle2)).comap_le
  stationary_increments := by
    intro s t hst
    have heq : (fun ω : Ω₁ × Ω₂ => (L₁.X t ω.1 + L₂.X t ω.2) - (L₁.X s ω.1 + L₂.X s ω.2)) =
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) ∘
        Prod.map (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) := by
      funext ⟨ω₁, ω₂⟩; ext i; simp only [Function.comp_apply, Prod.map_apply, Pi.add_apply, Pi.sub_apply]; ring
    have heq2 : (fun ω : Ω₁ × Ω₂ => L₁.X (t - s) ω.1 + L₂.X (t - s) ω.2) =
        (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) ∘
        Prod.map (L₁.X (t - s)) (L₂.X (t - s)) := rfl
    have hadd_m : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.1 + p.2) :=
      measurable_fst.add measurable_snd
    have hm1 : Measurable (fun ω₁ => L₁.X t ω₁ - L₁.X s ω₁) := (L₁.measurable t).sub (L₁.measurable s)
    have hm2 : Measurable (fun ω₂ => L₂.X t ω₂ - L₂.X s ω₂) := (L₂.measurable t).sub (L₂.measurable s)
    rw [heq, heq2,
      ← Measure.map_map hadd_m (hm1.prodMap hm2),
      ← Measure.map_map hadd_m ((L₁.measurable (t - s)).prodMap (L₂.measurable (t - s))),
      ← Measure.map_prod_map P₁ P₂ hm1 hm2,
      ← Measure.map_prod_map P₁ P₂ (L₁.measurable (t - s)) (L₂.measurable (t - s)),
      L₁.stationary_increments s t hst, L₂.stationary_increments s t hst]

private lemma sum_two_indep_rdLevy_charFun {d : ℕ}
    {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (L₁ : RdLevyProcess d Ω₁ P₁) (L₂ : RdLevyProcess d Ω₂ P₂)
    (t : ℝ≥0) (θ : Fin d → ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((innerRd θ ((sum_two_indep_rdLevy L₁ L₂).X t ω) : ℝ) : ℂ)) ∂(P₁.prod P₂) =
      (∫ ω₁, Complex.exp (Complex.I * ((innerRd θ (L₁.X t ω₁) : ℝ) : ℂ)) ∂P₁) *
      (∫ ω₂, Complex.exp (Complex.I * ((innerRd θ (L₂.X t ω₂) : ℝ) : ℂ)) ∂P₂) := by
  have hsplit : ∀ ω : Ω₁ × Ω₂,
      Complex.exp (Complex.I * ((innerRd θ ((sum_two_indep_rdLevy L₁ L₂).X t ω) : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((innerRd θ (L₁.X t ω.1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((innerRd θ (L₂.X t ω.2) : ℝ) : ℂ)) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    have hlin : innerRd θ (L₁.X t ω.1 + L₂.X t ω.2) =
        innerRd θ (L₁.X t ω.1) + innerRd θ (L₂.X t ω.2) := by
      simp [innerRd, mul_add, Finset.sum_add_distrib]
    change Complex.I * ((innerRd θ (L₁.X t ω.1 + L₂.X t ω.2) : ℝ) : ℂ) = _
    rw [hlin]
    push_cast
    ring
  simp_rw [hsplit]
  have hint : Integrable (fun ω : Ω₁ × Ω₂ =>
      Complex.exp (Complex.I * ((innerRd θ (L₁.X t ω.1) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((innerRd θ (L₂.X t ω.2) : ℝ) : ℂ))) (P₁.prod P₂) := by
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        ((measurable_innerRd θ).comp ((L₁.measurable t).comp measurable_fst))).mul
        ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        ((measurable_innerRd θ).comp ((L₂.measurable t).comp measurable_snd)))
        |>.aestronglyMeasurable
    · rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I,
        mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [MeasureTheory.integral_prod _ hint]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_mul_const]

/-! #### Lévy measure finiteness, `L²` integrability on `{‖x‖ < 1}`, and integral split -/

private lemma levyMeasure_tail_lt_top {d : ℕ}
    (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ν {x : Fin d → ℝ | ε ≤ normRd x} < ⊤ := by
  let c : ℝ≥0∞ := ENNReal.ofReal (min 1 (ε ^ (2 : ℕ)))
  let f : (Fin d → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ)))
  have hc_pos : 0 < c := ENNReal.ofReal_pos.mpr (lt_min one_pos (sq_pos_of_pos hε))
  have hf_meas : Measurable f :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.min (measurable_normRd.pow_const 2))
  have hsub : {x : Fin d → ℝ | ε ≤ normRd x} ⊆ {x : Fin d → ℝ | c ≤ f x} := fun x hx =>
    ENNReal.ofReal_le_ofReal (min_le_min le_rfl (pow_le_pow_left₀ hε.le hx 2))
  have hle : c * ν {x : Fin d → ℝ | ε ≤ normRd x} ≤ ∫⁻ x, f x ∂ν :=
    le_trans (mul_le_mul_right (measure_mono hsub) c)
      (mul_meas_ge_le_lintegral hf_meas c (μ := ν))
  exact ENNReal.lt_top_of_mul_ne_top_right
    (ne_top_of_le_ne_top hLevy.ne hle) hc_pos.ne'

private lemma levyMeasure_integrableOn_sq_small {d : ℕ}
    (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    IntegrableOn (fun x : Fin d → ℝ => ∑ i : Fin d, x i ^ (2 : ℕ))
      {x : Fin d → ℝ | normRd x < 1} ν := by
  have hmeas : AEStronglyMeasurable (fun x : Fin d → ℝ => ∑ i : Fin d, x i ^ (2 : ℕ))
      (ν.restrict {x : Fin d → ℝ | normRd x < 1}) :=
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral]
  have hBmeas : MeasurableSet {x : Fin d → ℝ | normRd x < 1} :=
    measurableSet_lt measurable_normRd measurable_const
  calc ∫⁻ x in {x : Fin d → ℝ | normRd x < 1}, ‖∑ i : Fin d, x i ^ (2 : ℕ)‖ₑ ∂ν
      = ∫⁻ x in {x : Fin d → ℝ | normRd x < 1},
          ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν := by
        refine setLIntegral_congr_fun hBmeas fun x hx => ?_
        have hnn : 0 ≤ ∑ i : Fin d, x i ^ (2 : ℕ) := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hsq : Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ) = ∑ i : Fin d, x i ^ (2 : ℕ) :=
          Real.sq_sqrt hnn
        have hlt1 : ∑ i : Fin d, x i ^ (2 : ℕ) ≤ 1 := by
          rw [← hsq]
          have : normRd x < 1 := hx
          have := pow_le_pow_left₀ (normRd_nonneg x) this.le 2
          simpa [normRd] using this
        rw [Real.enorm_eq_ofReal hnn, hsq, min_eq_right hlt1]
    _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν :=
        setLIntegral_le_lintegral _ _
    _ < ⊤ := hLevy

private lemma levy_integral_split {d : ℕ}
    (ν : Measure (Fin d → ℝ))
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤)
    (θ : Fin d → ℝ) :
    (∫ x, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
      Complex.I * ((innerRd θ x : ℝ) : ℂ) * (if normRd x < 1 then 1 else 0)) ∂ν) =
    (∫ x in {x : Fin d → ℝ | 1 ≤ normRd x},
      (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) ∂ν) +
    (∫ x in {x : Fin d → ℝ | normRd x < 1},
      (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
        Complex.I * ((innerRd θ x : ℝ) : ℂ)) ∂ν) := by
  let B_large : Set (Fin d → ℝ) := {x | 1 ≤ normRd x}
  let B_small : Set (Fin d → ℝ) := {x | normRd x < 1}
  let f : (Fin d → ℝ) → ℂ := fun x =>
    1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
      Complex.I * ((innerRd θ x : ℝ) : ℂ) * (if normRd x < 1 then 1 else 0)
  have hBl : MeasurableSet B_large := measurableSet_le measurable_const measurable_normRd
  have hBs : MeasurableSet B_small := measurableSet_lt measurable_normRd measurable_const
  have hdisj : Disjoint B_large B_small :=
    Set.disjoint_left.mpr fun x h1 h2 => not_lt.mpr (show 1 ≤ normRd x from h1) h2
  have hunion : B_large ∪ B_small = Set.univ := by
    ext x; simp [B_large, B_small]; exact le_or_gt 1 (normRd x)
  have hf_meas : Measurable f := by
    have h1 : Measurable (fun x : Fin d → ℝ =>
        (1 : ℂ) - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) :=
      measurable_const.sub ((Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp (measurable_innerRd θ))
    have h2 : Measurable (fun x : Fin d → ℝ =>
        Complex.I * ((innerRd θ x : ℝ) : ℂ) * (if normRd x < 1 then (1 : ℂ) else 0)) :=
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp (measurable_innerRd θ))).mul
        (Measurable.ite hBs measurable_const measurable_const)
    exact h1.add h2
  have hint_large : IntegrableOn f B_large ν := by
    have hfin : ν B_large < ⊤ := levyMeasure_tail_lt_top ν hLevy one_pos
    haveI : IsFiniteMeasure (ν.restrict B_large) := isFiniteMeasure_restrict.mpr hfin.ne
    refine Integrable.of_bound hf_meas.aestronglyMeasurable 2 ?_
    filter_upwards [ae_restrict_mem hBl] with x hx
    have hnot : ¬ normRd x < 1 := not_lt.mpr hx
    simp only [f, if_neg hnot, mul_zero, add_zero]
    calc ‖(1 : ℂ) - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]; norm_num
  have hint_small : IntegrableOn f B_small ν := by
    have hsq := levyMeasure_integrableOn_sq_small ν hLevy
    let C : ℝ := (∑ i : Fin d, θ i ^ (2 : ℕ)) / 2
    refine Integrable.mono' (hsq.const_mul C) hf_meas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hBs] with x hx
    have hlt : normRd x < 1 := hx
    simp only [f, if_pos hlt, mul_one]
    calc ‖(1 : ℂ) - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
            Complex.I * ((innerRd θ x : ℝ) : ℂ)‖
        ≤ innerRd θ x ^ (2 : ℕ) / 2 := norm_one_sub_exp_I_add_I_le (innerRd θ x)
      _ ≤ ((∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ))) / 2 :=
          div_le_div_of_nonneg_right (innerRd_sq_le θ x) (by norm_num)
      _ = C * (∑ i : Fin d, x i ^ (2 : ℕ)) := by dsimp [C]; ring
  calc ∫ x, f x ∂ν
      = ∫ x in (B_large ∪ B_small), f x ∂ν := by rw [hunion, Measure.restrict_univ]
    _ = (∫ x in B_large, f x ∂ν) + (∫ x in B_small, f x ∂ν) :=
        setIntegral_union hdisj hBs hint_large hint_small
    _ = (∫ x in B_large, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) ∂ν) +
        (∫ x in B_small, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
          Complex.I * ((innerRd θ x : ℝ) : ℂ)) ∂ν) := by
        congr 1
        · refine setIntegral_congr_fun hBl fun x hx => ?_
          have hnot : ¬ normRd x < 1 := not_lt.mpr hx
          simp [f, hnot]
        · refine setIntegral_congr_fun hBs fun x hx => ?_
          have hlt : normRd x < 1 := hx
          simp [f, hlt]

/-! ### Section 1: Part 1 — `d`-dimensional Gaussian-with-drift Lévy process -/

private lemma exists_sqrt_of_symm_psd {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ, 0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j) :
    ∃ S : Matrix (Fin d) (Fin d) ℝ,
      ∀ i k : Fin d, ∑ j : Fin d, S i j * S k j = A i k := by
  have hAherm : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hAsymm
  have hApsd : A.PosSemidef := by
    refine ⟨hAherm, fun v => ?_⟩
    have hdot : (v.sum fun i xi => v.sum fun j xj => star xi * A i j * xj) =
        ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j := by
      simp only [star_trivial]
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    rw [hdot]
    exact hApos v
  let U : Matrix (Fin d) (Fin d) ℝ := hAherm.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun k => Real.sqrt (hAherm.eigenvalues k))
  let S : Matrix (Fin d) (Fin d) ℝ := U * D
  refine ⟨S, fun i k => ?_⟩
  have hspec : A = U * Matrix.diagonal hAherm.eigenvalues * U.transpose := by
    have h := hAherm.spectral_theorem
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hDD : D * D.transpose = Matrix.diagonal hAherm.eigenvalues := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext m
    exact Real.mul_self_sqrt (hApsd.eigenvalues_nonneg m)
  have hSS : S * S.transpose = A := by
    calc S * S.transpose
        = U * D * (D.transpose * U.transpose) := by
          dsimp [S]; rw [Matrix.transpose_mul]
      _ = U * (D * D.transpose) * U.transpose := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal hAherm.eigenvalues * U.transpose := by rw [hDD]
      _ = A := hspec.symm
  have hentry := congrFun (congrFun hSS i) k
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using hentry

private lemma exists_std_brownian_1d :
    ∃ B : LevyStochCalc.Brownian.BrownianMotion ProbabilityTheory.gaussianLimit,
      (∀ ω, Continuous (fun t => B.W t ω)) ∧ (∀ ω, B.W 0 ω = 0) := by
  classical
  have hmod := ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification
  let Y := hmod.choose
  have hYmeas : ∀ t, Measurable (Y t) := hmod.choose_spec.1
  have hYae : ∀ t, Y t =ᵐ[ProbabilityTheory.gaussianLimit] ProbabilityTheory.preBrownian t :=
    hmod.choose_spec.2.1
  have hYholder := hmod.choose_spec.2.2
  have hYpre : ProbabilityTheory.IsPreBrownianReal Y ProbabilityTheory.gaussianLimit :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.congr (fun t => (hYae t).symm)
  have hYcont : ∀ ω, Continuous (fun t => Y t ω) := by
    intro ω
    rw [continuous_iff_continuousAt]
    intro t
    have hβ_pos : (0 : ℝ≥0) < (1 / 4 : ℝ≥0) := by norm_num
    have hbdd : BddAbove (Set.range (fun n : ℕ => (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)))) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨n, rfl⟩
      have hpos : (0 : ℝ) < 2 * ((n + 2 : ℕ) : ℝ) := by positivity
      rw [div_le_iff₀ hpos]
      push_cast
      linarith
    have hβ_lt : ((1 / 4 : ℝ≥0) : ℝ) <
        ⨆ n : ℕ, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) := by
      have h1 : ((1 / 4 : ℝ≥0) : ℝ) < (((1 + 2 : ℕ) : ℝ) - 1) / (2 * (1 + 2 : ℕ)) := by
        norm_num
      exact lt_of_lt_of_le h1 (le_ciSup hbdd 1)
    rcases hYholder ω t (1 / 4 : ℝ≥0) hβ_pos hβ_lt with ⟨U, hU, C, hHolder⟩
    exact (hHolder.continuousOn hβ_pos).continuousAt hU
  exact ⟨LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal hYpre hYmeas hYcont,
    fun ω => LevyStochCalc.Brownian.continuous_realTime hYcont ω,
    fun ω => by simp [LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal,
      LevyStochCalc.Brownian.realTime]⟩

private noncomputable def deterministic_drift_rdLevy {d : ℕ} (a : Fin d → ℝ) :
    RdLevyProcess d Unit (Measure.dirac ()) where
  X := fun t _ i => -(a i * (t : ℝ))
  measurable := fun _ => measurable_const
  cadlag := Filter.Eventually.of_forall fun _ => by
    have hcont : Continuous (fun s : ℝ≥0 => fun i : Fin d => -(a i * (s : ℝ))) :=
      continuous_pi fun i => (continuous_const.mul NNReal.continuous_coe).neg
    exact ⟨fun t => hcont.continuousAt.continuousWithinAt,
      fun t _ => ⟨fun i => -(a i * (t : ℝ)), hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
  start_zero := Filter.Eventually.of_forall fun _ => by ext i; simp
  indep_increments := by
    intro s t _
    have hbot : MeasurableSpace.comap
        (fun _ : Unit => (fun i : Fin d => -(a i * (t : ℝ))) - (fun i : Fin d => -(a i * (s : ℝ))))
        inferInstance = ⊥ := by
      rw [MeasurableSpace.comap_const]
    rw [hbot]
    exact indep_bot_left _
  stationary_increments := by
    intro s t hst
    have heq : (fun _ : Unit => (fun i : Fin d => -(a i * (t : ℝ))) - (fun i : Fin d => -(a i * (s : ℝ)))) =
        fun _ : Unit => fun i : Fin d => -(a i * ((t - s : ℝ≥0) : ℝ)) := by
      funext _; ext i
      simp only [Pi.sub_apply, NNReal.coe_sub hst]
      ring
    rw [heq]

private noncomputable def scaled_bm_rdLevy {d : ℕ} (v : Fin d → ℝ)
    (B : LevyStochCalc.Brownian.BrownianMotion ProbabilityTheory.gaussianLimit)
    (hBcont : ∀ ω, Continuous (fun t => B.W t ω))
    (hB0 : ∀ ω, B.W 0 ω = 0) :
    RdLevyProcess d (ℝ≥0 → ℝ) ProbabilityTheory.gaussianLimit where
  X := fun t ω i => v i * B.W (t : ℝ) ω
  measurable := fun t =>
    measurable_pi_lambda _ fun i => measurable_const.mul (B.measurable_eval (t : ℝ))
  cadlag := Filter.Eventually.of_forall fun ω => by
    have hcont : Continuous (fun s : ℝ≥0 => fun i : Fin d => v i * B.W (s : ℝ) ω) :=
      continuous_pi fun i => continuous_const.mul ((hBcont ω).comp NNReal.continuous_coe)
    exact ⟨fun t => hcont.continuousAt.continuousWithinAt,
      fun t _ => ⟨fun i => v i * B.W (t : ℝ) ω, hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
  start_zero := Filter.Eventually.of_forall fun ω => by ext i; simp [hB0 ω]
  indep_increments := by
    intro s t hst
    rcases eq_or_lt_of_le hst with rfl | hlt
    · have hzero : (fun ω : ℝ≥0 → ℝ => (fun i : Fin d => v i * B.W (s : ℝ) ω) -
          (fun i : Fin d => v i * B.W (s : ℝ) ω)) = fun _ => 0 := by funext ω; simp
      rw [hzero, MeasurableSpace.comap_const]
      exact indep_bot_left _
    · have hB_ind := (B.joint_increment_independent s.coe_nonneg (by exact_mod_cast hlt)).symm
      refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hB_ind ?_) ?_
      · refine iSup₂_le fun u hu => ?_
        have hcomp : (fun ω : ℝ≥0 → ℝ => fun i : Fin d => v i * B.W (u : ℝ) ω) =
            (fun r : ℝ => fun i : Fin d => v i * r) ∘ B.W (u : ℝ) := rfl
        rw [hcomp, ← MeasurableSpace.comap_comp]
        refine (MeasurableSpace.comap_mono ?_).trans
          (le_iSup₂_of_le (u : ℝ) (show (u : ℝ) ≤ (s : ℝ) by exact_mod_cast hu) le_rfl)
        exact (measurable_pi_lambda _ fun i => measurable_const.mul measurable_id).comap_le
      · have hcomp : (fun ω : ℝ≥0 → ℝ => (fun i : Fin d => v i * B.W (t : ℝ) ω) -
            (fun i : Fin d => v i * B.W (s : ℝ) ω)) =
            (fun r : ℝ => fun i : Fin d => v i * r) ∘ (fun ω => B.W (t : ℝ) ω - B.W (s : ℝ) ω) := by
          funext ω; ext i; simp only [Function.comp_apply, Pi.sub_apply]; ring
        rw [hcomp, ← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono
          (measurable_pi_lambda _ fun i => measurable_const.mul measurable_id).comap_le
  stationary_increments := by
    intro s t hst
    rcases eq_or_lt_of_le hst with rfl | hlt
    · simp only [tsub_self]
      have h1 : (fun ω : ℝ≥0 → ℝ => (fun i : Fin d => v i * B.W (s : ℝ) ω) -
          (fun i : Fin d => v i * B.W (s : ℝ) ω)) = fun _ => 0 := by funext ω; simp
      have h2 : (fun ω : ℝ≥0 → ℝ => fun i : Fin d => v i * B.W ((0 : ℝ≥0) : ℝ) ω) = fun _ => 0 := by
        funext ω; ext i; simp [hB0 ω]
      rw [h1, h2]
    · have hdiff : (fun ω : ℝ≥0 → ℝ => (fun i : Fin d => v i * B.W (t : ℝ) ω) -
          (fun i : Fin d => v i * B.W (s : ℝ) ω)) =
          (fun r : ℝ => fun i : Fin d => v i * r) ∘ (fun ω => B.W (t : ℝ) ω - B.W (s : ℝ) ω) := by
        funext ω; ext i; simp only [Function.comp_apply, Pi.sub_apply]; ring
      have hts : (fun ω : ℝ≥0 → ℝ => fun i : Fin d => v i * B.W ((t - s : ℝ≥0) : ℝ) ω) =
          (fun r : ℝ => fun i : Fin d => v i * r) ∘ (fun ω => B.W ((t - s : ℝ≥0) : ℝ) ω - B.W 0 ω) := by
        funext ω; ext i; simp [hB0 ω]
      have hlin_m : Measurable (fun r : ℝ => fun i : Fin d => v i * r) :=
        measurable_pi_lambda _ fun i => measurable_const.mul measurable_id
      have hm1 : Measurable (fun ω => B.W (t : ℝ) ω - B.W (s : ℝ) ω) :=
        (B.measurable_eval (t : ℝ)).sub (B.measurable_eval (s : ℝ))
      have hm2 : Measurable (fun ω => B.W ((t - s : ℝ≥0) : ℝ) ω - B.W 0 ω) :=
        (B.measurable_eval ((t - s : ℝ≥0) : ℝ)).sub (B.measurable_eval 0)
      rw [hdiff, hts,
        ← Measure.map_map hlin_m hm1,
        ← Measure.map_map hlin_m hm2,
        B.increment_gaussian s.coe_nonneg (by exact_mod_cast hlt),
        B.increment_gaussian le_rfl (by exact_mod_cast tsub_pos_of_lt hlt)]
      congr 2
      ext
      simp [NNReal.coe_sub hst]

private lemma scaled_bm_rdLevy_charFun {d : ℕ} (v : Fin d → ℝ)
    (B : LevyStochCalc.Brownian.BrownianMotion ProbabilityTheory.gaussianLimit)
    (hBcont : ∀ ω, Continuous (fun t => B.W t ω))
    (hB0 : ∀ ω, B.W 0 ω = 0) (t : ℝ≥0) (θ : Fin d → ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((innerRd θ ((scaled_bm_rdLevy v B hBcont hB0).X t ω) : ℝ) : ℂ))
        ∂ProbabilityTheory.gaussianLimit =
      Complex.exp (-(t : ℝ) * (((innerRd θ v) ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
  have hlin : ∀ ω, innerRd θ ((scaled_bm_rdLevy v B hBcont hB0).X t ω) =
      innerRd θ v * B.W (t : ℝ) ω := by
    intro ω
    simp only [innerRd, scaled_bm_rdLevy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hlin]
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · simp [hB0]
  · have hlaw : ProbabilityTheory.gaussianLimit.map (B.W (t : ℝ)) =
        ProbabilityTheory.gaussianReal 0 t := by
      have h := B.increment_gaussian le_rfl (show (0 : ℝ) < (t : ℝ) by exact_mod_cast ht)
      have heq : (fun ω => B.W (t : ℝ) ω - B.W 0 ω) = B.W (t : ℝ) := by
        funext ω; simp [hB0 ω]
      rw [heq] at h
      have hv : (⟨(t : ℝ) - 0, by linarith [t.coe_nonneg]⟩ : ℝ≥0) = t := by
        ext; simp
      rwa [hv] at h
    have hint : ∫ ω, Complex.exp (Complex.I * (((innerRd θ v * B.W (t : ℝ) ω : ℝ) : ℂ)))
        ∂ProbabilityTheory.gaussianLimit =
        charFun (ProbabilityTheory.gaussianLimit.map (B.W (t : ℝ))) (innerRd θ v) := by
      rw [charFun_apply_real, integral_map (B.measurable_eval (t : ℝ)).aemeasurable]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        dsimp only
        congr 1; push_cast; ring
      · exact (by fun_prop : Continuous fun x : ℝ =>
          Complex.exp ((innerRd θ v : ℂ) * (x : ℂ) * Complex.I)).aestronglyMeasurable
    rw [hint, hlaw, ProbabilityTheory.charFun_gaussianReal]
    congr 1
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
    push_cast
    ring

private lemma exists_gaussian_drift_rdLevy {d : ℕ}
    (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ, 0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ L : RdLevyProcess d Ω P,
          ∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I * ((innerRd θ (L.X t ω) : ℝ) : ℂ)) ∂P =
              Complex.exp (-(t : ℝ) *
                (Complex.I * ((∑ i : Fin d, a i * θ i : ℝ) : ℂ) +
                 (((∑ i : Fin d, ∑ j : Fin d, θ i * A i j * θ j : ℝ) / 2) : ℂ))) := by
  obtain ⟨S, hS⟩ := exists_sqrt_of_symm_psd A hAsymm hApos
  obtain ⟨B, hBcont, hB0⟩ := exists_std_brownian_1d
  -- Inductively sum the first k columns of S times independent 1D Brownian motions
  have hind : ∀ (k : ℕ) (hk : k ≤ d),
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := mΩ
        ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
          letI : IsProbabilityMeasure P := hP
          ∃ L : RdLevyProcess d Ω P,
            ∀ (t : ℝ≥0) (θ : Fin d → ℝ),
              ∫ ω, Complex.exp (Complex.I * ((innerRd θ (L.X t ω) : ℝ) : ℂ)) ∂P =
                Complex.exp (-(t : ℝ) *
                  (((∑ j : Fin k, (innerRd θ (fun i => S i ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)) ^ (2 : ℕ)) / 2 : ℝ) : ℂ)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
        deterministic_drift_rdLevy 0, fun t θ => ?_⟩
      simp [deterministic_drift_rdLevy, innerRd]
    | succ k ih =>
      intro hk
      obtain ⟨Ωk, mΩk, Pk, hPk, Lk, hLk⟩ := ih (Nat.le_of_succ_le hk)
      letI : MeasurableSpace Ωk := mΩk
      letI : IsProbabilityMeasure Pk := hPk
      let col : Fin d → ℝ := fun i => S i ⟨k, hk⟩
      let Lnew := scaled_bm_rdLevy col B hBcont hB0
      refine ⟨Ωk × (ℝ≥0 → ℝ), inferInstance, Pk.prod ProbabilityTheory.gaussianLimit, inferInstance,
        sum_two_indep_rdLevy Lk Lnew, fun t θ => ?_⟩
      rw [sum_two_indep_rdLevy_charFun Lk Lnew t θ, hLk t θ,
        scaled_bm_rdLevy_charFun col B hBcont hB0 t θ, ← Complex.exp_add]
      congr 1
      have hsum : (∑ j : Fin (k + 1), (innerRd θ (fun i => S i ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)) ^ (2 : ℕ)) =
          (∑ j : Fin k, (innerRd θ (fun i => S i ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hk)⟩)) ^ (2 : ℕ)) +
            (innerRd θ col) ^ (2 : ℕ) := by
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsum]
      push_cast
      ring
  obtain ⟨Ωg, mΩg, Pg, hPg, Lg, hLg⟩ := hind d le_rfl
  letI : MeasurableSpace Ωg := mΩg
  letI : IsProbabilityMeasure Pg := hPg
  let Ldrift := deterministic_drift_rdLevy a
  refine ⟨Unit × Ωg, inferInstance, (Measure.dirac ()).prod Pg, inferInstance,
    sum_two_indep_rdLevy Ldrift Lg, fun t θ => ?_⟩
  rw [sum_two_indep_rdLevy_charFun Ldrift Lg t θ, hLg t θ]
  have hdrift_cf :
      ∫ ω, Complex.exp (Complex.I * ((innerRd θ (Ldrift.X t ω) : ℝ) : ℂ)) ∂(Measure.dirac ()) =
        Complex.exp (-(t : ℝ) * (Complex.I * ((∑ i : Fin d, a i * θ i : ℝ) : ℂ))) := by
    rw [integral_dirac]
    congr 1
    have hinner : innerRd θ (Ldrift.X t ()) = -(t : ℝ) * ∑ i : Fin d, a i * θ i := by
      simp only [innerRd, Ldrift, deterministic_drift_rdLevy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hinner]
    push_cast
    ring
  rw [hdrift_cf, ← Complex.exp_add]
  congr 1
  have hquad : (∑ j : Fin d, (innerRd θ (fun i => S i ⟨j.val, j.isLt⟩)) ^ (2 : ℕ)) =
      ∑ i : Fin d, ∑ k : Fin d, θ i * A i k * θ k := by
    have h1 : ∀ j : Fin d, (innerRd θ (fun i => S i j)) ^ (2 : ℕ) =
        ∑ i : Fin d, ∑ k : Fin d, θ i * (S i j * S k j) * θ k := by
      intro j
      rw [sq, innerRd, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    calc ∑ j : Fin d, (innerRd θ (fun i => S i ⟨j.val, j.isLt⟩)) ^ (2 : ℕ)
        = ∑ j : Fin d, ∑ i : Fin d, ∑ k : Fin d, θ i * (S i j * S k j) * θ k :=
          Finset.sum_congr rfl fun j _ => h1 j
      _ = ∑ i : Fin d, ∑ j : Fin d, ∑ k : Fin d, θ i * (S i j * S k j) * θ k :=
          Finset.sum_comm
      _ = ∑ i : Fin d, ∑ k : Fin d, ∑ j : Fin d, θ i * (S i j * S k j) * θ k :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin d, ∑ k : Fin d, θ i * (∑ j : Fin d, S i j * S k j) * θ k := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ i : Fin d, ∑ k : Fin d, θ i * A i k * θ k := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hS i k]
  rw [hquad]
  push_cast
  ring

/-! ## Section 2: `d`-Dimensional Compound Poisson Process -/

private structure CadlagPoissonProcess (r : ℝ≥0) (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  C : ℝ≥0 → Ω → ℕ
  measurable : ∀ t : ℝ≥0, Measurable (C t)
  start_zero : ∀ ω : Ω, C 0 ω = 0
  mono : ∀ ω : Ω, Monotone (fun t : ℝ≥0 => C t ω)
  right_const : ∀ (ω : Ω) (t : ℝ≥0), ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u : ℝ≥0, t ≤ u → u ≤ t + δ → C u ω = C t ω
  left_const : ∀ (ω : Ω) (t : ℝ≥0), 0 < t → ∃ s : ℝ≥0, s < t ∧ ∀ u : ℝ≥0, s ≤ u → u < t → C u ω = C s ω
  incr_law : ∀ (s t : ℝ≥0), s ≤ t →
    P.map (fun ω => C t ω - C s ω) = ProbabilityTheory.poissonMeasure (r * (t - s))
  indep_incr : ∀ (s t : ℝ≥0), s ≤ t →
    ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun ω => C t ω - C s ω) inferInstance)
      (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (C u) inferInstance)
      P

/-- An antitone sequence in `ℕ` is eventually constant. -/
private lemma exists_eventually_const_of_antitone_nat {k : ℕ → ℕ} (hk : Antitone k) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k n = k n₀ := by
  have hne : (Set.range k).Nonempty := ⟨k 0, 0, rfl⟩
  classical
  let m := WellFounded.min Nat.lt_wfRel.wf (Set.range k) hne
  have hm_mem : m ∈ Set.range k := WellFounded.min_mem Nat.lt_wfRel.wf (Set.range k) hne
  obtain ⟨n₀, hn₀⟩ := hm_mem
  refine ⟨n₀, fun n hn => le_antisymm (hk hn) ?_⟩
  rw [hn₀]
  exact not_lt.mp (WellFounded.not_lt_min Nat.lt_wfRel.wf (Set.range k) (⟨n, rfl⟩ : k n ∈ Set.range k))

private noncomputable def ennrealToNat (x : ℝ≥0∞) : ℕ := Nat.floor x.toReal

private lemma measurable_ennrealToNat : Measurable ennrealToNat :=
  Nat.measurable_floor.comp ENNReal.measurable_toReal

private lemma ennrealToNat_natCast (k : ℕ) : ennrealToNat (k : ℝ≥0∞) = k := by
  simp [ennrealToNat]

/-- A monotone sequence in `ℕ` bounded above is eventually constant. -/
private lemma exists_eventually_const_of_monotone_bdd {k : ℕ → ℕ} {B : ℕ}
    (hk : Monotone k) (hB : ∀ n, k n ≤ B) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k n = k n₀ := by
  have hanti : Antitone (fun n => B - k n) := fun i j hij => Nat.sub_le_sub_left (hk hij) B
  obtain ⟨n₀, hn₀⟩ := exists_eventually_const_of_antitone_nat hanti
  refine ⟨n₀, fun n hn => ?_⟩
  have h := hn₀ n hn
  have h1 := hB n
  have h2 := hB n₀
  omega

/-- Strictly decreasing sequence of rationals converging down to `t : ℝ≥0`. -/
private lemma exists_antitone_rat_gt (t : ℝ≥0) :
    ∃ q : ℕ → ℚ, Antitone q ∧ (∀ n, (t : ℝ) < (q n : ℝ)) ∧
      (∀ n, (q n : ℝ) < (t : ℝ) + 1 / ((n : ℝ) + 1)) := by
  have step : ∀ (n : ℕ) (u : ℝ), (t : ℝ) < u →
      ∃ r : ℚ, (t : ℝ) < (r : ℝ) ∧ (r : ℝ) < min u ((t : ℝ) + 1 / ((n : ℝ) + 1)) := by
    intro n u hu
    have hlt : (t : ℝ) < min u ((t : ℝ) + 1 / ((n : ℝ) + 1)) :=
      lt_min hu (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
    exact exists_rat_btwn hlt
  choose f hf1 hf2 using step
  let q : ℕ → { r : ℚ // (t : ℝ) < (r : ℝ) } := Nat.rec
    ⟨f 0 ((t : ℝ) + 2) (by linarith), hf1 0 _ (by linarith)⟩
    (fun n prev => ⟨f (n + 1) (prev.1 : ℝ) prev.2, hf1 (n + 1) _ prev.2⟩)
  refine ⟨fun n => (q n).1, ?_, fun n => (q n).2, ?_⟩
  · refine antitone_nat_of_succ_le fun n => ?_
    have hlt : ((q (n + 1)).1 : ℝ) < ((q n).1 : ℝ) :=
      lt_of_lt_of_le (hf2 (n + 1) ((q n).1 : ℝ) (q n).2) (min_le_left _ _)
    exact_mod_cast le_of_lt hlt
  · intro n
    cases n with
    | zero =>
      exact lt_of_lt_of_le (hf2 0 ((t : ℝ) + 2) (by linarith)) (min_le_right _ _)
    | succ n =>
      exact lt_of_lt_of_le (hf2 (n + 1) ((q n).1 : ℝ) (q n).2) (min_le_right _ _)

private lemma exists_cadlag_poisson_counting (r : ℝ≥0) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        Nonempty (CadlagPoissonProcess r Ω P) := by
  let ν₁ : Measure ℝ := (r : ℝ≥0∞) • Measure.dirac (1 : ℝ)
  have hν₁_fin : IsFiniteMeasure ν₁ := by
    refine ⟨?_⟩
    simp [ν₁]
  obtain ⟨Ω, mΩ, P, hP, ⟨N⟩⟩ := Kyprianou.poissonRandomMeasureExists ν₁
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have href : ∀ {a b : ℝ≥0}, a ≤ b →
      LevyStochCalc.Poisson.referenceIntensity ν₁ (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ ({1} : Set ℝ)) =
        ((r * (b - a) : ℝ≥0) : ℝ≥0∞) := by
    intro a b hab
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod]
    have hsub : Set.Ioc (a : ℝ) (b : ℝ) ⊆ Set.Ici (0 : ℝ) := fun x hx =>
      le_trans a.coe_nonneg (le_of_lt hx.1)
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
    have hdir : ν₁ {1} = (r : ℝ≥0∞) := by
      simp [ν₁]
    rw [hdir]
    have hba : ENNReal.ofReal ((b : ℝ) - (a : ℝ)) = ((b - a : ℝ≥0) : ℝ≥0∞) := by
      rw [← NNReal.coe_sub hab, ENNReal.ofReal_coe_nnreal]
    rw [hba, mul_comm]
    norm_cast
  have hBmeas : ∀ (a b : ℝ), MeasurableSet (Set.Ioc a b ×ˢ ({1} : Set ℝ)) :=
    fun a b => measurableSet_Ioc.prod (measurableSet_singleton 1)
  let Qnn := { q : ℚ // 0 ≤ q }
  let GQ : Set Ω := ⋂ q : Qnn, { ω : Ω | ∃ k : ℕ, N.N ω (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1}) = k }
  have hGQ_meas : MeasurableSet GQ := by
    refine MeasurableSet.iInter fun q => ?_
    have heq : { ω : Ω | ∃ k : ℕ, N.N ω (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1}) = k } =
        ⋃ k : ℕ, (fun ω => N.N ω (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1})) ⁻¹' {(k : ℝ≥0∞)} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      (N.measurable_eval (hBmeas 0 (q.1 : ℝ))) (measurableSet_singleton _)
  have hGQ_ae : ∀ᵐ ω ∂P, ω ∈ GQ := by
    rw [show GQ = ⋂ q : Qnn, { ω : Ω | ∃ k : ℕ, N.N ω (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1}) = k } from rfl]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [ae_all_iff]
    intro q
    let qnn : ℝ≥0 := ⟨(q.1 : ℝ), by exact_mod_cast q.2⟩
    have hfin : LevyStochCalc.Poisson.referenceIntensity ν₁ (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1}) ≠ ⊤ := by
      have h := href (bot_le : (0 : ℝ≥0) ≤ qnn)
      change LevyStochCalc.Poisson.referenceIntensity ν₁ (Set.Ioc (0 : ℝ) (q.1 : ℝ) ×ˢ {1}) = _ at h
      rw [h]; exact ENNReal.coe_ne_top
    exact N.integer_valued (hBmeas 0 (q.1 : ℝ)) hfin
  have hGQ_right : ∀ {ω : Ω}, ω ∈ GQ → ∀ t : ℝ≥0,
      (∃ k : ℕ, N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1}) = k) ∧
      (∃ δ : ℝ≥0, 0 < δ ∧
        N.N ω (Set.Ioc (0 : ℝ) ((t + δ : ℝ≥0) : ℝ) ×ˢ {1}) = N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1})) := by
    intro ω hω t
    obtain ⟨q, hq_anti, hq_gt, hq_lt⟩ := exists_antitone_rat_gt t
    have hq_nn : ∀ n, 0 ≤ q n := fun n => by
      have : (0 : ℝ) < (q n : ℝ) := lt_of_le_of_lt t.coe_nonneg (hq_gt n)
      exact_mod_cast le_of_lt this
    have hk_ex : ∀ n, ∃ k : ℕ, N.N ω (Set.Ioc (0 : ℝ) (q n : ℝ) ×ˢ {1}) = k := fun n =>
      (Set.mem_iInter.mp hω ⟨q n, hq_nn n⟩)
    choose k hk using hk_ex
    have hk_anti : Antitone k := by
      intro i j hij
      have hsub : Set.Ioc (0 : ℝ) (q j : ℝ) ×ˢ ({1} : Set ℝ) ⊆
          Set.Ioc (0 : ℝ) (q i : ℝ) ×ˢ ({1} : Set ℝ) :=
        Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hq_anti hij)) Set.Subset.rfl
      have hle : ((k j : ℕ) : ℝ≥0∞) ≤ ((k i : ℕ) : ℝ≥0∞) := by
        rw [← hk j, ← hk i]; exact measure_mono hsub
      exact_mod_cast hle
    obtain ⟨n₀, hn₀⟩ := exists_eventually_const_of_antitone_nat hk_anti
    have hinter : (⋂ n : ℕ, Set.Ioc (0 : ℝ) (q n : ℝ) ×ˢ ({1} : Set ℝ)) =
        Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ ({1} : Set ℝ) := by
      ext ⟨x, y⟩
      simp only [Set.mem_iInter, Set.mem_prod, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · intro h
        refine ⟨⟨(h 0).1.1, ?_⟩, (h 0).2⟩
        by_contra hx
        push_neg at hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        have h1 : (q n : ℝ) < (t : ℝ) + 1 / ((n : ℝ) + 1) := hq_lt n
        have h2 : x ≤ (q n : ℝ) := (h n).1.2
        linarith
      · intro ⟨⟨hx0, hxt⟩, hy⟩ n
        exact ⟨⟨hx0, le_trans hxt (le_of_lt (hq_gt n))⟩, hy⟩
    have htend : Filter.Tendsto (fun n => N.N ω (Set.Ioc (0 : ℝ) (q n : ℝ) ×ˢ {1}))
        Filter.atTop (nhds (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1}))) := by
      rw [← hinter]
      refine MeasureTheory.tendsto_measure_iInter_atTop
        (fun n => (hBmeas 0 (q n : ℝ)).nullMeasurableSet) ?_ ⟨0, ?_⟩
      · intro i j hij
        exact Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hq_anti hij)) Set.Subset.rfl
      · rw [hk 0]; exact ENNReal.natCast_ne_top _
    have htend_const : Filter.Tendsto (fun n => N.N ω (Set.Ioc (0 : ℝ) (q n : ℝ) ×ˢ {1}))
        Filter.atTop (nhds ((k n₀ : ℕ) : ℝ≥0∞)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
      rw [hk n, hn₀ n hn]
    have heq_t : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1}) = (k n₀ : ℕ) :=
      tendsto_nhds_unique htend htend_const
    refine ⟨⟨k n₀, heq_t⟩, ?_⟩
    let δ : ℝ≥0 := ⟨(q n₀ : ℝ) - (t : ℝ), by linarith [hq_gt n₀]⟩
    have hδ_pos : 0 < δ := by
      change (0 : ℝ) < (q n₀ : ℝ) - (t : ℝ)
      linarith [hq_gt n₀]
    refine ⟨δ, hδ_pos, ?_⟩
    have htd : ((t + δ : ℝ≥0) : ℝ) = (q n₀ : ℝ) := by
      change (t : ℝ) + ((q n₀ : ℝ) - (t : ℝ)) = (q n₀ : ℝ)
      ring
    rw [htd, hk n₀, heq_t]
  let C : ℝ≥0 → Ω → ℕ := fun t ω => by
    classical exact if ω ∈ GQ then ennrealToNat (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1})) else 0
  have hC_meas : ∀ t : ℝ≥0, Measurable (C t) := fun t => by
    classical
    exact Measurable.ite hGQ_meas (measurable_ennrealToNat.comp (N.measurable_eval (hBmeas 0 (t : ℝ)))) measurable_const
  have hC_zero : ∀ ω : Ω, C 0 ω = 0 := fun ω => by
    classical
    simp [C, ennrealToNat]
  have hC_mono : ∀ ω : Ω, Monotone (fun t : ℝ≥0 => C t ω) := fun ω s t hst => by
    classical
    by_cases hω : ω ∈ GQ
    · simp only [C, if_pos hω]
      obtain ⟨ks, hks⟩ := (hGQ_right hω s).1
      obtain ⟨kt, hkt⟩ := (hGQ_right hω t).1
      rw [hks, hkt, ennrealToNat_natCast, ennrealToNat_natCast]
      have hle : ((ks : ℕ) : ℝ≥0∞) ≤ ((kt : ℕ) : ℝ≥0∞) := by
        rw [← hks, ← hkt]
        exact measure_mono (Set.prod_mono (Set.Ioc_subset_Ioc_right (by exact_mod_cast hst)) Set.Subset.rfl)
      exact_mod_cast hle
    · simp [C, hω]
  have hC_right : ∀ (ω : Ω) (t : ℝ≥0),
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u : ℝ≥0, t ≤ u → u ≤ t + δ → C u ω = C t ω := by
    intro ω t
    classical
    by_cases hω : ω ∈ GQ
    · obtain ⟨δ, hδ_pos, hδ_eq⟩ := (hGQ_right hω t).2
      refine ⟨δ, hδ_pos, fun u htu hutδ => ?_⟩
      have h1 : C t ω ≤ C u ω := hC_mono ω htu
      have h2 : C u ω ≤ C (t + δ) ω := hC_mono ω hutδ
      have h3 : C (t + δ) ω = C t ω := by
        simp only [C, if_pos hω, hδ_eq]
      omega
    · exact ⟨1, one_pos, fun u _ _ => by simp [C, hω]⟩
  have hC_left : ∀ (ω : Ω) (t : ℝ≥0), 0 < t →
      ∃ s : ℝ≥0, s < t ∧ ∀ u : ℝ≥0, s ≤ u → u < t → C u ω = C s ω := by
    intro ω t ht
    let seq : ℕ → ℝ≥0 := fun n => t * (n : ℝ≥0) / ((n : ℝ≥0) + 1)
    have hseq_lt : ∀ n, seq n < t := fun n => by
      change ((t : ℝ) * (n : ℝ) / ((n : ℝ) + 1)) < (t : ℝ)
      have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hden]
      nlinarith
    have hseq_mono : Monotone seq := fun i j hij => by
      change (t : ℝ) * (i : ℝ) / ((i : ℝ) + 1) ≤ (t : ℝ) * (j : ℝ) / ((j : ℝ) + 1)
      have hdi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hdj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hdi hdj]
      have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      nlinarith [t.coe_nonneg]
    have hk_mono : Monotone (fun n => C (seq n) ω) := fun i j hij => hC_mono ω (hseq_mono hij)
    have hk_bdd : ∀ n, C (seq n) ω ≤ C t ω := fun n => hC_mono ω (le_of_lt (hseq_lt n))
    obtain ⟨n₀, hn₀⟩ := exists_eventually_const_of_monotone_bdd hk_mono hk_bdd
    refine ⟨seq n₀, hseq_lt n₀, fun u hsu hut => ?_⟩
    have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have htu_pos : (0 : ℝ) < (t : ℝ) - (u : ℝ) := by
      have : (u : ℝ) < (t : ℝ) := by exact_mod_cast hut
      linarith
    obtain ⟨m, hm⟩ := exists_nat_gt ((t : ℝ) / ((t : ℝ) - (u : ℝ)))
    let n := max n₀ m
    have hu_le : u ≤ seq n := by
      change (u : ℝ) ≤ (t : ℝ) * (n : ℝ) / ((n : ℝ) + 1)
      have hdn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [le_div_iff₀ hdn]
      have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_right n₀ m
      have hgt : (t : ℝ) / ((t : ℝ) - (u : ℝ)) < (n : ℝ) + 1 := by linarith
      have hmul := (div_lt_iff₀ htu_pos).mp hgt
      nlinarith
    have h1 : C (seq n₀) ω ≤ C u ω := hC_mono ω hsu
    have h2 : C u ω ≤ C (seq n) ω := hC_mono ω hu_le
    have h3 : C (seq n) ω = C (seq n₀) ω := hn₀ n (le_max_left n₀ m)
    omega
  have hC_incr_eq : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {ω : Ω}, ω ∈ GQ →
      C t ω - C s ω = ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1})) := by
    intro s t hst ω hω
    classical
    simp only [C, if_pos hω]
    obtain ⟨ks, hks⟩ := (hGQ_right hω s).1
    obtain ⟨kt, hkt⟩ := (hGQ_right hω t).1
    have hunion : Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ ({1} : Set ℝ) =
        (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ ({1} : Set ℝ)) ∪ (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ ({1} : Set ℝ)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_union, Set.mem_prod, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · intro ⟨⟨hx0, hxt⟩, hy⟩
        by_cases hxs : x ≤ (s : ℝ)
        · exact Or.inl ⟨⟨hx0, hxs⟩, hy⟩
        · exact Or.inr ⟨⟨lt_of_not_ge hxs, hxt⟩, hy⟩
      · rintro (⟨⟨hx0, hxs⟩, hy⟩ | ⟨⟨hxs, hxt⟩, hy⟩)
        · exact ⟨⟨hx0, le_trans hxs (by exact_mod_cast hst)⟩, hy⟩
        · exact ⟨⟨lt_of_le_of_lt s.coe_nonneg hxs, hxt⟩, hy⟩
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ ({1} : Set ℝ))
        (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ ({1} : Set ℝ)) := by
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ ⟨⟨_, hxs⟩, _⟩ ⟨⟨hxs', _⟩, _⟩
      linarith
    have hadd : N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {1}) =
        N.N ω (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ {1}) + N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}) := by
      rw [hunion, measure_union hdisj (hBmeas (s : ℝ) (t : ℝ))]
    have hfin_st : N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}) ≠ ⊤ := by
      intro htop
      rw [htop, add_top, hkt] at hadd
      exact ENNReal.natCast_ne_top kt hadd
    have htoReal := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add (by rw [hks]; exact ENNReal.natCast_ne_top ks) hfin_st,
      hkt, hks, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at htoReal
    have hdiff : (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1})).toReal = ((kt - ks : ℕ) : ℝ) := by
      have hle : ks ≤ kt := by
        have : ((ks : ℕ) : ℝ) ≤ ((kt : ℕ) : ℝ) := by
          linarith [ENNReal.toReal_nonneg (a := N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}))]
        exact_mod_cast this
      rw [Nat.cast_sub hle]
      linarith
    rw [hkt, hks, ennrealToNat_natCast, ennrealToNat_natCast, ennrealToNat, hdiff, Nat.floor_natCast]
  have hC_law : ∀ (s t : ℝ≥0), s ≤ t →
      P.map (fun ω => C t ω - C s ω) = ProbabilityTheory.poissonMeasure (r * (t - s)) := by
    intro s t hst
    have hae : (fun ω => C t ω - C s ω) =ᵐ[P]
        (fun ω => ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}))) := by
      filter_upwards [hGQ_ae] with ω hω
      exact hC_incr_eq hst hω
    rw [Measure.map_congr hae]
    have hcomp : (fun ω => ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}))) =
        ennrealToNat ∘ (fun ω => N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1})) := rfl
    rw [hcomp, ← Measure.map_map measurable_ennrealToNat (N.measurable_eval (hBmeas (s : ℝ) (t : ℝ)))]
    have hfin : LevyStochCalc.Poisson.referenceIntensity ν₁ (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}) ≠ ⊤ := by
      rw [href hst]; exact ENNReal.coe_ne_top
    rw [N.poisson_law (hBmeas (s : ℝ) (t : ℝ)) hfin, href hst, ENNReal.toNNReal_coe]
    unfold LevyStochCalc.Poisson.poissonMeasureENN
    rw [Measure.map_map measurable_ennrealToNat (Measurable.of_discrete)]
    have hid : ennrealToNat ∘ (fun n : ℕ => (n : ℝ≥0∞)) = id := by
      funext n; exact ennrealToNat_natCast n
    rw [hid, Measure.map_id]
  have hC_indep : ∀ (s t : ℝ≥0), s ≤ t →
      ProbabilityTheory.Indep
        (MeasurableSpace.comap (fun ω => C t ω - C s ω) inferInstance)
        (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (C u) inferInstance)
        P := by
    intro s t hst
    rcases eq_or_lt_of_le hst with rfl | hlt
    · have hconst : (fun ω => C s ω - C s ω) = fun _ => (0 : ℕ) := by
        funext ω; simp
      rw [hconst]
      refine indep_of_indep_of_le_left (ProbabilityTheory.indep_bot_left _) ?_
      rw [MeasurableSpace.comap_const]
    · refine indep_past_of_finset hC_meas ((hC_meas t).sub (hC_meas s)) fun p u hu => ?_
      have h1 : (fun ω => C t ω - C s ω) =ᵐ[P]
          (fun ω => ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}))) := by
        filter_upwards [hGQ_ae] with ω hω
        exact hC_incr_eq (le_of_lt hlt) hω
      have h2 : (fun ω => fun j : Fin p => C (u j) ω) =ᵐ[P]
          (fun ω => fun j : Fin p => ennrealToNat (N.N ω (Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ {1}))) := by
        filter_upwards [hGQ_ae] with ω hω
        funext j
        classical
        simp [C, hω]
      have hind_raw : ProbabilityTheory.IndepFun
          (fun ω => ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1})))
          (fun ω => fun j : Fin p => ennrealToNat (N.N ω (Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ {1}))) P := by
        have hpf := (N.joint_past_future_independent s.coe_nonneg (by exact_mod_cast hlt)
          (measurableSet_singleton (1 : ℝ)) (by simp [ν₁])).symm
        rw [ProbabilityTheory.IndepFun_iff_Indep]
        refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hpf ?_) ?_
        · rw [MeasurableSpace.comap_le_iff_le_map]
          have hmeas_F : @Measurable Ω (Fin p → ℕ)
              (⨆ B ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic (s : ℝ) ×ˢ Set.univ ∧ MeasurableSet C },
                MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
              inferInstance
              (fun ω => fun j : Fin p => ennrealToNat (N.N ω (Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ {1}))) := by
            refine @measurable_pi_lambda Ω (Fin p) _
              (⨆ B ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic (s : ℝ) ×ˢ Set.univ ∧ MeasurableSet C },
                MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _ _ fun j => ?_
            have hmem : Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ ({1} : Set ℝ) ∈
                { C : Set (ℝ × ℝ) | C ⊆ Set.Iic (s : ℝ) ×ˢ Set.univ ∧ MeasurableSet C } := by
              refine ⟨fun ⟨x, y⟩ ⟨⟨_, hxu⟩, _⟩ => ⟨?_, trivial⟩, hBmeas 0 ((u j : ℝ≥0) : ℝ)⟩
              have hus : u j ≤ s := hu j
              exact le_trans hxu (by exact_mod_cast hus)
            have hle_u : MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ {1}))
                inferInstance ≤
                ⨆ B ∈ { C : Set (ℝ × ℝ) | C ⊆ Set.Iic (s : ℝ) ×ˢ Set.univ ∧ MeasurableSet C },
                  MeasurableSpace.comap (fun ω => N.N ω B) inferInstance :=
              le_iSup₂_of_le (Set.Ioc (0 : ℝ) ((u j : ℝ≥0) : ℝ) ×ˢ {1}) hmem le_rfl
            exact (measurable_ennrealToNat.comp (comap_measurable _)).mono hle_u le_rfl
          exact fun A hA => hmeas_F hA
        · rw [MeasurableSpace.comap_le_iff_le_map]
          have hmeas_inc : @Measurable Ω ℕ
              (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1})) inferInstance)
              inferInstance
              (fun ω => ennrealToNat (N.N ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ {1}))) :=
            measurable_ennrealToNat.comp (comap_measurable _)
          exact fun A hA => hmeas_inc hA
      exact hind_raw.congr h1.symm h2.symm
  exact ⟨Ω, mΩ, P, hP, ⟨⟨C, hC_meas, hC_zero, hC_mono, hC_right, hC_left, hC_law, hC_indep⟩⟩⟩

/-! ### Poisson moment & generating-function identities -/

private lemma poissonMeasure_integral_pow (lam : ℝ≥0) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∫ n : ℕ, z ^ n ∂(ProbabilityTheory.poissonMeasure lam) =
      Complex.exp (((lam : ℝ) : ℂ) * (z - 1)) := by
  have hint : Integrable (fun n : ℕ => z ^ n) (ProbabilityTheory.poissonMeasure lam) := by
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun n => ?_)
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
  rw [MeasureTheory.integral_countable hint]
  have hterm : ∀ n : ℕ,
      (ProbabilityTheory.poissonMeasure lam).real {n} • z ^ n =
        Complex.exp (-((lam : ℝ) : ℂ)) * ((((lam : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ)) := by
    intro n
    rw [ProbabilityTheory.poissonMeasure_real_singleton, Complex.real_smul]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum : ∑' n : ℕ, (((lam : ℝ) : ℂ) * z) ^ n / (n.factorial : ℂ) =
      Complex.exp (((lam : ℝ) : ℂ) * z) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (((lam : ℝ) : ℂ) * z)
    rw [← Complex.exp_eq_exp_ℂ] at h
    exact h.tsum_eq
  rw [hsum, ← Complex.exp_add]
  congr 1
  ring

private lemma poissonMeasure_summable_nat_sq (lam : ℝ≥0) :
    Summable (fun n : ℕ => (ProbabilityTheory.poissonMeasure lam).real {n} * ((n : ℝ) ^ (2 : ℕ))) := by
  have hexp : Summable (fun k : ℕ => ((lam : ℝ) ^ k) / (k.factorial : ℝ)) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (lam : ℝ)
    exact h.summable
  have h1 : Summable (fun n : ℕ => Real.exp (-(lam : ℝ)) * (lam : ℝ) *
      ((lam : ℝ) ^ (n - 1) / ((n - 1).factorial : ℝ))) := by
    have hshift : Summable (fun n : ℕ => ((lam : ℝ) ^ (n - 1) / ((n - 1).factorial : ℝ))) := by
      rw [← summable_nat_add_iff 1]
      simpa using hexp
    exact hshift.mul_left _
  have h2 : Summable (fun n : ℕ => Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (2 : ℕ) *
      ((lam : ℝ) ^ (n - 2) / ((n - 2).factorial : ℝ))) := by
    have hshift : Summable (fun n : ℕ => ((lam : ℝ) ^ (n - 2) / ((n - 2).factorial : ℝ))) := by
      rw [← summable_nat_add_iff 2]
      simpa using hexp
    exact hshift.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h1.add h2)
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  match n with
  | 0 =>
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  | 1 =>
    simp only [Nat.cast_one, one_pow, mul_one, pow_one, Nat.factorial_one, div_one,
      Nat.sub_self, pow_zero, Nat.factorial_zero]
    have : 0 ≤ Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (2 : ℕ) *
        ((lam : ℝ) ^ (1 - 2) / ((1 - 2).factorial : ℝ)) := by positivity
    linarith
  | k + 2 =>
    have hfac1 : ((k + 2).factorial : ℝ) = ((k + 2 : ℕ) : ℝ) * ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfac2 : ((k + 2).factorial : ℝ) = ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hsplit : (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) =
        ((k + 2 : ℕ) : ℝ) + ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hne1 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hne2 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hfac_ne : (k.factorial : ℝ) ≠ 0 := by positivity
    have hfac1_ne : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [hsplit, mul_add]
    have ht1 : Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (k + 2) / ((k + 2).factorial : ℝ) * ((k + 2 : ℕ) : ℝ) =
        Real.exp (-(lam : ℝ)) * (lam : ℝ) * ((lam : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
      rw [hfac1, pow_succ']
      field_simp
    have ht2 : Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (k + 2) / ((k + 2).factorial : ℝ) *
          (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) =
        Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (2 : ℕ) * ((lam : ℝ) ^ k / (k.factorial : ℝ)) := by
      rw [hfac2]
      have hp : (lam : ℝ) ^ (k + 2) = (lam : ℝ) ^ (2 : ℕ) * (lam : ℝ) ^ k := by ring
      rw [hp]
      field_simp
    have hk1 : k + 2 - 1 = k + 1 := by omega
    have hk2 : k + 2 - 2 = k := by omega
    rw [hk1, hk2, ht1, ht2]

private lemma poissonMeasure_integrable_nat_sq (lam : ℝ≥0) :
    Integrable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))) (ProbabilityTheory.poissonMeasure lam) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, MeasureTheory.lintegral_countable']
  have hsum := poissonMeasure_summable_nat_sq lam
  have htsum_lt : (∑' n : ℕ, ENNReal.ofReal ((ProbabilityTheory.poissonMeasure lam).real {n} * ((n : ℝ) ^ (2 : ℕ)))) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) htsum_lt
  refine tsum_congr fun n => ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [mul_comm, Real.enorm_eq_ofReal (by positivity)]

private lemma poissonMeasure_integrable_nat (lam : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure lam) := by
  refine (poissonMeasure_integrable_nat_sq lam).mono' Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have : (n : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
    cases n with
    | zero => simp
    | succ k =>
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith
  exact this

private lemma poissonMeasure_integral_nat (lam : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure lam) = (lam : ℝ) := by
  rw [MeasureTheory.integral_countable (poissonMeasure_integrable_nat lam)]
  have hsum : Summable (fun n : ℕ => (ProbabilityTheory.poissonMeasure lam).real {n} * (n : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (poissonMeasure_summable_nat_sq lam)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    cases n with
    | zero => simp
    | succ k =>
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith
  simp_rw [smul_eq_mul]
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have hterm : ∀ k : ℕ,
      (ProbabilityTheory.poissonMeasure lam).real {k + 1} * ((k + 1 : ℕ) : ℝ) =
        Real.exp (-(lam : ℝ)) * (lam : ℝ) * ((lam : ℝ) ^ k / (k.factorial : ℝ)) := by
    intro k
    rw [ProbabilityTheory.poissonMeasure_real_singleton, Nat.factorial_succ, pow_succ']
    have h1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hexp : ∑' k : ℕ, (lam : ℝ) ^ k / (k.factorial : ℝ) = Real.exp (lam : ℝ) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (lam : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    exact h.tsum_eq
  rw [hexp]
  have : Real.exp (-(lam : ℝ)) * (lam : ℝ) * Real.exp (lam : ℝ) =
      (lam : ℝ) * (Real.exp (-(lam : ℝ)) * Real.exp (lam : ℝ)) := by ring
  rw [this, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

private lemma poissonMeasure_integral_nat_sq (lam : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) ^ (2 : ℕ)) ∂(ProbabilityTheory.poissonMeasure lam) =
      (lam : ℝ) + (lam : ℝ) ^ (2 : ℕ) := by
  rw [MeasureTheory.integral_countable (poissonMeasure_integrable_nat_sq lam)]
  simp_rw [smul_eq_mul]
  have hsum := poissonMeasure_summable_nat_sq lam
  have hsum1 : Summable (fun n : ℕ => (ProbabilityTheory.poissonMeasure lam).real {n} * (n : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    cases n with
    | zero => simp
    | succ k =>
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
      nlinarith
  have hsum_diff : Summable (fun n : ℕ =>
      (ProbabilityTheory.poissonMeasure lam).real {n} * (((n : ℝ) ^ (2 : ℕ)) - (n : ℝ))) := by
    have heq : (fun n : ℕ => (ProbabilityTheory.poissonMeasure lam).real {n} * (((n : ℝ) ^ (2 : ℕ)) - (n : ℝ))) =
        fun n => (ProbabilityTheory.poissonMeasure lam).real {n} * ((n : ℝ) ^ (2 : ℕ)) -
          (ProbabilityTheory.poissonMeasure lam).real {n} * (n : ℝ) := by
      funext n; ring
    rw [heq]; exact hsum.sub hsum1
  have hsplit : ∑' n : ℕ, (ProbabilityTheory.poissonMeasure lam).real {n} * ((n : ℝ) ^ (2 : ℕ)) =
      (∑' n : ℕ, (ProbabilityTheory.poissonMeasure lam).real {n} * (n : ℝ)) +
      (∑' n : ℕ, (ProbabilityTheory.poissonMeasure lam).real {n} * (((n : ℝ) ^ (2 : ℕ)) - (n : ℝ))) := by
    rw [← hsum1.tsum_add hsum_diff]
    refine tsum_congr fun n => by ring
  rw [hsplit]
  have hpart1 : ∑' n : ℕ, (ProbabilityTheory.poissonMeasure lam).real {n} * (n : ℝ) = (lam : ℝ) := by
    have := poissonMeasure_integral_nat lam
    rw [MeasureTheory.integral_countable (poissonMeasure_integrable_nat lam)] at this
    simpa [smul_eq_mul] using this
  have hpart2 : ∑' n : ℕ, (ProbabilityTheory.poissonMeasure lam).real {n} * (((n : ℝ) ^ (2 : ℕ)) - (n : ℝ)) =
      (lam : ℝ) ^ (2 : ℕ) := by
    rw [hsum_diff.tsum_eq_zero_add]
    have hsum_diff1 : Summable (fun n : ℕ =>
        (ProbabilityTheory.poissonMeasure lam).real {n + 1} *
          ((((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) - ((n + 1 : ℕ) : ℝ))) :=
      (summable_nat_add_iff 1).mpr hsum_diff
    rw [hsum_diff1.tsum_eq_zero_add]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self,
      mul_zero, zero_add, zero_add, Nat.cast_one, one_pow]
    have hterm : ∀ k : ℕ,
        (ProbabilityTheory.poissonMeasure lam).real {k + 2} *
          ((((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) - ((k + 2 : ℕ) : ℝ)) =
          Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (2 : ℕ) * ((lam : ℝ) ^ k / (k.factorial : ℝ)) := by
      intro k
      rw [ProbabilityTheory.poissonMeasure_real_singleton]
      have hfac : ((k + 2).factorial : ℝ) = ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
      have hsub : (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) - ((k + 2 : ℕ) : ℝ) =
          ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      have hp : (lam : ℝ) ^ (k + 2) = (lam : ℝ) ^ (2 : ℕ) * (lam : ℝ) ^ k := by ring
      have h1 : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h3 : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [hfac, hsub, hp]
      field_simp
    simp_rw [hterm]
    rw [tsum_mul_left]
    have hexp : ∑' k : ℕ, (lam : ℝ) ^ k / (k.factorial : ℝ) = Real.exp (lam : ℝ) := by
      have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (lam : ℝ)
      rw [← Real.exp_eq_exp_ℝ] at h
      exact h.tsum_eq
    rw [hexp]
    have : Real.exp (-(lam : ℝ)) * (lam : ℝ) ^ (2 : ℕ) * Real.exp (lam : ℝ) =
        (lam : ℝ) ^ (2 : ℕ) * (Real.exp (-(lam : ℝ)) * Real.exp (lam : ℝ)) := by ring
    rw [this, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hpart1, hpart2]

/-! ### `infinitePi` block-law and disjoint-coordinate independence helpers -/

private lemma infinitePi_block_law {E : Type*} [MeasurableSpace E]
    (F : Measure E) [IsProbabilityMeasure F] (m n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => F)).map (fun y : ℕ → E => fun j : Fin n => y (m + j.val)) =
      Measure.pi (fun _ : Fin n => F) := by
  let I : Finset ℕ := (Finset.univ : Finset (Fin n)).image (fun j : Fin n => m + j.val)
  let φ : I ≃ Fin n :=
    { toFun := fun x =>
        ⟨x.1 - m, by
          obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.2
          have := j.isLt
          omega⟩
      invFun := fun j => ⟨m + j.val, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      left_inv := fun x => by
        ext
        dsimp only
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp x.2
        have := j.isLt
        omega
      right_inv := fun j => by
        ext; simp }
  have hcomp : (fun y : ℕ → E => fun j : Fin n => y (m + j.val)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) φ) ∘ I.restrict := by
    funext y j
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft]
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin n => E) φ (I.restrict y) (φ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.piCongrLeft _ φ).measurable
    (Finset.measurable_restrict I)]
  rw [Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft φ (fun _ : Fin n => F)

private lemma infinitePi_indep_range_block {E : Type*} [MeasurableSpace E]
    (F : Measure E) [IsProbabilityMeasure F] (m n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun y : ℕ → E => fun j : Fin n => y (m + j.val))
      (fun y : ℕ → E => fun j : Fin m => y j.val)
      (Measure.infinitePi (fun _ : ℕ => F)) := by
  let S : Finset ℕ := (Finset.univ : Finset (Fin n)).image (fun j : Fin n => m + j.val)
  let R : Finset ℕ := (Finset.univ : Finset (Fin m)).image (fun j : Fin m => j.val)
  have hdisj : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro x hxS hxR
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hxS
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hxR
    omega
  have hind_sr : ProbabilityTheory.IndepFun (S.restrict (π := fun _ : ℕ => E))
      (R.restrict (π := fun _ : ℕ => E)) (Measure.infinitePi (fun _ : ℕ => F)) := by
    have hlaw_union :
        (Measure.infinitePi (fun _ : ℕ => F)).map (fun y => (S.restrict y, R.restrict y)) =
          (Measure.pi (fun _ : S => F)).prod (Measure.pi (fun _ : R => F)) := by
      have hmp := MeasureTheory.measurePreserving_piFinsetUnion hdisj (fun _ : ℕ => F)
      have heq_map : (fun y : ℕ → E => (S.restrict y, R.restrict y)) =
          (MeasurableEquiv.piFinsetUnion (fun _ : ℕ => E) hdisj).symm ∘ (S ∪ R).restrict := by
        funext y
        symm
        dsimp only [Function.comp_apply]
        rw [MeasurableEquiv.symm_apply_eq]
        ext ⟨x, hx⟩
        by_cases hxS : x ∈ S
        · have hx_eq : (⟨x, hx⟩ : ↥(S ∪ R)) = Equiv.Finset.union S R hdisj (Sum.inl ⟨x, hxS⟩) := rfl
          rw [hx_eq]
          simp only [MeasurableEquiv.piFinsetUnion, MeasurableEquiv.coe_trans, Function.comp_apply,
            MeasurableEquiv.coe_piCongrLeft]
          rw [Equiv.piCongrLeft_apply_apply]
          rfl
        · have hxR : x ∈ R := (Finset.mem_union.mp hx).resolve_left hxS
          have hx_eq : (⟨x, hx⟩ : ↥(S ∪ R)) = Equiv.Finset.union S R hdisj (Sum.inr ⟨x, hxR⟩) := rfl
          rw [hx_eq]
          simp only [MeasurableEquiv.piFinsetUnion, MeasurableEquiv.coe_trans, Function.comp_apply,
            MeasurableEquiv.coe_piCongrLeft]
          rw [Equiv.piCongrLeft_apply_apply]
          rfl
      rw [heq_map, ← Measure.map_map (MeasurableEquiv.piFinsetUnion _ hdisj).symm.measurable
        (Finset.measurable_restrict (S ∪ R)), Measure.infinitePi_map_restrict]
      have hsymm := hmp.symm (MeasurableEquiv.piFinsetUnion (fun _ : ℕ => E) hdisj)
      exact hsymm.map_eq
    have hprod_eq : (Measure.infinitePi (fun _ : ℕ => F)).map (fun y => (S.restrict y, R.restrict y)) =
        ((Measure.infinitePi (fun _ : ℕ => F)).map S.restrict).prod
          ((Measure.infinitePi (fun _ : ℕ => F)).map R.restrict) := by
      rw [hlaw_union, Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (Finset.measurable_restrict S).aemeasurable
      (Finset.measurable_restrict R).aemeasurable).mpr hprod_eq
  let fS : (S → E) → (Fin n → E) := fun z j => z ⟨m + j.val, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  let fR : (R → E) → (Fin m → E) := fun z j => z ⟨j.val, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hfS : Measurable fS := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hfR : Measurable fR := measurable_pi_lambda _ fun j => measurable_pi_apply _
  exact hind_sr.comp hfS hfR

private lemma exists_compound_poisson_rdLevy {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (hμ : μ Set.univ < ⊤) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ L : RdLevyProcess d Ω P,
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I * ((innerRd θ (L.X t ω) : ℝ) : ℂ)) ∂P =
              Complex.exp (-(t : ℝ) * ∫ x, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) ∂μ)) ∧
          ((∀ᵐ x ∂μ, ∀ i : Fin d, |x i| ≤ 1) →
            ∀ (t : ℝ≥0) (i : Fin d),
              Integrable (fun ω => L.X t ω i) P ∧
              ∫ ω, L.X t ω i ∂P = (t : ℝ) * ∫ x, x i ∂μ ∧
              Integrable (fun ω => (L.X t ω i - (t : ℝ) * ∫ x, x i ∂μ) ^ (2 : ℕ)) P ∧
              ∫ ω, (L.X t ω i - (t : ℝ) * ∫ x, x i ∂μ) ^ (2 : ℕ) ∂P =
                (t : ℝ) * ∫ x, (x i) ^ (2 : ℕ) ∂μ) := by
  haveI : IsFiniteMeasure μ := ⟨hμ⟩
  by_cases hμ0 : μ Set.univ = 0
  · have hμ_zero : μ = 0 := Measure.measure_univ_eq_zero.mp hμ0
    refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
      deterministic_drift_rdLevy 0, fun t θ => ?_, fun _ t i => ?_⟩
    · subst hμ_zero
      simp [deterministic_drift_rdLevy, innerRd]
    · subst hμ_zero
      refine ⟨?_, by simp [deterministic_drift_rdLevy], ?_, by simp [deterministic_drift_rdLevy]⟩
      · simpa [deterministic_drift_rdLevy] using integrable_const (0 : ℝ)
      · simpa [deterministic_drift_rdLevy] using integrable_const (0 : ℝ)
  · let r : ℝ≥0 := (μ Set.univ).toNNReal
    have hr_coe : (r : ℝ≥0∞) = μ Set.univ := ENNReal.coe_toNNReal hμ.ne
    let F : Measure (Fin d → ℝ) := (μ Set.univ)⁻¹ • μ
    have hF_prob : IsProbabilityMeasure F := by
      refine ⟨?_⟩
      simp only [F, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hμ0 hμ.ne
    have hμ_eq_smul : μ = (r : ℝ≥0∞) • F := by
      simp only [F, hr_coe, smul_smul]
      rw [ENNReal.mul_inv_cancel hμ0 hμ.ne, one_smul]
    obtain ⟨ΩN, mN, PN, hPN, ⟨CP⟩⟩ := exists_cadlag_poisson_counting r
    letI : MeasurableSpace ΩN := mN
    letI : IsProbabilityMeasure PN := hPN
    let ΩY := ℕ → (Fin d → ℝ)
    let PY : Measure ΩY := Measure.infinitePi (fun _ : ℕ => F)
    have hPY_prob : IsProbabilityMeasure PY := inferInstance
    let Ω := ΩN × ΩY
    let P : Measure Ω := PN.prod PY
    let X : ℝ≥0 → Ω → (Fin d → ℝ) := fun t ω => ∑ k ∈ Finset.range (CP.C t ω.1), ω.2 k
    have hsum_meas : ∀ n : ℕ, Measurable (fun y : ΩY => ∑ k ∈ Finset.range n, y k) := fun n =>
      Finset.measurable_sum _ fun k _ => measurable_pi_apply k
    have hX_meas : ∀ t : ℝ≥0, Measurable (X t) := fun t => by
      have hpair : Measurable (fun p : ℕ × ΩY => ∑ k ∈ Finset.range p.1, p.2 k) :=
        measurable_from_prod_countable_right hsum_meas
      exact hpair.comp ((CP.measurable t).comp measurable_fst |>.prodMk measurable_snd)
    have hX_incr : ∀ {s t : ℝ≥0}, s ≤ t → ∀ ω : Ω,
        X t ω - X s ω = ∑ k ∈ Finset.range (CP.C t ω.1 - CP.C s ω.1), ω.2 (CP.C s ω.1 + k) := by
      intro s t hst ω
      have hle : CP.C s ω.1 ≤ CP.C t ω.1 := CP.mono ω.1 hst
      have hadd : CP.C s ω.1 + (CP.C t ω.1 - CP.C s ω.1) = CP.C t ω.1 := Nat.add_sub_of_le hle
      have hs : X t ω = X s ω + ∑ k ∈ Finset.range (CP.C t ω.1 - CP.C s ω.1), ω.2 (CP.C s ω.1 + k) := by
        simp only [X]
        conv_lhs => rw [← hadd, Finset.sum_range_add]
      rw [hs, add_sub_cancel_left]
    -- Block-sum measure depends only on increment length `n`, independent of offset `m`
    have hblock_sum_eq : ∀ (A : Set (Fin d → ℝ)), MeasurableSet A → ∀ (m n : ℕ),
        PY { y : ΩY | (∑ k ∈ Finset.range n, y (m + k)) ∈ A } =
          (Measure.pi (fun _ : Fin n => F)) { z : Fin n → (Fin d → ℝ) | (∑ j : Fin n, z j) ∈ A } := by
      intro A hA m n
      have hmeas_sum : Measurable (fun z : Fin n → (Fin d → ℝ) => ∑ j : Fin n, z j) :=
        Finset.measurable_sum _ fun j _ => measurable_pi_apply j
      have hmeas_block : Measurable (fun y : ΩY => fun j : Fin n => y (m + j.val)) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply (m + j.val)
      have hpre : { y : ΩY | (∑ k ∈ Finset.range n, y (m + k)) ∈ A } =
          (fun y : ΩY => fun j : Fin n => y (m + j.val)) ⁻¹'
            ((fun z : Fin n → (Fin d → ℝ) => ∑ j : Fin n, z j) ⁻¹' A) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [Fin.sum_univ_eq_sum_range (fun k => y (m + k)) n]
      rw [hpre, ← Measure.map_apply hmeas_block (hmeas_sum hA), infinitePi_block_law F m n]
      rfl
    -- Stationary increments
    have hX_stat : ∀ {s t : ℝ≥0}, s ≤ t → P.map (fun ω => X t ω - X s ω) = P.map (X (t - s)) := by
      intro s t hst
      have hmeas_sub : Measurable (fun ω : Ω => X t ω - X s ω) := (hX_meas t).sub (hX_meas s)
      ext A hA
      rw [Measure.map_apply hmeas_sub hA, Measure.map_apply (hX_meas (t - s)) hA]
      rw [Measure.prod_apply (hmeas_sub hA), Measure.prod_apply ((hX_meas (t - s)) hA)]
      let g : ℕ → ℝ≥0∞ := fun n =>
        (Measure.pi (fun _ : Fin n => F)) { z : Fin n → (Fin d → ℝ) | (∑ j : Fin n, z j) ∈ A }
      have hLHS : ∀ ωN : ΩN,
          PY (Prod.mk ωN ⁻¹' ((fun ω => X t ω - X s ω) ⁻¹' A)) = g (CP.C t ωN - CP.C s ωN) := by
        intro ωN
        have hset : Prod.mk ωN ⁻¹' ((fun ω => X t ω - X s ω) ⁻¹' A) =
            { y : ΩY | (∑ k ∈ Finset.range (CP.C t ωN - CP.C s ωN), y (CP.C s ωN + k)) ∈ A } := by
          ext y; simp [hX_incr hst (ωN, y)]
        rw [hset]
        exact hblock_sum_eq A hA (CP.C s ωN) (CP.C t ωN - CP.C s ωN)
      have hRHS : ∀ ωN : ΩN,
          PY (Prod.mk ωN ⁻¹' (X (t - s) ⁻¹' A)) = g (CP.C (t - s) ωN) := by
        intro ωN
        have hset : Prod.mk ωN ⁻¹' (X (t - s) ⁻¹' A) =
            { y : ΩY | (∑ k ∈ Finset.range (CP.C (t - s) ωN), y (0 + k)) ∈ A } := by
          ext y; simp [X]
        rw [hset]
        exact hblock_sum_eq A hA 0 (CP.C (t - s) ωN)
      rw [lintegral_congr hLHS, lintegral_congr hRHS]
      have hC_sub_meas : Measurable (fun ωN => CP.C t ωN - CP.C s ωN) :=
        (CP.measurable t).sub (CP.measurable s)
      rw [← lintegral_map (Measurable.of_discrete) hC_sub_meas,
        ← lintegral_map (Measurable.of_discrete) (CP.measurable (t - s))]
      rw [CP.incr_law s t hst]
      have h0 : CP.C (t - s) = fun ωN => CP.C (t - s) ωN - CP.C 0 ωN := by
        funext ωN; simp [CP.start_zero ωN]
      rw [h0, CP.incr_law 0 (t - s) bot_le, tsub_zero]
    -- Independent increments
    have hX_indep : ∀ {s t : ℝ≥0}, s ≤ t →
        ProbabilityTheory.Indep
          (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance)
          (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (X u) inferInstance) P := by
      intro s t hst
      refine indep_past_of_finset hX_meas ((hX_meas t).sub (hX_meas s)) fun p u hu => ?_
      rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
      intro A B hA hB
      have hmeas_past : Measurable (fun ω : Ω => fun j : Fin p => X (u j) ω) :=
        measurable_pi_lambda _ fun j => hX_meas (u j)
      have hmeas_inc : Measurable (fun ω : Ω => X t ω - X s ω) :=
        (hX_meas t).sub (hX_meas s)
      rw [Measure.prod_apply ((hmeas_inc hA).inter (hmeas_past hB)),
        Measure.prod_apply (hmeas_inc hA), Measure.prod_apply (hmeas_past hB)]
      let g : ℕ → ℝ≥0∞ := fun n =>
        (Measure.pi (fun _ : Fin n => F)) { z : Fin n → (Fin d → ℝ) | (∑ j : Fin n, z j) ∈ A }
      let h_past : (Fin p → ℕ) → ℝ≥0∞ := fun c =>
        PY { y : ΩY | (fun j : Fin p => ∑ k ∈ Finset.range (c j), y k) ∈ B }
      have hslice_inc : ∀ ωN : ΩN,
          PY (Prod.mk ωN ⁻¹' ((fun ω => X t ω - X s ω) ⁻¹' A)) = g (CP.C t ωN - CP.C s ωN) := by
        intro ωN
        have hset : Prod.mk ωN ⁻¹' ((fun ω => X t ω - X s ω) ⁻¹' A) =
            { y : ΩY | (∑ k ∈ Finset.range (CP.C t ωN - CP.C s ωN), y (CP.C s ωN + k)) ∈ A } := by
          ext y; simp [hX_incr hst (ωN, y)]
        rw [hset]
        exact hblock_sum_eq A hA (CP.C s ωN) (CP.C t ωN - CP.C s ωN)
      have hslice_past : ∀ ωN : ΩN,
          PY (Prod.mk ωN ⁻¹' ((fun ω => fun j : Fin p => X (u j) ω) ⁻¹' B)) =
            h_past (fun j : Fin p => CP.C (u j) ωN) := fun ωN => rfl
      have hslice_inter : ∀ ωN : ΩN,
          PY (Prod.mk ωN ⁻¹' (((fun ω => X t ω - X s ω) ⁻¹' A) ∩
            ((fun ω => fun j : Fin p => X (u j) ω) ⁻¹' B))) =
            g (CP.C t ωN - CP.C s ωN) * h_past (fun j : Fin p => CP.C (u j) ωN) := by
        intro ωN
        let m := CP.C s ωN
        let n := CP.C t ωN - CP.C s ωN
        let fInc : (Fin n → (Fin d → ℝ)) → (Fin d → ℝ) := fun z => ∑ j : Fin n, z j
        let fPast : (Fin m → (Fin d → ℝ)) → (Fin p → (Fin d → ℝ)) := fun z j =>
          ∑ k ∈ Finset.range (CP.C (u j) ωN),
            if hk : k < m then z ⟨k, hk⟩ else 0
        have hfInc : Measurable fInc := Finset.measurable_sum _ fun j _ => measurable_pi_apply j
        have hfPast : Measurable fPast := by
          refine measurable_pi_lambda _ fun j => Finset.measurable_sum _ fun k _ => ?_
          split_ifs with hk
          · exact measurable_pi_apply (⟨k, hk⟩ : Fin m)
          · exact measurable_const
        have hind_y : ProbabilityTheory.IndepFun
            (fInc ∘ fun y : ΩY => fun j : Fin n => y (m + j.val))
            (fPast ∘ fun y : ΩY => fun j : Fin m => y j.val) PY :=
          (infinitePi_indep_range_block F m n).comp hfInc hfPast
        have heq1 : Prod.mk ωN ⁻¹' ((fun ω => X t ω - X s ω) ⁻¹' A) =
            (fInc ∘ fun y : ΩY => fun j : Fin n => y (m + j.val)) ⁻¹' A := by
          ext y
          simp only [Set.mem_preimage, Function.comp_apply, fInc, hX_incr hst (ωN, y)]
          rw [Fin.sum_univ_eq_sum_range (fun k => y (m + k)) n]
        have heq2 : Prod.mk ωN ⁻¹' ((fun ω => fun j : Fin p => X (u j) ω) ⁻¹' B) =
            (fPast ∘ fun y : ΩY => fun j : Fin m => y j.val) ⁻¹' B := by
          ext y
          simp only [Set.mem_preimage, Function.comp_apply, fPast, X]
          have heq_fn : (fun j : Fin p => ∑ k ∈ Finset.range (CP.C (u j) ωN), y k) =
              (fun j : Fin p => ∑ k ∈ Finset.range (CP.C (u j) ωN), if hk : k < m then y k else 0) := by
            funext j
            refine Finset.sum_congr rfl fun k hk => ?_
            have hku : k < CP.C (u j) ωN := Finset.mem_range.mp hk
            have hum : CP.C (u j) ωN ≤ m := CP.mono ωN (hu j)
            rw [dif_pos (lt_of_lt_of_le hku hum)]
          rw [heq_fn]
        rw [Set.preimage_inter, heq1, heq2,
          (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.mp hind_y) A B hA hB,
          ← heq1, ← heq2, hslice_inc ωN, hslice_past ωN]
      rw [lintegral_congr hslice_inter, lintegral_congr hslice_inc, lintegral_congr hslice_past]
      -- Convert bounded [0,1] ENNReal lintegral of product of independent functions to real integral
      have hg_le1 : ∀ n, g n ≤ 1 := fun n => by
        calc g n ≤ (Measure.pi (fun _ : Fin n => F)) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hh_le1 : ∀ c, h_past c ≤ 1 := fun c => by
        calc h_past c ≤ PY Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hC_sub_meas : Measurable (fun ωN => CP.C t ωN - CP.C s ωN) :=
        (CP.measurable t).sub (CP.measurable s)
      have hmeas_g : Measurable (fun ωN => g (CP.C t ωN - CP.C s ωN)) :=
        (Measurable.of_discrete : Measurable g).comp hC_sub_meas
      have hmeas_h : Measurable (fun ωN => h_past (fun j : Fin p => CP.C (u j) ωN)) :=
        (Measurable.of_discrete : Measurable h_past).comp
          (measurable_pi_lambda _ fun j => CP.measurable (u j))
      have hmeas_gh : Measurable (fun ωN => g (CP.C t ωN - CP.C s ωN) *
          h_past (fun j : Fin p => CP.C (u j) ωN)) := hmeas_g.mul hmeas_h
      have hind_N : ProbabilityTheory.IndepFun
          (fun ωN => (g (CP.C t ωN - CP.C s ωN)).toReal)
          (fun ωN => (h_past (fun j : Fin p => CP.C (u j) ωN)).toReal) PN := by
        have hbase : ProbabilityTheory.IndepFun
            (fun ωN => CP.C t ωN - CP.C s ωN)
            (fun ωN => fun j : Fin p => CP.C (u j) ωN) PN := by
          rw [ProbabilityTheory.IndepFun_iff_Indep]
          refine indep_of_indep_of_le_right (CP.indep_incr s t hst) ?_
          rw [MeasurableSpace.comap_le_iff_le_map]
          have hm : @Measurable ΩN (Fin p → ℕ)
              (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (CP.C v) inferInstance) inferInstance
              (fun ωN => fun j : Fin p => CP.C (u j) ωN) := by
            refine @measurable_pi_lambda ΩN (Fin p) _
              (⨆ v ∈ Set.Iic s, MeasurableSpace.comap (CP.C v) inferInstance) _ _ fun j => ?_
            exact (comap_measurable (CP.C (u j))).mono (le_iSup₂_of_le (u j) (hu j) le_rfl) le_rfl
          exact fun S hS => hm hS
        exact hbase.comp (Measurable.of_discrete : Measurable fun n => (g n).toReal)
          (Measurable.of_discrete : Measurable fun c => (h_past c).toReal)
      have hmul_real := hind_N.integral_fun_mul_eq_mul_integral
        hmeas_g.ennreal_toReal.aestronglyMeasurable
        hmeas_h.ennreal_toReal.aestronglyMeasurable
      have hconv : ∀ (f : ΩN → ℝ≥0∞), Measurable f → (∀ ωN, f ωN ≤ 1) →
          ∫⁻ ωN, f ωN ∂PN = ENNReal.ofReal (∫ ωN, (f ωN).toReal ∂PN) := by
        intro f hf hle1
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
        · refine lintegral_congr fun ωN =>
            (ENNReal.ofReal_toReal (lt_of_le_of_lt (hle1 ωN) ENNReal.one_lt_top).ne).symm
        · refine Integrable.of_bound hf.ennreal_toReal.aestronglyMeasurable 1
            (Filter.Eventually.of_forall fun ωN => ?_)
          rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle1 ωN)
        · exact Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
      rw [hconv _ hmeas_gh (fun ωN => by
            calc g (CP.C t ωN - CP.C s ωN) * h_past (fun j : Fin p => CP.C (u j) ωN)
                ≤ 1 * 1 := mul_le_mul' (hg_le1 _) (hh_le1 _)
              _ = 1 := mul_one 1),
        hconv _ hmeas_g (fun ωN => hg_le1 _),
        hconv _ hmeas_h (fun ωN => hh_le1 _)]
      have htoReal_mul : (fun ωN => (g (CP.C t ωN - CP.C s ωN) * h_past (fun j : Fin p => CP.C (u j) ωN)).toReal) =
          fun ωN => (g (CP.C t ωN - CP.C s ωN)).toReal * (h_past (fun j : Fin p => CP.C (u j) ωN)).toReal := by
        funext ωN; exact ENNReal.toReal_mul
      rw [htoReal_mul, hmul_real, ENNReal.ofReal_mul (integral_nonneg fun _ => ENNReal.toReal_nonneg)]
    -- Assemble RdLevyProcess
    let L : RdLevyProcess d Ω P :=
      { X := X
        measurable := hX_meas
        cadlag := Filter.Eventually.of_forall fun ω => by
          refine ⟨fun t => ?_, fun t ht => ?_⟩
          · obtain ⟨δ, hδ_pos, hδ⟩ := CP.right_const ω.1 t
            refine continuousWithinAt_const.congr_of_eventuallyEq ?_ rfl
            have hmem : Set.Ico t (t + δ) ∈ nhdsWithin t (Set.Ici t) := by
              rw [mem_nhdsWithin]
              refine ⟨Set.Iio (t + δ), isOpen_Iio, lt_add_of_pos_right t hδ_pos, ?_⟩
              intro u ⟨hu1, hu2⟩
              exact ⟨hu2, hu1⟩
            filter_upwards [hmem] with u hu
            simp only [X, hδ u hu.1 (le_of_lt hu.2)]
          · obtain ⟨s, hst, hs⟩ := CP.left_const ω.1 t ht
            refine ⟨X s ω, tendsto_const_nhds.congr' ?_⟩
            have hmem : Set.Ioo s t ∈ nhdsWithin t (Set.Iio t) := by
              rw [mem_nhdsWithin]
              refine ⟨Set.Ioi s, isOpen_Ioi, hst, fun u ⟨hu1, hu2⟩ => ⟨hu1, hu2⟩⟩
            filter_upwards [hmem] with u hu
            simp only [X, hs u (le_of_lt hu.1) hu.2]
        start_zero := Filter.Eventually.of_forall fun ω => by
          simp [X, CP.start_zero ω.1]
        indep_increments := fun s t hst => hX_indep hst
        stationary_increments := fun s t hst => hX_stat hst }
    refine ⟨Ω, inferInstance, P, inferInstance, L, ?_, ?_⟩
    · -- Characteristic function
      intro t θ
      have hcont_exp : Continuous (fun x : Fin d → ℝ =>
          Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) := by
        unfold innerRd; fun_prop
      have hint_prod : Integrable (fun ω : Ω =>
          Complex.exp (Complex.I * ((innerRd θ (X t ω) : ℝ) : ℂ))) P :=
        Integrable.of_bound (hcont_exp.measurable.comp (hX_meas t)).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω => by
            rw [Complex.norm_exp_I_mul_ofReal])
      rw [MeasureTheory.integral_prod _ hint_prod]
      let φ : ℂ := ∫ x, Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) ∂F
      have hφ_norm : ‖φ‖ ≤ 1 := by
        calc ‖φ‖ ≤ ∫ x, ‖Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))‖ ∂F :=
              norm_integral_le_integral_norm _
          _ = ∫ _ : Fin d → ℝ, (1 : ℝ) ∂F := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
              dsimp only
              rw [Complex.norm_exp_I_mul_ofReal]
          _ = 1 := by simp
      have hinner_n : ∀ n : ℕ,
          ∫ y : ΩY, Complex.exp (Complex.I * ((innerRd θ (∑ k ∈ Finset.range n, y k) : ℝ) : ℂ)) ∂PY =
            φ ^ n := by
        intro n
        have hprod_exp : ∀ y : ΩY,
            Complex.exp (Complex.I * ((innerRd θ (∑ k ∈ Finset.range n, y k) : ℝ) : ℂ)) =
              ∏ k : Fin n, Complex.exp (Complex.I * ((innerRd θ (y k.val) : ℝ) : ℂ)) := by
          intro y
          have hlin : innerRd θ (∑ k ∈ Finset.range n, y k) =
              ∑ k : Fin n, innerRd θ (y k.val) := by
            rw [Fin.sum_univ_eq_sum_range (fun k => innerRd θ (y k)) n]
            simp only [innerRd, Finset.sum_apply, Finset.mul_sum]
            exact Finset.sum_comm
          rw [hlin, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
        simp_rw [hprod_exp]
        have hind_all : ProbabilityTheory.iIndepFun
            (fun (k : ℕ) (y : ΩY) => Complex.exp (Complex.I * ((innerRd θ (y k) : ℝ) : ℂ))) PY :=
          ProbabilityTheory.iIndepFun_infinitePi fun _ => hcont_exp.measurable
        have hind_fin : ProbabilityTheory.iIndepFun
            (fun (k : Fin n) (y : ΩY) => Complex.exp (Complex.I * ((innerRd θ (y k.val) : ℝ) : ℂ))) PY :=
          hind_all.precomp Fin.val_injective
        rw [hind_fin.integral_fun_prod_eq_prod_integral (fun k =>
          (hcont_exp.measurable.comp (measurable_pi_apply k.val)).aestronglyMeasurable)]
        have hfactor : ∀ k : Fin n,
            ∫ y : ΩY, Complex.exp (Complex.I * ((innerRd θ (y k.val) : ℝ) : ℂ)) ∂PY = φ := by
          intro k
          have hmap : PY.map (fun y : ΩY => y k.val) = F := Measure.infinitePi_map_eval _ k.val
          dsimp only [φ]
          rw [← hmap, integral_map (measurable_pi_apply k.val).aemeasurable hcont_exp.aestronglyMeasurable]
        simp_rw [hfactor]
        simp
      have hslice : ∀ ωN : ΩN,
          ∫ y : ΩY, Complex.exp (Complex.I * ((innerRd θ (X t (ωN, y)) : ℝ) : ℂ)) ∂PY =
            φ ^ (CP.C t ωN) := fun ωN => hinner_n (CP.C t ωN)
      simp_rw [hslice]
      have hlaw_Ct : PN.map (CP.C t) = ProbabilityTheory.poissonMeasure (r * t) := by
        have h0 : CP.C t = fun ωN => CP.C t ωN - CP.C 0 ωN := by
          funext ωN; simp [CP.start_zero ωN]
        rw [h0, CP.incr_law 0 t bot_le, tsub_zero]
      rw [← integral_map (CP.measurable t).aemeasurable (Measurable.of_discrete.aestronglyMeasurable),
        hlaw_Ct, poissonMeasure_integral_pow (r * t) φ hφ_norm]
      congr 1
      have hμ_int : ∫ x, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) ∂μ =
          ((r : ℝ) : ℂ) * (1 - φ) := by
        rw [hμ_eq_smul, integral_smul_measure]
        simp only [ENNReal.coe_toReal, Complex.real_smul]
        congr 1
        have hint_1 : Integrable (fun _ : Fin d → ℝ => (1 : ℂ)) F := integrable_const 1
        have hint_e : Integrable (fun x : Fin d → ℝ =>
            Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) F :=
          Integrable.of_bound hcont_exp.aestronglyMeasurable 1
            (Filter.Eventually.of_forall fun x => by rw [Complex.norm_exp_I_mul_ofReal])
        rw [integral_sub hint_1 hint_e, integral_const, probReal_univ, one_smul]
      rw [hμ_int]
      push_cast
      ring
    · -- First and second moments when marks are bounded by 1 a.e.
      intro hbdd t i
      have hbdd_F : ∀ᵐ x ∂F, |x i| ≤ 1 := by
        have h0 : μ {x | ¬ |x i| ≤ 1} = 0 := ae_iff.mp (hbdd.mono fun x hx => hx i)
        rw [ae_iff]
        simp only [F, Measure.smul_apply, smul_eq_mul, h0, mul_zero]
      have hF_int_x : Integrable (fun x : Fin d → ℝ => x i) F := by
        refine Integrable.of_bound (continuous_apply i).aestronglyMeasurable 1 ?_
        filter_upwards [hbdd_F] with x hx
        simpa [Real.norm_eq_abs] using hx
      have hF_int_x2 : Integrable (fun x : Fin d → ℝ => (x i) ^ (2 : ℕ)) F := by
        refine Integrable.of_bound ((continuous_apply i).pow 2).aestronglyMeasurable 1 ?_
        filter_upwards [hbdd_F] with x hx
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [abs_nonneg (x i), sq_abs (x i)]
      let m₁ : ℝ := ∫ x, x i ∂F
      let m₂ : ℝ := ∫ x, (x i) ^ (2 : ℕ) ∂F
      have hlaw_Ct : PN.map (CP.C t) = ProbabilityTheory.poissonMeasure (r * t) := by
        have h0 : CP.C t = fun ωN => CP.C t ωN - CP.C 0 ωN := by
          funext ωN; simp [CP.start_zero ωN]
        rw [h0, CP.incr_law 0 t bot_le, tsub_zero]
      have hCN_int : Integrable (fun ωN => (CP.C t ωN : ℝ)) PN := by
        have h := poissonMeasure_integrable_nat (r * t)
        rw [← hlaw_Ct] at h
        exact h.comp_measurable (CP.measurable t)
      have hCN_int2 : Integrable (fun ωN => ((CP.C t ωN : ℝ) ^ (2 : ℕ))) PN := by
        have h := poissonMeasure_integrable_nat_sq (r * t)
        rw [← hlaw_Ct] at h
        exact h.comp_measurable (CP.measurable t)
      have hCN_mean : ∫ ωN, (CP.C t ωN : ℝ) ∂PN = (r : ℝ) * (t : ℝ) := by
        have h := poissonMeasure_integral_nat (r * t)
        rw [← hlaw_Ct, integral_map (CP.measurable t).aemeasurable
          (Measurable.of_discrete.aestronglyMeasurable)] at h
        simpa using h
      have hCN_sq : ∫ ωN, ((CP.C t ωN : ℝ) ^ (2 : ℕ)) ∂PN =
          (r : ℝ) * (t : ℝ) + ((r : ℝ) * (t : ℝ)) ^ (2 : ℕ) := by
        have h := poissonMeasure_integral_nat_sq (r * t)
        rw [← hlaw_Ct, integral_map (CP.measurable t).aemeasurable
          (Measurable.of_discrete.aestronglyMeasurable)] at h
        simpa using h
      have hbdd_PY : ∀ᵐ y ∂PY, ∀ k : ℕ, |y k i| ≤ 1 := by
        rw [ae_all_iff]
        intro k
        have hmap : PY.map (fun y : ΩY => y k) = F := Measure.infinitePi_map_eval _ k
        rw [← hmap] at hbdd_F
        exact ae_of_ae_map (measurable_pi_apply k).aemeasurable hbdd_F
      have hbdd_P : ∀ᵐ ω ∂P, |L.X t ω i| ≤ (CP.C t ω.1 : ℝ) := by
        have h2 : ∀ᵐ ω ∂P, ∀ k : ℕ, |ω.2 k i| ≤ 1 :=
          Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd (μ := PN) (ν := PY)) hbdd_PY
        filter_upwards [h2] with ω hω
        simp only [L, X, Finset.sum_apply]
        calc |∑ k ∈ Finset.range (CP.C t ω.1), ω.2 k i|
            ≤ ∑ k ∈ Finset.range (CP.C t ω.1), |ω.2 k i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ Finset.range (CP.C t ω.1), (1 : ℝ) := Finset.sum_le_sum fun k _ => hω k
          _ = (CP.C t ω.1 : ℝ) := by simp
      have hX_int : Integrable (fun ω => L.X t ω i) P := by
        have hdom : Integrable (fun ω : Ω => (CP.C t ω.1 : ℝ)) P :=
          hCN_int.comp_fst PY
        refine hdom.mono' ((continuous_apply i).measurable.comp (hX_meas t)).aestronglyMeasurable ?_
        filter_upwards [hbdd_P] with ω hω
        simpa [Real.norm_eq_abs] using hω
      have hX_int2 : Integrable (fun ω => (L.X t ω i) ^ (2 : ℕ)) P := by
        have hdom : Integrable (fun ω : Ω => ((CP.C t ω.1 : ℝ) ^ (2 : ℕ))) P :=
          hCN_int2.comp_fst PY
        refine hdom.mono' (((continuous_apply i).pow 2).measurable.comp (hX_meas t)).aestronglyMeasurable ?_
        filter_upwards [hbdd_P] with ω hω
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [abs_nonneg (L.X t ω i), sq_abs (L.X t ω i)]
      -- Slice moments on PY
      have hPY_eval_int : ∀ k : ℕ, Integrable (fun y : ΩY => y k i) PY := fun k => by
        have hmap : PY.map (fun y : ΩY => y k) = F := Measure.infinitePi_map_eval _ k
        rw [← hmap] at hF_int_x
        exact hF_int_x.comp_measurable (measurable_pi_apply k)
      have hPY_eval_int2 : ∀ k : ℕ, Integrable (fun y : ΩY => (y k i) ^ (2 : ℕ)) PY := fun k => by
        have hmap : PY.map (fun y : ΩY => y k) = F := Measure.infinitePi_map_eval _ k
        rw [← hmap] at hF_int_x2
        exact hF_int_x2.comp_measurable (measurable_pi_apply k)
      have hPY_eval_mean : ∀ k : ℕ, ∫ y : ΩY, y k i ∂PY = m₁ := fun k => by
        have hmap : PY.map (fun y : ΩY => y k) = F := Measure.infinitePi_map_eval _ k
        dsimp only [m₁]
        rw [← hmap, integral_map (measurable_pi_apply k).aemeasurable (continuous_apply i).aestronglyMeasurable]
      have hPY_eval_sq : ∀ k : ℕ, ∫ y : ΩY, (y k i) ^ (2 : ℕ) ∂PY = m₂ := fun k => by
        have hmap : PY.map (fun y : ΩY => y k) = F := Measure.infinitePi_map_eval _ k
        dsimp only [m₂]
        rw [← hmap, integral_map (measurable_pi_apply k).aemeasurable ((continuous_apply i).pow 2).aestronglyMeasurable]
      have hPY_sum_mean : ∀ n : ℕ, ∫ y : ΩY, (∑ k ∈ Finset.range n, y k i) ∂PY = (n : ℝ) * m₁ := by
        intro n
        rw [integral_finset_sum _ fun k _ => hPY_eval_int k]
        simp_rw [hPY_eval_mean]
        simp
      have hPY_sum_sq : ∀ n : ℕ,
          ∫ y : ΩY, (∑ k ∈ Finset.range n, y k i) ^ (2 : ℕ) ∂PY =
            (n : ℝ) * m₂ + ((n : ℝ) ^ (2 : ℕ) - (n : ℝ)) * m₁ ^ (2 : ℕ) := by
        intro n
        have hexpand : ∀ y : ΩY,
            (∑ k ∈ Finset.range n, y k i) ^ (2 : ℕ) =
              ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, y j i * y k i := fun y => by
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
        simp_rw [hexpand]
        have hmeas_coord : ∀ k : ℕ, Measurable (fun y : ΩY => y k i) := fun k => by
          have hk : Measurable (fun y : ΩY => y k) := measurable_pi_apply k
          exact (continuous_apply i).measurable.comp hk
        have hint_jk : ∀ j k : ℕ, Integrable (fun y : ΩY => y j i * y k i) PY := fun j k => by
          refine Integrable.of_bound ((hmeas_coord j).mul (hmeas_coord k)).aestronglyMeasurable 1 ?_
          filter_upwards [hbdd_PY] with y hy
          rw [Real.norm_eq_abs, abs_mul]
          calc |y j i| * |y k i| ≤ 1 * 1 := mul_le_mul (hy j) (hy k) (abs_nonneg _) zero_le_one
            _ = 1 := mul_one 1
        rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hint_jk j k]
        have hinner : ∀ j ∈ Finset.range n,
            ∫ y : ΩY, (∑ k ∈ Finset.range n, y j i * y k i) ∂PY =
              m₂ + ((n : ℝ) - 1) * m₁ ^ (2 : ℕ) := by
          intro j hj
          rw [integral_finset_sum _ fun k _ => hint_jk j k]
          have hpair : ∀ k ∈ Finset.range n,
              ∫ y : ΩY, y j i * y k i ∂PY = if k = j then m₂ else m₁ ^ (2 : ℕ) := by
            intro k _
            split_ifs with hkj
            · subst hkj
              simpa [sq] using hPY_eval_sq k
            · have hind : ProbabilityTheory.IndepFun (fun y : ΩY => y j i) (fun y : ΩY => y k i) PY :=
                (ProbabilityTheory.iIndepFun_infinitePi (fun _ => (continuous_apply i).measurable)).indepFun
                  (Ne.symm hkj)
              rw [hind.integral_fun_mul_eq_mul_integral
                (hmeas_coord j).aestronglyMeasurable (hmeas_coord k).aestronglyMeasurable,
                hPY_eval_mean j, hPY_eval_mean k, sq]
          rw [Finset.sum_congr rfl hpair, ← Finset.add_sum_erase _ _ hj, if_pos rfl]
          have herase : ∑ k ∈ (Finset.range n).erase j, (if k = j then m₂ else m₁ ^ (2 : ℕ)) =
              ∑ _k ∈ (Finset.range n).erase j, m₁ ^ (2 : ℕ) :=
            Finset.sum_congr rfl fun k hk => if_neg (Finset.ne_of_mem_erase hk)
          rw [herase]
          have hcard : ((Finset.range n).erase j).card = n - 1 := by
            rw [Finset.card_erase_of_mem hj, Finset.card_range]
          have hn1 : 1 ≤ n := by
            have := Finset.mem_range.mp hj; omega
          simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_sub hn1, Nat.cast_one]
        rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      -- Compute E[X t _ i] and E[(X t _ i)^2]
      have hμ_m1 : ∫ x, x i ∂μ = (r : ℝ) * m₁ := by
        rw [hμ_eq_smul, integral_smul_measure]
        simp [m₁]
      have hμ_m2 : ∫ x, (x i) ^ (2 : ℕ) ∂μ = (r : ℝ) * m₂ := by
        rw [hμ_eq_smul, integral_smul_measure]
        simp [m₂]
      have hEX : ∫ ω, L.X t ω i ∂P = (t : ℝ) * ∫ x, x i ∂μ := by
        rw [MeasureTheory.integral_prod _ hX_int]
        have hsl : ∀ ωN : ΩN, ∫ y : ΩY, L.X t (ωN, y) i ∂PY = (CP.C t ωN : ℝ) * m₁ := fun ωN => by
          simp only [L, X, Finset.sum_apply]
          exact hPY_sum_mean (CP.C t ωN)
        simp_rw [hsl]
        rw [integral_mul_const, hCN_mean, hμ_m1]
        ring
      have hEX2 : ∫ ω, (L.X t ω i) ^ (2 : ℕ) ∂P =
          (t : ℝ) * ∫ x, (x i) ^ (2 : ℕ) ∂μ + ((t : ℝ) * ∫ x, x i ∂μ) ^ (2 : ℕ) := by
        rw [MeasureTheory.integral_prod _ hX_int2]
        have hsl : ∀ ωN : ΩN, ∫ y : ΩY, (L.X t (ωN, y) i) ^ (2 : ℕ) ∂PY =
            (CP.C t ωN : ℝ) * m₂ + (((CP.C t ωN : ℝ) ^ (2 : ℕ)) - (CP.C t ωN : ℝ)) * m₁ ^ (2 : ℕ) := fun ωN => by
          simp only [L, X, Finset.sum_apply]
          exact hPY_sum_sq (CP.C t ωN)
        simp_rw [hsl]
        have hint_a : Integrable (fun ωN => (CP.C t ωN : ℝ) * m₂) PN := hCN_int.mul_const m₂
        have hint_b : Integrable (fun ωN => (((CP.C t ωN : ℝ) ^ (2 : ℕ)) - (CP.C t ωN : ℝ)) * m₁ ^ (2 : ℕ)) PN :=
          (hCN_int2.sub hCN_int).mul_const (m₁ ^ (2 : ℕ))
        rw [integral_add hint_a hint_b, integral_mul_const, integral_mul_const,
          integral_sub hCN_int2 hCN_int, hCN_mean, hCN_sq, hμ_m1, hμ_m2]
        ring
      let c : ℝ := (t : ℝ) * ∫ x, x i ∂μ
      have hX_sub_int2 : Integrable (fun ω => (L.X t ω i - c) ^ (2 : ℕ)) P := by
        have heq : (fun ω => (L.X t ω i - c) ^ (2 : ℕ)) =
            fun ω => (L.X t ω i) ^ (2 : ℕ) - (2 * c) * L.X t ω i + c ^ (2 : ℕ) := by
          funext ω; ring
        rw [heq]
        exact (hX_int2.sub (hX_int.const_mul (2 * c))).add (integrable_const _)
      have hvar : ∫ ω, (L.X t ω i - c) ^ (2 : ℕ) ∂P = (t : ℝ) * ∫ x, (x i) ^ (2 : ℕ) ∂μ := by
        have heq : (fun ω => (L.X t ω i - c) ^ (2 : ℕ)) =
            fun ω => (L.X t ω i) ^ (2 : ℕ) - (2 * c) * L.X t ω i + c ^ (2 : ℕ) := by
          funext ω; ring
        have hint_s : Integrable (fun ω => (L.X t ω i) ^ (2 : ℕ) - (2 * c) * L.X t ω i) P :=
          hX_int2.sub (hX_int.const_mul (2 * c))
        rw [heq, integral_add hint_s (integrable_const _),
          integral_sub hX_int2 (hX_int.const_mul (2 * c)), integral_const_mul,
          integral_const, probReal_univ, one_smul, hEX, hEX2]
        simp only [c]
        ring
      exact ⟨hX_int, hEX, hX_sub_int2, hvar⟩

/-! ## Section 3: `d`-Dimensional Compensated Small-Jump Lévy Process -/

/-- Lemma 3.1: Existence of decreasing shell radii `ε : ℕ → ℝ` with `ε 0 = 1`, `ε n → 0`,
and `∫_{normRd < ε n} ‖x‖² dν ≤ 1 / 16^n` for `n ≥ 1`. -/
private lemma exists_small_jump_shells {d : ℕ}
    (ν : Measure (Fin d → ℝ)) (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    ∃ ε : ℕ → ℝ,
      ε 0 = 1 ∧
      (∀ n, 0 < ε n) ∧
      (∀ n, ε (n + 1) < ε n) ∧
      Tendsto ε atTop (nhds 0) ∧
      (∀ n ≥ 1, ∫ x in {x : Fin d → ℝ | normRd x < ε n},
        (∑ i : Fin d, x i ^ (2 : ℕ)) ∂ν ≤ (1 : ℝ) / (16 : ℝ) ^ n) := by
  have hint_sq : IntegrableOn (fun x : Fin d → ℝ => ∑ i : Fin d, x i ^ (2 : ℕ))
      {x : Fin d → ℝ | normRd x < 1} ν :=
    levyMeasure_integrableOn_sq_small ν hLevy
  have htend_zero : Tendsto
      (fun m : ℕ => ∫ x in {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)},
        (∑ i : Fin d, x i ^ (2 : ℕ)) ∂ν) atTop (nhds 0) := by
    let F : ℕ → (Fin d → ℝ) → ℝ := fun m x =>
      Set.indicator {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)}
        (fun x => ∑ i : Fin d, x i ^ (2 : ℕ)) x
    have hF_eq : ∀ m : ℕ,
        ∫ x in {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)},
          (∑ i : Fin d, x i ^ (2 : ℕ)) ∂ν =
        ∫ x in {x : Fin d → ℝ | normRd x < 1}, F m x ∂ν := by
      intro m
      have hmeas_m : MeasurableSet {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)} :=
        measurableSet_lt (by unfold normRd; fun_prop) measurable_const
      rw [MeasureTheory.integral_indicator hmeas_m, Measure.restrict_restrict hmeas_m]
      have hsub : {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)} ⊆
          {x : Fin d → ℝ | normRd x < 1} := by
        intro x hx
        have hle : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        exact lt_of_lt_of_le hx hle
      rw [Set.inter_eq_left.mpr hsub]
    simp_rw [hF_eq]
    have hlim : Tendsto (fun m : ℕ => ∫ x in {x : Fin d → ℝ | normRd x < 1}, F m x ∂ν)
        atTop (nhds (∫ _ in {x : Fin d → ℝ | normRd x < 1}, (0 : ℝ) ∂ν)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun x => ∑ i : Fin d, x i ^ (2 : ℕ)) ?_ hint_sq ?_ ?_
      · intro m
        have hmeas_m : MeasurableSet {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)} :=
          measurableSet_lt (by unfold normRd; fun_prop) measurable_const
        exact ((by fun_prop : Continuous fun x : Fin d → ℝ => ∑ i : Fin d, x i ^ (2 : ℕ)).measurable.indicator
          hmeas_m).aestronglyMeasurable
      · intro m
        refine Filter.Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)}
        · simp only [F, Set.indicator_of_mem hx, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _), le_rfl]
        · simp only [F, Set.indicator_of_notMem hx, norm_zero]
          exact Finset.sum_nonneg fun i _ => sq_nonneg _
      · have hne0 : ∀ᵐ x ∂(ν.restrict {x : Fin d → ℝ | normRd x < 1}), x ≠ 0 := by
          rw [ae_iff]
          have hset : {x : Fin d → ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
          rw [hset]
          refine le_antisymm ?_ (by positivity)
          calc (ν.restrict {x : Fin d → ℝ | normRd x < 1}) {0} ≤ ν {0} :=
                Measure.restrict_le_self _
            _ = 0 := hzero
        filter_upwards [hne0] with x hx
        have hpos : 0 < normRd x := by
          have hsum_pos : 0 < ∑ i : Fin d, x i ^ (2 : ℕ) := by
            have hex : ∃ i : Fin d, x i ≠ 0 := by
              by_contra hall; push_neg at hall; exact hx (funext hall)
            obtain ⟨i₀, hi₀⟩ := hex
            calc 0 < x i₀ ^ (2 : ℕ) := sq_pos_of_ne_zero hi₀
              _ ≤ ∑ i : Fin d, x i ^ (2 : ℕ) :=
                Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)
          exact Real.sqrt_pos.mpr hsum_pos
        obtain ⟨M, hM⟩ := exists_nat_one_div_lt hpos
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop M] with m hm
        have hlt : 1 / ((m : ℝ) + 1) < normRd x := by
          have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast Nat.add_le_add_right hm 1
          exact lt_of_le_of_lt hle hM
        have hnotmem : x ∉ {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)} := not_lt.mpr (le_of_lt hlt)
        simp only [F, Set.indicator_of_notMem hnotmem]
    simpa using hlim
  have hstep : ∀ (n : ℕ) (r : ℝ), 0 < r →
      ∃ r' : ℝ, 0 < r' ∧ r' < r ∧ r' < 1 / ((n : ℝ) + 2) ∧
        ∫ x in {x : Fin d → ℝ | normRd x < r'}, (∑ i : Fin d, x i ^ (2 : ℕ)) ∂ν ≤
          (1 : ℝ) / (16 : ℝ) ^ (n + 1) := by
    intro n r hr
    have hpos_rhs : (0 : ℝ) < (1 : ℝ) / (16 : ℝ) ^ (n + 1) := by positivity
    have hev1 : ∀ᶠ m : ℕ in atTop,
        ∫ x in {x : Fin d → ℝ | normRd x < 1 / ((m : ℝ) + 1)},
          (∑ i : Fin d, x i ^ (2 : ℕ)) ∂ν < (1 : ℝ) / (16 : ℝ) ^ (n + 1) :=
      htend_zero.eventually (Iio_mem_nhds hpos_rhs)
    obtain ⟨m1, hm1⟩ := Filter.eventually_atTop.mp hev1
    obtain ⟨m2, hm2⟩ := exists_nat_one_div_lt (lt_min hr (show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity))
    let m : ℕ := max m1 m2
    refine ⟨1 / ((m : ℝ) + 1), by positivity, ?_, ?_, le_of_lt (hm1 m (le_max_left m1 m2))⟩
    · have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m2 : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hle_nat : m2 ≤ m := le_max_right m1 m2
        have : (m2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle_nat
        linarith
      exact lt_of_le_of_lt hle (lt_of_lt_of_le hm2 (min_le_left _ _))
    · have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m2 : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hle_nat : m2 ≤ m := le_max_right m1 m2
        have : (m2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle_nat
        linarith
      exact lt_of_le_of_lt hle (lt_of_lt_of_le hm2 (min_le_right _ _))
  choose f hf_pos hf_lt hf_div hf_int using hstep
  let seq : ℕ → { r : ℝ // 0 < r } := Nat.rec ⟨1, one_pos⟩
    (fun n prev => ⟨f n prev.1 prev.2, hf_pos n prev.1 prev.2⟩)
  refine ⟨fun n => (seq n).1, rfl, fun n => (seq n).2,
    fun n => hf_lt n (seq n).1 (seq n).2, ?_, ?_⟩
  · refine squeeze_zero (fun n => le_of_lt (seq n).2) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat)
    cases n with
    | zero => simp [seq]
    | succ k =>
      have h1 : (seq (k + 1)).1 < 1 / ((k : ℝ) + 2) := hf_div k (seq k).1 (seq k).2
      have h2 : (1 : ℝ) / ((k : ℝ) + 2) ≤ 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
        push_cast; apply le_of_eq; ring
      exact le_trans (le_of_lt h1) h2
  · intro n hn
    cases n with
    | zero => omega
    | succ k => exact hf_int k (seq k).1 (seq k).2

/-- Lemma 3.2: Compensated finite-measure small-jump shell process (mean zero, exact L² variance
and exact compensated Lévy–Khintchine exponent). -/
private lemma exists_compensated_shell_rdLevy {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (hμ : μ Set.univ < ⊤)
    (hbdd : ∀ᵐ x ∂μ, ∀ i : Fin d, |x i| ≤ 1) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ Z : RdLevyProcess d Ω P,
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I * ((innerRd θ (Z.X t ω) : ℝ) : ℂ)) ∂P =
              Complex.exp (-(t : ℝ) *
                ∫ x, (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
                  Complex.I * ((innerRd θ x : ℝ) : ℂ)) ∂μ)) ∧
          (∀ (t : ℝ≥0) (i : Fin d),
            Integrable (fun ω => Z.X t ω i) P ∧
            ∫ ω, Z.X t ω i ∂P = 0 ∧
            Integrable (fun ω => (Z.X t ω i) ^ (2 : ℕ)) P ∧
            ∫ ω, (Z.X t ω i) ^ (2 : ℕ) ∂P = (t : ℝ) * ∫ x, (x i) ^ (2 : ℕ) ∂μ) := by
  haveI : IsFiniteMeasure μ := ⟨hμ⟩
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, L₀, hcf₀, hmom₀⟩ := exists_compound_poisson_rdLevy μ hμ
  letI : MeasurableSpace Ω₀ := mΩ₀
  letI : IsProbabilityMeasure P₀ := hP₀
  let b : Fin d → ℝ := fun i => ∫ x, x i ∂μ
  let Ldrift := deterministic_drift_rdLevy b
  let Z := sum_two_indep_rdLevy L₀ Ldrift
  refine ⟨Ω₀ × Unit, inferInstance, P₀.prod (Measure.dirac ()), inferInstance, Z, ?_, ?_⟩
  · intro t θ
    rw [sum_two_indep_rdLevy_charFun L₀ Ldrift t θ, hcf₀ t θ]
    have hdrift_cf :
        ∫ ω, Complex.exp (Complex.I * ((innerRd θ (Ldrift.X t ω) : ℝ) : ℂ)) ∂(Measure.dirac ()) =
          Complex.exp (-(t : ℝ) * (Complex.I * ((∑ i : Fin d, b i * θ i : ℝ) : ℂ))) := by
      rw [integral_dirac]
      congr 1
      have hinner : innerRd θ (Ldrift.X t ()) = -(t : ℝ) * ∑ i : Fin d, b i * θ i := by
        simp only [innerRd, Ldrift, deterministic_drift_rdLevy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hinner]; push_cast; ring
    rw [hdrift_cf, ← Complex.exp_add]
    congr 1
    have hint_coord : ∀ i : Fin d, Integrable (fun x : Fin d → ℝ => x i) μ := fun i => by
      refine Integrable.of_bound (continuous_apply i).aestronglyMeasurable 1 ?_
      filter_upwards [hbdd] with x hx
      simpa [Real.norm_eq_abs] using hx i
    have hint_part1 : Integrable (fun x : Fin d → ℝ =>
        1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) μ := by
      have hcont : Continuous (fun x : Fin d → ℝ =>
          1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))) := by
        unfold innerRd; fun_prop
      refine Integrable.of_bound hcont.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun x => ?_)
      calc ‖1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))‖
          ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ))‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, Complex.norm_exp_I_mul_ofReal]; norm_num
    have hint_part2 : Integrable (fun x : Fin d → ℝ =>
        Complex.I * ((innerRd θ x : ℝ) : ℂ)) μ := by
      have hlin : Integrable (fun x : Fin d → ℝ => innerRd θ x) μ := by
        unfold innerRd
        exact integrable_finset_sum _ fun i _ => (hint_coord i).const_mul (θ i)
      exact (Complex.ofRealCLM.integrable_comp hlin).const_mul Complex.I
    have hlin_int : Complex.I * ((∑ i : Fin d, b i * θ i : ℝ) : ℂ) =
        ∫ x, Complex.I * ((innerRd θ x : ℝ) : ℂ) ∂μ := by
      rw [integral_const_mul]
      congr 1
      have hr : ∑ i : Fin d, b i * θ i = ∫ x, innerRd θ x ∂μ := by
        unfold innerRd
        rw [integral_finset_sum _ fun i _ => (hint_coord i).const_mul (θ i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]; dsimp only [b]; ring
      rw [hr]
      exact (Complex.ofRealCLM.integral_comp_comm (by
        unfold innerRd; exact integrable_finset_sum _ fun i _ => (hint_coord i).const_mul (θ i))).symm
    rw [integral_add hint_part1 hint_part2, ← hlin_int]
    ring
  · intro t i
    obtain ⟨h1, h2, h3, h4⟩ := hmom₀ hbdd t i
    have hZ_eq : ∀ ω : Ω₀ × Unit, Z.X t ω i = L₀.X t ω.1 i - (t : ℝ) * b i := fun ω => by
      simp only [Z, sum_two_indep_rdLevy, Ldrift, deterministic_drift_rdLevy, Pi.add_apply]
      ring
    have hZ_int : Integrable (fun ω : Ω₀ × Unit => Z.X t ω i) (P₀.prod (Measure.dirac ())) := by
      simp_rw [hZ_eq]
      exact (h1.comp_fst (Measure.dirac ())).sub (integrable_const _)
    have hZ_mean : ∫ ω : Ω₀ × Unit, Z.X t ω i ∂(P₀.prod (Measure.dirac ())) = 0 := by
      simp_rw [hZ_eq]
      rw [integral_sub (h1.comp_fst (Measure.dirac ())) (integrable_const _),
        MeasureTheory.integral_prod _ (h1.comp_fst (Measure.dirac ()))]
      simp only [integral_dirac, integral_const, probReal_univ, one_smul, h2, b, sub_self]
    have hZ_int2 : Integrable (fun ω : Ω₀ × Unit => (Z.X t ω i) ^ (2 : ℕ))
        (P₀.prod (Measure.dirac ())) := by
      simp_rw [hZ_eq]
      exact h3.comp_fst (Measure.dirac ())
    have hZ_var : ∫ ω : Ω₀ × Unit, (Z.X t ω i) ^ (2 : ℕ) ∂(P₀.prod (Measure.dirac ())) =
        (t : ℝ) * ∫ x, (x i) ^ (2 : ℕ) ∂μ := by
      simp_rw [hZ_eq]
      rw [MeasureTheory.integral_prod _ (h3.comp_fst (Measure.dirac ()))]
      simp only [integral_dirac]
      exact h4
    exact ⟨hZ_int, hZ_mean, hZ_int2, hZ_var⟩

/-- Lemma 3.3: Doob maximal inequality for a mean-zero L² càdlàg `RdLevyProcess`. -/
private lemma rdLevy_maximal_tail_bound {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (L : RdLevyProcess d Ω P) (i : Fin d) {σ2 : ℝ} (hσ2 : 0 ≤ σ2)
    (hmean : ∀ t : ℝ≥0, Integrable (fun ω => L.X t ω i) P ∧ ∫ ω, L.X t ω i ∂P = 0)
    (hvar : ∀ t : ℝ≥0, Integrable (fun ω => (L.X t ω i) ^ (2 : ℕ)) P ∧
      ∫ ω, (L.X t ω i) ^ (2 : ℕ) ∂P ≤ (t : ℝ) * σ2)
    (K : ℝ≥0) {δ : ℝ≥0} (hδ : 0 < δ) :
    P { ω : Ω | ∃ t : ℝ≥0, t ≤ K ∧ (δ : ℝ) < |L.X t ω i| } ≤
      ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := by
  -- Step 1: Finite discrete maximal bound on any monotone sequence `u : ℕ → ℝ≥0` with `u N ≤ K`
  have hfin_bound : ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ (N : ℕ), u N ≤ K →
      P { ω : Ω | ∃ k ≤ N, (δ : ℝ) < |L.X (u k) ω i| } ≤
        ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := by
    intro u hu N huN
    let ℱ : Filtration ℕ mΩ :=
      { seq := fun k => ⨆ v ∈ Set.Iic (u k), MeasurableSpace.comap (L.X v) inferInstance
        mono' := fun k l hkl =>
          iSup₂_le fun v hv => le_iSup₂_of_le v (le_trans hv (hu hkl)) le_rfl
        le' := fun k => iSup₂_le fun v _ => (L.measurable v).comap_le }
    let f : ℕ → Ω → ℝ := fun k ω => (L.X (u k) ω i) ^ (2 : ℕ)
    have hf_adapt : StronglyAdapted ℱ f := by
      intro k
      have hm_k : @Measurable Ω ℝ (ℱ k) inferInstance (f k) := by
        have hle : MeasurableSpace.comap (L.X (u k)) inferInstance ≤ ℱ k :=
          le_iSup₂_of_le (u k) (Set.mem_Iic.mpr le_rfl) le_rfl
        exact (((continuous_apply i).pow 2).measurable.comp (comap_measurable (L.X (u k)))).mono hle le_rfl
      exact hm_k.stronglyMeasurable
    have hf_int : ∀ k, Integrable (f k) P := fun k => (hvar (u k)).1
    have hf_sub : Submartingale f ℱ P := by
      refine submartingale_of_setIntegral_le hf_adapt hf_int fun k l hkl s hs => ?_
      let Y : Ω → ℝ := fun ω => L.X (u k) ω i
      let Δ : Ω → ℝ := fun ω => L.X (u l) ω i - L.X (u k) ω i
      have hY_meas_Fk : @Measurable Ω ℝ (ℱ k) inferInstance Y := by
        have hle : MeasurableSpace.comap (L.X (u k)) inferInstance ≤ ℱ k :=
          le_iSup₂_of_le (u k) (Set.mem_Iic.mpr le_rfl) le_rfl
        exact ((continuous_apply i).measurable.comp (comap_measurable (L.X (u k)))).mono hle le_rfl
      have hsY_meas_Fk : @Measurable Ω ℝ (ℱ k) inferInstance (s.indicator Y) :=
        hY_meas_Fk.indicator hs
      have hΔ_meas_inc : @Measurable Ω ℝ
          (MeasurableSpace.comap (fun ω => L.X (u l) ω - L.X (u k) ω) inferInstance) inferInstance Δ := by
        have hcm : @Measurable Ω (Fin d → ℝ)
            (MeasurableSpace.comap (fun ω => L.X (u l) ω - L.X (u k) ω) inferInstance) inferInstance
            (fun ω => L.X (u l) ω - L.X (u k) ω) :=
          comap_measurable (fun ω => L.X (u l) ω - L.X (u k) ω)
        exact (continuous_apply i).measurable.comp hcm
      have hind_ind : ProbabilityTheory.IndepFun (s.indicator Y) Δ P := by
        rw [ProbabilityTheory.IndepFun_iff_Indep]
        have hbase := (L.indep_increments (u k) (u l) (hu hkl)).symm
        refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hbase ?_) ?_
        · exact hΔ_meas_inc.comap_le
        · exact hsY_meas_Fk.comap_le
      have hs_mΩ : MeasurableSet s := ℱ.le k s hs
      have hint_YΔ : Integrable (fun ω => (s.indicator Y ω) * Δ ω) P := by
        have hY_int2 : Integrable (fun ω => (Y ω) ^ (2 : ℕ)) P := (hvar (u k)).1
        have hL_int2 : Integrable (fun ω => (L.X (u l) ω i) ^ (2 : ℕ)) P := (hvar (u l)).1
        have hΔ_int2 : Integrable (fun ω => (Δ ω) ^ (2 : ℕ)) P := by
          have hdom : Integrable (fun ω => 2 * (L.X (u l) ω i) ^ (2 : ℕ) + 2 * (Y ω) ^ (2 : ℕ)) P :=
            (hL_int2.const_mul 2).add (hY_int2.const_mul 2)
          refine hdom.mono' ((((continuous_apply i).measurable.comp ((L.measurable (u l)).sub (L.measurable (u k)))).pow_const 2).aestronglyMeasurable)
            (Filter.Eventually.of_forall fun ω => ?_)
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          dsimp only [Δ, Y]
          nlinarith [sq_nonneg (L.X (u l) ω i + L.X (u k) ω i)]
        have hdom : Integrable (fun ω => (Y ω) ^ (2 : ℕ) + (Δ ω) ^ (2 : ℕ)) P := hY_int2.add hΔ_int2
        refine hdom.mono'
          (((hY_meas_Fk.mono (ℱ.le k) le_rfl).indicator hs_mΩ).mul
            ((continuous_apply i).measurable.comp ((L.measurable (u l)).sub (L.measurable (u k))))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |s.indicator Y ω| ≤ |Y ω| := by
          by_cases hω : ω ∈ s <;> simp [hω]
        nlinarith [abs_nonneg (Y ω), abs_nonneg (Δ ω), sq_abs (Y ω), sq_abs (Δ ω),
          sq_nonneg (|Y ω| - |Δ ω|)]
      have hcross_zero : ∫ ω in s, Y ω * Δ ω ∂P = 0 := by
        rw [← integral_indicator hs_mΩ]
        have heq : (fun ω => s.indicator (fun ω => Y ω * Δ ω) ω) =
            fun ω => s.indicator Y ω * Δ ω := by
          funext ω; by_cases hω : ω ∈ s <;> simp [hω]
        rw [heq, hind_ind.integral_fun_mul_eq_mul_integral
          ((hY_meas_Fk.mono (ℱ.le k) le_rfl).indicator hs_mΩ).aestronglyMeasurable
          ((continuous_apply i).measurable.comp ((L.measurable (u l)).sub (L.measurable (u k)))).aestronglyMeasurable]
        have hEΔ : ∫ ω, Δ ω ∂P = 0 := by
          change ∫ ω, (L.X (u l) ω i - L.X (u k) ω i) ∂P = 0
          rw [integral_sub (hmean (u l)).1 (hmean (u k)).1, (hmean (u l)).2, (hmean (u k)).2, sub_self]
        rw [hEΔ, mul_zero]
      have hge : ∀ ω, f k ω + 2 * (Y ω * Δ ω) ≤ f l ω := fun ω => by
        dsimp only [f, Y, Δ]
        nlinarith [sq_nonneg (L.X (u l) ω i - L.X (u k) ω i)]
      have hint_lhs : IntegrableOn (fun ω => f k ω + 2 * (Y ω * Δ ω)) s P := by
        refine (hf_int k).integrableOn.add ?_
        have h1 : IntegrableOn (fun ω => Y ω * Δ ω) s P := by
          rw [← integrable_indicator_iff hs_mΩ]
          have heq : s.indicator (fun ω => Y ω * Δ ω) = fun ω => s.indicator Y ω * Δ ω := by
            funext ω; by_cases hω : ω ∈ s <;> simp [hω]
          rw [heq]; exact hint_YΔ
        exact h1.const_mul 2
      calc ∫ ω in s, f k ω ∂P
          = ∫ ω in s, f k ω ∂P + 2 * ∫ ω in s, Y ω * Δ ω ∂P := by rw [hcross_zero, mul_zero, add_zero]
        _ = ∫ ω in s, (f k ω + 2 * (Y ω * Δ ω)) ∂P := by
            rw [integral_add (hf_int k).integrableOn]
            · rw [integral_const_mul]
            · have h1 : IntegrableOn (fun ω => Y ω * Δ ω) s P := by
                rw [← integrable_indicator_iff hs_mΩ]
                have heq : s.indicator (fun ω => Y ω * Δ ω) = fun ω => s.indicator Y ω * Δ ω := by
                  funext ω; by_cases hω : ω ∈ s <;> simp [hω]
                rw [heq]; exact hint_YΔ
              exact h1.const_mul 2
        _ ≤ ∫ ω in s, f l ω ∂P := setIntegral_mono_on hint_lhs (hf_int l).integrableOn hs_mΩ fun ω _ => hge ω
    have hf_nonneg : 0 ≤ f := fun k ω => sq_nonneg _
    have hmax := MeasureTheory.maximal_ineq hf_sub hf_nonneg (ε := δ ^ (2 : ℕ)) N
    let E_sup : Set Ω :=
      { ω | ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω }
    have hsub_set : { ω : Ω | ∃ k ≤ N, (δ : ℝ) < |L.X (u k) ω i| } ⊆ E_sup := by
      rintro ω ⟨k, hkN, hklt⟩
      change ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j => f j ω
      have hk_mem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)
      calc ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ)
          = (δ : ℝ) ^ (2 : ℕ) := by push_cast; rfl
        _ ≤ (L.X (u k) ω i) ^ (2 : ℕ) := by
            nlinarith [sq_abs (L.X (u k) ω i), abs_nonneg (L.X (u k) ω i), δ.coe_nonneg]
        _ = f k ω := rfl
        _ ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j => f j ω :=
            Finset.le_sup' (fun j => f j ω) hk_mem
    have hint_le : ∫ ω in E_sup, f N ω ∂P ≤ (K : ℝ) * σ2 := by
      calc ∫ ω in E_sup, f N ω ∂P
          ≤ ∫ ω, f N ω ∂P := setIntegral_le_integral (hf_int N) (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        _ ≤ (u N : ℝ) * σ2 := (hvar (u N)).2
        _ ≤ (K : ℝ) * σ2 := mul_le_mul_of_nonneg_right (by exact_mod_cast huN) hσ2
    have hmul_le : ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * P { ω : Ω | ∃ k ≤ N, (δ : ℝ) < |L.X (u k) ω i| } ≤
        ENNReal.ofReal ((K : ℝ) * σ2) := by
      calc ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * P { ω : Ω | ∃ k ≤ N, (δ : ℝ) < |L.X (u k) ω i| }
          ≤ ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * P E_sup := by gcongr
        _ ≤ ENNReal.ofReal (∫ ω in E_sup, f N ω ∂P) := hmax
        _ ≤ ENNReal.ofReal ((K : ℝ) * σ2) := ENNReal.ofReal_le_ofReal hint_le
    have hδ2_pos : (0 : ℝ≥0∞) < ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast pow_pos hδ 2
    have hδ2_ne0 : ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) ≠ 0 := hδ2_pos.ne'
    have hδ2_netop : ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [← ENNReal.mul_le_mul_iff_right hδ2_ne0 hδ2_netop]
    calc ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * P { ω : Ω | ∃ k ≤ N, (δ : ℝ) < |L.X (u k) ω i| }
        ≤ ENNReal.ofReal ((K : ℝ) * σ2) := hmul_le
      _ = ((δ ^ (2 : ℕ) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hδr : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ.ne'
          push_cast
          field_simp
  -- Step 2: Dyadic grid approximation + right-continuity from `L.cadlag`
  let grid : ℕ → ℕ → ℝ≥0 := fun m k => K * ((min k (2 ^ m) : ℕ) : ℝ≥0) / ((2 ^ m : ℕ) : ℝ≥0)
  let Em : ℕ → Set Ω := fun m => { ω : Ω | ∃ k ≤ 2 ^ m, (δ : ℝ) < |L.X (grid m k) ω i| }
  have hEm_mono : Monotone Em := by
    intro m₁ m₂ hm ω ⟨k, hk, hlt⟩
    refine ⟨k * 2 ^ (m₂ - m₁), ?_, ?_⟩
    · calc k * 2 ^ (m₂ - m₁) ≤ 2 ^ m₁ * 2 ^ (m₂ - m₁) := Nat.mul_le_mul_right _ hk
        _ = 2 ^ (m₁ + (m₂ - m₁)) := (pow_add 2 _ _).symm
        _ = 2 ^ m₂ := by rw [Nat.add_sub_of_le hm]
    · have hgrid_eq : grid m₂ (k * 2 ^ (m₂ - m₁)) = grid m₁ k := by
        apply NNReal.coe_injective
        have hmin1 : min k (2 ^ m₁) = k := Nat.min_eq_left hk
        have hle2 : k * 2 ^ (m₂ - m₁) ≤ 2 ^ m₂ := by
          calc k * 2 ^ (m₂ - m₁) ≤ 2 ^ m₁ * 2 ^ (m₂ - m₁) := Nat.mul_le_mul_right _ hk
            _ = 2 ^ m₂ := by rw [← pow_add, Nat.add_sub_of_le hm]
        have hmin2 : min (k * 2 ^ (m₂ - m₁)) (2 ^ m₂) = k * 2 ^ (m₂ - m₁) := Nat.min_eq_left hle2
        simp only [grid, hmin1, hmin2, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
        have hpow : ((2 ^ m₂ : ℕ) : ℝ) = ((2 ^ m₁ : ℕ) : ℝ) * ((2 ^ (m₂ - m₁) : ℕ) : ℝ) := by
          norm_cast; rw [← pow_add, Nat.add_sub_of_le hm]
        have h1 : ((2 ^ m₁ : ℕ) : ℝ) ≠ 0 := by positivity
        have h2 : ((2 ^ (m₂ - m₁) : ℕ) : ℝ) ≠ 0 := by positivity
        rw [hpow, Nat.cast_mul]
        field_simp
      rwa [hgrid_eq]
  have hEm_bound : ∀ m : ℕ, P (Em m) ≤ ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := by
    intro m
    have hmono_k : Monotone (grid m) := fun a b hab => by
      dsimp only [grid]
      gcongr
    have hleK : grid m (2 ^ m) ≤ K := by
      apply NNReal.coe_le_coe.mp
      simp only [grid, min_self, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
      have hpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
      rw [mul_div_cancel_right₀ _ hpos.ne']
    exact hfin_bound (grid m) hmono_k (2 ^ m) hleK
  have hunion_bound : P (⋃ m : ℕ, Em m) ≤ ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := by
    have htend : Tendsto (fun m => P (Em m)) atTop (nhds (P (⋃ m : ℕ, Em m))) :=
      MeasureTheory.tendsto_measure_iUnion_atTop hEm_mono
    exact le_of_tendsto' htend hEm_bound
  have hae_sub : ∀ᵐ ω ∂P,
      ω ∈ { ω : Ω | ∃ t : ℝ≥0, t ≤ K ∧ (δ : ℝ) < |L.X t ω i| } → ω ∈ ⋃ m : ℕ, Em m := by
    filter_upwards [L.cadlag] with ω ⟨hrc, _⟩ ⟨t, htK, hlt⟩
    rcases eq_or_lt_of_le htK with hEq | hltK
    · refine Set.mem_iUnion.mpr ⟨0, 1, le_rfl, ?_⟩
      have hgrid0 : grid 0 1 = K := by simp [grid]
      rwa [hgrid0, ← hEq]
    · have hKpos : (0 : ℝ) < (K : ℝ) := by
        have : (t : ℝ) < (K : ℝ) := by exact_mod_cast hltK
        linarith [t.coe_nonneg]
      have hcont_abs : ContinuousWithinAt (fun u : ℝ≥0 => |L.X u ω i|) (Set.Ici t) t :=
        (continuous_abs.comp (continuous_apply i)).continuousAt.comp_continuousWithinAt (hrc t)
      have hev := hcont_abs.eventually (Ioi_mem_nhds hlt)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
      obtain ⟨η, hη_pos, hη⟩ := hev
      have hgap : (0 : ℝ) < min η ((K : ℝ) - (t : ℝ)) :=
        lt_min hη_pos (sub_pos.mpr (by exact_mod_cast hltK))
      -- Find `m` with `K / 2^m < min η (K - t)`
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (K : ℝ) / ((2 ^ m : ℕ) : ℝ) < min η ((K : ℝ) - (t : ℝ)) := by
        have htend2 : Tendsto (fun m : ℕ => (K : ℝ) / ((2 ^ m : ℕ) : ℝ)) atTop (nhds 0) := by
          have : (fun m : ℕ => (K : ℝ) / ((2 ^ m : ℕ) : ℝ)) = fun m => (K : ℝ) * ((1 / 2 : ℝ) ^ m) := by
            funext m; simp [div_eq_mul_inv, one_div, inv_pow]
          rw [this]
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (K : ℝ)
        exact (htend2.eventually (Iio_mem_nhds hgap)).exists
      let k : ℕ := Nat.ceil ((t : ℝ) * ((2 ^ m : ℕ) : ℝ) / (K : ℝ))
      have h2m_pos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
      have hk_ge : (t : ℝ) ≤ (K : ℝ) * (k : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
        have hc : (t : ℝ) * ((2 ^ m : ℕ) : ℝ) / (K : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
        rw [le_div_iff₀ h2m_pos]
        have := (div_le_iff₀ hKpos).mp hc
        linarith
      have hk_lt : (K : ℝ) * (k : ℝ) / ((2 ^ m : ℕ) : ℝ) < (t : ℝ) + (K : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
        have hlt_c : (k : ℝ) < (t : ℝ) * ((2 ^ m : ℕ) : ℝ) / (K : ℝ) + 1 :=
          Nat.ceil_lt_add_one (by positivity)
        rw [div_lt_iff₀ h2m_pos]
        have hmul := mul_lt_mul_of_pos_left hlt_c hKpos
        have h1 : (K : ℝ) * ((t : ℝ) * ((2 ^ m : ℕ) : ℝ) / (K : ℝ) + 1) =
            (t : ℝ) * ((2 ^ m : ℕ) : ℝ) + (K : ℝ) := by field_simp
        rw [h1] at hmul
        have h2 : ((t : ℝ) + (K : ℝ) / ((2 ^ m : ℕ) : ℝ)) * ((2 ^ m : ℕ) : ℝ) =
            (t : ℝ) * ((2 ^ m : ℕ) : ℝ) + (K : ℝ) := by field_simp
        linarith
      have hk_le : k ≤ 2 ^ m := by
        have hreal : (k : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
          have h1 : (K : ℝ) * (k : ℝ) / ((2 ^ m : ℕ) : ℝ) < (K : ℝ) := by
            have := lt_of_lt_of_le hm (min_le_right _ _)
            linarith
          have h2 : (K : ℝ) * (k : ℝ) < (K : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
            rwa [div_lt_iff₀ h2m_pos] at h1
          exact lt_of_mul_lt_mul_left h2 (le_of_lt hKpos)
        exact_mod_cast le_of_lt hreal
      refine Set.mem_iUnion.mpr ⟨m, k, hk_le, ?_⟩
      have hgrid_val : ((grid m k : ℝ≥0) : ℝ) = (K : ℝ) * (k : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
        simp only [grid, Nat.min_eq_left hk_le, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
      have hdist : dist (grid m k) t < η := by
        rw [NNReal.dist_eq, hgrid_val, abs_of_nonneg (by linarith)]
        have := lt_of_lt_of_le hm (min_le_left _ _)
        linarith
      have hge_t : grid m k ∈ Set.Ici t := by
        change (t : ℝ) ≤ ((grid m k : ℝ≥0) : ℝ)
        rw [hgrid_val]; exact hk_ge
      exact hη hdist hge_t
  calc P { ω : Ω | ∃ t : ℝ≥0, t ≤ K ∧ (δ : ℝ) < |L.X t ω i| }
      ≤ P (⋃ m : ℕ, Em m) := measure_mono_ae hae_sub
    _ ≤ ENNReal.ofReal ((K : ℝ) * σ2 / (δ : ℝ) ^ (2 : ℕ)) := hunion_bound

/-- Lemma 3.4: Locally uniform limit of càdlàg `ℝ^d`-valued functions is càdlàg. -/
private lemma cadlag_of_tendsto_uniform_on_Iic {d : ℕ}
    (f : ℕ → ℝ≥0 → (Fin d → ℝ)) (g : ℝ≥0 → (Fin d → ℝ))
    (hf : ∀ n, (∀ t : ℝ≥0, ContinuousWithinAt (f n) (Set.Ici t) t) ∧
      (∀ t : ℝ≥0, 0 < t → ∃ l : Fin d → ℝ, Tendsto (f n) (nhdsWithin t (Set.Iio t)) (nhds l)))
    (hunif : ∀ (K : ℕ) (η : ℝ), 0 < η →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ≥0, t ≤ (K : ℝ≥0) → dist (f n t) (g t) < η) :
    (∀ t : ℝ≥0, ContinuousWithinAt g (Set.Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : Fin d → ℝ, Tendsto g (nhdsWithin t (Set.Iio t)) (nhds l)) := by
  constructor
  · intro t
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    let K : ℕ := Nat.ceil (t : ℝ) + 1
    obtain ⟨N, hN⟩ := hunif K (ε / 3) (by linarith)
    have hrcN := Metric.continuousWithinAt_iff.mp ((hf N).1 t) (ε / 3) (by linarith)
    obtain ⟨δ, hδ_pos, hδ⟩ := hrcN
    refine ⟨min δ 1, lt_min hδ_pos one_pos, fun u hu hdist => ?_⟩
    have htK : t ≤ (K : ℝ≥0) := by
      change (t : ℝ) ≤ ((Nat.ceil (t : ℝ) + 1 : ℕ) : ℝ)
      push_cast; linarith [Nat.le_ceil (t : ℝ)]
    have huK : u ≤ (K : ℝ≥0) := by
      have hd1 : dist u t < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
      rw [NNReal.dist_eq] at hd1
      have : (u : ℝ) - (t : ℝ) < 1 := (abs_lt.mp hd1).2
      change (u : ℝ) ≤ ((Nat.ceil (t : ℝ) + 1 : ℕ) : ℝ)
      push_cast; linarith [Nat.le_ceil (t : ℝ)]
    have h1 : dist (g u) (f N u) < ε / 3 := by
      rw [dist_comm]; exact hN N le_rfl u huK
    have h2 : dist (f N u) (f N t) < ε / 3 :=
      hδ hu (lt_of_lt_of_le hdist (min_le_left _ _))
    have h3 : dist (f N t) (g t) < ε / 3 := hN N le_rfl t htK
    linarith [dist_triangle (g u) (f N u) (g t), dist_triangle (f N u) (f N t) (g t)]
  · intro t ht
    let K : ℕ := Nat.ceil (t : ℝ) + 1
    have htK : t ≤ (K : ℝ≥0) := by
      change (t : ℝ) ≤ ((Nat.ceil (t : ℝ) + 1 : ℕ) : ℝ)
      push_cast; linarith [Nat.le_ceil (t : ℝ)]
    choose L hL using fun n => (hf n).2 t ht
    have hne_flt : (nhdsWithin t (Set.Iio t)).NeBot := by
      rw [nhdsWithin_neBot]
      intro s hs
      rw [Metric.mem_nhds_iff] at hs
      obtain ⟨r, hr_pos, hr⟩ := hs
      let u : ℝ≥0 := ⟨(t : ℝ) - min ((t : ℝ) / 2) (r / 2), by
        have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        linarith [min_le_left ((t : ℝ) / 2) (r / 2)]⟩
      have hut : u < t := by
        change (t : ℝ) - min ((t : ℝ) / 2) (r / 2) < (t : ℝ)
        have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        have : 0 < min ((t : ℝ) / 2) (r / 2) := lt_min (by linarith) (by linarith)
        linarith
      have hu_ball : u ∈ Metric.ball t r := by
        rw [Metric.mem_ball, NNReal.dist_eq]
        change |(t : ℝ) - min ((t : ℝ) / 2) (r / 2) - (t : ℝ)| < r
        have htp : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
        have hmin_pos : 0 < min ((t : ℝ) / 2) (r / 2) := lt_min (by linarith) (by linarith)
        have hmin_le : min ((t : ℝ) / 2) (r / 2) ≤ r / 2 := min_le_right _ _
        have heq : (t : ℝ) - min ((t : ℝ) / 2) (r / 2) - (t : ℝ) = -min ((t : ℝ) / 2) (r / 2) := by ring
        rw [heq, abs_neg, abs_of_pos hmin_pos]
        linarith
      exact ⟨u, hr hu_ball, hut⟩
    have hCauchy : CauchySeq L := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif K (ε / 4) (by linarith)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hev_m : ∀ᶠ u in nhdsWithin t (Set.Iio t), dist (f m u) (L m) < ε / 4 :=
        (hL m).eventually (Metric.ball_mem_nhds (L m) (by linarith))
      have hev_n : ∀ᶠ u in nhdsWithin t (Set.Iio t), dist (f n u) (L n) < ε / 4 :=
        (hL n).eventually (Metric.ball_mem_nhds (L n) (by linarith))
      have hev_lt : ∀ᶠ u in nhdsWithin t (Set.Iio t), u < t := self_mem_nhdsWithin
      obtain ⟨u, hu_m, hu_n, hu_lt⟩ := (hev_m.and (hev_n.and hev_lt)).exists
      have huK : u ≤ (K : ℝ≥0) := le_trans (le_of_lt hu_lt) htK
      have h1 : dist (L m) (f m u) < ε / 4 := by rw [dist_comm]; exact hu_m
      have h2 : dist (f m u) (g u) < ε / 4 := hN m hm u huK
      have h3 : dist (g u) (f n u) < ε / 4 := by rw [dist_comm]; exact hN n hn u huK
      linarith [dist_triangle (L m) (f m u) (L n), dist_triangle (f m u) (g u) (L n),
        dist_triangle (g u) (f n u) (L n)]
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hCauchy
    refine ⟨l, ?_⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hunif K (ε / 3) (by linarith)
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp ((Metric.tendsto_nhds.mp hl) (ε / 3) (by linarith))
    let N := max N₁ N₂
    have hev_N := ((Metric.tendsto_nhds.mp (hL N)) (ε / 3) (by linarith))
    filter_upwards [hev_N, self_mem_nhdsWithin] with u huN hult
    have huK : u ≤ (K : ℝ≥0) := le_trans (le_of_lt hult) htK
    have h1 : dist (g u) (f N u) < ε / 3 := by rw [dist_comm]; exact hN₁ N (le_max_left _ _) u huK
    have h3 : dist (L N) l < ε / 3 := hN₂ N (le_max_right _ _)
    linarith [dist_triangle (g u) (f N u) l, dist_triangle (f N u) (L N) l]

/-- Lemma 3.5: Existence of the `d`-dimensional compensated small-jump Lévy process. -/
private lemma exists_compensated_small_jump_rdLevy {d : ℕ}
    (ν : Measure (Fin d → ℝ)) (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ L : RdLevyProcess d Ω P,
          ∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I * ((innerRd θ (L.X t ω) : ℝ) : ℂ)) ∂P =
              Complex.exp (-(t : ℝ) *
                ∫ x in {x : Fin d → ℝ | normRd x < 1},
                  (1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) +
                    Complex.I * ((innerRd θ x : ℝ) : ℂ)) ∂ν) := by
  obtain ⟨ε, hε0, hε_pos, hε_dec, hε_tend, hε_sq⟩ := exists_small_jump_shells ν hzero hLevy
  have hε_anti : Antitone ε := antitone_nat_of_succ_le fun n => le_of_lt (hε_dec n)
  have hε_le1 : ∀ n, ε n ≤ 1 := fun n => hε0 ▸ hε_anti (Nat.zero_le n)
  let S : ℕ → Set (Fin d → ℝ) := fun n => {x : Fin d → ℝ | ε (n + 1) ≤ normRd x ∧ normRd x < ε n}
  have hS_meas : ∀ n, MeasurableSet (S n) := fun n => by
    show MeasurableSet ({x : Fin d → ℝ | ε (n + 1) ≤ normRd x} ∩ {x : Fin d → ℝ | normRd x < ε n})
    exact (measurableSet_le measurable_const (by unfold normRd; fun_prop)).inter
      (measurableSet_lt (by unfold normRd; fun_prop) measurable_const)
  have hS_disj : Pairwise (fun m n => Disjoint (S m) (S n)) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have : ε n ≤ ε (m + 1) := hε_anti (Nat.succ_le_of_lt hlt)
      linarith [hx1.1, hx2.2]
    · have : ε m ≤ ε (n + 1) := hε_anti (Nat.succ_le_of_lt hgt)
      linarith [hx2.1, hx1.2]
  have hμ_fin : ∀ n, (ν.restrict (S n)) Set.univ < ⊤ := fun n => by
    rw [Measure.restrict_apply_univ]
    calc ν (S n) ≤ ν {x : Fin d → ℝ | ε (n + 1) ≤ normRd x} := measure_mono fun x hx => hx.1
      _ < ⊤ := levyMeasure_tail_lt_top ν hLevy (hε_pos (n + 1))
  have hμ_bdd : ∀ n, ∀ᵐ x ∂(ν.restrict (S n)), ∀ i : Fin d, |x i| ≤ 1 := fun n => by
    rw [MeasureTheory.ae_restrict_iff' (hS_meas n)]
    refine Filter.Eventually.of_forall fun x hx i => ?_
    have hxi_le : |x i| ≤ normRd x := by
      unfold normRd
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
    exact le_trans hxi_le (le_trans (le_of_lt hx.2) (hε_le1 n))
  -- Build independent compensated shell processes `(Ωn n, Pn n, Zn n)`
  choose Ωn mΩn Pn hPn Zn hZn_cf hZn_mom using
    fun n => exists_compensated_shell_rdLevy (ν.restrict (S n)) (hμ_fin n) (hμ_bdd n)
  letI : ∀ n, MeasurableSpace (Ωn n) := mΩn
  letI : ∀ n, IsProbabilityMeasure (Pn n) := hPn
  let Ω := ∀ n : ℕ, Ωn n
  let P : Measure Ω := Measure.infinitePi Pn
  have hint_eval : ∀ (k : ℕ) (f : Ωn k → ℂ), Measurable f →
      ∫ ω, f (ω k) ∂P = ∫ ω₀, f ω₀ ∂(Pn k) := fun k f hf => by
    have hmap : P.map (fun ω : Ω => ω k) = Pn k := Measure.infinitePi_map_eval Pn k
    rw [← hmap, integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable]
  -- Partial sums `W N t ω` and limit `X t ω`
  let W : ℕ → ℝ≥0 → Ω → (Fin d → ℝ) := fun N t ω =>
    ∑ n ∈ Finset.range N, (Zn n).X t (ω n)
  have hW_meas : ∀ N t, Measurable (W N t) := fun N t =>
    Finset.measurable_sum _ fun n _ => ((Zn n).measurable t).comp (measurable_pi_apply n)
  let X : ℝ≥0 → Ω → (Fin d → ℝ) := fun t ω =>
    Filter.limUnder Filter.atTop (fun N => W N t ω)
  have hX_meas : ∀ t, Measurable (X t) := fun t =>
    (MeasureTheory.StronglyMeasurable.limUnder fun N => (hW_meas N t).stronglyMeasurable).measurable
  -- Uniform convergence of `W N · ω` on every `[0, K]` almost surely via Doob + Borel-Cantelli
  have htail_bound : ∀ (K : ℕ) (i : Fin d) (n : ℕ), 1 ≤ n →
      P { ω : Ω | ∃ t : ℝ≥0, t ≤ (K : ℝ≥0) ∧ ((1 : ℝ) / (2 : ℝ) ^ n) < |(Zn n).X t (ω n) i| } ≤
        ENNReal.ofReal ((K : ℝ) / (4 : ℝ) ^ n) := by
    intro K i n hn
    have hmap : P.map (fun ω : Ω => ω n) = Pn n := Measure.infinitePi_map_eval Pn n
    let δn : ℝ≥0 := ⟨(1 : ℝ) / (2 : ℝ) ^ n, by positivity⟩
    have hδn_pos : 0 < δn := by change (0 : ℝ) < 1 / (2 : ℝ) ^ n; positivity
    let A_n : Set (Ωn n) := { ω₀ : Ωn n | ∃ t : ℝ≥0, t ≤ (K : ℝ≥0) ∧ (δn : ℝ) < |(Zn n).X t ω₀ i| }
    have hpre_eq : { ω : Ω | ∃ t : ℝ≥0, t ≤ (K : ℝ≥0) ∧ ((1 : ℝ) / (2 : ℝ) ^ n) < |(Zn n).X t (ω n) i| } =
        (fun ω : Ω => ω n) ⁻¹' A_n := rfl
    have hle_map : P ((fun ω : Ω => ω n) ⁻¹' A_n) ≤ Pn n A_n := by
      rw [← hmap]
      exact Measure.le_map_apply (measurable_pi_apply n).aemeasurable A_n
    have hvar_n : ∀ t : ℝ≥0, Integrable (fun ω₀ => ((Zn n).X t ω₀ i) ^ (2 : ℕ)) (Pn n) ∧
        ∫ ω₀, ((Zn n).X t ω₀ i) ^ (2 : ℕ) ∂(Pn n) ≤ (t : ℝ) * ((1 : ℝ) / (16 : ℝ) ^ n) := by
      intro t
      obtain ⟨_, _, hint2, hval2⟩ := hZn_mom n t i
      refine ⟨hint2, ?_⟩
      rw [hval2]
      refine mul_le_mul_of_nonneg_left ?_ t.coe_nonneg
      have hint_Sn : IntegrableOn (fun x : Fin d → ℝ => ∑ j : Fin d, x j ^ (2 : ℕ)) (S n) ν := by
        refine (levyMeasure_integrableOn_sq_small ν hLevy).mono_set fun x hx =>
          lt_of_lt_of_le hx.2 (hε_le1 n)
      have hint_i : IntegrableOn (fun x : Fin d → ℝ => x i ^ (2 : ℕ)) (S n) ν := by
        refine hint_Sn.mono' (continuous_apply i |>.pow 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      calc ∫ x in S n, x i ^ (2 : ℕ) ∂ν
          ≤ ∫ x in S n, (∑ j : Fin d, x j ^ (2 : ℕ)) ∂ν :=
            setIntegral_mono_on hint_i hint_Sn (hS_meas n) fun x _ =>
              Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
        _ ≤ ∫ x in {x : Fin d → ℝ | normRd x < ε n}, (∑ j : Fin d, x j ^ (2 : ℕ)) ∂ν := by
            refine setIntegral_mono_set ((levyMeasure_integrableOn_sq_small ν hLevy).mono_set
              fun x hx => lt_of_lt_of_le hx (hε_le1 n))
              (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun j _ => sq_nonneg _)
              (Filter.Eventually.of_forall fun x hx => hx.2)
        _ ≤ (1 : ℝ) / (16 : ℝ) ^ n := hε_sq n hn
    have hmax_n := rdLevy_maximal_tail_bound (Zn n) i (by positivity)
      (fun t => ⟨(hZn_mom n t i).1, (hZn_mom n t i).2.1⟩) hvar_n (K : ℝ≥0) hδn_pos
    have hrhs_eq : ((K : ℝ≥0) : ℝ) * ((1 : ℝ) / (16 : ℝ) ^ n) / (δn : ℝ) ^ (2 : ℕ) =
        (K : ℝ) / (4 : ℝ) ^ n := by
      change (K : ℝ) * ((1 : ℝ) / (16 : ℝ) ^ n) / ((1 : ℝ) / (2 : ℝ) ^ n) ^ (2 : ℕ) =
        (K : ℝ) / (4 : ℝ) ^ n
      have h16 : (16 : ℝ) ^ n = (4 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ (2 : ℕ) := by
        rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num; rw [← mul_pow]; norm_num
      have h2ne : (2 : ℝ) ^ n ≠ 0 := by positivity
      have h4ne : (4 : ℝ) ^ n ≠ 0 := by positivity
      rw [h16]
      field_simp
    rw [hpre_eq]
    calc P ((fun ω : Ω => ω n) ⁻¹' A_n)
        ≤ Pn n A_n := hle_map
      _ ≤ ENNReal.ofReal (((K : ℝ≥0) : ℝ) * ((1 : ℝ) / (16 : ℝ) ^ n) / (δn : ℝ) ^ (2 : ℕ)) := hmax_n
      _ = ENNReal.ofReal ((K : ℝ) / (4 : ℝ) ^ n) := by rw [hrhs_eq]
  -- Borel-Cantelli gives a.s. uniform geometric decay on `[0, K]` for all `K` and `i`
  have hae_geom : ∀ᵐ ω ∂P, ∀ (K : ℕ) (i : Fin d),
      ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ t : ℝ≥0, t ≤ (K : ℝ≥0) → |(Zn n).X t (ω n) i| ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    rw [ae_all_iff]; intro K
    rw [ae_all_iff]; intro i
    let bad : ℕ → Set Ω := fun n =>
      { ω : Ω | ∃ t : ℝ≥0, t ≤ (K : ℝ≥0) ∧ ((1 : ℝ) / (2 : ℝ) ^ n) < |(Zn n).X t (ω n) i| }
    have hsum_ne_top : (∑' n : ℕ, P (bad n)) ≠ ⊤ := by
      have hgeo : Summable (fun n : ℕ => (K : ℝ) / (4 : ℝ) ^ n) := by
        have h : (fun n : ℕ => (K : ℝ) / (4 : ℝ) ^ n) = fun n => (K : ℝ) * ((1 / 4 : ℝ) ^ n) := by
          funext n; simp [div_eq_mul_inv, one_div, inv_pow]
        rw [h]
        exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      have htail_lt : (∑' n : ℕ, P (bad (n + 1))) < ⊤ := by
        calc ∑' n : ℕ, P (bad (n + 1))
            ≤ ∑' n : ℕ, ENNReal.ofReal ((K : ℝ) / (4 : ℝ) ^ (n + 1)) :=
              ENNReal.tsum_le_tsum fun n => htail_bound K i (n + 1) (Nat.succ_pos n)
          _ ≤ ∑' n : ℕ, ENNReal.ofReal ((K : ℝ) / (4 : ℝ) ^ n) :=
              ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal (by
                apply div_le_div_of_nonneg_left (Nat.cast_nonneg K) (by positivity)
                exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
          _ < ⊤ := by
              rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hgeo]
              exact ENNReal.ofReal_lt_top
      have hle_sum : ∑' n : ℕ, P (bad n) ≤ P (bad 0) + ∑' n : ℕ, P (bad (n + 1)) := by
        rw [ENNReal.tsum_eq_iSup_nat]
        refine iSup_le fun N => ?_
        cases N with
        | zero => simp
        | succ N =>
          rw [Finset.sum_range_succ', add_comm]
          exact add_le_add_right (ENNReal.sum_le_tsum (Finset.range N)) _
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨measure_ne_top P _, htail_lt.ne⟩) hle_sum
    have hbc := MeasureTheory.measure_limsup_atTop_eq_zero hsum_ne_top
    have hae_not : ∀ᵐ ω ∂P, ω ∉ Filter.limsup bad Filter.atTop := by
      rw [ae_iff]
      have heq : {ω : Ω | ¬ ω ∉ Filter.limsup bad Filter.atTop} = Filter.limsup bad Filter.atTop := by
        ext ω; simp
      rw [heq]; exact hbc
    filter_upwards [hae_not] with ω hω
    rw [Filter.limsup_eq_iInf_iSup_of_nat] at hω
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion,
      not_forall, not_exists] at hω
    obtain ⟨N₀, hN₀⟩ := hω
    refine ⟨N₀, fun n hn t htK => ?_⟩
    have hnot : ω ∉ bad n := hN₀ n hn
    simp only [bad, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hnot
    exact hnot t htK
  have hae_cadlag_all : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((∀ t : ℝ≥0, ContinuousWithinAt (fun s => (Zn n).X s (ω n)) (Set.Ici t) t) ∧
       (∀ t : ℝ≥0, 0 < t → ∃ l : Fin d → ℝ,
         Tendsto (fun s => (Zn n).X s (ω n)) (nhdsWithin t (Set.Iio t)) (nhds l))) ∧
      (Zn n).X 0 (ω n) = 0 := by
    rw [ae_all_iff]; intro n
    have hmap : P.map (fun ω : Ω => ω n) = Pn n := Measure.infinitePi_map_eval Pn n
    have hmp : MeasurePreserving (fun ω : Ω => ω n) P (Pn n) :=
      ⟨measurable_pi_apply n, hmap⟩
    exact hmp.quasiMeasurePreserving.ae ((Zn n).cadlag.and (Zn n).start_zero)
  -- On the full-measure event, `W N · ω` converges uniformly on `[0, K]` to `X · ω`
  have hae_unif : ∀ᵐ ω ∂P,
      (∀ (K : ℕ) (η : ℝ), 0 < η → ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ≥0, t ≤ (K : ℝ≥0) →
        dist (W n t ω) (X t ω) < η) ∧
      (∀ t : ℝ≥0, Tendsto (fun N => W N t ω) atTop (nhds (X t ω))) := by
    filter_upwards [hae_geom] with ω hω
    have hconv_coord : ∀ (t : ℝ≥0) (i : Fin d), Summable (fun n : ℕ => (Zn n).X t (ω n) i) := by
      intro t i
      let K : ℕ := Nat.ceil (t : ℝ)
      have htK : t ≤ (K : ℝ≥0) := by
        change (t : ℝ) ≤ (Nat.ceil (t : ℝ) : ℝ); exact Nat.le_ceil _
      obtain ⟨N₀, hN₀⟩ := hω K i
      rw [← summable_nat_add_iff N₀]
      have hgeom0 : Summable (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) := by
        have : (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) = fun n => (1 / 2 : ℝ) ^ n := by
          funext n; simp [one_div, inv_pow]
        rw [this]; exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
      have hgeom : Summable (fun k : ℕ => (1 : ℝ) / (2 : ℝ) ^ (k + N₀)) :=
        (summable_nat_add_iff N₀).mpr hgeom0
      refine Summable.of_norm_bounded hgeom fun k => ?_
      rw [Real.norm_eq_abs]
      exact hN₀ (k + N₀) (Nat.le_add_left N₀ k) t htK
    have htend_W : ∀ t : ℝ≥0, Tendsto (fun N => W N t ω) atTop (nhds (X t ω)) := by
      intro t
      have hex : ∃ l : Fin d → ℝ, Tendsto (fun N => W N t ω) atTop (nhds l) := by
        refine ⟨fun i => ∑' n : ℕ, (Zn n).X t (ω n) i, ?_⟩
        rw [tendsto_pi_nhds]
        intro i
        simpa [W, Finset.sum_apply] using (hconv_coord t i).hasSum.tendsto_sum_nat
      obtain ⟨l, hl⟩ := hex
      have hlim_eq : X t ω = l := hl.limUnder_eq
      rwa [hlim_eq]
    refine ⟨fun K η hη => ?_, htend_W⟩
    -- Find uniform tail index across all `i : Fin d`
    choose N₀ hN₀ using fun i : Fin d => hω K i
    let M₀ : ℕ := Finset.univ.sup N₀
    obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℕ, (2 : ℝ) / (2 : ℝ) ^ M₁ < η := by
      have ht : Tendsto (fun m : ℕ => (2 : ℝ) / (2 : ℝ) ^ m) atTop (nhds 0) := by
        have : (fun m : ℕ => (2 : ℝ) / (2 : ℝ) ^ m) = fun m => (2 : ℝ) * ((1 / 2 : ℝ) ^ m) := by
          funext m; simp [div_eq_mul_inv, inv_pow]
        rw [this]
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
      exact (ht.eventually (Iio_mem_nhds hη)).exists
    refine ⟨max M₀ M₁, fun N hN t htK => ?_⟩
    rw [dist_pi_lt_iff hη]
    intro i
    have htail_le : ∀ m ≥ N, |W m t ω i - W N t ω i| ≤ (2 : ℝ) / (2 : ℝ) ^ N := by
      intro m hm
      have hdiff : W m t ω i - W N t ω i = ∑ n ∈ Finset.Ico N m, (Zn n).X t (ω n) i := by
        simp only [W, Finset.sum_apply]
        rw [← Finset.sum_range_add_sum_Ico _ hm, add_sub_cancel_left]
      rw [hdiff]
      calc |∑ n ∈ Finset.Ico N m, (Zn n).X t (ω n) i|
          ≤ ∑ n ∈ Finset.Ico N m, |(Zn n).X t (ω n) i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.Ico N m, ((1 : ℝ) / (2 : ℝ) ^ n) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hni : N₀ i ≤ n := le_trans (Finset.le_sup (Finset.mem_univ i))
              (le_trans (le_max_left M₀ M₁) (le_trans hN (Finset.mem_Ico.mp hn).1))
            exact hN₀ i n hni t htK
        _ ≤ (2 : ℝ) / (2 : ℝ) ^ N := by
            have hgeom_sum : ∀ k : ℕ, ∑ j ∈ Finset.range k, ((1 : ℝ) / (2 : ℝ) ^ (N + j)) ≤
                (2 : ℝ) / (2 : ℝ) ^ N := by
              intro k
              have hfac : ∑ j ∈ Finset.range k, ((1 : ℝ) / (2 : ℝ) ^ (N + j)) =
                  ((1 : ℝ) / (2 : ℝ) ^ N) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [pow_add, one_div, mul_inv, one_div, one_div, inv_pow]
              rw [hfac, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
              have hpos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ N := by positivity
              have hle2 : ((1 / 2 : ℝ) ^ k - 1) / ((1 / 2 : ℝ) - 1) ≤ 2 := by
                have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
                have hdiv : ((1 / 2 : ℝ) ^ k - 1) / ((1 / 2 : ℝ) - 1) = 2 * (1 - (1 / 2 : ℝ) ^ k) := by ring
                linarith
              calc ((1 : ℝ) / (2 : ℝ) ^ N) * (((1 / 2 : ℝ) ^ k - 1) / ((1 / 2 : ℝ) - 1))
                  ≤ ((1 : ℝ) / (2 : ℝ) ^ N) * 2 := mul_le_mul_of_nonneg_left hle2 (le_of_lt hpos)
                _ = (2 : ℝ) / (2 : ℝ) ^ N := by ring
            have hreindex : ∑ n ∈ Finset.Ico N m, ((1 : ℝ) / (2 : ℝ) ^ n) =
                ∑ j ∈ Finset.range (m - N), ((1 : ℝ) / (2 : ℝ) ^ (N + j)) := by
              rw [Finset.sum_Ico_eq_sum_range]
            rw [hreindex]
            exact hgeom_sum (m - N)
    have htend_i : Tendsto (fun m => |W m t ω i - W N t ω i|) atTop (nhds |X t ω i - W N t ω i|) :=
      (((tendsto_pi_nhds.mp (htend_W t)) i).sub tendsto_const_nhds).abs
    have hle_lim : |X t ω i - W N t ω i| ≤ (2 : ℝ) / (2 : ℝ) ^ N :=
      le_of_tendsto htend_i (Filter.eventually_atTop.mpr ⟨N, htail_le⟩)
    rw [Real.dist_eq, abs_sub_comm]
    have hle_M1 : (2 : ℝ) / (2 : ℝ) ^ N ≤ (2 : ℝ) / (2 : ℝ) ^ M₁ := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (le_trans (le_max_right M₀ M₁) hN)
    exact lt_of_le_of_lt (le_trans hle_lim hle_M1) hM₁
  -- Càdlàg paths and `X 0 = 0` a.e.
  have hX_cadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
      (∀ t : ℝ≥0, 0 < t → ∃ l : Fin d → ℝ,
        Tendsto (fun s => X s ω) (nhdsWithin t (Set.Iio t)) (nhds l)) := by
    filter_upwards [hae_cadlag_all, hae_unif] with ω hcad ⟨hunif, _⟩
    refine cadlag_of_tendsto_uniform_on_Iic (fun N t => W N t ω) (fun t => X t ω) (fun N => ?_) hunif
    induction N with
    | zero =>
      simp only [W, Finset.range_zero, Finset.sum_empty]
      exact ⟨fun t => continuousWithinAt_const, fun t _ => ⟨0, tendsto_const_nhds⟩⟩
    | succ N ih =>
      have hsucc : (fun t => W (N + 1) t ω) = fun t => W N t ω + (Zn N).X t (ω N) := by
        funext t; simp [W, Finset.sum_range_succ]
      rw [hsucc]
      refine ⟨fun t => (ih.1 t).add ((hcad N).1.1 t), fun t ht => ?_⟩
      obtain ⟨l1, hl1⟩ := ih.2 t ht
      obtain ⟨l2, hl2⟩ := (hcad N).1.2 t ht
      exact ⟨l1 + l2, hl1.add hl2⟩
  have hX_zero : ∀ᵐ ω ∂P, X 0 ω = 0 := by
    filter_upwards [hae_cadlag_all, hae_unif] with ω hcad ⟨_, htend⟩
    have hW0 : ∀ N, W N 0 ω = 0 := fun N => by
      simp only [W]
      refine Finset.sum_eq_zero fun n _ => (hcad n).2
    have hconst : Tendsto (fun N => W N 0 ω) atTop (nhds (0 : Fin d → ℝ)) := by
      simp_rw [hW0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (htend 0) hconst
  -- Stationary increments via `Measure.ext_of_charFunDual` + DCT
  have hX_stat : ∀ {s t : ℝ≥0}, s ≤ t → P.map (fun ω => X t ω - X s ω) = P.map (X (t - s)) := by
    intro s t hst
    have hmeas_sub : Measurable (fun ω => X t ω - X s ω) := (hX_meas t).sub (hX_meas s)
    haveI : IsProbabilityMeasure (P.map (fun ω => X t ω - X s ω)) :=
      Measure.isProbabilityMeasure_map hmeas_sub.aemeasurable
    haveI : IsProbabilityMeasure (P.map (X (t - s))) :=
      Measure.isProbabilityMeasure_map (hX_meas (t - s)).aemeasurable
    apply Measure.ext_of_charFunDual
    ext L
    rw [charFunDual_apply, charFunDual_apply,
      integral_map hmeas_sub.aemeasurable (by fun_prop : Continuous fun v : Fin d → ℝ =>
        Complex.exp ((L v : ℂ) * Complex.I)).aestronglyMeasurable,
      integral_map (hX_meas (t - s)).aemeasurable (by fun_prop : Continuous fun v : Fin d → ℝ =>
        Complex.exp ((L v : ℂ) * Complex.I)).aestronglyMeasurable]
    have hLHS_tend : Tendsto (fun N : ℕ =>
        ∫ ω, Complex.exp (((L (W N t ω - W N s ω) : ℝ) : ℂ) * Complex.I) ∂P)
        atTop (nhds (∫ ω, Complex.exp (((L (X t ω - X s ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const 1) ?_ ?_
      · intro N
        exact ((by fun_prop : Continuous fun v : Fin d → ℝ =>
          Complex.exp ((L v : ℂ) * Complex.I)).measurable.comp ((hW_meas N t).sub (hW_meas N s))).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      · filter_upwards [hae_unif] with ω ⟨_, htend⟩
        exact ((by fun_prop : Continuous fun v : Fin d → ℝ =>
          Complex.exp ((L v : ℂ) * Complex.I)).continuousAt.tendsto).comp
          ((htend t).sub (htend s))
    have hRHS_tend : Tendsto (fun N : ℕ =>
        ∫ ω, Complex.exp (((L (W N (t - s) ω) : ℝ) : ℂ) * Complex.I) ∂P)
        atTop (nhds (∫ ω, Complex.exp (((L (X (t - s) ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const 1) ?_ ?_
      · intro N
        exact ((by fun_prop : Continuous fun v : Fin d → ℝ =>
          Complex.exp ((L v : ℂ) * Complex.I)).measurable.comp (hW_meas N (t - s))).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      · filter_upwards [hae_unif] with ω ⟨_, htend⟩
        exact ((by fun_prop : Continuous fun v : Fin d → ℝ =>
          Complex.exp ((L v : ℂ) * Complex.I)).continuousAt.tendsto).comp (htend (t - s))
    have heq_N : ∀ N : ℕ,
        ∫ ω, Complex.exp (((L (W N t ω - W N s ω) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω, Complex.exp (((L (W N (t - s) ω) : ℝ) : ℂ) * Complex.I) ∂P := by
      intro N
      have hprod1 : ∀ ω, Complex.exp (((L (W N t ω - W N s ω) : ℝ) : ℂ) * Complex.I) =
          ∏ n : Fin N, Complex.exp (((L ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        have hsub : W N t ω - W N s ω = ∑ n : Fin N, ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) := by
          simp only [W, ← Finset.sum_sub_distrib]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X t (ω n) - (Zn n).X s (ω n)) N).symm
        rw [hsub, map_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      have hprod2 : ∀ ω, Complex.exp (((L (W N (t - s) ω) : ℝ) : ℂ) * Complex.I) =
          ∏ n : Fin N, Complex.exp (((L ((Zn n.val).X (t - s) (ω n.val)) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        have hsum : W N (t - s) ω = ∑ n : Fin N, (Zn n.val).X (t - s) (ω n.val) := by
          simp only [W]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X (t - s) (ω n)) N).symm
        rw [hsum, map_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      simp_rw [hprod1, hprod2]
      have hcontL : Continuous fun v : Fin d → ℝ => Complex.exp (((L v : ℝ) : ℂ) * Complex.I) := by
        fun_prop
      have hind1 : ProbabilityTheory.iIndepFun
          (fun (n : Fin N) (ω : Ω) =>
            Complex.exp (((L ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I)) P :=
        (ProbabilityTheory.iIndepFun_infinitePi fun n =>
          hcontL.measurable.comp (((Zn n).measurable t).sub ((Zn n).measurable s))).precomp Fin.val_injective
      have hind2 : ProbabilityTheory.iIndepFun
          (fun (n : Fin N) (ω : Ω) =>
            Complex.exp (((L ((Zn n.val).X (t - s) (ω n.val)) : ℝ) : ℂ) * Complex.I)) P :=
        (ProbabilityTheory.iIndepFun_infinitePi fun n =>
          hcontL.measurable.comp ((Zn n).measurable (t - s))).precomp Fin.val_injective
      rw [hind1.integral_fun_prod_eq_prod_integral (fun n =>
            (hcontL.measurable.comp ((((Zn n.val).measurable t).sub ((Zn n.val).measurable s)).comp
              (measurable_pi_apply n.val))).aestronglyMeasurable),
        hind2.integral_fun_prod_eq_prod_integral (fun n =>
            (hcontL.measurable.comp (((Zn n.val).measurable (t - s)).comp
              (measurable_pi_apply n.val))).aestronglyMeasurable)]
      refine Finset.prod_congr rfl fun n _ => ?_
      have h1 : ∫ ω, Complex.exp (((L ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω₀, Complex.exp (((L ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I) ∂(Pn n.val) :=
        hint_eval n.val _ (hcontL.measurable.comp (((Zn n.val).measurable t).sub ((Zn n.val).measurable s)))
      have h2 : ∫ ω, Complex.exp (((L ((Zn n.val).X (t - s) (ω n.val)) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω₀, Complex.exp (((L ((Zn n.val).X (t - s) ω₀) : ℝ) : ℂ) * Complex.I) ∂(Pn n.val) :=
        hint_eval n.val _ (hcontL.measurable.comp ((Zn n.val).measurable (t - s)))
      rw [h1, h2]
      have hmeas_sub_n : Measurable (fun ω₀ => (Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) :=
        ((Zn n.val).measurable t).sub ((Zn n.val).measurable s)
      have hstat_n := (Zn n.val).stationary_increments s t hst
      rw [← integral_map hmeas_sub_n.aemeasurable hcontL.aestronglyMeasurable,
        hstat_n, integral_map ((Zn n.val).measurable (t - s)).aemeasurable hcontL.aestronglyMeasurable]
    simp_rw [heq_N] at hLHS_tend
    exact tendsto_nhds_unique hLHS_tend hRHS_tend
  -- Independent increments via `indep_past_of_finset` + `Measure.ext_of_charFunDual` + DCT
  have hX_indep : ∀ {s t : ℝ≥0}, s ≤ t →
      ProbabilityTheory.Indep
        (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance)
        (⨆ u ∈ Set.Iic s, MeasurableSpace.comap (X u) inferInstance) P := by
    intro s t hst
    refine indep_past_of_finset hX_meas ((hX_meas t).sub (hX_meas s)) fun p u hu => ?_
    let Y : Ω → (Fin d → ℝ) := fun ω => X t ω - X s ω
    let Zp : Ω → (Fin p → (Fin d → ℝ)) := fun ω j => X (u j) ω
    have hY_meas : Measurable Y := (hX_meas t).sub (hX_meas s)
    have hZp_meas : Measurable Zp := measurable_pi_lambda _ fun j => hX_meas (u j)
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hY_meas.aemeasurable hZp_meas.aemeasurable]
    haveI : IsProbabilityMeasure (P.map (fun ω => (Y ω, Zp ω))) :=
      Measure.isProbabilityMeasure_map (hY_meas.prodMk hZp_meas).aemeasurable
    haveI : IsProbabilityMeasure ((P.map Y).prod (P.map Zp)) := by
      haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY_meas.aemeasurable
      haveI : IsProbabilityMeasure (P.map Zp) := Measure.isProbabilityMeasure_map hZp_meas.aemeasurable
      infer_instance
    apply Measure.ext_of_charFunDual
    ext L
    let L₁ : StrongDual ℝ (Fin d → ℝ) := L.comp (ContinuousLinearMap.inl ℝ (Fin d → ℝ) (Fin p → Fin d → ℝ))
    let L₂ : StrongDual ℝ (Fin p → Fin d → ℝ) := L.comp (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin p → Fin d → ℝ))
    have hL_split : ∀ (v : Fin d → ℝ) (w : Fin p → Fin d → ℝ), L (v, w) = L₁ v + L₂ w := fun v w => by
      have hv : (v, w) = (v, (0 : Fin p → Fin d → ℝ)) + ((0 : Fin d → ℝ), w) := by
        simp [Prod.mk_add_mk]
      conv_lhs => rw [hv, map_add]
      rfl
    have hcontL : Continuous fun q : (Fin d → ℝ) × (Fin p → Fin d → ℝ) =>
        Complex.exp (((L q : ℝ) : ℂ) * Complex.I) := by fun_prop
    have hcontL₁ : Continuous fun v : Fin d → ℝ => Complex.exp (((L₁ v : ℝ) : ℂ) * Complex.I) := by fun_prop
    have hcontL₂ : Continuous fun w : Fin p → Fin d → ℝ => Complex.exp (((L₂ w : ℝ) : ℂ) * Complex.I) := by fun_prop
    rw [charFunDual_apply, charFunDual_apply,
      integral_map (hY_meas.prodMk hZp_meas).aemeasurable hcontL.aestronglyMeasurable]
    have hRHS_prod :
        ∫ q : (Fin d → ℝ) × (Fin p → Fin d → ℝ), Complex.exp (((L q : ℝ) : ℂ) * Complex.I)
          ∂((P.map Y).prod (P.map Zp)) =
        (∫ ω, Complex.exp (((L₁ (Y ω) : ℝ) : ℂ) * Complex.I) ∂P) *
        (∫ ω, Complex.exp (((L₂ (Zp ω) : ℝ) : ℂ) * Complex.I) ∂P) := by
      have hfactor : ∀ q : (Fin d → ℝ) × (Fin p → Fin d → ℝ),
          Complex.exp (((L q : ℝ) : ℂ) * Complex.I) =
            Complex.exp (((L₁ q.1 : ℝ) : ℂ) * Complex.I) * Complex.exp (((L₂ q.2 : ℝ) : ℂ) * Complex.I) := by
        intro ⟨v, w⟩
        rw [hL_split v w, Complex.ofReal_add, add_mul, Complex.exp_add]
      simp_rw [hfactor]
      haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY_meas.aemeasurable
      haveI : IsProbabilityMeasure (P.map Zp) := Measure.isProbabilityMeasure_map hZp_meas.aemeasurable
      rw [MeasureTheory.integral_prod_mul
            (f := fun v : Fin d → ℝ => Complex.exp (((L₁ v : ℝ) : ℂ) * Complex.I))
            (g := fun w : Fin p → Fin d → ℝ => Complex.exp (((L₂ w : ℝ) : ℂ) * Complex.I)),
        integral_map hY_meas.aemeasurable hcontL₁.aestronglyMeasurable,
        integral_map hZp_meas.aemeasurable hcontL₂.aestronglyMeasurable]
    rw [hRHS_prod]
    let YN : ℕ → Ω → (Fin d → ℝ) := fun N ω => W N t ω - W N s ω
    let ZN : ℕ → Ω → (Fin p → Fin d → ℝ) := fun N ω j => W N (u j) ω
    have hLHS_tend : Tendsto (fun N : ℕ =>
        ∫ ω, Complex.exp (((L (YN N ω, ZN N ω) : ℝ) : ℂ) * Complex.I) ∂P)
        atTop (nhds (∫ ω, Complex.exp (((L (Y ω, Zp ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const 1) ?_ ?_
      · intro N
        exact (hcontL.measurable.comp (((hW_meas N t).sub (hW_meas N s)).prodMk
          (measurable_pi_lambda _ fun j => hW_meas N (u j)))).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      · filter_upwards [hae_unif] with ω ⟨_, htend⟩
        refine (hcontL.continuousAt.tendsto).comp ?_
        exact ((htend t).sub (htend s)).prodMk_nhds (tendsto_pi_nhds.mpr fun j => htend (u j))
    have hR1_tend : Tendsto (fun N : ℕ =>
        ∫ ω, Complex.exp (((L₁ (YN N ω) : ℝ) : ℂ) * Complex.I) ∂P)
        atTop (nhds (∫ ω, Complex.exp (((L₁ (Y ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const 1) ?_ ?_
      · intro N
        exact (hcontL₁.measurable.comp ((hW_meas N t).sub (hW_meas N s))).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      · filter_upwards [hae_unif] with ω ⟨_, htend⟩
        exact (hcontL₁.continuousAt.tendsto).comp ((htend t).sub (htend s))
    have hR2_tend : Tendsto (fun N : ℕ =>
        ∫ ω, Complex.exp (((L₂ (ZN N ω) : ℝ) : ℂ) * Complex.I) ∂P)
        atTop (nhds (∫ ω, Complex.exp (((L₂ (Zp ω) : ℝ) : ℂ) * Complex.I) ∂P)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
        (integrable_const 1) ?_ ?_
      · intro N
        exact (hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => hW_meas N (u j))).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      · filter_upwards [hae_unif] with ω ⟨_, htend⟩
        exact (hcontL₂.continuousAt.tendsto).comp (tendsto_pi_nhds.mpr fun j => htend (u j))
    have heq_N : ∀ N : ℕ,
        ∫ ω, Complex.exp (((L (YN N ω, ZN N ω) : ℝ) : ℂ) * Complex.I) ∂P =
          (∫ ω, Complex.exp (((L₁ (YN N ω) : ℝ) : ℂ) * Complex.I) ∂P) *
          (∫ ω, Complex.exp (((L₂ (ZN N ω) : ℝ) : ℂ) * Complex.I) ∂P) := by
      intro N
      have hprodL : ∀ ω, Complex.exp (((L (YN N ω, ZN N ω) : ℝ) : ℂ) * Complex.I) =
          ∏ n : Fin N, (Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I)) := by
        intro ω
        have hY_sum : YN N ω = ∑ n : Fin N, ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) := by
          simp only [YN, W, ← Finset.sum_sub_distrib]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X t (ω n) - (Zn n).X s (ω n)) N).symm
        have hZ_sum : ZN N ω = ∑ n : Fin N, (fun j : Fin p => (Zn n.val).X (u j) (ω n.val)) := by
          funext j
          simp only [ZN, W, Finset.sum_apply]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X (u j) (ω n)) N).symm
        rw [hL_split, hY_sum, hZ_sum, map_sum, map_sum, Complex.ofReal_add, Complex.ofReal_sum,
          Complex.ofReal_sum, add_mul, Finset.sum_mul, Finset.sum_mul, Complex.exp_add,
          Complex.exp_sum, Complex.exp_sum, Finset.prod_mul_distrib]
      have hprod1 : ∀ ω, Complex.exp (((L₁ (YN N ω) : ℝ) : ℂ) * Complex.I) =
          ∏ n : Fin N, Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        have hY_sum : YN N ω = ∑ n : Fin N, ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) := by
          simp only [YN, W, ← Finset.sum_sub_distrib]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X t (ω n) - (Zn n).X s (ω n)) N).symm
        rw [hY_sum, map_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      have hprod2 : ∀ ω, Complex.exp (((L₂ (ZN N ω) : ℝ) : ℂ) * Complex.I) =
          ∏ n : Fin N, Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        have hZ_sum : ZN N ω = ∑ n : Fin N, (fun j : Fin p => (Zn n.val).X (u j) (ω n.val)) := by
          funext j
          simp only [ZN, W, Finset.sum_apply]
          exact (Fin.sum_univ_eq_sum_range (fun n => (Zn n).X (u j) (ω n)) N).symm
        rw [hZ_sum, map_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      simp_rw [hprodL, hprod1, hprod2]
      have hindL : ProbabilityTheory.iIndepFun
          (fun (n : Fin N) (ω : Ω) =>
            Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I)) P :=
        (ProbabilityTheory.iIndepFun_infinitePi fun n =>
          (hcontL₁.measurable.comp (((Zn n).measurable t).sub ((Zn n).measurable s))).mul
          (hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => (Zn n).measurable (u j)))).precomp Fin.val_injective
      have hind1 : ProbabilityTheory.iIndepFun
          (fun (n : Fin N) (ω : Ω) =>
            Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I)) P :=
        (ProbabilityTheory.iIndepFun_infinitePi fun n =>
          hcontL₁.measurable.comp (((Zn n).measurable t).sub ((Zn n).measurable s))).precomp Fin.val_injective
      have hind2 : ProbabilityTheory.iIndepFun
          (fun (n : Fin N) (ω : Ω) =>
            Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I)) P :=
        (ProbabilityTheory.iIndepFun_infinitePi fun n =>
          hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => (Zn n).measurable (u j))).precomp Fin.val_injective
      rw [hindL.integral_fun_prod_eq_prod_integral (fun n =>
            ((hcontL₁.measurable.comp (((Zn n.val).measurable t).sub ((Zn n.val).measurable s))).mul
             (hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => (Zn n.val).measurable (u j)))).comp
              (measurable_pi_apply n.val) |>.aestronglyMeasurable),
        hind1.integral_fun_prod_eq_prod_integral (fun n =>
            (hcontL₁.measurable.comp (((Zn n.val).measurable t).sub ((Zn n.val).measurable s))).comp
              (measurable_pi_apply n.val) |>.aestronglyMeasurable),
        hind2.integral_fun_prod_eq_prod_integral (fun n =>
            (hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => (Zn n.val).measurable (u j))).comp
              (measurable_pi_apply n.val) |>.aestronglyMeasurable),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun n _ => ?_
      have hmp : MeasurePreserving (fun ω : Ω => ω n.val) P (Pn n.val) :=
        ⟨measurable_pi_apply n.val, Measure.infinitePi_map_eval Pn n.val⟩
      have hm1 : Measurable (fun ω₀ : Ωn n.val =>
          Complex.exp (((L₁ ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I)) :=
        hcontL₁.measurable.comp (((Zn n.val).measurable t).sub ((Zn n.val).measurable s))
      have hm2 : Measurable (fun ω₀ : Ωn n.val =>
          Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) ω₀) : ℝ) : ℂ) * Complex.I)) :=
        hcontL₂.measurable.comp (measurable_pi_lambda _ fun j => (Zn n.val).measurable (u j))
      have heq_f1 : ∫ ω, Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω₀, Complex.exp (((L₁ ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I) *
            Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) ω₀) : ℝ) : ℂ) * Complex.I) ∂(Pn n.val) :=
        hint_eval n.val _ (hm1.mul hm2)
      have heq_f2 : ∫ ω, Complex.exp (((L₁ ((Zn n.val).X t (ω n.val) - (Zn n.val).X s (ω n.val)) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω₀, Complex.exp (((L₁ ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I) ∂(Pn n.val) :=
        hint_eval n.val _ hm1
      have heq_f3 : ∫ ω, Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) (ω n.val)) : ℝ) : ℂ) * Complex.I) ∂P =
          ∫ ω₀, Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) ω₀) : ℝ) : ℂ) * Complex.I) ∂(Pn n.val) :=
        hint_eval n.val _ hm2
      rw [heq_f1, heq_f2, heq_f3]
      have hind_n : ProbabilityTheory.IndepFun
          (fun ω₀ : Ωn n.val => Complex.exp (((L₁ ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I))
          (fun ω₀ : Ωn n.val => Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) ω₀) : ℝ) : ℂ) * Complex.I))
          (Pn n.val) := by
        rw [ProbabilityTheory.IndepFun_iff_Indep]
        have hbase := (Zn n.val).indep_increments s t hst
        refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hbase ?_) ?_
        · have hm_past : @Measurable (Ωn n.val) ℂ
              (⨆ v ∈ Set.Iic s, MeasurableSpace.comap ((Zn n.val).X v) inferInstance) inferInstance
              (fun ω₀ => Complex.exp (((L₂ (fun j => (Zn n.val).X (u j) ω₀) : ℝ) : ℂ) * Complex.I)) := by
            refine hcontL₂.measurable.comp ?_
            refine @measurable_pi_lambda (Ωn n.val) (Fin p) _
              (⨆ v ∈ Set.Iic s, MeasurableSpace.comap ((Zn n.val).X v) inferInstance) _ _ fun j => ?_
            exact (comap_measurable ((Zn n.val).X (u j))).mono (le_iSup₂_of_le (u j) (hu j) le_rfl) le_rfl
          exact hm_past.comap_le
        · have hm_inc : @Measurable (Ωn n.val) ℂ
              (MeasurableSpace.comap (fun ω₀ => (Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) inferInstance) inferInstance
              (fun ω₀ => Complex.exp (((L₁ ((Zn n.val).X t ω₀ - (Zn n.val).X s ω₀) : ℝ) : ℂ) * Complex.I)) :=
            hcontL₁.measurable.comp (comap_measurable _)
          exact hm_inc.comap_le
      exact hind_n.integral_fun_mul_eq_mul_integral hm1.aestronglyMeasurable hm2.aestronglyMeasurable
    simp_rw [heq_N] at hLHS_tend
    exact tendsto_nhds_unique hLHS_tend (hR1_tend.mul hR2_tend)
  -- Assemble RdLevyProcess and prove characteristic function
  let L : RdLevyProcess d Ω P :=
    { X := X
      measurable := hX_meas
      cadlag := hX_cadlag
      start_zero := hX_zero
      indep_increments := fun s t hst => hX_indep hst
      stationary_increments := fun s t hst => hX_stat hst }
  refine ⟨Ω, inferInstance, P, inferInstance, L, fun t θ => ?_⟩
  have hcont_exp : Continuous fun v : Fin d → ℝ =>
      Complex.exp (Complex.I * ((innerRd θ v : ℝ) : ℂ)) := by unfold innerRd; fun_prop
  have hLHS_tend : Tendsto (fun N : ℕ =>
      ∫ ω, Complex.exp (Complex.I * ((innerRd θ (W N t ω) : ℝ) : ℂ)) ∂P)
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ((innerRd θ (X t ω) : ℝ) : ℂ)) ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_
      (integrable_const 1) ?_ ?_
    · intro N
      exact (hcont_exp.measurable.comp (hW_meas N t)).aestronglyMeasurable
    · intro N
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Complex.norm_exp_I_mul_ofReal]
    · filter_upwards [hae_unif] with ω ⟨_, htend⟩
      exact (hcont_exp.continuousAt.tendsto).comp (htend t)
  let g_levy : (Fin d → ℝ) → ℂ := fun x =>
    1 - Complex.exp (Complex.I * ((innerRd θ x : ℝ) : ℂ)) + Complex.I * ((innerRd θ x : ℝ) : ℂ)
  have hband_eq : ∀ N : ℕ, {x : Fin d → ℝ | ε N ≤ normRd x ∧ normRd x < 1} =
      ⋃ n ∈ Finset.range N, S n := by
    intro N
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, S]
    constructor
    · intro ⟨hxN, hx1⟩
      induction N with
      | zero => rw [hε0] at hxN; linarith
      | succ k ih =>
        by_cases hxk : ε k ≤ normRd x
        · obtain ⟨n, hnk, hn⟩ := ih hxk
          exact ⟨n, Nat.lt_succ_of_lt hnk, hn⟩
        · exact ⟨k, Nat.lt_succ_self k, hxN, lt_of_not_ge hxk⟩
    · rintro ⟨n, hnN, h1, h2⟩
      exact ⟨le_trans (hε_anti (Nat.succ_le_of_lt hnN)) h1, lt_of_lt_of_le h2 (hε_le1 n)⟩
  have hW_cf : ∀ N : ℕ,
      ∫ ω, Complex.exp (Complex.I * ((innerRd θ (W N t ω) : ℝ) : ℂ)) ∂P =
        Complex.exp (-(t : ℝ) * ∫ x in {x : Fin d → ℝ | ε N ≤ normRd x ∧ normRd x < 1}, g_levy x ∂ν) := by
    intro N
    have hprod : ∀ ω, Complex.exp (Complex.I * ((innerRd θ (W N t ω) : ℝ) : ℂ)) =
        ∏ n : Fin N, Complex.exp (Complex.I * ((innerRd θ ((Zn n.val).X t (ω n.val)) : ℝ) : ℂ)) := by
      intro ω
      have hlin : innerRd θ (W N t ω) = ∑ n : Fin N, innerRd θ ((Zn n.val).X t (ω n.val)) := by
        rw [Fin.sum_univ_eq_sum_range (fun n => innerRd θ ((Zn n).X t (ω n))) N]
        simp only [W, innerRd, Finset.sum_apply, Finset.mul_sum]
        exact Finset.sum_comm
      rw [hlin, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    simp_rw [hprod]
    have hind : ProbabilityTheory.iIndepFun
        (fun (n : Fin N) (ω : Ω) =>
          Complex.exp (Complex.I * ((innerRd θ ((Zn n.val).X t (ω n.val)) : ℝ) : ℂ))) P :=
      (ProbabilityTheory.iIndepFun_infinitePi fun n =>
        hcont_exp.measurable.comp ((Zn n).measurable t)).precomp Fin.val_injective
    rw [hind.integral_fun_prod_eq_prod_integral (fun n =>
      (hcont_exp.measurable.comp (((Zn n.val).measurable t).comp (measurable_pi_apply n.val))).aestronglyMeasurable)]
    have hfac : ∀ n : Fin N,
        ∫ ω, Complex.exp (Complex.I * ((innerRd θ ((Zn n.val).X t (ω n.val)) : ℝ) : ℂ)) ∂P =
          Complex.exp (-(t : ℝ) * ∫ x in S n.val, g_levy x ∂ν) := by
      intro n
      have hcf_n : ∫ ω, Complex.exp (Complex.I * ((innerRd θ ((Zn n.val).X t (ω n.val)) : ℝ) : ℂ)) ∂P =
          ∫ ω₀, Complex.exp (Complex.I * ((innerRd θ ((Zn n.val).X t ω₀) : ℝ) : ℂ)) ∂(Pn n.val) :=
        hint_eval n.val _ (hcont_exp.measurable.comp ((Zn n.val).measurable t))
      rw [hcf_n, hZn_cf n.val t θ]
    simp_rw [hfac, ← Complex.exp_sum, ← Finset.mul_sum]
    congr 2
    have hg_int_small : IntegrableOn g_levy {x : Fin d → ℝ | normRd x < 1} ν := by
      have hcont_g : Continuous g_levy := by unfold g_levy innerRd; fun_prop
      let Cθ : ℝ := (∑ i : Fin d, θ i ^ (2 : ℕ)) / 2
      have hdom : IntegrableOn (fun x : Fin d → ℝ => Cθ * ∑ i : Fin d, x i ^ (2 : ℕ))
          {x : Fin d → ℝ | normRd x < 1} ν :=
        (levyMeasure_integrableOn_sq_small ν hLevy).const_mul Cθ
      refine hdom.mono' hcont_g.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      have hcs : (innerRd θ x) ^ (2 : ℕ) ≤ (∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ)) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ x
      calc ‖g_levy x‖
          ≤ (innerRd θ x) ^ (2 : ℕ) / 2 := norm_one_sub_exp_I_add_I_le (innerRd θ x)
        _ ≤ ((∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ))) / 2 :=
            div_le_div_of_nonneg_right hcs (by norm_num)
        _ = Cθ * ∑ i : Fin d, x i ^ (2 : ℕ) := by dsimp only [Cθ]; ring
    rw [hband_eq N, MeasureTheory.integral_biUnion_finset (Finset.range N) (fun n _ => hS_meas n)
      (fun m _ n _ hmn => hS_disj hmn) (fun n _ => hg_int_small.mono_set fun x hx =>
        lt_of_lt_of_le hx.2 (hε_le1 n))]
    exact Fin.sum_univ_eq_sum_range (fun n => ∫ x in S n, g_levy x ∂ν) N
  -- Take `N → ∞` on RHS via DCT on `{x | normRd x < 1}`
  have hRHS_tend : Tendsto (fun N : ℕ =>
      Complex.exp (-(t : ℝ) * ∫ x in {x : Fin d → ℝ | ε N ≤ normRd x ∧ normRd x < 1}, g_levy x ∂ν))
      atTop (nhds (Complex.exp (-(t : ℝ) * ∫ x in {x : Fin d → ℝ | normRd x < 1}, g_levy x ∂ν))) := by
    refine (Complex.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.comp ?_
    let G : ℕ → (Fin d → ℝ) → ℂ := fun N x =>
      Set.indicator {x : Fin d → ℝ | ε N ≤ normRd x} g_levy x
    have hG_eq : ∀ N : ℕ,
        ∫ x in {x : Fin d → ℝ | ε N ≤ normRd x ∧ normRd x < 1}, g_levy x ∂ν =
          ∫ x in {x : Fin d → ℝ | normRd x < 1}, G N x ∂ν := by
      intro N
      have hmN : MeasurableSet {x : Fin d → ℝ | ε N ≤ normRd x} :=
        measurableSet_le measurable_const (by unfold normRd; fun_prop)
      rw [MeasureTheory.integral_indicator hmN, Measure.restrict_restrict hmN]
      rfl
    simp_rw [hG_eq]
    let Cθ : ℝ := (∑ i : Fin d, θ i ^ (2 : ℕ)) / 2
    have hdom : IntegrableOn (fun x : Fin d → ℝ => Cθ * ∑ i : Fin d, x i ^ (2 : ℕ))
        {x : Fin d → ℝ | normRd x < 1} ν :=
      (levyMeasure_integrableOn_sq_small ν hLevy).const_mul Cθ
    have hcont_g : Continuous g_levy := by unfold g_levy innerRd; fun_prop
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => Cθ * ∑ i : Fin d, x i ^ (2 : ℕ)) ?_ hdom ?_ ?_
    · intro N
      have hmN : MeasurableSet {x : Fin d → ℝ | ε N ≤ normRd x} :=
        measurableSet_le measurable_const (by unfold normRd; fun_prop)
      exact (hcont_g.measurable.indicator hmN).aestronglyMeasurable
    · intro N
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ {x : Fin d → ℝ | ε N ≤ normRd x}
      · simp only [G, Set.indicator_of_mem hx]
        have hcs : (innerRd θ x) ^ (2 : ℕ) ≤ (∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ)) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ x
        calc ‖g_levy x‖
            ≤ (innerRd θ x) ^ (2 : ℕ) / 2 := norm_one_sub_exp_I_add_I_le (innerRd θ x)
          _ ≤ ((∑ i : Fin d, θ i ^ (2 : ℕ)) * (∑ i : Fin d, x i ^ (2 : ℕ))) / 2 :=
              div_le_div_of_nonneg_right hcs (by norm_num)
          _ = Cθ * ∑ i : Fin d, x i ^ (2 : ℕ) := by dsimp only [Cθ]; ring
      · simp only [G, Set.indicator_of_notMem hx, norm_zero]
        exact mul_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num))
          (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · have hne0 : ∀ᵐ x ∂(ν.restrict {x : Fin d → ℝ | normRd x < 1}), x ≠ 0 := by
        rw [ae_iff]
        have hset : {x : Fin d → ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
        rw [hset]
        refine le_antisymm ?_ (by positivity)
        calc (ν.restrict {x : Fin d → ℝ | normRd x < 1}) {0} ≤ ν {0} := Measure.restrict_le_self _
          _ = 0 := hzero
      filter_upwards [hne0] with x hx
      have hpos : 0 < normRd x := by
        have hsum_pos : 0 < ∑ i : Fin d, x i ^ (2 : ℕ) := by
          have hex : ∃ i : Fin d, x i ≠ 0 := by
            by_contra hall; push_neg at hall; exact hx (funext hall)
          obtain ⟨i₀, hi₀⟩ := hex
          calc 0 < x i₀ ^ (2 : ℕ) := sq_pos_of_ne_zero hi₀
            _ ≤ ∑ i : Fin d, x i ^ (2 : ℕ) :=
              Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i₀)
        exact Real.sqrt_pos.mpr hsum_pos
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hε_tend.eventually (Iio_mem_nhds hpos)] with N hN
      have hmem : x ∈ {x : Fin d → ℝ | ε N ≤ normRd x} := le_of_lt hN
      simp only [G, Set.indicator_of_mem hmem]
  simp_rw [hW_cf] at hLHS_tend
  exact tendsto_nhds_unique hLHS_tend hRHS_tend

end Exercise210Helpers

/-! ## Section 4: Top-level Theorem `solution` -/

theorem solution
    (d : ℕ) (hd : 1 < d) (a : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    (hAsymm : A.transpose = A)
    (hApos : ∀ v : Fin d → ℝ,
      0 ≤ ∑ i : Fin d, ∑ j : Fin d, v i * A i j * v j)
    (ν : Measure (Fin d → ℝ))
    (hzero : ν {0} = 0)
    (hLevy : (∫⁻ x, ENNReal.ofReal
      (min 1 (Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) ^ (2 : ℕ))) ∂ν) < ⊤) :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ X : ℝ≥0 → Ω → (Fin d → ℝ),
          (∀ᵐ ω ∂P,
            (∀ t : ℝ≥0,
              ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
            ∀ t : ℝ≥0, 0 < t →
              ∃ l : Fin d → ℝ,
                Tendsto (fun s => X s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
          (∀ᵐ ω ∂P, X 0 ω = 0) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            ProbabilityTheory.Indep
              (MeasurableSpace.comap
                (fun ω => X t ω - X s ω) inferInstance)
              (⨆ u ∈ Set.Iic s,
                MeasurableSpace.comap (X u) inferInstance) P) ∧
          (∀ (s t : ℝ≥0), s ≤ t →
            P.map (fun ω => X t ω - X s ω) =
              P.map (X (t - s))) ∧
          (∀ (t : ℝ≥0) (θ : Fin d → ℝ),
            ∫ ω, Complex.exp (Complex.I *
              (((∑ i : Fin d, θ i * X t ω i : ℝ)) : ℂ)) ∂P =
            Complex.exp (-(t : ℝ) *
              (Complex.I *
                (((∑ i : Fin d, a i * θ i : ℝ)) : ℂ) +
               (((∑ i : Fin d, ∑ j : Fin d,
                   θ i * A i j * θ j : ℝ) / 2) : ℂ) +
               ∫ x, (1 -
                 Complex.exp (Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) +
                 Complex.I *
                   (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ) *
                   (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν))) := by
  have _ := hd
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, L₁, hcf₁⟩ :=
    Exercise210Helpers.exists_gaussian_drift_rdLevy a A hAsymm hApos
  letI : MeasurableSpace Ω₁ := mΩ₁
  letI : IsProbabilityMeasure P₁ := hP₁
  have hlarge_fin : (ν.restrict {x : Fin d → ℝ | 1 ≤ Exercise210Helpers.normRd x}) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact Exercise210Helpers.levyMeasure_tail_lt_top ν hLevy one_pos
  obtain ⟨Ω₂, mΩ₂, P₂, hP₂, L₂, hcf₂, _⟩ :=
    Exercise210Helpers.exists_compound_poisson_rdLevy
      (ν.restrict {x : Fin d → ℝ | 1 ≤ Exercise210Helpers.normRd x}) hlarge_fin
  letI : MeasurableSpace Ω₂ := mΩ₂
  letI : IsProbabilityMeasure P₂ := hP₂
  obtain ⟨Ω₃, mΩ₃, P₃, hP₃, L₃, hcf₃⟩ :=
    Exercise210Helpers.exists_compensated_small_jump_rdLevy ν hzero hLevy
  letI : MeasurableSpace Ω₃ := mΩ₃
  letI : IsProbabilityMeasure P₃ := hP₃
  let L₂₃ := Exercise210Helpers.sum_two_indep_rdLevy L₂ L₃
  let L := Exercise210Helpers.sum_two_indep_rdLevy L₁ L₂₃
  refine ⟨Ω₁ × (Ω₂ × Ω₃), inferInstance, P₁.prod (P₂.prod P₃), inferInstance, L.X,
    L.cadlag, L.start_zero, L.indep_increments, L.stationary_increments, fun t θ => ?_⟩
  change ∫ ω, Complex.exp (Complex.I * ((Exercise210Helpers.innerRd θ (L.X t ω) : ℝ) : ℂ))
      ∂(P₁.prod (P₂.prod P₃)) = _
  rw [Exercise210Helpers.sum_two_indep_rdLevy_charFun L₁ L₂₃ t θ,
    Exercise210Helpers.sum_two_indep_rdLevy_charFun L₂ L₃ t θ,
    hcf₁ t θ, hcf₂ t θ, hcf₃ t θ, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hsplit := Exercise210Helpers.levy_integral_split ν hLevy θ
  have hrhs :
      ∫ x, (1 - Complex.exp (Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ)) +
        Complex.I * ((∑ i : Fin d, θ i * x i : ℝ) : ℂ) *
          (if Real.sqrt (∑ i : Fin d, x i ^ (2 : ℕ)) < 1 then 1 else 0)) ∂ν =
      (∫ x in {x : Fin d → ℝ | 1 ≤ Exercise210Helpers.normRd x},
        (1 - Complex.exp (Complex.I * ((Exercise210Helpers.innerRd θ x : ℝ) : ℂ))) ∂ν) +
      (∫ x in {x : Fin d → ℝ | Exercise210Helpers.normRd x < 1},
        (1 - Complex.exp (Complex.I * ((Exercise210Helpers.innerRd θ x : ℝ) : ℂ)) +
          Complex.I * ((Exercise210Helpers.innerRd θ x : ℝ) : ℂ)) ∂ν) := hsplit
  rw [hrhs]
  ring
