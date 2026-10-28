-- Prove2me | solution 1 for ItoCalculusII.continuous_product_rule_fixed_time
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:13:52.517506+00:00
-- url     : https://prove2.me/submissions/5284e8b6-7d8c-414a-9f59-1ce4673a93ab

import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_itoFormula_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_add_readable
import Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
import Theorems.Thm_ItoLemma_exists_smooth_fin_two_bump_plateau
import Theorems.Thm_ItoLemma_fin_two_truncated_product_smooth_compact_plateau
import Theorems.Thm_ItoLemma_fin_two_truncated_product_derivatives_eq_on_plateau_interior
import Theorems.Thm_ItoLemma_coordDeriv_norm_le_fderiv_norm
import Theorems.Thm_ItoLemma_fin_two_product_gradient_hasFDerivAt
import Theorems.Thm_ItoLemma_fin_two_smooth_compact_iterated_derivatives_bounded
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_readable
import Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime_readable
import Theorems.Thm_LevyStochCalc_Probability_exists_lt_exitTime_readable
import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime
import Mathlib

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

namespace S88U

lemma prog_add {Ω : Type u} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {A B : Ω → ℝ → ℝ} (hA : Probability.ProgressivelyMeasurable ℱ A)
    (hB : Probability.ProgressivelyMeasurable ℱ B) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)

lemma sq_bdd {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → ℝ → ℝ} {c : ℝ} (h : ∀ ω s, ‖A ω s‖ ≤ c) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  have hc : ∀ ω s, (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖c‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    gcongr
    have := h ω s
    exact_mod_cast (show ‖A ω s‖ ≤ ‖c‖ from this.trans (Real.le_norm_self c))
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hc ω s
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top

lemma fderiv_prod (z : Fin 2 → ℝ) :
    HasFDerivAt (fun y : Fin 2 → ℝ => y 0 * y 1)
      (z 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        z 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)) z :=
  (hasFDerivAt_apply 0 z).mul (hasFDerivAt_apply 1 z)

lemma unif_gen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (Fin 2 → ℝ) → F) (hc : Continuous g) (hs : HasCompactSupport g) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin 2 → ℝ, ‖z - w‖ < δ → ‖g z - g w‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 (hs.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ, hδ, fun z w hzw => ?_⟩
  have := h (show dist z w < δ by rwa [dist_eq_norm])
  rw [dist_eq_norm] at this; exact this.le

set_option maxHeartbeats 1000000 in
lemma analytic (R : ℝ) (hR : 0 < R) :
    ∃ (f : (Fin 2 → ℝ) → ℝ) (f' : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ)
      (f'' : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      (∀ z, HasFDerivAt f (f' z) z) ∧ (∀ z, HasFDerivAt f' (f'' z) z) ∧
      (∀ z, ‖f' z‖ ≤ K₁) ∧ 0 ≤ K₂ ∧ (∀ z, ‖f'' z‖ ≤ K₂) ∧ Continuous f'' ∧ Continuous f' ∧
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin 2 → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε) ∧
      (∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → f z = z 0 * z 1) ∧
      (∀ z : Fin 2 → ℝ, ‖z‖ < R →
        coordDeriv f' 0 z = z 1 ∧ coordDeriv f' 1 z = z 0 ∧
        coordDeriv₂ f'' 0 0 z = 0 ∧ coordDeriv₂ f'' 0 1 z = 1 ∧
        coordDeriv₂ f'' 1 0 z = 1 ∧ coordDeriv₂ f'' 1 1 z = 0) := by
  obtain ⟨ψ, hψ, hψs, hψp, -⟩ := ItoLemma.exists_smooth_fin_two_bump_plateau R hR.le
  obtain ⟨hfs, hfc, hfp⟩ := ItoLemma.fin_two_truncated_product_smooth_compact_plateau R ψ hψ hψs hψp
  obtain ⟨f, hfdef⟩ : ∃ f : (Fin 2 → ℝ) → ℝ, f = fun z => ψ z * (z 0 * z 1) := ⟨_, rfl⟩
  rw [← hfdef] at hfs hfc
  have hfp' : ∀ z : Fin 2 → ℝ, ‖z‖ ≤ R → f z = z 0 * z 1 := fun z hz => by rw [hfdef]; exact hfp z hz
  have hdiff : ∀ z, HasFDerivAt f (fderiv ℝ f z) z := fun z =>
    (hfs.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hf1 : ContDiff ℝ 2 (fderiv ℝ f) := hfs.fderiv_right (WithTop.coe_le_coe.2 le_top)
  have hdiff' : ∀ z, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z := fun z =>
    (hf1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hf2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hf1.fderiv_right one_add_one_eq_two.le
  have hc1 : Continuous (fderiv ℝ f) := hf1.continuous
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) := hf2.continuous
  have hs1 : HasCompactSupport (fderiv ℝ f) := hfc.fderiv (𝕜 := ℝ)
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hs1.fderiv (𝕜 := ℝ)
  obtain ⟨K, -, hK⟩ := ItoLemma.fin_two_smooth_compact_iterated_derivatives_bounded f hfs hfc
  have hK₁ : ∀ z, ‖fderiv ℝ f z‖ ≤ K := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact hK 1 (by norm_num) z
  have hK₂' : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K := fun z => by
    have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1) (x := z)
    rw [norm_iteratedFDeriv_one] at e
    have h2 : ‖iteratedFDeriv ℝ (1 + 1) f z‖ ≤ K := hK 2 le_rfl z
    first | exact e.symm.le.trans h2 | exact e.le.trans h2 | exact e.ge.trans h2 | exact e.symm.ge.trans h2
  have hK₂ : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ max K 0 := fun z => (hK₂' z).trans (le_max_left _ _)
  have hunif' := unif_gen _ hf2.continuous hs2
  -- coordinate derivatives on the plateau
  have hcd : ∀ z : Fin 2 → ℝ, ‖z‖ < R →
      coordDeriv (fderiv ℝ f) 0 z = z 1 ∧ coordDeriv (fderiv ℝ f) 1 z = z 0 ∧
      coordDeriv₂ (fderiv ℝ (fderiv ℝ f)) 0 0 z = 0 ∧
      coordDeriv₂ (fderiv ℝ (fderiv ℝ f)) 0 1 z = 1 ∧
      coordDeriv₂ (fderiv ℝ (fderiv ℝ f)) 1 0 z = 1 ∧
      coordDeriv₂ (fderiv ℝ (fderiv ℝ f)) 1 1 z = 0 := by
    intro z hz
    obtain ⟨e1, e2⟩ :=
      ItoLemma.fin_two_truncated_product_derivatives_eq_on_plateau_interior R ψ hψp z hz
    have g1 : fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1) = fun x =>
        x 0 • (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
          x 1 • (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) := by
      funext x; exact (fderiv_prod x).fderiv
    have g2 : HasFDerivAt (fderiv ℝ (fun y : Fin 2 → ℝ => y 0 * y 1))
        ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
        (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)) z := by
      rw [g1]
      exact ItoLemma.fin_two_product_gradient_hasFDerivAt z
    simp only [coordDeriv, coordDeriv₂]
    rw [hfdef, e1, e2, g2.fderiv, g1]
    simp
  exact ⟨_, _, _, K, max K 0, hdiff, hdiff', hK₁, le_max_right _ _, hK₂, hc2, hc1, hunif',
    hfp', hcd⟩


lemma exit_isStoppingTime {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (X : Ω → ℝ → (Fin 2 → ℝ)) (hc : ∀ ω, Continuous (X ω)) (ha : ∀ t, Measurable[ℱ t] (fun ω => X ω t))
    (R : ℝ) : IsStoppingTime ℱ (Probability.exitTime X R) := by
  intro t
  by_cases ht : 0 ≤ t
  · have key : {ω | Probability.exitTime X R ω ≤ t} =
        (⋃ n : ℕ, ⋂ q : ℚ, {ω | ‖X ω (max 0 (min t (q : ℝ)))‖ ≤ R - 1 / ((n : ℝ) + 1)})ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter]
      rw [Probability.exitTime_le_iff_readable (hc ω)]
      have hcl : Continuous fun r : ℝ => ‖X ω (max 0 (min t r))‖ :=
        ((hc ω).comp (continuous_const.max (continuous_const.min continuous_id))).norm
      constructor
      · rintro ⟨s, hs, hRs⟩ ⟨n, hn⟩
        have hall : ∀ r : ℝ, ‖X ω (max 0 (min t r))‖ ≤ R - 1 / ((n : ℝ) + 1) := fun r =>
          Rat.denseRange_cast.induction_on (p := fun r => ‖X ω (max 0 (min t r))‖ ≤
            R - 1 / ((n : ℝ) + 1)) r (isClosed_le hcl continuous_const) hn
        have h1 := hall s
        rw [min_eq_right hs.2, max_eq_right hs.1] at h1
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro h
        by_contra hne
        push_neg at hne
        obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
          (Set.nonempty_Icc.2 ht) ((hc ω).norm.continuousOn (s := Set.Icc 0 t))
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hne s₀ hs₀))
        refine h ⟨n, fun q => ?_⟩
        have hm : max 0 (min t (q : ℝ)) ∈ Set.Icc 0 t :=
          ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
        have := hmax hm
        simp only [Set.mem_setOf_eq] at this
        linarith
    rw [key]
    refine MeasurableSet.compl (m := ℱ t) (MeasurableSet.iUnion (m := ℱ t) fun n =>
      MeasurableSet.iInter (m := ℱ t) fun q => ?_)
    have hq : Measurable[ℱ t] (fun ω => X ω (max 0 (min t (q : ℝ)))) :=
      (ha _).mono (ℱ.mono (max_le ht (min_le_left _ _))) le_rfl
    exact (measurable_norm.comp hq) measurableSet_Iic
  · have key : {ω | Probability.exitTime X R ω ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [Probability.exitTime_le_iff_readable (hc ω)]
      rintro ⟨s, hs, -⟩
      exact ht (hs.1.trans hs.2)
    rw [key]; exact @MeasurableSet.empty _ (ℱ t)

end S88U

set_option maxHeartbeats 1600000 in
open S88U in
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    (H : Fin 2 → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin 2) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin 2 → ℝ)
    (bdrift : Fin 2 → Ω → ℝ → ℝ)
    (X : ℝ → Ω → Fin 2 → ℝ)
    (hX : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀m : ∀ p : Fin 2, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p : Fin 2, Measurable (Function.uncurry (bdrift p)))
    {B C : ℝ} (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hB : ∀ p ω s, |bdrift p ω s| ≤ B)
    (hCH : ∀ p k ω s, |H p k ω s| ≤ C)
    (hplusm : ∀ p q k, Measurable (Function.uncurry
      fun ω s => H p k ω s + H q k ω s))
    (hplusp : ∀ p q k, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => H p k ω s + H q k ω s))
    (hplusq : ∀ (p q : Fin 2) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hJm : ∀ k : Fin d, Measurable (Function.uncurry
      fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s))
    (hJp : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ
      (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s))
    (hJq : ∀ (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
 :
    (fun ω => X T ω 0 * X T ω 1 - X 0 ω 0 * X 0 ω 1) =ᵐ[P] fun ω =>
      (∫ s in Set.Ioc (0 : ℝ) T,
         (X s ω 1 * bdrift 0 ω s + X s ω 0 * bdrift 1 ω s +
           ∑ k : Fin d, H 0 k ω s * H 1 k ω s) ∂volume) +
      ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
        (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s)
        (hJm k) (hJp k) (hJq k) T ω := by
  -- the process facts
  have hXc : ∀ ω, Continuous fun t => X t ω := hX.continuous_path
  have hXa : ∀ t, Measurable[ℱ t] (X t) := fun t => (hX.adapted t).measurable
  have hXm : ∀ t, Measurable (X t) := fun t => (hXa t).mono (ℱ.le t) le_rfl
  have hXj : Measurable (fun q : Ω × ℝ => X q.2 q.1) :=
    (measurable_uncurry_of_continuous_of_measurable hXc hXm).comp measurable_swap
  obtain ⟨Y, hYdef⟩ : ∃ Y : Ω → ℝ → (Fin 2 → ℝ), Y = fun ω t => X t ω := ⟨_, rfl⟩
  have hYc : ∀ ω, Continuous (Y ω) := fun ω => by rw [hYdef]; exact hXc ω
  have hYn : ∀ ω s, ‖Y ω s‖ = ‖X s ω‖ := fun ω s => by rw [hYdef]
  have hτ : ∀ n : ℕ, IsStoppingTime ℱ (Probability.exitTime Y (n : ℝ)) := fun n =>
    exit_isStoppingTime ℱ Y hYc (fun t => by rw [hYdef]; exact hXa t) _
  have hbd : ∀ (n : ℕ) ω, ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime Y (n : ℝ) ω →
      ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ ≤ n := by
    intro n ω hω s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0
      by_contra hc
      push_neg at hc
      have h1 : Probability.exitTime Y (n : ℝ) ω ≤ ((0 : ℝ) : WithTop ℝ) :=
        (Probability.exitTime_le_iff_readable (hYc ω) _ _).2
          ⟨0, ⟨le_rfl, le_rfl⟩, by rw [hYn]; exact hc.le⟩
      have h2 : ((T : ℝ) : WithTop ℝ) ≤ ((0 : ℝ) : WithTop ℝ) := hω.trans h1
      have h3 : T ≤ 0 := by exact_mod_cast h2
      linarith
    · rw [← hYn]
      exact Probability.norm_le_of_le_exitTime_readable (hYc ω) hpos
        (le_trans (by exact_mod_cast hs.2) hω)
  have core : ∀ n : ℕ, ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime Y (n : ℝ) ω →
      X T ω 0 * X T ω 1 - X 0 ω 0 * X 0 ω 1 =
      (∫ s in Set.Ioc (0 : ℝ) T,
         (X s ω 1 * bdrift 0 ω s + X s ω 0 * bdrift 1 ω s +
           ∑ k : Fin d, H 0 k ω s * H 1 k ω s) ∂volume) +
      ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
        (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s)
        (hJm k) (hJp k) (hJq k) T ω := by
    intro n
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (n : ℝ) + 1 := ⟨_, rfl⟩
    have hR : 0 < R := by rw [hRdef]; positivity
    have hXRs : ∀ ω s, 0 < s → ((s : ℝ) : WithTop ℝ) ≤ Probability.exitTime Y (n : ℝ) ω →
        ‖X s ω‖ < R := fun ω s hs hsτ => by
      rw [← hYn]
      exact (Probability.norm_le_of_le_exitTime_readable (hYc ω) hs hsτ).trans_lt
        (by rw [hRdef]; linarith)
    obtain ⟨f, f', f'', K₁, K₂, hdiff, hdiff', hK₁, hK₂0, hK₂, hc2, hc1, hunif', hfp, hcd⟩ :=
      analytic R hR
    have hcdc : ∀ p : Fin 2, Continuous (coordDeriv (f') p) := fun p =>
      hc1.clm_apply continuous_const
    have hcdb : ∀ p z, ‖coordDeriv (f') p z‖ ≤ K₁ := fun p z =>
      (ItoLemma.coordDeriv_norm_le_fderiv_norm _ p z).trans (hK₁ z)
    set G : Fin 2 → Fin d → Ω → ℝ → ℝ := fun p k ω s => coordDeriv (f') p (X s ω) * H p k ω s
      with hGdef
    have hmg : ∀ p k, Measurable (Function.uncurry (G p k)) := fun p k =>
      ((hcdc p).measurable.comp hXj).mul (hHm p k)
    have hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ (G p k) := fun p k =>
      Probability.ProgressivelyMeasurable.mul
        (ItoLemma.continuous_adapted_composition_progressive hXc hXa (hcdc p)) (hHp p k)
    have hGb : ∀ p k ω s, ‖G p k ω s‖ ≤ K₁ * C := fun p k ω s => by
      simp only [hGdef, norm_mul]
      exact mul_le_mul (hcdb p _) (by simpa [Real.norm_eq_abs] using hCH p k ω s) (norm_nonneg _)
        ((norm_nonneg _).trans (hcdb p (X s ω)))
    have hqg : ∀ p k (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖G p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p k => sq_bdd (hGb p k)
    have hito := IsVectorItoVersion.itoFormula_readable hC0 hCH hX hX₀m hbm hB0 hB hplusm hplusp
      hplusq hdiff hdiff' hK₁ hK₂0 hK₂ hc2 hunif' hmg hpg hqg hT
    -- stochastic integrals
    have hSI : ∀ k : Fin d, ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime Y (n : ℝ) ω →
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (G 0 k) (hmg 0 k) (hpg 0 k) (hqg 0 k) T ω +
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (G 1 k) (hmg 1 k) (hpg 1 k) (hqg 1 k) T ω =
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s)
          (hJm k) (hJp k) (hJq k) T ω := by
      intro k
      have hma : Measurable (Function.uncurry fun ω s => G 0 k ω s + G 1 k ω s) :=
        (hmg 0 k).add (hmg 1 k)
      have hpa := prog_add (hpg 0 k) (hpg 1 k)
      have hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖G 0 k ω s + G 1 k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
        sq_bdd (c := K₁ * C + K₁ * C) fun ω s => (norm_add_le _ _).trans (add_le_add (hGb 0 k ω s) (hGb 1 k ω s))
      have h1 := stochasticIntegralBrownian_add_readable (W.W k) ℱ (hcoord k) (hmg 0 k) (hmg 1 k)
        (hpg 0 k) (hpg 1 k) (hqg 0 k) (hqg 1 k) hma hpa hqa hT
      have h2 := stochasticIntegralBrownian_congr_of_le_readable (Probability.exitTime Y (n : ℝ))
        (W.W k) ℱ (hcoord k) (hτ n) hma hpa hqa (hJm k) (hJp k) (hJq k)
        (fun ω s hs hsτ => by
          obtain ⟨c0, c1, -⟩ := hcd (X s ω) (hXRs ω s hs hsτ)
          simp only [hGdef, c0, c1]) hT
      filter_upwards [h1, h2] with ω e1 e2 hω
      rw [← e1, e2 hω]
    have hSI' : ∀ᵐ ω ∂P, ∀ k : Fin d, ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime Y (n : ℝ) ω →
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (G 0 k) (hmg 0 k) (hpg 0 k) (hqg 0 k) T ω +
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (G 1 k) (hmg 1 k) (hpg 1 k) (hqg 1 k) T ω =
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => X s ω 1 * H 0 k ω s + X s ω 0 * H 1 k ω s)
          (hJm k) (hJp k) (hJq k) T ω := ae_all_iff.2 hSI
    filter_upwards [hito, hSI'] with ω e1 e2 hω
    replace e2 := fun k => e2 k hω
    have hXR' : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ < R := fun s hs =>
      (hbd n ω hω s hs).trans_lt (by rw [hRdef]; linarith)
    -- endpoint values
    have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hTT : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
    have fT : f (X T ω) = X T ω 0 * X T ω 1 := hfp _ (hXR' T hTT).le
    have f0 : f (X 0 ω) = X 0 ω 0 * X 0 ω 1 := hfp _ (hXR' 0 hT0).le
    -- measurability in time and bounds
    have hXs : ∀ i : Fin 2, Measurable fun s => X s ω i := fun i =>
      ((continuous_apply i).comp (hXc ω)).measurable
    have hbs : ∀ p : Fin 2, Measurable fun s => bdrift p ω s := fun p =>
      (hbm p).comp measurable_prodMk_left
    have hHs' : ∀ p k, Measurable fun s => H p k ω s := fun p k =>
      (hHm p k).comp measurable_prodMk_left
    have hXb : ∀ i : Fin 2, ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω i‖ ≤ R := fun i s hs =>
      (norm_le_pi_norm (X s ω) i).trans (hXR' s (Set.Ioc_subset_Icc_self hs)).le
    have hfin : volume (Set.Ioc (0 : ℝ) T) ≠ ⊤ := by simp
    have iA : IntegrableOn (fun s => X s ω 1 * bdrift 0 ω s) (Set.Ioc (0 : ℝ) T) := by
      refine Measure.integrableOn_of_bounded (M := R * B) hfin
        ((hXs 1).mul (hbs 0)).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
      rw [norm_mul]
      exact mul_le_mul (hXb 1 s hs) (by simpa [Real.norm_eq_abs] using hB 0 ω s) (norm_nonneg _)
        hR.le
    have iB : IntegrableOn (fun s => X s ω 0 * bdrift 1 ω s) (Set.Ioc (0 : ℝ) T) := by
      refine Measure.integrableOn_of_bounded (M := R * B) hfin
        ((hXs 0).mul (hbs 1)).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
      rw [norm_mul]
      exact mul_le_mul (hXb 0 s hs) (by simpa [Real.norm_eq_abs] using hB 1 ω s) (norm_nonneg _)
        hR.le
    have iC : IntegrableOn (fun s => ∑ k : Fin d, H 0 k ω s * H 1 k ω s) (Set.Ioc (0 : ℝ) T) := by
      refine integrable_finsetSum _ fun k _ => ?_
      refine Measure.integrableOn_of_bounded (M := C * C) hfin
        ((hHs' 0 k).mul (hHs' 1 k)).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
      rw [norm_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hCH 0 k ω s)
        (by simpa [Real.norm_eq_abs] using hCH 1 k ω s) (norm_nonneg _) hC0
    -- rewrite the drift integrals on the plateau
    have cong : ∀ (g₁ g₂ : ℝ → ℝ), (∀ s ∈ Set.Ioc (0 : ℝ) T, g₁ s = g₂ s) →
        ∫ s in Set.Ioc (0 : ℝ) T, g₁ s = ∫ s in Set.Ioc (0 : ℝ) T, g₂ s :=
      fun g₁ g₂ h => setIntegral_congr_fun measurableSet_Ioc h
    have hpl : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω‖ < R := fun s hs =>
      hXR' s (Set.Ioc_subset_Icc_self hs)
    simp only [Fin.sum_univ_two] at e1
    rw [cong (fun s => coordDeriv f' 0 (X s ω) * bdrift 0 ω s) (fun s => X s ω 1 * bdrift 0 ω s) (fun s hs => by rw [(hcd _ (hpl s hs)).1]),
      cong (fun s => coordDeriv f' 1 (X s ω) * bdrift 1 ω s) (fun s => X s ω 0 * bdrift 1 ω s) (fun s hs => by rw [(hcd _ (hpl s hs)).2.1]),
      cong (fun s => coordDeriv₂ f'' 0 0 (X s ω) * ∑ k : Fin d, H 0 k ω s * H 0 k ω s) (fun _ => 0) (fun s hs => by rw [(hcd _ (hpl s hs)).2.2.1, zero_mul]),
      cong (fun s => coordDeriv₂ f'' 0 1 (X s ω) * ∑ k : Fin d, H 0 k ω s * H 1 k ω s) (fun s => ∑ k : Fin d, H 0 k ω s * H 1 k ω s)
        (fun s hs => by rw [(hcd _ (hpl s hs)).2.2.2.1, one_mul]),
      cong (fun s => coordDeriv₂ f'' 1 0 (X s ω) * ∑ k : Fin d, H 1 k ω s * H 0 k ω s) (fun s => ∑ k : Fin d, H 0 k ω s * H 1 k ω s)
        (fun s hs => by
          rw [(hcd _ (hpl s hs)).2.2.2.2.1, one_mul]
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _),
      cong (fun s => coordDeriv₂ f'' 1 1 (X s ω) * ∑ k : Fin d, H 1 k ω s * H 1 k ω s) (fun _ => 0) (fun s hs => by rw [(hcd _ (hpl s hs)).2.2.2.2.2, zero_mul]),
      fT, f0] at e1
    have iAB : IntegrableOn (fun s => X s ω 1 * bdrift 0 ω s + X s ω 0 * bdrift 1 ω s)
        (Set.Ioc (0 : ℝ) T) := iA.add iB
    rw [e1, integral_add iAB iC, integral_add iA iB, ← Finset.sum_add_distrib]
    simp only [integral_zero]
    rw [Finset.sum_congr rfl fun k _ => e2 k]
    ring
  filter_upwards [ae_all_iff.2 core] with ω hω
  obtain ⟨K, hK⟩ := Probability.exists_lt_exitTime_readable (hYc ω) hT.le
  exact hω K (hK K le_rfl).le
