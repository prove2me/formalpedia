-- Prove2me | solution 1 for Kyprianou.Ch01.queueExponentialMartingaleAndPassage
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:48:16.628873+00:00
-- url     : https://prove2.me/submissions/a595438f-2fa4-4760-b839-5fcdb4419fda

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_expMoment
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_indep_stationary
import Theorems.Thm_Kyprianou_Ch01_queueUpperPassageProbability
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The fibre `{jumpCount T t = n}` described by finitely/countably many inequalities. -/
theorem queueMart_aux_jumpCount_eq_iff (T : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ProbabilityTheory.jumpCount T t = n ↔
      ((t < T n ∧ ∀ k < n, T k ≤ t) ∨ (n = 0 ∧ ∀ k, T k ≤ t)) := by
  unfold ProbabilityTheory.jumpCount
  by_cases hne : ({k | t < T k} : Set ℕ).Nonempty
  · have hmem := Nat.sInf_mem hne
    constructor
    · intro h
      left
      refine ⟨h ▸ hmem, fun k hk => ?_⟩
      by_contra hc
      have := Nat.sInf_le (show k ∈ {k | t < T k} from lt_of_not_ge hc)
      omega
    · rintro (⟨h1, h2⟩ | ⟨h0, h2⟩)
      · apply le_antisymm (Nat.sInf_le h1)
        by_contra hc
        push Not at hc
        exact absurd (h2 _ hc) (not_le.mpr hmem)
      · obtain ⟨k, hk⟩ := hne
        exact absurd (h2 k) (not_le.mpr hk)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Nat.sInf_empty]
    have hall : ∀ k, T k ≤ t := by
      intro k
      by_contra hc
      have : k ∈ ({k | t < T k} : Set ℕ) := lt_of_not_ge hc
      rw [hne] at this
      exact this
    constructor
    · intro h; right; exact ⟨h.symm, hall⟩
    · rintro (⟨h1, -⟩ | ⟨h0, -⟩)
      · exact absurd (hall n) (not_le.mpr h1)
      · exact h0.symm

/-- Aggregate claims at a fixed time are measurable. -/
theorem queueMart_aux_aggregateClaims_measurable
    {Ω : Type*} [MeasurableSpace Ω] (arrival claims : ℕ → Ω → ℝ)
    (hA : ∀ n, Measurable (arrival n)) (hY : ∀ n, Measurable (claims n)) (t : ℝ≥0) :
    Measurable (aggregateClaims arrival claims t) := by
  classical
  set T : ℕ → Ω → ℝ := fun n ω => ProbabilityTheory.arrival arrival n ω with hT
  set N : Ω → ℕ := fun ω => ProbabilityTheory.jumpCount (fun n => T n ω) (t : ℝ) with hN
  have hTmeas : ∀ n, Measurable (T n) := fun n =>
    Finset.measurable_sum _ (fun i _ => hA i)
  have hNmeas : Measurable N := by
    refine measurable_to_countable' (fun n => ?_)
    have : N ⁻¹' {n} = ({ω | t < T n ω} ∩ ⋂ k ∈ Finset.range n, {ω | T k ω ≤ t}) ∪
        ({ω | n = 0} ∩ ⋂ k, {ω | T k ω ≤ t}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hN,
        queueMart_aux_jumpCount_eq_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_range]
      rfl
    rw [this]
    exact MeasurableSet.union (MeasurableSet.inter (measurableSet_lt measurable_const
      (hTmeas n)) (Finset.measurableSet_biInter _ fun k _ =>
        measurableSet_le (hTmeas k) measurable_const))
      (MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.iInter fun k =>
        measurableSet_le (hTmeas k) measurable_const))
  have hG : Measurable (fun p : Ω × ℕ => ∑ i ∈ Finset.range p.2, claims i p.1) :=
    measurable_from_prod_countable_left (fun n => by
      simpa using Finset.measurable_sum (Finset.range n) (fun i _ => hY i))
  have heq : aggregateClaims arrival claims t =
      (fun p : Ω × ℕ => ∑ i ∈ Finset.range p.2, claims i p.1) ∘ (fun ω => (ω, N ω)) := by
    funext ω
    simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath,
      hN, hT]
  rw [heq]
  exact hG.comp (measurable_id.prodMk hNmeas)

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (hPos : F (Set.Iic (0 : ℝ)) = 0)
    (hIntegrable : Integrable (fun z : ℝ => z) F)
    (mu : ℝ) (hMean : (∫ z, z ∂F) = mu)
    (hOverload : 1 < (rate : ℝ) * mu)
    (theta : ℝ) (hTheta : 0 < theta)
    (hRoot : queueLaplaceExponent rate F theta = 0) :
    let X : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω =>
        Real.exp (theta * X t ω -
          queueLaplaceExponent rate F theta * (t : ℝ))
    (∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) =
          (∫ ω in A, M s ω ∂P)) ∧
    ∀ x : ℝ, 0 < x →
      (P {ω | ∃ t : ℝ≥0, 0 < t ∧ x < X t ω}).toReal =
        Real.exp (-theta * x) := by
  intro X M
  set R : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims 1 0 with hR
  -- claims are a.s. positive, so aggregate claims are a.s. nonnegative
  have hclaims : ∀ᵐ ω ∂P, ∀ n, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    rw [ae_iff]
    have h := (hDriver.law_mark n).measure_eq (p := fun y : ℝ => y ≤ 0) measurableSet_Iic
    simp only [not_lt]
    rw [h]
    exact hPos
  have hSsum : ∀ (u : ℝ≥0) ω, aggregateClaims arrival claims u ω =
      ∑ i ∈ Finset.range (ProbabilityTheory.jumpCount
        (fun n => ProbabilityTheory.arrival arrival n ω) (u : ℝ)), claims i ω := by
    intro u ω
    simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]
  have hS0 : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 ≤ aggregateClaims arrival claims u ω := by
    filter_upwards [hclaims] with ω hω u
    rw [hSsum]
    exact Finset.sum_nonneg fun i _ => (hω i).le
  have hRu : ∀ u ω, R u ω = (u : ℝ) - aggregateClaims arrival claims u ω := by
    intro u ω
    simp [hR, riskSurplus]
  have hSmeas : ∀ u, Measurable (aggregateClaims arrival claims u) := fun u =>
    queueMart_aux_aggregateClaims_measurable arrival claims hDriver.measurable_interarrival
      hDriver.measurable_mark u
  have hRmeas : ∀ u, Measurable (R u) := by
    intro u
    have : R u = fun ω => (u : ℝ) - aggregateClaims arrival claims u ω := funext (hRu u)
    rw [this]
    exact measurable_const.sub (hSmeas u)
  -- integrability of the exponential of the surplus
  have hEint : ∀ u : ℝ≥0, Integrable (fun ω => Real.exp (theta * R u ω)) P := by
    intro u
    refine Integrable.mono' (integrable_const (Real.exp (theta * u)))
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [hS0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp, hRu]
    nlinarith [hω u]
  -- the exponential moment: E exp(θ X_u) = 1
  have hmom : ∀ u : ℝ≥0, 0 < u → ∫ ω, Real.exp (theta * R u ω) ∂P = 1 := by
    intro u hu
    have hint : Integrable (fun ω => Real.exp (-theta * aggregateClaims arrival claims u ω)) P := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [hS0] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [hω u])
    obtain ⟨hFint, hFeq⟩ := Kyprianou.Ch01.aggregateClaims_expMoment P arrival claims rate F
      hDriver hrate (-theta) u hu hint
    have hpsi : (rate : ℝ) * ((∫ y, Real.exp (-theta * y) ∂F) - 1) = -theta := by
      have h := hRoot
      unfold queueLaplaceExponent at h
      rw [integral_sub (integrable_const 1) hFint, integral_const] at h
      simp only [probReal_univ, smul_eq_mul, one_mul] at h
      linarith
    have hsplit : (fun ω => Real.exp (theta * R u ω)) = fun ω =>
        Real.exp (theta * u) * Real.exp (-theta * aggregateClaims arrival claims u ω) := by
      funext ω
      rw [hRu, ← Real.exp_add]
      ring_nf
    rw [hsplit, integral_const_mul, hFeq, ← Real.exp_add]
    have : (rate : ℝ) * (u : ℝ) * ((∫ y, Real.exp (-theta * y) ∂F) - 1) = -theta * u := by
      rw [mul_comm (rate : ℝ) (u : ℝ), mul_assoc, hpsi]; ring
    rw [this]
    simp
  -- the natural filtration
  have hnat_le : ∀ s, naturalSigma R s ≤ ‹MeasurableSpace Ω› := fun s =>
    iSup₂_le (fun u _ => (hRmeas u).comap_le)
  have hRnat : ∀ s, Measurable[naturalSigma R s] (R s) := fun s =>
    Measurable.of_comap_le
      (le_iSup₂ (f := fun u (_ : u ≤ s) => MeasurableSpace.comap (R u) inferInstance) s le_rfl)
  -- martingale identity
  have hmart : ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Ω, MeasurableSet[naturalSigma R s] A →
      (∫ ω in A, Real.exp (theta * R t ω) ∂P) = ∫ ω in A, Real.exp (theta * R s ω) ∂P := by
    intro s t hst A hA
    rcases eq_or_lt_of_le hst with rfl | hlt
    · rfl
    obtain ⟨hInd, hlaw⟩ := Kyprianou.Ch01.riskSurplus_increment_indep_stationary P arrival
      claims rate hrate F hDriver 1 s t hst
    set D : Ω → ℝ := fun ω => R t ω - R s ω with hD
    have hDmeas : Measurable D := (hRmeas t).sub (hRmeas s)
    have hDmom : ∫ ω, Real.exp (theta * D ω) ∂P = 1 := by
      have h1 : ∫ ω, Real.exp (theta * D ω) ∂P = ∫ y, Real.exp (theta * y) ∂(P.map D) :=
        (integral_map (f := fun y => Real.exp (theta * y)) hDmeas.aemeasurable
          (Measurable.aestronglyMeasurable (by fun_prop))).symm
      have h2 : ∫ y, Real.exp (theta * y) ∂(P.map (R (t - s))) =
          ∫ ω, Real.exp (theta * R (t - s) ω) ∂P :=
        integral_map (f := fun y => Real.exp (theta * y)) (hRmeas _).aemeasurable
          (Measurable.aestronglyMeasurable (by fun_prop))
      rw [h1, hlaw, h2, hmom _ (tsub_pos_of_lt hlt)]
    have hA' : MeasurableSet A := hnat_le s A hA
    set X1 : Ω → ℝ := A.indicator (fun ω => Real.exp (theta * R s ω)) with hX1
    set X2 : Ω → ℝ := fun ω => Real.exp (theta * D ω) with hX2
    have hX1nat : Measurable[naturalSigma R s] X1 :=
      (Real.measurable_exp.comp (measurable_const.mul (hRnat s))).indicator hA
    have hX2D : Measurable[MeasurableSpace.comap D inferInstance] X2 :=
      Real.measurable_exp.comp (measurable_const.mul (comap_measurable D))
    have hIndep : IndepFun X1 X2 P :=
      (IndepFun_iff_Indep X1 X2 P).mpr
        (indep_of_indep_of_le_left (indep_of_indep_of_le_right hInd.symm hX2D.comap_le)
          hX1nat.comap_le)
    have hprod : A.indicator (fun ω => Real.exp (theta * R t ω)) = X1 * X2 := by
      funext ω
      by_cases hω : ω ∈ A
      · simp only [hX1, hX2, hD, Pi.mul_apply, indicator_of_mem hω, ← Real.exp_add]
        ring_nf
      · simp [hX1, indicator_of_notMem hω]
    rw [← integral_indicator hA', ← integral_indicator hA', hprod,
      hIndep.integral_mul_eq_mul_integral
        ((hX1nat.mono (hnat_le s) le_rfl).aestronglyMeasurable)
        ((Real.measurable_exp.comp (measurable_const.mul hDmeas)).aestronglyMeasurable),
      hX2, hDmom, mul_one]
  have hMeq : ∀ t, M t = fun ω => Real.exp (theta * R t ω) := by
    intro t
    funext ω
    simp only [M, X, hR, hRoot, zero_mul, sub_zero]
  refine ⟨fun s t hst => ⟨?_, fun A hA => ?_⟩, ?_⟩
  · rw [hMeq]; exact hEint t
  · rw [hMeq, hMeq]; exact hmart s t hst A hA
  · exact Kyprianou.Ch01.queueUpperPassageProbability P arrival claims rate hrate F hDriver hPos
      hIntegrable mu hMean hOverload theta hTheta hRoot
