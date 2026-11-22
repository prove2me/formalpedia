-- Prove2me | solution 1 for Kyprianou.Ch01.riskSurplus_increment_stationary
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T10:28:43.505691+00:00
-- url     : https://prove2.me/submissions/b92b36e1-8e01-464a-8584-9c8637fc0bd2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_hasIndependentIncrements
import Theorems.Thm_levy_foundations_jumpCountLtIff
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_Kyprianou_Ch01_compoundDriver_toFoundations
import Theorems.Thm_levy_foundations_compoundPoissonCharFun
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Jump counts are measurable in any σ-algebra in which the interarrivals are. -/
theorem cpIncr_aux_jumpCount_measurable {Ω : Type*} (m : MeasurableSpace Ω)
    (τ : ℕ → Ω → ℝ) (hτ : ∀ n, Measurable[m] (τ n)) (u : ℝ) :
    Measurable[m] (fun ω => ProbabilityTheory.jumpCount
      (fun n => ProbabilityTheory.arrival τ n ω) u) := by
  classical
  have hT : ∀ n, Measurable[m] (fun ω => ProbabilityTheory.arrival τ n ω) := fun n =>
    Finset.measurable_sum _ (fun i _ => hτ i)
  refine @measurable_to_countable' ℕ Ω _ _ m _ (fun n => ?_)
  have hiff : ∀ ω, ProbabilityTheory.jumpCount (fun n => ProbabilityTheory.arrival τ n ω) u = n ↔
      ((u < ProbabilityTheory.arrival τ n ω ∧ ∀ k < n, ProbabilityTheory.arrival τ k ω ≤ u) ∨
        (n = 0 ∧ ∀ k, ProbabilityTheory.arrival τ k ω ≤ u)) := by
    intro ω
    set T := fun n => ProbabilityTheory.arrival τ n ω
    show sInf {k | u < T k} = n ↔ _
    by_cases hne : ({k | u < T k} : Set ℕ).Nonempty
    · have hmem := Nat.sInf_mem hne
      constructor
      · intro h
        left
        refine ⟨h ▸ hmem, fun k hk => ?_⟩
        by_contra hc
        have := Nat.sInf_le (show k ∈ {k | u < T k} from lt_of_not_ge hc)
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
      have hall : ∀ k, T k ≤ u := by
        intro k
        by_contra hc
        have : k ∈ ({k | u < T k} : Set ℕ) := lt_of_not_ge hc
        rw [hne] at this
        exact this
      constructor
      · intro h; right; exact ⟨h.symm, hall⟩
      · rintro (⟨h1, -⟩ | ⟨h0, -⟩)
        · exact absurd (hall n) (not_le.mpr h1)
        · exact h0.symm
  have : (fun ω => ProbabilityTheory.jumpCount
      (fun n => ProbabilityTheory.arrival τ n ω) u) ⁻¹' {n} =
      ({ω | u < ProbabilityTheory.arrival τ n ω} ∩
        ⋂ k ∈ Finset.range n, {ω | ProbabilityTheory.arrival τ k ω ≤ u}) ∪
      ({ω | n = 0} ∩ ⋂ k, {ω | ProbabilityTheory.arrival τ k ω ≤ u}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hiff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
    rfl
  rw [this]
  exact MeasurableSet.union (MeasurableSet.inter (measurableSet_lt measurable_const
    (hT n)) (Finset.measurableSet_biInter _ fun k _ =>
      measurableSet_le (hT k) measurable_const))
    (MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.iInter fun k =>
      measurableSet_le (hT k) measurable_const))

/-- Almost surely the arrival times are strictly increasing and divergent, and the jump
count is characterised by `n < N_t ↔ T_n ≤ t`. -/
theorem cpIncr_aux_threshold_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) (hd : IsCompoundPoissonDriver arrival claims rate F P) :
    ∀ᵐ ω ∂P, ∀ (u : ℝ) (k : ℕ),
      k < ProbabilityTheory.jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) u ↔
        ProbabilityTheory.arrival arrival k ω ≤ u := by
  have hd' := Kyprianou.Ch01.compoundDriver_toFoundations hd
  filter_upwards [levy_foundations_compoundDriverArrivalStrictMono hd' hrate,
    levy_foundations_compoundDriverArrivalDiverges hd' hrate] with ω hmono hdiv u k
  exact levy_foundations_jumpCountLtIff _ hmono hdiv k u

/-- Aggregate claims at a fixed time are a finite sum over the jump count. -/
theorem cpIncr_aux_aggregateClaims_eq {Ω : Type*} (arrival claims : ℕ → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    aggregateClaims arrival claims u ω =
      ∑ j ∈ Finset.range (ProbabilityTheory.jumpCount
        (fun k => ProbabilityTheory.arrival arrival k ω) (u : ℝ)), claims j ω := by
  simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath]

/-- Aggregate claims at a fixed time are measurable. -/
theorem cpIncr_aux_aggregateClaims_measurable {Ω : Type*} [MeasurableSpace Ω]
    (arrival claims : ℕ → Ω → ℝ) (hA : ∀ n, Measurable (arrival n))
    (hY : ∀ n, Measurable (claims n)) (u : ℝ≥0) :
    Measurable (aggregateClaims arrival claims u) := by
  have hN := cpIncr_aux_jumpCount_measurable _ arrival hA (u : ℝ)
  have hG : Measurable (fun p : Ω × ℕ => ∑ i ∈ Finset.range p.2, claims i p.1) :=
    measurable_from_prod_countable_left (fun n => by
      simpa using Finset.measurable_sum (Finset.range n) (fun i _ => hY i))
  have heq : aggregateClaims arrival claims u =
      (fun p : Ω × ℕ => ∑ i ∈ Finset.range p.2, claims i p.1) ∘
        (fun ω => (ω, ProbabilityTheory.jumpCount
          (fun k => ProbabilityTheory.arrival arrival k ω) (u : ℝ))) := by
    funext ω; exact cpIncr_aux_aggregateClaims_eq arrival claims u ω
  rw [heq]
  exact hG.comp (measurable_id.prodMk hN)

/-- The aggregate claims start at zero almost surely. -/
theorem cpIncr_aux_aggregateClaims_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) (hd : IsCompoundPoissonDriver arrival claims rate F P) :
    ∀ᵐ ω ∂P, aggregateClaims arrival claims 0 ω = 0 := by
  have hr : (0 : ℝ) < rate := by exact_mod_cast hrate
  have hpos : ∀ᵐ ω ∂P, 0 < arrival 0 ω := by
    have := isProbabilityMeasure_expMeasure hr
    rw [ae_iff]
    have h := (hd.law_interarrival 0).measure_eq (p := fun y : ℝ => y ≤ 0) measurableSet_Iic
    simp only [not_lt]
    rw [h, show {x : ℝ | x ≤ 0} = Iic 0 from rfl, ← ofReal_cdf, cdf_expMeasure_eq hr]
    simp
  filter_upwards [cpIncr_aux_threshold_ae P arrival claims rate hrate F hd, hpos] with ω hω hp
  rw [cpIncr_aux_aggregateClaims_eq]
  have : ProbabilityTheory.jumpCount (fun k => ProbabilityTheory.arrival arrival k ω)
      ((0 : ℝ≥0) : ℝ) = 0 := by
    by_contra hne
    have h0 := (hω _ 0).mp (Nat.pos_of_ne_zero hne)
    simp [ProbabilityTheory.arrival] at h0
    linarith
  rw [this]
  simp

/-- Characteristic function of the aggregate claims. -/
theorem cpStat_aux_charFun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) (hd : IsCompoundPoissonDriver arrival claims rate F P) (u : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (aggregateClaims arrival claims u)) ξ =
      Complex.exp ((u : ℝ) * ((rate : ℝ) * (charFun F ξ - 1))) := by
  have h := levy_foundations_compoundPoissonCharFun
    (Kyprianou.Ch01.compoundDriver_toFoundations hd) hrate 0 u ξ
  have heq : LevyFoundations.compoundPoisson 0 arrival claims (u : ℝ) =
      aggregateClaims arrival claims u := rfl
  rw [heq] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    P.map (fun ω => riskSurplus arrival claims premium 0 t ω -
        riskSurplus arrival claims premium 0 s ω) =
      P.map (riskSurplus arrival claims premium 0 (t - s)) := by
  set S : ℝ≥0 → Ω → ℝ := fun u => aggregateClaims arrival claims u with hSdef
  have hSm : ∀ u, Measurable (S u) := fun u =>
    cpIncr_aux_aggregateClaims_measurable arrival claims hDriver.measurable_interarrival
      hDriver.measurable_mark u
  -- independence of S_s - S_0 and S_t - S_s
  have hII := Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements P arrival claims rate
    hrate F hDriver
  set g : Fin 3 → ℝ≥0 := ![0, s, t] with hg
  have hgm : Monotone g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g, Fin.le_def]
  have hI := hII 2 g hgm
  have hindep : IndepFun (fun ω => S s ω - S 0 ω) (fun ω => S t ω - S s ω) P := by
    have := hI.indepFun (i := 0) (j := 1) (by decide)
    simp [g] at this
    exact this
  set A : Ω → ℝ := fun ω => S s ω - S 0 ω with hA
  set D : Ω → ℝ := fun ω => S t ω - S s ω with hD
  have hAm : Measurable A := (hSm s).sub (hSm 0)
  have hDm : Measurable D := (hSm t).sub (hSm s)
  have h0 := cpIncr_aux_aggregateClaims_zero_ae P arrival claims rate hrate F hDriver
  have hAeq : P.map A = P.map (S s) := by
    refine Measure.map_congr ?_
    filter_upwards [h0] with ω hω
    simp [hA, S, hω]
  have hADeq : P.map (A + D) = P.map (S t) := by
    refine Measure.map_congr ?_
    filter_upwards [h0] with ω hω
    simp [hA, hD, S, hω]
  have hlawD : P.map D = P.map (S (t - s)) := by
    have : IsProbabilityMeasure (P.map D) := Measure.isProbabilityMeasure_map hDm.aemeasurable
    have : IsProbabilityMeasure (P.map (S (t - s))) :=
      Measure.isProbabilityMeasure_map (hSm _).aemeasurable
    apply Measure.ext_of_charFun
    funext ξ
    have hmul := congrFun (hindep.charFun_map_add_eq_mul hAm.aemeasurable hDm.aemeasurable) ξ
    rw [hADeq, hAeq, Pi.mul_apply] at hmul
    have hφ := fun u => cpStat_aux_charFun P arrival claims rate hrate F hDriver u ξ
    simp only [S] at hmul
    rw [hφ t, hφ s] at hmul
    rw [show (S (t - s)) = aggregateClaims arrival claims (t - s) from rfl, hφ (t - s)]
    have hne : Complex.exp ((s : ℝ) * ((rate : ℝ) * (charFun F ξ - 1))) ≠ 0 := Complex.exp_ne_zero _
    have hsplit : Complex.exp ((t : ℝ) * ((rate : ℝ) * (charFun F ξ - 1))) =
        Complex.exp ((s : ℝ) * ((rate : ℝ) * (charFun F ξ - 1))) *
          Complex.exp (((t - s : ℝ≥0) : ℝ) * ((rate : ℝ) * (charFun F ξ - 1))) := by
      rw [← Complex.exp_add, NNReal.coe_sub hst]
      congr 1
      push_cast
      ring
    rw [hsplit] at hmul
    exact (mul_left_cancel₀ hne hmul).symm
  -- transfer to the surplus
  have hR : ∀ u ω, riskSurplus arrival claims premium 0 u ω = premium * (u : ℝ) - S u ω := by
    intro u ω; simp [riskSurplus, S]
  have hfun1 : (fun ω => riskSurplus arrival claims premium 0 t ω -
      riskSurplus arrival claims premium 0 s ω) =
      (fun y => premium * ((t - s : ℝ≥0) : ℝ) - y) ∘ D := by
    funext ω
    simp only [hR, Function.comp, hD, NNReal.coe_sub hst]
    ring
  have hfun2 : riskSurplus arrival claims premium 0 (t - s) =
      (fun y => premium * ((t - s : ℝ≥0) : ℝ) - y) ∘ S (t - s) := by
    funext ω; simp only [hR, Function.comp]
  have hgm' : Measurable (fun y : ℝ => premium * ((t - s : ℝ≥0) : ℝ) - y) :=
    measurable_const.sub measurable_id
  rw [hfun1, hfun2, ← Measure.map_map hgm' hDm, ← Measure.map_map hgm' (hSm _), hlawD]
