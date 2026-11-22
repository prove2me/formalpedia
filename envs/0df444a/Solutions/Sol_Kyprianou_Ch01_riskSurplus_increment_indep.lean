-- Prove2me | solution 1 for Kyprianou.Ch01.riskSurplus_increment_indep
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T10:31:05.794013+00:00
-- url     : https://prove2.me/submissions/0734b692-58c2-4f9a-99c2-7e9bfc4f8f46

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_hasIndependentIncrements
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_increments_add_linear_drift
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indep_naturalFiltration
import Theorems.Thm_levy_foundations_jumpCountLtIff
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_Kyprianou_Ch01_compoundDriver_toFoundations
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

/-- Independence from a σ-algebra survives adjoining the σ-algebra of an almost surely
zero random variable. -/
theorem cpInd_aux_indep_sup_trivial {Ω : Type*} (M : Bool → MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h1 : M true ≤ mΩ) (h2 : M false ≤ mΩ) (Z : Ω → ℝ) (hZ : Measurable Z)
    (hZ0 : ∀ᵐ ω ∂P, Z ω = 0) (hind : Indep (M true) (M false) P) :
    Indep (M true) (M false ⊔ MeasurableSpace.comap Z inferInstance) P := by
  have h3 : MeasurableSpace.comap Z inferInstance ≤ mΩ := hZ.comap_le
  let p2 : Set (Set Ω) := Set.image2 (· ∩ ·) {E | MeasurableSet[M false] E}
    {C | MeasurableSet[MeasurableSpace.comap Z inferInstance] C}
  have hp2pi : IsPiSystem p2 := by
    rintro _ ⟨E1, hE1, C1, hC1, rfl⟩ _ ⟨E2, hE2, C2, hC2, rfl⟩ _
    refine ⟨E1 ∩ E2, MeasurableSet.inter (m := M false) hE1 hE2, C1 ∩ C2,
      MeasurableSet.inter (m := MeasurableSpace.comap Z inferInstance) hC1 hC2, ?_⟩
    simp only
    rw [Set.inter_inter_inter_comm]
  have hgen : M false ⊔ MeasurableSpace.comap Z inferInstance =
      MeasurableSpace.generateFrom p2 := by
    apply le_antisymm
    · refine sup_le (fun E hE => ?_) (fun C hC => ?_)
      · exact MeasurableSpace.measurableSet_generateFrom ⟨E, hE, Set.univ,
          MeasurableSet.univ (m := MeasurableSpace.comap Z inferInstance), Set.inter_univ E⟩
      · exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ,
          MeasurableSet.univ (m := M false), C, hC, Set.univ_inter C⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨E, hE, C, hC, rfl⟩
      exact MeasurableSet.inter
        (le_sup_left (a := M false) (b := MeasurableSpace.comap Z inferInstance) E hE)
        (le_sup_right (a := M false) (b := MeasurableSpace.comap Z inferInstance) C hC)
  refine IndepSets.indep h1 (sup_le h2 h3) (@MeasurableSpace.isPiSystem_measurableSet Ω (M true)) hp2pi
    (@MeasurableSpace.generateFrom_measurableSet Ω (M true)).symm hgen ?_
  rw [IndepSets_iff]
  rintro A _ hA ⟨E, hE, C, hC, rfl⟩
  obtain ⟨B, hB, rfl⟩ := hC
  have hindAE := (Indep_iff (M true) (M false) P).mp hind A E hA hE
  have hnz : P {ω | Z ω ≠ 0} = 0 := ae_iff.mp hZ0
  by_cases h0 : (0 : ℝ) ∈ B
  · have hconull : P (Z ⁻¹' B)ᶜ = 0 := by
      apply measure_mono_null _ hnz
      intro ω hω h
      exact hω (show Z ω ∈ B from h ▸ h0)
    rw [← Set.inter_assoc, measure_inter_conull hconull, measure_inter_conull hconull, hindAE]
  · have hnull : P (Z ⁻¹' B) = 0 := by
      apply measure_mono_null _ hnz
      intro ω hω h
      exact h0 (h ▸ hω)
    rw [measure_mono_null Set.inter_subset_right (measure_mono_null Set.inter_subset_right hnull),
      measure_mono_null Set.inter_subset_right hnull, mul_zero]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P)
    (premium : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
        (MeasurableSpace.comap
          (fun ω => riskSurplus arrival claims premium 0 t ω -
            riskSurplus arrival claims premium 0 s ω) inferInstance)
        (naturalSigma (riskSurplus arrival claims premium 0) s) P := by
  set S : ℝ≥0 → Ω → ℝ := fun u => aggregateClaims arrival claims u with hSdef
  set R : ℝ≥0 → Ω → ℝ := riskSurplus arrival claims premium 0 with hRdef
  have hSm : ∀ u, Measurable (S u) := fun u =>
    cpIncr_aux_aggregateClaims_measurable arrival claims hDriver.measurable_interarrival
      hDriver.measurable_mark u
  have hR : ∀ u ω, R u ω = premium * (u : ℝ) - S u ω := by
    intro u ω; simp [hRdef, riskSurplus, S]
  have hRm : ∀ u, Measurable (R u) := by
    intro u
    have : R u = fun ω => premium * (u : ℝ) - S u ω := funext (hR u)
    rw [this]; exact measurable_const.sub (hSm u)
  -- independent increments of the surplus
  have hII := Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements P arrival claims rate
    hrate F hDriver
  have hIIneg : HasIndependentIncrements (fun u ω => -S u ω) P := by
    intro n g hg
    have h := (hII n g hg).comp (fun _ x => -x) (fun _ => measurable_neg)
    refine (iIndepFun_congr (fun i => ae_of_all _ (fun ω => ?_))).mp h
    simp [ProbabilityTheory.increment, S]
    ring
  have hIIR : HasIndependentIncrements R P := by
    have h := AvramDividend.Classical.avram_a06_independent_increments_add_linear_drift P
      (fun u ω => -S u ω) premium hIIneg
    have heq : (fun u ω => -S u ω + premium * (u : ℝ)) = R := by
      funext u ω; rw [hR]; ring
    rwa [heq] at h
  -- the process restarted at zero
  set X' : ℝ≥0 → Ω → ℝ := fun u ω => R u ω - R 0 ω with hX'
  have hincr : ∀ a b, ProbabilityTheory.increment X' a b = ProbabilityTheory.increment R a b := by
    intro a b; funext ω; simp [ProbabilityTheory.increment, hX']
  have hIIX' : HasIndependentIncrements X' P := by
    intro n g hg
    simp only [hincr]
    exact hIIR n g hg
  have hX'sm : ∀ i, StronglyMeasurable (X' i) := fun i => ((hRm i).sub (hRm 0)).stronglyMeasurable
  have hX'0 : X' 0 = fun _ => 0 := by funext ω; simp [hX']
  have hnat := ProbabilityTheory.HasIndependentIncrements.indep_naturalFiltration hIIX' hX'sm hX'0
    (fun i => (zero_le : (0 : ℝ≥0) ≤ i)) hst
  rw [hincr] at hnat
  -- adjoin σ(X_0), which is a.s. trivial
  have h0 := cpIncr_aux_aggregateClaims_zero_ae P arrival claims rate hrate F hDriver
  have hR0 : ∀ᵐ ω ∂P, R 0 ω = 0 := by
    filter_upwards [h0] with ω hω
    rw [hR]; simp [S, hω]
  let Gs : ℝ≥0 → MeasurableSpace Ω := fun u =>
    (MeasureTheory.Filtration.natural (fun i => X' i) hX'sm).seq u
  have hG'le : Gs s ≤ ‹MeasurableSpace Ω› :=
    (MeasureTheory.Filtration.natural (fun i => X' i) hX'sm).le s
  have hDle : MeasurableSpace.comap (ProbabilityTheory.increment R s t) inferInstance ≤
      ‹MeasurableSpace Ω› := ((hRm t).sub (hRm s)).comap_le
  let Mb : Bool → MeasurableSpace Ω := fun b => if b then
    MeasurableSpace.comap (ProbabilityTheory.increment R s t) inferInstance else Gs s
  have hsup := cpInd_aux_indep_sup_trivial Mb P hDle hG'le (R 0) (hRm 0) hR0 hnat
  have hle : naturalSigma R s ≤ Gs s ⊔ MeasurableSpace.comap (R 0) inferInstance := by
    refine iSup₂_le (fun u hu => ?_)
    have hX'u : Measurable[Gs s] (X' u) := by
      have : MeasurableSpace.comap (X' u) inferInstance ≤ Gs s :=
        le_iSup₂ (f := fun j (_ : j ≤ s) => MeasurableSpace.comap (X' j) inferInstance) u hu
      exact Measurable.of_comap_le this
    have hR0m : Measurable[MeasurableSpace.comap (R 0) inferInstance] (R 0) := comap_measurable _
    have hsum : Measurable[Gs s ⊔ MeasurableSpace.comap (R 0) inferInstance]
        (fun ω => X' u ω + R 0 ω) :=
      (hX'u.mono le_sup_left le_rfl).add (hR0m.mono le_sup_right le_rfl)
    have heq : (fun ω => X' u ω + R 0 ω) = R u := by funext ω; simp [hX']
    rw [heq] at hsum
    exact hsum.comap_le
  exact indep_of_indep_of_le_right hsup hle
