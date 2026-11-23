-- Prove2me | solution 1 for Kyprianou.markedCompoundPoissonRandomMeasureCh02V6
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T11:46:43.8688+00:00
-- url     : https://prove2.me/submissions/6a873c23-4360-45a2-9ac8-4080423054ff

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ch02MarkedPoissonCountEqualsN
import Theorems.Thm_Kyprianou_Ch02_poissonMeasureIicTendstoZeroV1
import Theorems.Thm_Kyprianou_Ch02_markedCompoundPoissonBoundedDisjointLawV6

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

private lemma measurable_marked_mu_eval
    {Ω : Type} [MeasurableSpace Ω]
    (T : ℕ → Ω → ℝ≥0) (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable (fun ω =>
      (Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))) A) := by
  have heq :
      (fun ω =>
        (Measure.sum (fun n : ℕ =>
          Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))) A) =
      (fun ω => ∑' n : ℕ,
        A.indicator (fun _ => (1 : ENNReal)) ((T (n + 1) ω : ℝ), ξ (n + 1) ω)) := by
    funext ω
    rw [Measure.sum_apply _ hA]
    refine tsum_congr fun n => ?_
    rw [Measure.dirac_apply' _ hA]
    rfl
  rw [heq]
  refine Measurable.tsum fun n => ?_
  have hpair : Measurable (fun ω => ((T (n + 1) ω : ℝ), ξ (n + 1) ω)) :=
    (NNReal.continuous_coe.measurable.comp (hTmeas (n + 1) (Nat.succ_pos n))).prodMk
      (hξmeas (n + 1))
  exact (measurable_const.indicator hA).comp hpair

private lemma dirac_sum_nat_or_top'
    {α : Type*} [MeasurableSpace α]
    (p : ℕ → α) {A : Set α} (hA : MeasurableSet A) :
    (∃ n : ℕ, (Measure.sum (fun k : ℕ => Measure.dirac (p k))) A = (n : ENNReal)) ∨
    (Measure.sum (fun k : ℕ => Measure.dirac (p k))) A = ⊤ := by
  classical
  rw [Measure.sum_apply _ hA]
  have hterm : ∀ k : ℕ, Measure.dirac (p k) A = if p k ∈ A then (1 : ENNReal) else 0 := by
    intro k
    rw [Measure.dirac_apply' _ hA]
    by_cases hk : p k ∈ A
    · simp [hk]
    · simp [hk]
  simp_rw [hterm]
  by_cases hfin : Set.Finite {k : ℕ | p k ∈ A}
  · left
    refine ⟨hfin.toFinset.card, ?_⟩
    rw [tsum_eq_sum (s := hfin.toFinset)]
    · calc
        ∑ k ∈ hfin.toFinset, (if p k ∈ A then (1 : ENNReal) else 0)
            = ∑ _k ∈ hfin.toFinset, (1 : ENNReal) := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hmem : p k ∈ A := hfin.mem_toFinset.mp hk
              simp [hmem]
        _ = (hfin.toFinset.card : ENNReal) := by simp
    · intro k hk
      have hnot : p k ∉ A := fun hmem => hk (hfin.mem_toFinset.mpr hmem)
      simp [hnot]
  · right
    have hinf : Set.Infinite {k : ℕ | p k ∈ A} := hfin
    rw [ENNReal.tsum_eq_iSup_sum, iSup_eq_top]
    intro b hb
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
    obtain ⟨s, hs_sub, hs_card⟩ := hinf.exists_subset_card_eq n
    refine ⟨s, ?_⟩
    have hsum : ∑ k ∈ s, (if p k ∈ A then (1 : ENNReal) else 0) = (n : ENNReal) := by
      calc
        ∑ k ∈ s, (if p k ∈ A then (1 : ENNReal) else 0)
            = ∑ _k ∈ s, (1 : ENNReal) := by
              refine Finset.sum_congr rfl fun k hk => ?_
              have hmem : p k ∈ A := hs_sub hk
              simp [hmem]
        _ = (s.card : ENNReal) := by simp
        _ = (n : ENNReal) := by rw [hs_card]
    rw [hsum]
    exact hn

private lemma continuous_poissonMeasure_Iic (n : ℕ) :
    Continuous (fun r : ℝ≥0 => ProbabilityTheory.poissonMeasure r (Set.Iic n)) := by
  have heq :
      (fun r : ℝ≥0 => ProbabilityTheory.poissonMeasure r (Set.Iic n)) =
      (fun r : ℝ≥0 => ∑ j ∈ Finset.range (n + 1),
        ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ j / (Nat.factorial j : ℝ))) := by
    funext r
    have hset : (Set.Iic n : Set ℕ) = ⋃ j ∈ Finset.range (n + 1), ({j} : Set ℕ) := by
      ext k
      simp
    rw [hset, measure_biUnion_finset]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [ProbabilityTheory.poissonMeasure_singleton]
    · intro i _ j _ hij
      exact Set.disjoint_singleton.mpr hij
    · intro j _
      exact measurableSet_singleton j
  rw [heq]
  refine continuous_finsetSum _ fun j _ => ?_
  refine ENNReal.continuous_ofReal.comp ?_
  have hr : Continuous (fun r : ℝ≥0 => (r : ℝ)) := NNReal.continuous_coe
  fun_prop

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hFzero : F {0} = 0)
    (N : ℝ≥0 → Ω → ℕ)
    (T : ℕ → Ω → ℝ≥0)
    (ξ : ℕ → Ω → ℝ)
    (hTmeas : ∀ n : ℕ, 0 < n → Measurable (T n))
    (hξmeas : ∀ k : ℕ, Measurable (ξ k))
    (hNlevy : ProbabilityTheory.IsLevyProcess
       (fun t ω => (N t ω : ℝ)) P)
    (hNlaw : ∀ t : ℝ≥0,
       P.map (N t) = ProbabilityTheory.poissonMeasure (rate * t))
    (harrival : ∀ᵐ ω ∂P,
       ∀ (n : ℕ), 0 < n →
         ∀ (t : ℝ≥0), (n ≤ N t ω ↔ T n ω ≤ t))
    (hmarklaw : ∀ k : ℕ, P.map (ξ k) = F)
    (hIID : ProbabilityTheory.iIndepFun ξ P)
    (hcross : ProbabilityTheory.Indep
      (⨆ k : ℕ, MeasurableSpace.comap (ξ k) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (N t) inferInstance) P) :
    let μ : Ω → Measure (ℝ × ℝ) := fun ω =>
      Measure.sum (fun n : ℕ =>
        Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω))
    let intensity : Measure (ℝ × ℝ) :=
      (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F)
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A < ⊤ →
       P.map (fun ω => μ ω A) =
         (ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
           (Nat.cast : ℕ → ENNReal)) ∧
    (∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
       intensity A = ⊤ →
       ∀ᵐ ω ∂P, μ ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set (ℝ × ℝ)),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => μ ω (A i)) P) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
       μ ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ) = (N t ω : ENNReal)) := by
  dsimp only
  set μ : Ω → Measure (ℝ × ℝ) := fun ω =>
    Measure.sum (fun n : ℕ =>
      Measure.dirac ((T (n + 1) ω : ℝ), ξ (n + 1) ω)) with hμ_def
  set intensity : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ici (0 : ℝ))).prod ((rate : ENNReal) • F) with hint_def
  have hNzero : ∀ ω : Ω, N 0 ω = 0 := by
    intro ω
    have hz : (N 0 ω : ℝ) = 0 := congrFun hNlevy.start_zero ω
    exact_mod_cast hz
  have hTpos_ae : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < T (n + 1) ω := by
    filter_upwards [harrival] with ω hω n
    refine lt_of_not_ge fun hle => ?_
    have hn := (hω (n + 1) (Nat.succ_pos n) 0).2 hle
    simp [hNzero] at hn
  have hslice_meas : ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → ∀ k : ℕ,
      MeasurableSet (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
    fun _ hA _ => hA.inter (measurableSet_Ioc.prod MeasurableSet.univ)
  have hslice_union : ∀ (A : Set (ℝ × ℝ)),
      (⋃ k : ℕ, A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) =
      A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    intro A
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc,
      Set.mem_Ioi, Set.mem_univ, and_true]
    constructor
    · rintro ⟨k, hAxy, hxpos, _⟩
      exact ⟨hAxy, hxpos⟩
    · rintro ⟨hAxy, hxpos⟩
      exact ⟨⌈x⌉₊, hAxy, hxpos, Nat.le_ceil x⟩
  have hslice_mono : ∀ (A : Set (ℝ × ℝ)),
      Monotone (fun k : ℕ => A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) := by
    intro A k₁ k₂ hk
    refine Set.inter_subset_inter_right A (Set.prod_mono_left ?_)
    intro x hx
    exact ⟨hx.1, hx.2.trans (Nat.cast_le.mpr hk)⟩
  have hint_Ioi : ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      intensity (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) = intensity A := by
    intro A hA
    have hIoi_eq : volume.restrict (Set.Ici (0 : ℝ)) = volume.restrict (Set.Ioi (0 : ℝ)) :=
      Measure.restrict_congr_set Ioi_ae_eq_Ici.symm
    have hcompl_zero :
        intensity ((Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))ᶜ) = 0 := by
      have hcompl_eq :
          ((Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))ᶜ : Set (ℝ × ℝ)) =
          (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) := by
        ext ⟨x, y⟩
        simp
      rw [hcompl_eq, hint_def, hIoi_eq, Measure.prod_prod]
      have hz : (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
        rw [Measure.restrict_apply measurableSet_Ioi.compl, Set.compl_inter_self, measure_empty]
      rw [hz, zero_mul]
    have hdiff_zero : intensity (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) = 0 :=
      measure_mono_null (fun _ hx => hx.2) hcompl_zero
    have hunion :
        (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) ∪
          (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) = A :=
      Set.inter_union_sdiff A _
    have hdisj :
        Disjoint (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
          (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
      Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2
    have hmeas_diff : MeasurableSet (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
      hA.diff (measurableSet_Ioi.prod MeasurableSet.univ)
    calc
      intensity (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
          = intensity (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) +
              intensity (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) := by
                rw [hdiff_zero, add_zero]
      _ = intensity ((A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) ∪
              (A \ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))) :=
            (measure_union hdisj hmeas_diff).symm
      _ = intensity A := by rw [hunion]
  have hint_slice_tendsto : ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      Tendsto (fun k : ℕ => intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))))
        atTop (𝓝 (intensity A)) := by
    intro A hA
    have ht := tendsto_measure_iUnion_atTop (μ := intensity) (hslice_mono A)
    rw [hslice_union A, hint_Ioi A hA] at ht
    exact ht
  have hμ_iSup_ae : ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      ∀ᵐ ω ∂P,
        (⨆ k : ℕ, μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) = μ ω A := by
    intro A hA
    filter_upwards [hTpos_ae] with ω hω
    have ht1 := tendsto_measure_iUnion_atTop (μ := μ ω) (hslice_mono A)
    have ht2 := tendsto_atTop_iSup (f := fun k : ℕ =>
      μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))))
      (fun k₁ k₂ hk => measure_mono (hslice_mono A hk))
    have hlim :
        (⨆ k : ℕ, μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) =
          μ ω (⋃ k : ℕ, A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
      tendsto_nhds_unique ht2 ht1
    rw [hlim, hslice_union A]
    have hAIoi : MeasurableSet (A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))) :=
      hA.inter (measurableSet_Ioi.prod MeasurableSet.univ)
    rw [hμ_def, Measure.sum_apply _ hAIoi, Measure.sum_apply _ hA]
    refine tsum_congr fun n => ?_
    rw [Measure.dirac_apply' _ hAIoi, Measure.dirac_apply' _ hA]
    have hposR : (0 : ℝ) < (T (n + 1) ω : ℝ) := by exact_mod_cast hω n
    by_cases hmem : ((T (n + 1) ω : ℝ), ξ (n + 1) ω) ∈ A
    · have hmem' : ((T (n + 1) ω : ℝ), ξ (n + 1) ω) ∈
          A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
        ⟨hmem, hposR, trivial⟩
      simp [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
    · have hmem' : ((T (n + 1) ω : ℝ), ξ (n + 1) ω) ∉
          A ∩ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
        fun h => hmem h.1
      simp [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  have hμ_Iic_tendsto : ∀ (A : Set (ℝ × ℝ)), MeasurableSet A → ∀ x : ENNReal,
      Tendsto
        (fun k : ℕ => P {ω | μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x})
        atTop (𝓝 (P {ω | μ ω A ≤ x})) := by
    intro A hA x
    let E : ℕ → Set Ω := fun k =>
      {ω | μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x}
    have hE_anti : Antitone E := by
      intro k₁ k₂ hk ω hω
      exact le_trans (measure_mono (hslice_mono A hk)) hω
    have hE_meas : ∀ k, NullMeasurableSet (E k) P := by
      intro k
      have hm : Measurable
          (fun ω => μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) :=
        measurable_marked_mu_eval T ξ hTmeas hξmeas (hslice_meas A hA k)
      exact (hm measurableSet_Iic).nullMeasurableSet
    have hE_fin : ∃ k, P (E k) ≠ ⊤ := ⟨0, measure_ne_top P _⟩
    have ht := tendsto_measure_iInter_atTop hE_meas hE_anti hE_fin
    have hae_eq : (⋂ k : ℕ, E k) =ᵐ[P] {ω | μ ω A ≤ x} := by
      rw [MeasureTheory.ae_eq_set]
      constructor
      · have hsub : (⋂ k : ℕ, E k) \ {ω | μ ω A ≤ x} ⊆
            {ω | (⨆ k : ℕ, μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) ≠ μ ω A} := by
          intro ω ⟨h1, h2⟩ heq
          apply h2
          change μ ω A ≤ x
          rw [← heq, iSup_le_iff]
          intro k
          exact Set.mem_iInter.mp h1 k
        exact measure_mono_null hsub (ae_iff.mp (hμ_iSup_ae A hA))
      · have hsub : {ω | μ ω A ≤ x} \ (⋂ k : ℕ, E k) = ∅ := by
          ext ω
          simp only [Set.mem_sdiff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and,
            not_forall]
          intro hle hnot
          rcases hnot with ⟨k, hk⟩
          exact hk (le_trans (measure_mono Set.inter_subset_left) hle)
        rw [hsub, measure_empty]
    rw [measure_congr hae_eq] at ht
    exact ht
  have hclause_a :
      ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
        intensity A < ⊤ →
        P.map (fun ω => μ ω A) =
          (ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
            (Nat.cast : ℕ → ENNReal) := by
    intro A hA hAfin
    have hμA_meas : Measurable (fun ω => μ ω A) :=
      measurable_marked_mu_eval T ξ hTmeas hξmeas hA
    have hrate_tendsto :
        Tendsto
          (fun k : ℕ => (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal)
          atTop (𝓝 (intensity A).toNNReal) :=
      (ENNReal.tendsto_toNNReal (ne_top_of_lt hAfin)).comp (hint_slice_tendsto A hA)
    have hIic_eq : ∀ n : ℕ,
        P {ω | μ ω A ≤ (n : ENNReal)} =
          ProbabilityTheory.poissonMeasure (intensity A).toNNReal (Set.Iic n) := by
      intro n
      have ht1 := hμ_Iic_tendsto A hA (n : ENNReal)
      have ht2 :
          Tendsto
            (fun k : ℕ =>
              ProbabilityTheory.poissonMeasure
                (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal
                (Set.Iic n))
            atTop
            (𝓝 (ProbabilityTheory.poissonMeasure (intensity A).toNNReal (Set.Iic n))) :=
        ((continuous_poissonMeasure_Iic n).tendsto _).comp hrate_tendsto
      have heq_k : ∀ k : ℕ,
          P {ω | μ ω (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ (n : ENNReal)} =
            ProbabilityTheory.poissonMeasure
              (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal
              (Set.Iic n) := by
        intro k
        let Ak : Set (ℝ × ℝ) := A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))
        have hAk_meas : MeasurableSet Ak := hslice_meas A hA k
        have hAk_law :=
          (Kyprianou.Ch02.markedCompoundPoissonBoundedDisjointLawV6
            P rate hrate F hFzero N T ξ hTmeas hξmeas hNlevy hNlaw harrival hmarklaw hIID hcross
            (k : ℝ≥0) 1 (fun _ => Ak) (fun _ => hAk_meas)
            (fun _ => Set.inter_subset_right)
            (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 0
        have hμAk_meas : Measurable (fun ω => μ ω Ak) :=
          measurable_marked_mu_eval T ξ hTmeas hξmeas hAk_meas
        have hpre :
            ((fun ω => μ ω Ak) ⁻¹' Set.Iic (n : ENNReal)) =
              {ω | μ ω Ak ≤ (n : ENNReal)} := rfl
        have hpre_nat :
            ((Nat.cast : ℕ → ENNReal) ⁻¹' Set.Iic (n : ENNReal)) = Set.Iic n := by
          ext j
          simp
        calc
          P {ω | μ ω Ak ≤ (n : ENNReal)}
              = (P.map (fun ω => μ ω Ak)) (Set.Iic (n : ENNReal)) := by
                  rw [Measure.map_apply hμAk_meas measurableSet_Iic, hpre]
          _ = ((ProbabilityTheory.poissonMeasure (intensity Ak).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) (Set.Iic (n : ENNReal)) := by
                  rw [hAk_law]
          _ = ProbabilityTheory.poissonMeasure (intensity Ak).toNNReal (Set.Iic n) := by
                  rw [Measure.map_apply measurable_from_top measurableSet_Iic, hpre_nat]
      simp_rw [heq_k] at ht1
      exact tendsto_nhds_unique ht1 ht2
    have hsingleton_eq : ∀ n : ℕ,
        (P.map (fun ω => μ ω A)) {(n : ENNReal)} =
          ((ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
            (Nat.cast : ℕ → ENNReal)) {(n : ENNReal)} := by
      intro n
      have hcast_sing :
          ((ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map
            (Nat.cast : ℕ → ENNReal)) {(n : ENNReal)} =
            ProbabilityTheory.poissonMeasure (intensity A).toNNReal {n} := by
        rw [Measure.map_apply measurable_from_top (measurableSet_singleton _)]
        congr 1
        ext j
        simp
      rw [hcast_sing, Measure.map_apply hμA_meas (measurableSet_singleton _)]
      cases n with
      | zero =>
        simp only [Nat.cast_zero]
        have h1 : ((fun ω => μ ω A) ⁻¹' {(0 : ENNReal)}) = {ω | μ ω A ≤ (0 : ENNReal)} := by
          ext ω; simp
        have h2 : ({0} : Set ℕ) = Set.Iic 0 := by ext j; simp
        rw [h1, h2]
        simpa using hIic_eq 0
      | succ n =>
        have hsplit_P :
            {ω | μ ω A ≤ ((n + 1 : ℕ) : ENNReal)} =
              {ω | μ ω A ≤ (n : ENNReal)} ∪ ((fun ω => μ ω A) ⁻¹' {((n + 1 : ℕ) : ENNReal)}) := by
          ext ω
          simp only [Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff]
          constructor
          · intro hle
            rcases dirac_sum_nat_or_top' (fun k => ((T (k + 1) ω : ℝ), ξ (k + 1) ω)) hA with
              ⟨m, hm⟩ | htop
            · change μ ω A = (m : ENNReal) at hm
              change μ ω A ≤ ((n + 1 : ℕ) : ENNReal) at hle
              rw [hm] at hle
              have hmle : m ≤ n + 1 := Nat.cast_le.mp hle
              rcases Nat.lt_or_eq_of_le hmle with hlt | rfl
              · left
                change μ ω A ≤ (n : ENNReal)
                rw [hm]
                exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp hlt)
              · right
                exact hm
            · change μ ω A = ⊤ at htop
              change μ ω A ≤ ((n + 1 : ℕ) : ENNReal) at hle
              rw [htop] at hle
              exact absurd (top_le_iff.mp hle) (ENNReal.natCast_ne_top (n + 1))
          · rintro (hle | heq)
            · change μ ω A ≤ (n : ENNReal) at hle
              exact le_trans hle (Nat.cast_le.mpr (Nat.le_succ n))
            · exact le_of_eq heq
        have hdisj_P :
            Disjoint {ω | μ ω A ≤ (n : ENNReal)}
              ((fun ω => μ ω A) ⁻¹' {((n + 1 : ℕ) : ENNReal)}) := by
          refine Set.disjoint_left.mpr fun ω h1 h2 => ?_
          change μ ω A ≤ (n : ENNReal) at h1
          change μ ω A = ((n + 1 : ℕ) : ENNReal) at h2
          rw [h2] at h1
          have : n + 1 ≤ n := Nat.cast_le.mp h1
          omega
        have hadd_P :
            P {ω | μ ω A ≤ ((n + 1 : ℕ) : ENNReal)} =
              P {ω | μ ω A ≤ (n : ENNReal)} +
                P ((fun ω => μ ω A) ⁻¹' {((n + 1 : ℕ) : ENNReal)}) := by
          rw [hsplit_P, measure_union hdisj_P (hμA_meas (measurableSet_singleton _))]
        have hsplit_N : (Set.Iic (n + 1) : Set ℕ) = Set.Iic n ∪ {n + 1} := by
          ext j; simp; omega
        have hdisj_N : Disjoint (Set.Iic n : Set ℕ) {n + 1} := by
          refine Set.disjoint_left.mpr fun j h1 h2 => ?_
          simp only [Set.mem_Iic, Set.mem_singleton_iff] at h1 h2
          omega
        have hadd_N :
            ProbabilityTheory.poissonMeasure (intensity A).toNNReal (Set.Iic (n + 1)) =
              ProbabilityTheory.poissonMeasure (intensity A).toNNReal (Set.Iic n) +
                ProbabilityTheory.poissonMeasure (intensity A).toNNReal {n + 1} := by
          rw [hsplit_N, measure_union hdisj_N (measurableSet_singleton _)]
        have hlin :
            P {ω | μ ω A ≤ (n : ENNReal)} +
              P ((fun ω => μ ω A) ⁻¹' {((n + 1 : ℕ) : ENNReal)}) =
            P {ω | μ ω A ≤ (n : ENNReal)} +
              ProbabilityTheory.poissonMeasure (intensity A).toNNReal {n + 1} := by
          rw [← hadd_P, hIic_eq (n + 1), hadd_N, ← hIic_eq n]
        exact (ENNReal.add_right_inj (measure_ne_top P _)).mp hlin
    let ν₁ : Measure ENNReal := P.map (fun ω => μ ω A)
    let ν₂ : Measure ENNReal :=
      (ProbabilityTheory.poissonMeasure (intensity A).toNNReal).map (Nat.cast : ℕ → ENNReal)
    have hrange_eq : (Set.range (Nat.cast : ℕ → ENNReal)) = ⋃ n : ℕ, {(n : ENNReal)} :=
      (Set.iUnion_singleton_eq_range (Nat.cast : ℕ → ENNReal)).symm
    have hdisj_sing : Pairwise (fun i j : ℕ => Disjoint ({(i : ENNReal)} : Set ENNReal) {(j : ENNReal)}) := by
      intro i j hij
      exact Set.disjoint_singleton.mpr (fun h => hij (Nat.cast_injective h))
    have hν₁_range : ν₁ (Set.range (Nat.cast : ℕ → ENNReal)) = 1 := by
      rw [hrange_eq, measure_iUnion hdisj_sing (fun _ => measurableSet_singleton _)]
      have hts : (∑' n : ℕ, ν₁ {(n : ENNReal)}) = ∑' n : ℕ, ν₂ {(n : ENNReal)} :=
        tsum_congr hsingleton_eq
      rw [hts, ← measure_iUnion hdisj_sing (fun _ => measurableSet_singleton _), ← hrange_eq]
      change ν₂ (Set.range (Nat.cast : ℕ → ENNReal)) = 1
      rw [Measure.map_apply measurable_from_top (Set.countable_range _).measurableSet]
      have hpre_univ : (Nat.cast : ℕ → ENNReal) ⁻¹' Set.range (Nat.cast : ℕ → ENNReal) = Set.univ :=
        Set.preimage_range (Nat.cast : ℕ → ENNReal)
      rw [hpre_univ, measure_univ]
    have hν₁_compl : ν₁ (Set.range (Nat.cast : ℕ → ENNReal))ᶜ = 0 := by
      have : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map hμA_meas.aemeasurable
      rw [prob_compl_eq_one_sub (Set.countable_range _).measurableSet, hν₁_range, tsub_self]
    have hν₂_compl : ν₂ (Set.range (Nat.cast : ℕ → ENNReal))ᶜ = 0 := by
      rw [Measure.map_apply measurable_from_top (Set.countable_range _).measurableSet.compl]
      have hpre_empty : (Nat.cast : ℕ → ENNReal) ⁻¹' (Set.range (Nat.cast : ℕ → ENNReal))ᶜ = ∅ := by
        rw [Set.preimage_compl, Set.preimage_range, Set.compl_univ]
      rw [hpre_empty, measure_empty]
    refine Measure.ext fun S hS => ?_
    classical
    have hdecomp : ∀ (ν : Measure ENNReal), ν (Set.range (Nat.cast : ℕ → ENNReal))ᶜ = 0 →
        ν S = ∑' n : ℕ, if (n : ENNReal) ∈ S then ν {(n : ENNReal)} else 0 := by
      intro ν hνc
      have hdiff0 : ν (S \ Set.range (Nat.cast : ℕ → ENNReal)) = 0 :=
        measure_mono_null (fun _ hx => hx.2) hνc
      have hS_eq : ν S = ν (S ∩ Set.range (Nat.cast : ℕ → ENNReal)) := by
        have hu := Set.inter_union_sdiff S (Set.range (Nat.cast : ℕ → ENNReal))
        have hd : Disjoint (S ∩ Set.range (Nat.cast : ℕ → ENNReal))
            (S \ Set.range (Nat.cast : ℕ → ENNReal)) :=
          Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2
        have hmd : MeasurableSet (S \ Set.range (Nat.cast : ℕ → ENNReal)) :=
          hS.diff (Set.countable_range _).measurableSet
        calc
          ν S = ν ((S ∩ Set.range (Nat.cast : ℕ → ENNReal)) ∪
                (S \ Set.range (Nat.cast : ℕ → ENNReal))) := by rw [hu]
          _ = ν (S ∩ Set.range (Nat.cast : ℕ → ENNReal)) +
                ν (S \ Set.range (Nat.cast : ℕ → ENNReal)) := measure_union hd hmd
          _ = ν (S ∩ Set.range (Nat.cast : ℕ → ENNReal)) := by rw [hdiff0, add_zero]
      rw [hS_eq, hrange_eq, Set.inter_iUnion, measure_iUnion]
      · refine tsum_congr fun n => ?_
        by_cases hn : (n : ENNReal) ∈ S
        · have : S ∩ {(n : ENNReal)} = {(n : ENNReal)} := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
            exact ⟨fun h => h.2, fun h => ⟨h ▸ hn, h⟩⟩
          rw [this, if_pos hn]
        · have : S ∩ {(n : ENNReal)} = ∅ := by
            ext x; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨h1, rfl⟩; exact hn h1
          rw [this, measure_empty, if_neg hn]
      · intro i j hij
        exact (hdisj_sing hij).mono Set.inter_subset_right Set.inter_subset_right
      · intro n
        exact hS.inter (measurableSet_singleton _)
    rw [hdecomp ν₁ hν₁_compl, hdecomp ν₂ hν₂_compl]
    refine tsum_congr fun n => ?_
    by_cases hn : (n : ENNReal) ∈ S
    · simp [hn, ν₁, ν₂, hsingleton_eq n]
    · simp [hn]
  refine ⟨hclause_a, ?_, ?_, ?_⟩
  · -- Clause (b): intensity A = ⊤ → ∀ᵐ ω ∂P, μ ω A = ⊤
    intro A hA hAtop
    have ht_int := hint_slice_tendsto A hA
    rw [hAtop] at ht_int
    have hAk_fin : ∀ k : ℕ,
        intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) < ⊤ := by
      intro k
      refine lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_
      rw [hint_def, Measure.prod_prod]
      have hv : volume.restrict (Set.Ici (0 : ℝ)) (Set.Ioc (0 : ℝ) (k : ℝ)) < ⊤ := by
        rw [Measure.restrict_apply measurableSet_Ioc]
        exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) (by simp)
      have hf : ((rate : ENNReal) • F) Set.univ < ⊤ := by simp
      exact ENNReal.mul_lt_top hv hf
    have ht_nnreal :
        Tendsto
          (fun k : ℕ => (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal)
          atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have hev := (ENNReal.tendsto_nhds_top_iff_nnreal.mp ht_int) b
      filter_upwards [hev] with k hk
      have hle : (b : ENNReal) ≤
          ((intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal : ENNReal) := by
        rw [ENNReal.coe_toNNReal (ne_top_of_lt (hAk_fin k))]
        exact le_of_lt hk
      exact ENNReal.coe_le_coe.mp hle
    have hzero_le : ∀ m : ℕ, P {ω | μ ω A ≤ (m : ENNReal)} = 0 := by
      intro m
      have ht0 :
          Tendsto
            (fun k : ℕ =>
              ProbabilityTheory.poissonMeasure
                (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal
                (Set.Iic m))
            atTop (𝓝 (0 : ENNReal)) :=
        (Kyprianou.Ch02.poissonMeasureIicTendstoZeroV1 m).comp ht_nnreal
      have hle_k : ∀ k : ℕ,
          P {ω | μ ω A ≤ (m : ENNReal)} ≤
            ProbabilityTheory.poissonMeasure
              (intensity (A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))).toNNReal
              (Set.Iic m) := by
        intro k
        let Ak : Set (ℝ × ℝ) := A ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))
        have hAk_meas : MeasurableSet Ak := hslice_meas A hA k
        have hμAk_meas : Measurable (fun ω => μ ω Ak) :=
          measurable_marked_mu_eval T ξ hTmeas hξmeas hAk_meas
        have hsub : {ω | μ ω A ≤ (m : ENNReal)} ⊆ {ω | μ ω Ak ≤ (m : ENNReal)} :=
          fun ω hω => le_trans (measure_mono Set.inter_subset_left) hω
        calc
          P {ω | μ ω A ≤ (m : ENNReal)}
              ≤ P {ω | μ ω Ak ≤ (m : ENNReal)} := measure_mono hsub
          _ = (P.map (fun ω => μ ω Ak)) (Set.Iic (m : ENNReal)) := by
                rw [Measure.map_apply hμAk_meas measurableSet_Iic]; rfl
          _ = ((ProbabilityTheory.poissonMeasure (intensity Ak).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) (Set.Iic (m : ENNReal)) := by
                rw [hclause_a Ak hAk_meas (hAk_fin k)]
          _ = ProbabilityTheory.poissonMeasure (intensity Ak).toNNReal (Set.Iic m) := by
                rw [Measure.map_apply measurable_from_top measurableSet_Iic]
                congr 1; ext j; simp
      exact le_antisymm (ge_of_tendsto ht0 (Eventually.of_forall hle_k)) zero_le
    rw [ae_iff]
    have hcov : {ω | ¬ μ ω A = ⊤} ⊆ ⋃ m : ℕ, {ω | μ ω A ≤ (m : ENNReal)} := by
      intro ω hω
      simp only [Set.mem_iUnion] at hω ⊢
      obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hω
      exact ⟨m, le_of_lt hm⟩
    exact measure_mono_null hcov (measure_iUnion_null hzero_le)
  · -- Clause (c): Countable pairwise-disjoint independence
    intro ι _ A hAmeas hAdisj
    let π : ι → Set (Set Ω) := fun i =>
      (fun S => (fun ω => μ ω (A i)) ⁻¹' S) '' Set.range (Set.Iic : ENNReal → Set ENNReal)
    have hle : ∀ i, MeasurableSpace.comap (fun ω => μ ω (A i)) inferInstance ≤ ‹MeasurableSpace Ω› :=
      fun i => (measurable_marked_mu_eval T ξ hTmeas hξmeas (hAmeas i)).comap_le
    have hpi : ∀ i, IsPiSystem (π i) := by
      intro i s₁ hs₁ s₂ hs₂ _
      rcases hs₁ with ⟨_, ⟨x₁, rfl⟩, rfl⟩
      rcases hs₂ with ⟨_, ⟨x₂, rfl⟩, rfl⟩
      refine ⟨Set.Iic (min x₁ x₂), ⟨min x₁ x₂, rfl⟩, ?_⟩
      ext ω
      simp
    have hgen : ∀ i,
        MeasurableSpace.comap (fun ω => μ ω (A i)) inferInstance =
          MeasurableSpace.generateFrom (π i) := by
      intro i
      rw [← MeasurableSpace.comap_generateFrom]
      congr 1
      have hborel : (inferInstance : MeasurableSpace ENNReal) = borel ENNReal :=
        BorelSpace.measurable_eq
      rw [hborel, borel_eq_generateFrom_Iic]
    refine ProbabilityTheory.iIndepSets.iIndep hle π hpi hgen ?_
    rw [ProbabilityTheory.iIndepSets_iff]
    intro s f hf
    have hx_ex : ∀ i : s, ∃ x : ENNReal, f i = (fun ω => μ ω (A i)) ⁻¹' Set.Iic x := by
      intro i
      rcases hf i i.2 with ⟨_, ⟨x, rfl⟩, hfi⟩
      exact ⟨x, hfi.symm⟩
    choose x hx using hx_ex
    let e : Fin s.card ≃ s := (Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm
    have ht_lhs :
        Tendsto
          (fun k : ℕ =>
            P (⋂ i : s, {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i}))
          atTop (𝓝 (P (⋂ i ∈ s, f i))) := by
      let E : ℕ → Set Ω := fun k =>
        ⋂ i : s, {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i}
      have hE_anti : Antitone E := by
        intro k₁ k₂ hk ω hω
        simp only [E, Set.mem_iInter] at hω ⊢
        intro i
        exact le_trans (measure_mono (hslice_mono (A i) hk)) (hω i)
      have hE_meas : ∀ k, NullMeasurableSet (E k) P := by
        intro k
        refine (MeasurableSet.iInter fun i => ?_).nullMeasurableSet
        exact (measurable_marked_mu_eval T ξ hTmeas hξmeas (hslice_meas (A i) (hAmeas i) k))
          measurableSet_Iic
      have ht := tendsto_measure_iInter_atTop hE_meas hE_anti ⟨0, measure_ne_top P _⟩
      have hae_all :
          ∀ᵐ ω ∂P, ∀ i : s,
            (⨆ k : ℕ, μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) = μ ω (A i) :=
        ae_all_iff.mpr fun i => hμ_iSup_ae (A i) (hAmeas i)
      have hae_eq : (⋂ k : ℕ, E k) =ᵐ[P] (⋂ i ∈ s, f i) := by
        rw [MeasureTheory.ae_eq_set]
        constructor
        · have hsub : (⋂ k : ℕ, E k) \ (⋂ i ∈ s, f i) ⊆
              {ω | ¬ ∀ i : s,
                (⨆ k : ℕ, μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ)))) = μ ω (A i)} := by
            intro ω ⟨h1, h2⟩ hall
            apply h2
            simp only [Set.mem_iInter]
            intro i hi
            rw [hx ⟨i, hi⟩]
            change μ ω (A i) ≤ x ⟨i, hi⟩
            rw [← hall ⟨i, hi⟩, iSup_le_iff]
            intro k
            exact Set.mem_iInter.mp (Set.mem_iInter.mp h1 k) ⟨i, hi⟩
          exact measure_mono_null hsub (ae_iff.mp hae_all)
        · have hsub : (⋂ i ∈ s, f i) \ (⋂ k : ℕ, E k) = ∅ := by
            ext ω
            simp only [Set.mem_sdiff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and,
              not_forall]
            intro h hnot
            rcases hnot with ⟨k, hk⟩
            apply hk
            rw [Set.mem_iInter]
            intro i
            have hi := h i.1 i.2
            rw [hx i] at hi
            exact le_trans (measure_mono Set.inter_subset_left) hi
          rw [hsub, measure_empty]
      rw [measure_congr hae_eq] at ht
      exact ht
    have ht_rhs :
        Tendsto
          (fun k : ℕ =>
            ∏ i : s, P {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i})
          atTop (𝓝 (∏ i ∈ s, P (f i))) := by
      have hprod_eq : (∏ i ∈ s, P (f i)) = ∏ i : s, P {ω | μ ω (A i) ≤ x i} := by
        rw [← Finset.prod_coe_sort s (fun i => P (f i))]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hx i]
        rfl
      rw [hprod_eq]
      have hprod_ind : ∀ t : Finset s,
          Tendsto
            (fun k : ℕ =>
              ∏ i ∈ t, P {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i})
            atTop (𝓝 (∏ i ∈ t, P {ω | μ ω (A i) ≤ x i})) := by
        intro t
        induction t using Finset.cons_induction with
        | empty =>
          simp
        | cons a t ha ih =>
          simp_rw [Finset.prod_cons]
          exact ENNReal.Tendsto.mul (hμ_Iic_tendsto (A a) (hAmeas a) (x a))
            (Or.inr (ENNReal.prod_ne_top fun _ _ => measure_ne_top P _))
            ih
            (Or.inr (measure_ne_top P _))
      exact hprod_ind Finset.univ
    have heq_k : ∀ k : ℕ,
        P (⋂ i : s, {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i}) =
        ∏ i : s, P {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i} := by
      intro k
      let Ak : Fin s.card → Set (ℝ × ℝ) :=
        fun j => A (e j) ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))
      have hAk_ind :=
        (Kyprianou.Ch02.markedCompoundPoissonBoundedDisjointLawV6
          P rate hrate F hFzero N T ξ hTmeas hξmeas hNlevy hNlaw harrival hmarklaw hIID hcross
          (k : ℝ≥0) s.card Ak
          (fun j => hslice_meas (A (e j)) (hAmeas (e j)) k)
          (fun _ => Set.inter_subset_right)
          (fun j₁ j₂ hj =>
            (hAdisj (fun heq => hj (e.injective (Subtype.ext heq)))).mono
              Set.inter_subset_left Set.inter_subset_left)).2
      have hmul :=
        (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hAk_ind)
          Finset.univ (sets := fun j => Set.Iic (x (e j))) (fun _ _ => measurableSet_Iic)
      have hlhs_eq :
          (⋂ i : s, {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i}) =
          (⋂ j ∈ (Finset.univ : Finset (Fin s.card)), (fun ω => μ ω (Ak j)) ⁻¹' Set.Iic (x (e j))) := by
        ext ω
        simp only [Set.mem_iInter, Finset.mem_univ, forall_true_left, Set.mem_preimage,
          Set.mem_Iic, Ak]
        exact ⟨fun h j => h (e j), fun h i => by simpa using h (e.symm i)⟩
      have hrhs_eq :
          (∏ i : s, P {ω | μ ω (A i ∩ (Set.Ioc (0 : ℝ) (k : ℝ) ×ˢ (Set.univ : Set ℝ))) ≤ x i}) =
          (∏ j ∈ (Finset.univ : Finset (Fin s.card)), P ((fun ω => μ ω (Ak j)) ⁻¹' Set.Iic (x (e j)))) := by
        refine (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
      rw [hlhs_eq, hrhs_eq]
      exact hmul
    simp_rw [heq_k] at ht_lhs
    exact tendsto_nhds_unique ht_lhs ht_rhs
  · -- Clause (d): directly from Proved theorem Kyprianou.ch02MarkedPoissonCountEqualsN
    exact Kyprianou.ch02MarkedPoissonCountEqualsN
      P rate hrate F hFzero N T ξ hNlevy hNlaw harrival hmarklaw hIID hcross
