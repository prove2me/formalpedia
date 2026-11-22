-- Prove2me | solution 1 for Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T10:25:49.411242+00:00
-- url     : https://prove2.me/submissions/fee0c476-a01d-4bda-9363-81073e7a4601

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_positive_future_count_factor_from_ae_history
import Theorems.Thm_AvramDividend_Classical_avram_a06_zero_future_factor_from_ae_history
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_finite_nat_atomic_chain_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_nat_family_independent_of_atomic_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_disjoint_iid_mark_sums_independent
import Theorems.Thm_levy_foundations_jumpCountLtIff
import Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
import Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
import Theorems.Thm_Kyprianou_Ch01_compoundDriver_toFoundations
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Scaling an exponential variable of rate `r` by `r` gives a unit exponential. -/
theorem cpIncr_aux_expMeasure_map_mul (r : ℝ) (hr : 0 < r) :
    (expMeasure r).map (fun x => r * x) = expMeasure 1 := by
  have h1 := isProbabilityMeasure_expMeasure hr
  have h2 := isProbabilityMeasure_expMeasure (show (0:ℝ) < 1 from one_pos)
  have hmeas : Measurable (fun x : ℝ => r * x) := measurable_const.mul measurable_id
  have : IsProbabilityMeasure ((expMeasure r).map (fun x => r * x)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine Measure.ext_of_Iic _ _ (fun a => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic]
  have hpre : (fun x : ℝ => r * x) ⁻¹' Iic a = Iic (a / r) := by
    ext x; simp [le_div_iff₀ hr, mul_comm]
  rw [hpre, ← ofReal_cdf, ← ofReal_cdf, cdf_expMeasure_eq hr, cdf_expMeasure_eq one_pos]
  congr 1
  by_cases ha : 0 ≤ a
  · rw [if_pos (div_nonneg ha hr.le), if_pos ha]
    congr 2
    field_simp
  · rw [if_neg (fun h => ha (by
      have := mul_nonneg h hr.le; rwa [div_mul_cancel₀ _ hr.ne'] at this)), if_neg ha]

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

/-- Count increments of a compound Poisson driver over a monotone grid are independent. -/
theorem cpIncr_aux_countIncrements_iIndep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate) (F : Measure ℝ)
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) ω =>
      ProbabilityTheory.jumpCount (fun k => ProbabilityTheory.arrival arrival k ω)
          (t i.succ : ℝ) -
        ProbabilityTheory.jumpCount (fun k => ProbabilityTheory.arrival arrival k ω)
          (t i.castSucc : ℝ)) P := by
  classical
  set r : ℝ := (rate : ℝ) with hrdef
  have hr : 0 < r := by simpa [r] using hrate
  set jc : ℝ → Ω → ℕ := fun u ω =>
    ProbabilityTheory.jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) u with hjc
  have hjcm : ∀ u, Measurable (jc u) := fun u =>
    cpIncr_aux_jumpCount_measurable _ arrival hd.measurable_interarrival u
  -- rescaled unit-rate clock
  set τ' : ℕ → Ω → ℝ := fun i ω => r * arrival i ω with hτ'
  have hτ'm : ∀ i, Measurable (τ' i) := fun i =>
    measurable_const.mul (hd.measurable_interarrival i)
  have hiid : iIndepFun τ' P :=
    (hd.indep.precomp Sum.inl_injective).comp (fun _ x => r * x)
      (fun _ => measurable_const.mul measurable_id)
  have hExp : ∀ i, HasLaw (τ' i) (expMeasure 1) P := by
    intro i
    have hY : HasLaw (fun x : ℝ => r * x) (expMeasure 1) (expMeasure r) :=
      ⟨(measurable_const.mul measurable_id).aemeasurable, cpIncr_aux_expMeasure_map_mul r hr⟩
    exact hY.comp (hd.law_interarrival i)
  set N : Ω → ℝ → ℕ := fun ω u => jc (u / r) ω with hN
  have hNjc : ∀ ω (a : ℝ), N ω (r * a) = jc a ω := by
    intro ω a
    simp only [hN, mul_div_cancel_left₀ a hr.ne']
  have hThr : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ' i ω) ≤ u := by
    filter_upwards [cpIncr_aux_threshold_ae P arrival claims rate hrate F hd] with ω hω u k
    rw [hω, le_div_iff₀ hr]
    simp only [τ', ProbabilityTheory.arrival, Finset.sum_mul, mul_comm r]
  set Z : Fin n → Ω → ℕ := fun i ω => jc (t i.succ) ω - jc (t i.castSucc) ω with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i =>
    (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp
      ((hjcm _).prodMk (hjcm _))
  -- the step factorisation
  have hStep : ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
      P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
        P {ω | ∀ i : Fin n, i < j → Z i ω = v i} * P {ω | Z j ω = k} := by
    intro j v k
    set clock : ℝ := r * (t j.castSucc : ℝ) with hclock
    have hclock0 : 0 ≤ clock := mul_nonneg hr.le (t j.castSucc).2
    set dt : ℝ := r * ((t j.succ : ℝ) - t j.castSucc) with hdt
    have hmono : (t j.castSucc : ℝ) ≤ t j.succ := by
      exact_mod_cast ht (Fin.castSucc_le_succ j)
    have hdt0 : 0 ≤ dt := mul_nonneg hr.le (by linarith)
    have hZj : ∀ ω, Z j ω = N ω (clock + dt) - N ω clock := by
      intro ω
      have : clock + dt = r * (t j.succ : ℝ) := by rw [hclock, hdt]; ring
      rw [this, hNjc, hNjc]
    have hmem : ∀ i : Fin n, i < j → ∀ a : Fin (n + 1), a ≤ i.succ →
        r * (t a : ℝ) ∈ Set.Iic clock := by
      intro i hi a ha
      have h1 : a ≤ j.castSucc := ha.trans (Fin.succ_le_castSucc_iff.mpr hi)
      have h2 : (t a : ℝ) ≤ t j.castSucc := by exact_mod_cast ht h1
      exact mul_le_mul_of_nonneg_left h2 hr.le
    set G : Set (Set.Iic clock → ℕ) := {f | ∀ (i : Fin n) (hi : i < j),
      f ⟨r * t i.succ, hmem i hi _ le_rfl⟩ -
        f ⟨r * t i.castSucc, hmem i hi _ (Fin.castSucc_le_succ i)⟩ = v i} with hG
    have hGm : MeasurableSet G := by
      have : G = ⋂ (i : Fin n), ⋂ (hi : i < j), {f : Set.Iic clock → ℕ |
          f ⟨r * t i.succ, hmem i hi _ le_rfl⟩ -
            f ⟨r * t i.castSucc, hmem i hi _ (Fin.castSucc_le_succ i)⟩ = v i} := by
        ext f; simp [hG]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => ?_
      have hpair : Measurable (fun f : Set.Iic clock → ℕ =>
          (f ⟨r * t i.succ, hmem i hi _ le_rfl⟩,
            f ⟨r * t i.castSucc, hmem i hi _ (Fin.castSucc_le_succ i)⟩)) :=
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)
      have hmf : Measurable (fun f : Set.Iic clock → ℕ =>
          f ⟨r * t i.succ, hmem i hi _ le_rfl⟩ -
            f ⟨r * t i.castSucc, hmem i hi _ (Fin.castSucc_le_succ i)⟩) :=
        (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp hpair
      exact hmf (measurableSet_singleton (v i))
    set H : Set Ω := {ω | ∀ i : Fin n, i < j → Z i ω = v i} with hH
    have hHG : H = (fun ω (s : Set.Iic clock) => N ω (s : ℝ)) ⁻¹' G := by
      ext ω
      simp only [hH, hG, Set.mem_ofPred_eq, Set.mem_preimage, hNjc, hZ]
    have hHpast : MeasurableSet[MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H := ⟨G, hGm, hHG.symm⟩
    have hHm : MeasurableSet H := by
      have : H = ⋂ (i : Fin n), ⋂ (_ : i < j), (Z i) ⁻¹' {v i} := by
        ext ω; simp [hH]
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        hZm i (measurableSet_singleton _)
    have hNc : Measurable (fun ω => N ω clock) := hjcm _
    have hset : ∀ (A : Set Ω) (k : ℕ), {ω | ω ∈ A ∧ N ω (clock + dt) - N ω clock = k} =
        {ω | ω ∈ A ∧ Z j ω = k} := by
      intro A k; ext ω; simp [hZj]
    rcases k with _ | k
    · have h1 := AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history τ' hτ'm
        hiid hExp N hThr clock hclock0 hNc H hHm hHpast dt hdt0
      have h2 := AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history τ' hτ'm
        hiid hExp N hThr clock hclock0 hNc Set.univ MeasurableSet.univ
        MeasurableSet.univ dt hdt0
      rw [hset] at h1 h2
      simp only [Set.mem_univ, true_and, measure_univ, one_mul] at h2
      rw [h2]
      simpa [hH] using h1
    · have h1 := AvramDividend.Classical.avram_a06_positive_future_count_factor_from_ae_history
        τ' hτ'm hiid hExp N hThr clock hclock0 hNc H hHm hHpast dt hdt0 (k + 1) (Nat.succ_pos k)
      rw [hset, show {ω | N ω (clock + dt) - N ω clock = k + 1} = {ω | Z j ω = k + 1} by
        ext ω; simp [hZj]] at h1
      simpa [hH] using h1
  have hAtoms := AvramDividend.Classical.avram_a06_generic_finite_nat_atomic_chain_product
    P n Z hStep
  exact AvramDividend.Classical.avram_a06_generic_nat_family_independent_of_atomic_product
    P n Z hZm hAtoms

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ)
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hDriver : IsCompoundPoissonDriver arrival claims rate F P) :
    HasIndependentIncrements (fun t : ℝ≥0 => aggregateClaims arrival claims t) P := by
  classical
  intro n t ht
  set jc : ℝ → Ω → ℕ := fun u ω =>
    ProbabilityTheory.jumpCount (fun k => ProbabilityTheory.arrival arrival k ω) u with hjc
  -- σ-algebras of interarrivals and marks
  set f : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim arrival claims with hf
  set m : ℕ ⊕ ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (f i) inferInstance
    with hm
  have hmeas_f : ∀ i, Measurable (f i) := by
    rintro (i | i)
    exacts [hDriver.measurable_interarrival i, hDriver.measurable_mark i]
  have hm_le : ∀ i, m i ≤ ‹MeasurableSpace Ω› := fun i => (hmeas_f i).comap_le
  have hiInd : iIndep m P := (iIndepFun_iff_iIndep _ f P).mp hDriver.indep
  have hmS : ∀ (S : Set (ℕ ⊕ ℕ)) i, i ∈ S → Measurable[⨆ j ∈ S, m j] (f i) := fun S i hi =>
    Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ S) => m j) i hi)
  set Sτ : Set (ℕ ⊕ ℕ) := {i | i.isLeft} with hSτ
  set SY : Set (ℕ ⊕ ℕ) := {i | i.isRight} with hSY
  have hdisj : Disjoint Sτ SY := by
    rw [Set.disjoint_left]
    rintro (i | i) h1 h2 <;> simp [hSτ, hSY] at h1 h2
  have hIndτY : Indep (⨆ j ∈ Sτ, m j) (⨆ j ∈ SY, m j) P :=
    indep_iSup_of_disjoint hm_le hiInd hdisj
  -- monotone modification of the jump counts on the grid
  set Nm : Fin (n + 1) → Ω → ℕ := fun i ω =>
    (Finset.univ.filter (fun k => k ≤ i)).sup (fun k => jc (t k) ω) with hNm
  have hNmono : ∀ ω, Monotone (fun i => Nm i ω) := by
    intro ω a b hab
    exact Finset.sup_mono (fun k hk => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hab)
  have hvec : ∀ (mm : MeasurableSpace Ω), (∀ k, Measurable[mm] (arrival k)) →
      Measurable[mm] (fun ω => fun i => Nm i ω) := by
    intro mm hτ
    have hv : Measurable[mm] (fun ω => fun k : Fin (n + 1) => jc (t k) ω) :=
      measurable_pi_lambda _ (fun k => cpIncr_aux_jumpCount_measurable mm arrival hτ _)
    have hg : Measurable (fun (w : Fin (n + 1) → ℕ) => fun i : Fin (n + 1) =>
        (Finset.univ.filter (fun k => k ≤ i)).sup w) := measurable_of_countable _
    exact hg.comp hv
  have hNmeas : Measurable (fun ω => fun i => Nm i ω) :=
    hvec _ hDriver.measurable_interarrival
  -- a.s. the jump count is monotone in time, so the modification is harmless
  have hjc_mono : ∀ᵐ ω ∂P, ∀ a b : ℝ, a ≤ b → jc a ω ≤ jc b ω := by
    filter_upwards [cpIncr_aux_threshold_ae P arrival claims rate hrate F hDriver] with ω hω a b hab
    by_contra hc
    push Not at hc
    have h1 := (hω a (jc b ω)).mp hc
    exact lt_irrefl _ ((hω b (jc b ω)).mpr (h1.trans hab))
  have hNm_eq : ∀ᵐ ω ∂P, ∀ i, Nm i ω = jc (t i) ω := by
    filter_upwards [hjc_mono] with ω hω i
    apply le_antisymm
    · exact Finset.sup_le (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact hω _ _ (by exact_mod_cast ht hk))
    · exact Finset.le_sup (f := fun k => jc (t k) ω) (by simp)
  -- the inputs of the random-block mark-sum lemma
  have hCount : iIndepFun (fun (i : Fin n) ω => Nm i.succ ω - Nm i.castSucc ω) P := by
    refine (iIndepFun_congr (fun i => ?_)).mp
      (cpIncr_aux_countIncrements_iIndep P arrival claims rate hrate F hDriver n t ht)
    filter_upwards [hNm_eq] with ω hω
    simp [hω, hjc]
  have hMarks : iIndepFun claims P := by
    have h := hDriver.indep.precomp (g := Sum.inr) Sum.inr_injective
    exact h
  have hSame : ∀ j k, IdentDistrib (claims j) (claims k) P P := fun j k =>
    ⟨(hDriver.measurable_mark j).aemeasurable, (hDriver.measurable_mark k).aemeasurable,
      by rw [(hDriver.law_mark j).map_eq, (hDriver.law_mark k).map_eq]⟩
  have hYvec : Measurable (fun ω => fun j => claims j ω) :=
    measurable_pi_lambda _ hDriver.measurable_mark
  have hSep : IndepFun (fun ω => fun i => Nm i ω) (fun ω => fun j => claims j ω) P := by
    have hX : Measurable[⨆ j ∈ Sτ, m j] (fun ω => fun i => Nm i ω) :=
      hvec _ (fun k => hmS Sτ (Sum.inl k) (by simp [hSτ]))
    have hvecY : ∀ (mm : MeasurableSpace Ω), (∀ j, Measurable[mm] (claims j)) →
        Measurable[mm] (fun ω => fun j => claims j ω) := fun mm h => measurable_pi_lambda _ h
    have hY : Measurable[⨆ j ∈ SY, m j] (fun ω => fun j => claims j ω) :=
      hvecY _ (fun j => hmS SY (Sum.inr j) (by simp [hSY]))
    exact (IndepFun_iff_Indep _ _ P).mpr
      (indep_of_indep_of_le_left (indep_of_indep_of_le_right hIndτY hY.comap_le) hX.comap_le)
  have hband := AvramDividend.Classical.avram_a06_random_disjoint_iid_mark_sums_independent
    P n Nm claims hNmeas hYvec hNmono hCount hMarks hSame hSep
  -- identify the band sums with the increments of the aggregate claims
  refine (iIndepFun_congr (fun i => ?_)).mp hband
  have hS : ∀ (u : ℝ≥0) ω, aggregateClaims arrival claims u ω =
      ∑ j ∈ Finset.range (jc u ω), claims j ω := by
    intro u ω
    simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath,
      hjc]
  filter_upwards [hNm_eq, hjc_mono] with ω hω hmono
  simp only [ProbabilityTheory.increment, hS, hω]
  have hle : jc (t i.castSucc) ω ≤ jc (t i.succ) ω :=
    hmono _ _ (by exact_mod_cast ht (Fin.castSucc_le_succ i))
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  ring
