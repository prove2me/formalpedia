-- Prove2me | solution 1 for Kyprianou.Ch01.aggregateClaims_expMoment
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:36:23.398077+00:00
-- url     : https://prove2.me/submissions/6cb525b2-ba03-4278-a2dd-49c26db9f05d

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

/-- The fibre `{jumpCount T t = n}` described by finitely/countably many inequalities. -/
theorem aggExpMoment_aux_jumpCount_eq_iff (T : ℕ → ℝ) (t : ℝ) (n : ℕ) :
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

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (θ : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hint : Integrable
      (fun ω => Real.exp (θ * aggregateClaims arrival claims t ω)) P) :
    Integrable (fun y : ℝ => Real.exp (θ * y)) F ∧
      (∫ ω, Real.exp (θ * aggregateClaims arrival claims t ω) ∂P) =
        Real.exp ((rate : ℝ) * (t : ℝ) * ((∫ y, Real.exp (θ * y) ∂F) - 1)) := by
  classical
  set f : ℕ ⊕ ℕ → Ω → ℝ := Sum.elim arrival claims with hf
  set m : ℕ ⊕ ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (f i) inferInstance
    with hm
  have hmeas_f : ∀ i, Measurable (f i) := by
    rintro (i | i)
    exacts [hd.measurable_interarrival i, hd.measurable_mark i]
  have hm_le : ∀ i, m i ≤ ‹MeasurableSpace Ω› := fun i => (hmeas_f i).comap_le
  have hiInd : iIndep m P := (iIndepFun_iff_iIndep _ f P).mp hd.indep
  have hsup_le : ∀ S : Set (ℕ ⊕ ℕ), (⨆ i ∈ S, m i) ≤ ‹MeasurableSpace Ω› :=
    fun S => iSup₂_le (fun i _ => hm_le i)
  have hmS : ∀ (S : Set (ℕ ⊕ ℕ)) i, i ∈ S → Measurable[⨆ j ∈ S, m j] (f i) := fun S i hi =>
    Measurable.of_comap_le (le_iSup₂ (f := fun j (_ : j ∈ S) => m j) i hi)
  have hfac : ∀ (S U : Set (ℕ ⊕ ℕ)), Disjoint S U → ∀ (X Y : Ω → ℝ≥0∞),
      Measurable[⨆ i ∈ S, m i] X → Measurable[⨆ i ∈ U, m i] Y →
      ∫⁻ ω, X ω * Y ω ∂P = (∫⁻ ω, X ω ∂P) * ∫⁻ ω, Y ω ∂P := fun S U hSU X Y hX hY =>
    lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (hsup_le S) (hsup_le U) (indep_iSup_of_disjoint hm_le hiInd hSU) hX hY
  -- the jump count
  set Sτ : Set (ℕ ⊕ ℕ) := {i | i.isLeft} with hSτ
  set T : ℕ → Ω → ℝ := fun n ω => ProbabilityTheory.arrival arrival n ω with hT
  set N : Ω → ℕ := fun ω => ProbabilityTheory.jumpCount (fun n => T n ω) (t : ℝ) with hN
  have hTmeas : ∀ n, Measurable[⨆ j ∈ Sτ, m j] (T n) := fun n =>
    Finset.measurable_sum _ (fun i _ => hmS Sτ (Sum.inl i) (by simp [hSτ]))
  have hNmeas : Measurable[⨆ j ∈ Sτ, m j] N := by
    refine @measurable_to_countable' ℕ Ω _ _ (⨆ j ∈ Sτ, m j) N (fun n => ?_)
    have : N ⁻¹' {n} = ({ω | t < T n ω} ∩ ⋂ k ∈ Finset.range n, {ω | T k ω ≤ t}) ∪
        ({ω | n = 0} ∩ ⋂ k, {ω | T k ω ≤ t}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hN,
        aggExpMoment_aux_jumpCount_eq_iff, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_range]
      rfl
    rw [this]
    refine MeasurableSet.union (MeasurableSet.inter (measurableSet_lt measurable_const
      (hTmeas n)) (Finset.measurableSet_biInter _ fun k _ =>
        measurableSet_le (hTmeas k) measurable_const))
      (MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.iInter fun k =>
        measurableSet_le (hTmeas k) measurable_const))
  have hNmeas' : Measurable N := hNmeas.mono (hsup_le _) le_rfl
  have hlaw : P.map N = poissonMeasure (rate * t) :=
    levy_foundations_compoundPoissonJumpCountLaw
      ⟨hd.measurable_interarrival, hd.measurable_mark, hd.indep, hd.law_interarrival,
        hd.law_mark⟩ hrate t
  have hPN : ∀ n, P (N ⁻¹' {n}) =
      ENNReal.ofReal (Real.exp (-((rate * t : ℝ≥0) : ℝ)) * ((rate * t : ℝ≥0) : ℝ) ^ n
        / (n.factorial : ℝ)) := by
    intro n
    rw [← Measure.map_apply hNmeas' (measurableSet_singleton n), hlaw, poissonMeasure_singleton]
  -- claims factors
  set Sy : Set (ℕ ⊕ ℕ) := {i | i.isRight} with hSy
  set g : ℕ → Ω → ℝ≥0∞ := fun i ω => ENNReal.ofReal (Real.exp (θ * claims i ω)) with hg
  have hgmeas : ∀ (S : Set (ℕ ⊕ ℕ)) i, Sum.inr i ∈ S → Measurable[⨆ j ∈ S, m j] (g i) :=
    fun S i hi => ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hmS S (Sum.inr i) hi)))
  set Mt : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (Real.exp (θ * y)) ∂F with hMt
  have hgint : ∀ i, ∫⁻ ω, g i ω ∂P = Mt := fun i =>
    (hd.law_mark i).lintegral_comp (f := fun y => ENNReal.ofReal (Real.exp (θ * y)))
      (by fun_prop)
  have hprod : ∀ n, ∫⁻ ω, ∏ i ∈ Finset.range n, g i ω ∂P = Mt ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.prod_range_succ]
      rw [hfac (Sum.inr '' Iio n) {Sum.inr n} (by
          rw [Set.disjoint_singleton_right]
          rintro ⟨k, hk, hkn⟩
          simp only [Sum.inr.injEq] at hkn
          exact (lt_irrefl n) (hkn ▸ hk))
        _ _ (Finset.measurable_prod _ (fun i hi => hgmeas _ i
          ⟨i, by simpa using hi, rfl⟩)) (hgmeas _ n rfl), ih, hgint, pow_succ]
  -- decomposition along the jump count
  have hS : ∀ ω, aggregateClaims arrival claims t ω =
      ∑ i ∈ Finset.range (N ω), claims i ω := by
    intro ω
    simp [aggregateClaims, ProbabilityTheory.compoundPoisson, ProbabilityTheory.piecewisePath,
      hN, hT]
  have hG : ∀ ω, ENNReal.ofReal (Real.exp (θ * aggregateClaims arrival claims t ω)) =
      ∑' n, (N ⁻¹' {n}).indicator (fun ω => ∏ i ∈ Finset.range n, g i ω) ω := by
    intro ω
    rw [tsum_eq_single (f := fun n => (N ⁻¹' {n}).indicator (fun ω => ∏ i ∈ Finset.range n, g i ω) ω) (N ω) (fun n hn => indicator_of_notMem (s := N ⁻¹' {n}) (show ω ∉ N ⁻¹' {n} from fun h => hn (Eq.symm h)) _),
      indicator_of_mem (show ω ∈ N ⁻¹' {N ω} from rfl), hS, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  have hlint : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * aggregateClaims arrival claims t ω)) ∂P =
      ∑' n, P (N ⁻¹' {n}) * Mt ^ n := by
    simp_rw [hG]
    rw [lintegral_tsum (fun n => ((Finset.measurable_prod _ (fun i _ =>
      (hgmeas Sy i (by simp [hSy])).mono (hsup_le _) le_rfl)).indicator
        (hNmeas' (measurableSet_singleton n))).aemeasurable)]
    congr 1
    funext n
    have h1 : (N ⁻¹' {n}).indicator (fun ω => ∏ i ∈ Finset.range n, g i ω) =
        fun ω => (N ⁻¹' {n}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
          ∏ i ∈ Finset.range n, g i ω := by
      funext ω
      by_cases hω : ω ∈ N ⁻¹' {n}
      · simp [indicator_of_mem hω]
      · simp [indicator_of_notMem hω]
    rw [h1, hfac Sτ Sy (by
        rw [Set.disjoint_left]
        rintro (i | i) h1 h2 <;> simp [hSτ, hSy] at h1 h2)
      _ _ (measurable_const.indicator (hNmeas (measurableSet_singleton n)))
      (Finset.measurable_prod _ (fun i _ => hgmeas Sy i (by simp [hSy]))),
      lintegral_indicator_const (hNmeas' (measurableSet_singleton n)), one_mul, hprod]
  -- finiteness of the claim exponential moment
  set lam : ℝ := ((rate * t : ℝ≥0) : ℝ) with hlam
  have hlam_pos : 0 < lam := by
    rw [hlam]; exact_mod_cast mul_pos hrate ht
  have hfin := hint.lintegral_lt_top
  rw [hlint] at hfin
  have hMt_fin : Mt ≠ ∞ := by
    intro htop
    have h1 : P (N ⁻¹' {1}) * Mt ^ 1 ≤ ∑' n, P (N ⁻¹' {n}) * Mt ^ n :=
      ENNReal.le_tsum (f := fun n => P (N ⁻¹' {n}) * Mt ^ n) 1
    have hpos : P (N ⁻¹' {1}) ≠ 0 := by
      rw [hPN]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have h2 : P (N ⁻¹' {1}) * Mt ^ 1 = ∞ := by rw [htop, pow_one, ENNReal.mul_top hpos]
    rw [h2] at h1
    exact absurd (lt_of_le_of_lt h1 hfin) (lt_irrefl _)
  have hFint : Integrable (fun y : ℝ => Real.exp (θ * y)) F :=
    ⟨Measurable.aestronglyMeasurable (by fun_prop),
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => (Real.exp_pos _).le)).mpr
        (lt_top_iff_ne_top.mpr hMt_fin)⟩
  refine ⟨hFint, ?_⟩
  set M : ℝ := ∫ y, Real.exp (θ * y) ∂F with hM
  have hM0 : 0 ≤ M := integral_nonneg fun y => (Real.exp_pos _).le
  have hMt_eq : Mt = ENNReal.ofReal M :=
    (ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ fun y => (Real.exp_pos _).le)).symm
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
    hint.aestronglyMeasurable, hlint]
  have hterm : ∀ n, P (N ⁻¹' {n}) * Mt ^ n =
      ENNReal.ofReal (Real.exp (-lam) * ((lam * M) ^ n / (n.factorial : ℝ))) := by
    intro n
    rw [hPN, hMt_eq, ← ENNReal.ofReal_pow hM0, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow]
    ring
  have hexp : HasSum (fun n : ℕ => (lam * M) ^ n / (n.factorial : ℝ)) (Real.exp (lam * M)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (lam * M)
  have hsum := hexp.mul_left (Real.exp (-lam))
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum.summable, hsum.tsum_eq,
    ENNReal.toReal_ofReal (by positivity), ← Real.exp_add]
  congr 1
  rw [hlam, NNReal.coe_mul]
  ring
