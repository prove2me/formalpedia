-- Prove2me | solution 1 for OAI.Problem356.Transport.exists_measurable_lift_preserving_label
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:47:22.287158+00:00
-- url     : https://prove2.me/submissions/65cc2361-12cb-41a0-bca1-e77b33c7e79e

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel

open OAI OAI.Problem356
universe uX uY uIndex
open MeasureTheory Set
open scoped ENNReal
open ProbabilityTheory Filter Topology
open scoped unitInterval

theorem pb_cdf_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    μ.real {x : ℝ | cdf μ x ≤ u} = u := by
  set F := cdf μ with hF
  rcases eq_or_lt_of_le hu1 with h1 | h1
  · subst h1
    have : {x : ℝ | F x ≤ 1} = Set.univ := Set.eq_univ_of_forall fun x => cdf_le_one μ x
    rw [this]; simp
  set S := {x : ℝ | F x ≤ u} with hS
  have hSc : IsClosed S := isClosed_le hc continuous_const
  obtain ⟨x0, hx0⟩ : ∃ x0, u < F x0 :=
    ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds h1)).exists
  have hbdd : BddAbove S := by
    refine ⟨x0, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have := monotone_cdf μ hlt.le
    exact absurd (lt_of_lt_of_le hx0 this) (not_lt.mpr hx)
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    have hu0' : u ≤ 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨x, hx⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds hpos)).exists
      have : x ∈ S := le_of_lt hx
      rw [he] at this; exact this
    simp; linarith
  set a := sSup S with ha
  have haS : a ∈ S := hSc.csSup_mem hne hbdd
  have hSI : S = Set.Iic a := by
    ext x
    constructor
    · intro hx; exact le_csSup hbdd hx
    · intro hx; exact le_trans (monotone_cdf μ hx) haS
  have hFa : F a = u := by
    apply le_antisymm haS
    by_contra hlt
    push Not at hlt
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hc.tendsto a).eventually (gt_mem_nhds hlt))
    have hmem : a + ε / 2 ∈ S := by
      show F (a + ε / 2) ≤ u
      apply le_of_lt
      apply hball
      rw [Real.dist_eq]
      rw [abs_of_pos (by linarith)]
      linarith
    have := le_csSup hbdd hmem
    linarith
  rw [hSI, ← cdf_eq_real, ← hF, hFa]

theorem pb_cdf_cont (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ x, ν {x} = 0) :
    Continuous (cdf ν) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf ν).measure_singleton x
  rw [measure_cdf, h x] at h1
  have h2 : cdf ν x - Function.leftLim (cdf ν) x ≤ 0 := ENNReal.ofReal_eq_zero.mp h1.symm
  have h3 := (monotone_cdf ν).leftLim_le (le_refl x)
  linarith

theorem pb_uniform {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] :
    ∃ f : X → I, Measurable f ∧ Measure.map f μ = volume := by
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := X)
  set ν := Measure.map e μ with hν
  have hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  have hatom : ∀ x, ν {x} = 0 := by
    intro x
    rw [hν, Measure.map_apply he.measurable (measurableSet_singleton x)]
    rcases (e ⁻¹' {x}).eq_empty_or_nonempty with h | ⟨y, hy⟩
    · rw [h]; simp
    · have : e ⁻¹' {x} = {y} := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy ⊢
        constructor
        · intro hz; exact he.injective (hz.trans hy.symm)
        · intro hz; rw [hz, hy]
      rw [this]; exact measure_singleton y
  have hc := pb_cdf_cont ν hatom
  let f : X → I := fun x => ⟨cdf ν (e x), cdf_nonneg ν _, cdf_le_one ν _⟩
  have hf : Measurable f := (hc.measurable.comp he.measurable).subtype_mk
  refine ⟨f, hf, ?_⟩
  have hprob : IsProbabilityMeasure (Measure.map f μ) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply Measure.ext_of_Iic
  intro a
  rw [unitInterval.volume_Iic, Measure.map_apply hf measurableSet_Iic]
  have hset : f ⁻¹' Set.Iic a = e ⁻¹' {y : ℝ | cdf ν y ≤ (a : ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    rfl
  rw [hset, ← Measure.map_apply he.measurable (measurableSet_le hc.measurable measurable_const), ← hν]
  have := pb_cdf_sub ν hc a.2.1 a.2.2
  rw [← ofReal_measureReal (measure_ne_top ν _), this]

theorem pb_quantile_key (ν : Measure ℝ) [IsProbabilityMeasure ν] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (x : ℝ) : sInf {y | u ≤ cdf ν y} ≤ x ↔ u ≤ cdf ν x := by
  set S := {y | u ≤ cdf ν y} with hS
  obtain ⟨y0, hy0⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hu1)).exists
  have hne : S.Nonempty := ⟨y0, hy0.le⟩
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hu0))
  have hbdd : BddBelow S := by
    refine ⟨b, fun y hy => ?_⟩
    by_contra h
    push Not at h
    exact absurd hy (not_le.mpr (hb y h.le))
  constructor
  · intro hx
    set a := sInf S
    have hFa : u ≤ cdf ν a := by
      have hcw : ContinuousWithinAt (cdf ν) (Set.Ioi a) a :=
        ((cdf ν).right_continuous a).mono Set.Ioi_subset_Ici_self
      apply ge_of_tendsto hcw
      apply eventually_nhdsWithin_of_forall
      intro y hy
      obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
      exact le_trans hs (monotone_cdf ν hsy.le)
    exact le_trans hFa (monotone_cdf ν hx)
  · intro hx
    exact csInf_le hbdd hx

theorem pb_I_null : (volume : Measure I) {u : I | ¬ ((u : ℝ) ∈ Set.Ioo 0 1)} = 0 := by
  apply measure_mono_null (t := {0} ∪ {1})
  · intro u hu
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, not_and_or, not_lt] at hu
    rcases hu with h | h
    · left; exact Subtype.ext (le_antisymm h u.2.1)
    · right; exact Subtype.ext (le_antisymm u.2.2 h)
  · apply measure_union_null
    · rw [← Set.Icc_self, unitInterval.volume_Icc]; simp
    · rw [← Set.Icc_self, unitInterval.volume_Icc]; simp

theorem pb_quantile (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ q : I → ℝ, Measurable q ∧ Measure.map q volume = ν := by
  classical
  let q : I → ℝ := fun u => if (u : ℝ) ∈ Set.Ioo 0 1 then sInf {y | (u : ℝ) ≤ cdf ν y} else 0
  have hpre : ∀ x, q ⁻¹' Set.Iic x = ({u : I | (u : ℝ) ∈ Set.Ioo 0 1} ∩ {u | (u : ℝ) ≤ cdf ν x}) ∪
      ({u : I | ¬ (u : ℝ) ∈ Set.Ioo 0 1} ∩ {_u | (0 : ℝ) ≤ x}) := by
    intro x
    ext u
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, q]
    by_cases hu : (u : ℝ) ∈ Set.Ioo 0 1
    · rw [if_pos hu, pb_quantile_key ν hu.1 hu.2]
      tauto
    · rw [if_neg hu]
      tauto
  have hIoo : MeasurableSet {u : I | (u : ℝ) ∈ Set.Ioo 0 1} := measurable_subtype_coe measurableSet_Ioo
  have hmeas : ∀ x, MeasurableSet (q ⁻¹' Set.Iic x) := by
    intro x
    rw [hpre x]
    exact (hIoo.inter (measurableSet_le measurable_subtype_coe measurable_const)).union
      (hIoo.compl.inter (MeasurableSet.const _))
  have hq : Measurable q := measurable_of_Iic hmeas
  refine ⟨q, hq, ?_⟩
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hq measurableSet_Iic, ← ofReal_cdf]
  have hT : (volume : Measure I) {u : I | (u : ℝ) ≤ cdf ν x} = ENNReal.ofReal (cdf ν x) := by
    have := unitInterval.volume_Iic (⟨cdf ν x, cdf_nonneg ν x, cdf_le_one ν x⟩ : I)
    exact this
  rw [← hT]
  apply measure_congr
  have hae : ∀ᵐ u : I ∂(volume : Measure I), (u : ℝ) ∈ Set.Ioo 0 1 := pb_I_null
  filter_upwards [hae] with u hu
  apply propext
  change u ∈ q ⁻¹' Set.Iic x ↔ u ∈ {u : I | (u : ℝ) ≤ cdf ν x}
  rw [hpre x]
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

theorem pb_transport {X Y : Type*}
    [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass μ]
    (hmass : μ Set.univ = ν Set.univ) :
    ∃ Q : X → Y, Measurable Q ∧ Measure.map Q μ = ν := by
  set m := μ Set.univ with hm
  rcases eq_or_ne m 0 with h0 | h0
  · obtain ⟨y⟩ := ‹Nonempty Y›
    refine ⟨fun _ => y, measurable_const, ?_⟩
    have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp h0
    have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (hmass ▸ h0)
    rw [hμ, hν, Measure.map_zero]
  have htop : m ≠ ⊤ := measure_ne_top μ _
  set μ' := m⁻¹ • μ with hμ'
  set ν' := m⁻¹ • ν with hν'
  have hμp : IsProbabilityMeasure μ' := ⟨by
    rw [hμ', Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]⟩
  have hνp : IsProbabilityMeasure ν' := ⟨by
    rw [hν', Measure.smul_apply, smul_eq_mul, ← hmass, ENNReal.inv_mul_cancel h0 htop]⟩
  have hμn : NullSingletonClass μ' := ⟨fun x => by
    rw [hμ', Measure.smul_apply, measure_singleton, smul_zero]⟩
  obtain ⟨f, hf, hfmap⟩ := pb_uniform μ'
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := Y)
  have : IsProbabilityMeasure (Measure.map e ν') := Measure.isProbabilityMeasure_map he.measurable.aemeasurable
  obtain ⟨q, hq, hqmap⟩ := pb_quantile (Measure.map e ν')
  obtain ⟨r, hr, hre⟩ := he.exists_measurable_extend (measurable_id (α := Y)) (fun _ => ‹Nonempty Y›)
  refine ⟨r ∘ q ∘ f, hr.comp (hq.comp hf), ?_⟩
  have hμeq : μ = m • μ' := by
    rw [hμ', smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]
  have hνeq : ν = m • ν' := by
    rw [hν', smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]
  have h1 : Measure.map (r ∘ q ∘ f) μ' = ν' := by
    rw [← Measure.map_map hr (hq.comp hf), ← Measure.map_map hq hf, hfmap, hqmap,
      Measure.map_map hr he.measurable, hre, Measure.map_id]
  conv_lhs => rw [hμeq]
  rw [Measure.map_smul, h1, ← hνeq]

theorem pb_partition {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty ι›
  let idx : α → ι := fun x => if h : ∃ i, x ∈ B i then Classical.choose h else i0
  have hidx : ∀ i x, x ∈ B i → idx x = i := by
    intro i x hx
    have h : ∃ i, x ∈ B i := ⟨i, hx⟩
    simp only [idx, dif_pos h]
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (Classical.choose_spec h) hx
  let f : α → β := fun x => T (idx x) x
  have hEq : ∀ i, EqOn f (T i) (B i) := by
    intro i x hx
    simp only [f, hidx i x hx]
  have hpre : ∀ s, f ⁻¹' s = (⋃ i, B i ∩ T i ⁻¹' s) ∪ ((⋃ i, B i)ᶜ ∩ T i0 ⁻¹' s) := by
    intro s
    ext x
    by_cases hx : ∃ i, x ∈ B i
    · obtain ⟨i, hi⟩ := hx
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff]
      rw [hEq i hi]
      constructor
      · intro h; exact Or.inl ⟨i, hi, h⟩
      · rintro (⟨j, hj, h⟩ | ⟨h, _⟩)
        · have : i = j := by
            by_contra hne; exact Set.disjoint_left.mp (hdisj hne) hi hj
          subst this; exact h
        · exact absurd ⟨i, hi⟩ h
    · have hfx : f x = T i0 x := by simp only [f, idx, dif_neg hx]
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, hfx]
      constructor
      · intro h; exact Or.inr ⟨hx, h⟩
      · rintro (⟨j, hj, h⟩ | ⟨_, h⟩)
        · exact absurd ⟨j, hj⟩ hx
        · exact h
  have hfm : Measurable f := by
    intro s hs
    rw [hpre s]
    exact (MeasurableSet.iUnion fun i => (hB i).inter (hT i hs)).union
      ((MeasurableSet.iUnion hB).compl.inter (hT i0 hs))
  refine ⟨f, hfm, hEq, ?_⟩
  ext s hs
  rw [Measure.map_apply hfm hs, Measure.sum_apply _ hs]
  have hnull : μ (⋃ i, B i)ᶜ = 0 := ae_iff.mp hcover
  rw [← measure_inter_conull hnull, Set.inter_iUnion,
    measure_iUnion (fun i j hij => Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hij))
      (fun i => (hfm hs).inter (hB i))]
  refine tsum_congr (fun i => ?_)
  rw [Measure.map_apply (hT i) hs, Measure.restrict_apply (hT i hs)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h, hx⟩; exact ⟨(hEq i hx) ▸ h, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨(hEq i hx).symm ▸ h, hx⟩

theorem solution
    {X : Type uX} {Y : Type uY} {ι : Type uIndex} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [Nonempty ι]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f)
    (hmarg : ν.map f = μ) (p : X → ι) (hp : Measurable p) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, p (f (Q x)) = p x := by
  classical
  let Xs : ι → Set X := fun i => p ⁻¹' {i}
  let Ys : ι → Set Y := fun i => (p ∘ f) ⁻¹' {i}
  have hXs : ∀ i, MeasurableSet (Xs i) := fun i => hp (measurableSet_singleton i)
  have hYs : ∀ i, MeasurableSet (Ys i) := fun i => (hp.comp hf) (measurableSet_singleton i)
  have hmassi : ∀ i, (μ.restrict (Xs i)) Set.univ = (ν.restrict (Ys i)) Set.univ := by
    intro i
    rw [Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Set.univ_inter, ← hmarg, Measure.map_apply hf (hXs i)]
    rfl
  have hnull : ∀ i, NullSingletonClass (μ.restrict (Xs i)) := fun i => ⟨fun x =>
    le_antisymm ((Measure.restrict_apply_le _ _).trans (measure_singleton x).le) bot_le⟩
  have hQ : ∀ i, ∃ Q : X → Y, Measurable Q ∧ Measure.map Q (μ.restrict (Xs i)) = ν.restrict (Ys i) :=
    fun i => pb_transport _ _ (hmassi i)
  choose Qs hQm hQmap using hQ
  have hdisjX : Pairwise fun i j => Disjoint (Xs i) (Xs j) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hi hj => hij (hi.symm.trans hj)
  have hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, Xs i := Filter.Eventually.of_forall fun x =>
    Set.mem_iUnion.mpr ⟨p x, rfl⟩
  obtain ⟨Q, hQmeas, hEq, hQsum⟩ := pb_partition μ Xs hXs hdisjX hcover Qs hQm
  refine ⟨Q, hQmeas, ?_, ?_⟩
  · rw [hQsum]
    simp_rw [hQmap]
    ext s hs
    rw [Measure.sum_apply _ hs]
    simp_rw [Measure.restrict_apply hs]
    rw [← measure_iUnion]
    · congr 1
      ext y
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun ⟨i, h, _⟩ => h, fun h => ⟨p (f y), h, rfl⟩⟩
    · intro i j hij
      exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
        (Set.disjoint_left.mpr fun y hi hj => hij (hi.symm.trans hj))
    · exact fun i => hs.inter (hYs i)
  · have hi : ∀ i, ∀ᵐ x ∂μ, x ∈ Xs i → p (f (Q x)) = p x := by
      intro i
      have h1 : ∀ᵐ x ∂(μ.restrict (Xs i)), Qs i x ∈ Ys i := by
        have : ∀ᵐ y ∂(ν.restrict (Ys i)), y ∈ Ys i := ae_restrict_mem (hYs i)
        rw [← hQmap i] at this
        exact (ae_map_iff (hQm i).aemeasurable (hYs i)).mp this
      rw [ae_restrict_iff' (hXs i)] at h1
      filter_upwards [h1] with x hx hxi
      have h2 := hx hxi
      rw [hEq i hxi]
      simp only [Ys, Xs, Set.mem_preimage, Set.mem_singleton_iff, Function.comp] at h2 hxi ⊢
      rw [h2, hxi]
    have hall := ae_all_iff.mpr hi
    filter_upwards [hall] with x hx
    exact hx (p x) rfl

