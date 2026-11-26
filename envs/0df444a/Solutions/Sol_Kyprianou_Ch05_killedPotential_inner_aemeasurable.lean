-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_inner_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:07:18.712857+00:00
-- url     : https://prove2.me/submissions/8af7daee-c81e-4a07-bcdc-ae23193346d8

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  ∀ f : Real → ENNReal, Measurable f →
    AEMeasurable (fun t : Real =>
      ∫⁻ omega in {omega : Omega |
        (Real.toNNReal t : WithTop NNReal) < death omega},
        f (Y (Real.toNNReal t) omega) ∂P) (volume.restrict (Set.Ici (0 : Real))) := by
  intro f hf
  have hdeath : Measurable death := hKilled.2.2.1
  have hYAEMeas : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have h := (hKilled.1.1.stationary_increments 0 s).1
    have hinc : ProbabilityTheory.increment Y 0 (0 + s) = Y s := by
      funext ω
      simp [ProbabilityTheory.increment, hKilled.1.1.start_zero]
    rwa [hinc] at h
  -- a.e. lifts to the product measure, via measurable supersets of the null sets
  have hlift_snd : ∀ {q : Omega → Prop}, (∀ᵐ ω ∂P, q ω) →
      ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P), q p.2 := by
    intro q hq
    rw [MeasureTheory.ae_iff] at hq ⊢
    obtain ⟨T, hTsup, hTmeas, hTnull⟩ :=
      MeasureTheory.exists_measurable_superset_of_null hq
    have hsub : {p : Real × Omega | ¬ q p.2} ⊆ Set.univ ×ˢ T := by
      intro p hp
      exact ⟨Set.mem_univ _, hTsup hp⟩
    have hle : ((volume.restrict (Set.Ici (0 : Real))).prod P)
        {p : Real × Omega | ¬ q p.2} ≤ 0 :=
      calc ((volume.restrict (Set.Ici (0 : Real))).prod P) {p : Real × Omega | ¬ q p.2}
          ≤ ((volume.restrict (Set.Ici (0 : Real))).prod P) (Set.univ ×ˢ T) :=
            measure_mono hsub
      _ = (volume.restrict (Set.Ici (0 : Real))) Set.univ * P T :=
            MeasureTheory.Measure.prod_prod Set.univ T
      _ = 0 := by rw [hTnull, mul_zero]
    exact le_antisymm hle bot_le
  have hlift_fst : ∀ {q : Real → Prop},
      (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : Real))), q t) →
      ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P), q p.1 := by
    intro q hq
    rw [MeasureTheory.ae_iff] at hq ⊢
    obtain ⟨T, hTsup, hTmeas, hTnull⟩ :=
      MeasureTheory.exists_measurable_superset_of_null hq
    have hsub : {p : Real × Omega | ¬ q p.1} ⊆ T ×ˢ Set.univ := by
      intro p hp
      exact ⟨hTsup hp, Set.mem_univ _⟩
    have hle : ((volume.restrict (Set.Ici (0 : Real))).prod P)
        {p : Real × Omega | ¬ q p.1} ≤ 0 :=
      calc ((volume.restrict (Set.Ici (0 : Real))).prod P) {p : Real × Omega | ¬ q p.1}
          ≤ ((volume.restrict (Set.Ici (0 : Real))).prod P) (T ×ˢ Set.univ) :=
            measure_mono hsub
      _ = (volume.restrict (Set.Ici (0 : Real))) T * P Set.univ :=
            MeasureTheory.Measure.prod_prod T Set.univ
      _ = 0 := by rw [hTnull, zero_mul]
    exact le_antisymm hle bot_le
  have hfst_ae : ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P),
      p.1 ∈ Set.Ici (0 : Real) :=
    hlift_fst (ae_restrict_mem measurableSet_Ici)
  have hsnd_ae : ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P),
      IsCadlag (fun t => Y t p.2) :=
    hlift_snd hKilled.1.1.cadlag_ae
  -- dyadic step function from above: s n t = (⌊t * 2^n⌋₊ + 1) / 2^n, strictly above t
  have hs_gt : ∀ (n : ℕ) (t : Real), t < (⌊t * 2^n⌋₊ + 1 : Real) / 2^n := by
    intro n t
    have h2 : (0 : Real) < 2^n := by positivity
    rw [lt_div_iff₀ h2]
    exact Nat.lt_floor_add_one _
  have hs_le : ∀ (n : ℕ) (t : Real), 0 ≤ t →
      (⌊t * 2^n⌋₊ + 1 : Real) / 2^n ≤ t + ((2 : Real)^n)⁻¹ := by
    intro n t ht
    have h2 : (0 : Real) < 2^n := by positivity
    rw [div_le_iff₀ h2]
    have hfloor : (⌊t * 2^n⌋₊ : Real) ≤ t * 2^n :=
      Nat.floor_le (mul_nonneg ht (by positivity))
    have hmul : (t + ((2 : Real)^n)⁻¹) * 2^n = t * 2^n + 1 := by
      rw [add_mul, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero)]
    rw [hmul]
    linarith
  have hs_tendsto : ∀ t : Real, 0 ≤ t →
      Tendsto (fun n => (⌊t * 2^n⌋₊ + 1 : Real) / 2^n) atTop (nhds t) := by
    intro t ht
    have hinv : Tendsto (fun n => ((2 : Real)^n)⁻¹) atTop (nhds 0) := by
      have heq : (fun n => ((2 : Real)^n)⁻¹) = (fun n => (1 / 2)^n) := by
        funext n
        simp [inv_pow, one_div]
      rw [heq]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : Real) ≤ 1 / 2 by norm_num) (show (1 / 2 : Real) < 1 by norm_num)
    have hup : Tendsto (fun n => t + ((2 : Real)^n)⁻¹) atTop (nhds t) := by
      have h : Tendsto (fun n => t + ((2 : Real)^n)⁻¹) atTop (nhds (t + 0)) :=
        tendsto_const_nhds.add hinv
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Filter.Eventually.of_forall (fun n => le_of_lt (hs_gt n t)))
      (Filter.Eventually.of_forall (fun n => hs_le n t ht))
  -- measurability of the dyadic slabs
  have hfloor_meas : ∀ n : ℕ, Measurable (fun t : Real => ⌊t * 2^n⌋₊) :=
    fun n => (measurable_id.mul_const (2^n : Real)).nat_floor
  have hslab : ∀ (n k : ℕ),
      MeasurableSet ({t : Real | ⌊t * 2^n⌋₊ = k} ×ˢ (Set.univ : Set Omega)) := by
    intro n k
    apply MeasurableSet.prod _ MeasurableSet.univ
    exact hfloor_meas n (measurableSet_singleton k)
  -- the step approximants of the process are jointly AEMeasurable
  have hT : ∀ (n N : ℕ), AEMeasurable
      (∑ k ∈ Finset.range N,
        Set.indicator ({t : Real | ⌊t * 2^n⌋₊ = k} ×ˢ Set.univ)
          (fun q : Real × Omega => Y (Real.toNNReal (((k : Real) + 1) / 2^n)) q.2))
      ((volume.restrict (Set.Ici (0 : Real))).prod P) := by
    intro n N
    apply Finset.aemeasurable_sum
    intro k _
    have hsec : AEMeasurable
        (fun q : Real × Omega => Y (Real.toNNReal (((k : Real) + 1) / 2^n)) q.2)
        ((volume.restrict (Set.Ici (0 : Real))).prod P) :=
      (hYAEMeas (Real.toNNReal (((k : Real) + 1) / 2^n))).comp_snd
    exact AEMeasurable.indicator hsec (hslab n k)
  have hlimT : ∀ n : ℕ, ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P),
      Tendsto (fun N => (∑ k ∈ Finset.range N,
        Set.indicator ({t : Real | ⌊t * 2^n⌋₊ = k} ×ˢ Set.univ)
          (fun q : Real × Omega => Y (Real.toNNReal (((k : Real) + 1) / 2^n)) q.2)) p) atTop
        (nhds (Y (Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) p.2)) := by
    intro n
    filter_upwards [hfst_ae] with p _
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventually_atTop.mpr ⟨⌊p.1 * 2^n⌋₊ + 1, fun N hN => ?_⟩
    simp only [Finset.sum_apply]
    symm
    calc (∑ k ∈ Finset.range N,
          Set.indicator ({t : Real | ⌊t * 2^n⌋₊ = k} ×ˢ Set.univ)
            (fun q => Y (Real.toNNReal (((k : Real) + 1) / 2^n)) q.2) p)
        = Set.indicator ({t : Real | ⌊t * 2^n⌋₊ = ⌊p.1 * 2^n⌋₊} ×ˢ Set.univ)
            (fun q => Y (Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) q.2) p := by
          apply Finset.sum_eq_single
          · intro k _ hk
            apply Set.indicator_of_notMem
            intro hmem
            exact hk (Set.mem_prod.mp hmem).1.symm
          · intro hnotmem
            exact absurd (Finset.mem_range.mpr (by omega)) hnotmem
    _ = Y (Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) p.2 := by
          apply Set.indicator_of_mem
          exact Set.mem_prod.mpr ⟨rfl, Set.mem_univ _⟩
  have hYn : ∀ n : ℕ, AEMeasurable
      (fun p : Real × Omega =>
        Y (Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) p.2)
      ((volume.restrict (Set.Ici (0 : Real))).prod P) :=
    fun n => aemeasurable_of_tendsto_metrizable_ae' (hT n) (hlimT n)
  -- the approximants converge a.e. by right-continuity of cadlag paths
  have hlimY : ∀ᵐ p ∂((volume.restrict (Set.Ici (0 : Real))).prod P),
      Tendsto (fun n =>
        Y (Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) p.2) atTop
        (nhds (Y (Real.toNNReal p.1) p.2)) := by
    filter_upwards [hfst_ae, hsnd_ae] with p hp0 hcad
    have hu_nhds : Tendsto
        (fun n => Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) atTop
        (nhds (Real.toNNReal p.1)) :=
      (continuous_real_toNNReal.tendsto p.1).comp (hs_tendsto p.1 hp0)
    have hmem : ∀ n, Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n) ∈
        Set.Ici (Real.toNNReal p.1) := by
      intro n
      rw [Set.mem_Ici, ← NNReal.coe_le_coe,
        Real.coe_toNNReal _ (le_trans hp0 (le_of_lt (hs_gt n p.1))),
        Real.coe_toNNReal _ hp0]
      exact le_of_lt (hs_gt n p.1)
    have hu_within : Tendsto
        (fun n => Real.toNNReal ((⌊p.1 * 2^n⌋₊ + 1 : Real) / 2^n)) atTop
        (nhdsWithin (Real.toNNReal p.1) (Set.Ici (Real.toNNReal p.1))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu_nhds
        (Filter.Eventually.of_forall hmem)
    have hcad' : ∀ (t : NNReal), IsCadlagAt (fun s => Y s p.2) t := hcad
    have hcont : Tendsto (fun s => Y s p.2)
        (nhdsWithin (Real.toNNReal p.1) (Set.Ici (Real.toNNReal p.1)))
        (nhds (Y (Real.toNNReal p.1) p.2)) :=
      (hcad' (Real.toNNReal p.1)).left
    exact hcont.comp hu_within
  have hY : AEMeasurable (fun p : Real × Omega => Y (Real.toNNReal p.1) p.2)
      ((volume.restrict (Set.Ici (0 : Real))).prod P) :=
    aemeasurable_of_tendsto_metrizable_ae' hYn hlimY
  -- the alive set is jointly measurable, and the integrand is AEMeasurable
  have hAlive : MeasurableSet
      {p : Real × Omega | (Real.toNNReal p.1 : WithTop NNReal) < death p.2} := by
    apply measurableSet_lt
      (f := fun p : Real × Omega => (Real.toNNReal p.1 : WithTop NNReal))
      (g := fun p : Real × Omega => death p.2)
    · exact (measurable_real_toNNReal.comp measurable_fst).withTop_coe
    · exact hdeath.comp measurable_snd
  have hG : AEMeasurable
      (({p : Real × Omega | (Real.toNNReal p.1 : WithTop NNReal) < death p.2}).indicator
        (fun p => f (Y (Real.toNNReal p.1) p.2)))
      ((volume.restrict (Set.Ici (0 : Real))).prod P) :=
    AEMeasurable.indicator (hf.comp_aemeasurable hY) hAlive
  have hAlive_t : ∀ t : Real, MeasurableSet
      {ω : Omega | (Real.toNNReal t : WithTop NNReal) < death ω} :=
    fun t => hdeath measurableSet_Ioi
  have hEq : (fun t : Real =>
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          f (Y (Real.toNNReal t) omega) ∂P)
      = (fun t : Real => ∫⁻ ω,
          (({p : Real × Omega | (Real.toNNReal p.1 : WithTop NNReal) < death p.2}).indicator
            (fun p => f (Y (Real.toNNReal p.1) p.2))) (t, ω) ∂P) := by
    funext t
    rw [← lintegral_indicator (hAlive_t t)]
    congr 1
  rw [hEq]
  exact hG.lintegral_prod_right'
