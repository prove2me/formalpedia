-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.actualHeightRestrictedIntegralExhausts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:07:58.682794+00:00
-- url     : https://prove2.me/submissions/3904ebf0-1e9a-4aac-95ef-15bb6cbb87cd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_stageB_tauPlus_coe_eq
import Theorems.Thm_stageB_tauPlus_lt_iff
import Theorems.Thm_stageB_reflect_eq
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal

private theorem stageB_height_family {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕) (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) :
    let U : ℝ → Set Ω := fun h => {ω | NoDrawdownBeforeUpcrossing D.X 1 (max h 1) ω}
    (∀ h, NullMeasurableSet (U h) P) ∧ Monotone U := by
  classical
  dsimp only
  constructor
  · intro h
    have hp : 0 < max h 1 := lt_of_lt_of_le zero_lt_one (le_max_right h 1)
    have hE := Kyprianou.Ch08.StageB.actual_height_effective_event_measurable A 1 (max h 1) zero_lt_one hp
    simpa using (Kyprianou.Ch08.StageB.actual_height_no_drawdown_null_measurable_of_effective_event
      A D hAX 1 (max h 1) zero_lt_one hp hE)
  · intro h h' hh' ω hω
    intro t ht
    exact lt_of_lt_of_le (hω t ht) (max_le_max hh' le_rfl)

private theorem stageB_height_exhausts {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : SpectrallyNegativeLevy P 𝓕) (D : SpectrallyNegativeModel Ω P)
    (hAX : ∀ᵐ ω ∂P, ∀ t, A.X t ω = D.X t ω) (q c : ℝ) :
    ∀ᵐ ω ∂P, ω ∉ (⋃ h : ℝ, {ω | NoDrawdownBeforeUpcrossing D.X 1 (max h 1) ω}) →
      c * discountedAt q (tauPlus D.X 1 ω) = 0 := by
  filter_upwards [hAX] with ω hω
  intro hnot
  by_cases htop : tauPlus D.X 1 ω = ⊤
  · simp [htop, discountedAt]
  · exfalso
    have htAD : tauPlus A.X 1 ω = tauPlus D.X 1 ω := by simp [tauPlus, hω]
    have htopA : tauPlus A.X 1 ω ≠ ⊤ := by simpa [htAD] using htop
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp htopA
    obtain ⟨v, _, hvmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
      (⟨0, ⟨le_rfl, bot_le⟩⟩ : (Icc (0 : ℝ≥0) u).Nonempty) isCompact_Icc (reflectedSup_upperSemicontinuousOn_Icc A ω u)
    apply hnot
    let H : ℝ := |reflectedSup A v ω| + 1
    refine mem_iUnion.mpr ⟨H, ?_⟩
    simp only [NoDrawdownBeforeUpcrossing]
    intro t ht
    have htA : (t : WithTop ℝ≥0) < tauPlus A.X 1 ω := by simpa [htAD] using ht
    have htENN : (t : ℝ≥0∞) < (tauPlus A.X 1 ω : ℝ≥0∞) := by simpa [stageB_tauPlus_coe_eq] using (stageB_tauPlus_lt_iff A 1 ω (t := t)).1 htA
    have htu : t < u := ENNReal.coe_lt_coe.mp (by simpa [← hu] using htENN)
    have hlt : reflectedSup A t ω < H := by
      dsimp [H]
      exact lt_of_le_of_lt (hvmax ⟨bot_le, le_of_lt htu⟩)
        (lt_of_le_of_lt (le_abs_self _) (lt_add_one _))
    have hltA : reflectAtSup A.X 0 t ω < max H 1 :=
      lt_of_lt_of_le (by simpa [stageB_reflect_eq A t ω] using hlt) (le_max_left H 1)
    simpa [reflectAtSup, Kyprianou.Ch08.runningSup, hω] using hltA

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto
      (fun h : ℝ => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds (∫ ω, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  classical
  obtain ⟨_, A, hAX, hAψ⟩ := Kyprianou.Ch08.StageB.source_result81_filtered_avram_model Ω P D ψ hψ
  have hs := ((hW q hq).1).2.1
  have hroot : A.ψ (Phi ψ q) = q := (hAψ (Phi ψ q) hs.1).trans hs.2
  obtain ⟨hbase, _⟩ := Kyprianou.Ch08.StageB.filtered_avram_upcrossing_discount_real_cap
    A q hq (Phi ψ q) hs.1 hroot
  let U : ℝ → Set Ω := fun h => {ω | NoDrawdownBeforeUpcrossing D.X 1 (max h 1) ω}
  let f : Ω → ℝ := fun ω => Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω)
  let g : Ω → ℝ := fun ω => Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus A.X 1 ω)
  have hgint : Integrable g P := by simpa [g] using hbase.const_mul (Real.exp (Phi ψ q * 1))
  have hfg : f =ᵐ[P] g := hAX.mono (fun ω hω => by simp [f, g, tauPlus, hω])
  have hfint : Integrable f P := hgint.congr hfg.symm
  have hU := stageB_height_family A D hAX
  have hUnull (h : ℝ) : NullMeasurableSet (U h) P := by simpa [U] using hU.1 h
  have hUmono : Monotone U := by simpa [U] using hU.2
  have hzero : ∀ᵐ ω ∂P, ω ∉ (⋃ h : ℝ, U h) → f ω = 0 := by
    simpa [f, U] using stageB_height_exhausts A D hAX q (Real.exp (Phi ψ q * 1))
  have hconv : Tendsto (fun h : ℝ => ∫ ω in U h, f ω ∂P) atTop
      (nhds (∫ ω in (⋃ h : ℝ, U h), f ω ∂P)) :=
    MeasureTheory.tendsto_setIntegral_of_monotone₀ hUnull hUmono hfint.integrableOn
  have hfull : (∫ ω in (⋃ h : ℝ, U h), f ω ∂P) = ∫ ω, f ω ∂P := MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero hzero
  have hUconv : Tendsto (fun h : ℝ => ∫ ω in U h, f ω ∂P) atTop (nhds (∫ ω, f ω ∂P)) := by
    simpa [hfull] using hconv
  have hfun : (fun h : ℝ => ∫ ω in U h, f ω ∂P) =ᶠ[atTop]
      (fun h : ℝ => ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, f ω ∂P) := by
    refine eventually_atTop.2 ⟨1, ?_⟩
    intro h hh
    simp [U, max_eq_left hh]
  simpa only [f] using hUconv.congr' hfun
