-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.actualHeightStrictLeftFromPathMargin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:17:56.76921+00:00
-- url     : https://prove2.me/submissions/f8d2b802-e2e1-484a-9578-736547ab77a7

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_strict_exit_clocks_aemeasurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_event_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_no_drawdown_null_measurable_of_effective_event
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

private lemma tauPlus_shift {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x d : ℝ) (ω : Ω) :
    tauPlus (shifted X x) (x + d) ω = tauPlus X d ω := by
  unfold tauPlus shifted; congr 1; ext t; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by simpa using hlt⟩

private theorem discountedAt_measurable (q : ℝ) : Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  have heq : (fun t : ℝ≥0∞ => discountedAt q t) =
      fun t => if t = ⊤ then 0 else Real.exp (-q * t.toReal) := by
    funext t; induction t using WithTop.recTopCoe with
    | top => exact (if_pos rfl).symm
    | coe s => simp [discountedAt]
  rw [heq]; exact Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))

private theorem discountedAt_norm_le_one (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0∞) : ‖discountedAt q t‖ ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s => simpa [discountedAt, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg))

private theorem noDrawdown_mono {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) {a r s : ℝ} (hrs : r ≤ s) {ω : Ω} (h : NoDrawdownBeforeUpcrossing X a r ω) : NoDrawdownBeforeUpcrossing X a s ω := by
  intro t ht; exact (h t ht).trans_le hrs

private theorem solution_core
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q)
    (hmargin : ∀ y : ℝ, 0 < y → ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
      NoDrawdownBeforeUpcrossing D.X 1 y ω →
      ∃ h : ℝ, 0 < h ∧ h < y ∧ NoDrawdownBeforeUpcrossing D.X 1 h ω) :
    ∀ y : ℝ, 0 < y → Tendsto
      (fun h : ℝ => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (nhdsWithin y (Set.Iio y))
      (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  classical
  intro y hy
  let c : ℝ := Real.exp (Phi ψ q * 1)
  let g : Ω → ℝ := fun ω => c * discountedAt q (tauPlus D.X (1 : ℝ) ω)
  let S : ℝ → Set Ω := fun r => {ω | NoDrawdownBeforeUpcrossing D.X (1 : ℝ) r ω}
  let l : Filter ℝ := nhdsWithin y (Iio y)
  obtain ⟨F, A, hAX, _⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnhds_pos : ∀ᶠ r : ℝ in 𝓝 y, 0 < r := Ioi_mem_nhds hy; have hpos : ∀ᶠ r : ℝ in l, 0 < r := by simpa [l] using hnhds_pos.filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r : ℝ in 𝓝[<] y, r < y := self_mem_nhdsWithin
  have hClock : AEMeasurable (fun ω => (tauPlus D.X (1 : ℝ) ω : ℝ≥0∞)) P := by
    have hEq : (fun ω => (tauPlus D.X (1 : ℝ) ω : ℝ≥0∞)) = fun ω => (tauPlus (shifted D.X 0) (0 + (1 : ℝ)) ω : ℝ≥0∞) := by funext ω; exact (tauPlus_shift D.X 0 (1 : ℝ) ω).symm
    rw [hEq]; simpa using (source_result81_strict_exit_clocks_aemeasurable Ω P D 0 (1 : ℝ)).1
  have hdisc : AEMeasurable (fun ω => discountedAt q (tauPlus D.X (1 : ℝ) ω)) P := (discountedAt_measurable q).comp_aemeasurable hClock
  have hg : AEStronglyMeasurable g P := by simpa [g] using (hdisc.const_mul c).aestronglyMeasurable
  have hNull (r : ℝ) (hr : 0 < r) : NullMeasurableSet (S r) P := by
    have hE : MeasurableSet {ω : Ω | twoSidedExitUpTime A (1 : ℝ) ω < ⊤ ∧ NoDrawdownBeforeUpcrossing A.X (1 : ℝ) r ω} := actual_height_effective_event_measurable A (1 : ℝ) r zero_lt_one hr
    simpa [S] using actual_height_no_drawdown_null_measurable_of_effective_event A D hAX (1 : ℝ) r zero_lt_one hr hE
  have hMeasEv : ∀ᶠ r : ℝ in l, AEStronglyMeasurable ((S r).indicator g) P := by filter_upwards [hpos] with r hr; exact (aestronglyMeasurable_indicator_iff₀ (hNull r hr)).2 hg.restrict
  have hBound : ∀ᶠ r : ℝ in l, ∀ᵐ ω ∂P, ‖(S r).indicator g ω‖ ≤ ‖c‖ := by
    refine Eventually.of_forall fun r => Eventually.of_forall fun ω => ?_
    by_cases hrS : ω ∈ S r
    · rw [Set.indicator_of_mem hrS, norm_mul]; simpa using mul_le_mul_of_nonneg_left (discountedAt_norm_le_one q hq _) (norm_nonneg c)
    · simp [Set.indicator_of_notMem hrS, norm_nonneg c]
  have hmono (r s : ℝ) (hrs : r ≤ s) {ω : Ω} (hrS : ω ∈ S r) : ω ∈ S s := by simpa [S] using noDrawdown_mono D.X hrs (by simpa [S] using hrS)
  have hTend : ∀ᵐ ω ∂P, Tendsto (fun r => (S r).indicator g ω) l (nhds ((S y).indicator g ω)) := by
    filter_upwards [hmargin y hy] with ω hmar
    by_cases hgω : g ω = 0
    · have hz : ∀ r : ℝ, (S r).indicator g ω = 0 := by
        intro r; by_cases hs : ω ∈ S r
        · simp [Set.indicator_of_mem hs, hgω]
        · simp [Set.indicator_of_notMem hs, hgω]
      have he : (fun r : ℝ => (S r).indicator g ω) =ᶠ[l] (fun _ : ℝ => 0) := Eventually.of_forall hz
      simpa [hz y] using (tendsto_const_nhds.congr' he.symm : Tendsto (fun r : ℝ => (S r).indicator g ω) l (nhds (0 : ℝ)))
    · have hdisc_ne : discountedAt q (tauPlus D.X (1 : ℝ) ω) ≠ 0 := by intro hd; apply hgω; simp [g, hd]
      have hmem : ∀ᶠ r : ℝ in l, (ω ∈ S r) ↔ (ω ∈ S y) := by
        by_cases hyS : ω ∈ S y
        · obtain ⟨h0, _, hh0y, hh0S⟩ := hmar hdisc_ne (by simpa [S] using hyS)
          have hge : ∀ᶠ r : ℝ in 𝓝[<] y, h0 < r := Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hh0y)
          filter_upwards [hge, hlt] with r hgr hry
          constructor
          · intro hrS; exact hmono r y (le_of_lt hry) hrS
          · intro _; exact hmono h0 r (le_of_lt hgr) (by simpa [S] using hh0S)
        · filter_upwards [hlt] with r hry
          constructor
          · intro hrS; exact False.elim (hyS (hmono r y (le_of_lt hry) hrS))
          · intro hyS'; exact False.elim (hyS hyS')
      have he : (fun r : ℝ => (S r).indicator g ω) =ᶠ[l] (fun _ : ℝ => (S y).indicator g ω) := by
        filter_upwards [hmem] with r hr
        by_cases hs : ω ∈ S y
        · simp [Set.indicator_of_mem (hr.mpr hs), Set.indicator_of_mem hs]
        · simp [Set.indicator_of_notMem (fun h => hs (hr.mp h)), Set.indicator_of_notMem hs]
      exact tendsto_const_nhds.congr' he.symm
  have hDCT : Tendsto (fun r : ℝ => ∫ ω, (S r).indicator g ω ∂P) l (nhds (∫ ω, (S y).indicator g ω ∂P)) := by
    exact tendsto_integral_filter_of_dominated_convergence (μ := P) (l := l) (F := fun r ω => (S r).indicator g ω) (f := fun ω => (S y).indicator g ω) (bound := fun _ : Ω => ‖c‖) hMeasEv hBound (MeasureTheory.integrable_const (μ := P) ‖c‖) hTend
  have hIntEv : (fun r : ℝ => ∫ ω, (S r).indicator g ω ∂P) =ᶠ[l] (fun r : ℝ => ∫ ω in S r, g ω ∂P) := by filter_upwards [hpos] with r hr; exact integral_indicator₀ (μ := P) (s := S r) (hNull r hr) (f := g)
  have hLimEq : (∫ ω, (S y).indicator g ω ∂P) = ∫ ω in S y, g ω ∂P := integral_indicator₀ (μ := P) (s := S y) (hNull y hy) (f := g)
  have hFinal := hDCT.congr' hIntEv
  rw [hLimEq] at hFinal
  simpa [c, g, S, l] using hFinal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q)
    (hmargin : ∀ y : ℝ, 0 < y → ∀ᵐ ω ∂P, discountedAt q (tauPlus D.X 1 ω) ≠ 0 →
      NoDrawdownBeforeUpcrossing D.X 1 y ω →
      ∃ h : ℝ, 0 < h ∧ h < y ∧ NoDrawdownBeforeUpcrossing D.X 1 h ω) :
    ∀ y : ℝ, 0 < y → Tendsto
      (fun h : ℝ => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) (nhdsWithin y (Set.Iio y))
      (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  exact solution_core P D ψ W hψ hW q hq hmargin
