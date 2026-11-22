-- Prove2me | solution 1 for NemytskiiLebesgue.convergesTo_of_tendsTo_of_growth_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:10.134929+00:00
-- url     : https://prove2.me/submissions/deb6e962-a2de-4c39-ac97-8000e146ed4e

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p ≠ ⊤)
    {f : ℕ → Ω → F} (f_meas : ∀ n : ℕ, AEStronglyMeasurable (f n) μ)
    {g : Ω → F} (hgp : MemLp g p μ)
    {l : Ω → ℝ} (hlp : MemLp l p μ)
    (hfl : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖f n ω‖ ≤ l ω)
    (hfg : ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    f.NemytskiiConvergesTo g p μ := by
  apply tendsto_Lp_of_tendsto_ae h1p hp f_meas hgp _ _ hfg
  · intro ε hε
    obtain ⟨δ, hδ, hbound⟩ :=
      (unifIntegrable_const (ι := ℕ) h1p hp hlp) hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    apply le_trans (eLpNorm_mono_ae _) (hbound n s hs hμs)
    filter_upwards [hfl n] with ω hω
    by_cases hωs : ω ∈ s
    · rw [Set.indicator_of_mem hωs, Set.indicator_of_mem hωs]
      exact hω.trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hωs, Set.indicator_of_notMem hωs]
      simp
  · intro ε hε
    obtain ⟨s, hs, hμs, hbound⟩ :=
      (unifTight_const (ι := ℕ) hp hlp).exists_measurableSet_indicator (ε := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    refine ⟨s, hμs.ne, fun n => ?_⟩
    apply le_trans (eLpNorm_mono_ae _) (hbound n)
    filter_upwards [hfl n] with ω hω
    by_cases hωs : ω ∈ sᶜ
    · rw [Set.indicator_of_mem hωs, Set.indicator_of_mem hωs]
      exact hω.trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hωs, Set.indicator_of_notMem hωs]
      simp
end NemytskiiLebesgue
