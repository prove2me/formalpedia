-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_normalized_scale_at_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:42:20.050543+00:00
-- url     : https://prove2.me/submissions/20578bff-9251-4404-a1fd-13587eb2704e

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_tilted_descending_potential
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_from_tilted_potential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (q : ℝ)
    (hq : 0 ≤ q) :
    ∃ w : ℝ → ℝ, IsQScale ψ q w := by
  obtain ⟨F, A, hpaths, hexp⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnegative : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro h
    apply D.excludesNegativeSubordinator
    filter_upwards [hpaths, h] with ω heq ha
    intro s t hst
    simpa only [heq] using ha hst
  obtain ⟨hr, ν, hsupp, hfin, hatom, hlap⟩ :=
    source_result81_tilted_descending_potential A hnegative q hq
  obtain ⟨W, hW⟩ := source_result81_scale_from_tilted_potential A.ψ q hr
    ν hsupp hfin hatom hlap
  have hsets : RightRootSet ψ q = RightRootSet A.ψ q := by
    ext β
    change (0 ≤ β ∧ ψ β = q) ↔ (0 ≤ β ∧ A.ψ β = q)
    exact ⟨fun ⟨hn, he⟩ => ⟨hn, (hexp β hn).trans he⟩,
      fun ⟨hn, he⟩ => ⟨hn, (hexp β hn).symm.trans he⟩⟩
  have hPhi : Phi ψ q = Phi A.ψ q := congrArg sSup hsets
  obtain ⟨⟨hqn, hmem, hmax⟩, hzero, hn, hcont, hmono, hl⟩ := hW
  refine ⟨W, ⟨hqn, ?_, ?_⟩, hzero, hn, hcont, hmono, ?_⟩
  · rw [hPhi, hsets]
    exact hmem
  · rw [hPhi, hsets]
    exact hmax
  · intro β hb hlt
    rw [← hexp β hb]
    exact hl β hb (hPhi ▸ hlt)
