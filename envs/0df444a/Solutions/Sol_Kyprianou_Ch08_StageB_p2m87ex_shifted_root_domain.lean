-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87ex_shifted_root_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:18:14.464637+00:00
-- url     : https://prove2.me/submissions/c1a30b81-8897-451e-b0fa-cd748e6a4a98

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_levy_root_domain
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_laplace_convex
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_convex_root_bridge
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m89_psi_differentiable_pos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (c q : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    IsScaleTransformDomainBridge (shiftedExponent ψ c) q := by
  obtain ⟨F, X, hpath, hexp⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnegative : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => X.X t ω)) := by
    intro h
    apply D.excludesNegativeSubordinator
    filter_upwards [hpath, h] with ω heq ha
    intro s t hst
    simpa only [heq] using ha hst
  have hdom := (source_result81_levy_root_domain X hnegative).2
  have hcv := source_result81_law_laplace_convex Ω P D ψ hψ
  let f := shiftedExponent ψ c
  have hf0 : f 0 = 0 := by simp [f, shiftedExponent]
  have hfc : ConvexOn ℝ (Ici (0 : ℝ)) f := by
    refine ⟨convex_Ici _, ?_⟩
    intro u hu v hv a b ha hb hab
    have hh := hcv.2 (show u+c ∈ Ici 0 from add_nonneg hu hc)
      (show v+c ∈ Ici 0 from add_nonneg hv hc) ha hb hab
    change ψ (a*(u+c)+b*(v+c)) ≤ a*ψ (u+c)+b*ψ (v+c) at hh
    change ψ (a*u+b*v+c)-ψ c ≤ a*(ψ (u+c)-ψ c)+b*(ψ (v+c)-ψ c)
    have he : a*(u+c)+b*(v+c)=a*u+b*v+c := by nlinarith
    rw [he] at hh
    nlinarith [congrArg (fun z : ℝ => z*ψ c) hab]
  have hcont := ConvexOn.continuousOn isOpen_Ioi (hfc.subset Ioi_subset_Ici_self (convex_Ioi _))
  have hlarge (r : ℝ) : ∃ b : ℝ, 0 < b ∧ r < f b := by
    let L := max (r + ψ c) 0
    have hL := hdom L (le_max_right _ _)
    let B := max c (Phi X.ψ L) + 1
    have hb : c < B := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
    have hB : 0 ≤ B := hc.trans hb.le
    have hgt : L < X.ψ B := (hL.2 B hB).mp (lt_of_le_of_lt (le_max_right _ _) (lt_add_one _))
    refine ⟨B-c, sub_pos.mpr hb, ?_⟩
    change r < ψ (B-c+c) - ψ c
    rw [sub_add_cancel, ← hexp B hB]
    linarith [le_max_left (r+ψ c) 0]
  exact source_result81_convex_root_bridge f hf0 hfc hcont hlarge q hq
