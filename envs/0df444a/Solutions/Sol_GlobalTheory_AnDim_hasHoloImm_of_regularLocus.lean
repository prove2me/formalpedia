-- Prove2me | solution 1 for GlobalTheory.AnDim.hasHoloImm_of_regularLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:03.007564+00:00
-- url     : https://prove2.me/submissions/fd80f368-e4ed-4a0f-b6dd-bb38fd2152c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
import Theorems.Thm_GlobalTheory_AnDim_injective_fderiv_of_comp
import Theorems.Thm_GlobalTheory_AnDim_padL_apply_of_le
import Theorems.Thm_GlobalTheory_AnDim_padL_injective
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.AnDim
theorem _root_.solution {A : FinHolAtlas d X} {T : Set X} {n k : ℕ} (hk : k ≤ n)
    (h : (regularLocus A T n).Nonempty) : HasHoloImm A T k := by
  obtain ⟨x, hxT, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := h
  obtain ⟨j, hj⟩ := A.cover x
  have hp : ∀ i : Fin d, n ≤ (i : ℕ) → ψ x i = 0 := (hT.le ⟨hxT, hx⟩).2
  set a : (Fin k → ℂ) → Fin d → ℂ := fun z => ψ x + padL k d z with ha
  have han : ∀ z, AnalyticAt ℂ a z := fun z => analyticAt_const.add ((padL k d).analyticAt z)
  have hac : Continuous a := continuous_const.add (padL k d).continuous
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.symm.isOpen_inter_preimage (A.chart j).open_source
  have hF : ∀ z ∈ a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source),
      AnalyticAt ℂ (A.chart j ∘ ψ.symm ∘ a) z := fun z hz =>
    ((hψ j).2 (a z) hz).comp (han z)
  refine ⟨a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source), ψ.symm ∘ a, j, hV.preimage hac,
    ⟨0, ?_⟩, fun z hz => ⟨?_, hz.2⟩, hF, fun z hz => ?_⟩
  · simp [ha, ψ.map_source hx, ψ.left_inv hx, hj]
  · refine (hT.ge ⟨ψ.map_target hz.1, fun i hi => ?_⟩).1
    rw [ψ.right_inv hz.1]
    simp [ha, hp i hi, padL_apply_of_le z (hk.trans hi)]
  · refine injective_fderiv_of_comp (G := ψ ∘ (A.chart j).symm) (H := a) (hF z hz).differentiableAt
      ((hψ j).1 _ ⟨(A.chart j).map_source hz.2, ?_⟩).differentiableAt ?_ ?_
    · simpa [(A.chart j).left_inv hz.2] using ψ.map_target hz.1
    · filter_upwards [(hV.preimage hac).mem_nhds hz] with w hw
      simp [(A.chart j).left_inv hw.2, ψ.right_inv hw.1]
    · have : fderiv ℂ a z = padL k d := ((padL k d).hasFDerivAt.const_add (ψ x)).fderiv
      rw [this]
      exact padL_injective (hk.trans hnd)
end GlobalTheory.AnDim
