-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.exists_nhds_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:38.000091+00:00
-- url     : https://prove2.me/submissions/e016947d-0bdb-4be3-bbb7-3d5a464d7259

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution (φ : G → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ)
    {δ : ℝ} (hδ : 0 < δ) : ∃ V ∈ 𝓝 (0 : G), ∀ a b, a - b ∈ V → |φ a - φ b| < δ := by
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have huc : UniformContinuous φ := hs.uniformContinuous_of_continuous hc
  have hmem := huc (Metric.dist_mem_uniformity hδ)
  rw [uniformity_eq_comap_nhds_zero G] at hmem
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.1 hmem
  refine ⟨V, hV, fun a b hab => ?_⟩
  have h1 : (b, a) ∈ (fun p : G × G => p.2 - p.1) ⁻¹' V := hab
  have h2 := hsub h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Real.dist_eq] at h2
  rwa [abs_sub_comm]
end GlobalTheory.CompanionTheory.RiemannCore
