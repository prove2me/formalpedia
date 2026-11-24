-- Prove2me | solution 1 for GlobalTheory.JR.exists_nhds_zero_add_invariant_of_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:54.113874+00:00
-- url     : https://prove2.me/submissions/a5d68f42-39d6-4e00-8b04-55c85928a562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportPartialFourierGLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR
namespace GlobalTheory.JR
theorem _root_.solution {X : Type} [UniformSpace X] [AddCommGroup X] [IsUniformAddGroup X] {f : X → ℂ}
    (hf : IsTest f) : ∃ U ∈ 𝓝 (0 : X), ∀ Y : X, ∀ u ∈ U, f (Y + u) = f Y := by
  obtain ⟨hlc, hcs⟩ := hf

  have hK : IsCompact (tsupport f) := hcs
  haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
  have hfin0 : (Set.range fun x : tsupport f => f x).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  have hT : (Set.range f).Finite := by
    refine (hfin0.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ tsupport f
    · exact Set.mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
    · exact Set.mem_insert_iff.2 (Or.inl (image_eq_zero_of_notMem_tsupport hx))

  set D : Set ℂ := (Set.image2 (fun a b => a - b) (Set.range f) (Set.range f)) \ {0} with hD
  have hDfin : D.Finite := (hT.image2 _ hT).diff
  have hDo : Dᶜ ∈ 𝓝 (0 : ℂ) := hDfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hDo
  have huc := hcs.uniformContinuous_of_continuous hlc.continuous (Metric.dist_mem_uniformity hε)
  rw [uniformity_eq_comap_nhds_zero X, Filter.mem_map, Filter.mem_comap] at huc
  obtain ⟨V, hV, hVs⟩ := huc
  refine ⟨V, hV, fun Y u hu => ?_⟩
  have h1 : ((Y, Y + u) : X × X) ∈ (fun p : X × X => p.2 - p.1) ⁻¹' V := by
    simpa [add_sub_cancel_left] using hu
  have h1' := hVs h1
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at h1'
  have h2 : f (Y + u) - f Y ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm, dist_comm]; exact h1'
  have h3 := hball h2
  by_contra hne
  exact h3 ⟨⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩, fun h => hne (sub_eq_zero.1 h)⟩
end GlobalTheory.JR
