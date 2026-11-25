-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.iwahoriFactorization_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:26.707198+00:00
-- url     : https://prove2.me/submissions/32741a8c-81ea-46ae-8af2-b9f5f965783f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {G : Type*} [Group G] {K Nbar M N : Subgroup G}
    (h : ∀ k ∈ K, ∃ z ∈ K ⊓ Nbar, ∃ y ∈ K ⊓ M, ∃ x ∈ K ⊓ N, k = z * y * x) :
    ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z := by
  intro k hk
  obtain ⟨z, hz, y, hy, x, hx, e⟩ := h k⁻¹ (K.inv_mem hk)
  refine ⟨x⁻¹, Subgroup.inv_mem _ hx, y⁻¹, Subgroup.inv_mem _ hy, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
  rw [← inv_inv k, e]
  group
end GroundTheory.Automorphic.Parabolic
