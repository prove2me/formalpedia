-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.genQuotMk_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:41.446821+00:00
-- url     : https://prove2.me/submissions/4f7c8b6e-5495-41d1-8a07-2f636b06f733

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem


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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
variable {N}
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
include hNK
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution : Function.Injective (genQuotMk hσ hKc hKo N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker, genQuotMk, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hn
  have := hn 1
  rw [map_one, Module.End.one_apply] at this
  have h2 : (fixedProj σ hσ hKc hKo (n : V) : V) = n := fixedProj_apply_of_mem hσ hKc hKo (hNK n.2)
  rw [Submodule.mem_bot]
  refine Subtype.ext ?_
  rw [← h2]
  simp only [Submodule.coe_inclusion] at this
  rw [this]
  rfl
end GroundTheory.Automorphic.RestrictedTensor
