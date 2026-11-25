-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_mem_range_finiteEmbed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:05:10.962797+00:00
-- url     : https://prove2.me/submissions/ce5d69ca-ad68-4f1b-baa5-372aa74aa35e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_finiteEmbed_tprod
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_extend_restrict

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
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ξ : ∀ v, V v} {t : ⨂[ℂ] v, V v}
    (ht : t ∈ restrictedTensor ξ) : ∃ T₀ : Finset ι, ∀ T, T₀ ⊆ T →
      t ∈ LinearMap.range (finiteEmbed ξ T) := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, rfl⟩ := ht
    refine ⟨(isRestricted_iff_finite.1 hx).toFinset, fun T hT => ⟨tprod ℂ fun v => x v, ?_⟩⟩
    rw [finiteEmbed_tprod, extend_restrict]
    intro v hv
    by_contra hxv
    exact hv (hT (by simpa using hxv))
  | zero => exact ⟨∅, fun T _ => Submodule.zero_mem _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    exact ⟨A ∪ B, fun T hT => Submodule.add_mem _ (hA T (Finset.union_subset_left hT))
      (hB T (Finset.union_subset_right hT))⟩
  | smul c a _ ha =>
    obtain ⟨A, hA⟩ := ha
    exact ⟨A, fun T hT => Submodule.smul_mem _ c (hA T hT)⟩
end GroundTheory.Automorphic.RestrictedTensor
