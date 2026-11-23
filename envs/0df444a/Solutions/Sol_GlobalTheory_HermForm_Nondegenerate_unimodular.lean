-- Prove2me | solution 1 for GlobalTheory.HermForm.Nondegenerate.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:01.129805+00:00
-- url     : https://prove2.me/submissions/6e39dcb4-3526-42c6-a8e4-1f16a7ebe910

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}
namespace GlobalTheory.HermForm
namespace Nondegenerate
theorem _root_.solution (H : h.Nondegenerate) : h.Unimodular := by
  let b := Module.finBasis K V
  let σ : V ≃ₗ⋆[K] V :=
    (b.equivFun.trans (starLinearEquiv K (A := Fin (Module.finrank K V) → K))).trans
      b.equivFun.symm
  let φ : V →ₗ[K] Module.Dual K V := h.toDual.comp σ.toLinearMap
  have hinj : Function.Injective φ := (h.nondegenerate_iff_injective.1 H).comp σ.injective
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  exact ⟨h.nondegenerate_iff_injective.1 H, Function.Surjective.of_comp (g := σ) hsurj⟩
end Nondegenerate
end GlobalTheory.HermForm
