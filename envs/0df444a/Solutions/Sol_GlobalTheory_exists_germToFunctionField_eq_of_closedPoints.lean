-- Prove2me | solution 1 for GlobalTheory.exists_germToFunctionField_eq_of_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:26:02.814551+00:00
-- url     : https://prove2.me/submissions/fa2b3ea2-79c3-4f3e-80e8-09222c2faeeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_mem_range_stalk
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{0}} [IsIntegral Z]
    [JacobsonSpace Z] (W : Z.Opens) [Nonempty W] (t : Z.functionField)
    (h : ∀ x ∈ W, IsClosed ({x} : Set Z) →
      t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) :
    ∃ s : Γ(Z, W), Z.germToFunctionField W s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally W t fun x hx => ?_
  obtain ⟨z, ⟨hzx, hzW⟩, hz⟩ := nonempty_inter_closedPoints (Z := closure {x} ∩ (W : Set Z))
    ⟨x, subset_closure rfl, hx⟩ (isClosed_closure.isLocallyClosed.inter W.isOpen.isLocallyClosed)
  obtain ⟨V, hV, s, hzV, hVW, hs⟩ := exists_germToFunctionField_eq_of_mem_range_stalk
    (h z hzW hz) hzW
  exact ⟨V, hV, s, (specializes_iff_mem_closure.mpr hzx).mem_open V.isOpen hzV, hVW, hs⟩
end GlobalTheory
