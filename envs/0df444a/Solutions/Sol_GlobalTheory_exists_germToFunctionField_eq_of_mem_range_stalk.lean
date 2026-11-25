-- Prove2me | solution 1 for GlobalTheory.exists_germToFunctionField_eq_of_mem_range_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:12.073736+00:00
-- url     : https://prove2.me/submissions/0cb46572-8621-4503-b3ab-c01a87a9c159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
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
    {t : Z.functionField} {x : Z}
    (h : t ∈ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) {W : Z.Opens} (hx : x ∈ W) :
    ∃ (V : Z.Opens) (_ : Nonempty V) (s : Γ(Z, V)),
      x ∈ V ∧ V ≤ W ∧ Z.germToFunctionField V s = t := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨V, hV, s, rfl⟩ := Z.presheaf.exists_germ_eq g
  haveI : Nonempty V := ⟨⟨x, hV⟩⟩
  haveI : Nonempty (V ⊓ W : Z.Opens) := ⟨⟨x, hV, hx⟩⟩
  refine ⟨V ⊓ W, inferInstance, Z.presheaf.map (homOfLE inf_le_left).op s, ⟨hV, hx⟩,
    inf_le_right, ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact Z.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ s
end GlobalTheory
