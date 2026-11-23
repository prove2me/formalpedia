-- Prove2me | solution 1 for GlobalTheory.Retract.isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:08.766304+00:00
-- url     : https://prove2.me/submissions/35292154-fc1a-4ff0-9c02-0d5d63006017

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_apply_apply
import Theorems.Thm_GlobalTheory_Retract_appLE_comp_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y : Scheme.{u}} {i : X ⟶ Y} {r : Y ⟶ X} (hir : i ≫ r = 𝟙 X)
include hir
namespace GlobalTheory.Retract
theorem _root_.solution [IsReduced Y] : IsReduced X := by
  refine ⟨fun U ↦ ?_⟩
  have hUV : U ≤ i ⁻¹ᵁ r ⁻¹ᵁ U := fun x hx ↦ by
    change r (i x) ∈ U
    rwa [apply_apply hir]
  refine isReduced_of_injective (r.appLE U (r ⁻¹ᵁ U) le_rfl).hom
    (Function.LeftInverse.injective (g := (i.appLE (r ⁻¹ᵁ U) U hUV).hom) fun a ↦ ?_)
  exact congr($(appLE_comp_appLE hir hUV le_rfl).hom a)
end GlobalTheory.Retract
