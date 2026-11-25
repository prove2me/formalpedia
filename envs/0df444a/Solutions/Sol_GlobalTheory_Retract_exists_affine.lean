-- Prove2me | solution 1 for GlobalTheory.Retract.exists_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:47.936615+00:00
-- url     : https://prove2.me/submissions/51c6cf16-f764-4cfd-ab15-f0d775a37fee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_exists_affine_le

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
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
namespace GlobalTheory.Retract
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens) (W : S.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen W ∧ x ∈ U ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U ∧ U ≤ f ⁻¹ᵁ W ∧ V ≤ g ⁻¹ᵁ W := by
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨U, V, hU, hV, hxU, hUW, hUV, hVU⟩ := exists_affine_le hir x (f ⁻¹ᵁ W) hxW
  refine ⟨U, V, W, hU, hV, hW, hxU, hUV, hVU, hUW, ?_⟩
  subst hr
  intro y hy
  exact hUW (hVU hy)
end GlobalTheory.Retract
