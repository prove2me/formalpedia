-- Prove2me | solution 1 for GlobalTheory.Retract.exists_affine_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:08.761681+00:00
-- url     : https://prove2.me/submissions/89520132-deea-4088-958d-18285995f797

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_apply_apply

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
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ O ∧
      U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U := by
  obtain ⟨U₀, hU₀, hxU₀, hU₀O⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hix : i x ∈ r ⁻¹ᵁ U₀ := by
    change r (i x) ∈ U₀
    rwa [apply_apply hir]
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₀⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hix
  obtain ⟨a, ha, hxa⟩ := IsAffineOpen.exists_basicOpen_le hU₀ (V := i ⁻¹ᵁ V₀) ⟨x, hxV₀⟩ hxU₀
  have hV : Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a) = V₀ ⊓ r ⁻¹ᵁ X.basicOpen a := by
    simp [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]
  refine ⟨X.basicOpen a, Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a), IsAffineOpen.basicOpen hU₀ a,
    IsAffineOpen.basicOpen hV₀ _, hxa, (X.basicOpen_le a).trans hU₀O, ?_, ?_⟩
  · rw [hV]
    intro z hz
    refine ⟨ha hz, ?_⟩
    change r (i z) ∈ X.basicOpen a
    rwa [apply_apply hir]
  · rw [hV]
    exact inf_le_right
end GlobalTheory.Retract
