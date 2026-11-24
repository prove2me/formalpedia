-- Prove2me | solution 1 for GlobalTheory.SchemeHomsFromPoints.eq_zero_of_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:51.870018+00:00
-- url     : https://prove2.me/submissions/4cf0c0b0-1cba-47b9-9c49-2c8a816b6087

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Theorems.Thm_GlobalTheory_SchemeHomsFromPoints_dense_closedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    (W : X.Opens) (h : Γ(X, W))
    (H : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∀ e : ⊤ ≤ x ⁻¹ᵁ W, valAt x W e h = 0) : h = 0 := by
  rw [← basicOpen_eq_bot_iff]
  by_contra hne
  have hne' : ((X.basicOpen h : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hne (TopologicalSpace.Opens.ext h0)
  obtain ⟨x, hx, hxc⟩ := (dense_closedPoints p).inter_open_nonempty _ (X.basicOpen h).isOpen hne'
  have e : ⊤ ≤ (pointOfClosedPoint p x hxc) ⁻¹ᵁ W := by
    intro a _
    change pointOfClosedPoint p x hxc a ∈ W
    exact (pointOfClosedPoint_apply p x hxc a).symm ▸ X.basicOpen_le h hx
  have h1 := H _ (pointOfClosedPoint_comp p x hxc) e
  have h2 : ((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h1
  have h3 := Scheme.basicOpen_appLE (pointOfClosedPoint p x hxc) ⊤ W e h
  have h4 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
      (Spec (CommRingCat.of ℂ)).basicOpen (((pointOfClosedPoint p x hxc).appLE W ⊤ e).hom h) := by
    have h5 : (IsLocalRing.closedPoint ℂ : Spec (CommRingCat.of ℂ)) ∈
        ⊤ ⊓ (pointOfClosedPoint p x hxc) ⁻¹ᵁ X.basicOpen h := by
      refine ⟨trivial, ?_⟩
      change pointOfClosedPoint p x hxc _ ∈ X.basicOpen h
      exact (pointOfClosedPoint_apply p x hxc _).symm ▸ hx
    rw [← h3] at h5
    exact h5
  rw [h2, Scheme.basicOpen_zero] at h4
  exact h4
end GlobalTheory.SchemeHomsFromPoints
