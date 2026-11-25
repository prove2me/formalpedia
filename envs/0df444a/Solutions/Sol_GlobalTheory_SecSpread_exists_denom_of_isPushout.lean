-- Prove2me | solution 1 for GlobalTheory.SecSpread.exists_denom_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:08:29.887793+00:00
-- url     : https://prove2.me/submissions/b626de03-22de-420b-accf-2f13dae8c256

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
namespace GlobalTheory.SecSpread
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {R₀ A K P : CommRingCat.{0}} {α : R₀ ⟶ A}
    {ψ : R₀ ⟶ K} {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout α ψ inl inr) (c : R →+* R₀)
    (hK : ∀ k : K, ∃ d : R, d ≠ 0 ∧ ∃ r : R₀, ψ.hom (c d) * k = ψ.hom r) (t : P) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : A, inl.hom (α.hom (c d)) * t = inl.hom a := by
  have hw : ∀ r, inl.hom (α.hom r) = inr.hom (ψ.hom r) := fun r => congr($(H.w).hom r)
  have ht : t ∈ Subring.closure (Set.range inl ∪ Set.range inr) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout H]; trivial
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨1, one_ne_zero, a, by simp⟩
    · obtain ⟨d, hd, r, hr⟩ := hK k
      refine ⟨d, hd, α.hom r, ?_⟩
      rw [hw, hw, ← hr, map_mul]
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | one => exact ⟨1, one_ne_zero, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, a, ha⟩ := hx
    obtain ⟨e, he, b, hb⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, α.hom (c e) * a + α.hom (c d) * b, ?_⟩
    simp only [map_mul, map_add]
    rw [← ha, ← hb]; ring
  | neg x _ hx =>
    obtain ⟨d, hd, a, ha⟩ := hx
    exact ⟨d, hd, -a, by rw [map_neg, ← ha, mul_neg]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, a, ha⟩ := hx
    obtain ⟨e, he, b, hb⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, a * b, ?_⟩
    simp only [map_mul]
    rw [← ha, ← hb]; ring
end GlobalTheory.SecSpread
