-- Prove2me | solution 1 for GlobalTheory.LieExt.exists_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:28.133531+00:00
-- url     : https://prove2.me/submissions/b8c286b6-85c0-4d6d-bafc-01b172f0a14c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieMultIffFinrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.LieExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LieExt
theorem _root_.solution {k K O : Type} [Field k] [IsAlgClosed k] [Field K] [CommRing O] [Algebra.IsIntegral ℤ O]
    (φ : k →+* K) (τ : O →+* K) : ∃ χ : O →+* k, φ.comp χ = τ := by
  let _ := φ.toAlgebra
  have h : ∀ a, ∃ z : k, φ z = τ a := fun a => by
    have hi : IsIntegral k (τ a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map τ.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))
  choose f hf using h
  have inj := φ.injective
  exact ⟨⟨⟨⟨f, inj (by simp [hf])⟩, fun a b => inj (by simp [hf])⟩, inj (by simp [hf]),
    fun a b => inj (by simp [hf])⟩, RingHom.ext hf⟩
end GlobalTheory.LieExt
