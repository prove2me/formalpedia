-- Prove2me | solution 1 for GlobalTheory.Spread.exists_fg_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:09:21.948044+00:00
-- url     : https://prove2.me/submissions/b76056d5-bf67-46c4-87f4-08208f86f07b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution [QuasiCompact pB] [LocallyOfFiniteType pZ]
    (R : Subalgebra k A) (hR : R.FG) (a b : pullback pB (spMap (algebraMap k R)) ⟶ Z)
    (ha : a ≫ pZ = pullback.fst _ _ ≫ pB) (hb : b ≫ pZ = pullback.fst _ _ ≫ pB)
    (hab : bcMap pB R.val ≫ a = bcMap pB R.val ≫ b) :
    ∃ (R' : Subalgebra k A) (h : R ≤ R'), R'.FG ∧
      bcMap pB (Subalgebra.inclusion h) ≫ a = bcMap pB (Subalgebra.inclusion h) ≫ b := by
  classical
  obtain ⟨s, rfl⟩ := hR
  obtain ⟨t, f, h⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (bcDiagram pB A) (bcStr pB A) pZ (bcCone pB A) (isLimitBcCone pB A) (i := .op s) a b
    ha.symm hb.symm hab
  exact ⟨Algebra.adjoin k (t.unop : Set A), _, Subalgebra.fg_adjoin_finset _, h⟩
end GlobalTheory.Spread
