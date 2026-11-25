-- Prove2me | solution 1 for GlobalTheory.exists_pullU_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:07:54.960282+00:00
-- url     : https://prove2.me/submissions/1bee4f08-a68e-44e8-8f56-fd64d762a0e9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
include hc
namespace GlobalTheory
theorem _root_.solution {i : I} {U : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (s t : Γ(D.obj i, U)ˣ)
    (h : ∀ y : X, π i y ∈ U → gm (π i) y U s = gm (π i) y U t) :
    ∃ (j : I) (f : j ⟶ i), pullU (D.map f) U s = pullU (D.map f) U t := by
  have h' : pullU (π i) U s = pullU (π i) U t := unit_ext fun y hy =>
    (gm_pull (𝟙 _) _ y U hy s).trans ((h y hy).trans (gm_pull (𝟙 _) _ y U hy t).symm)
  obtain ⟨j, f, hf⟩ := exists_app_map_eq_map_of_isLimit D _ hc hU s.val t.val (congrArg Units.val h')
  exact ⟨j, f, Units.ext hf⟩
end GlobalTheory
