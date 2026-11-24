-- Prove2me | solution 1 for GlobalTheory.TransvFin.valT_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:09.380571+00:00
-- url     : https://prove2.me/submissions/0a679be7-a9a6-4e44-a713-040a8d2d49ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteOfIsClosedSingleton
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TransvFin
namespace GlobalTheory.TransvFin
theorem _root_.solution {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) {U : X.Opens}
    (h : ⊤ ≤ w ⁻¹ᵁ U) (f : Γ(X, U)) (p : Sp K) (hp : w p ∉ X.basicOpen f) : valT (T := K) w U f = 0 := by
  by_contra hne
  have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((w.appLE U ⊤ h).hom f)) := by
    have e : valT (T := K) w U f = _ := dif_pos h
    exact e ▸ Ne.isUnit hne
  have h2 : IsUnit ((w.appLE U ⊤ h).hom f) := by
    have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [Iso.hom_inv_id_apply] at this
  have h3 := (Sp K).basicOpen_of_isUnit h2
  rw [Scheme.basicOpen_appLE] at h3
  exact hp ((h3.ge (x := p) trivial).2)
end GlobalTheory.TransvFin
