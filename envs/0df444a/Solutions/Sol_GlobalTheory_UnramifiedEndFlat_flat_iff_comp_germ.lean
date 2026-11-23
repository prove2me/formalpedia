-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.flat_iff_comp_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:07.115246+00:00
-- url     : https://prove2.me/submissions/f28b9124-34d0-4cfe-970a-cb4ed9d2f167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing
namespace GlobalTheory.UnramifiedEndFlat
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C
end GlobalTheory.UnramifiedEndFlat
