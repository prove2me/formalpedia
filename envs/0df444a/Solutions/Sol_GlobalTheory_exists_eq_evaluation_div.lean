-- Prove2me | solution 1 for GlobalTheory.exists_eq_evaluation_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:30.54595+00:00
-- url     : https://prove2.me/submissions/90626ec4-27bb-4a52-8dc9-92e514c72fbc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueFieldMapFiniteSeparableOfTame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (z : X.residueField x) : ∃ a b : Γ(X, U), z = X.evaluation U x hx a / X.evaluation U x hx b := by
  classical
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have he : ∀ c, X.evaluation U x hx c =
      (X.residue x).hom (algebraMap Γ(X, U) (X.presheaf.stalk x) c) := fun c => rfl
  obtain ⟨s, rfl⟩ : ∃ s, (X.residue x).hom s = z := IsLocalRing.residue_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  change s * algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U)) =
    algebraMap Γ(X, U) (X.presheaf.stalk x) a at hab
  have hb0 : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U))) :=
    IsLocalization.map_units _ b
  have hb := hb0.map (X.residue x).hom
  refine ⟨a, b, ?_⟩
  rw [he, he, eq_div_iff hb.ne_zero, ← map_mul (X.residue x).hom, hab]
end GlobalTheory
