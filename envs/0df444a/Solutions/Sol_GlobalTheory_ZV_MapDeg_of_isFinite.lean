-- Prove2me | solution 1 for GlobalTheory.ZV.MapDeg.of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:15.463097+00:00
-- url     : https://prove2.me/submissions/1477b054-d6a1-4d07-8581-f36eb72f5b0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension

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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
namespace MapDeg
theorem _root_.solution {ψ : X ⟶ Y} [IsFinite ψ] {D : ℕ}
    (h : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      letI := (ψ.app U).hom.toAlgebra
      Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D) : MapDeg ψ D := fun U hU hne => by
  letI := (ψ.app U).hom.toAlgebra
  haveI : Nonempty U := hne.to_subtype
  haveI : Module.Finite Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) := ψ.finite_app U hU
  exact (Module.finrank_eq_rank _ _).symm.trans (congrArg _ (h U hU hne))
end MapDeg
end GlobalTheory.ZV
