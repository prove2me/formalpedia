-- Prove2me | solution 1 for GlobalTheory.ZV.MapDeg.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:43.778952+00:00
-- url     : https://prove2.me/submissions/88eba4ed-f03d-4b68-a06b-597d20bb15a3

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
theorem _root_.solution {ψ : X ⟶ Y} {D : ℕ} (h : MapDeg ψ D) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty) :
    letI := (ψ.app U).hom.toAlgebra
    Module.finrank Γ(Y, U) Γ(X, ψ ⁻¹ᵁ U) = D :=
  (congrArg Cardinal.toNat (h U hU hne)).trans (Cardinal.toNat_natCast D)
end MapDeg
end GlobalTheory.ZV
