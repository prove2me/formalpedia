-- Prove2me | solution 1 for GlobalTheory.VolFin.gen_rs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:22.327907+00:00
-- url     : https://prove2.me/submissions/41558a99-825f-46e1-bbbf-6a0e654a6c75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff

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
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
open GlobalTheory GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
namespace GlobalTheory.VolFin
theorem _root_.solution {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    gen V hV (rs X h a) = gen U (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a
end GlobalTheory.VolFin
