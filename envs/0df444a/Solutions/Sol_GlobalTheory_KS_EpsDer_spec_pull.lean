-- Prove2me | solution 1 for GlobalTheory.KS.EpsDer.spec_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:26.508291+00:00
-- url     : https://prove2.me/submissions/1c908b88-46da-4015-a930-71d6ca86a349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationOfDualNumberThickening

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsDer
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.KS.EpsDer
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (((spMap f).appLE ⊤ ⊤ e).hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a) := by
  have key : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop :=
    (Scheme.Hom.app_eq_appLE (f := spMap f) (U := ⊤)).symm
  rw [key]
  exact congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
end GlobalTheory.KS.EpsDer
