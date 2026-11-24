-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.deform_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:27:11.860826+00:00
-- url     : https://prove2.me/submissions/793b0752-e44b-409e-a856-55ba87a139f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor
namespace GlobalTheory.KS.DerMor
theorem _root_.solution {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) (W : X.Opens) :
    (deform n c hres hnil).app W = CommRingCat.ofHom (c W) := rfl
end GlobalTheory.KS.DerMor
