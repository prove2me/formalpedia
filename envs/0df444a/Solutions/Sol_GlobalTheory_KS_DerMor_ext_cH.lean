-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.ext_cH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:27:12.580526+00:00
-- url     : https://prove2.me/submissions/413ddf60-f6fa-4e97-a126-c5a69f8de40a

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
theorem _root_.solution {R : Type} [CommRing R] {X : Scheme.{0}} (f g : X ⟶ Sp R)
    (h : ∀ a, cH f ⊤ a = cH g ⊤ a) : f = g := by
  have top : ∀ (k : X ⟶ Sp R) (r : R),
      cH k ⊤ r = (Scheme.Γ.map k.op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    intro k r
    have e1 : k.appLE ⊤ ⊤ le_top = k.app ⊤ := k.appLE_eq_app
    unfold cH
    rw [e1]
    rfl
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext r
  exact (top f r).symm.trans ((h r).trans (top g r))
end GlobalTheory.KS.DerMor
