-- Prove2me | solution 1 for GlobalTheory.LinearUnifCheck.torusEndOf_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:29.24428+00:00
-- url     : https://prove2.me/submissions/04e69ab3-85dd-40f3-bbde-be2900084a0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_NeTopOfAdmissibleBase
import Theorems.Thm_GlobalTheory_LinearUnifCheck_torusEndOf_iff
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LinearUnifCheck
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.LinearUnifCheck
theorem _root_.solution {h : X → X} {t t' : splitTorus S X ⟶ splitTorus S X}
    (ht : TorusEndOf X h t) (ht' : TorusEndOf X h t') : t = t' := by
  refine (splitTorusPointsEquiv S X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusEndOf_iff _ _).1 ht,
    (torusEndOf_iff _ _).1 ht']
end GlobalTheory.LinearUnifCheck
