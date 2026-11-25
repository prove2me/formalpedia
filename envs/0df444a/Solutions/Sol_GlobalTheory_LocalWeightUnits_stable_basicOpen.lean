-- Prove2me | solution 1 for GlobalTheory.LocalWeightUnits.stable_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:51:52.838154+00:00
-- url     : https://prove2.me/submissions/20382ff2-6c05-4d37-8ccd-0ea1ac53b81e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_ZJ_charUnit_zero_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}
namespace GlobalTheory.LocalWeightUnits
theorem _root_.solution {V : H.left.Opens} (hV : Stable i V) {b : Γ(H.left, V)} (hb : HasWt i V b 0) :
    Stable i (H.left.basicOpen b) := by
  intro Y t g h
  have h₁ : ⊤ ≤ g.left ⁻¹ᵁ V := h.trans (g.left.preimage_mono (H.left.basicOpen_le b))
  have e := congrArg Y.left.basicOpen (hb Y t g h₁ (hV Y t g h₁))
  rw [charUnit_zero_val, map_one, _root_.one_mul, Scheme.basicOpen_appLE, Scheme.basicOpen_appLE] at e
  exact ((le_inf le_rfl h).trans e.ge).trans inf_le_right
end GlobalTheory.LocalWeightUnits
