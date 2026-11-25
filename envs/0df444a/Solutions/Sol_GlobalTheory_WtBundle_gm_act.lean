-- Prove2me | solution 1 for GlobalTheory.WtBundle.gm_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:45.116685+00:00
-- url     : https://prove2.me/submissions/9194c504-6200-48dd-8598-3fbee2ea6b17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CommGroupCommonFactorQuotientCancel
import Theorems.Thm_GlobalTheory_WtBundle_gm_of_isWt
import Theorems.Thm_GlobalTheory_WtBundle_act_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.WtBundle
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
variable (Q : TQ G X)
namespace GlobalTheory.WtBundle
theorem _root_.solution {V : Q.B.left.Opens} {u : Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ} {χ : X} (hu : IsWt Q.i _ u.val χ)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h : Q.q.left (g.left z) ∈ V) :
    gm ((t ≫ Q.i) * g).left z (Q.q.left ⁻¹ᵁ V) u =
      gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z (Q.q.left ⁻¹ᵁ V) u :=
  gm_of_isWt hu t g z ((congrArg (fun m : Z ⟶ Q.B => m.left z ∈ V) (act_comp Q t g)).mpr h) h
end GlobalTheory.WtBundle
