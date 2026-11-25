-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.val_eq_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:35.589714+00:00
-- url     : https://prove2.me/submissions/add4958f-2aab-4d5b-b459-bba0020d3f8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
import Theorems.Thm_GlobalTheory_WeilNoncomm_lift_translPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
namespace GlobalTheory.WeilNoncomm
theorem _root_.solution {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) (θ : ThetaGrp G L k T) (a : T ⟶ G)
    (J : (T.left ⟶ G.left) → L.ι) :
    val θ.φ (lift (𝟙 T) a).left z J = loc G z θ a (J a.left) (J (θ.pt * a).left) :=
  val_of _ _ z J _ fun i => by
    fin_cases i
    · show J ((lift (𝟙 T) a).left ≫ (snd T G).left) = J a.left
      rw [← Over.comp_left, lift_snd]
    · show J ((lift (𝟙 T) a).left ≫ (translPt G θ.pt).left) = J (θ.pt * a).left
      rw [← Over.comp_left, lift_translPt]
end GlobalTheory.WeilNoncomm
