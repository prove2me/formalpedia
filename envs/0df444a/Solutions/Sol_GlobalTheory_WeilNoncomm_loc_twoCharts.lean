-- Prove2me | solution 1 for GlobalTheory.WeilNoncomm.loc_twoCharts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:30.163871+00:00
-- url     : https://prove2.me/submissions/3833df85-b874-4f1e-bc10-8a13e4db593f

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
import Theorems.Thm_GlobalTheory_WeilNoncomm_gm_sgn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
theorem _root_.solution {T : Over S} (z : T.left) (θ : ThetaGrp G (twoCharts G.left) 1 T) (a : T ⟶ G) :
    loc G z θ a false true = -loc G z θ a false false := by
  have k₄ := gen_trans θ.isGen (lift (𝟙 T) a).left z (j := ![false, true]) (j' := ![false, false])
    (Set.mem_iInter.2 fun _ => trivial) (Set.mem_iInter.2 fun _ => trivial)
  refine k₄.trans (Eq.trans (congrArg (· * loc G z θ a false false) ?_) (neg_one_mul _))
  rw [trF, Fin.prod_univ_two]
  refine (congrArg₂ (fun a b => a ^ (1 : ℤ) * b ^ (-1 : ℤ)) (gm_sgn _ z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ false)
      (gm_sgn _ z (⊤ ⊓ ⊤) ⟨trivial, trivial⟩ true)).trans ?_
  simp [sgn]
end GlobalTheory.WeilNoncomm
