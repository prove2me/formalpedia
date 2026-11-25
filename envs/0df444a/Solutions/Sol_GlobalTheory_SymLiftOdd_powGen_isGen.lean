-- Prove2me | solution 1 for GlobalTheory.SymLiftOdd.powGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:07:17.824973+00:00
-- url     : https://prove2.me/submissions/0a9c7e11-6194-4c4a-b08f-7b30ef03ee6a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_GlobalTheory_SymLiftOdd_isGen_of_gm
import Theorems.Thm_GlobalTheory_SymLiftOdd_gm_powGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}
namespace GlobalTheory.SymLiftOdd
theorem _root_.solution (θ : ThetaGrp A L k T) (n : ℕ) : (powGen A L k θ n).IsGen := by
  refine isGen_of_gm fun y j j' hj hj' => ?_
  rw [gm_powGen θ n (𝟙 _) y j hj, gm_powGen θ n (𝟙 _) y j' hj', trF, Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j₀ _ => gen_trans (DVR.pullGen_isGen L _ _ _ θ.isGen _) (𝟙 _) y
    (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj (j₀, b)) (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj' (j₀, b))
end GlobalTheory.SymLiftOdd
