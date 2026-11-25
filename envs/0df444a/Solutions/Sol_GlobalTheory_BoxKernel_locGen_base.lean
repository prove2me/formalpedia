-- Prove2me | solution 1 for GlobalTheory.BoxKernel.locGen_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:01:56.314046+00:00
-- url     : https://prove2.me/submissions/1f441286-aa96-41f1-b0c0-31a45e48a36d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KTrivExternalTensorPowerLineBundle
import Theorems.Thm_GlobalTheory_BoxKernel_gen_of_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxKernel
open GlobalTheory.KerPow
variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]
namespace GlobalTheory.BoxKernel
theorem _root_.solution (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k
end GlobalTheory.BoxKernel
