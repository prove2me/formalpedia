-- Prove2me | solution 1 for GlobalTheory.exists_isGen_linComb_of_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:36.749325+00:00
-- url     : https://prove2.me/submissions/8baf3d72-d762-4571-9199-c74628b1e1d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm
end GlobalTheory
