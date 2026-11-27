-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.genRd_rigPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:41:35.496842+00:00
-- url     : https://prove2.me/submissions/81be5dc3-9d4b-4f73-b06b-3db7a8d21439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Theorems.Thm_GlobalTheory_AnVal_AnFr_genMove_e_zero_left
import Theorems.Thm_GlobalTheory_AnVal_genMove_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_valU


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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution (k : ℤ) :
    Φ.GenRd (K := PUnit) (fun _ => eSec A) (fun _ => k) (rigPow A L.L L.rig k) x0 (fun _ => 0) 1 := by
  refine ⟨fun _ => Φ.genMove_e_zero_left.symm, fun j hj => ?_⟩
  have hk := genMove_chart L.L (K := PUnit) (fun _ => eSec A) x0 j hj PUnit.unit
  rw [← Φ.genMove_e_zero_left] at hk
  rw [_root_.one_mul, Fintype.prod_unique]
  have e := Φ.fr_0 (j PUnit.unit) hk
  show _ = Φ.fr (j PUnit.unit) 0 ^ k
  rw [e]
  exact vtf_valU x0 hj (L.rig.s j) k
end AnFr
end GlobalTheory.AnVal
