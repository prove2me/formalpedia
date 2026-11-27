-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.existsUnique_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:23:55.924654+00:00
-- url     : https://prove2.me/submissions/0c908b1a-1413-4073-b095-652e6413a520

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SectionReadingExistsUniqueIsTheta
import Theorems.Thm_GlobalTheory_AnVal_AnFr_exists_chart_e
import Theorems.Thm_GlobalTheory_AnVal_AnFr_rd_iff
import Theorems.Thm_GlobalTheory_AnVal_AnFr_rd_eq_div

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) : ∃! θ, Φ.Rd k F θ := by
  choose c hc using Φ.exists_chart_e
  refine ⟨fun z => valAt' (vtfQ A (Φ.e z)).left ((LPow A L.L k (Over.mk x0)).U (fun _ => c z))
    (F.f (fun _ => c z)) / Φ.fr (c z) z ^ k, ?_, fun θ hθ => ?_⟩
  · refine (Φ.rd_iff k F _).2 fun z => ⟨c z, hc z, ?_⟩
    rw [div_mul_cancel₀ _ (zpow_ne_zero _ (Φ.fr_ne _ z (hc z)))]
  · funext z
    exact Φ.rd_eq_div hθ (c z) z (hc z)
end AnFr
end GlobalTheory.AnVal
