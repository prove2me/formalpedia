-- Prove2me | solution 1 for GlobalTheory.AnValSym.negT_translPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:57:09.214871+00:00
-- url     : https://prove2.me/submissions/8542ef2c-af5e-4d14-84fb-aed01fe5199f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ThetaConstSymmetricSquareEqOne
import Theorems.Thm_GlobalTheory_AnValSym_translPt_eq
import Theorems.Thm_GlobalTheory_AnValSym_translT_snd
import Theorems.Thm_GlobalTheory_AnValSym_negT_snd
import Theorems.Thm_GlobalTheory_AnValSym_negT_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValSym
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}
namespace GlobalTheory.AnValSym
theorem _root_.solution [IsCommMonObj A] (x : T ⟶ A) :
    negT A T ≫ translPt A x = translT A x⁻¹ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)) := by
  rw [translPt_eq, comp_mul, ← Category.assoc, negT_fst, negT_snd, ← Category.assoc, translT_snd, ← Hom.inv_def,
    mul_inv_rev, GrpObj.comp_inv, inv_inv]
  exact mul_comm _ _
end GlobalTheory.AnValSym
