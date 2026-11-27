-- Prove2me | solution 1 for GlobalTheory.AdjRead.hol_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:45:47.996725+00:00
-- url     : https://prove2.me/submissions/56b5c8ff-0ddd-415a-8e53-a5055bf58bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
omit [IsCommMonObj A]
namespace GlobalTheory.AdjRead
theorem _root_.solution {N : ℕ} (P : (Fin N → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => (Φ.e (P v)).left) := by
  have hh := Φ.hol
  unfold IsHolFam at hh ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hh U f
  have hP : Continuous P := LinearMap.continuous_of_finiteDimensional P
  exact ⟨ho.preimage hP, hd.comp (LinearMap.toContinuousLinearMap P).differentiableOn (fun z hz => hz)⟩
end GlobalTheory.AdjRead
