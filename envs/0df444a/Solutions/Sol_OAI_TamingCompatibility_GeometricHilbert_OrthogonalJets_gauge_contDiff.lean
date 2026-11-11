-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:15:34.168201+00:00
-- url     : https://prove2.me/submissions/22906365-c710-482a-b2e6-b95841310b44

import Mathlib
import Definitions.Def_OAIQ239Tc007

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SymbolMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.OrthogonalJets
open scoped RealInnerProductSpace ContDiff
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_contDiff_oai (A : V →L[ℝ] End (W := W)) : ContDiff ℝ ∞ (gauge A) := by
  apply ContDiff.comp _ A.contDiff
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) z).contDiffAt

end TamingCompatibility.GeometricHilbert.OrthogonalJets


end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.OrthogonalJets.gauge_contDiff_oai.{u_1, u_2}
