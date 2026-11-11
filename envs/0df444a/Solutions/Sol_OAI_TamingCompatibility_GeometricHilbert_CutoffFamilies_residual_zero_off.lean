-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:35.614729+00:00
-- url     : https://prove2.me/submissions/99fe70cb-1c7f-4278-9a99-b30b5eba20f3

import Mathlib
import Definitions.Def_OAIQ239Tc003

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeCutoffResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma residual_zero_off_oai (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) (q : P) (t : ℝ) {z : V} (hz : z ∉ tsupport χ) :
    residual (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
      (fun y => zero a b c χ (q,y)) t z = 0 := by
  have hdd (j : Fin 4) : fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single j 1)) z = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hz (tsupport_fderiv_apply_subset ℝ _ hh))
  simp [NormalHeatResidual.residual,principal,first,zero,cutoffPrincipal,cutoffFirst,cutoffZero,
    image_eq_zero_of_notMem_tsupport hz,fderiv_of_notMem_tsupport ℝ hz,hdd]

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off_oai.{u_1, u_2} := @OAI.TamingCompatibility.GeometricHilbert.CutoffFamilies.residual_zero_off_oai.{u_1, u_2}
