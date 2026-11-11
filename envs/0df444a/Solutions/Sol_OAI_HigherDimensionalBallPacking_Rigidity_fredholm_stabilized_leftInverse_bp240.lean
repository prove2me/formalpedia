-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:09:22.764163+00:00
-- url     : https://prove2.me/submissions/aea1d858-dfdb-4dda-b61b-302bb5d22ca4

import Mathlib

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FreeLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function
variable {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

 theorem fredholm_stabilized_leftInverse_bp240_oai (P : E →L[ℝ] F) (hP : P.IsFredholm)
    (Q : E →L[ℝ] D) (hQ : Injective (Q.comp P.ker.subtypeL)) :
    (P.prod Q).HasLeftInverse := by
  obtain ⟨pkg⟩ := hP.nonempty_fredholmPackage
  let S : F →L[ℝ] E := pkg.quasiInverse
  have hPSP (v : E) : P (S (P v))=P v := by
    rw [pkg.eq_equiv]
    simp [S,ContinuousLinearMap.FredholmPackage.quasiInverse,Submodule.projectionOnto_projection]
  let QK : P.ker →L[ℝ] D := Q.comp P.ker.subtypeL
  obtain ⟨U,hU⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hQ
  let T : F × D →L[ℝ] E := S.comp (ContinuousLinearMap.fst ℝ F D)
  let L : F × D →L[ℝ] E := T + P.ker.subtypeL.comp
    (U.comp (ContinuousLinearMap.snd ℝ F D-Q.comp T))
  refine ⟨L,fun v => ?_⟩
  have hr : v-S (P v)∈P.ker := by
    change P (v-S (P v))=0
    rw [map_sub,hPSP,sub_self]
  have hu := congrArg (fun z : P.ker => (z:E)) (hU ⟨v-S (P v),hr⟩)
  change (U (Q (v-S (P v))) : E)=v-S (P v) at hu
  change S (P v)+(U (Q v-Q (S (P v))) : E)=v
  rw [←map_sub,hu]
  abel


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse_bp240_oai.{u_1, u_2, u_3} := @OAI.HigherDimensionalBallPacking.Rigidity.fredholm_stabilized_leftInverse_bp240_oai.{u_1, u_2, u_3}
