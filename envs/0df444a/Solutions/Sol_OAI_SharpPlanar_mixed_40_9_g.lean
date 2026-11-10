-- Prove2me | solution 1 for OAI.SharpPlanar.mixed_40_9_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:34:44.211714+00:00
-- url     : https://prove2.me/submissions/173686cb-be97-4499-89a9-717c3c78cf71

import Mathlib
import Definitions.Def_OAIQ098G1697

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_MixedBound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma mixed_40_9_g_oai : transformTaylor 9 40/((Nat.factorial 9):ℝ)≤(105999991106160182956535889:ℝ)/1000000000000000000000000000000 := by
  first | (simp [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [transformTaylor,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.mixed_40_9_g_oai := @OAI.SharpPlanar.mixed_40_9_g_oai
