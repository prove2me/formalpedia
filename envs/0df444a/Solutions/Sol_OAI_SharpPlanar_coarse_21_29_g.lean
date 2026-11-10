-- Prove2me | solution 1 for OAI.SharpPlanar.coarse_21_29_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:26:09.257801+00:00
-- url     : https://prove2.me/submissions/e3f15c15-6f80-47d8-a049-487d158d93b0

import Mathlib
import Definitions.Def_OAIQ098G1690

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_CoarseBound21
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
lemma coarse_21_29_g_oai : sharpTaylor 29 21/((Nat.factorial 29):ℝ)≤(713855953241536:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.coarse_21_29_g_oai := @OAI.SharpPlanar.coarse_21_29_g_oai
