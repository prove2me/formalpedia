-- Prove2me | solution 1 for OAI.SharpPlanar.coarse_31_21_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:27:24.683388+00:00
-- url     : https://prove2.me/submissions/c9d6c9b0-0db8-44d9-8c67-295d57230f82

import Mathlib
import Definitions.Def_OAIQ098G1690

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_CoarseBound31
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
lemma coarse_31_21_g_oai : sharpTaylor 21 31/((Nat.factorial 21):ℝ)≤(1744203475531886507303:ℝ)/1000000000000000000000000000000 := by
  first | (simp [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; all_goals first | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | rfl | decide) | (norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]; done) | norm_num [sharpTaylor,directRational,transformRational,atomicRational,pieceIntCap,atomIntCap,piUpper, densityCap,densityNum,densityDen,lambdaCap,pieceBase,atomBase,atomMass,massRational,slopeCap,zCap,Fin.sum_univ_succ,Nat.factorial]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.coarse_31_21_g_oai := @OAI.SharpPlanar.coarse_31_21_g_oai
