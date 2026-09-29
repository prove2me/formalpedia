-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fb819303-12a2-5042-890c-20abbf6b274c

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

open LanglandsTunnell.CubicInduction

namespace Ws31
namespace TT

theorem torus_mul_upperUnipotent3 (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (u : (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    (iotaGL (diagUnitGL2 u) : LocalGL3 v) * upperUnipotent3 x y z =
      upperUnipotent3 ((u : v.adicCompletion ℚ) * x) y ((u : v.adicCompletion ℚ) * z) * iotaGL (diagUnitGL2 u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, upperUnipotent3, diagUnitGL2, Matrix.mul_apply, Fin.sum_univ_three]
end Ws31.TT

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ) (g : LocalGL3 v) :
    W (iotaGL (diagUnitGL2 a) * (upperUnipotent3 x 0 0 * g)) = ψv ((a : v.adicCompletion ℚ) * x) * W (iotaGL (diagUnitGL2 a) * g) := by
  rw [← mul_assoc, Ws31.TT.torus_mul_upperUnipotent3 v a x 0 0, mul_zero, mul_assoc, hW, add_zero]

end S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_apply_iotaGL_diagUnitGL2_mul_upperUnipotent3_mul_of_isGL3PsiWhittakerFn (solution)
