-- Prove2me | solution 1 for NumberField.StandardAddChar.exists_ne_zero_and_hasDerivAt_psiQ_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7d73fa0c-24f2-54d6-8b9e-94ceded900a6

import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace PsiQRealDerivative

open NumberField.StandardAddChar

private theorem psiQ_ofReal_zero (s : ℝ) :
    psiQ ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ) =
      Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) := by
  rw [psiQ_apply]
  show psiArch (AutomorphicForm.StandardKernel.ofReal s) * psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, psiArch_apply, finprod_unique, psiArchPlace_apply]
  congr 2
  exact congrArg (fun r : ℝ => (r : ℂ))
    ((InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).apply_symm_apply s)

private theorem hasDerivAt_cexp_two_pi_I_mul :
    HasDerivAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * ((0 : ℝ) : ℂ)) * (2 * Real.pi * Complex.I * 1)) 0 :=
  ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp

end PsiQRealDerivative

open NumberField NumberField.StandardAddChar PsiQRealDerivative in
theorem solution :
    ∃ lam : ℂ, lam ≠ 0 ∧
      HasDerivAt
        (fun s : ℝ => NumberField.StandardAddChar.psiQ
          ((AutomorphicForm.StandardKernel.ofReal s, 0) : AdeleRing (𝓞 ℚ) ℚ))
        lam 0 := by
  refine ⟨_, ?_, hasDerivAt_cexp_two_pi_I_mul.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => psiQ_ofReal_zero s)⟩
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) one_ne_zero)

end
end S_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal
end P2MW
export P2MW.S_NumberField_StandardAddChar_exists_ne_zero_and_hasDerivAt_psiQ_ofReal (solution)
