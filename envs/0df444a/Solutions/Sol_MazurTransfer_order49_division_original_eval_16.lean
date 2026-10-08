-- Prove2me | solution 1 for MazurTransfer.order49_division_original_eval_16
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:16:07.554568+00:00
-- url     : https://prove2.me/submissions/20b26166-2d38-4cc1-b23b-15c0f9fb0199

import Definitions.Def_MazurTransfer_Order49BacktrackingCofactors
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DirectEvaluationPredicates
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
open Polynomial
namespace MazurTransfer.Order49DivisionExplicitEvaluation
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

namespace Internal

-- In the coefficient declarations below, `X : ℚ[X]` is the parameter `D`.




























































































































































































































































































































































































































































































































































































































end Internal

















namespace Internal





end Internal

























































namespace Internal


















































lemma quotient_prePsiSeven (d : ℚ) :
    (MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 7 =
      ((MazurTorsion.Kubert.orderSevenQuotient d).preΨ₄ * (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₂Sq ^ 2 -
          (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₃ ^ 3) * (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₃ ^ 3 -
        (MazurTorsion.Kubert.orderSevenQuotient d).preΨ₄ ^ 3 *
          (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₂Sq ^ 2 := by
  have hfive :
      (MazurTorsion.Kubert.orderSevenQuotient d).preΨ' 5 =
        (MazurTorsion.Kubert.orderSevenQuotient d).preΨ₄ * (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₂Sq ^ 2 -
          (MazurTorsion.Kubert.orderSevenQuotient d).Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      (MazurTorsion.Kubert.orderSevenQuotient d).preΨ'_odd 0]
    norm_num
  rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num,
    (MazurTorsion.Kubert.orderSevenQuotient d).preΨ'_odd 1]
  norm_num [hfive]



end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end MazurTransfer.Order49DivisionExplicitEvaluation

namespace MazurTransfer.Order49DivisionExplicitEvaluation
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal



private lemma eval_16 (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 16 := by
  unfold MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate
  rw [MazurTransfer.Order49DivisionExplicitEvaluation.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.quotient_prePsiSeven]
  simp only [MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient0Chunk2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient1Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient2Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient2Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient3Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient4Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient5,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient5Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient6Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor0Coefficient7Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient0Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient0Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient0Chunk2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient1Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient1Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient2Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient2Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient3,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient3Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient3Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient4,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient4Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient5,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient5Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient6,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient6Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor1Coefficient7Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient0Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient0Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient0Chunk2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient1Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient1Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient2Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient2Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient3,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient3Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient3Chunk1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient4,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient4Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient5,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient5Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient6,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient6Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient7,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.divisionCofactor2Coefficient7Chunk0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.dualKernelPolynomial,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactor2,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData0,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData1,
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.divisionCofactorData2,
    MazurTorsion.Kubert.orderSevenB,
    MazurTorsion.Kubert.orderSevenC,
    MazurTorsion.Kubert.orderSevenQuotient,
    WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,
    WeierstrassCurve.b₈,
    Polynomial.eval_add,
    Polynomial.eval_sub,
    Polynomial.eval_neg,
    Polynomial.eval_mul,
    Polynomial.eval_pow,
    Polynomial.eval_C,
    Polynomial.eval_X,
    Polynomial.eval_zero,
    Polynomial.eval_one,
    Polynomial.eval_natCast,
    Polynomial.eval_ofNat,
    Polynomial.eval_intCast,
    Polynomial.map_add,
    Polynomial.map_sub,
    Polynomial.map_neg,
    Polynomial.map_mul,
    Polynomial.map_pow,
    Polynomial.map_C,
    Polynomial.map_X,
    Polynomial.coe_evalRingHom,
    Polynomial.map_natCast,
    Polynomial.map_ofNat]
  ring









end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

end MazurTransfer.Order49DivisionExplicitEvaluation

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.DivisionEvalCertificate d 16 := by
  exact MazurTransfer.Order49DivisionExplicitEvaluation.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.eval_16 d
#print axioms solution
