-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:26:05.693351+00:00
-- url     : https://prove2.me/submissions/74aea80e-ab2c-4c14-9aed-fe04dda351ed

import Definitions.Def_MazurTransfer_Order49ResultantRecurrenceData0
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_0
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_1
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_2
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_3
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_4
import Theorems.Thm_MazurTransfer_order49_resultant_recurrence0_inner_block_5


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingCertificateData. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Polynomial data for the order-seven backtracking certificates

This file stores the degree-33 selection cofactor and the three canonical
degree-seven quotient cofactors as nested polynomials in `ℚ[D][X]`.  The
pointwise `ℚ[X]` factors are obtained only by specializing the inner parameter
variable, so the large coefficient tables have a single source of truth.

The quotient factors are ordered by constant-term `D`-valuation `3`, `2`, and
`1`; this is the canonical order used by the FLINT resultant computation.

## Computational provenance

The coefficient tables were generated with SymPy polynomial arithmetic over
`ℚ[x,d]`.  The computation expanded the order-seven Tate and selection
formulas, formed the selection numerator and the quotient seventh division
polynomial, divided each exactly by the displayed dual-kernel cubic, factored
the quotient cofactor, and sorted its three factors by constant-term
`d`-valuation `3`, `2`, and `1`.  SymPy specialization at the integer
abscissas emitted the Horner expressions in the evaluation shards.  The Lean
`ring` proofs in those shards and the interpolation argument in the final
certificate check the emitted data; they do not trust the generating script.
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

lemma selectionCofactorData_degree :
    selectionCofactorData.natDegree ≤ 33 := by
  unfold selectionCofactorData
  compute_degree







lemma divisionCofactorData0_degree :
    divisionCofactorData0.natDegree ≤ 7 := by
  unfold divisionCofactorData0
  compute_degree











@[simp] theorem divisionCofactorData0_coeff_seven :
    divisionCofactorData0.coeff 7 = 1 := by
  simp [divisionCofactorData0, Internal.divisionCofactor0Coefficient7,
    Internal.divisionCofactor0Coefficient7Chunk0]



































namespace Internal






















































end Internal

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end
end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner0 :
    Internal.selectionCofactorCoefficient0 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient0 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.1

theorem recurrence0Inner1 :
    Internal.selectionCofactorCoefficient1 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient1 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.2.1

theorem recurrence0Inner2 :
    Internal.selectionCofactorCoefficient2 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient2 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.2.2.1

theorem recurrence0Inner3 :
    Internal.selectionCofactorCoefficient3 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient3 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.2.2.2.1

theorem recurrence0Inner4 :
    Internal.selectionCofactorCoefficient4 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient4 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.2.2.2.2.1

theorem recurrence0Inner5 :
    Internal.selectionCofactorCoefficient5 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient5 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_0.2.2.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart1. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner6 :
    Internal.selectionCofactorCoefficient6 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient0 +
      exceptional0 * remainder2Coefficient6 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.1

theorem recurrence0Inner7 :
    Internal.selectionCofactorCoefficient7 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient1 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient0 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.2.1

theorem recurrence0Inner8 :
    Internal.selectionCofactorCoefficient8 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient2 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient1 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.2.2.1

theorem recurrence0Inner9 :
    Internal.selectionCofactorCoefficient9 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient3 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient2 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.2.2.2.1

theorem recurrence0Inner10 :
    Internal.selectionCofactorCoefficient10 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient4 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient3 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.2.2.2.2.1

theorem recurrence0Inner11 :
    Internal.selectionCofactorCoefficient11 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient5 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient4 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_1.2.2.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart2. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner12 :
    Internal.selectionCofactorCoefficient12 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient6 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient5 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.1

theorem recurrence0Inner13 :
    Internal.selectionCofactorCoefficient13 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient7 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient6 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.2.1

theorem recurrence0Inner14 :
    Internal.selectionCofactorCoefficient14 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient8 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient7 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.2.2.1

theorem recurrence0Inner15 :
    Internal.selectionCofactorCoefficient15 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient9 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient8 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.2.2.2.1

theorem recurrence0Inner16 :
    Internal.selectionCofactorCoefficient16 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient10 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient9 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.2.2.2.2.1

theorem recurrence0Inner17 :
    Internal.selectionCofactorCoefficient17 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient11 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient10 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_2.2.2.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart3. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner18 :
    Internal.selectionCofactorCoefficient18 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient12 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient11 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.1

theorem recurrence0Inner19 :
    Internal.selectionCofactorCoefficient19 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient13 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient12 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.2.1

theorem recurrence0Inner20 :
    Internal.selectionCofactorCoefficient20 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient14 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient13 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.2.2.1

theorem recurrence0Inner21 :
    Internal.selectionCofactorCoefficient21 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient15 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient14 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.2.2.2.1

theorem recurrence0Inner22 :
    Internal.selectionCofactorCoefficient22 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient16 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient15 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.2.2.2.2.1

theorem recurrence0Inner23 :
    Internal.selectionCofactorCoefficient23 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient17 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient16 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_3.2.2.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart4. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner24 :
    Internal.selectionCofactorCoefficient24 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient18 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient17 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.1

theorem recurrence0Inner25 :
    Internal.selectionCofactorCoefficient25 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient19 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient18 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.2.1

theorem recurrence0Inner26 :
    Internal.selectionCofactorCoefficient26 =
      Internal.divisionCofactor0Coefficient0 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient20 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient19 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.2.2.1

theorem recurrence0Inner27 :
    Internal.selectionCofactorCoefficient27 =
      Internal.divisionCofactor0Coefficient1 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient21 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient20 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.2.2.2.1

theorem recurrence0Inner28 :
    Internal.selectionCofactorCoefficient28 =
      Internal.divisionCofactor0Coefficient2 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient22 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient21 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.2.2.2.2.1

theorem recurrence0Inner29 :
    Internal.selectionCofactorCoefficient29 =
      Internal.divisionCofactor0Coefficient3 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient23 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient22 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_4.2.2.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0InnerPart5. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence certificates for order-seven branch zero

This internal proof shard checks a balanced subset of the independent
coefficient identities used by the initial pseudo-remainder recurrence.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem recurrence0Inner30 :
    Internal.selectionCofactorCoefficient30 =
      Internal.divisionCofactor0Coefficient4 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient24 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient23 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_5.1

theorem recurrence0Inner31 :
    Internal.selectionCofactorCoefficient31 =
      Internal.divisionCofactor0Coefficient5 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient25 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient24 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_5.2.1

theorem recurrence0Inner32 :
    Internal.selectionCofactorCoefficient32 =
      Internal.divisionCofactor0Coefficient6 * quotient0Coefficient26 +
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient25 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_5.2.2.1

theorem recurrence0Inner33 :
    Internal.selectionCofactorCoefficient33 =
      Internal.divisionCofactor0Coefficient7 * quotient0Coefficient26 := by
  exact MazurTransfer.order49_resultant_recurrence0_inner_block_5.2.2.2

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end


/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Initial resultant recurrence for order-seven branch zero

This file checks the first primitive pseudo-remainder recurrence over
the bivariate polynomial ring. The internal coefficient identities are
exact ring certificates for the thirty-four outer coefficients.
-/

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

@[simp] private theorem remainder0_coeff_0 :
    remainder0.coeff 0 = Internal.selectionCofactorCoefficient0 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_0 :
    remainder1.coeff 0 = Internal.divisionCofactor0Coefficient0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_0 :
    quotient0.coeff 0 = quotient0Coefficient0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_0 :
    remainder2.coeff 0 = remainder2Coefficient0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_1 :
    remainder0.coeff 1 = Internal.selectionCofactorCoefficient1 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_1 :
    remainder1.coeff 1 = Internal.divisionCofactor0Coefficient1 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_1 :
    quotient0.coeff 1 = quotient0Coefficient1 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_1 :
    remainder2.coeff 1 = remainder2Coefficient1 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_2 :
    remainder0.coeff 2 = Internal.selectionCofactorCoefficient2 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_2 :
    remainder1.coeff 2 = Internal.divisionCofactor0Coefficient2 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_2 :
    quotient0.coeff 2 = quotient0Coefficient2 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_2 :
    remainder2.coeff 2 = remainder2Coefficient2 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_3 :
    remainder0.coeff 3 = Internal.selectionCofactorCoefficient3 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_3 :
    remainder1.coeff 3 = Internal.divisionCofactor0Coefficient3 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_3 :
    quotient0.coeff 3 = quotient0Coefficient3 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_3 :
    remainder2.coeff 3 = remainder2Coefficient3 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_4 :
    remainder0.coeff 4 = Internal.selectionCofactorCoefficient4 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_4 :
    remainder1.coeff 4 = Internal.divisionCofactor0Coefficient4 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_4 :
    quotient0.coeff 4 = quotient0Coefficient4 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_4 :
    remainder2.coeff 4 = remainder2Coefficient4 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_5 :
    remainder0.coeff 5 = Internal.selectionCofactorCoefficient5 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_5 :
    remainder1.coeff 5 = Internal.divisionCofactor0Coefficient5 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_5 :
    quotient0.coeff 5 = quotient0Coefficient5 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_5 :
    remainder2.coeff 5 = remainder2Coefficient5 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_6 :
    remainder0.coeff 6 = Internal.selectionCofactorCoefficient6 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_6 :
    remainder1.coeff 6 = Internal.divisionCofactor0Coefficient6 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_6 :
    quotient0.coeff 6 = quotient0Coefficient6 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_6 :
    remainder2.coeff 6 = remainder2Coefficient6 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_7 :
    remainder0.coeff 7 = Internal.selectionCofactorCoefficient7 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_7 :
    remainder1.coeff 7 = Internal.divisionCofactor0Coefficient7 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_7 :
    quotient0.coeff 7 = quotient0Coefficient7 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_7 :
    remainder2.coeff 7 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_8 :
    remainder0.coeff 8 = Internal.selectionCofactorCoefficient8 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_8 :
    remainder1.coeff 8 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_8 :
    quotient0.coeff 8 = quotient0Coefficient8 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_8 :
    remainder2.coeff 8 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_9 :
    remainder0.coeff 9 = Internal.selectionCofactorCoefficient9 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_9 :
    remainder1.coeff 9 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_9 :
    quotient0.coeff 9 = quotient0Coefficient9 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_9 :
    remainder2.coeff 9 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_10 :
    remainder0.coeff 10 = Internal.selectionCofactorCoefficient10 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_10 :
    remainder1.coeff 10 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_10 :
    quotient0.coeff 10 = quotient0Coefficient10 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_10 :
    remainder2.coeff 10 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_11 :
    remainder0.coeff 11 = Internal.selectionCofactorCoefficient11 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_11 :
    remainder1.coeff 11 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_11 :
    quotient0.coeff 11 = quotient0Coefficient11 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_11 :
    remainder2.coeff 11 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_12 :
    remainder0.coeff 12 = Internal.selectionCofactorCoefficient12 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_12 :
    remainder1.coeff 12 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_12 :
    quotient0.coeff 12 = quotient0Coefficient12 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_12 :
    remainder2.coeff 12 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_13 :
    remainder0.coeff 13 = Internal.selectionCofactorCoefficient13 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_13 :
    remainder1.coeff 13 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_13 :
    quotient0.coeff 13 = quotient0Coefficient13 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_13 :
    remainder2.coeff 13 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_14 :
    remainder0.coeff 14 = Internal.selectionCofactorCoefficient14 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_14 :
    remainder1.coeff 14 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_14 :
    quotient0.coeff 14 = quotient0Coefficient14 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_14 :
    remainder2.coeff 14 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_15 :
    remainder0.coeff 15 = Internal.selectionCofactorCoefficient15 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_15 :
    remainder1.coeff 15 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_15 :
    quotient0.coeff 15 = quotient0Coefficient15 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_15 :
    remainder2.coeff 15 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_16 :
    remainder0.coeff 16 = Internal.selectionCofactorCoefficient16 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_16 :
    remainder1.coeff 16 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_16 :
    quotient0.coeff 16 = quotient0Coefficient16 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_16 :
    remainder2.coeff 16 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_17 :
    remainder0.coeff 17 = Internal.selectionCofactorCoefficient17 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_17 :
    remainder1.coeff 17 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_17 :
    quotient0.coeff 17 = quotient0Coefficient17 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_17 :
    remainder2.coeff 17 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_18 :
    remainder0.coeff 18 = Internal.selectionCofactorCoefficient18 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_18 :
    remainder1.coeff 18 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_18 :
    quotient0.coeff 18 = quotient0Coefficient18 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_18 :
    remainder2.coeff 18 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_19 :
    remainder0.coeff 19 = Internal.selectionCofactorCoefficient19 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_19 :
    remainder1.coeff 19 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_19 :
    quotient0.coeff 19 = quotient0Coefficient19 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_19 :
    remainder2.coeff 19 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_20 :
    remainder0.coeff 20 = Internal.selectionCofactorCoefficient20 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_20 :
    remainder1.coeff 20 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_20 :
    quotient0.coeff 20 = quotient0Coefficient20 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_20 :
    remainder2.coeff 20 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_21 :
    remainder0.coeff 21 = Internal.selectionCofactorCoefficient21 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_21 :
    remainder1.coeff 21 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_21 :
    quotient0.coeff 21 = quotient0Coefficient21 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_21 :
    remainder2.coeff 21 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_22 :
    remainder0.coeff 22 = Internal.selectionCofactorCoefficient22 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_22 :
    remainder1.coeff 22 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_22 :
    quotient0.coeff 22 = quotient0Coefficient22 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_22 :
    remainder2.coeff 22 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_23 :
    remainder0.coeff 23 = Internal.selectionCofactorCoefficient23 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_23 :
    remainder1.coeff 23 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_23 :
    quotient0.coeff 23 = quotient0Coefficient23 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_23 :
    remainder2.coeff 23 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_24 :
    remainder0.coeff 24 = Internal.selectionCofactorCoefficient24 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_24 :
    remainder1.coeff 24 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_24 :
    quotient0.coeff 24 = quotient0Coefficient24 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_24 :
    remainder2.coeff 24 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_25 :
    remainder0.coeff 25 = Internal.selectionCofactorCoefficient25 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_25 :
    remainder1.coeff 25 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_25 :
    quotient0.coeff 25 = quotient0Coefficient25 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_25 :
    remainder2.coeff 25 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_26 :
    remainder0.coeff 26 = Internal.selectionCofactorCoefficient26 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_26 :
    remainder1.coeff 26 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_26 :
    quotient0.coeff 26 = quotient0Coefficient26 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_26 :
    remainder2.coeff 26 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_27 :
    remainder0.coeff 27 = Internal.selectionCofactorCoefficient27 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_27 :
    remainder1.coeff 27 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_27 :
    quotient0.coeff 27 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_27 :
    remainder2.coeff 27 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_28 :
    remainder0.coeff 28 = Internal.selectionCofactorCoefficient28 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_28 :
    remainder1.coeff 28 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_28 :
    quotient0.coeff 28 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_28 :
    remainder2.coeff 28 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_29 :
    remainder0.coeff 29 = Internal.selectionCofactorCoefficient29 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_29 :
    remainder1.coeff 29 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_29 :
    quotient0.coeff 29 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_29 :
    remainder2.coeff 29 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_30 :
    remainder0.coeff 30 = Internal.selectionCofactorCoefficient30 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_30 :
    remainder1.coeff 30 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_30 :
    quotient0.coeff 30 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_30 :
    remainder2.coeff 30 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_31 :
    remainder0.coeff 31 = Internal.selectionCofactorCoefficient31 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_31 :
    remainder1.coeff 31 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_31 :
    quotient0.coeff 31 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_31 :
    remainder2.coeff 31 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_32 :
    remainder0.coeff 32 = Internal.selectionCofactorCoefficient32 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_32 :
    remainder1.coeff 32 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_32 :
    quotient0.coeff 32 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_32 :
    remainder2.coeff 32 = 0 := by
  simp [remainder2, outerTerm]

@[simp] private theorem remainder0_coeff_33 :
    remainder0.coeff 33 = Internal.selectionCofactorCoefficient33 := by
  simp [remainder0, selectionCofactorData]

@[simp] private theorem remainder1_coeff_33 :
    remainder1.coeff 33 = 0 := by
  simp [remainder1, divisionCofactorData0]

@[simp] private theorem quotient0_coeff_33 :
    quotient0.coeff 33 = 0 := by
  simp [quotient0, outerTerm]

@[simp] private theorem remainder2_coeff_33 :
    remainder2.coeff 33 = 0 := by
  simp [remainder2, outerTerm]


private lemma quotient0_degree : quotient0.natDegree ≤ 26 := by
  unfold quotient0 outerTerm
  compute_degree

private lemma remainder2_degree : remainder2.natDegree ≤ 6 := by
  unfold remainder2 outerTerm
  compute_degree

private lemma recurrence0_left_degree :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).natDegree ≤ 33 := by
  unfold remainder0
  compute_degree
  exact selectionCofactorData_degree

private lemma recurrence0_right_degree :
    (remainder1 * quotient0 +
      Polynomial.C exceptional0 * remainder2).natDegree ≤ 33 := by
  have hdivision := divisionCofactorData0_degree
  have hquotient := quotient0_degree
  have hremainder := remainder2_degree
  unfold remainder1
  compute_degree
  omega

private theorem recurrence0Coefficient0 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 0 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 0 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner0]

private theorem recurrence0Coefficient1 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 1 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 1 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner1]

private theorem recurrence0Coefficient2 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 2 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 2 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner2]
  ring

private theorem recurrence0Coefficient3 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 3 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 3 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner3]
  ring

private theorem recurrence0Coefficient4 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 4 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 4 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner4]
  ring

private theorem recurrence0Coefficient5 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 5 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 5 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner5]
  ring

private theorem recurrence0Coefficient6 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 6 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 6 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner6]
  ring

private theorem recurrence0Coefficient7 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 7 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 7 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner7]
  ring

private theorem recurrence0Coefficient8 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 8 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 8 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner8]
  ring

private theorem recurrence0Coefficient9 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 9 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 9 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner9]
  ring

private theorem recurrence0Coefficient10 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 10 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 10 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner10]
  ring

private theorem recurrence0Coefficient11 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 11 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 11 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner11]
  ring

private theorem recurrence0Coefficient12 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 12 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 12 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner12]
  ring

private theorem recurrence0Coefficient13 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 13 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 13 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner13]
  ring

private theorem recurrence0Coefficient14 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 14 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 14 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner14]
  ring

private theorem recurrence0Coefficient15 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 15 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 15 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner15]
  ring

private theorem recurrence0Coefficient16 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 16 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 16 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner16]
  ring

private theorem recurrence0Coefficient17 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 17 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 17 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner17]
  ring

private theorem recurrence0Coefficient18 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 18 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 18 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner18]
  ring

private theorem recurrence0Coefficient19 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 19 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 19 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner19]
  ring

private theorem recurrence0Coefficient20 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 20 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 20 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner20]
  ring

private theorem recurrence0Coefficient21 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 21 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 21 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner21]
  ring

private theorem recurrence0Coefficient22 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 22 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 22 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner22]
  ring

private theorem recurrence0Coefficient23 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 23 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 23 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner23]
  ring

private theorem recurrence0Coefficient24 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 24 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 24 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner24]
  ring

private theorem recurrence0Coefficient25 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 25 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 25 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner25]
  ring

private theorem recurrence0Coefficient26 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 26 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 26 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner26]
  ring

private theorem recurrence0Coefficient27 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 27 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 27 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner27]
  ring

private theorem recurrence0Coefficient28 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 28 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 28 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner28]
  ring

private theorem recurrence0Coefficient29 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 29 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 29 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner29]
  ring

private theorem recurrence0Coefficient30 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 30 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 30 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner30]
  ring

private theorem recurrence0Coefficient31 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 31 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 31 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner31]
  ring

private theorem recurrence0Coefficient32 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 32 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 32 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner32]

private theorem recurrence0Coefficient33 :
    (Polynomial.C ((remainder1.coeff 7) ^ 27) *
      remainder0).coeff 33 =
        (remainder1 * quotient0 +
          Polynomial.C exceptional0 * remainder2).coeff 33 := by
  rw [show remainder1.coeff 7 = 1 by simp [remainder1]]
  norm_num [Polynomial.coeff_mul, Finset.antidiagonal]
  rw [recurrence0Inner33]


theorem recurrence0_checked : recurrence0 := by
  unfold recurrence0
  apply Polynomial.ext
  intro degree
  by_cases hdegree : degree ≤ 33
  · interval_cases degree
    · exact recurrence0Coefficient0
    · exact recurrence0Coefficient1
    · exact recurrence0Coefficient2
    · exact recurrence0Coefficient3
    · exact recurrence0Coefficient4
    · exact recurrence0Coefficient5
    · exact recurrence0Coefficient6
    · exact recurrence0Coefficient7
    · exact recurrence0Coefficient8
    · exact recurrence0Coefficient9
    · exact recurrence0Coefficient10
    · exact recurrence0Coefficient11
    · exact recurrence0Coefficient12
    · exact recurrence0Coefficient13
    · exact recurrence0Coefficient14
    · exact recurrence0Coefficient15
    · exact recurrence0Coefficient16
    · exact recurrence0Coefficient17
    · exact recurrence0Coefficient18
    · exact recurrence0Coefficient19
    · exact recurrence0Coefficient20
    · exact recurrence0Coefficient21
    · exact recurrence0Coefficient22
    · exact recurrence0Coefficient23
    · exact recurrence0Coefficient24
    · exact recurrence0Coefficient25
    · exact recurrence0Coefficient26
    · exact recurrence0Coefficient27
    · exact recurrence0Coefficient28
    · exact recurrence0Coefficient29
    · exact recurrence0Coefficient30
    · exact recurrence0Coefficient31
    · exact recurrence0Coefficient32
    · exact recurrence0Coefficient33
  · have hdegree' : 33 < degree := Nat.lt_of_not_ge hdegree
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt recurrence0_left_degree hdegree')]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt recurrence0_right_degree hdegree')]

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

end

theorem solution :
MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0 := by
  exact MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.recurrence0_checked

#print axioms solution
