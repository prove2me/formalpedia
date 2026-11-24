-- Prove2me | solution 1 for GlobalTheory.MajPosCpx.mul_submatrix_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:53:22.174635+00:00
-- url     : https://prove2.me/submissions/a88dd725-49df-495a-930d-07bc1a79a566

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexWittBasisNormalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory GlobalTheory.MajPosCpx
namespace GlobalTheory.MajPosCpx
theorem _root_.solution {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by
  ext i j; simp [Matrix.mul_apply]
end GlobalTheory.MajPosCpx
