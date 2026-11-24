-- Prove2me | solution 1 for GlobalTheory.MajPosCpx.gram_sub_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:53:21.358277+00:00
-- url     : https://prove2.me/submissions/1de87bec-6625-40a7-8549-647d13b25df1

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
theorem _root_.solution {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by
  ext i j; rw [← hR]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
end GlobalTheory.MajPosCpx
