-- Prove2me | solution 1 for GlobalTheory.UnRep.SplitRep.mix_mul_mix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:04.619838+00:00
-- url     : https://prove2.me/submissions/0f63e166-f928-464d-a880-faf09b6a133c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
import Theorems.Thm_GlobalTheory_UnRep_SplitRep_mix_val
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Idele_smul_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep.SplitRep
namespace _root_.GlobalTheory.UnRep.SplitRep
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε)
    (hε' : (1 - ε) * (1 - ε) = 1 - ε) (κ : GL (Fin n) R) :
    (_root_.GlobalTheory.UnRep.SplitRep.mix ε hε κ).1 * (_root_.GlobalTheory.UnRep.SplitRep.mix (1 - ε) hε' κ).1 = κ.1 := by
  rw [_root_.GlobalTheory.UnRep.SplitRep.mix_val, _root_.GlobalTheory.UnRep.SplitRep.mix_val]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
  linear_combination (norm := module) hε • ((2 : R) • κ.1 - κ.1 * κ.1 - 1)
end _root_.GlobalTheory.UnRep.SplitRep
end GlobalTheory.UnRep.SplitRep
