-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.cast_sign_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:51:39.431783+00:00
-- url     : https://prove2.me/submissions/e8794270-7ae1-4aa7-9dc3-30b2e99b7ff6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : A) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) * x = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • x := by
  rw [Int.cast_smul_eq_zsmul, zsmul_eq_mul]
end GlobalTheory.QuantumMinorAdjacentSwap
