-- Prove2me | solution 1 for GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:37.521394+00:00
-- url     : https://prove2.me/submissions/9dec3d49-ffee-4808-82e9-a40a8f81f196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulStatement
import Theorems.Thm_GlobalTheory_HilbFam_TwistMul_twist_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  first | exact @GlobalTheory.HilbFam.TwistMul.twist_twist | exact GlobalTheory.HilbFam.TwistMul.twist_twist | (intros; apply GlobalTheory.HilbFam.TwistMul.twist_twist <;> assumption)
end _root_.GlobalTheory.T
