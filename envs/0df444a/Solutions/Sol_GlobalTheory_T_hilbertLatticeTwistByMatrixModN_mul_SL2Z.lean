-- Prove2me | solution 1 for GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul_SL2Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:41.817513+00:00
-- url     : https://prove2.me/submissions/1ee5215f-2e03-486f-86ae-b47ae6e0f710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2Z
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2ZStatement
import Theorems.Thm_GlobalTheory_HilbFam_TwistSL_twist_mul_sl


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  first | exact @GlobalTheory.HilbFam.TwistSL.twist_mul_sl | exact GlobalTheory.HilbFam.TwistSL.twist_mul_sl | (intros; apply GlobalTheory.HilbFam.TwistSL.twist_mul_sl <;> assumption)
end _root_.GlobalTheory.T
