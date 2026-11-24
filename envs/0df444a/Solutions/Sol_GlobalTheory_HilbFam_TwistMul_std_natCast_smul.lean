-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMul.std_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:36.223891+00:00
-- url     : https://prove2.me/submissions/003bbf4e-72cf-459b-8b7f-32ba2a1dd874

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMul

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
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMul
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMul
theorem _root_.solution (N : ℕ) {y : Fin 2 → F} (hy : y ∈ stdLat F) : (N : F) • y ∈ stdLat F := by
  rw [Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ N hy
end GlobalTheory.HilbFam.TwistMul
