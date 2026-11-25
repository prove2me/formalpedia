-- Prove2me | solution 1 for GlobalTheory.T.hilbertLatticeTwist_hasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:44.95442+00:00
-- url     : https://prove2.me/submissions/96c5636a-ed37-4d05-8037-b0e55865b6ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistHasLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistHasLevelStatement
import Theorems.Thm_GlobalTheory_HilbFam_hasLevel_twist_of_hasLevel


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)), HasLevel N L → HasLevel N (twist N L α) := by
  first | exact @GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | exact GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel | (intros; apply GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel <;> assumption)
end _root_.GlobalTheory.T
