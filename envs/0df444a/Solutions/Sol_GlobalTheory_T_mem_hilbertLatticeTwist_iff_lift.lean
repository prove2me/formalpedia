-- Prove2me | solution 1 for GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:41.74187+00:00
-- url     : https://prove2.me/submissions/c6d1059d-859b-4150-81a9-0326e866403f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Theorems.Thm_GlobalTheory_HilbFam_TwistMem_mem_twist_iff


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F), L ≤ stdLat F → (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔ ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  first | exact @GlobalTheory.HilbFam.TwistMem.mem_twist_iff | exact GlobalTheory.HilbFam.TwistMem.mem_twist_iff | (intros; apply GlobalTheory.HilbFam.TwistMem.mem_twist_iff <;> assumption)
end _root_.GlobalTheory.T
