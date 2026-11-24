-- Prove2me | solution 1 for GlobalTheory.T.iteratedPartialDeriv_const_mul_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:16:11.712089+00:00
-- url     : https://prove2.me/submissions/8fa866ad-316d-4ed2-b798-be4418e8ebd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindex
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Theorems.Thm_GlobalTheory_HilbFam_iterD_const_mul_reindex


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
theorem _root_.solution : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  first | exact @GlobalTheory.HilbFam.iterD_const_mul_reindex | exact GlobalTheory.HilbFam.iterD_const_mul_reindex | (intros; apply GlobalTheory.HilbFam.iterD_const_mul_reindex <;> assumption)
end _root_.GlobalTheory.T
