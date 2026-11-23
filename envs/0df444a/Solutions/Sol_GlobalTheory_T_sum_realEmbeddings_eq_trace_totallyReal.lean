-- Prove2me | solution 1 for GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:57.365689+00:00
-- url     : https://prove2.me/submissions/3ef5dfcf-46fa-439c-916d-acd805c6abac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyReal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Theorems.Thm_GlobalTheory_HilbFam_sum_realEmb_eq_trace


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : F), ∑ i : Emb F, ((i y : ℝ) : ℂ) = ((Algebra.trace ℚ F y : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HilbFam.sum_realEmb_eq_trace | exact GlobalTheory.HilbFam.sum_realEmb_eq_trace | (intros; apply GlobalTheory.HilbFam.sum_realEmb_eq_trace <;> assumption)
end _root_.GlobalTheory.T
