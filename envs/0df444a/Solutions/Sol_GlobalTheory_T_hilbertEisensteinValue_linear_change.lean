-- Prove2me | solution 1 for GlobalTheory.T.hilbertEisensteinValue_linear_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:04.491671+00:00
-- url     : https://prove2.me/submissions/36b3b3ef-9a99-4f94-bb34-a6f731bd666d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Theorems.Thm_GlobalTheory_HilbFam_gval_linear_change


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, coord b a x i = lam i * coord b' a' (T x) i) → gval k L b a = (∏ i, lam i)⁻¹ ^ k * gval k L' b' a' := by
  first | exact @GlobalTheory.HilbFam.gval_linear_change | exact GlobalTheory.HilbFam.gval_linear_change | (intros; apply GlobalTheory.HilbFam.gval_linear_change <;> assumption)
end _root_.GlobalTheory.T
