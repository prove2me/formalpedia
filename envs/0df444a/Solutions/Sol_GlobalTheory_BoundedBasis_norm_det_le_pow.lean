-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.norm_det_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:21.726303+00:00
-- url     : https://prove2.me/submissions/59ceb322-0eb3-4103-9cfb-7ce52186fd8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, ‖M i k‖ ≤ b) : ‖M.det‖ ≤ (r * b) ^ r := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := b) h
  rw [Fintype.card_fin, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  rw [mul_pow]
  gcongr
  exact_mod_cast Nat.factorial_le_pow r
end GlobalTheory.BoundedBasis
