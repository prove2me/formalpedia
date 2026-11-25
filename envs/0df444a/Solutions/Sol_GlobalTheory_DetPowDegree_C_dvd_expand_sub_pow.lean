-- Prove2me | solution 1 for GlobalTheory.DetPowDegree.C_dvd_expand_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:06.837144+00:00
-- url     : https://prove2.me/submissions/0d3b0102-78e1-4f66-878b-a2b147356282

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
open GlobalTheory GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
variable {l : ℤ} {L E : ℕ}
namespace GlobalTheory.DetPowDegree
theorem _root_.solution {σ : Type} (l i : ℕ) (hl : l.Prime) (f : MvPolynomial σ ℤ) :
    MvPolynomial.C (l : ℤ) ∣ expand (l ^ i) f - f ^ (l ^ i) := by
  haveI := Fact.mk hl
  rw [C_dvd_iff_zmod, map_sub, map_expand, map_pow, sub_eq_zero]
  generalize map (Int.castRingHom (ZMod l)) f = g
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_comm, expand_mul, ih, expand_zmod, ← pow_mul, mul_comm]
end GlobalTheory.DetPowDegree
