-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.chr_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:25:54.512121+00:00
-- url     : https://prove2.me/submissions/160b2d7a-cf60-4b86-b711-244206047a65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_IsMu_mul
import Theorems.Thm_GlobalTheory_Phase_Ph_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {y z : Matrix κ ι ℚ} {N : ℕ} (hy : IntM ((N : ℚ) • y)) (hz : IntM z) :
    chr y ((N : ℚ) • z) = 1 := by
  have h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k) := by
    refine IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_
    have := (hz k i).mul (hy k i)
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    convert this using 1; ring
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  unfold chr
  rw [← hn, mul_comm]
  simp only [eq_intCast, Rat.cast_intCast]
  exact Complex.exp_int_mul_two_pi_mul_I _
end GlobalTheory.Phase.ShapeOps
