-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.isSB_mul_chr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:05.91471+00:00
-- url     : https://prove2.me/submissions/2ca50dd1-d7d8-41cf-a713-4b7ae91170d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_chr_add
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_intM_nsmul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_exists_den
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_chr_eq_one

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
theorem _root_.solution {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) (y : Matrix κ ι ℚ) :
    IsSB (fun x => φ x * chr y x) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨N, hN, hy⟩ := exists_den y
  refine ⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩
  · have := intM_nsmul N (h1 x (left_ne_zero_of_mul hx))
    rwa [smul_smul, ← Nat.cast_mul] at this
  · have e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    have a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x := by rw [e1]; exact h2 x _ (intM_nsmul N hz)
    have a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x := by
      rw [chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]
    simp only [a1, a2]
end GlobalTheory.Phase.ShapeOps
