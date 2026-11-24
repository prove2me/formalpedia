-- Prove2me | solution 1 for GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:56.970341+00:00
-- url     : https://prove2.me/submissions/a98d2cd6-fd61-441f-9bde-6db210d81aac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussSumMulGaussSumInvOfIsPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
open GlobalTheory GlobalTheory.GaussInt
namespace GlobalTheory.GaussInt
theorem _root_.solution {K : Type} [Field K] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter K N} {ψ : AddChar (ZMod N) K} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : K) := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  rw [Finset.sum_eq_single (1 : ZMod N)]
  · simp
  · intro a _ ha
    simp [ha]
  · simp
end GlobalTheory.GaussInt
