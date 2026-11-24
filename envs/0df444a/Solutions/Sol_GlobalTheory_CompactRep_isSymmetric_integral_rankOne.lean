-- Prove2me | solution 1 for GlobalTheory.CompactRep.isSymmetric_integral_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:08.266509+00:00
-- url     : https://prove2.me/submissions/fc7d2db0-e694-4cc2-ae23-73c45aa716f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace
import Theorems.Thm_GlobalTheory_CompactRep_inner_integral_rankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory.CompactRep
theorem _root_.solution {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x,
    ← integral_conj]
  congr 1
  funext k
  rw [map_mul, inner_conj_symm, inner_conj_symm, mul_comm]
end GlobalTheory.CompactRep
