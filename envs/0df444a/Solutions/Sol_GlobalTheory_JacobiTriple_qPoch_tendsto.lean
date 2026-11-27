-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.qPoch_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:32.723809+00:00
-- url     : https://prove2.me/submissions/c38a1ecd-ebe9-44a1-858f-1c595951b88e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution (t : ℂ) (ht : ‖t‖ < 1) :
    Filter.Tendsto (qPoch t) Filter.atTop (nhds (qPochInf t)) ∧ qPochInf t ≠ 0 ∧
      ∀ m, qPoch t m ≠ 0 := by
  have hg : Summable (fun i : ℕ => ‖t‖ * ‖t‖ ^ i) :=
    (summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left ‖t‖
  have hsum : Summable (fun i : ℕ => ‖-(t ^ (i + 1))‖) :=
    hg.congr (fun i => by rw [norm_neg, norm_pow, pow_succ, mul_comm])
  have hne : ∀ i : ℕ, 1 + -(t ^ (i + 1)) ≠ 0 := by
    intro i h
    have h1 : t ^ (i + 1) = 1 := by linear_combination -h
    have h2 : ‖t‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg t) ht (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hm := multipliable_one_add_of_summable hsum
  have h0 := tprod_one_add_ne_zero_of_summable hne hsum
  simp only [← sub_eq_add_neg] at hm h0 hne
  refine ⟨hm.hasProd.tendsto_prod_nat, h0, fun m => Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)⟩
end GlobalTheory.JacobiTriple
