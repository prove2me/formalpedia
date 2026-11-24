-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_sum_eq_sum_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:55.059146+00:00
-- url     : https://prove2.me/submissions/bc65ed06-6d6f-4388-a80c-b2ec78575712

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinAndSumsSeparated
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Type*} [AddCommGroup X] {ι : Type*}
    (e : Basis ι ℤ X) {C : ℝ} (hC : 0 ≤ C) {N' D k : ℕ} (hN' : 2 * (D : ℝ) * C < N') (hk : k ≤ D)
    (α β : Fin k → X) (hα : ∀ j i, |(e.repr (α j) i : ℝ)| ≤ C)
    (hβ : ∀ j i, |(e.repr (β j) i : ℝ)| ≤ C) (w : X)
    (h : ∑ j, α j = ∑ j, β j + N' • w) : w = 0 := by
  refine e.repr.injective (Finsupp.ext fun i => ?_)
  have h1 : ∑ j, (e.repr (α j) i : ℝ) = ∑ j, (e.repr (β j) i : ℝ) + N' * (e.repr w i : ℝ) := by
    have := congrArg (fun x => e.repr x i) h
    simp only [map_add, map_sum, map_nsmul, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at this
    exact_mod_cast this
  have bound : ∀ γ : Fin k → X, (∀ j i, |(e.repr (γ j) i : ℝ)| ≤ C) →
      |∑ j, (e.repr (γ j) i : ℝ)| ≤ D * C := fun γ hγ => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hγ j i).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hC
  have hA := abs_le.1 (bound α hα)
  have hB := abs_le.1 (bound β hβ)
  have hpos : (0 : ℝ) < N' := lt_of_le_of_lt (by positivity) hN'
  have h2 : (e.repr w i : ℝ) < 1 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.2, hB.1]
  have h3 : (-1 : ℝ) < (e.repr w i : ℝ) := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.1 hc) hpos.le
    linarith [hA.1, hB.2]
  have h2' : e.repr w i < 1 := by exact_mod_cast h2
  have h3' : -1 < e.repr w i := by exact_mod_cast h3
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  omega
end GlobalTheory
