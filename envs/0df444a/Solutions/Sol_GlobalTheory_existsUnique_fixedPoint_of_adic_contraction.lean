-- Prove2me | solution 1 for GlobalTheory.existsUnique_fixedPoint_of_adic_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:21.02182+00:00
-- url     : https://prove2.me/submissions/c67645fd-1d32-4716-ad93-fd4a764f1a3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_eq_of_forall_sub_mem_ideal_pow
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X


attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_C

set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S τ ι : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory
theorem _root_.solution (J : Ideal S) [IsAdicComplete J S]
    (T : (ι → S) → ι → S)
    (hT : ∀ n x y, (∀ i, x i - y i ∈ J ^ n) → ∀ i, T x i - T y i ∈ J ^ (n + 1)) :
    ∃! x, T x = x := by
  have hit : ∀ n x y i, T^[n] x i - T^[n] y i ∈ J ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y) i
  have hc : ∀ i, ∃ L : S, ∀ n, T^[n] 0 i - L ∈ J ^ n := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => T^[n] 0 i) fun {m n} hmn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [SModEq.sub_mem, Function.iterate_add_apply]
      simpa using hit m 0 _ i
    exact ⟨L, fun n => by simpa [SModEq.sub_mem] using hL n⟩
  choose L hL using hc
  refine ⟨L, funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_, fun y hy => ?_⟩
  · have h1 := hT n _ _ (fun i => hL i n) i
    have h2 := hL i (n + 1)
    rw [Function.iterate_succ_apply'] at h2
    have := sub_mem h2 h1
    refine Ideal.pow_le_pow_right n.le_succ ?_
    convert this using 1
    ring
  · refine funext fun i => eq_of_forall_sub_mem_ideal_pow J fun n => ?_
    have h1 := hit n y 0 i
    rw [Function.iterate_fixed hy] at h1
    simpa using add_mem h1 (hL i n)
end GlobalTheory
