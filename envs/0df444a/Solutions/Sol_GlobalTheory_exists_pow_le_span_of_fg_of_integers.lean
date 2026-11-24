-- Prove2me | solution 1 for GlobalTheory.exists_pow_le_span_of_fg_of_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:47.206705+00:00
-- url     : https://prove2.me/submissions/5ca56200-27aa-48ce-9391-20260359351e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {C : Type*} [Field C] {v : Valuation C NNReal}
    {O : Type*} [CommRing O] [Algebra O C] (hv : v.Integers O) {J : Ideal O} (hJ : J.FG)
    (hJ' : J ≠ ⊤) {a : O} (ha : v (algebraMap O C a) ≠ 0) :
    ∃ n : ℕ, J ^ n ≤ Ideal.span {a} := by
  classical
  obtain ⟨S, rfl⟩ := hJ
  set r : NNReal := S.sup fun s => v (algebraMap O C s) with hr
  have hr1 : r < 1 := by
    rw [hr, Finset.sup_lt_iff (by simp)]
    intro s hs
    refine lt_of_le_of_ne (hv.map_le_one s) fun h => hJ' ?_
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hs) (hv.isUnit_of_one' h)
  have hS : ∀ x ∈ Ideal.span (S : Set O), v (algebraMap O C x) ≤ r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Finset.le_sup (f := fun s => v (algebraMap O C s)) hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, map_mul, map_mul]
      exact (mul_le_of_le_one_left' (hv.map_le_one c)).trans hx
  have hpow : ∀ n : ℕ, ∀ x ∈ (Ideal.span (S : Set O)) ^ n, v (algebraMap O C x) ≤ r ^ n := by
    intro n
    induction n with
    | zero => intro x _; simpa using hv.map_le_one x
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
      · rw [map_mul, map_mul, pow_succ]
        exact mul_le_mul' (ih y hy) (hS z hz)
      · rw [map_add]; exact v.map_add_le hy hz
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one (pos_iff_ne_zero.mpr ha) hr1
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.mem_span_singleton]
  exact hv.dvd_of_le ((hpow n x hx).trans hn.le)
end GlobalTheory
