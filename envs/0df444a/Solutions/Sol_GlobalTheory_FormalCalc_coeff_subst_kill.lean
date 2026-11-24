-- Prove2me | solution 1 for GlobalTheory.FormalCalc.coeff_subst_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:26:16.633403+00:00
-- url     : https://prove2.me/submissions/9410c201-fcaf-4b34-9afe-1b972e1bf57b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Sum
variable {σ τ ι κ μ A : Type*} [CommRing A]
open Classical
namespace GlobalTheory.FormalCalc
theorem _root_.solution (e : ι → κ) {b : κ → MvPowerSeries κ A} (hb0 : ∀ i, b (e i) = 0)
    (hb1 : ∀ k, k ∉ Set.range e → b k = X k) (f : MvPowerSeries κ A) (α : κ →₀ ℕ) :
    coeff α (subst b f) = if ∀ i, α (e i) = 0 then coeff α f else 0 := by
  have hb : b = (fun k => if k ∈ Set.range e then (0 : A) else 1) • X := by
    funext k
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hk
      simp [hb0]
    · simp only [Pi.smul_apply', hb1 k hk, if_neg hk, one_smul]
  rw [hb, ← rescale_eq_subst, coeff_rescale]
  split_ifs with h
  · rw [Finsupp.prod, Finset.prod_eq_one, one_mul]
    intro k hk
    rw [if_neg, one_pow]
    rintro ⟨i, rfl⟩
    exact Finsupp.mem_support_iff.mp hk (h i)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi), zero_mul]
    rw [if_pos ⟨i, rfl⟩, zero_pow hi]
end GlobalTheory.FormalCalc
