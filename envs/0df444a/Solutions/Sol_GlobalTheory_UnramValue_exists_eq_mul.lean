-- Prove2me | solution 1 for GlobalTheory.UnramValue.exists_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:47:47.077738+00:00
-- url     : https://prove2.me/submissions/926ccd1e-8343-4a14-9bf0-ab4cf0ba23c3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Theorems.Thm_GlobalTheory_UnramValue_isClosed_rootRing
import Theorems.Thm_GlobalTheory_UnramValue_pow_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.UnramValue
theorem _root_.solution {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h1 : ‖y‖ < 1) : ∃ z ∈ rootRing l m, y = l * z := by
  have hp : l.Prime := Fact.out
  have hN1 : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.2 hm).ne' hp.one_lt
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have step : ∀ j : ℕ, ∃ w ∈ rootRing l m, y ^ ((l ^ m.totient) ^ j) = y + l * w := by
    intro j
    induction j with
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | succ j ih =>
      obtain ⟨w, hw, hwe⟩ := ih
      obtain ⟨z, hz, hze⟩ := pow_sub_mem hl (pow_mem hy ((l ^ m.totient) ^ j))
      refine ⟨w + z, add_mem hw hz, ?_⟩
      rw [pow_succ, pow_mul, hze, hwe]
      ring
  have hmem : ∀ j : ℕ, (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)) ∈ rootRing l m := by
    intro j
    obtain ⟨w, hw, hwe⟩ := step j
    have e : (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)) = -w := by
      rw [hwe, sub_add_cancel_left, mul_neg, inv_mul_cancel_left₀ hl0]
    rw [e]
    exact neg_mem hw
  have ht : Filter.Tendsto (fun j : ℕ => (l : Om l)⁻¹ * (y - y ^ ((l ^ m.totient) ^ j)))
      Filter.atTop (nhds ((l : Om l)⁻¹ * (y - 0))) := by
    have h0 : Filter.Tendsto (fun j : ℕ => y ^ ((l ^ m.totient) ^ j)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).comp
        (tendsto_pow_atTop_atTop_of_one_lt hN1)
    exact (tendsto_const_nhds.sub h0).const_mul _
  have hz := (isClosed_rootRing hm).mem_of_tendsto ht (Filter.Eventually.of_forall hmem)
  rw [sub_zero] at hz
  exact ⟨(l : Om l)⁻¹ * y, hz, (mul_inv_cancel_left₀ hl0 y).symm⟩
end GlobalTheory.UnramValue
