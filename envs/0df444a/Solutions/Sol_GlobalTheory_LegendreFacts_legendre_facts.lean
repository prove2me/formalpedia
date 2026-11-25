-- Prove2me | solution 1 for GlobalTheory.LegendreFacts.legendre_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:55.287796+00:00
-- url     : https://prove2.me/submissions/b3bac6e5-0197-4f7b-bba6-68186579bd32

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Theorems.Thm_GlobalTheory_LegendreFacts_mfact_eq_prod
import Theorems.Thm_P2M_GlobalTheory_LegendreFacts_degree_eq_sum__2b1d5d1ba054
import Theorems.Thm_GlobalTheory_LegendreBounds_digitSum_le
import Theorems.Thm_GlobalTheory_LegendreBounds_legendre_bounds
import Theorems.Thm_GlobalTheory_LegendreBounds_legendre_real
import Theorems.Thm_GlobalTheory_LegendreBounds_padicValNat_prod_factorial
import Theorems.Thm_GlobalTheory_LegendreBounds_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
namespace GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds
private lemma padicValNat_factorial_eq_div_of_lt_sq (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : N < l ^ 2) :
    padicValNat l N.factorial = N / l := by
  have : Fact l.Prime := ⟨hl⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hpos.ne' hN)]
    simp
end GlobalTheory.LegendreFacts
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreFacts
theorem _root_.solution : F2 := by
  intro l hl
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hden : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    have h := legendre_real l hl N
    simpa using h
  · intro N _
    have h := digitSum_le l N hl.one_lt
    rw [Real.natFloor_logb_natCast]
    have hc : (((Nat.digits l N).sum : ℕ) : ℝ) ≤ (((Nat.log l N + 1) * (l - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hl.one_lt.le, Nat.cast_add, Nat.cast_one] at hc
    rw [mul_comm]
    exact hc
  · intro σ _ A hA
    rw [mfact_eq_prod, degree_eq_sum']
    rw [degree_eq_sum'] at hA
    constructor
    · have h := ((legendre_bounds l hl).2.1) σ (fun j => A j) hA
      simpa using h
    · rw [padicValNat_prod_factorial l hl Finset.univ (fun j => A j)]
      have hterm : ∀ j ∈ (Finset.univ : Finset σ),
          (padicValNat l (A j).factorial : ℝ) ≤ (A j : ℝ) / ((l : ℝ) - 1) :=
        fun j _ => upper l hl (A j)
      calc ∑ j, (padicValNat l (A j).factorial : ℝ)
          ≤ ∑ j, (A j : ℝ) / ((l : ℝ) - 1) := Finset.sum_le_sum hterm
        _ = ((∑ j, A j : ℕ) : ℝ) / ((l : ℝ) - 1) := by
          rw [← Finset.sum_div]
          push_cast
          rfl
  · intro N hN
    exact padicValNat_factorial_eq_div_of_lt_sq l hl N hN
end GlobalTheory.LegendreFacts
