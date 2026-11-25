-- Prove2me | solution 1 for GlobalTheory.LegendreBounds.legendre_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:47:58.611169+00:00
-- url     : https://prove2.me/submissions/8811efd7-a181-4325-bb1b-c815ca1896e9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Theorems.Thm_GlobalTheory_LegendreBounds_lower
import Theorems.Thm_GlobalTheory_LegendreBounds_upper
import Theorems.Thm_GlobalTheory_LegendreBounds_upper_of_pos
import Theorems.Thm_GlobalTheory_LegendreBounds_padicValNat_prod_factorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds
namespace GlobalTheory.LegendreBounds
theorem _root_.solution :
  (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  intro l hl
  refine ⟨fun N hN => ⟨lower l hl N N hN le_rfl, upper_of_pos l hl N hN⟩, ?_, ?_⟩
  · intro κ _ A hA
    rw [padicValNat_prod_factorial l hl Finset.univ A]
    have key : ∀ j ∈ (Finset.univ : Finset κ), (A j : ℝ) / (l - 1) - (Real.logb l ((∑ i, A i : ℕ) : ℝ) + 1)
        ≤ padicValNat l (A j).factorial := fun j _ =>
      lower l hl (A j) (∑ i, A i) hA
        (Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j))
    have h := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div,
      ← Nat.cast_sum] at h
    linarith
  · intro n₀ x
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn
    · simp
    · have e1 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => x + c)
      have e2 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => c)
      rw [e1, e2, ← Finset.sum_sub_distrib]
      calc _ ≤ ∑ c ∈ Finset.range n₀, ((x : ℝ) / (l - 1) + (Real.logb l n₀ + 1)) :=
            Finset.sum_le_sum fun c hc => by
              have h1 := upper l hl (x + c)
              have h2 := lower l hl c n₀ hn (Finset.mem_range.mp hc).le
              push_cast at h1
              have h3 : ((x : ℝ) + c) / (l - 1) = x / (l - 1) + c / (l - 1) := add_div _ _ _
              linarith
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
end GlobalTheory.LegendreBounds
