-- Prove2me | solution 1 for GlobalTheory.FlowProgramme.optimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:17:20.084232+00:00
-- url     : https://prove2.me/submissions/ed832b45-588e-4c2b-95c3-ede853e7ace6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CyclicSolvable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory GlobalTheory.FlowProgramme
namespace GlobalTheory.FlowProgramme
theorem _root_.solution (l d : ℕ) [NeZero d] (X : ZMod d → ℝ) (hl : 2 ≤ l) (hX : ∀ a, 0 ≤ X a) :
    ∃ x : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a) ∧ ∀ x' : ZMod d → ℕ → ℝ, ((∀ a i, 0 ≤ x' a i) ∧ (∀ a i, x' a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x' a i + ∑ i ∈ Finset.range d, x' (a - i) i ≤ X a) →
      ∑ a, ∑ i ∈ Finset.range d, x' a i ≤ ∑ a, ∑ i ∈ Finset.range d, x a i := by
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) ≤ l := by linarith
  let S : Set (ZMod d → ℕ → ℝ) := {x | ((∀ a i, 0 ≤ x a i) ∧ (∀ a i, x a i ≠ 0 → Odd i ∧ i < d) ∧ ∀ a, ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i + ∑ i ∈ Finset.range d, x (a - i) i ≤ X a)}
  have hclosed : IsClosed S := by
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun a => isClosed_iInter fun i =>
        isClosed_le continuous_const (by fun_prop)
    · refine isClosed_iInter fun a => isClosed_iInter fun i => ?_
      by_cases h : Odd i ∧ i < d
      · convert isClosed_univ
        ext x
        simp [h]
      · have hc : IsClosed {x : ZMod d → ℕ → ℝ | x a i = 0} :=
          isClosed_eq (by fun_prop) continuous_const
        convert hc
        tauto
    · exact isClosed_iInter fun a => isClosed_le (by fun_prop) continuous_const
  have hK : IsCompact (Set.pi Set.univ fun a : ZMod d =>
      Set.pi Set.univ fun _ : ℕ => Set.Icc (0 : ℝ) (X a)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_Icc
  have hS : IsCompact S := by
    refine hK.of_isClosed_subset hclosed ?_
    rintro x ⟨h0, h1, h2⟩ a - i -
    refine ⟨h0 a i, ?_⟩
    by_cases h : x a i = 0
    · rw [h]; exact hX a
    · have hi := Finset.mem_range.2 (h1 a i h).2
      have e1 : (l : ℝ) ^ i * x a i ≤ ∑ i ∈ Finset.range d, (l : ℝ) ^ i * x a i :=
        Finset.single_le_sum (f := fun i => (l : ℝ) ^ i * x a i)
          (fun j _ => mul_nonneg (by positivity) (h0 a j)) hi
      have e2 : 0 ≤ ∑ i ∈ Finset.range d, x (a - i) i := Finset.sum_nonneg fun j _ => h0 _ j
      have e3 : x a i ≤ (l : ℝ) ^ i * x a i := le_mul_of_one_le_left (h0 a i) (one_le_pow₀ hl1)
      have := h2 a
      linarith
  have hne : S.Nonempty := ⟨fun _ _ => 0, fun _ _ => le_rfl, fun _ _ h => absurd rfl h,
    fun a => by simpa using hX a⟩
  obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne
    (f := fun x => ∑ a, ∑ i ∈ Finset.range d, x a i) (Continuous.continuousOn (by fun_prop))
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩
end GlobalTheory.FlowProgramme
