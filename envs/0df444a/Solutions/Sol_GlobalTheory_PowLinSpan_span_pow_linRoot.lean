-- Prove2me | solution 1 for GlobalTheory.PowLinSpan.span_pow_linRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:26.986065+00:00
-- url     : https://prove2.me/submissions/c76d81e9-f8cb-45ee-aed9-c9906447ec7c

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots
import Theorems.Thm_GlobalTheory_PowLinSpan_eval_polOf
import Theorems.Thm_GlobalTheory_PowLinSpan_degreeOf_polOf_le
import Theorems.Thm_GlobalTheory_PowLinSpan_homog_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.PowLinSpan
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace GlobalTheory.PowLinSpan
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N d : ℕ) (Q : MvPolynomial (ι × Fin N) ℝ),
    Q.IsHomogeneous d →
    Q ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) '' {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := by
  intro ι _ _ N d Q hQ
  by_contra hnot
  obtain ⟨φ, hφQ, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ u : ι → Fin N → ℝ, (∀ τ, StrictAnti (u τ)) →
      φ ((∑ x : ι × Fin N, C (u x.1 x.2) * X x) ^ d) = 0 := by
    intro u hu
    have hmem : Formalism.DegreeFormula.linRoot u ^ d ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) ''
        {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := Submodule.subset_span ⟨u, hu, rfl⟩
    have h0 : φ (Formalism.DegreeFormula.linRoot u ^ d) = 0 := by
      have := Submodule.mem_map_of_mem (f := φ) hmem
      rw [hφ] at this
      simpa using this
    rw [Formalism.DegreeFormula.linRoot, neg_pow] at h0
    rcases neg_one_pow_eq_or (MvPolynomial (ι × Fin N) ℝ) d with h | h <;> rw [h] at h0
    · simpa using h0
    · simpa using h0
  have hP : polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (polOf φ d)
      (fun x => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ) - (x.2 : ℝ) * (d + 1))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective]
      · simpa using Nat.lt_succ_of_le (degreeOf_polOf_le φ d x)
      · intro a b hab
        simpa using hab
    · intro v hv
      rw [eval_polOf]
      have := hkill (fun τ i => v (τ, i)) ?_
      · simpa using this
      intro τ i j hij
      obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp (hv (τ, i))
      obtain ⟨b, hb, hvb⟩ := Finset.mem_image.mp (hv (τ, j))
      simp only [Finset.mem_range] at ha hb
      have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
        exact_mod_cast this
      have hb' : (b : ℝ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.mp hb
      have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      show v (τ, j) < v (τ, i)
      rw [← hva, ← hvb]
      simp only
      nlinarith
  exact hφQ (homog_kill φ d hP Q hQ)
end GlobalTheory.PowLinSpan
