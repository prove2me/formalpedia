-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LatticeCount.summable_of_lattice_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:17.07741+00:00
-- url     : https://prove2.me/submissions/a4ec2453-ebc5-4c7d-9ff3-97de6ce3c5ec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOfLatticeDecay
import Theorems.Thm_GlobalTheory_CompanionTheory_LatticeCount_summable_prod_inv_one_add_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LatticeCount
namespace GlobalTheory.CompanionTheory.LatticeCount
theorem _root_.solution (ι : Type) (d : ℕ) (w : ι → ℂ) (f : ι → Fin d → ℝ)
    (hf : Function.Injective f) (N : ℕ) (hN : 0 < N) (C : ℝ)
    (hC : ∀ i, ‖w i‖ * ∏ k, (1 + f i k ^ 2) ≤ C)
    (hint : ∀ i, w i ≠ 0 → ∀ k, ∃ n : ℤ, (N : ℝ) * f i k = n) : Summable w := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let S := {i // w i ≠ 0}
  choose n hn using fun i : S => hint i.1 i.2
  have hinj : Function.Injective n := by
    intro a b hab
    apply Subtype.ext
    apply hf
    funext k
    have h1 := hn a k
    have h2 := hn b k
    rw [hab] at h1
    exact mul_left_cancel₀ hNpos.ne' (h1.trans h2.symm)
  have hg := ((summable_prod_inv_one_add_sq d).comp_injective hinj).mul_left (((N : ℝ) ^ 2) ^ d * C)
  have hbound : ∀ a : S, ‖w a.1‖ ≤ ((N : ℝ) ^ 2) ^ d * C *
      ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)⁻¹ := by
    intro a
    have hle : ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) ≤
        ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) := by
      have : ((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2) =
          ∏ k : Fin d, ((N : ℝ) ^ 2 * (1 + f a.1 k ^ 2)) := by
        rw [Finset.prod_mul_distrib]; simp
      rw [this]
      refine Finset.prod_le_prod (fun k _ => by positivity) (fun k _ => ?_)
      rw [← hn a k]
      have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hpos : (0 : ℝ) < ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2) :=
      Finset.prod_pos (fun k _ => by positivity)
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖w a.1‖ * ∏ k, ((1 : ℝ) + (n a k : ℝ) ^ 2)
        ≤ ‖w a.1‖ * (((N : ℝ) ^ 2) ^ d * ∏ k, (1 + f a.1 k ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ((N : ℝ) ^ 2) ^ d * (‖w a.1‖ * ∏ k, (1 + f a.1 k ^ 2)) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ d * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hsub : Summable (w ∘ (Subtype.val : S → ι)) :=
    Summable.of_norm_bounded hg hbound
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).1 hsub
  intro x hx
  by_contra h0
  exact hx ⟨⟨x, h0⟩, rfl⟩
end GlobalTheory.CompanionTheory.LatticeCount
