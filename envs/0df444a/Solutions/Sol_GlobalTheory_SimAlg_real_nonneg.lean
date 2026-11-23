-- Prove2me | solution 1 for GlobalTheory.SimAlg.real_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:53.545165+00:00
-- url     : https://prove2.me/submissions/b2981f44-3169-49b7-8d08-8528f2201f63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ) := by
  have hZ : ∀ c : Fin d → ℤ, 0 ≤ ∑ i, ∑ j, c i * c j * G i j := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · have := (hG c hc).le
      simp only [dotProduct, mulVec, Finset.mul_sum] at this
      refine this.trans_eq ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hQ : ∀ c : Fin d → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ) := by
    intro c
    obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) c
    choose a ha using hm
    have hm0 : ((m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero m
    have ha' : ∀ i, (a i : ℝ) = ((m : ℤ) : ℝ) * (c i : ℝ) := by
      intro i
      have := ha i
      simp only [eq_intCast, zsmul_eq_mul, Submonoid.smul_def] at this
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ) := by
      exact_mod_cast hZ a
    have h2 : ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ)
        = ((m : ℤ) : ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ) := by
      simp only [Finset.mul_sum, ha']
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hd : DenseRange (Pi.map fun (_ : Fin d) => ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x : Fin d → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ)) x ?_ hQ
  exact isClosed_le continuous_const (by fun_prop)
end GlobalTheory.SimAlg
