-- Prove2me | solution 1 for GlobalTheory.ReducedBasisBound.conj_entry_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:07.790278+00:00
-- url     : https://prove2.me/submissions/78066653-c24c-44d3-af70-240ed833309c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound
variable {N : ℕ} {C₁ Cm T : ℝ} {a : Fin N → ℝ} {n m Z : Matrix (Fin N) (Fin N) ℝ}
namespace GlobalTheory.ReducedBasisBound
theorem _root_.solution (hC : 1 ≤ C₁) (ha : ∀ i, 0 < a i) (hle : ∀ i j, i ≤ j → a i ≤ C₁ * a j)
    (hnm : n * m = 1) (hn_low : ∀ i j, j < i → n i j = 0) (hm_low : ∀ i j, j < i → m i j = 0)
    (M' : Matrix (Fin N) (Fin N) ℤ)
    (h2 : diagonal a * n * M'.map (Int.cast : ℤ → ℝ) = Zᵀ * diagonal a * n)
    (ε : ℝ) (hA : ∀ i j, a i ≤ ε * a j → M' j i = 0) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ * C₁ ^ 2 = ε) :
    ∀ i j, a i ≤ δ * a j → Z i j = 0 := by
  intro i j hij
  have hC0 : 0 ≤ C₁ := by linarith
  have h := congrArg (· * m) h2
  simp only [Matrix.mul_assoc] at h
  rw [hnm, Matrix.mul_one] at h
  have e := congrFun (congrFun h j) i
  rw [diagonal_mul, mul_diagonal, transpose_apply] at e
  have hz : (n * (M'.map (Int.cast : ℤ → ℝ) * m)) j i = 0 := by
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro p _
    rcases lt_or_ge p j with hp | hp
    · rw [hn_low j p hp, zero_mul]
    · have hin : (M'.map (Int.cast : ℤ → ℝ) * m) p i = 0 := by
        rw [mul_apply]
        apply Finset.sum_eq_zero
        intro q _
        rcases lt_or_ge i q with hq | hq
        · rw [hm_low q i hq, mul_zero]
        · have hq' : a q ≤ ε * a p := by
            calc a q ≤ C₁ * a i := hle q i hq
              _ ≤ C₁ * (δ * a j) := by gcongr
              _ ≤ C₁ * (δ * (C₁ * a p)) := by gcongr; exact hle j p hp
              _ = ε * a p := by rw [← hδ]; ring
          rw [Matrix.map_apply, hA q p hq']
          simp
      rw [hin, mul_zero]
  rw [hz, mul_zero] at e
  exact (mul_eq_zero.mp e.symm).resolve_right (ne_of_gt (ha i))
end GlobalTheory.ReducedBasisBound
