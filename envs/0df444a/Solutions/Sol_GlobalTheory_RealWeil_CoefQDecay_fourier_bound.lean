-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.fourier_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:03.976685+00:00
-- url     : https://prove2.me/submissions/dc7205c6-dda0-4753-a3ad-7fbbc1bc0dee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_contDiff_prodTrans
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integrable_prodTrans
import Theorems.Thm_GlobalTheory_RealWeil_CoefQDecay_integral_prodTrans_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}
namespace GlobalTheory.RealWeil.CoefQDecay
theorem _root_.solution (g g' : Sch (Fin n)) (p ξ : EuclideanSpace ℝ (Fin n)) (N m : ℕ) (hm : m ≤ N) :
    ‖ξ‖ ^ m * ‖𝓕 (prodTrans g g' p) ξ‖ ≤
      2 ^ m * ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x := by
  have h'f : ∀ (k' m' : ℕ), (k' : ℕ∞) ≤ 0 → (m' : ℕ∞) ≤ (m : ℕ∞) →
      Integrable (fun v => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m' (prodTrans g g' p) v‖) := by
    intro k' m' hk' _
    have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
    subst hk0
    simpa using integrable_prodTrans g g' p m'
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := prodTrans g g' p) (K := 0)
    (N := m) ((contDiff_prodTrans g g' p).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := m)
    le_rfl le_rfl ξ
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
      ∫ v, ‖v‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (prodTrans g g' p) v‖)
      = ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ := by
    rw [Finset.sum_product]; simp
  rw [hsum, norm_iteratedFDeriv_zero] at key
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
  refine key.trans ?_
  gcongr
  calc ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖
      ≤ ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x :=
        Finset.sum_le_sum fun j _ => integral_prodTrans_le g g' p j
end GlobalTheory.RealWeil.CoefQDecay
