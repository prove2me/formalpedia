-- Prove2me | solution 1 for GlobalTheory.WittGauss.weight_add_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:04:47.479138+00:00
-- url     : https://prove2.me/submissions/134eafe1-1850-4f0c-8f46-c61eab577cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
import Theorems.Thm_GlobalTheory_WittGauss_weight_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))
include hb h0 h1 hm ha
namespace GlobalTheory.WittGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (n : ℕ) (hx : ∀ i ≤ n, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i ≤ n, a (y.coeff i) ≤ c ^ p ^ i) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by
  have key : ∀ z : WittVector p R, (∀ i ≤ n, a (z.coeff i) ≤ c ^ p ^ i) →
      ∃ z' : WittVector p R, truncate (n + 1) z = truncate (n + 1) z' ∧
        ∀ i, a (z'.coeff i) ≤ c ^ p ^ i := by
    intro z hz
    refine ⟨WittVector.mk p fun i => if i ≤ n then z.coeff i else 0, ?_, fun i => ?_⟩
    · ext i
      rw [coeff_truncate, coeff_truncate, WittVector.coeff_mk, if_pos (Nat.lt_succ_iff.1 i.2)]
    · rw [WittVector.coeff_mk]
      split_ifs with h
      · exact hz i h
      · simpa [h0] using pow_nonneg hc _
  obtain ⟨x', hx1, hx2⟩ := key x hx
  obtain ⟨y', hy1, hy2⟩ := key y hy
  have h : truncate (n + 1) (x + y) = truncate (n + 1) (x' + y') := by
    rw [map_add, map_add, hx1, hy1]
  have h2 := congrArg (TruncatedWittVector.coeff (Fin.last n)) h
  rw [coeff_truncate, coeff_truncate, Fin.val_last] at h2
  rw [h2]
  exact weight_add a hb h0 h1 hm ha p c hc x' y' hx2 hy2 n
end GlobalTheory.WittGauss
