-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.sum_le_of_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:39.574889+00:00
-- url     : https://prove2.me/submissions/e6ccab0d-a978-49d5-a4e8-d347d4c26e7d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
open Classical
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution {α ι : Type} [Fintype ι] (a : α → ℝ) (φ : α → ι → ℤ)
    (g : ι → ℤ → ℝ) (K : ℕ) (ha : ∀ r, 0 ≤ a r) (hg : ∀ w k, 0 ≤ g w k)
    (hgs : ∀ w, Summable (g w)) (hle : ∀ r, a r ≤ ∏ w, g w (φ r w))
    (hfib : ∀ (T : Finset α) (n : ι → ℤ), (T.filter fun r => φ r = n).card ≤ K) :
    Summable a ∧ ∑' r, a r ≤ K * ∏ w, ∑' k, g w k := by
  have key : ∀ T : Finset α, ∑ r ∈ T, a r ≤ K * ∏ w, ∑' k, g w k := by
    intro T
    have hG : ∀ n : ι → ℤ, 0 ≤ ∏ w, g w (n w) :=
      fun n => Finset.prod_nonneg fun w _ => hg w _
    have s1 : ∑ r ∈ T, a r ≤ ∑ r ∈ T, ∏ w, g w (φ r w) := Finset.sum_le_sum fun r _ => hle r
    have s2 : ∑ r ∈ T, ∏ w, g w (φ r w)
        = ∑ n ∈ T.image φ, (T.filter fun r => φ r = n).card • ∏ w, g w (n w) :=
      Finset.sum_comp (fun n : ι → ℤ => ∏ w, g w (n w)) φ
    have s3 : ∑ n ∈ T.image φ, (T.filter fun r => φ r = n).card • ∏ w, g w (n w)
        ≤ ∑ n ∈ T.image φ, (K : ℝ) * ∏ w, g w (n w) := by
      refine Finset.sum_le_sum fun n _ => ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib T n) (hG n)
    have s4 : ∑ n ∈ T.image φ, ∏ w, g w (n w)
        ≤ ∑ n ∈ Fintype.piFinset (fun w => (T.image φ).image (fun n => n w)), ∏ w, g w (n w) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hG n
      intro n hn
      rw [Fintype.mem_piFinset]
      intro w
      exact Finset.mem_image_of_mem _ hn
    have s5 : ∑ n ∈ Fintype.piFinset (fun w => (T.image φ).image (fun n => n w)), ∏ w, g w (n w)
        ≤ ∏ w, ∑' k, g w k := by
      rw [← Finset.prod_univ_sum]
      refine Finset.prod_le_prod (fun w _ => Finset.sum_nonneg fun k _ => hg w k) fun w _ => ?_
      exact (hgs w).sum_le_tsum _ fun k _ => hg w k
    rw [← Finset.mul_sum] at s3
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    calc ∑ r ∈ T, a r ≤ _ := s1
      _ = _ := s2
      _ ≤ _ := s3
      _ ≤ _ := mul_le_mul_of_nonneg_left (s4.trans s5) hK
  have hsum : Summable a := summable_of_sum_le ha key
  exact ⟨hsum, hsum.tsum_le_of_sum_le key⟩
end GlobalTheory.CompanionTheory.SW.LatSum
