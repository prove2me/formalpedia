-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:37.978911+00:00
-- url     : https://prove2.me/submissions/18314f62-4615-48aa-abdd-a4f95831f463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivial
import Theorems.Thm_GlobalTheory_RankFibreKer_minor_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k) :
    Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by
  rintro ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have m1 : minor Z J = 1 := by rw [minor, hJ, det_one]
  have m1' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have e1 : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, m1', map_one]
  have hg : valuation k (g.val.det) ≤ 1 := by
    have := (hgZ J).1
    rwa [minor_mul, m1, mul_one] at this
  have hZJ' : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') := e1.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hg zero_le'
      _ = valuation k (minor Z J') := one_mul _
  have hg1 : valuation k (g.val.det) = 1 := by rwa [hZJ', mul_one] at e1
  have hJJ : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hZJ']; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have := (hgZ J).2 h
      rw [minor_mul, m1, mul_one, hg1] at this
      exact absurd this (lt_irrefl _)
  subst hJJ
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j; simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'
end GlobalTheory.RankFibreKer
