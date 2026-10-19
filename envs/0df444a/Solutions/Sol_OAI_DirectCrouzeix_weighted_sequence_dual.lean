-- Prove2me | solution 1 for OAI.DirectCrouzeix.weighted_sequence_dual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:53:24.395092+00:00
-- url     : https://prove2.me/submissions/b976bea6-508e-44bf-aed2-82a328fea07d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/BoundaryEnergy.lean:L112-L133
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.weighted_sequence_dual. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Theorems.Thm_OAI_DirectCrouzeix_weighted_coefficient_dual

-- ---- from OAI.Analysis.DirectCrouzeix.PositiveBlocks ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_nonneg {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : 0 ≤ hsSq M := by
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg).1

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.BoundaryEnergy ----
namespace OAI

universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

theorem faberWeight_pos (k : ℕ) : 0 < faberWeight k := by
  unfold faberWeight
  split <;> norm_num

theorem weighted_sequence_dual {ι : Type u_85} {κ : Type u_86} [Fintype ι] [Fintype κ]
    (P : ℕ → Matrix ι κ ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ N (C : Fin N → Matrix ι κ ℂ),
      ‖∑ k : Fin N, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k : Fin N, faberWeight k * hsSq (C k)) :
    hsSq (P 0) + (1/2 : ℝ) * ∑' n : ℕ, hsSq (P (n+1)) ≤ b := by
  have hsum : ∀ N, ∑ k ∈ Finset.range N, hsSq (P k) / faberWeight k ≤ b := by
    intro N
    have hh := weighted_coefficient_dual (fun k : Fin N => P k)
      (fun k => faberWeight k) (fun k => faberWeight_pos k) b hb (h N)
    rw [← Fin.sum_univ_eq_sum_range (fun k => hsSq (P k) / faberWeight k)]
    exact hh
  have hnon : ∀ k, 0 ≤ hsSq (P k) / faberWeight k :=
    fun k => div_nonneg (hsSq_nonneg _) (faberWeight_pos k).le
  have hsumm : Summable (fun k => hsSq (P k) / faberWeight k) :=
    summable_of_sum_range_le hnon hsum
  have hh := Real.tsum_le_of_sum_range_le hnon hsum
  rw [hsumm.tsum_eq_zero_add] at hh
  have hw0 : faberWeight 0 = 1 := by simp [faberWeight]
  have hw (n : ℕ) : faberWeight (n+1) = 2 := by simp [faberWeight]
  simp only [hw0,hw,div_one] at hh
  rw [tsum_div_const] at hh
  convert hh using 1 ; ring

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.weighted_sequence_dual := @_root_.OAI.DirectCrouzeix.weighted_sequence_dual
