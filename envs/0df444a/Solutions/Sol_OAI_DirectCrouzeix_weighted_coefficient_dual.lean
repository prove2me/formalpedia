-- Prove2me | solution 1 for OAI.DirectCrouzeix.weighted_coefficient_dual
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:51:36.581578+00:00
-- url     : https://prove2.me/submissions/c103b4f9-7e9a-4f73-86bb-a735e3797dbb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Duality.lean:L15-L46
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.weighted_coefficient_dual. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

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

-- ---- from OAI.Analysis.DirectCrouzeix.HilbertSchmidt ----
namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_smul {ι : Type u_16} {κ : Type u_17} [Fintype ι] [Fintype κ]
    (c : ℂ) (M : Matrix ι κ ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul,
    mul_pow, Finset.mul_sum]

theorem entryPair_conj {ι : Type u_20} {κ : Type u_21} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : entryPair M (M.map star) = (hsSq M : ℂ) := by
  simp only [entryPair, Matrix.map_apply, hsSq_eq_sum_norm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

theorem hsSq_map_star {ι : Type u_22} {κ : Type u_23} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq (M.map star) = hsSq M := by
  simp [hsSq_eq_sum_norm_sq]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.SingularPairs ----
namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem entryPair_smul_right {ι : Type u_39} {κ : Type u_40} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) (c : ℂ) : entryPair M (c • C) = c * entryPair M C := by
  simp [entryPair, Finset.mul_sum, mul_left_comm]

end DirectCrouzeix

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.Duality ----
namespace OAI

universe u_41 u_42 u_43 u_44 u_45

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem weighted_coefficient_dual {ρ : Type u_41} {ι : Type u_42} {κ : Type u_43}
    [Fintype ρ] [Fintype ι] [Fintype κ]
    (P : ρ → Matrix ι κ ℂ) (w : ρ → ℝ) (hw : ∀ k, 0 < w k)
    (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ C : ρ → Matrix ι κ ℂ,
      ‖∑ k, entryPair (P k) (C k)‖ ^ 2 ≤ b * ∑ k, w k * hsSq (C k)) :
    (∑ k, hsSq (P k) / w k) ≤ b := by
  let C : ρ → Matrix ι κ ℂ := fun k => ((w k : ℂ)⁻¹) • (P k).map star
  let s : ℝ := ∑ k, hsSq (P k) / w k
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => div_nonneg (hsSq_nonneg _) (hw k).le)
  have hp : (∑ k, entryPair (P k) (C k)) = (s : ℂ) := by
    simp only [C, entryPair_smul_right, entryPair_conj, s, Complex.ofReal_sum,
      Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv]
    ring
  have he : (∑ k, w k * hsSq (C k)) = s := by
    apply Finset.sum_congr rfl
    intro k _
    simp only [C, hsSq_smul, hsSq_map_star, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hw k)]
    field_simp
  have ht := h C
  rw [hp, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs] at ht
  by_cases hs0 : s = 0
  · change s ≤ b
    simpa [hs0] using hb
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    change s ≤ b
    apply (mul_le_mul_iff_left₀ hspos).mp
    nlinarith

open MeasureTheory

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.weighted_coefficient_dual := @_root_.OAI.DirectCrouzeix.weighted_coefficient_dual
