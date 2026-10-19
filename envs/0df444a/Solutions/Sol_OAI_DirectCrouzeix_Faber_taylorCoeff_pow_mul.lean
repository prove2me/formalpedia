-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:14:54.93558+00:00
-- url     : https://prove2.me/submissions/ecdad8e3-86df-4785-90d5-87387066362f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/TaylorFourier.lean:L55-L79
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul. The node keeps its source
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem taylorCoeff_pow_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (j k : ℕ) :
    taylorCoeff (fun u => u^j*f u) k = if j ≤ k then taylorCoeff f (k-j) else 0 := by
  classical
  rw [taylorCoeff,iteratedDeriv_fun_mul (f := fun u : ℂ => u^j) (n := k) (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero]
  by_cases hjk : j ≤ k
  · rw [Finset.sum_eq_single j]
    · simp only [ite_true,smul_eq_mul,ite_eq_left hjk,taylorCoeff]
      have hfac : (k.factorial : ℂ) = (k.choose j : ℂ) * (j.factorial : ℂ) * ((k-j).factorial : ℂ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
      have hkn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      have hjn : ((k-j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp
      linear_combination -(iteratedDeriv (k-j) f 0)*hfac
    · intro i hi hij
      simp [hij]
    · exact fun h => (h (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))).elim
  · rw [ite_eq_right hjk]
    have he : ∑ i ∈ Finset.range (k+1), (k.choose i : ℂ) *
        (if i = j then (j.factorial : ℂ) else 0) * iteratedDeriv (k-i) f 0 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hij : i ≠ j := by have hik := Finset.mem_range.mp hi; omega
      simp [hij]
    rw [he,smul_zero]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul := @_root_.OAI.DirectCrouzeix.Faber.taylorCoeff_pow_mul
