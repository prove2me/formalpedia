-- Prove2me | solution 2 for OAI.Problem313.low_degree_influence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:05:53.262536+00:00
-- url     : https://prove2.me/submissions/960fba49-4310-44e3-9a3c-cc18202b3324

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegreeInfluence.lean:L43-L89
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.low_degree_influence_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegreeInfluence ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- Summing pivotal-event three-halves powers using a uniform influence bound. -/
theorem sum_mul_sqrt_le {ι : Type u} [Fintype ι] (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : ∀ i, a i ≤ B) :
    (∑ i, a i * Real.sqrt (a i)) ≤ Real.sqrt B * ∑ i, a i := by
  calc
    (∑ i, a i * Real.sqrt (a i)) ≤ ∑ i, a i * Real.sqrt B := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hB i)) (ha i)
    _ = Real.sqrt B * ∑ i, a i := by rw [Finset.mul_sum]; congr 1; ext i; ring

/-- A convenient conversion between real three-halves powers and square roots. -/
theorem rpow_three_halves_eq_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    x ^ (3/2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  convert Real.rpow_add_of_nonneg hx (show (0:ℝ) ≤ 1 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) using 1 <;> norm_num

/-- The small-total-influence regime turns the individual influence bound into a power of `m`. -/
theorem sqrt_influence_ratio_le (m I : ℝ) (hm : 0 < m)
    (hI : I ≤ m ^ (1/4 : ℝ)) :
    Real.sqrt (I/m) ≤ m ^ (-3/8 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Real.rpow_nonneg hm.le _, ?_⟩
  have hsq : (m ^ (-3/8 : ℝ))^2 = m ^ (-3/4 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsq]
  calc
    I/m ≤ m ^ (1/4 : ℝ) / m := div_le_div_of_nonneg_right hI hm.le
    _ = m ^ (-3/4 : ℝ) := by
      convert (Real.rpow_sub hm (1/4 : ℝ) 1).symm using 1 <;> norm_num

/-- The numerical case split at the end of the low-degree Fourier estimate.
The factor `A` can be instantiated with `σ²`. -/
theorem low_degree_influence_bound {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hL1 : L ≤ 1)
    (hprojection : L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hI0 : 0 ≤ I := by rw [← hsum]; exact Finset.sum_nonneg fun i _ => ha i
  have hpow0 : 0 ≤ m ^ (1/16 : ℝ) := Real.rpow_nonneg hmpos.le _
  by_cases hsmall : I ≤ m ^ (1/4 : ℝ)
  · have hsum_bound : (∑ i, (a i) ^ (3/2 : ℝ)) ≤ m ^ (-3/8 : ℝ) * I := by
      calc
        (∑ i, (a i) ^ (3/2 : ℝ)) = ∑ i, a i * Real.sqrt (a i) := by
          apply Finset.sum_congr rfl
          intro i _
          exact rpow_three_halves_eq_mul_sqrt (a i) (ha i)
        _ ≤ Real.sqrt (I/m) * I := by
          simpa [hsum] using sum_mul_sqrt_le a (I/m) ha hindividual
        _ ≤ m ^ (-3/8 : ℝ) * I := mul_le_mul_of_nonneg_right
          (sqrt_influence_ratio_le m I hmpos hsmall) hI0
    have hcoefficient : A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤ m ^ (-1/4 : ℝ) := by
      calc
        A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) ≤
            m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (by simpa using mul_le_mul_of_nonneg_right hA1 hpow0)
            (Real.rpow_nonneg hmpos.le _)
        _ = m ^ (-5/16 : ℝ) := by rw [← Real.rpow_add hmpos]; norm_num
        _ ≤ m ^ (-1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
    calc
      L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ) := hprojection
      _ ≤ A * m ^ (1/16 : ℝ) * (m ^ (-3/8 : ℝ) * I) :=
        mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg hA0 hpow0)
      _ = (A * m ^ (1/16 : ℝ) * m ^ (-3/8 : ℝ)) * I := by ring
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_right hcoefficient hI0
  · have hinverse : m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) = 1 := by
      rw [← Real.rpow_add hmpos]
      norm_num
    calc
      L ≤ 1 := hL1
      _ = m ^ (-1/4 : ℝ) * m ^ (1/4 : ℝ) := hinverse.symm
      _ ≤ m ^ (-1/4 : ℝ) * I := mul_le_mul_of_nonneg_left
        (le_of_lt (lt_of_not_ge hsmall)) (Real.rpow_nonneg hmpos.le _)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution.{u} : type_of% @_root_.OAI.Problem313.low_degree_influence_bound.{u} := @_root_.OAI.Problem313.low_degree_influence_bound.{u}
