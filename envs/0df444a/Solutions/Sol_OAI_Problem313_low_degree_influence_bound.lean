-- Prove2me | solution 1 for OAI.Problem313.low_degree_influence_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:05:13.873924+00:00
-- url     : https://prove2.me/submissions/388edf55-e0e6-47df-a663-4d005c102f49

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

open OAI OAI.Problem313
universe u


theorem solution {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I A L : ℝ)
    (hm : 1 ≤ m) (ha : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = I) (hindividual : ∀ i, a i ≤ I/m)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hL1 : L ≤ 1)
    (hprojection : L ≤ A * m ^ (1/16 : ℝ) * ∑ i, (a i) ^ (3/2 : ℝ)) :
    L ≤ m ^ (-1/4 : ℝ) * I := by
  have hm0 : 0 < m := by linarith
  have hI : 0 ≤ I := hsum ▸ Finset.sum_nonneg (fun i _ => ha i)
  have hS : ∑ i, (a i)^(3/2:ℝ) ≤ I * (I/m)^(1/2:ℝ) := by
    have : ∀ i, (a i)^(3/2:ℝ) ≤ a i * (I/m)^(1/2:ℝ) := by
      intro i
      rw [show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add' (ha i) (by norm_num), Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ha i) (hindividual i) (by norm_num)) (ha i)
    calc _ ≤ ∑ i, a i * (I/m)^(1/2:ℝ) := Finset.sum_le_sum (fun i _ => this i)
      _ = I * (I/m)^(1/2:ℝ) := by rw [← Finset.sum_mul, hsum]
  by_cases hc : I ≤ m^(3/8:ℝ)
  · have h1 : (I/m)^(1/2:ℝ) ≤ m^(-5/16:ℝ) := by
      calc (I/m)^(1/2:ℝ) ≤ (m^(3/8:ℝ)/m)^(1/2:ℝ) :=
            Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hc hm0.le) (by norm_num)
        _ = m^(-5/16:ℝ) := by rw [← Real.rpow_sub_one hm0.ne', ← Real.rpow_mul hm0.le]; norm_num
    have h2 : m^(1/16:ℝ) * m^(-5/16:ℝ) = m^(-1/4:ℝ) := by rw [← Real.rpow_add hm0]; norm_num
    have hpos1 : 0 ≤ m^(1/16:ℝ) := by positivity
    calc L ≤ A * m^(1/16:ℝ) * ∑ i, (a i)^(3/2:ℝ) := hprojection
      _ ≤ 1 * m^(1/16:ℝ) * (I * m^(-5/16:ℝ)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hA1 hpos1)
            (hS.trans (mul_le_mul_of_nonneg_left h1 hI))
            (Finset.sum_nonneg (fun i _ => by have := ha i; positivity)) (by positivity)
      _ = m^(-1/4:ℝ) * I := by rw [← h2]; ring
  · push_neg at hc
    have h3 : 1 ≤ m^(-1/4:ℝ) * m^(3/8:ℝ) := by
      rw [← Real.rpow_add hm0]; exact Real.one_le_rpow hm (by norm_num)
    have : m^(-1/4:ℝ) * m^(3/8:ℝ) ≤ m^(-1/4:ℝ) * I := mul_le_mul_of_nonneg_left hc.le (by positivity)
    linarith

