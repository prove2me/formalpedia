-- Prove2me | solution 1 for OAI.Erdos3.affineComparisonAccuracy_gram
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:01:04.575432+00:00
-- url     : https://prove2.me/submissions/dc145dd1-65ac-460d-acc1-ae316ccfc3d3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B010
import Theorems.Thm_OAI_Erdos3_affineComparisonAccuracy_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_exp_neg_div_eight {A B : ℝ} (hAB : B + 4 ≤ A) :
    Real.exp (-A) ≤ Real.exp (-B) / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 4 := by
    calc
      8 ≤ (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp (-(B + 4)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 4 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h8

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem lowDegreeCoordinateSets_card (b : ℕ) :
    (lowDegreeCoordinateSets I b).card = ∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j := by
  rw [lowDegreeCoordinateSets, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem lowDegreeCoordinateSets_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) (j : ℕ) :
    ((lowDegreeCoordinateSets ι j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + 1)) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (j + 1)) :
      ((Fintype.card ι).choose k : ℝ) ≤ Real.exp ((j : ℝ) * P) := by
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ (Fintype.card ι : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow (Fintype.card ι) k
      _ ≤ (Real.exp P) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount k
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hP)
  rw [lowDegreeCoordinateSets_card, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ Finset.range (j + 1), Real.exp ((j : ℝ) * P) := Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * Real.exp ((j : ℝ) * P) := by simp
    _ ≤ Real.exp j * Real.exp ((j : ℝ) * P) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineResidueAccuracy
namespace OAI

section

namespace Erdos3

theorem affineComparisonAccuracy_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P L T : ℝ} (b : ℕ) (hP : 0 ≤ P) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    2 * affineComparisonAccuracy b P L T * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + affineComparisonAccuracy b P L T) ^ 2 ≤ Real.exp (-T) := by
  let η := affineComparisonAccuracy b P L T
  have he := affineComparisonAccuracy_bounds (level := Real.exp (-L)) b hP hL hT le_rfl
  have hη0 : 0 < η := he.1
  have hη1 : η < 1 := he.2.1
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have hc2 : ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 ≤
      Real.exp (2 * (b : ℝ) * (P + 1)) := by
    calc
      _ ≤ (Real.exp ((b : ℝ) * (P + 1))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp4 : (4 : ℝ) ^ b ≤ Real.exp (2 * (b : ℝ)) := by
    exact (pow_le_pow_left₀ (by norm_num) hfour b).trans_eq (by rw [← Real.exp_nat_mul]; congr 1; ring)
  have hsq : (1 + η) ^ 2 ≤ 4 := by nlinarith
  have hsmall : η ≤ Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8 := by
    apply exp_neg_le_exp_neg_div_eight
    unfold affineComparisonAccuracyLog
    have hp : 0 ≤ (P + 3) ^ 3 := by positivity
    linarith
  change 2 * η * _ ^ 2 * _ ^ b * (1 + η) ^ 2 ≤ _
  calc
    _ ≤ 2 * η * Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ)) * 4 := by gcongr
    _ = 8 * η * (Real.exp (2 * (b : ℝ) * (P + 1)) * Real.exp (2 * (b : ℝ))) := by ring
    _ = 8 * η * Real.exp (2 * (b : ℝ) * (P + 2)) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ 8 * (Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) / 8) * Real.exp (2 * (b : ℝ) * (P + 2)) := by gcongr
    _ = Real.exp (-(2 * (b : ℝ) * (P + 2) + T)) * Real.exp (2 * (b : ℝ) * (P + 2)) := by ring
    _ = Real.exp (-T) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affineComparisonAccuracy_gram.{u_1} := @OAI.Erdos3.affineComparisonAccuracy_gram.{u_1}
