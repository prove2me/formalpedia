-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:28:49.752989+00:00
-- url     : https://prove2.me/submissions/a6ae5d08-4e23-4c16-a496-e7830b852ae0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierDerivative.lean:L67-L108
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.RussoReindex ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

variable {ι : Type u} [DecidableEq ι]

variable [Fintype ι]

/-- Splitting a finite Boolean cube at one coordinate. -/
theorem sum_bool_split (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x, g x) = ∑ z : {j : ι // j ≠ i} → Bool,
      (g (russoInsert i true z) + g (russoInsert i false z)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp g]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  rfl

/-- The product excluding a coordinate does not depend on that coordinate. -/
theorem prod_erase_russoInsert (p : ℝ) (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j ∈ Finset.univ.erase i, if russoInsert i b z j = true then p else 1-p) =
    ∏ j ∈ Finset.univ.erase i, if russoInsert i c z j = true then p else 1-p := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hji]

/-- A Bernoulli weight factors at a chosen coordinate. -/
theorem prod_russoInsert (p : ℝ) (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    (∏ j, if russoInsert i b z j = true then p else 1-p) =
    (if b = true then p else 1-p) *
      ∏ j ∈ Finset.univ.erase i, if russoInsert i false z j = true then p else 1-p := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if russoInsert i b z j = true then p else 1-p) (Finset.mem_univ i)]
  rw [prod_erase_russoInsert p i b false]
  simp

/-- Discrete integration by parts for a centered Bernoulli coordinate. -/
theorem sum_weight_centered_coordinate (p : ℝ) (i : ι) (g : (ι → Bool) → ℝ) :
    (∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) * g x *
      ((if x i = true then (1 : ℝ) else 0) - p)) =
    p * (1-p) * ∑ x : ι → Bool, (∏ j, if x j = true then p else 1-p) *
      (g (Function.update x i true) - g (Function.update x i false)) := by
  rw [sum_bool_split i, sum_bool_split i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [russoInsert_self, update_russoInsert, prod_russoInsert,
    Bool.false_eq_true, ↓reduceIte]
  ring

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.FourierDerivative ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

private theorem char_update_aux (p : ℝ) (S : Finset ι) (i : ι) (hi : i ∉ S)
    (x : ι → Bool) (b : Bool) : char p S (Function.update x i b) = char p S x := by
  unfold char
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]

variable [Fintype ι]

/-- Fourier coefficients of a coordinate derivative, with the same full cube on both sides. -/
theorem coeff_insert_eq_sqrt_mul_delta {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (A : Finset ι) (hi : i ∉ A) :
    coeff p g (insert i A) =
      Real.sqrt (p * (1-p)) * coeff p (delta i g) A := by
  classical
  have hpos : 0 < p * (1-p) := mul_pos hp (sub_pos.mpr hp1)
  have hs : Real.sqrt (p * (1-p)) ^ 2 = p * (1-p) := Real.sq_sqrt hpos.le
  have hn : Real.sqrt (p * (1-p)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hc := Problem313.sum_weight_centered_coordinate p i (fun x => g x * char p A x)
  have hcenter :
      (∑ x, weight p x * (g x * char p A x) *
        ((if x i = true then (1 : ℝ) else 0)-p)) =
      p * (1-p) * coeff p (delta i g) A := by
    calc
      _ = p * (1-p) * ∑ x, weight p x *
          (g (Function.update x i true) * char p A (Function.update x i true) -
           g (Function.update x i false) * char p A (Function.update x i false)) := hc
      _ = _ := by
        congr 1
        unfold coeff
        apply Finset.sum_congr (by ext; simp)
        intro x hx
        rw [char_update_aux p A i hi, char_update_aux p A i hi]
        unfold delta
        ring
  apply mul_left_cancel₀ hn
  calc
    Real.sqrt (p * (1-p)) * coeff p g (insert i A) =
        ∑ x, weight p x * (g x * char p A x) *
          ((if x i = true then (1 : ℝ) else 0)-p) := by
      rw [coeff, Finset.mul_sum]
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      rw [char, Finset.prod_insert hi]
      change Real.sqrt (p * (1-p)) *
        (weight p x * g x * (chi p (x i) * char p A x)) = _
      unfold chi
      field_simp
    _ = p * (1-p) * coeff p (delta i g) A := hcenter
    _ = Real.sqrt (p * (1-p)) *
        (Real.sqrt (p * (1-p)) * coeff p (delta i g) A) := by rw [← mul_assoc, ← pow_two, hs]

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta.{u} := @_root_.OAI.Problem313.BiasedFourier.coeff_insert_eq_sqrt_mul_delta.{u}
