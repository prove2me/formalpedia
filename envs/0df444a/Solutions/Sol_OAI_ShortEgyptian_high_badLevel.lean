-- Prove2me | solution 1 for OAI.ShortEgyptian.high_badLevel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:21:40.941549+00:00
-- url     : https://prove2.me/submissions/f07116a8-30bf-437e-b522-c41786c7bf28

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean:L14-L61
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.high_badLevel. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Theorems.Thm_OAI_ShortEgyptian_badLevel_of_moment
import Theorems.Thm_OAI_ShortEgyptian_deterministicProduct_injective
import Theorems.Thm_OAI_ShortEgyptian_high_list_moment
import Theorems.Thm_OAI_ShortEgyptian_products_scale_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.ListConstruction ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma deterministicProduct_bound {J : Type uJ} [Fintype J]
    (S : ℝ) (hS : 2 ≤ S) (hlog : 0 < Real.log S)
    (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (p : J → ℕ) (hp : ∀ j, (p j:ℝ) ≤ 2*S^100) (I : J → Bool) :
    (deterministicProduct p I:ℝ) ≤ Real.exp (101*S) := by
  apply products_scale_bound S hS hlog hm
  intro j
  split
  · exact hp j
  · simp only [Nat.cast_one]
    have hh : (1:ℝ) ≤ S^100 := one_le_pow₀ (by linarith)
    linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleRho_pos (S : ℝ) : 0 < scaleRho S := Real.exp_pos _
end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueAssembly ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma high_badLevel {J : Type uJ} [Fintype J]
    (S X : ℝ) (C : ℕ) (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (hcard : Fintype.card J = scaleM S) (hmax : ∀ j, (p j:ℝ) ≤ 2*S^100)
    (hS : 2 ≤ S) (hlog : 1 ≤ Real.log S) (hm100 : 100 ≤ (scaleM S:ℝ))
    (hP : (reciprocalPower (3*dimC):ℝ) ≤ Real.log S)
    (hconst : (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC) ≤ Real.exp (S/4))
    (hX : Real.exp S ≤ X) (hXD : X ≤ Real.exp ((dimX:ℝ)*S))
    (hClo : Real.exp ((dimC:ℝ)*S) ≤ C) (hChi : (C:ℝ) ≤ Real.exp (2*(dimC:ℝ)*S)) :
    ((badLevel (deterministicProduct p) C X (scaleRho S)).card:ℝ) ≤
      X*Real.exp (-(1/1000:ℝ)*scaleM S) := by
  have hS0 : 0 < S := by linarith
  have hl : 0 < Real.log S := by linarith
  have hm : (scaleM S:ℝ) ≤ S/Real.log S := Nat.floor_le (by positivity)
  have hJ : (Fintype.card J:ℝ) ≤ S/Real.log S := by simpa [hcard] using hm
  have hmoment (l : ℕ) (hlI : l ∈ Icc 1 ⌊1/(scaleRho S)^4⌋₊) :
      (∑ u ∈ scaleInterval X (scaleRho S), ‖phaseAverage (deterministicProduct p) C u l‖^2) ≤
      X*Real.exp (-(1/100:ℝ)*scaleM S) := by
    have hlhi : (l:ℝ) ≤ Real.exp ((1/2500:ℝ)*scaleM S) := by
      calc
        _ ≤ (⌊1/(scaleRho S)^4⌋₊:ℝ) := by exact_mod_cast (mem_Icc.mp hlI).2
        _ ≤ 1/(scaleRho S)^4 := Nat.floor_le (by positivity)
        _ = _ := by
          unfold scaleRho
          rw [←Real.exp_nat_mul,one_div,←Real.exp_neg]
          congr 1
          push_cast
          ring
    exact high_list_moment S X dimC (scaleM S) C l (deterministicProduct p)
      (deterministicProduct_injective p hp hinj) (by simp [hcard])
      (deterministicProduct_bound S hS hl hJ p hmax)
      hS0 hlog (by norm_num [dimC,dimX,dimM]) hm hm100 hP hconst hX
      (by simpa only [dimC,Nat.cast_mul,Nat.cast_ofNat,show (4:ℝ)*(dimX:ℝ)/4 = dimX by ring] using hXD)
      hClo hChi (mem_Icc.mp hlI).1 hlhi
  have hh := badLevel_of_moment (deterministicProduct p) C X (scaleRho S)
    (X*Real.exp (-(1/100:ℝ)*scaleM S)) (scaleRho_pos S)
    (mul_nonneg ((Real.exp_nonneg _).trans hX) (Real.exp_nonneg _)) hmoment
  apply hh.trans
  have heq : X*Real.exp (-(1/100:ℝ)*scaleM S)/(scaleRho S)^10 =
      X*Real.exp (-(9/1000:ℝ)*scaleM S) := by
    unfold scaleRho
    rw [←Real.exp_nat_mul,div_eq_mul_inv,←Real.exp_neg,mul_assoc,←Real.exp_add]
    congr 2
    push_cast
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) ((Real.exp_nonneg _).trans hX)
  have hm0 : (0:ℝ) ≤ scaleM S := Nat.cast_nonneg _
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology


theorem solution.{uJ} : type_of% @_root_.OAI.ShortEgyptian.high_badLevel.{uJ} := @_root_.OAI.ShortEgyptian.high_badLevel.{uJ}
