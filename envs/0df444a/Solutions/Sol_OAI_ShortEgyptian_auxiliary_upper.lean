-- Prove2me | solution 1 for OAI.ShortEgyptian.auxiliary_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:23:35.811191+00:00
-- url     : https://prove2.me/submissions/ad4b6195-b1e4-4d05-8634-5df3082c71b0

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean:L63-L92
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.auxiliary_upper. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_products_scale_bound

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueAssembly ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma auxiliary_upper {J : Type uJ} {A : Type uA} [Fintype J]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : Fin 1000 → (J × Bool) → A)
    (hS : 2 ≤ S) (hlog : 0 < Real.log S) (hm : (Fintype.card J:ℝ) ≤ S/Real.log S)
    (h₀ : ∀ j, (p₀ j:ℝ) ≤ 2*S^100) (hp : ∀ x, (p x:ℝ) ≤ 2*S^100)
    (ha : (2:ℝ)^a ≤ Real.exp S) :
    (auxiliaryDenominator a p₀ p f:ℝ) ≤ Real.exp ((dimM:ℝ)*S) := by
  have h₁ := products_scale_bound S hS hlog hm p₀ h₀
  have h₂ (i : Fin 1000) : ((∏ j,p (f i (j,false))*p (f i (j,true)) : ℕ):ℝ) ≤ Real.exp (202*S) := by
    rw [prod_mul_distrib,Nat.cast_mul]
    calc
      _ ≤ Real.exp (101*S)*Real.exp (101*S) := mul_le_mul
        (products_scale_bound S hS hlog hm _ (fun _ => hp _))
        (products_scale_bound S hS hlog hm _ (fun _ => hp _)) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have h₃ : ((∏ i : Fin 1000, ∏ j,p (f i (j,false))*p (f i (j,true)) : ℕ):ℝ) ≤ Real.exp (202000*S) := by
    push_cast
    calc
      _ ≤ ∏ _i : Fin 1000,Real.exp (202*S) := prod_le_prod (fun _ _ => by positivity) (fun i _ => by simpa only [Nat.cast_prod,Nat.cast_mul] using h₂ i)
      _ = _ := by rw [prod_const,card_univ,Fintype.card_fin,←Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold auxiliaryDenominator
  push_cast
  calc
    _ ≤ Real.exp S*Real.exp (101*S)*Real.exp (202000*S) := by
      exact mul_le_mul (mul_le_mul ha (by simpa only [Nat.cast_prod] using h₁)
        (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (Real.exp_nonneg _))
        (by simpa only [Nat.cast_prod,Nat.cast_mul] using h₃)
        (prod_nonneg (fun _ _ => prod_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = Real.exp (202102*S) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num [dimM]; nlinarith)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.auxiliary_upper.{uJ,uA} := @_root_.OAI.ShortEgyptian.auxiliary_upper.{uJ,uA}
