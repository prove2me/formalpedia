-- Prove2me | solution 1 for OAI.ShortEgyptian.auxiliary_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:25:47.500129+00:00
-- url     : https://prove2.me/submissions/8857dd99-aa7d-4865-9f11-c95030654db7

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueAssembly.lean:L94-L114
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.auxiliary_lower. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.ListConstruction ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma auxiliaryDenominator_pos {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A)
    (h₀ : ∀ j, 0 < p₀ j) (hp : ∀ x, 0 < p x) :
    0 < auxiliaryDenominator a p₀ p f := by
  unfold auxiliaryDenominator
  exact mul_pos (mul_pos (by positivity) (prod_pos (fun j _ => h₀ j)))
    (prod_pos (fun _ _ => prod_pos (fun _ _ => mul_pos (hp _) (hp _))))

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ResidueAssembly ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma auxiliary_lower {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (S : ℝ) (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A)
    (hS : 0 < S) (hlog : 0 < Real.log S) (hm : S/(2*Real.log S) ≤ (Fintype.card J:ℝ))
    (h₀ : ∀ j, S^100 ≤ (p₀ j:ℝ)) (h₀pos : ∀ j, 0 < p₀ j) (hp : ∀ x, 0 < p x) :
    Real.exp S < (auxiliaryDenominator a p₀ p f:ℝ) := by
  have hbase : Real.exp (50*S) ≤ ((∏ j,p₀ j : ℕ):ℝ) := by
    have hm' := (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mp hm
    calc
      _ ≤ Real.exp ((Fintype.card J:ℝ)*(100*Real.log S)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (S^100)^Fintype.card J := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [←Real.exp_log (pow_pos hS 100),Real.log_pow]
        norm_num
      _ = ∏ _j : J, S^100 := by simp
      _ ≤ _ := by push_cast; exact prod_le_prod (fun _ _ => by positivity) (fun j _ => h₀ j)
  have hMpos := auxiliaryDenominator_pos a p₀ p f h₀pos hp
  have hd : (∏ j,p₀ j) ∣ auxiliaryDenominator a p₀ p f :=
    dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  exact (Real.exp_lt_exp.mpr (by nlinarith : S < 50*S)).trans_le
    (hbase.trans (by exact_mod_cast Nat.le_of_dvd hMpos hd))

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical Filter Topology


theorem solution.{uJ,uA,uR} : type_of% @_root_.OAI.ShortEgyptian.auxiliary_lower.{uJ,uA,uR} := @_root_.OAI.ShortEgyptian.auxiliary_lower.{uJ,uA,uR}
