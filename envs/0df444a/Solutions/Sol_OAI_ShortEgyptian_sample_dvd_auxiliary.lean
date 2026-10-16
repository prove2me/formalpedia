-- Prove2me | solution 1 for OAI.ShortEgyptian.sample_dvd_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:13:51.264702+00:00
-- url     : https://prove2.me/submissions/6daf57f7-8590-498e-bae1-1d92aab330d7

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean:L67-L80
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.sample_dvd_auxiliary. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.ListConstruction ----
namespace OAI

universe uJ uA uR

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

lemma sample_dvd_auxiliary {J : Type uJ} {A : Type uA} {R : Type uR} [Fintype J] [Fintype R]
    (a : ℕ) (p₀ : J → ℕ) (p : A → ℕ) (f : R → (J × Bool) → A) (i : R) (I : J → Bool) :
    sampleProduct p I (f i) ∣ auxiliaryDenominator a p₀ p f := by
  have hd : sampleProduct p I (f i) ∣ ∏ j,p (f i (j,false))*p (f i (j,true)) := by
    unfold sampleProduct
    apply prod_dvd_prod_of_dvd
    intro j _
    cases hI : I j
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hb : (∏ j, p (f i (j,false))*p (f i (j,true))) ∣
      ∏ k : R, ∏ j, p (f k (j,false))*p (f k (j,true)) :=
    dvd_prod_of_mem (fun k : R => ∏ j, p (f k (j,false))*p (f k (j,true))) (mem_univ i)
  exact dvd_mul_of_dvd_right (hd.trans hb) _

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uJ,uA,uR} : type_of% @_root_.OAI.ShortEgyptian.sample_dvd_auxiliary.{uJ,uA,uR} := @_root_.OAI.ShortEgyptian.sample_dvd_auxiliary.{uJ,uA,uR}
