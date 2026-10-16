-- Prove2me | solution 1 for OAI.ShortEgyptian.deterministicProduct_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:12:07.365802+00:00
-- url     : https://prove2.me/submissions/52d3ac9f-8d9b-4476-afa7-a05fc73f0c3f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ListConstruction.lean:L21-L39
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.deterministicProduct_injective. The node keeps its source
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

lemma deterministicProduct_injective {J : Type uJ} [Fintype J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (deterministicProduct p) := by
  have hd (I : J → Bool) (j : J) : p j ∣ deterministicProduct p I ↔ I j = true := by
    rw [deterministicProduct,(hp j).prime.dvd_finsetProd_iff]
    constructor
    · rintro ⟨k,_,hk⟩
      by_cases hI : I k = true
      · simp only [hI,ite_true] at hk
        have hjk : j = k := hinj ((Nat.prime_dvd_prime_iff_eq (hp j) (hp k)).mp hk)
        simpa [hjk] using hI
      · simp only [hI] at hk
        exact False.elim ((hp j).not_dvd_one hk)
    · intro hI
      exact ⟨j,mem_univ j,by simp [hI]⟩
  intro I K hIK
  funext j
  have heq : (I j = true) ↔ K j = true := by rw [←hd I j,←hd K j,hIK]
  cases hI : I j <;> cases hK : K j <;> simp_all

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical


theorem solution.{uJ} : type_of% @_root_.OAI.ShortEgyptian.deterministicProduct_injective.{uJ} := @_root_.OAI.ShortEgyptian.deterministicProduct_injective.{uJ}
