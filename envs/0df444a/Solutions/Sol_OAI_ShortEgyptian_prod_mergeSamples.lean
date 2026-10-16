-- Prove2me | solution 1 for OAI.ShortEgyptian.prod_mergeSamples
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:38:08.194351+00:00
-- url     : https://prove2.me/submissions/5df4169b-48bd-4a98-ade7-de344e180960

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SamplePartitions.lean:L62-L76
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.prod_mergeSamples. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.SamplePartitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uJ uA uE uM uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma prod_partition {J : Type uJ} {M : Type uM} [Fintype J] [CommMonoid M]
    (L R : Finset J) (hdis : Disjoint L R) (f : J → M) :
    (∏ j, f j) = (∏ j : ((L∪R)ᶜ : Finset J), f j)*(∏ j : L, f j)*(∏ j : R, f j) := by
  simp only [prod_coe_sort]
  rw [mul_assoc,← prod_union hdis]
  exact (prod_compl_mul_prod _ _).symm

lemma prod_mergeSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J) (hdis : Disjoint L R)
    (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) (p : A → ℕ) :
    (∏ j, p (mergeSamples L R z x y j)) = (∏ j, p (z j))*(∏ j, p (x j))*(∏ j, p (y j)) := by
  rw [prod_partition L R hdis]
  have heq := (partitionSamples (A := A) L R hdis).apply_symm_apply (z,(x,y))
  have hz := congrArg (fun f => f.1) heq
  have hx := congrArg (fun f => f.2.1) heq
  have hy := congrArg (fun f => f.2.2) heq
  change (fun j : ((L∪R)ᶜ : Finset J) => mergeSamples L R z x y j) = z at hz
  change (fun j : L => mergeSamples L R z x y j) = x at hx
  change (fun j : R => mergeSamples L R z x y j) = y at hy
  have hz' := congrArg (fun f : ((L∪R)ᶜ : Finset J) → A => ∏ j, p (f j)) hz
  have hx' := congrArg (fun f : L → A => ∏ j, p (f j)) hx
  have hy' := congrArg (fun f : R → A => ∏ j, p (f j)) hy
  rw [hz',hx',hy']

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{uJ,uA} : type_of% @_root_.OAI.ShortEgyptian.prod_mergeSamples.{uJ,uA} := @_root_.OAI.ShortEgyptian.prod_mergeSamples.{uJ,uA}
