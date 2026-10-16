-- Prove2me | solution 1 for OAI.ShortEgyptian.binary_unitSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:35:03.107136+00:00
-- url     : https://prove2.me/submissions/676dc2b1-4049-4464-8f34-dc33044278d8

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/TerminalExpansion.lean:L25-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.binary_unitSum. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem

-- ---- from OAI.NumberTheory.ShortEgyptian.TerminalExpansion ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma binary_unitSum (a M u : ℕ) (hM : 0 < M) (hd : 2^a ∣ M) (hu : u ≤ 2^a) :
    ∃ ns : List ℕ, (∀ n ∈ ns, 0 < n) ∧ unitSum ns = (u:ℚ)/M ∧ ns.length ≤ a+1 := by
  induction a generalizing u with
  | zero =>
    have hu' : u = 0 ∨ u = 1 := by norm_num at hu; omega
    rcases hu' with rfl | rfl
    · exact ⟨[],by simp,by simp,by simp⟩
    · exact ⟨[M],by simpa using hM,by simp,by simp⟩
  | succ a ih =>
    have hd' : 2^a ∣ M := (pow_dvd_pow 2 (by omega : a ≤ a+1)).trans hd
    by_cases hsmall : u ≤ 2^a
    · obtain ⟨ns,hns,heq,hlen⟩ := ih u hd' hsmall
      exact ⟨ns,hns,heq,by omega⟩
    · have hpow : 0 < 2^a := by positivity
      have hdpos : 0 < M/2^a := Nat.div_pos (Nat.le_of_dvd hM hd') hpow
      have hur : u-2^a ≤ 2^a := by rw [pow_succ] at hu; omega
      obtain ⟨ns,hns,heq,hlen⟩ := ih (u-2^a) hd' hur
      refine ⟨(M/2^a)::ns,by simpa using And.intro hdpos hns,?_,by simpa using Nat.succ_le_succ hlen⟩
      rw [unitSum_cons,heq]
      have hdiv : ((M/2^a:ℕ):ℚ)*(2:ℚ)^a = M := by exact_mod_cast Nat.div_mul_cancel hd'
      have huQ : (u:ℚ) = (u-2^a:ℕ)+(2:ℚ)^a := by exact_mod_cast (Nat.sub_add_cancel (by omega : 2^a ≤ u)).symm
      have hMq : (M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
      have hdq : ((M/2^a:ℕ):ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
      field_simp
      nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.binary_unitSum := @_root_.OAI.ShortEgyptian.binary_unitSum
