-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:20:14.754531+00:00
-- url     : https://prove2.me/submissions/91b7cc24-2a45-4b40-87d5-999b988316bd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S115
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_Native_setupAfterFrontend_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationCorrectness_normalizedBody_length_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem dedupClauses_subset (F : Formula α) : dedupClauses F ⊆ F := by
  intro C hC
  induction F with
  | nil => simp [dedupClauses] at hC
  | cons D F ih =>
    by_cases h : F.any (fun E => equivalent D E) = true
    · have htail : C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact List.mem_cons_of_mem D (ih htail)
    · have hsplit : C = D ∨ C ∈ dedupClauses F := by simpa [dedupClauses, h] using hC
      exact hsplit.elim (fun h => h ▸ List.mem_cons_self) (fun h => List.mem_cons_of_mem D (ih h))

theorem absorb_subset (F : Formula α) : absorb F ⊆ F := by
  intro C hC
  exact dedupClauses_subset F (List.mem_filter.mp hC).1

end SubexponentialSAT.ExecCNF

namespace SubexponentialSAT.ExecCNF
universe u
variable {α : Type u} [DecidableEq α]

theorem normalize_literal_nodup (neg : α → α) (F : Formula α) :
    ∀ C ∈ normalize neg F, C.Nodup := by
  intro C hC
  have h1 := absorb_subset _ hC
  have h2 := (List.mem_filter.mp h1).1
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h2
  exact dedupLiterals_nodup D

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFCodeTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact list transport through literal codes

These equalities preserve clause order and the last-occurrence conventions.
They connect the encoded normalization programs to the typed executable CNF
operations, rather than identifying only their finite-set semantics.
-/

namespace SubexponentialSAT.ExecCNFCodeTransport

open ExecCNF

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

theorem dedupLiterals_eq_of_nodup (C : Clause α) (hC : C.Nodup) : dedupLiterals C = C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hC
      have h : ¬ contains x xs = true := by simpa only [contains_true] using hx
      simp only [dedupLiterals, ite_eq_right h, ih hxs]

theorem cleanLiterals_eq_of_nodup (F : Formula α) (hF : ∀ C ∈ F, C.Nodup) :
    cleanLiterals F = F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      simp only [cleanLiterals, List.map_cons]
      rw [dedupLiterals_eq_of_nodup C (hF C (by simp))]
      congr 1
      exact ih (fun D hD => hF D (by simp [hD]))

@[simp] theorem cleanLiterals_normalize (neg : α → α) (F : Formula α) :
    cleanLiterals (normalize neg F) = normalize neg F :=
  cleanLiterals_eq_of_nodup _ (normalize_literal_nodup neg F)

/-- The extra pass in the typed worklist does not alter order or multiplicity. -/
theorem normalizedInput_eq_normalize {n : ℕ}
    (F : Formula (SAT.Literal (Fin n))) :
    ExecSparsifyWorklist.normalizedInput F = normalize SAT.Literal.negate F := by
  exact cleanLiterals_normalize SAT.Literal.negate F

end SubexponentialSAT.ExecCNFCodeTransport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CanonicalFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical normalizer emits the ordered body consumed by the
disjoint DFS. Both sides retain the declared ambient variable universe. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem canonical_normalized_formula {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedFormula F =
      ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F) :=
  ExecCNFCodeTransport.normalizedInput_eq_normalize _

theorem canonical_normalized_body {n : ℕ} (F : SAT.CNF (Fin n)) :
    SubexpNormalizationCorrectness.normalizedBody F =
      DisjointReuse.SparseCountProgram.encodeBody (ExecCNF.normalize SAT.Literal.negate
        (ExecQuantitativeSparsify.formulaList F)) := by
  unfold SubexpNormalizationCorrectness.normalizedBody
  rw [canonical_normalized_formula]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSetupSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

theorem frontendReady_stack_bound {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) (ha : FrontendReady F binary a) (hlen : binary.length ≤ n) :
    ∀ i, (a.stacks i).length ≤ Encoding.formulaBitLength F + 1 := by
  intro i
  have hn := Encoding.numVariables_le_formulaBitLength F
  by_cases hi : i = ABI.countStack
  · subst i
    rw [ha.input]
    exact Nat.le_succ _
  by_cases hu : i = 258
  · subst i
    rw [ha.header, Encoding.length_encodeNat]
    omega
  by_cases hb : i = 265
  · subst i
    rw [ha.body]
    have hl := SubexpNormalizationCorrectness.normalizedBody_length_le F
    have hh : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
      rw [Encoding.formulaBitLength_eq]
      omega
    omega
  by_cases hd : i = 267
  · subst i
    rw [ha.dimension]
    omega
  rw [ha.blank i hi hu hb hd]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativePrepared
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual canonical setup frame supplies the exact disjoint DFS ports.
No declared coordinate is compressed, and the threshold is the computed
reciprocal-budget choice used by the sharp visit bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem SetupReady.dfs_prepared {k n : ℕ} {F : SAT.CNF (Fin n)}
    {a : State 80 1220} (h : SetupReady k F a) :
    DFSStartup.Prepared (a.stacks 259)
      (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) a := by
  refine ⟨h.blank 257 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.header, rfl,
    h.blank 260 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 261 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 262 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 263 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.body.trans (canonical_normalized_body F), ?_⟩
  intro i hi
  apply h.blank i
  · intro he
    subst i
    change 256 < 256 at hi
    omega
  all_goals intro he; subst i; omega

/-- The large branch can reuse the actual parsed frame after the finite cutoff
test, without reparsing or assuming the remaining setup has been executed. -/
theorem setupAfterFrontend_prepared_execution_oai (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        DFSVisit.BoundedEval (setupAfterFrontend k) steps a b
          ((C + 1220) * (Encoding.formulaBitLength F + 1) ^ 3) ∧
        DFSStartup.Prepared (b.stacks 259)
          (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) b ∧
        SetupReady k F b ∧ steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨C, hC, hrun⟩ := setupAfterFrontend_eval k hk
  refine ⟨C, hC, ?_⟩
  intro n F binary a ha hv hlen hn hs
  obtain ⟨steps, b, he, hb, ht⟩ := hrun F binary a ha hv hlen hn hs
  refine ⟨steps, b, ⟨he, ?_⟩, hb.dfs_prepared, hb, ht⟩
  intro t c hle htrace i
  have hinitial := StreamResources.dataBits_le_mul
    (a.withPC (some (compiled (setupAfterFrontend k) 256 256).entry))
    (frontendReady_stack_bound F binary a ha hlen)
  have hlocal := StructuredSpace.local_stack_bound (compiled (setupAfterFrontend k) 256 256)
    (steps := C * (Encoding.formulaBitLength F + 1) ^ 3) hinitial t c
    (hle.trans ((Nat.le_succ steps).trans ht)) htrace i
  have hlinear : Encoding.formulaBitLength F + 1 ≤ (Encoding.formulaBitLength F + 1) ^ 3 :=
    Nat.le_self_pow (by decide) _
  nlinarith only [hlocal, hlinear]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution_oai
