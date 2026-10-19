-- Prove2me | solution 1 for OAI.RecursivePotentials.XSigma_no_equivalent_AUC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:00:21.541122+00:00
-- url     : https://prove2.me/submissions/f503c8a9-c834-4b3c-96bc-e64aec5b4472

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L462-L474
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.XSigma_no_equivalent_AUC. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_single
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_path_step
import Theorems.Thm_OAI_RecursivePotentials_TreeSpace_siblings_weaklyNull
import Theorems.Thm_OAI_RecursivePotentials_bounded_trees_modulus_le_zero

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) [Infinite ι] :
    ¬Module.Finite ℝ (TreeVector T) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (TreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap
    (Completion.coe_injective (TreeVector T))
  exact TreeVector.not_finite_dimensional T hf

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma upper_pos : 0 < A.upper := A.lower_pos.trans_le A.lower_le_upper

end EquivalentNorm

theorem bounded_trees_not_AUC {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) : ¬A.AUC := by
  intro ha
  have ht : 0 < A.lower * c / (2 * A.upper * M) := by have := A.lower_pos; have := A.upper_pos; positivity
  exact (not_lt_of_ge (bounded_trees_modulus_le_zero hE A u hm hM hc hu hd hdc)) (ha _ ht)

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

lemma basisVector_norm (c : ι) (hc : c ≠ T.root) : ‖basisVector T c‖ = 2 := by
  change ‖(↑(show TreeVector T from Finsupp.single c 1) : TreeSpace T)‖ = 2
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_single c hc

lemma pathVector_step (c : ι) (hc : c ≠ T.root) :
    pathVector T c - pathVector T (T.parent c) = basisVector T c := by
  let u : TreeVector T := T.path c
  let v : TreeVector T := T.path (T.parent c)
  let e : TreeVector T := Finsupp.single c 1
  have he : u - v = e := by
    change T.path c - T.path (T.parent c) = Finsupp.single c 1
    rw [T.path_step c hc]; abel
  change (↑u : TreeSpace T) - ↑v = ↑e
  rw [← Completion.coe_sub, he]

end

end TreeSpace

lemma sequenceChildren_spec (s : List ℕ) (k : ℕ) :
    sequenceChildren s k ≠ sequenceTree.root ∧
      sequenceTree.parent (sequenceChildren s k) = s := by
  change s ++ [k] ≠ [] ∧ (s ++ [k]).dropLast = s
  simp

lemma XSigma_path_increments (s : List ℕ) :
    WeaklyNull (fun k => TreeSpace.pathVector sequenceTree (s ++ [k]) -
      TreeSpace.pathVector sequenceTree s) := by
  have he : ∀ k, TreeSpace.pathVector sequenceTree (s ++ [k]) -
      TreeSpace.pathVector sequenceTree s = TreeSpace.basisVector sequenceTree (sequenceChildren s k) := by
    intro k
    have h := TreeSpace.pathVector_step sequenceTree (sequenceChildren s k)
      (sequenceChildren_spec s k).1
    rw [(sequenceChildren_spec s k).2] at h
    exact h
  simp_rw [he]
  exact TreeSpace.siblings_weaklyNull sequenceTree s (sequenceChildren s) (sequenceChildren_spec s)

theorem XSigma_no_equivalent_AUC (A : EquivalentNorm XSigma) : ¬A.AUC := by
  apply bounded_trees_not_AUC (TreeSpace.not_finite_dimensional sequenceTree) A
    (fun _ s => TreeSpace.pathVector sequenceTree s)
    (m := 1) (M := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs; simp
  · intro h hh s hs; exact XSigma_path_increments s
  · intro h hh s hs k
    have ht := TreeSpace.pathVector_step sequenceTree (sequenceChildren s k)
      (sequenceChildren_spec s k).1
    rw [(sequenceChildren_spec s k).2] at ht
    change 2 ≤ ‖TreeSpace.pathVector sequenceTree (sequenceChildren s k) - TreeSpace.pathVector sequenceTree s‖
    rw [ht]
    exact (TreeSpace.basisVector_norm sequenceTree _ (sequenceChildren_spec s k).1).ge

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials
open scoped BigOperators
open Filter Topology


theorem solution : type_of% @_root_.OAI.RecursivePotentials.XSigma_no_equivalent_AUC := @_root_.OAI.RecursivePotentials.XSigma_no_equivalent_AUC
