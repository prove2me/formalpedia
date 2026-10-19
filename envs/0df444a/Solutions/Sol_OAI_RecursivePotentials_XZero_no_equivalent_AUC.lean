-- Prove2me | solution 1 for OAI.RecursivePotentials.XZero_no_equivalent_AUC
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:03:16.773083+00:00
-- url     : https://prove2.me/submissions/4f991bb7-45aa-40dc-828b-25d545abe20b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L661-L672
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.XZero_no_equivalent_AUC. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_cutPath
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_siblings_le
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_single
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_path_step
import Theorems.Thm_OAI_RecursivePotentials_bounded_trees_modulus_le_zero
import Theorems.Thm_OAI_RecursivePotentials_weaklyNull_of_finsupp_bound

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

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (v : ZeroTreeVector T) : ‖inclusion T v‖ = 2 * ‖v‖ := by
  rw [inclusion_apply, norm_half]
  ring

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_inclusion (x : ZeroTreeSpace T) : ‖inclusion T x‖ = 2 * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [inclusion_coe, Completion.norm_coe, Completion.norm_coe]
      exact ZeroTreeVector.norm_inclusion T v

lemma inclusion_injective : Function.Injective (inclusion T) := by
  intro x y h
  have he : inclusion T (x - y) = 0 := by rw [map_sub, h, sub_self]
  have hn := norm_inclusion T (x - y)
  rw [he, norm_zero] at hn
  have hz : ‖x - y‖ = 0 := by linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (ZeroTreeVector T) := by
  intro h
  have : Module.Finite ℝ (TreeVector.coordinate T T.root).ker := h
  have : Module.Finite ℝ (TreeVector T ⧸ (TreeVector.coordinate T T.root).ker) :=
    Submodule.CoFG.ker (TreeVector.coordinate T T.root).toLinearMap
  exact TreeVector.not_finite_dimensional T
    (Module.Finite.of_submodule_quotient (TreeVector.coordinate T T.root).ker)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (ZeroTreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T).toLinearMap
    (Completion.coe_injective (ZeroTreeVector T))
  exact ZeroTreeVector.not_finite_dimensional T hf

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma cutPath_step (c : ι) (hc : c ≠ T.root) :
    T.cutPath c - T.cutPath (T.parent c) = Finsupp.single c 1 := by
  unfold cutPath
  rw [T.path_step c hc]
  abel

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma normSum_emb_siblings (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) (a : ℕ →₀ ℝ) :
    T.normSum (a.embDomain f) ≤ 2 * Real.sqrt (∑ k ∈ a.support, a k ^ 2) := by
  have h := T.normSum_siblings_le s (a.embDomain f) (by
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hc
    exact hf k)
  simpa only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self] using h

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

lemma basisVector_norm (c : ι) (hc : c ≠ T.root) : ‖basisVector T c‖ = 2 := by
  change ‖(↑(show TreeVector T from Finsupp.single c 1) : TreeSpace T)‖ = 2
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_single c hc

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

lemma cutPathVector_norm (s : ι) (hs : s ≠ T.root) : ‖cutPathVector T s‖ = 2 := by
  change ‖(↑(show TreeVector T from T.cutPath s) : TreeSpace T)‖ = 2
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_cutPath s hs

lemma cutPathVector_step (c : ι) (hc : c ≠ T.root) :
    cutPathVector T c - cutPathVector T (T.parent c) = basisVector T c := by
  let u : TreeVector T := T.cutPath c
  let v : TreeVector T := T.cutPath (T.parent c)
  let e : TreeVector T := Finsupp.single c 1
  have he : u - v = e := T.cutPath_step c hc
  change (↑u : TreeSpace T) - ↑v = ↑e
  rw [← Completion.coe_sub, he]

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

lemma basisVector_norm (c : ι) (hc : c ≠ T.root) : ‖basisVector T c hc‖ = 1 := by
  have h := norm_inclusion T (basisVector T c hc)
  rw [inclusion_basisVector, TreeSpace.basisVector_norm T c hc] at h
  linarith

lemma pathVector_norm (s : ι) (hs : s ≠ T.root) : ‖pathVector T s‖ = 1 := by
  have h := norm_inclusion T (pathVector T s)
  rw [inclusion_pathVector, TreeSpace.cutPathVector_norm T s hs] at h
  linarith

lemma pathVector_step (c : ι) (hc : c ≠ T.root) :
    pathVector T c - pathVector T (T.parent c) = basisVector T c hc := by
  apply inclusion_injective T
  rw [map_sub, inclusion_pathVector, inclusion_pathVector, inclusion_basisVector]
  exact TreeSpace.cutPathVector_step T c hc

lemma siblings_weaklyNull (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) :
    WeaklyNull (fun k => basisVector T (f k) (hf k).1) := by
  let L : (ℕ →₀ ℝ) →ₗ[ℝ] TreeVector T :=
    { toFun := Finsupp.embDomain f
      map_add' := Finsupp.embDomain_add f
      map_smul' := by
        intro r a
        change Finsupp.embDomain f (r • a) = r • Finsupp.embDomain f a
        ext c
        by_cases hc : c ∈ Set.range f
        · obtain ⟨k, rfl⟩ := hc
          simp only [Finsupp.embDomain_apply_self, Finsupp.smul_apply]
        · simp only [Finsupp.embDomain_of_notMem_range f _ c hc, Finsupp.smul_apply, smul_zero] }
  have hr : T.root ∉ Set.range f := by
    rintro ⟨k, hk⟩
    exact (hf k).1 hk
  let L₀ : (ℕ →₀ ℝ) →ₗ[ℝ] ZeroTreeVector T :=
    L.codRestrict (TreeVector.coordinate T T.root).ker (fun a => by
      change Finsupp.embDomain f a T.root = 0
      exact Finsupp.embDomain_of_notMem_range f a T.root hr)
  let D : (ℕ →₀ ℝ) →ₗ[ℝ] ZeroTreeSpace T :=
    (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T).toLinearMap.comp L₀
  have he : ∀ k, D (Finsupp.single k 1) = basisVector T (f k) (hf k).1 := by
    intro k
    apply congrArg (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T)
    apply Subtype.ext
    exact Finsupp.embDomain_single f k 1
  simp_rw [← he]
  refine weaklyNull_of_finsupp_bound D (by norm_num : (0 : ℝ) ≤ 1) ?_
  intro a
  change ‖(↑(L₀ a) : ZeroTreeSpace T)‖ ≤ _
  rw [Completion.norm_coe, ZeroTreeVector.norm_half, one_mul]
  change T.normSum (a.embDomain f) / 2 ≤ _
  have h := T.normSum_emb_siblings s f hf a
  linarith

end

end ZeroTreeSpace

lemma joinedNode_ne_root (h : ℕ) (s : List ℕ) : joinedNode h s ≠ joinedTree.root := by
  simp [joinedNode, joinedTree]

lemma joinedNode_parent (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    joinedTree.parent (joinedNode h (s ++ [k])) = joinedNode h s := by
  have hs' : s.length ≤ h := hs.le
  have hsk : (s ++ [k]).length ≤ h := by simp; omega
  simp only [joinedNode, List.take_of_length_le hs', List.take_of_length_le hsk]
  change (if s ++ [k] = [] then none else _) = _
  have he : s ++ [k] ≠ [] := by simp
  rw [ite_eq_right he]
  congr 3
  simp

lemma joinedChildren_spec (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    joinedChildren h s hs k ≠ joinedTree.root ∧
      joinedTree.parent (joinedChildren h s hs k) = joinedNode h s :=
  ⟨joinedNode_ne_root _ _, joinedNode_parent h s hs k⟩

lemma XZero_path_increments (h : ℕ) (s : List ℕ) (hs : s.length < h) :
    WeaklyNull (fun k => ZeroTreeSpace.pathVector joinedTree (joinedNode h (s ++ [k])) -
      ZeroTreeSpace.pathVector joinedTree (joinedNode h s)) := by
  have he : ∀ k, ZeroTreeSpace.pathVector joinedTree (joinedNode h (s ++ [k])) -
      ZeroTreeSpace.pathVector joinedTree (joinedNode h s) =
      ZeroTreeSpace.basisVector joinedTree (joinedChildren h s hs k) (joinedChildren_spec h s hs k).1 := by
    intro k
    have H := ZeroTreeSpace.pathVector_step joinedTree (joinedChildren h s hs k)
      (joinedChildren_spec h s hs k).1
    have H' := H
    simp only [(joinedChildren_spec h s hs k).2] at H'
    convert H' using 1 ; rfl
  simp_rw [he]
  exact ZeroTreeSpace.siblings_weaklyNull joinedTree _ _ (joinedChildren_spec h s hs)

theorem XZero_no_equivalent_AUC (A : EquivalentNorm XZero) : ¬A.AUC := by
  apply bounded_trees_not_AUC (ZeroTreeSpace.not_finite_dimensional joinedTree) A
    (fun h s => ZeroTreeSpace.pathVector joinedTree (joinedNode h s))
    (m := 1) (M := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs
    rw [ZeroTreeSpace.pathVector_norm _ _ (joinedNode_ne_root h s)]; exact ⟨le_rfl, le_rfl⟩
  · intro h hh s hs; exact XZero_path_increments h s hs
  · intro h hh s hs k
    have he := ZeroTreeSpace.pathVector_step joinedTree (joinedNode h (s ++ [k]))
      (joinedNode_ne_root h (s ++ [k]))
    rw [joinedNode_parent h s hs k] at he
    rw [he, ZeroTreeSpace.basisVector_norm]

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials
open scoped BigOperators
open Filter Topology


theorem solution : type_of% @_root_.OAI.RecursivePotentials.XZero_no_equivalent_AUC := @_root_.OAI.RecursivePotentials.XZero_no_equivalent_AUC
