-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:47:40.250378+00:00
-- url     : https://prove2.me/submissions/c70df4fc-42d8-46f2-8d53-3134acb11347

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L437-L490
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma child_not_mem_ancestors {s c : ι} (hc : c ≠ T.root) (hp : T.parent c = s) :
    c ∉ T.ancestors s := by
  intro h
  have h₁ := T.depth_le_of_mem_ancestors s h
  have h₂ := T.parent_depth c hc
  rw [hp] at h₂
  omega

lemma child_function_zero_on_ancestors (s : ι) (b : ι → ℝ)
    (hb : ∀ c, b c ≠ 0 → c ≠ T.root ∧ T.parent c = s)
    {a : ι} (ha : a ∈ T.ancestors s) : b a = 0 := by
  by_contra hh
  exact T.child_not_mem_ancestors (hb a hh).1 (hb a hh).2 ha

lemma attached_upper (s : ι) (b : ι → ℝ) (hb0 : ∀ c, 0 ≤ b c)
    (hb : ∀ c, b c ≠ 0 → c ≠ T.root ∧ T.parent c = s)
    {R : ℝ} (hR : 0 ≤ R) (hsq : ∀ S : Finset ι, ∑ c ∈ S, b c ^ 2 ≤ R ^ 2) :
    T.GlobalUpper (fun c => R * T.path s c + b c) := by
  intro a S hS
  dsimp only
  by_cases ha : a = s
  · subst a
    have hzero := T.child_function_zero_on_ancestors s b hb (T.mem_ancestors_self s)
    have hsum : ∑ c ∈ S, (R * T.path s c + b c) ^ 2 = ∑ c ∈ S, b c ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [path_apply, ite_eq_right (T.child_not_mem_ancestors (hS c hc).1 (hS c hc).2)]
      ring
    have hself : T.path s s = 1 := by rw [path_apply, ite_eq_left (T.mem_ancestors_self s)]
    rw [hsum, hself, hzero, mul_one, add_zero]
    exact hsq S
  · have hsum : ∑ c ∈ S, (R * T.path s c + b c) ^ 2 = ∑ c ∈ S, (R * T.path s c) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hz : b c = 0 := by
        by_contra hh
        exact ha ((hS c hc).2.symm.trans (hb c hh).2)
      rw [hz, add_zero]
    rw [hsum]
    have hp := ((T.path_upper s).smul T R) a S hS
    simp only [Pi.smul_apply, smul_eq_mul] at hp
    have hnon : 0 ≤ R * T.path s a := mul_nonneg hR (T.path_nonneg s a)
    nlinarith [hb0 a, sq_nonneg (b a)]

lemma sum_sq_le_support (v : ι →₀ ℝ) (S : Finset ι) :
    ∑ c ∈ S, v c ^ 2 ≤ ∑ c ∈ v.support, v c ^ 2 := by
  have he : ∑ c ∈ S ∪ v.support, v c ^ 2 = ∑ c ∈ v.support, v c ^ 2 := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro c hc hn
    rw [Finsupp.notMem_support_iff.mp hn]
    norm_num
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun c hc hn => sq_nonneg _)

lemma positivePart_sq_le (a : ℝ) : max a 0 ^ 2 ≤ a ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
  · rw [max_eq_right (le_of_not_ge ha)]
    simpa using sq_nonneg a

theorem normSum_siblings_le (s : ι) (v : ι →₀ ℝ)
    (hv : ∀ c ∈ v.support, c ≠ T.root ∧ T.parent c = s) :
    T.normSum v ≤ 2 * Real.sqrt (∑ c ∈ v.support, v c ^ 2) := by
  let R := Real.sqrt (∑ c ∈ v.support, v c ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = ∑ c ∈ v.support, v c ^ 2 := Real.sq_sqrt
    (Finset.sum_nonneg (fun c hc => sq_nonneg _))
  let p : ι → ℝ := fun c => R * T.path s c + max (v c) 0
  let q : ι → ℝ := fun c => R * T.path s c + max (-v c) 0
  have hp : T.GlobalUpper p := by
    refine T.attached_upper s (fun c => max (v c) 0) (fun c => le_max_right _ _) ?_ hR ?_
    · intro c hc
      apply hv c (Finsupp.mem_support_iff.mpr ?_)
      intro he
      simp [he] at hc
    · intro S
      calc
        ∑ c ∈ S, max (v c) 0 ^ 2 ≤ ∑ c ∈ S, v c ^ 2 :=
          Finset.sum_le_sum (fun c hc => positivePart_sq_le _)
        _ ≤ R ^ 2 := by rw [hR2]; exact sum_sq_le_support v S
  have hq : T.GlobalUpper q := by
    refine T.attached_upper s (fun c => max (-v c) 0) (fun c => le_max_right _ _) ?_ hR ?_
    · intro c hc
      apply hv c (Finsupp.mem_support_iff.mpr ?_)
      intro he
      simp [he] at hc
    · intro S
      calc
        ∑ c ∈ S, max (-v c) 0 ^ 2 ≤ ∑ c ∈ S, v c ^ 2 := by
          apply Finset.sum_le_sum
          intro c hc
          simpa only [neg_sq] using positivePart_sq_le (-v c)
        _ ≤ R ^ 2 := by rw [hR2]; exact sum_sq_le_support v S
  have hdiff : ∀ c, p c - q c = v c := by
    intro c
    dsimp [p, q]
    by_cases hc : 0 ≤ v c
    · rw [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]
      ring
    · have hcn := le_of_not_ge hc
      rw [max_eq_right hcn, max_eq_left (neg_nonneg.mpr hcn)]
      ring
  have hle := T.potentials_minimal v p q
    (fun c => add_nonneg (mul_nonneg hR (T.path_nonneg s c)) (le_max_right _ _))
    (fun c => add_nonneg (mul_nonneg hR (T.path_nonneg s c)) (le_max_right _ _))
    hdiff hp hq T.root
  have hv0 : v T.root = 0 := by
    by_contra h
    exact (hv T.root (Finsupp.mem_support_iff.mpr h)).1 rfl
  have hp0 : p T.root = R := by simp [p, T.path_root, hv0]
  have hq0 : q T.root = R := by simp [q, T.path_root, hv0]
  rw [hp0, hq0] at hle
  unfold normSum
  linarith

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_siblings_le.{uIndex}
