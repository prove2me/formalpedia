-- Prove2me | solution 2 for OAI.Saxl.paired_term_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:17:01.221257+00:00
-- url     : https://prove2.me/submissions/674c7d11-6870-4264-8b97-24467610ccc8

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/RepeatedProjection.lean:L161-L211
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.paired_term_projection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_RepeatedProjection

-- ---- from OAI.RepresentationTheory.Saxl.RepeatedProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

lemma weighted_perm_sum {X : Type uX} [Fintype X] (t a : X → ℝ)
    (g : Equiv.Perm X) (hg : ∀ i, t (g i) = t i) :
    ∑ i, t i * a (g i) = ∑ i, t i * a i := by
  simpa only [hg] using Equiv.sum_comp g (fun i => t i * a i)

/- The strict square-moment equality used in the dominance projection.
The labels may be real; the application uses actual nonnegative integer letters. -/
theorem pair_sum_rigidity {X : Type uX} [Fintype X]
    (a t c : X → ℝ) (ω g h k : Equiv.Perm X)
    (hω : ∀ i, t (ω i) = t i) (hcomp : ∀ i, a i + a (ω i) = t i)
    (hg : ∀ i, t (g i) = t i) (hh : ∀ i, t (h i) = t i)
    (hc : ∀ i, c i = a (g i) + a (h i)) (hk : ∀ i, c i = t (k i)) : c = t := by
  have hbase : 2 * (∑ i, t i * a i) = ∑ i, t i ^ 2 := by
    have he := weighted_perm_sum t a ω hω
    have hs : (∑ i, t i * a i) + (∑ i, t i * a (ω i)) = ∑ i, t i ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_add, hcomp i, pow_two]
    linarith
  have hcross : ∑ i, t i * c i = ∑ i, t i ^ 2 := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, weighted_perm_sum t a g hg, weighted_perm_sum t a h hh]
    linarith
  have hsquare : ∑ i, c i ^ 2 = ∑ i, t i ^ 2 := by
    simp only [hk]
    exact Equiv.sum_comp k (fun i => t i ^ 2)
  have hsum : ∑ i, (c i - t i) ^ 2 = 0 := by
    calc
      (∑ i, (c i - t i) ^ 2) = (∑ i, c i ^ 2) - 2 * (∑ i, t i * c i) +
          (∑ i, t i ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hsquare, hcross]; ring
  funext i
  have hz : (c i - t i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j-t j))).mp hsum i
      (Finset.mem_univ i)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end Saxl

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

lemma pairSumMap_single {n d e : ℕ} (a b : Fin n → Fin d) (c : Fin n → Fin e) :
    pairSumMap n d e (Pi.single (mergeWords a b) 1) c =
      if ∀ i, (a i).val + (b i).val = (c i).val then 1 else 0 := by
  classical
  rw [pairSumMap, wordMap_single]
  simp only [mergeWords, Equiv.symm_apply_apply]
  by_cases h : ∀ i, (a i).val + (b i).val = (c i).val
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma paired_relation_iff {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply ha
    apply Prod.ext
    · exact (ht h i).trans ((ht ω (g.val i)).trans (ht g i)).symm
    · apply Fin.ext
      have he := hω (g.val i)
      rw [ht g i] at he
      exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

lemma paired_term_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.paired_term_projection := @_root_.OAI.Saxl.paired_term_projection
