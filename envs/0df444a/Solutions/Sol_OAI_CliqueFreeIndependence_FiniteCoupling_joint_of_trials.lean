-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:36:48.999764+00:00
-- url     : https://prove2.me/submissions/12c97c5a-3181-4150-8366-ffc7b88a290e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean:L130-L265
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
lemma sum_push (p : I → ℝ) (f : I → J) (g : J → ℝ) :
    ∑ y, push p f y * g y = ∑ i, p i * g (f i) := by
  simp only [push, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

lemma law_push {p : I → ℝ} (hp : Law p) (f : I → J) : Law (push p f) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ by split_ifs <;> simp_all, ?_⟩
  have h := sum_push p f (fun _ ↦ 1)
  simpa [hp.2] using h

lemma sum_mix (p : I → ℝ) (q : I → J → ℝ) (g : J → ℝ) :
    ∑ y, mix p q y * g y = ∑ i, p i * ∑ y, q i y * g y := by
  simp only [mix, sum_mul, mul_sum, mul_assoc]
  exact sum_comm

lemma law_mix {p : I → ℝ} {q : I → J → ℝ} (hp : Law p) (hq : ∀ i, Law (q i)) :
    Law (mix p q) := by
  refine ⟨fun y ↦ sum_nonneg fun i _ ↦ mul_nonneg (hp.1 i) ((hq i).1 y), ?_⟩
  have h := sum_mix p q (fun _ ↦ 1)
  simpa only [mul_one, (hq _).2, hp.2] using h

lemma law_dirac (j : J) : Law (fun y ↦ if y = j then (1 : ℝ) else 0) := by
  constructor
  · intro y; dsimp; split_ifs <;> norm_num
  · simp

lemma prob_event_le_one {p : I → ℝ} (hp : Law p) (b : I → Prop) [DecidablePred b] :
    (∑ i, if b i then p i else 0) ≤ 1 := by
  rw [← hp.2]
  apply sum_le_sum
  intro i _
  split_ifs <;> simp_all

lemma expected_indicator_push {p : I → ℝ} (f : I → J) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then push p f y else 0) = ∑ i, if b (f i) then p i else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_push p f (fun y ↦ if b y then 1 else 0)

lemma expected_indicator_mix (p : I → ℝ) (q : I → J → ℝ) (b : J → Prop) [DecidablePred b] :
    (∑ y, if b y then mix p q y else 0) =
      ∑ i, p i * ∑ y, if b y then q i y else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using sum_mix p q (fun y ↦ if b y then 1 else 0)

/-- A finite version of the first-accepted-trial construction, with states the
set of unfinished rows. The recursion strictly decreases that finite set. -/
lemma joint_of_trials [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i))
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (A : E → Finset I) (label : E → J)
    (hmarg : ∀ i y, (∑ e, if i ∈ A e ∧ label e = y then t e else 0) = p i y)
    (D : I → I → ℝ)
    (hpair : ∀ i j,
      (∑ e, if Xor (i ∈ A e) (j ∈ A e) then t e else 0) ≤
        D i j * (∑ e, if i ∈ A e ∨ j ∈ A e then t e else 0)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
  have hacc (i : I) : (∑ e, if i ∈ A e then t e else 0) = 1 := by
    have h := congrArg (fun g : J → ℝ ↦ ∑ y, g y) (funext (hmarg i))
    change (∑ y, ∑ e, if i ∈ A e ∧ label e = y then t e else 0) = ∑ y, p i y at h
    rw [sum_comm, (hp i).2] at h
    convert h using 1
    apply sum_congr rfl
    intro e _
    by_cases hi : i ∈ A e <;> simp [hi]
  let base : I → J := fun _ ↦ Classical.choice (inferInstance : Nonempty J)
  have hpartial (S : Finset I) :
      ∃ q : (I → J) → ℝ, Law q ∧
        (∀ i ∈ S, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
        (∀ i ∈ S, ∀ j ∈ S, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · let active : E → Prop := fun e ↦ (S ∩ A e).Nonempty
      let r : E → ℝ := fun e ↦ if active e then t e else 0
      let Q : ℝ := ∑ e, r e
      have hr (e : E) : 0 ≤ r e := by dsimp [r]; split_ifs <;> simp_all
      have hactive (i : I) (hi : i ∈ S) (e : E) (ha : i ∈ A e) : active e :=
        ⟨i, mem_inter.2 ⟨hi, ha⟩⟩
      have hQ : 0 < Q := by
        obtain ⟨i, hi⟩ := hS
        have hle : (∑ e, if i ∈ A e then t e else 0) ≤ Q := by
          apply sum_le_sum
          intro e _
          by_cases ha : i ∈ A e
          · simp only [ha, ↓reduceIte, r, hactive i hi e ha, le_refl]
          · simpa only [ha, ↓reduceIte] using hr e
        rw [hacc] at hle
        linarith
      have hrec (e : E) : ∃ q : (I → J) → ℝ, Law q ∧
          (active e →
            (∀ i ∈ S \ A e, ∀ y, (∑ f, if f i = y then q f else 0) = p i y) ∧
            (∀ i ∈ S \ A e, ∀ j ∈ S \ A e,
              (∑ f, if f i ≠ f j then q f else 0) ≤ D i j)) := by
        by_cases he : active e
        · have hlt : S \ A e ⊂ S := by
            refine Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, ?_⟩
            intro heq
            obtain ⟨i, hi⟩ := he
            obtain ⟨hiS, hiA⟩ := mem_inter.1 hi
            rw [← heq] at hiS
            exact (mem_sdiff.1 hiS).2 hiA
          obtain ⟨q, hq, hqm, hqd⟩ := ih (S \ A e) hlt
          exact ⟨q, hq, fun _ ↦ ⟨hqm, hqd⟩⟩
        · exact ⟨_, law_dirac base, fun h ↦ (he h).elim⟩
      choose q hq hqrec using hrec
      let update : E → (I → J) → (I → J) :=
        fun e f i ↦ if i ∈ A e then label e else f i
      let coeff : E → ℝ := fun e ↦ r e / Q
      have hcoeff : Law coeff := by
        refine ⟨fun e ↦ div_nonneg (hr e) hQ.le, ?_⟩
        dsimp [coeff]
        rw [← sum_div]
        exact div_self hQ.ne'
      let out : (I → J) → ℝ := mix coeff (fun e ↦ push (q e) (update e))
      refine ⟨out, law_mix hcoeff (fun e ↦ law_push (hq e) (update e)), ?_, ?_⟩
      · intro i hi y
        change (∑ f, if f i = y then mix coeff (fun e ↦ push (q e) (update e)) f else 0) = _
        rw [expected_indicator_mix]
        simp_rw [expected_indicator_push]
        have heq (e : E) :
            r e * (∑ f, if update e f i = y then q e f else 0) =
              (if i ∈ A e ∧ label e = y then t e else 0) +
                p i y * (r e - if i ∈ A e then t e else 0) := by
          by_cases ha : i ∈ A e
          · have hb := hactive i hi e ha
            simp only [update, ha, ↓reduceIte, r, hb, true_and, sub_self, mul_zero, add_zero,
              sum_ite_irrel, (hq e).2]
            split_ifs <;> simp
          · have hni : i ∈ S \ A e := mem_sdiff.2 ⟨hi, ha⟩
            by_cases hb : active e
            · have hm := (hqrec e hb).1 i hni y
              simp only [update, ha, ↓reduceIte, false_and, r, hb, sub_zero, zero_add] at *
              rw [hm]
              ring
            · simp [r, hb, ha]
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        simp_rw [heq]
        rw [sum_add_distrib, ← mul_sum, sum_sub_distrib, hmarg, hacc]
        change (p i y + p i y * (Q - 1)) / Q = p i y
        field_simp
        ring
      · intro i hi j hj
        change (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) ≤ _
        have hem : (∑ f, if f i ≠ f j then mix coeff (fun e ↦ push (q e) (update e)) f else 0) =
            ∑ e, coeff e * ∑ f, if f i ≠ f j then push (q e) (update e) f else 0 :=
          expected_indicator_mix coeff (fun e ↦ push (q e) (update e)) (fun f ↦ f i ≠ f j)
        rw [hem]
        simp_rw [expected_indicator_push]
        have he (e : E) :
            r e * (∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
              D i j * r e + (if Xor (i ∈ A e) (j ∈ A e) then t e else 0) -
                D i j * (if i ∈ A e ∨ j ∈ A e then t e else 0) := by
          by_cases hai : i ∈ A e <;> by_cases haj : j ∈ A e
          · have hb := hactive i hi e hai
            simp [update, hai, haj, r, hb, Xor]
          · have hb := hactive i hi e hai
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ label e ≠ f j)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · have hb := hactive j hj e haj
            have hle := mul_le_mul_of_nonneg_left
              (prob_event_le_one (hq e) (fun f ↦ f i ≠ label e)) (ht e)
            simpa [update, hai, haj, r, hb, Xor] using hle
          · by_cases hb : active e
            · have hle := mul_le_mul_of_nonneg_left
                ((hqrec e hb).2 i (mem_sdiff.2 ⟨hi, hai⟩) j (mem_sdiff.2 ⟨hj, haj⟩)) (ht e)
              simpa [update, hai, haj, r, hb, Xor, mul_comm] using hle
            · simp [r, hb, hai, haj, Xor]
        have hsum := sum_le_sum (s := univ) (fun e _ ↦ he e)
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
        have hbound : (∑ e, r e * ∑ f, if update e f i ≠ update e f j then q e f else 0) ≤
            D i j * Q := by
          have hpij := hpair i j
          dsimp [Q]
          linarith
        simp only [coeff, div_mul_eq_mul_div, ← sum_div]
        exact (div_le_iff₀ hQ).2 (by nlinarith [hbound])
    · refine ⟨_, law_dirac base, ?_, ?_⟩ <;> simp_all
  obtain ⟨q, hq, hm, hd⟩ := hpartial univ
  exact ⟨q, hq, fun i ↦ hm i (mem_univ i), fun i j ↦ hd i (mem_univ i) j (mem_univ j)⟩

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteCoupling
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2


theorem solution.{u,v,z} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials.{u,v,z} := @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials.{u,v,z}
