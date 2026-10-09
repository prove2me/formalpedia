-- Prove2me | solution 1 for OAI.Erdos3.productANOVATensor_uniform_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:07:22.790974+00:00
-- url     : https://prove2.me/submissions/e769a205-4a52-44c4-9bf2-13198afad10e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B127

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DisjointPowersetSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I]

theorem disjoint_powerset_sum (T U : Finset I) (hTU : Disjoint T U) (f : Finset I → ℝ) :
    (∑ C ∈ (T ∪ U).powerset, f C) = ∑ A ∈ T.powerset, ∑ B ∈ U.powerset, f (A ∪ B) := by
  rw [← Finset.sum_product T.powerset U.powerset (fun p : Finset I × Finset I => f (p.1 ∪ p.2))]
  apply Finset.sum_bij' (fun C _ => (C ∩ T, C ∩ U)) (fun p _ => p.1 ∪ p.2)
  · intro C _
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB))
  · intro C hC
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro p hp
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hp
    have hAsub := Finset.mem_powerset.mp hA
    have hBsub := Finset.mem_powerset.mp hB
    apply Prod.ext <;> ext i
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    · have hAi : i ∈ p.1 → i ∈ T := fun h => hAsub h
      have hBi : i ∈ p.2 → i ∈ U := fun h => hBsub h
      have hdis : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hTU h.1 h.2
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
  · intro C hC
    congr 1
    have hsub := Finset.mem_powerset.mp hC
    ext i
    have hi : i ∈ C → i ∈ T ∨ i ∈ U := fun h => Finset.mem_union.mp (hsub h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_ne_zero (p : FiniteProbabilityWeights Ω) : ∃ x, p.weight x ≠ 0 := by
  obtain ⟨x, hx⟩ := p.exists_weight_pos
  exact ⟨x, hx.ne'⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteOrderedSubsetSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem finiteOrderedSubset_sum (k : ℕ) (g : Finset I → ℝ) :
    (∑ a : Fin k → I, if StrictMono a then g (Finset.univ.image a) else 0) =
      ∑ S ∈ Finset.univ.powersetCard k, g S := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij'
    (fun a _ => Finset.univ.image a)
    (fun S hS => S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_image_of_injective Finset.univ hm.injective⟩
  · intro S hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.orderEmbOfFin _).strictMono⟩
  · intro a ha
    have hm : StrictMono a := (Finset.mem_filter.mp ha).2
    exact (Finset.orderEmbOfFin_unique _ (fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩) hm).symm
  · intro S hS
    exact Finset.image_orderEmbOfFin_univ S _
  · intro a _
    rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativeFiberSlicePatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteTuple_sum_snoc {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (Fin (n + 1) → X) → A) :
    (∑ v, f v) = ∑ v : Fin n → X, ∑ a : X, f (Fin.snoc v a) := by
  calc
    (∑ v, f v) = ∑ p : X × (Fin n → X), f (Fin.snoc p.2 p.1) :=
      (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => X))
        (fun p => f (Fin.snoc p.2 p.1)) f (fun p => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem finiteProductIntegral_zero (w : Fin 0 → X → ℝ) (f : (Fin 0 → X) → ℝ) :
    finiteProductIntegral w f = f (fun i => Fin.elim0 i) := by
  classical
  simp only [finiteProductIntegral, Fin.prod_univ_zero, one_mul]
  rw [Fintype.sum_unique]
  congr 1

theorem finiteProductIntegral_snoc (n : ℕ) (w : Fin (n + 1) → X → ℝ)
    (f : (Fin (n + 1) → X) → ℝ) :
    finiteProductIntegral w f = finiteProductIntegral (fun i : Fin n => w i.castSucc)
      (fun v => ∑ a, w (Fin.last n) a * f (Fin.snoc v a)) := by
  unfold finiteProductIntegral
  rw [finiteTuple_sum_snoc]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Erdos3

end

section

namespace Erdos3

variable {I X : Type*}

theorem finiteSplitPoint_free (p : I → Prop) [DecidablePred p]
    (u : {i // p i} → X) (v : {i // ¬p i} → X) (i : {i // ¬p i}) :
    finiteSplitPoint p u v i = v i := by
  simp only [finiteSplitPoint, dif_neg i.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteProductIntegral_mono {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (w : I → X → ℝ) (hw : ∀ i x, 0 ≤ w i x) (f g : (I → X) → ℝ)
    (hfg : ∀ v, f v ≤ g v) : finiteProductIntegral w f ≤ finiteProductIntegral w g :=
  Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hfg v)
    (Finset.prod_nonneg (fun i _ => hw i (v i))))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*}

theorem finiteProductIntegral_reindex [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]
    (e : I ≃ J) (w : J → X → ℝ) (f : (J → X) → ℝ) :
    finiteProductIntegral (fun i => w (e i)) (fun v => f (fun j => v (e.symm j))) =
      finiteProductIntegral w f := by
  unfold finiteProductIntegral
  apply Fintype.sum_equiv (finiteProductCoordinateEquiv e)
  intro v
  have hprod : (∏ i, w (e i) (v i)) = ∏ j, w j (v (e.symm j)) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [Equiv.symm_apply_apply]
  simpa only [finiteProductCoordinateEquiv, Equiv.coe_fn_mk] using
    congrArg (fun t => t * f (fun j => v (e.symm j))) hprod

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_split (p : I → Prop) [DecidablePred p]
    (w : I → X → ℝ) (f : (I → X) → ℝ) :
    finiteProductIntegral w f =
      finiteProductIntegral (fun i : {i // p i} => w i) (fun u =>
        finiteProductIntegral (fun i : {i // ¬p i} => w i) (fun v => f (finiteSplitPoint p u v))) := by
  classical
  calc
    finiteProductIntegral w f =
        ∑ uv : ({i // p i} → X) × ({i // ¬p i} → X),
          (∏ i : {i // p i}, w i (uv.1 i)) *
            (∏ i : {i // ¬p i}, w i (uv.2 i)) * f (finiteSplitPoint p uv.1 uv.2) := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => X))
      intro x
      change (∏ i, w i (x i)) * f x =
        (∏ i : {i // p i}, w i (x i)) * (∏ i : {i // ¬p i}, w i (x i)) *
          f (finiteSplitPoint p (fun i => x i) (fun i => x i))
      rw [finiteSplitPoint_restrict, Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [finiteProductIntegral, Finset.mul_sum, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {X : Type*} {keep : X → Prop} {N : {x // keep x} → ℕ} {q s d : ℕ}

end Erdos3.ResidueBoxSlice

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_two (w : X → ℝ) (f : X → ℝ) :
    finiteWeightedLp w 2 f = Real.sqrt (∑ x, w x * f x ^ 2) := by
  simp only [finiteWeightedLp, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem norm_finiteWeightedL2Map (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (f : X → ℝ) :
    ‖finiteWeightedL2Map w f‖ = finiteWeightedLp w 2 f := by
  rw [EuclideanSpace.norm_eq, finiteWeightedLp_two]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  change |Real.sqrt (w x) * f x| ^ 2 = w x * f x ^ 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (hw x)]

theorem finiteWeightedLp_two_sum_le {J : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : Finset J) (f : J → X → ℝ) :
    finiteWeightedLp w 2 (fun x => ∑ j ∈ D, f j x) ≤ ∑ j ∈ D, finiteWeightedLp w 2 (f j) := by
  have he : (fun x => ∑ j ∈ D, f j x) = ∑ j ∈ D, f j := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, ← norm_finiteWeightedL2Map w hw, map_sum]
  exact (norm_sum_le D (fun j => finiteWeightedL2Map w (f j))).trans_eq
    (Finset.sum_congr rfl (fun j _ => norm_finiteWeightedL2Map w hw (f j)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionFill_fixed {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) (i : Fin n) (hi : s i = true) :
    finiteSectionFill n s z v i = z i := by
  exact finiteSplitPoint_fixed (fun i => s i = true) _ _ ⟨i, hi⟩

theorem finiteSectionFill_free {X : Type*} (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → X) (v : Fin (n - finiteSectionCount s) → X) (i : Fin (n - finiteSectionCount s)) :
    finiteSectionFill n s z v (finiteSectionFreeOrder n s i) = v i := by
  unfold finiteSectionFill
  rw [finiteSplitPoint_free, OrderIso.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

omit [Fintype X] in
theorem finiteSectionWeight_false (w : X → ℝ) (z x : X) :
    finiteSectionWeight w false z x = w x := by
  simp only [finiteSectionWeight, Bool.false_eq_true, ite_false]

theorem finiteSectionWeight_sum_true (w : X → ℝ) (z : X) (f : X → ℝ) :
    (∑ x, finiteSectionWeight w true z x * f x) = f z := by
  classical
  simp [finiteSectionWeight]

theorem finiteSectionIntegral_eq_product (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : Fin n => finiteSectionWeight (w i) (s i) (z i)) f := by
  induction n with
  | zero => rw [finiteSectionIntegral, finiteProductIntegral_zero]
  | succ n ih =>
    rw [finiteProductIntegral_snoc]
    cases hs : s (Fin.last n) with
    | false =>
      simp only [finiteSectionIntegral, hs, Bool.false_eq_true, ite_false,
        finiteSectionWeight_false, Fin.val_last, ih]
      rfl
    | true =>
      simp only [finiteSectionIntegral, hs, ite_true, finiteSectionWeight_sum_true, ih]
      rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

theorem FiniteProbabilityWeights.familyL2_eq (p : FiniteProbabilityWeights Ω)
    (E : Finset L) (g : L → Ω → ℝ) :
    finiteWeightedLp (fun v : ↥E × Ω => p.weight v.2) 2 (fun v => g v.1 v.2) =
      Real.sqrt (∑ l ∈ E, p.mean (fun x => g l x ^ 2)) := by
  rw [finiteWeightedLp_two, Fintype.sum_prod_type]
  congr 1
  exact Finset.sum_coe_sort E (fun l => p.mean (fun x => g l x ^ 2))

theorem FiniteProbabilityWeights.sqrt_sum_mean_sq_triangle (p : FiniteProbabilityWeights Ω)
    (D : Finset J) (E : Finset L) (f : J → L → Ω → ℝ) :
    Real.sqrt (∑ l ∈ E, p.mean (fun x => (∑ j ∈ D, f j l x) ^ 2)) ≤
      ∑ j ∈ D, Real.sqrt (∑ l ∈ E, p.mean (fun x => f j l x ^ 2)) := by
  have h := finiteWeightedLp_two_sum_le (fun v : ↥E × Ω => p.weight v.2)
    (fun v => p.nonneg v.2) D (fun j v => f j v.1 v.2)
  rw [p.familyL2_eq E (fun l x => ∑ j ∈ D, f j l x)] at h
  simpa only [p.familyL2_eq] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionCountBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteSectionCount_le (n : ℕ) (s : Fin n → Bool) : finiteSectionCount s ≤ n := by
  rw [finiteSectionCount_eq_card]
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => s i = true)

theorem finiteSectionCount_eq_zero_iff (n : ℕ) (s : Fin n → Bool) :
    finiteSectionCount s = 0 ↔ ∀ i, s i = false := by
  constructor
  · intro h i
    apply Bool.eq_false_iff.mpr
    intro hi
    have hb : (if s i then 1 else 0) ≤ finiteSectionCount s :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (if s j then 1 else 0)) (Finset.mem_univ i)
    simp only [hi, ite_true, h] at hb
    omega
  · intro h
    simp only [finiteSectionCount, h, Bool.false_eq_true, ite_false, Finset.sum_const_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProductPointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_pointMass (w : I → X → ℝ) (z : I → X) (f : (I → X) → ℝ) :
    finiteProductIntegral (fun i => finiteSectionWeight (w i) true (z i)) f = f z := by
  classical
  unfold finiteProductIntegral
  rw [Finset.sum_eq_single z]
  · simp [finiteSectionWeight]
  · intro v _ hv
    have hne : ∃ i, v i ≠ z i := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hne
    have hz : finiteSectionWeight (w i) true (z i) (v i) = 0 := by
      simp only [finiteSectionWeight, ite_true, hi, ite_false]
    have hp : (∏ j, finiteSectionWeight (w j) true (z j) (v j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hp, zero_mul]
  · simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionOrderedFree
namespace OAI

section

namespace Erdos3

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

theorem finiteProductIntegral_section_free (s : I → Bool) (w : I → X → ℝ)
    (f : (I → X) → ℝ) (z : I → X) :
    finiteProductIntegral (fun i => finiteSectionWeight (w i) (s i) (z i)) f =
      finiteProductIntegral (fun i : {i // s i ≠ true} => w i)
        (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v)) := by
  classical
  rw [finiteProductIntegral_split (fun i => s i = true)]
  have hfix : (fun i : {i // s i = true} => finiteSectionWeight (w i) (s i) (z i)) =
      (fun i : {i // s i = true} => finiteSectionWeight (w i) true (z i)) := by
    funext i x
    rw [i.property]
  have hfree : (fun i : {i // s i ≠ true} => finiteSectionWeight (w i) (s i) (z i)) =
      (fun i : {i // s i ≠ true} => w i) := by
    funext i x
    have hi : s i = false := Bool.eq_false_iff.mpr i.property
    rw [hi, finiteSectionWeight_false]
  rw [hfix, hfree, finiteProductIntegral_pointMass]

theorem finiteSectionIntegral_free (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : {i : Fin n // s i ≠ true} => w i)
        (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v)) := by
  rw [finiteSectionIntegral_eq_product, finiteProductIntegral_section_free]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

theorem finiteSectionIntegral_orderedFree (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionIntegral w n s f z =
      finiteProductIntegral (fun i : Fin (n - finiteSectionCount s) => w (finiteSectionFreeOrder n s i))
        (fun v => f (finiteSectionFill n s z v)) := by
  rw [finiteSectionIntegral_free]
  exact (finiteProductIntegral_reindex (finiteSectionFreeOrder n s).toEquiv
    (fun i : {i : Fin n // s i ≠ true} => w i)
    (fun v => f (finiteSplitPoint (fun i => s i = true) (fun i => z i) v))).symm

theorem finiteSectionL2Norm_orderedFree (w : ℕ → X → ℝ) (n : ℕ) (s : Fin n → Bool)
    (f : (Fin n → X) → ℝ) (z : Fin n → X) :
    finiteSectionL2Norm w n s f z =
      Real.sqrt (finiteProductIntegral
        (fun i : Fin (n - finiteSectionCount s) => w (finiteSectionFreeOrder n s i))
        (fun v => f (finiteSectionFill n s z v) ^ 2)) := by
  rw [finiteSectionL2Norm, finiteSectionIntegral_orderedFree]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionVanishing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteSectionIntegral_eq_zero_of_fixed (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X)
    (j : Fin n) (hj : s j = true) (hf : ∀ v, v j = z j → f v = 0) :
    finiteSectionIntegral w n s f z = 0 := by
  classical
  rw [finiteSectionIntegral_eq_product]
  unfold finiteProductIntegral
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v j = z j
  · rw [hf v hv, mul_zero]
  · have hz : finiteSectionWeight (w j) (s j) (z j) (v j) = 0 := by
      simp only [finiteSectionWeight, hj, ite_true, hv, ite_false]
    have hp : (∏ i : Fin n, finiteSectionWeight (w i) (s i) (z i) (v i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hz
    rw [hp, zero_mul]

theorem finiteSectionL2Norm_eq_zero_of_fixed (w : ℕ → X → ℝ) (n : ℕ)
    (s : Fin n → Bool) (f : (Fin n → X) → ℝ) (z : Fin n → X)
    (j : Fin n) (hj : s j = true) (hf : ∀ v, v j = z j → f v = 0) :
    finiteSectionL2Norm w n s f z = 0 := by
  unfold finiteSectionL2Norm
  rw [finiteSectionIntegral_eq_zero_of_fixed w n s _ z j hj
    (fun v hv => by rw [hf v hv]; norm_num), Real.sqrt_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_section (T A B : Finset I) (hAT : A ⊆ T)
    (z x y v : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y) =
      productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x)
        (productCoordinateMix Tᶜ y v) := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiA : i ∈ A <;> simp [productCoordinateMix, hiT, hiA]
  · have hiA : i ∉ A := fun h => hiT (hAT h)
    by_cases hiB : i ∈ B <;> simp [productCoordinateMix, hiT, hiA, hiB]

end Erdos3

end

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_eq_normalized (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : K ≠ 0) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x = K ^ A.card * productNormalizedSection μ T A z K f x := by
  simp only [productNormalizedSection, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hK), one_mul]

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductDependsOnMix
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.mix {S T : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn (S ∪ T) f) (z : ∀ i, X i) :
    ProductDependsOn T (fun x => f (productCoordinateMix S z x)) := by
  intro x y hxy
  apply hf
  intro i hi
  by_cases hs : i ∈ S
  · simp only [productCoordinateMix, hs, ite_true]
  · have ht : i ∈ T := (Finset.mem_union.mp hi).resolve_left hs
    simp only [productCoordinateMix, hs, ite_false, hxy i ht]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).mean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change (∏ i, (μ i).weight (x i)) * g (fun j => x (e j)) =
    (∏ j, (μ (e j)).weight (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem ProductDependsOn.subtypePoint {S : Finset I} {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x base : ∀ i, X i) :
    f (productSubtypePoint S (fun i => x i) base) = f x := by
  apply hf
  intro i hi
  exact productSubtypePoint_apply_mem S (fun j => x j) base ⟨i, hi⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMean_restrict (S : Finset I) (g : (∀ i : S, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean g := by
  classical
  let pS := FiniteProbabilityWeights.pi (fun i : S => μ i)
  let pC := FiniteProbabilityWeights.pi (fun i : {i // i ∉ S} => μ i)
  have hw (x : ∀ i, X i) : (FiniteProbabilityWeights.pi μ).weight x =
      pS.weight (fun i => x i) * pC.weight (fun i => x i) := by
    have hu : @Finset.univ S (Subtype.fintype (fun i : I => i ∈ S)) =
        @Finset.univ S (Finset.Subtype.fintype S) := by
      ext i
      simp only [Finset.mem_univ]
    simpa only [pS, pC, FiniteProbabilityWeights.pi, hu] using
      (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S) (fun i => (μ i).weight (x i))).symm
  calc
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun i => x i)) =
        ∑ z : (∀ i : S, X i) × (∀ i : {i // i ∉ S}, X i),
          pS.weight z.1 * pC.weight z.2 * g z.1 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) X)
      intro x
      change (FiniteProbabilityWeights.pi μ).weight x * g (fun i => x i) =
        pS.weight (fun i => x i) * pC.weight (fun i => x i) * g (fun i => x i)
      rw [hw]
    _ = pS.mean g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      calc
        (∑ v, pS.weight z * pC.weight v * g z) = pS.weight z * g z * ∑ v, pC.weight v := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = pS.weight z * g z := by rw [pC.total, mul_one]

theorem productMean_of_depends (S : Finset I) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn S f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean f =
      (FiniteProbabilityWeights.pi (fun i : S => μ i)).mean
        (fun z => f (productSubtypePoint S z base)) := by
  rw [← productMean_restrict μ S]
  congr 1
  funext x
  exact (hf.subtypePoint x base).symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

theorem productTuplePoint_apply (a : J → I) (ha : Function.Injective a)
    (v : ∀ j, X (a j)) (base : ∀ i, X i) (j : J) :
    productTuplePoint a ha v base (a j) = v j := by
  unfold productTuplePoint
  exact (productSubtypePoint_apply_mem (Finset.univ.image a) _ base
    (productTupleIndexEquiv a ha j)).trans
      (Equiv.piCongrLeft_apply_apply (fun i : ↥(Finset.univ.image a) => X i)
        (productTupleIndexEquiv a ha) v j)

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_tuple (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (f : (∀ i, X i) → ℝ)
    (hf : ProductDependsOn (Finset.univ.image a) f) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).mean
      (fun v => f (productTuplePoint a ha v base)) = (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productMean_of_depends μ (Finset.univ.image a) f hf base]
  let e := productTupleIndexEquiv a ha
  let eP := Equiv.piCongrLeft (fun i : ↥(Finset.univ.image a) => X i) e
  have h := productMean_reindex (fun i : ↥(Finset.univ.image a) => μ i) e
    (fun v => f (productTuplePoint a ha v base))
  have he (x : ∀ i : ↥(Finset.univ.image a), X i) :
      productTuplePoint a ha (fun j => x (e j)) base =
        productSubtypePoint (Finset.univ.image a) x base := by
    change productSubtypePoint (Finset.univ.image a) (eP (eP.symm x)) base = _
    rw [eP.apply_symm_apply]
  simp_rw [he] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_inclusion_exclusion (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productANOVA μ S f x = ∑ T ∈ S.powerset,
      (-1 : ℝ) ^ (S.card - T.card) * productConditionalMean μ T f x := by
  unfold productANOVA
  apply Finset.sum_bij' (fun U _ => S \ U) (fun T _ => S \ T)
  · intro U _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro T _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro U hU
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hU)
  · intro T hT
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
  · intro U hU
    have hu := Finset.mem_powerset.mp hU
    have hc : S.card - (S \ U).card = U.card := by
      rw [Finset.card_sdiff_of_subset hu]
      exact Nat.sub_sub_self (Finset.card_le_card hu)
    rw [hc]

theorem productANOVA_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productANOVA μ S f) := by
  intro x y hxy
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact productConditionalMean_depends μ (S \ U) f x y
    (fun i hi => hxy i (Finset.sdiff_subset hi))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_sectionAverage (T A U : Finset I) (hAT : A ⊆ T)
    (hTU : Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ U (productSectionAverage μ T A z f) x =
      ∑ B ∈ U.powerset, (-1 : ℝ) ^ (U.card - B.card) *
        productConditionalMean μ (A ∪ B) f (productCoordinateMix T z x) := by
  rw [productANOVA_inclusion_exclusion]
  apply Finset.sum_congr rfl
  intro B hB
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  have hBT : Disjoint B T := hTU.symm.mono_left (Finset.mem_powerset.mp hB)
  rw [Finset.sdiff_eq_self_of_disjoint hBT]

theorem productANOVA_disjoint_section (T U : Finset I) (hTU : Disjoint T U)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ (T ∪ U) f (productCoordinateMix T z x) =
      ∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
        productANOVA μ U (productSectionAverage μ T A z f) x := by
  rw [productANOVA_inclusion_exclusion, disjoint_powerset_sum T U hTU]
  apply Finset.sum_congr rfl
  intro A hA
  have hAT := Finset.mem_powerset.mp hA
  rw [productANOVA_sectionAverage μ T A U hAT hTU, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hBU := Finset.mem_powerset.mp hB
  have hAB : Disjoint A B := hTU.mono hAT hBU
  have he : (T ∪ U).card - (A ∪ B).card = (T.card - A.card) + (U.card - B.card) := by
    rw [Finset.card_union_of_disjoint hTU, Finset.card_union_of_disjoint hAB]
    have ha := Finset.card_le_card hAT
    have hb := Finset.card_le_card hBU
    omega
  rw [he, pow_add, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVAEnergy_mono {D E : Finset (Finset I)} (hDE : D ⊆ E)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ D f ≤ productANOVAEnergy μ E f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hDE
  intro U _ _
  exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _)

theorem productANOVAEnergy_le_level (D : Finset (Finset I)) (d : ℕ)
    (hD : ∀ U ∈ D, U.card = d) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ productANOVAEnergy μ (Finset.univ.powersetCard d) f := by
  apply productANOVAEnergy_mono μ _ f
  intro U hU
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD U hU⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVATensorChoices
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

omit [Fintype I] [LinearOrder I] in
theorem coordinateUnionWeight_nonneg (z : Sigma X) : 0 ≤ coordinateUnionWeight μ z :=
  (μ z.1).nonneg z.2

theorem productANOVATensor_zero_of_not_ordered (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X)
    (hz : ¬StrictMono (fun j => (z j).1)) : productANOVATensor μ k base f z = 0 := by
  simp only [productANOVATensor, hz, dite_false]

theorem productANOVATensor_zero_of_zero_weight (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) (j : Fin k)
    (hj : coordinateUnionWeight μ (z j) = 0) : productANOVATensor μ k base f z = 0 := by
  have hw : (∏ i, coordinateUnionWeight μ (z i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hj
  simp [productANOVATensor, hw]

theorem productANOVATensor_weighted_sq (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (a : Fin k → I) (v : ∀ j, X (a j)) :
    (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
      productANOVATensor μ k base f (fun j => ⟨a j, v j⟩) ^ 2 =
    if ha : StrictMono a then
      (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
        productANOVA μ (Finset.univ.image a) f (productTuplePoint a ha.injective v base) ^ 2
    else 0 := by
  classical
  by_cases ha : StrictMono a
  · simp only [productANOVATensor, ha, dite_true]
    change _ * (if (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v = 0 then 0 else _) ^ 2 = _
    by_cases hw : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v = 0
    · simp only [hw, zero_mul]
    · simp only [hw, ite_false]
  · simp only [productANOVATensor, ha, dite_false, zero_pow (by decide : 2 ≠ 0), mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_null_section (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (s : Fin k → Bool) (z : Fin k → Sigma X)
    (j : Fin k) (hj : s j = true) (hz : coordinateUnionWeight μ (z j) = 0) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k s (productANOVATensor μ k base f) z = 0 := by
  apply finiteSectionL2Norm_eq_zero_of_fixed _ k s _ z j hj
  intro v hv
  apply productANOVATensor_zero_of_zero_weight μ k base f v j
  rw [hv, hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

variable {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorGroupedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {J I : Type*} {X : I → Type*}

theorem finiteTaggedTuple_sum [Fintype I] [Fintype J] [DecidableEq J]
    [∀ i, Fintype (X i)] (F : (J → Sigma X) → ℝ) :
    (∑ z, F z) = ∑ a : J → I, ∑ v : ∀ j, X (a j), F (fun j => ⟨a j, v j⟩) := by
  classical
  calc
    (∑ z, F z) = ∑ av : Σ a : J → I, ∀ j, X (a j), F (fun j => ⟨av.1 j, av.2 j⟩) :=
      Fintype.sum_equiv finiteTaggedTupleEquiv _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem orderedFamilyTensor_energy (μ : ∀ i, FiniteProbabilityWeights (X i))
    (k : ℕ) (base : ∀ i, X i) (F : Finset I → (∀ i, X i) → ℝ)
    (hF : ∀ S, ProductDependsOn S (F S)) :
    finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
      (fun z => orderedFamilyTensor k base F z ^ 2) =
        ∑ S ∈ Finset.univ.powersetCard k, (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2) := by
  classical
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  calc
    _ = ∑ a : Fin k → I, if StrictMono a then
        (FiniteProbabilityWeights.pi μ).mean (fun x => F (Finset.univ.image a) x ^ 2) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : StrictMono a
      · simp only [orderedFamilyTensor, ha, dite_true, ite_true]
        refine productMean_tuple μ a ha.injective
          (fun x => F (Finset.univ.image a) x ^ 2) ?_ base
        intro x y hxy
        exact congrArg (fun t : ℝ => t ^ 2) (hF (Finset.univ.image a) x y hxy)
      · simp only [orderedFamilyTensor, ha, dite_false, ite_false,
          zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero]
    _ = _ := finiteOrderedSubset_sum k (fun S => (FiniteProbabilityWeights.pi μ).mean (fun x => F S x ^ 2))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] {k : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductTupleSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productTuplePoint_weight_ne_zero (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (v : ∀ j, X (a j)) (base : ∀ i, X i)
    (hb : (FiniteProbabilityWeights.pi μ).weight base ≠ 0)
    (hv : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v ≠ 0) :
    (FiniteProbabilityWeights.pi μ).weight (productTuplePoint a ha v base) ≠ 0 := by
  change (∏ i, (μ i).weight (base i)) ≠ 0 at hb
  change (∏ j, (μ (a j)).weight (v j)) ≠ 0 at hv
  change (∏ i, (μ i).weight (productTuplePoint a ha v base i)) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  by_cases hi : i ∈ Finset.univ.image a
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    rw [productTuplePoint_apply]
    exact Finset.prod_ne_zero_iff.mp hv j (Finset.mem_univ j)
  · have he : productTuplePoint a ha v base i = base i := by
      simp only [productTuplePoint, productSubtypePoint, hi, dite_false]
    rw [he]
    exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)

theorem exists_positive_productTuplePoint (μ : ∀ i, FiniteProbabilityWeights (X i))
    (a : J → I) (ha : Function.Injective a) (v : ∀ j, X (a j))
    (hv : (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v ≠ 0) :
    ∃ x : ∀ i, X i, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 ∧ ∀ j, x (a j) = v j := by
  obtain ⟨base, hb⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  exact ⟨productTuplePoint a ha v base, productTuplePoint_weight_ne_zero μ a ha v base hb hv,
    productTuplePoint_apply a ha v base⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => c * f y) x = c * productANOVA μ S f x := by
  simp only [productANOVA, productConditionalMean_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

theorem productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D (fun y => c * f y) = c ^ 2 * productANOVAEnergy μ D f := by
  simp only [productANOVAEnergy, productANOVA_smul, mul_pow,
    FiniteProbabilityWeights.mean_const_mul, Finset.mul_sum]

theorem sqrt_productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVAEnergy μ D (fun y => c * f y)) =
      |c| * Real.sqrt (productANOVAEnergy μ D f) := by
  rw [productANOVAEnergy_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem sqrt_productANOVASectionEnergy_le (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z f)) := by
  have hsign (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have h := (FiniteProbabilityWeights.pi μ).sqrt_sum_mean_sq_triangle T.powerset D
    (fun A U x => (-1 : ℝ) ^ (T.card - A.card) *
      productANOVA μ U (productSectionAverage μ T A z f) x)
  have he : productANOVASectionEnergy μ T D z f =
      ∑ U ∈ D, (FiniteProbabilityWeights.pi μ).mean (fun x =>
        (∑ A ∈ T.powerset, (-1 : ℝ) ^ (T.card - A.card) *
          productANOVA μ U (productSectionAverage μ T A z f) x) ^ 2) := by
    apply Finset.sum_congr rfl
    intro U hU
    congr 1
    funext x
    rw [productANOVA_disjoint_section μ T U (hD U hU)]
  rw [he]
  simpa only [mul_pow, hsign, one_mul, productANOVAEnergy] using h

theorem sqrt_productANOVASectionEnergy_le_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤
      ∑ A ∈ T.powerset, K ^ A.card *
        Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) := by
  apply (sqrt_productANOVASectionEnergy_le μ T D hD z f).trans_eq
  apply Finset.sum_congr rfl
  intro A _
  have he : productSectionAverage μ T A z f =
      fun x => K ^ A.card * productNormalizedSection μ T A z K f x :=
    funext (productSectionAverage_eq_normalized μ T A z hK.ne' f)
  rw [he, sqrt_productANOVAEnergy_smul, abs_of_nonneg (pow_nonneg hK.le _)]

theorem sqrt_productANOVASectionEnergy_le_of_normalized (T : Finset I) (D : Finset (Finset I))
    (hD : ∀ U ∈ D, Disjoint T U) (z : ∀ i, X i) {K B : ℝ} (hK : 0 < K)
    (f : (∀ i, X i) → ℝ)
    (hB : ∀ A ∈ T.powerset,
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (productANOVASectionEnergy μ T D z f) ≤ (1 + K) ^ T.card * B := by
  apply (sqrt_productANOVASectionEnergy_le_normalized μ T D hD z hK f).trans
  calc
    (∑ A ∈ T.powerset, K ^ A.card *
      Real.sqrt (productANOVAEnergy μ D (productNormalizedSection μ T A z K f)))
        ≤ ∑ A ∈ T.powerset, K ^ A.card * B :=
      Finset.sum_le_sum (fun A hA => mul_le_mul_of_nonneg_left (hB A hA) (pow_nonneg hK.le _))
    _ = (1 + K) ^ T.card * B := by
      rw [← Finset.sum_mul]
      congr 1
      simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : I => K) T).symm

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

omit μ [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)] in
theorem anovaSection_power_bound {j k : ℕ} (hjk : j ≤ k) {K R : ℝ}
    (hK : 1 ≤ K) (hR : 1 + K ≤ R) :
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ (2 * k - j) := by
  have hR0 : 0 ≤ R := by linarith
  calc
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ j * R ^ (2 * (k - j)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hR j) (pow_nonneg hR0 _)
    _ = R ^ (2 * k - j) := by
      rw [← pow_add]
      congr 1
      omega

omit μ [Fintype I] [DecidableEq I] [∀ i, Fintype (X i)] in
theorem anovaSection_power_bound_positive {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 1 + K ≤ R) :
    (1 + K) ^ j * R ^ (2 * (k - j)) ≤ R ^ (2 * k - 1) :=
  (anovaSection_power_bound hjk hK hR).trans (pow_le_pow_right₀ (by linarith) (by omega))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

omit μ [∀ i, Fintype (X i)] in
theorem mem_disjointCoordinateLevel (T U : Finset I) (d : ℕ) :
    U ∈ disjointCoordinateLevel T d ↔ Disjoint T U ∧ U.card = d := by
  simp only [disjointCoordinateLevel, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and, and_comm]

theorem productANOVASectionTensor_energy (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2) =
        productANOVASectionEnergy μ T (disjointCoordinateLevel T d) z f := by
  unfold productANOVASectionTensor
  rw [orderedFamilyTensor_energy μ]
  · simp only [productANOVASectionEnergy, disjointCoordinateLevel, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro U _
    by_cases hTU : Disjoint T U
    · simp only [hTU, ite_true]
    · simp only [hTU, ite_false, zero_pow (by decide : 2 ≠ 0), FiniteProbabilityWeights.mean_const]
  · intro U
    by_cases hTU : Disjoint T U
    · simpa only [hTU, ite_true] using (productANOVA_depends μ (T ∪ U) f).mix z
    · intro x y _
      simp only [hTU, ite_false]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVASectionTensor_bound_of_normalized (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) {K B : ℝ} (hK : 0 < K) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ A ⊆ T,
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d)
        (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2)) ≤ (1 + K) ^ T.card * B := by
  rw [productANOVASectionTensor_energy]
  apply sqrt_productANOVASectionEnergy_le_of_normalized μ T (disjointCoordinateLevel T d)
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).1) z hK f
  intro A hA
  apply (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (disjointCoordinateLevel T d) d
    (fun U hU => ((mem_disjointCoordinateLevel T U d).mp hU).2)
    (productNormalizedSection μ T A z K f))).trans
  exact hLower A (Finset.mem_powerset.mp hA)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorSectionPointwise
namespace OAI

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem finiteSectionFill_tagSet (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X) :
    Finset.univ.image (fun i => (finiteSectionFill n s z v i).1) =
      finiteFixedTagSet n s z ∪ Finset.univ.image (fun i => (v i).1) := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    by_cases hi : s i = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by rw [finiteSectionFill_fixed n s z v i hi]⟩
    · apply Finset.mem_union_right
      let j := (finiteSectionFreeOrder n s).symm ⟨i, hi⟩
      have he : (finiteSectionFreeOrder n s j : Fin n) = i :=
        congrArg Subtype.val ((finiteSectionFreeOrder n s).apply_symm_apply ⟨i, hi⟩)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [← he, finiteSectionFill_free]⟩
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [finiteSectionFill_fixed n s z v i i.property]⟩
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨finiteSectionFreeOrder n s j, Finset.mem_univ _, by rw [finiteSectionFill_free]⟩

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [LinearOrder I] {X : I → Type*}

theorem finiteSectionFill_free_strictMono (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    StrictMono (fun i => (v i).1) := by
  intro i j hij
  have he : (finiteSectionFreeOrder n s i : Fin n) < finiteSectionFreeOrder n s j :=
    (finiteSectionFreeOrder n s).strictMono hij
  simpa only [finiteSectionFill_free] using h he

theorem finiteSectionFill_fixed_injective (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1) := by
  intro i j hij
  apply Subtype.ext
  apply h.injective
  simpa only [finiteSectionFill_fixed n s z v i i.property,
    finiteSectionFill_fixed n s z v j j.property] using hij

theorem finiteSectionFill_tags_disjoint (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (v : Fin (n - finiteSectionCount s) → Sigma X)
    (h : StrictMono (fun i => (finiteSectionFill n s z v i).1)) :
    Disjoint (finiteFixedTagSet n s z) (Finset.univ.image (fun i => (v i).1)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb
  have he : (i : Fin n) = finiteSectionFreeOrder n s j := by
    apply h.injective
    simpa only [finiteSectionFill_fixed n s z v i i.property, finiteSectionFill_free] using hi.trans hj.symm
  exact (finiteSectionFreeOrder n s j).property (he ▸ i.property)

theorem finiteFixedTagSet_card (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (hinj : Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1)) :
    (finiteFixedTagSet n s z).card = finiteSectionCount s := by
  rw [finiteFixedTagSet, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    finiteSectionCount_eq_card]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem exists_positive_sectionAnchor (μ : ∀ i, FiniteProbabilityWeights (X i))
    (n : ℕ) (s : Fin n → Bool) (z : Fin n → Sigma X)
    (hinj : Function.Injective (fun i : {i : Fin n // s i = true} => (z i).1))
    (hz : ∀ i, s i = true → coordinateUnionWeight μ (z i) ≠ 0) :
    ∃ a : ∀ i, X i, (FiniteProbabilityWeights.pi μ).weight a ≠ 0 ∧
      ∀ i : {i : Fin n // s i = true}, a (z i).1 = (z i).2 := by
  apply exists_positive_productTuplePoint μ _ hinj (fun i => (z i).2)
  change (∏ i : {i : Fin n // s i = true}, coordinateUnionWeight μ (z i)) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hz i i.property)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_filled_sq_le (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → Sigma X) (base a : ∀ i, X i) (f : (∀ i, X i) → ℝ)
    (ha : ∀ i : {i : Fin n // s i = true}, a (z i).1 = (z i).2)
    (v : Fin (n - finiteSectionCount s) → Sigma X) :
    productANOVATensor μ n base f (finiteSectionFill n s z v) ^ 2 ≤
      productANOVASectionTensor μ (finiteFixedTagSet n s z) (n - finiteSectionCount s) a base f v ^ 2 := by
  classical
  have transport (x : ∀ i, X i) (u w : Sigma X) (h : u = w)
      (hu : x u.1 = u.2) : x w.1 = w.2 := by
    cases h
    exact hu
  by_cases ho : StrictMono (fun i => (finiteSectionFill n s z v i).1)
  · have hv := finiteSectionFill_free_strictMono n s z v ho
    have hd := finiteSectionFill_tags_disjoint n s z v ho
    by_cases hw : (∏ i, coordinateUnionWeight μ (finiteSectionFill n s z v i)) = 0
    · have he : productANOVATensor μ n base f (finiteSectionFill n s z v) = 0 := by
        simp only [productANOVATensor, ho, dite_true, hw, ite_true]
      rw [he, zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · have he : productANOVATensor μ n base f (finiteSectionFill n s z v) =
          productANOVASectionTensor μ (finiteFixedTagSet n s z) (n - finiteSectionCount s) a base f v := by
        simp only [productANOVATensor, ho, dite_true, hw, ite_false,
          productANOVASectionTensor, orderedFamilyTensor, hv, hd, ite_true]
        rw [finiteSectionFill_tagSet]
        apply productANOVA_depends μ _ f
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
          have hj : (z j).1 ∈ finiteFixedTagSet n s z :=
            Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
          simp only [productCoordinateMix, hj, ite_true]
          have he := productTuplePoint_apply (fun i => (finiteSectionFill n s z v i).1)
            ho.injective (fun i => (finiteSectionFill n s z v i).2) base j
          have he' : productTuplePoint (fun i => (finiteSectionFill n s z v i).1)
              ho.injective (fun i => (finiteSectionFill n s z v i).2) base (z j).1 = (z j).2 := by
            exact transport _ _ _ (finiteSectionFill_fixed n s z v j j.property) he
          exact he'.trans (ha j).symm
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
          have hj : (v j).1 ∉ finiteFixedTagSet n s z := fun h =>
            Finset.disjoint_left.mp hd h (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
          simp only [productCoordinateMix, hj, ite_false]
          have he := productTuplePoint_apply (fun i => (finiteSectionFill n s z v i).1)
            ho.injective (fun i => (finiteSectionFill n s z v i).2) base (finiteSectionFreeOrder n s j)
          have he' : productTuplePoint (fun i => (finiteSectionFill n s z v i).1)
              ho.injective (fun i => (finiteSectionFill n s z v i).2) base (v j).1 = (v j).2 := by
            exact transport _ _ _ (finiteSectionFill_free n s z v j) he
          exact he'.trans (productTuplePoint_apply _ hv.injective (fun i => (v i).2) base j).symm
      exact le_of_eq (congrArg (fun x : ℝ => x ^ 2) he)
  · rw [productANOVATensor_zero_of_not_ordered μ n base f _ ho, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVALpBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_energy (k : ℕ) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
      (fun z => productANOVATensor μ k base f z ^ 2) =
        productANOVAEnergy μ (Finset.univ.powersetCard k) f := by
  classical
  unfold finiteProductIntegral
  rw [finiteTaggedTuple_sum]
  calc
    _ = ∑ a : Fin k → I, if StrictMono a then
        (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ (Finset.univ.image a) f x ^ 2)
      else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      change (∑ v, (FiniteProbabilityWeights.pi (fun j => μ (a j))).weight v *
        productANOVATensor μ k base f (fun j => ⟨a j, v j⟩) ^ 2) = _
      simp_rw [productANOVATensor_weighted_sq]
      by_cases ha : StrictMono a
      · simp only [ha, dite_true, ite_true]
        refine productMean_tuple μ a ha.injective
          (fun x => productANOVA μ (Finset.univ.image a) f x ^ 2) ?_ base
        intro x y hxy
        exact congrArg (fun t : ℝ => t ^ 2) (productANOVA_depends μ (Finset.univ.image a) f x y hxy)
      · simp only [ha, dite_false, ite_false, Finset.sum_const_zero]
    _ = _ := finiteOrderedSubset_sum k
      (fun S => (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2))

theorem productANOVATensor_unfixed_section (k : ℕ) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (z : Fin k → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k (fun _ => false)
      (productANOVATensor μ k base f) z =
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) f) := by
  rw [finiteSectionL2Norm, finiteSectionIntegral_eq_product]
  change Real.sqrt (finiteProductIntegral (fun _ : Fin k => coordinateUnionWeight μ)
    (fun v => productANOVATensor μ k base f v ^ 2)) = _
  rw [productANOVATensor_energy]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [LinearOrder I] [Fintype J] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductTensorNormalizedUniform
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_section_bound_of_normalized (n : ℕ) (s : Fin n → Bool)
    (z : Fin n → Sigma X) (base : ∀ i, X i) {K B : ℝ} (hK : 1 ≤ K) (hB : 0 ≤ B)
    (f : (∀ i, X i) → ℝ)
    (hLower : ∀ T : Finset I, T.card = finiteSectionCount s → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - finiteSectionCount s))
          (productNormalizedSection μ T A a K f)) ≤ B) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      (1 + K) ^ finiteSectionCount s * B := by
  classical
  have hbound : 0 ≤ (1 + K) ^ finiteSectionCount s * B :=
    mul_nonneg (pow_nonneg (by linarith) _) hB
  by_cases hn : ∃ i, s i = true ∧ coordinateUnionWeight μ (z i) = 0
  · obtain ⟨i, hi, hz⟩ := hn
    rw [productANOVATensor_null_section μ n base f s z i hi hz]
    exact hbound
  · have hz : ∀ i, s i = true → coordinateUnionWeight μ (z i) ≠ 0 :=
      fun i hi he => hn ⟨i, hi, he⟩
    by_cases ho : ∃ v : Fin (n - finiteSectionCount s) → Sigma X,
        StrictMono (fun i => (finiteSectionFill n s z v i).1)
    · obtain ⟨v, hv⟩ := ho
      have hinj := finiteSectionFill_fixed_injective n s z v hv
      have hcard := finiteFixedTagSet_card n s z hinj
      obtain ⟨a, ha, haz⟩ := exists_positive_sectionAnchor μ n s z hinj hz
      rw [finiteSectionL2Norm_orderedFree]
      apply (Real.sqrt_le_sqrt (finiteProductIntegral_mono
        (fun _ : Fin (n - finiteSectionCount s) => coordinateUnionWeight μ)
        (fun _ x => coordinateUnionWeight_nonneg μ x) _ _
        (productANOVATensor_filled_sq_le μ n s z base a f haz))).trans
      have h := productANOVASectionTensor_bound_of_normalized μ (finiteFixedTagSet n s z)
        (n - finiteSectionCount s) a base (by linarith : 0 < K) f
        (hLower _ hcard a ha)
      simpa only [hcard] using h
    · rw [finiteSectionL2Norm_orderedFree]
      have he (v : Fin (n - finiteSectionCount s) → Sigma X) :
          productANOVATensor μ n base f (finiteSectionFill n s z v) = 0 :=
        productANOVATensor_zero_of_not_ordered μ n base f _ (fun hv => ho ⟨v, hv⟩)
      simp only [he, zero_pow (by decide : 2 ≠ 0), finiteProductIntegral, mul_zero,
        Finset.sum_const_zero, Real.sqrt_zero]
      exact hbound

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_uniform_of_normalized (n : ℕ) (base : ∀ i, X i)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ n → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - T.card))
          (productNormalizedSection μ T A a K f)) ≤ R ^ (2 * (n - T.card)))
    (s : Fin n → Bool) (z : Fin n → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) f)) (R ^ (2 * n - 1)) := by
  by_cases hs : finiteSectionCount s = 0
  · have he : s = fun _ => false := funext ((finiteSectionCount_eq_zero_iff n s).mp hs)
    rw [he, productANOVATensor_unfixed_section]
    exact le_max_left _ _
  · have hj : 0 < finiteSectionCount s := Nat.pos_of_ne_zero hs
    have hjn := finiteSectionCount_le n s
    have hb := productANOVATensor_section_bound_of_normalized μ n s z base hK
      (pow_nonneg (by linarith : 0 ≤ R) _) f (by
        intro T hT a ha A hAT
        simpa only [hT] using hLower T (by omega) (by omega) a ha A hAT)
    exact (hb.trans (anovaSection_power_bound_positive hj hjn hK hR)).trans (le_max_right _ _)

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.productANOVATensor_uniform_of_normalized.{u_1, u_2} := @OAI.Erdos3.productANOVATensor_uniform_of_normalized.{u_1, u_2}
