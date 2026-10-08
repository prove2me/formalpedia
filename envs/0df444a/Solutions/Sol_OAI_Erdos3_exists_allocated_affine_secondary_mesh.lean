-- Prove2me | solution 1 for OAI.Erdos3.exists_allocated_affine_secondary_mesh
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:41:16.071427+00:00
-- url     : https://prove2.me/submissions/fe3639b5-c2cf-42ad-af25-a4967b2471b4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016
import Theorems.Thm_OAI_Erdos3_normalizedBoxPartitions_positive
import Theorems.Thm_OAI_Erdos3_normalizedMesh_scale_large

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_mono {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E F : Ω → Prop) (hEF : ∀ x, E x → F x) : p.eventProbability E ≤ p.eventProbability F := by
  classical
  apply p.mean_mono
  intro x
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · simp only [hE, ite_false]
    split_ifs <;> norm_num

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem replacementAccuracy_spec {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    0 < replacementAccuracy B epsilon ∧ replacementAccuracy B epsilon ≤ 1 ∧
      B * replacementAccuracy B epsilon ≤ epsilon := by
  have hden : 0 < 1 + B := by positivity
  refine ⟨lt_min zero_lt_one (div_pos hepsilon hden), min_le_left _ _, ?_⟩
  calc
    _ ≤ B * (epsilon / (1 + B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hB
    _ ≤ epsilon := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      nlinarith

theorem replacementAccuracy_inverse_le_exp {B epsilon P : ℝ}
    (hB0 : 0 ≤ B) (hepsilon : 0 < epsilon) (hP : 0 ≤ P)
    (hB : B ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P) :
    (replacementAccuracy B epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold replacementAccuracy
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by linarith : 0 ≤ 2 * P + 2)
  · rw [inv_div, div_eq_mul_inv]
    calc
      (1 + B) * epsilon⁻¹ ≤ (1 + Real.exp P) * Real.exp P :=
        mul_le_mul (by linarith) heps (inv_nonneg.mpr hepsilon.le) (by positivity)
      _ ≤ 2 * (Real.exp P) ^ 2 := by nlinarith
      _ ≤ Real.exp 2 * (Real.exp P) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerBoxCharacterBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerInterval_indicator_expect (a b : ℤ) (hab : a ≤ b) (E : ℤ → Prop)
    [DecidablePred E] :
    (𝔼 x : Finset.Ico a b, if E x then (1 : ℝ) else 0) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  classical
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (Finset.Ico a b) (fun x : ℤ => if E x then (1 : ℝ) else 0),
    Fintype.card_coe]
  have hcard : ((Finset.Ico a b).card : ℝ) = ((b - a : ℤ) : ℝ) := by
    exact_mod_cast Int.card_Ico_of_le a b hab
  rw [hcard]
  congr 1
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEventUnion
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_or_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (E F : Ω → Prop) :
    p.eventProbability (fun x => E x ∨ F x) ≤ p.eventProbability E + p.eventProbability F := by
  classical
  unfold eventProbability
  calc
    _ ≤ p.mean (fun x => (if E x then 1 else 0) + (if F x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF]
    _ = _ := p.mean_add _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

variable [MeasurableSpace C]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem intervalUniformWeights_mean (a b : ℤ) (hab : a < b) (f : Finset.Ico a b → ℝ) :
    (intervalUniformWeights a b hab).mean f = 𝔼 x, f x := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  unfold intervalUniformWeights
  exact FiniteProbabilityWeights.uniform_mean f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem comparableBoxPartitions_length {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    H i ≤ (comparableBoxPartitions N H hH hHN i).length k ∧
      (comparableBoxPartitions N H hH hHN i).length k < 2 * H i :=
  FiniteProgressionPartition.mergedIntervals_length_bounds (N i) (H i) (hH i) (hHN i) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem physicalBoxCell_eq_iff (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (x : translatedIntegerBox lo N) (c : ∀ i, (P i).Label) :
    physicalBoxCell lo N P x = c ↔ ∀ i,
      intervalCellLower (lo i) (P i) (c i) ≤ x.val i ∧ x.val i < intervalCellUpper (lo i) (P i) (c i) := by
  change (fun i => intervalResidueCell (lo i) (P i) 1 0 ((physicalBoxUnitResidueEquiv lo N x) i)) = c ↔ _
  rw [funext_iff]
  exact forall_congr' (fun i => intervalResidueCell_eq_iff (lo i) (P i) (hstep i) 1 0 _ (c i))

theorem physicalBoxCell_subset (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i)) (fun i => (P i).length (c i)) ⊆
      translatedIntegerBox lo N := by
  intro x hx
  apply (mem_translatedIntegerBox lo N x).mpr
  intro i
  have hi := (mem_translatedIntegerBox _ _ x).mp hx i
  have hend : ((P i).start (c i) : ℤ) + (P i).length (c i) ≤ N i := by
    exact_mod_cast (P i).end_le_of_step_one (hstep i) (c i) (hpos i (c i))
  have hstart : (0 : ℤ) ≤ (P i).start (c i) := Int.natCast_nonneg _
  dsimp only [intervalCellLower] at hi
  constructor <;> omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalBoundaryLabels
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_cut_side_stable {a u v : ℤ} {r : ℕ}
    (hmove : |u - v| ≤ (r : ℤ)) (hfar : (r : ℤ) < |u - a|) :
    a ≤ u ↔ a ≤ v := by
  have hm := abs_le.mp hmove
  by_cases h : a ≤ u
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hfar
    have hv : a ≤ v := by omega
    exact ⟨fun _ => hv, fun _ => h⟩
  · have hu : u ≤ a := by omega
    rw [abs_of_nonpos (sub_nonpos.mpr hu)] at hfar
    have hv : ¬ a ≤ v := by omega
    exact ⟨fun h' => (h h').elim, fun h' => (hv h').elim⟩

theorem integer_interval_membership_stable {a b u v : ℤ} {r : ℕ}
    (hmove : |u - v| ≤ (r : ℤ))
    (hleft : (r : ℤ) < |u - a|) (hright : (r : ℤ) < |u - b|) :
    (a ≤ u ∧ u < b) ↔ (a ≤ v ∧ v < b) := by
  have hl := integer_cut_side_stable hmove hleft
  have hr := integer_cut_side_stable hmove hright
  constructor <;> intro h <;> constructor <;> omega

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem physicalBoxClassify_eq_some_iff (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (x : I → ℤ) (c : ∀ i, (P i).Label) :
    physicalBoxClassify lo N P x = some c ↔ ∀ i,
      intervalCellLower (lo i) (P i) (c i) ≤ x i ∧ x i < intervalCellUpper (lo i) (P i) (c i) := by
  constructor
  · intro h
    by_cases hx : x ∈ translatedIntegerBox lo N
    · simp only [physicalBoxClassify, dif_pos hx, Option.some.injEq] at h
      exact (physicalBoxCell_eq_iff lo N P hstep ⟨x, hx⟩ c).mp h
    · simp only [physicalBoxClassify, dif_neg hx] at h
      cases h
  · intro h
    have hxcell : x ∈ translatedIntegerBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) := by
      apply (mem_translatedIntegerBox _ _ x).mpr
      intro i
      exact h i
    have hx := physicalBoxCell_subset lo N P hstep hpos c hxcell
    have hc := (physicalBoxCell_eq_iff lo N P hstep ⟨x, hx⟩ c).mpr h
    simp only [physicalBoxClassify, dif_pos hx, Option.some.injEq]
    exact hc

theorem physicalBoxClassify_stable (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (r : I → ℕ) (u v : I → ℤ)
    (hmove : ∀ i, |u i - v i| ≤ (r i : ℤ)) (hfar : ¬ physicalBoundaryNear lo N P r u) :
    physicalBoxClassify lo N P u = physicalBoxClassify lo N P v := by
  have hi (i : I) (c : (P i).Label) :
      (intervalCellLower (lo i) (P i) c ≤ u i ∧ u i < intervalCellUpper (lo i) (P i) c) ↔
      (intervalCellLower (lo i) (P i) c ≤ v i ∧ v i < intervalCellUpper (lo i) (P i) c) := by
    apply integer_interval_membership_stable (hmove i)
    · exact lt_of_not_ge (fun h => hfar ⟨i, c, Or.inl h⟩)
    · exact lt_of_not_ge (fun h => hfar ⟨i, c, Or.inr h⟩)
  have hc (c : ∀ i, (P i).Label) :
      physicalBoxClassify lo N P u = some c ↔ physicalBoxClassify lo N P v = some c := by
    rw [physicalBoxClassify_eq_some_iff lo N P hstep hpos u c,
      physicalBoxClassify_eq_some_iff lo N P hstep hpos v c]
    exact forall_congr' (fun i => hi i (c i))
  cases hu : physicalBoxClassify lo N P u with
  | some c => exact ((hc c).mp hu).symm
  | none =>
      cases hv : physicalBoxClassify lo N P v with
      | none => rfl
      | some c =>
          have h := (hc c).mpr hv
          rw [hu] at h
          cases h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothIntegerTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothAffineSample_variation {J I : Type*} [Fintype J]
    (t u : J → ℤ) (z w : Option J × I → ℤ) (i : I)
    {T V r0 rV rt : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (ht : ∀ j, |(t j : ℝ)| ≤ T)
    (hw : ∀ j, |(w (some j, i) : ℝ)| ≤ V)
    (hbase : |(z (none, i) : ℝ) - w (none, i)| ≤ r0)
    (hdir : ∀ j, |(z (some j, i) : ℝ) - w (some j, i)| ≤ rV)
    (hparam : ∀ j, |(t j : ℝ) - u j| ≤ rt) :
    |(smoothAffineSample t z i : ℝ) - smoothAffineSample u w i| ≤
      r0 + (Fintype.card J : ℝ) * (T * rV + V * rt) := by
  have hid : (smoothAffineSample t z i : ℝ) - smoothAffineSample u w i =
      ((z (none, i) : ℝ) - w (none, i)) +
        ∑ j, ((t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)) := by
    simp only [smoothAffineSample, Int.cast_add, Int.cast_sum, Int.cast_mul, Finset.sum_sub_distrib]
    ring
  have hterm (j : J) : |(t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)| ≤ T * rV + V * rt := by
    calc
      _ = |(t j : ℝ) * ((z (some j, i) : ℝ) - w (some j, i)) +
          (w (some j, i) : ℝ) * ((t j : ℝ) - u j)| := by congr 1; ring
      _ ≤ |(t j : ℝ) * ((z (some j, i) : ℝ) - w (some j, i))| +
          |(w (some j, i) : ℝ) * ((t j : ℝ) - u j)| := abs_add_le _ _
      _ ≤ T * rV + V * rt := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul (ht j) (hdir j) (abs_nonneg _) hT)
          (mul_le_mul (hw j) (hparam j) (abs_nonneg _) hV)
  rw [hid]
  calc
    _ ≤ |(z (none, i) : ℝ) - w (none, i)| +
        |∑ j, ((t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i))| := abs_add_le _ _
    _ ≤ r0 + ∑ j, |(t j : ℝ) * z (some j, i) - (u j : ℝ) * w (some j, i)| :=
      add_le_add hbase (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ r0 + ∑ _j : J, (T * rV + V * rt) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hterm j))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem interval_event_probability (a b : ℤ) (hab : a < b) (E : ℤ → Prop)
    [DecidablePred E] :
    (intervalUniformWeights a b hab).eventProbability (fun x => E (x : ℤ)) =
      ((Finset.filter E (Finset.Ico a b)).card : ℝ) / ((b - a : ℤ) : ℝ) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean]
  convert integerInterval_indicator_expect a b hab.le E using 1
  congr 1
  funext x
  split_ifs <;> rfl

theorem interval_near_probability (a b v : ℤ) (hab : a < b) (r : ℕ) :
    (intervalUniformWeights a b hab).eventProbability (fun x => |(x : ℤ) - v| ≤ (r : ℤ)) ≤
      (2 * (r : ℝ) + 1) / ((b - a : ℤ) : ℝ) := by
  rw [interval_event_probability a b hab (fun x => |x - v| ≤ (r : ℤ))]
  have hsub : (Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)) ⊆
      Finset.Icc (v - (r : ℤ)) (v + (r : ℤ)) := by
    intro x hx
    have h := abs_le.mp (Finset.mem_filter.mp hx).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have he : (Finset.Icc (v - (r : ℤ)) (v + (r : ℤ))).card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  have hc : ((Finset.filter (fun x => |x - v| ≤ (r : ℤ)) (Finset.Ico a b)).card : ℝ) ≤
      2 * (r : ℝ) + 1 := by
    have h := Finset.card_le_card hsub
    rw [he] at h
    exact_mod_cast h
  exact div_le_div_of_nonneg_right hc (by exact_mod_cast (sub_pos.mpr hab).le)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_le_of_dependent_coordinate_slices {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (i : I) (f : (∀ j, X j) → ℝ) (C : ℝ)
    (hslice : ∀ x : ∀ j, X j, (𝔼 a : X i, f (Function.update x i a)) ≤ C) :
    (𝔼 x : ∀ j, X j, f x) ≤ C := by
  let e := Equiv.piSplitAt i X
  have he := Fintype.expect_equiv e f (fun p => f (e.symm p)) (fun x => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_le Finset.univ_nonempty
  intro r _
  let x : ∀ j, X j := e.symm (Classical.choice inferInstance, r)
  have hupdate (a : X i) : e.symm (a, r) = Function.update x i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.piSplitAt]
    · simp [e, x, Equiv.piSplitAt, hj]
  simpa only [hupdate] using hslice x

theorem integer_box_affine_near_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (lo hi : Option J × I → ℤ) (hlen : ∀ j, lo j < hi j)
    (t : J → ℤ) (i : I) (b : ℤ) (r : ℕ) :
    (integerBoxUniformWeights lo hi hlen).eventProbability
      (fun z => |smoothAffineSample t (fun j => (z j : ℤ)) i - b| ≤ (r : ℤ)) ≤
      (2 * (r : ℝ) + 1) / ((hi (none, i) - lo (none, i) : ℤ) : ℝ) := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  unfold FiniteProbabilityWeights.eventProbability
  rw [integerBoxUniformWeights_mean]
  apply expect_le_of_dependent_coordinate_slices (none, i)
  intro z
  have h := interval_near_probability (lo (none, i)) (hi (none, i))
    (b - ∑ j, t j * (z (some j, i) : ℤ)) (hlen (none, i)) r
  unfold FiniteProbabilityWeights.eventProbability at h
  rw [intervalUniformWeights_mean] at h
  convert h using 1
  apply Finset.expect_congr rfl
  intro a _
  have he : smoothAffineSample t (fun j => ((Function.update z (none, i) a) j : ℤ)) i - b =
      (a : ℤ) - (b - ∑ j, t j * (z (some j, i) : ℤ)) := by
    simp [smoothAffineSample, Function.update]
    ring
  dsimp only
  simp only [he]
  split_ifs <;> rfl

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

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

open scoped BigOperators Classical

theorem integer_box_physical_boundary_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (t : J → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) :
    (integerBoxUniformWeights sourceLo sourceHi hsource).eventProbability
      (fun z => physicalBoundaryNear lo N P r (smoothAffineSample t (fun j => (z j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  let p := integerBoxUniformWeights sourceLo sourceHi hsource
  let E := fun (e : Σ i, (P i).Label) (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    |smoothAffineSample t (fun j => (z j : ℤ)) e.1 - intervalCellLower (lo e.1) (P e.1) e.2| ≤ (r e.1 : ℤ) ∨
    |smoothAffineSample t (fun j => (z j : ℤ)) e.1 - intervalCellUpper (lo e.1) (P e.1) e.2| ≤ (r e.1 : ℤ)
  have hE (e : Σ i, (P i).Label) : p.eventProbability (E e) ≤
      2 * ((2 * (r e.1 : ℝ) + 1) / ((sourceHi (none, e.1) - sourceLo (none, e.1) : ℤ) : ℝ)) := by
    apply (p.eventProbability_or_le _ _).trans
    have hleft := integer_box_affine_near_probability sourceLo sourceHi hsource t e.1
      (intervalCellLower (lo e.1) (P e.1) e.2) (r e.1)
    have hright := integer_box_affine_near_probability sourceLo sourceHi hsource t e.1
      (intervalCellUpper (lo e.1) (P e.1) e.2) (r e.1)
    linarith
  have hcover (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j))
      (h : physicalBoundaryNear lo N P r (smoothAffineSample t (fun j => (z j : ℤ)))) : ∃ e, E e z := by
    obtain ⟨i, c, hc⟩ := h
    exact ⟨⟨i, c⟩, hc⟩
  apply (p.eventProbability_union_bound _ E hcover).trans
  calc
    _ ≤ ∑ e : Σ i, (P i).Label,
        2 * ((2 * (r e.1 : ℝ) + 1) / ((sourceHi (none, e.1) - sourceLo (none, e.1) : ℤ) : ℝ)) :=
      Finset.sum_le_sum (fun e _ => hE e)
    _ = _ := by
      rw [Fintype.sum_sigma]
      unfold physicalBoundaryBudget
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem sampled_physical_boundary_probability {J I T : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype T]
    (parameterLaw : FiniteProbabilityWeights T) (parameter : T → J → ℤ)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)) (r : I → ℕ) :
    (parameterLaw.prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (fun tz => physicalBoundaryNear lo N P r (smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.mean_prod]
  apply (parameterLaw.mean_mono (fun t =>
    integer_box_physical_boundary_probability sourceLo sourceHi hsource (parameter t) lo N P r)).trans_eq
  exact parameterLaw.mean_const _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem physicalMeshCrossing_subset_boundary {I X M : Type*} [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (mesh : X → M) (location : X → I → ℤ) (r : I → ℕ)
    (hmove : ∀ x y, mesh y = mesh x → ∀ i, |location x i - location y i| ≤ (r i : ℤ))
    (x : X) (hx : physicalMeshCrossing lo N P mesh location x) :
    physicalBoundaryNear lo N P r (location x) := by
  by_contra hn
  obtain ⟨y, hy, hxy⟩ := hx
  exact hxy (physicalBoxClassify_stable lo N P hstep hpos r (location x) (location y) (hmove x y hy) hn)

theorem affine_mesh_crossing_probability {J I T SCell TCell : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype T]
    (parameterLaw : FiniteProbabilityWeights T) (parameter : T → J → ℤ)
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ j, sourceLo j < sourceHi j)
    (sourceCell : (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) → SCell) (parameterCell : T → TCell)
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (r : I → ℕ) (r0 rV V : I → ℝ) (Tcap rt : ℝ) (hT : 0 ≤ Tcap) (hV : ∀ i, 0 ≤ V i)
    (ht : ∀ t j, |(parameter t j : ℝ)| ≤ Tcap)
    (hv : ∀ (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) j i, |((z (some j, i) : ℤ) : ℝ)| ≤ V i)
    (hbase : ∀ z w, sourceCell w = sourceCell z → ∀ i,
      |((z (none, i) : ℤ) : ℝ) - ((w (none, i) : ℤ) : ℝ)| ≤ r0 i)
    (hdir : ∀ z w, sourceCell w = sourceCell z → ∀ j i,
      |((z (some j, i) : ℤ) : ℝ) - ((w (some j, i) : ℤ) : ℝ)| ≤ rV i)
    (hparam : ∀ t u, parameterCell u = parameterCell t → ∀ j,
      |(parameter t j : ℝ) - parameter u j| ≤ rt)
    (hbudget : ∀ i, r0 i + (Fintype.card J : ℝ) * (Tcap * rV i + V i * rt) ≤ (r i : ℝ)) :
    (parameterLaw.prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (sourceCell tz.2, parameterCell tz.1))
        (fun tz => smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ)))) ≤
      physicalBoundaryBudget N P r (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) := by
  let mesh := fun tz : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    (sourceCell tz.2, parameterCell tz.1)
  let location := fun tz : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j)) =>
    smoothAffineSample (parameter tz.1) (fun j => (tz.2 j : ℤ))
  have hmove (x y : T × (∀ j, Finset.Ico (sourceLo j) (sourceHi j))) (he : mesh y = mesh x) (i : I) :
      |location x i - location y i| ≤ (r i : ℤ) := by
    have hs : sourceCell y.2 = sourceCell x.2 := congrArg Prod.fst he
    have hp : parameterCell y.1 = parameterCell x.1 := congrArg Prod.snd he
    have h := (smoothAffineSample_variation (parameter x.1) (parameter y.1)
      (fun j => (x.2 j : ℤ)) (fun j => (y.2 j : ℤ)) i hT (hV i) (ht x.1) (fun j => hv y.2 j i)
      (hbase x.2 y.2 hs i) (fun j => hdir x.2 y.2 hs j i) (hparam x.1 y.1 hp)).trans (hbudget i)
    exact_mod_cast h
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _
    (physicalMeshCrossing_subset_boundary lo N P hstep hpos mesh location r hmove)).trans
  exact sampled_physical_boundary_probability parameterLaw parameter sourceLo sourceHi hsource lo N P r

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineInterval_normalized_cap (D : ℕ) (a lo hi x : ℤ) {L C : ℝ}
    (hL : 0 < L) (hx : x ∈ Finset.Ico lo hi)
    (hlow : |((a + (D : ℤ) * lo : ℤ) : ℝ) / L| ≤ C)
    (hhigh : |((a + (D : ℤ) * hi : ℤ) : ℝ) / L| ≤ C) :
    |((a + (D : ℤ) * x : ℤ) : ℝ) / L| ≤ C := by
  have hx' := Finset.mem_Ico.mp hx
  have hleft : ((a + (D : ℤ) * lo : ℤ) : ℝ) ≤ ((a + (D : ℤ) * x : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.1 (Int.natCast_nonneg D))
  have hright : ((a + (D : ℤ) * x : ℤ) : ℝ) ≤ ((a + (D : ℤ) * hi : ℤ) : ℝ) := by
    exact_mod_cast add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hx'.2.le (Int.natCast_nonneg D))
  exact abs_le.mpr ⟨(abs_le.mp hlow).1.trans (div_le_div_of_nonneg_right hleft hL.le),
    (div_le_div_of_nonneg_right hright hL.le).trans (abs_le.mp hhigh).2⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem normalizedBoxPartitions_step {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    (normalizedBoxPartitions N H ρ hlarge hwhole i).step c = 1 := rfl

theorem normalizedBoxPartitions_lengths {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    ρ * H i / 4 ≤ ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ∧
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) ≤ ρ * H i := by
  obtain ⟨_, _, hlo, hup⟩ := normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)
  have hl := comparableBoxPartitions_length N (fun j => ⌊ρ * H j / 2⌋₊)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).1)
    (fun j => (normalizedGridLength_bounds (N j) (H j) ρ (hlarge j) (hwhole j)).2.1) i c
  have hl' : (⌊ρ * H i / 2⌋₊ : ℝ) ≤
      ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) := by exact_mod_cast hl.1
  have hu' : ((normalizedBoxPartitions N H ρ hlarge hwhole i).length c : ℝ) <
      2 * (⌊ρ * H i / 2⌋₊ : ℝ) := by exact_mod_cast hl.2
  exact ⟨hlo.trans hl', by linarith⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalizedBoxPartitions_coordinate_card_le {I : Type*}
    (N : I → ℕ) (H : I → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    {A : ℝ} (hA : 0 ≤ A) (hside : ∀ i, (N i : ℝ) ≤ A * H i) (i : I) :
    (Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label : ℝ) ≤ 4 * A / rho := by
  have hcard : Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label =
      N i / ⌊rho * H i / 2⌋₊ :=
    FiniteProgressionPartition.mergedIntervals_card (N i) ⌊rho * H i / 2⌋₊
      (normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)).1
      (normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)).2.1
  rw [hcard]
  obtain ⟨hpos, _, hlo, _⟩ := normalizedGridLength_bounds (N i) (H i) rho (hlarge i) (hwhole i)
  have hp : (0 : ℝ) < ⌊rho * H i / 2⌋₊ := by exact_mod_cast hpos
  have hq : ((N i / ⌊rho * H i / 2⌋₊ : ℕ) : ℝ) * (⌊rho * H i / 2⌋₊ : ℝ) ≤ N i := by
    exact_mod_cast Nat.div_mul_le_self (N i) ⌊rho * H i / 2⌋₊
  apply ((le_div_iff₀ hp).mpr hq).trans
  apply (div_le_div_iff₀ hp hrho).mpr
  calc
    (N i : ℝ) * rho ≤ (A * H i) * rho := mul_le_mul_of_nonneg_right (hside i) hrho.le
    _ = (4 * A) * (rho * H i / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

theorem rounded_boundary_ratio_le {delta H c width : ℝ}
    (hdelta : 0 < delta) (hH : 0 < H) (hc : 0 < c)
    (hlarge : 1 ≤ delta * H) (hwidth : c * H ≤ width) :
    (2 * (⌈delta * H⌉₊ : ℝ) + 1) / width ≤ 5 * delta / c := by
  have hW : 0 < width := (mul_pos hc hH).trans_le hwidth
  have hceil := (Nat.ceil_lt_add_one (mul_pos hdelta hH).le).le
  have hnum : 2 * (⌈delta * H⌉₊ : ℝ) + 1 ≤ 5 * delta * H := by nlinarith
  apply (div_le_div_iff₀ hW hc).mpr
  calc
    _ ≤ (5 * delta * H) * c := mul_le_mul_of_nonneg_right hnum hc.le
    _ = (5 * delta) * (c * H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (by positivity)

theorem normalized_physical_boundary_budget_le {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) (H width : I → ℝ) (rho : ℝ) (hrho : 0 < rho) (hH : ∀ i, 0 < H i)
    (hlarge : ∀ i, 4 ≤ rho * H i) (hwhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    {A c delta : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hdelta : 0 < delta)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i)
    (hround : ∀ i, 1 ≤ delta * H i) (hwidth : ∀ i, c * H i ≤ width i) :
    physicalBoundaryBudget N (normalizedBoxPartitions N H rho hlarge hwhole)
      (fun i => ⌈delta * H i⌉₊) width ≤
      40 * (Fintype.card I : ℝ) * A * delta / (rho * c) := by
  unfold physicalBoundaryBudget
  calc
    _ ≤ ∑ _i : I, (2 * (4 * A / rho)) * (5 * delta / c) := by
      apply Finset.sum_le_sum
      intro i _
      have hn := normalizedBoxPartitions_coordinate_card_le N H rho hrho hlarge hwhole hA hside i
      have hw := rounded_boundary_ratio_le hdelta (hH i) hc (hround i) (hwidth i)
      have hW : 0 < width i := (mul_pos hc (hH i)).trans_le (hwidth i)
      calc
        _ = (2 * (Fintype.card (normalizedBoxPartitions N H rho hlarge hwhole i).Label : ℝ)) *
            ((2 * (⌈delta * H i⌉₊ : ℝ) + 1) / width i) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hn (by norm_num)) hw (by positivity) (by positivity)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMeshLengths
namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_lower {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    Real.exp lengthLog ≤ delta * scale / 4 := by
  have hinv' := mul_le_mul_of_nonneg_left hinv hdelta.le
  rw [mul_inv_cancel₀ hdelta.ne'] at hinv'
  have hprod := mul_le_mul_of_nonneg_right hinv' (by positivity : 0 ≤ 4 * Real.exp lengthLog)
  have hsize := mul_le_mul_of_nonneg_left hscale hdelta.le
  rw [Real.exp_add] at hsize
  nlinarith

theorem normalizedBoxPartitions_exp_lengths {I : Type*}
    (N : I → ℕ) (scale : I → ℝ) (delta inverseLog lengthLog : ℝ)
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : ∀ i, 4 * Real.exp (inverseLog + lengthLog) ≤ scale i)
    (hlarge : ∀ i, 4 ≤ delta * scale i) (hwhole : ∀ i, delta * scale i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N scale delta hlarge hwhole i).Label) :
    Real.exp lengthLog ≤ ((normalizedBoxPartitions N scale delta hlarge hwhole i).length c : ℝ) :=
  (normalizedMesh_scale_lower hdelta hinv (hscale i)).trans
    (normalizedBoxPartitions_lengths N scale delta hlarge hwhole i c).1

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SecondaryMeshGeometry
namespace OAI

section

namespace Erdos3

theorem secondaryMeshAllocation_spec {boundary movement beta : ℝ}
    (hboundary : 0 ≤ boundary) (hmovement : 0 ≤ movement) (hbeta : 0 < beta) :
    0 < secondaryBoundaryMargin boundary beta ∧ secondaryBoundaryMargin boundary beta ≤ 1 ∧
      boundary * secondaryBoundaryMargin boundary beta ≤ beta ∧
      0 < secondaryMeshDelta boundary movement beta ∧ secondaryMeshDelta boundary movement beta ≤ 1 ∧
      secondaryMeshDelta boundary movement beta * movement ≤ secondaryBoundaryMargin boundary beta := by
  have hm := replacementAccuracy_spec hboundary hbeta
  have hd := replacementAccuracy_spec hmovement hm.1
  exact ⟨hm.1, hm.2.1, hm.2.2, hd.1, hd.2.1, (mul_comm _ _).trans_le hd.2.2⟩

theorem secondaryMeshAllocation_inverse_bounds {boundary movement beta P : ℝ}
    (hboundary : 0 ≤ boundary) (hmovement : 0 ≤ movement) (hbeta : 0 < beta) (hP : 0 ≤ P)
    (hboundaryP : boundary ≤ Real.exp P) (hmovementP : movement ≤ Real.exp P)
    (hbetaP : beta⁻¹ ≤ Real.exp P) :
    (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * P + 2) ∧
      (secondaryMeshDelta boundary movement beta)⁻¹ ≤ Real.exp (4 * P + 6) := by
  have hm := replacementAccuracy_inverse_le_exp hboundary hbeta hP hboundaryP hbetaP
  refine ⟨hm, ?_⟩
  have hmargin := (replacementAccuracy_spec hboundary hbeta).1
  have hmovement' : movement ≤ Real.exp (2 * P + 2) :=
    hmovementP.trans (Real.exp_le_exp.mpr (by linarith))
  have hd := replacementAccuracy_inverse_le_exp hmovement hmargin (by linarith : 0 ≤ 2 * P + 2)
    hmovement' hm
  exact hd.trans_eq (by congr 1; ring)

end Erdos3

end

section

namespace Erdos3

theorem secondaryMesh_geometry {boundary movement sourceRatio parameterRatio beta : ℝ}
    (hb : 0 ≤ boundary) (hm : 0 ≤ movement) (hs : 0 ≤ sourceRatio) (hp : 0 ≤ parameterRatio)
    (hbeta : 0 < beta) :
    let M := secondaryMovementBudget movement sourceRatio parameterRatio
    let margin := secondaryBoundaryMargin boundary beta
    let delta := secondaryMeshDelta boundary M beta
    0 < margin ∧ margin ≤ 1 ∧ boundary * margin ≤ beta ∧
      0 < delta ∧ delta ≤ 1 ∧ delta * movement ≤ margin ∧
      delta * sourceRatio ≤ 1 ∧ delta * parameterRatio ≤ 1 := by
  intro M margin delta
  have hM : 0 ≤ M := by dsimp only [M, secondaryMovementBudget]; positivity
  have h := secondaryMeshAllocation_spec hb hM hbeta
  change 0 < margin ∧ margin ≤ 1 ∧ boundary * margin ≤ beta ∧
    0 < delta ∧ delta ≤ 1 ∧ delta * M ≤ margin at h
  have hmM : movement ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  have hsM : sourceRatio ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  have hpM : parameterRatio ≤ M := by dsimp only [M, secondaryMovementBudget]; linarith
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    (mul_le_mul_of_nonneg_left hmM h.2.2.2.1.le).trans h.2.2.2.2.2,
    ((mul_le_mul_of_nonneg_left hsM h.2.2.2.1.le).trans h.2.2.2.2.2).trans h.2.1,
    ((mul_le_mul_of_nonneg_left hpM h.2.2.2.1.le).trans h.2.2.2.2.2).trans h.2.1⟩

theorem secondaryMovementBudget_le_exp {movement sourceRatio parameterRatio P : ℝ}
    (hm : movement ≤ Real.exp P) (hs : sourceRatio ≤ Real.exp P)
    (hp : parameterRatio ≤ Real.exp P) :
    secondaryMovementBudget movement sourceRatio parameterRatio ≤ Real.exp (P + 3) := by
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  rw [Real.exp_add]
  have h := mul_le_mul_of_nonneg_left hthree (Real.exp_nonneg P)
  unfold secondaryMovementBudget
  linarith

theorem normalizedMesh_upper_of_ratio {delta scale ratio : ℝ} (N : ℕ)
    (hdelta : 0 ≤ delta) (hbudget : delta * ratio ≤ 1)
    (hscale : scale ≤ ratio * (N : ℝ)) : delta * scale ≤ 2 * (N : ℝ) := by
  have h := mul_le_mul_of_nonneg_left hscale hdelta
  have h' := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N)
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SecondaryMeshLogBudget
namespace OAI

section

namespace Erdos3

theorem secondaryMesh_geometry_inverse {boundary movement sourceRatio parameterRatio beta U : ℝ}
    (hb : 0 ≤ boundary) (hm : 0 ≤ movement) (hs : 0 ≤ sourceRatio) (hp : 0 ≤ parameterRatio)
    (hbeta : 0 < beta) (hU : 0 ≤ U)
    (hbU : boundary ≤ Real.exp U) (hmU : movement ≤ Real.exp U)
    (hsU : sourceRatio ≤ Real.exp U) (hpU : parameterRatio ≤ Real.exp U)
    (hbetaU : beta⁻¹ ≤ Real.exp U) :
    (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * U + 8) ∧
    (secondaryMeshDelta boundary (secondaryMovementBudget movement sourceRatio parameterRatio) beta)⁻¹ ≤
      Real.exp (4 * U + 18) := by
  have he : Real.exp U ≤ Real.exp (U + 3) := Real.exp_le_exp.mpr (by linarith)
  have hM : 0 ≤ secondaryMovementBudget movement sourceRatio parameterRatio := by
    unfold secondaryMovementBudget; positivity
  have h := secondaryMeshAllocation_inverse_bounds hb hM hbeta (by linarith : 0 ≤ U + 3)
    (hbU.trans he) (secondaryMovementBudget_le_exp hmU hsU hpU) (hbetaU.trans he)
  simpa only [show 2 * (U + 3) + 2 = 2 * U + 8 by ring,
    show 4 * (U + 3) + 6 = 4 * U + 18 by ring] using h

theorem secondaryMesh_rounding_of_scale {boundary beta U lengthLog H : ℝ}
    (hmargin : 0 < secondaryBoundaryMargin boundary beta)
    (hinv : (secondaryBoundaryMargin boundary beta)⁻¹ ≤ Real.exp (2 * U + 8))
    (hU : 0 ≤ U) (hlen : 0 ≤ lengthLog)
    (hH : 4 * Real.exp (4 * U + 18 + lengthLog) ≤ H) :
    1 ≤ secondaryBoundaryMargin boundary beta * H := by
  have hexp : Real.exp (2 * U + 8) ≤ Real.exp (4 * U + 18 + lengthLog) :=
    Real.exp_le_exp.mpr (by linarith)
  have hle : (secondaryBoundaryMargin boundary beta)⁻¹ ≤ H := by
    have hpos := Real.exp_pos (4 * U + 18 + lengthLog)
    linarith [hinv.trans hexp]
  have h := mul_le_mul_of_nonneg_left hle hmargin.le
  simpa only [mul_inv_cancel₀ hmargin.ne'] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem integerBoxMesh_distance (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1)
    (z w : ∀ i, Finset.Ico (lo i) (hi i))
    (hsame : integerBoxMesh lo hi P w = integerBoxMesh lo hi P z) (i : I) :
    |(z i : ℤ) - (w i : ℤ)| ≤ ((P i).length (integerBoxMesh lo hi P z i) : ℤ) := by
  have hz := (physicalBoxCell_eq_iff lo (fun i => (hi i - lo i).toNat) P hstep
    (integerBoxMeshPoint lo hi z) (integerBoxMesh lo hi P z)).mp rfl i
  have hw := (physicalBoxCell_eq_iff lo (fun i => (hi i - lo i).toNat) P hstep
    (integerBoxMeshPoint lo hi w) (integerBoxMesh lo hi P z)).mp hsame i
  change intervalCellLower (lo i) (P i) (integerBoxMesh lo hi P z i) ≤ (z i : ℤ) ∧
    (z i : ℤ) < intervalCellUpper (lo i) (P i) (integerBoxMesh lo hi P z i) at hz
  change intervalCellLower (lo i) (P i) (integerBoxMesh lo hi P z i) ≤ (w i : ℤ) ∧
    (w i : ℤ) < intervalCellUpper (lo i) (P i) (integerBoxMesh lo hi P z i) at hw
  dsimp only [intervalCellUpper, intervalCellLower] at hz hw
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem normalized_integerBoxMesh_distance (lo hi : I → ℤ) (H : I → ℝ) (delta : ℝ)
    (hlarge : ∀ i, 4 ≤ delta * H i)
    (hwhole : ∀ i, delta * H i ≤ 2 * ((hi i - lo i).toNat : ℝ))
    (z w : ∀ i, Finset.Ico (lo i) (hi i))
    (hsame : integerBoxMesh lo hi (normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole) w =
      integerBoxMesh lo hi (normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole) z)
    (i : I) : |((z i : ℤ) : ℝ) - ((w i : ℤ) : ℝ)| ≤ delta * H i := by
  let P := normalizedBoxPartitions (fun i => (hi i - lo i).toNat) H delta hlarge hwhole
  have h := integerBoxMesh_distance lo hi P (normalizedBoxPartitions_step _ _ _ _ _) z w hsame i
  have hreal : |((z i : ℤ) : ℝ) - ((w i : ℤ) : ℝ)| ≤
      ((P i).length (integerBoxMesh lo hi P z i) : ℝ) := by exact_mod_cast h
  exact hreal.trans (normalizedBoxPartitions_lengths _ _ _ _ _ i (integerBoxMesh lo hi P z i)).2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

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

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affine_parameter_mesh_distance {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi anchor : J → ℤ) (D : ℕ) (hD : 0 < D) (L delta : ℝ)
    (hlarge : ∀ _j : J, 4 ≤ delta * (L / D))
    (hwhole : ∀ j, delta * (L / D) ≤ 2 * ((hi j - lo j).toNat : ℝ))
    (t u : ∀ j, Finset.Ico (lo j) (hi j))
    (hsame : integerBoxMesh lo hi (normalizedBoxPartitions (fun j => (hi j - lo j).toNat)
        (fun _ => L / D) delta hlarge hwhole) u =
      integerBoxMesh lo hi (normalizedBoxPartitions (fun j => (hi j - lo j).toNat)
        (fun _ => L / D) delta hlarge hwhole) t) (j : J) :
    |((anchor j + (D : ℤ) * (t j : ℤ) : ℤ) : ℝ) -
      ((anchor j + (D : ℤ) * (u j : ℤ) : ℤ) : ℝ)| ≤ delta * L := by
  have hd := normalized_integerBoxMesh_distance lo hi (fun _ => L / D) delta hlarge hwhole t u hsame j
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have he : ((anchor j + (D : ℤ) * (t j : ℤ) : ℤ) : ℝ) -
      ((anchor j + (D : ℤ) * (u j : ℤ) : ℤ) : ℝ) =
      (D : ℝ) * (((t j : ℤ) : ℝ) - ((u j : ℤ) : ℝ)) := by push_cast; ring
  rw [he, abs_mul, abs_of_nonneg hDr.le]
  calc
    _ ≤ (D : ℝ) * (delta * (L / D)) := mul_le_mul_of_nonneg_left hd hDr.le
    _ = _ := by field_simp

theorem concrete_affine_mesh_boundary_probability {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
    (parLo parHi anchor : J → ℤ) (hpar : ∀ j, parLo j < parHi j) (D : ℕ) (hD : 0 < D)
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) {L C B A c rho delta margin : ℝ}
    (hL : 0 < L) (hH : ∀ i, 0 < H i) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : 0 < c) (hrho : 0 < rho) (hmargin : 0 < margin)
    (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsiteRatio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hbaseWidth : ∀ i, c * H i ≤ ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ))
    (hround : ∀ i, 1 ≤ margin * H i)
    (hparamLo : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hparamHi : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hsourceLo : ∀ j i, |(sourceLo (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceHi : ∀ j i, |(sourceHi (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceLarge : ∀ z : Option J × I, 4 ≤ delta * smoothPairCoefficientScale (H z.2) L z.1)
    (hsourceWhole : ∀ z : Option J × I, delta * smoothPairCoefficientScale (H z.2) L z.1 ≤
      2 * ((sourceHi z - sourceLo z).toNat : ℝ))
    (hparamLarge : ∀ _j : J, 4 ≤ delta * (L / D))
    (hparamWhole : ∀ j, delta * (L / D) ≤ 2 * ((parHi j - parLo j).toNat : ℝ))
    (hbudget : delta * (1 + (Fintype.card J : ℝ) * (C + B)) ≤ margin) :
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    let S := fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1
    let sourceMesh := integerBoxMesh sourceLo sourceHi
      (normalizedBoxPartitions (fun z => (sourceHi z - sourceLo z).toNat) S delta hsourceLarge hsourceWhole)
    let parameterMesh := integerBoxMesh parLo parHi
      (normalizedBoxPartitions (fun j => (parHi j - parLo j).toNat) (fun _ => L / D) delta hparamLarge hparamWhole)
    let parameter := fun t : ∀ j, Finset.Ico (parLo j) (parHi j) => fun j => anchor j + (D : ℤ) * (t j : ℤ)
    ((integerBoxUniformWeights parLo parHi hpar).prod (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P (fun tz => (sourceMesh tz.2, parameterMesh tz.1))
        (fun tz => smoothAffineSample (parameter tz.1) (fun z => (tz.2 z : ℤ)))) ≤
      40 * (Fintype.card I : ℝ) * A * margin / (rho * c) := by
  intro P S sourceMesh parameterMesh parameter
  have ht (t : ∀ j, Finset.Ico (parLo j) (parHi j)) (j : J) : |(parameter t j : ℝ)| ≤ C * L := by
    have h := affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (t j : ℤ)
      hL (t j).property (hparamLo j) (hparamHi j)
    exact (div_le_iff₀ hL).mp (by simpa only [abs_div, abs_of_pos hL] using h)
  have hv (z : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (j : J) (i : I) :
      |((z (some j, i) : ℤ) : ℝ)| ≤ B * H i / L := by
    have hz := Finset.mem_Ico.mp (z (some j, i)).property
    have hlo : (sourceLo (some j, i) : ℝ) ≤ (z (some j, i) : ℤ) := by exact_mod_cast hz.1
    have hhi : ((z (some j, i) : ℤ) : ℝ) ≤ sourceHi (some j, i) := by exact_mod_cast hz.2.le
    exact abs_le.mpr ⟨(abs_le.mp (hsourceLo j i)).1.trans hlo, hhi.trans (abs_le.mp (hsourceHi j i)).2⟩
  have hb (z w : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (h : sourceMesh w = sourceMesh z) (i : I) :
      |((z (none, i) : ℤ) : ℝ) - ((w (none, i) : ℤ) : ℝ)| ≤ delta * H i :=
    normalized_integerBoxMesh_distance sourceLo sourceHi S delta hsourceLarge hsourceWhole z w h (none, i)
  have hvd (z w : ∀ j, Finset.Ico (sourceLo j) (sourceHi j)) (h : sourceMesh w = sourceMesh z) (j : J) (i : I) :
      |((z (some j, i) : ℤ) : ℝ) - ((w (some j, i) : ℤ) : ℝ)| ≤ delta * H i / L := by
    have hh := normalized_integerBoxMesh_distance sourceLo sourceHi S delta hsourceLarge hsourceWhole z w h (some j, i)
    simpa only [S, smoothPairCoefficientScale, mul_div_assoc] using hh
  have hp (t u : ∀ j, Finset.Ico (parLo j) (parHi j)) (h : parameterMesh u = parameterMesh t) (j : J) :
      |(parameter t j : ℝ) - parameter u j| ≤ delta * L :=
    affine_parameter_mesh_distance parLo parHi anchor D hD L delta hparamLarge hparamWhole t u h j
  have hr (i : I) : delta * H i + (Fintype.card J : ℝ) *
      ((C * L) * (delta * H i / L) + (B * H i / L) * (delta * L)) ≤ (⌈margin * H i⌉₊ : ℝ) := by
    calc
      _ = (delta * (1 + (Fintype.card J : ℝ) * (C + B))) * H i := by field_simp
      _ ≤ margin * H i := mul_le_mul_of_nonneg_right hbudget (hH i).le
      _ ≤ _ := Nat.le_ceil _
  have hbad := affine_mesh_crossing_probability (integerBoxUniformWeights parLo parHi hpar) parameter
    sourceLo sourceHi hsource sourceMesh parameterMesh lo N P
    (normalizedBoxPartitions_step _ _ _ _ _) (normalizedBoxPartitions_positive _ _ _ _ _)
    (fun i => ⌈margin * H i⌉₊) (fun i => delta * H i) (fun i => delta * H i / L)
    (fun i => B * H i / L) (C * L) (delta * L) (mul_nonneg hC hL.le) (fun i => div_nonneg (mul_nonneg hB (hH i).le) hL.le)
    ht hv hb hvd hp hr
  exact hbad.trans (normalized_physical_boundary_budget_le N H
    (fun i => ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ)) rho hrho hH
    hsiteLarge hsiteWhole hA hc hmargin hsiteRatio hround hbaseWidth)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineSecondaryMesh
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem exists_allocated_affine_secondary_mesh {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
    (parLo parHi anchor : J → ℤ) (hpar : ∀ j, parLo j < parHi j) (D : ℕ) (hD : 0 < D)
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) {L C B A c rho sourceRatio parameterRatio U lengthLog beta : ℝ}
    (hL : 0 < L) (hH : ∀ i, 0 < H i) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hc : 0 < c) (hrho : 0 < rho) (hsRatio : 0 ≤ sourceRatio) (hpRatio : 0 ≤ parameterRatio)
    (hU : 0 ≤ U) (hlength : 0 ≤ lengthLog) (hbeta : 0 < beta)
    (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ))
    (hsiteRatio : ∀ i, (N i : ℝ) ≤ A * H i)
    (hbaseWidth : ∀ i, c * H i ≤ ((sourceHi (none, i) - sourceLo (none, i) : ℤ) : ℝ))
    (hparamLo : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hparamHi : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hsourceLo : ∀ j i, |(sourceLo (some j, i) : ℝ)| ≤ B * H i / L)
    (hsourceHi : ∀ j i, |(sourceHi (some j, i) : ℝ)| ≤ B * H i / L)
    (hboundaryU : 40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp U)
    (hmovementU : 1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp U)
    (hsourceU : sourceRatio ≤ Real.exp U) (hparameterU : parameterRatio ≤ Real.exp U)
    (hbetaU : beta⁻¹ ≤ Real.exp U)
    (hsourceWidth : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ))
    (hparameterWidth : ∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ))
    (hsourceScale : ∀ z : Option J × I, 4 * Real.exp (4 * U + 18 + lengthLog) ≤
      smoothPairCoefficientScale (H z.2) L z.1)
    (hparameterScale : 4 * Real.exp (4 * U + 18 + lengthLog) ≤ L / (D : ℝ)) :
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    ∃ (S : ∀ z, FiniteProgressionPartition (sourceHi z - sourceLo z).toNat)
      (T : ∀ j, FiniteProgressionPartition (parHi j - parLo j).toNat),
    (∀ z cs, (S z).step cs = 1) ∧ (∀ z cs, 0 < (S z).length cs) ∧
    (∀ j ct, (T j).step ct = 1) ∧ (∀ j ct, 0 < (T j).length ct) ∧
    (∀ z cs, Real.exp lengthLog ≤ ((S z).length cs : ℝ)) ∧
    (∀ j ct, Real.exp lengthLog ≤ ((T j).length ct : ℝ)) ∧
    ((integerBoxUniformWeights parLo parHi hpar).prod
      (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh parLo parHi T tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val)
          (fun i => (tz.2 i).val))) ≤ beta := by
  intro P
  let boundary := 40 * (Fintype.card I : ℝ) * A / (rho * c)
  let movement := 1 + (Fintype.card J : ℝ) * (C + B)
  let M := secondaryMovementBudget movement sourceRatio parameterRatio
  let margin := secondaryBoundaryMargin boundary beta
  let delta := secondaryMeshDelta boundary M beta
  have hb : 0 ≤ boundary := by dsimp only [boundary]; positivity
  have hm : 0 ≤ movement := by dsimp only [movement]; positivity
  obtain ⟨hmargin, _, hpay, hdelta, _, hmove, hsw, hpw⟩ :=
    secondaryMesh_geometry hb hm hsRatio hpRatio hbeta
  have hinv := secondaryMesh_geometry_inverse hb hm hsRatio hpRatio hbeta hU
    hboundaryU hmovementU hsourceU hparameterU hbetaU
  change 0 < margin at hmargin
  change 0 < delta at hdelta
  change delta * movement ≤ margin at hmove
  change delta * sourceRatio ≤ 1 at hsw
  change delta * parameterRatio ≤ 1 at hpw
  have hsLarge (z : Option J × I) : 4 ≤ delta * smoothPairCoefficientScale (H z.2) L z.1 :=
    normalizedMesh_scale_large hdelta hinv.2 hlength (hsourceScale z)
  have hsWhole (z : Option J × I) : delta * smoothPairCoefficientScale (H z.2) L z.1 ≤
      2 * ((sourceHi z - sourceLo z).toNat : ℝ) :=
    normalizedMesh_upper_of_ratio _ hdelta.le hsw (hsourceWidth z)
  have htLarge (_j : J) : 4 ≤ delta * (L / (D : ℝ)) :=
    normalizedMesh_scale_large hdelta hinv.2 hlength hparameterScale
  have htWhole (j : J) : delta * (L / (D : ℝ)) ≤ 2 * ((parHi j - parLo j).toNat : ℝ) :=
    normalizedMesh_upper_of_ratio _ hdelta.le hpw (hparameterWidth j)
  let S := normalizedBoxPartitions (fun z => (sourceHi z - sourceLo z).toNat)
    (fun z => smoothPairCoefficientScale (H z.2) L z.1) delta hsLarge hsWhole
  let T := normalizedBoxPartitions (fun j => (parHi j - parLo j).toNat)
    (fun _ => L / (D : ℝ)) delta htLarge htWhole
  refine ⟨S, T, normalizedBoxPartitions_step _ _ _ _ _, normalizedBoxPartitions_positive _ _ _ _ _,
    normalizedBoxPartitions_step _ _ _ _ _, normalizedBoxPartitions_positive _ _ _ _ _, ?_, ?_, ?_⟩
  · exact normalizedBoxPartitions_exp_lengths _ _ delta (4 * U + 18) lengthLog hdelta hinv.2
      hsourceScale hsLarge hsWhole
  · exact normalizedBoxPartitions_exp_lengths _ _ delta (4 * U + 18) lengthLog hdelta hinv.2
      (fun _ => hparameterScale) htLarge htWhole
  · have hround (i : I) : 1 ≤ margin * H i :=
      secondaryMesh_rounding_of_scale hmargin hinv.1 hU hlength (hsourceScale (none,i))
    have hbad := concrete_affine_mesh_boundary_probability sourceLo sourceHi hsource
      parLo parHi anchor hpar D hD lo N H hL hH hC hB hA hc hrho hmargin
      hsiteLarge hsiteWhole hsiteRatio hbaseWidth hround hparamLo hparamHi hsourceLo hsourceHi
      hsLarge hsWhole htLarge htWhole hmove
    apply hbad.trans
    change 40 * (Fintype.card I : ℝ) * A * margin / (rho * c) ≤ beta
    calc
      _ = boundary * margin := by dsimp only [boundary]; ring
      _ ≤ beta := hpay

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.exists_allocated_affine_secondary_mesh.{u_1, u_2} := @OAI.Erdos3.exists_allocated_affine_secondary_mesh.{u_1, u_2}
