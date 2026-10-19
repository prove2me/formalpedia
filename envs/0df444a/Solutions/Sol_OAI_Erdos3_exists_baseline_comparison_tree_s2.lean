-- Prove2me | solution 1 for OAI.Erdos3.exists_baseline_comparison_tree_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:45:29.511048+00:00
-- url     : https://prove2.me/submissions/88637059-a419-4734-985c-55e4a67a672b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B121
import Definitions.Def_OAIE3v2B139
import Definitions.Def_OAIE3v2B162
import Theorems.Thm_OAI_Erdos3_exists_coprime_residue_physical_stability_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeTrace
namespace OAI

section

namespace Erdos3

universe u v

namespace CoordinateDecisionTree

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.weaken {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (extra : ℕ) : Valid Good I x tree (d + extra) := by
  induction h with
  | leaf good => exact .leaf good
  | @split I x i children d fresh branches ih =>
    have hsum : d + 1 + extra = d + extra + 1 := by omega
    rw [hsum]
    exact .split fresh ih

theorem Valid.mono {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d e : ℕ}
    (h : Valid Good I x tree d) (hde : d ≤ e) : Valid Good I x tree e := by
  have he : d + (e - d) = e := Nat.add_sub_of_le hde
  simpa only [he] using h.weaken (e - d)

end CoordinateDecisionTree

end Erdos3

end

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.congr_assignment {Good : Finset ι → (∀ i, Value i) → Prop}
    (hlocal : ∀ I x y, (∀ i ∈ I, x i = y i) → Good I x → Good I y)
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (y : ∀ i, Value i) (hxy : ∀ i ∈ I, x i = y i) :
    Valid Good I y tree d := by
  induction h generalizing y with
  | leaf good => exact .leaf (hlocal _ _ _ hxy good)
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro value
    apply ih value (Function.update y i value)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp only [Function.update_self]
    · have hji : j ≠ i := by intro heq; subst j; exact fresh hj
      simpa only [Function.update_of_ne hji] using hxy j hj

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.map {Good Better : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (hmap : ∀ J y, Good J y → Better J y) : Valid Better I x tree d := by
  induction h with
  | leaf good => exact .leaf (hmap _ _ good)
  | split fresh branches ih => exact .split fresh ih

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeCardBudget
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.with_card_budget {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (B : ℕ) (hB : I.card + d ≤ B) :
    Valid (fun J y => Good J y ∧ J.card ≤ B) I x tree d := by
  induction h with
  | leaf good => exact .leaf ⟨good, by omega⟩
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro value
    apply ih value
    rw [Finset.card_insert_of_notMem fresh]
    omega

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeOutside
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem outsideAssignment_update (K : Finset ι) (base : ∀ i, Value i)
    (x : ∀ i : {i // i ∉ K}, Value i.val) (i : {i // i ∉ K}) (v : Value i.val) :
    outsideAssignment K base (Function.update x i v) =
      Function.update (outsideAssignment K base x) i.val v := by
  funext j
  by_cases h : j = i.val
  · subst j
    simp only [outsideAssignment, i.property, dite_false, Function.update_self]
  · by_cases hj : j ∈ K
    · simp only [outsideAssignment, hj, dite_true, Function.update_of_ne h]
    · have hji : (⟨j, hj⟩ : {i // i ∉ K}) ≠ i := fun heq => h (congrArg Subtype.val heq)
      simp only [outsideAssignment, hj, dite_false, Function.update_of_ne h, Function.update_of_ne hji]

theorem Valid.liftOutside (K : Finset ι) (base : ∀ i, Value i)
    {Good : Finset {i // i ∉ K} → (∀ i : {i // i ∉ K}, Value i.val) → Prop}
    {Better : Finset ι → (∀ i, Value i) → Prop}
    (transfer : ∀ J y, Good J y → Better (K ∪ J.image Subtype.val) (outsideAssignment K base y))
    {I : Finset {i // i ∉ K}} {x : ∀ i : {i // i ∉ K}, Value i.val}
    {tree : CoordinateDecisionTree {i // i ∉ K} (fun i => Value i.val)} {d : ℕ}
    (h : Valid Good I x tree d) :
    Valid Better (K ∪ I.image Subtype.val) (outsideAssignment K base x) (tree.liftOutside K) d := by
  classical
  induction h with
  | leaf good => exact .leaf (transfer _ _ good)
  | @split I x i children d fresh branches ih =>
    have hfresh : i.val ∉ K ∪ I.image Subtype.val := by
      simp only [Finset.mem_union, Finset.mem_image]
      rintro (hK | ⟨j, hj, heq⟩)
      · exact i.property hK
      · exact fresh ((Subtype.ext heq : j = i) ▸ hj)
    apply Valid.split hfresh
    intro v
    have hsets : K ∪ (insert i I).image Subtype.val = insert i.val (K ∪ I.image Subtype.val) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert]
      aesop
    simpa only [hsets, outsideAssignment_update] using ih v

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

theorem residueIndexLength_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact scalarResidue_card_absolute_error a b r v hab hr

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_half_width (a v : ℤ) (N r : ℕ) (hr : 0 < r)
    (hwidth : 2 * (r : ℝ) ≤ (N : ℝ)) :
    0 < residueIndexLength a (a + N) r v ∧
    (N : ℝ) / 2 ≤ (r : ℝ) * (residueIndexLength a (a + N) r v : ℝ) := by
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlength := residueIndexLength_ge_of_width a (a + N) r v hrz 1 (by norm_num)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using (show (r : ℝ) * (1 + 1) ≤ (N : ℝ) by linarith))
  have herror := residueIndexLength_absolute_error a (a + N) r v (by omega) hrz
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hlo := (abs_le.mp herror).1
  have hmul := mul_le_mul_of_nonneg_left hlo hrr.le
  have hdiv : (r : ℝ) * ((N : ℝ) / r) = (N : ℝ) := by field_simp
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (residueIndexLength a (a + N) r v : ℝ) by linarith)
  · nlinarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_le_width (lo a : ℤ) (N M : ℕ) (hM : 0 < M) :
    residueIndexLength lo (lo + N) M a ≤ N := by
  rw [residueIndexLength_eq_card lo (lo + N) M a (Nat.cast_pos.mpr hM)]
  have h := Finset.card_filter_le (Finset.Ico lo (lo + N)) (fun z => z ≡ a [ZMOD (M : ℤ)])
  simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

theorem residue_slice_counting_cost (lo a : ℤ) (H N M : ℕ) (p : ℝ)
    (hM : 0 < M) (hNH : N ≤ H) (hH : Real.exp (p + 2) ≤ (H : ℝ))
    (hcount : Real.exp (-p) * (H : ℝ) ≤ (residueIndexLength lo (lo + N) M a : ℝ)) :
    (M : ℝ) ≤ Real.exp (p + 2) ∧ Real.exp (-p) * (H : ℝ) ≤ (N : ℝ) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hHreal : (0 : ℝ) < H := (Real.exp_pos (p + 2)).trans_le hH
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hinv : Real.exp (-p) * Real.exp p = 1 := by rw [← Real.exp_add]; simp
  have hsmall : 2 ≤ Real.exp (-p) * (H : ℝ) := by
    calc
      2 ≤ Real.exp 2 := htwo
      _ = Real.exp (-p) * Real.exp (p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-p) * (H : ℝ) := mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
  have herror := (abs_le.mp (residueIndexLength_absolute_error lo (lo + N) M a
    (by omega) (Nat.cast_pos.mpr hM))).2
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hNHreal : (N : ℝ) ≤ H := by exact_mod_cast hNH
  have hquotient : Real.exp (-p) * (H : ℝ) / 2 ≤ (H : ℝ) / M := by
    have hquot := div_le_div_of_nonneg_right hNHreal hMreal.le
    linarith
  have hmul : Real.exp (-p) * (H : ℝ) / 2 * (M : ℝ) ≤ H :=
    (le_div_iff₀ hMreal).mp hquotient
  have hfactor : Real.exp (-p) * (M : ℝ) ≤ 2 := by
    apply le_of_mul_le_mul_right (a := (H : ℝ)) _ hHreal
    nlinarith [hmul]
  have hbound : (M : ℝ) ≤ 2 * Real.exp p := by
    have h := mul_le_mul_of_nonneg_right hfactor (Real.exp_pos p).le
    calc
      (M : ℝ) = (Real.exp (-p) * (M : ℝ)) * Real.exp p := by nlinarith [hinv]
      _ ≤ 2 * Real.exp p := h
  refine ⟨?_, ?_⟩
  · calc
      (M : ℝ) ≤ 2 * Real.exp p := hbound
      _ ≤ Real.exp 2 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_pos p).le
      _ = Real.exp (p + 2) := by rw [← Real.exp_add, add_comm]
  · exact hcount.trans (by exact_mod_cast residueIndexLength_le_width lo a N M hM)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSliceCost
namespace OAI

section

namespace Erdos3

theorem PhysicalSubbox.length_le {σ : Type*} {parent lo : σ → ℤ} {H N : σ → ℕ}
    (h : PhysicalSubbox parent H lo N) (j : σ) : N j ≤ H j := by
  have hj := h j
  omega

theorem ResidueSliceLogCostLE.mono {σ : Type*} {H N : σ → ℕ} {lo a : σ → ℤ}
    {M : ℕ} {P Q : ℝ} (h : ResidueSliceLogCostLE H lo N M a P) (hPQ : P ≤ Q) :
    ResidueSliceLogCostLE H lo N M a Q := by
  intro j
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
    (Nat.cast_nonneg (H j))).trans (h j)

theorem residueSliceLogCostLE_of_bounds {σ : Type*}
    (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ) (A B : ℝ)
    (hM : 0 < M) (hmodulus : (M : ℝ) ≤ Real.exp B)
    (hwidth : ∀ j, Real.exp (-A) * (H j : ℝ) ≤ (N j : ℝ))
    (hlarge : ∀ j, Real.exp (B + 2) ≤ (N j : ℝ)) :
    ResidueSliceLogCostLE H lo N M a (A + B + 2) := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have htwomodulus : 2 * (M : ℝ) ≤ Real.exp (B + 2) := by
    calc
      2 * (M : ℝ) ≤ 2 * Real.exp B := mul_le_mul_of_nonneg_left hmodulus (by norm_num)
      _ ≤ Real.exp 2 * Real.exp B := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (B + 2) := by rw [← Real.exp_add, add_comm]
  have hpaid : 2 * (M : ℝ) * Real.exp (-(A + B + 2)) ≤ Real.exp (-A) := by
    calc
      _ ≤ Real.exp (B + 2) * Real.exp (-(A + B + 2)) :=
        mul_le_mul_of_nonneg_right htwomodulus (Real.exp_pos _).le
      _ = Real.exp (-A) := by rw [← Real.exp_add]; congr 1; ring
  intro j
  have hhalf := (residueIndexLength_half_width (lo j) (a j) (N j) M hM
    (htwomodulus.trans (hlarge j))).2
  have hpaidH := mul_le_mul_of_nonneg_right hpaid (Nat.cast_nonneg (H j))
  apply le_of_mul_le_mul_left (a := 2 * (M : ℝ)) _ (by positivity)
  nlinarith [hwidth j]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem intervalClip_unitInterval (T : D.Niltest w) : T.intervalClip.UnitIntervalValued := by
  intro z
  exact ⟨rfl, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem intervalClip_complexityLE (T : D.Niltest w) (p : ℝ) :
    T.intervalClip.ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem intervalClip_eval (T : D.Niltest w) (x : σ → ℤ)
    (hx : (T.eval x).im = 0 ∧ 0 ≤ (T.eval x).re ∧ (T.eval x).re ≤ 1) :
    T.intervalClip.eval x = T.eval x := by
  change ((max 0 (min 1 (T.eval x).re) : ℝ) : ℂ) = T.eval x
  apply Complex.ext
  · simp only [Complex.ofReal_re, min_eq_right hx.2.2, max_eq_right hx.2.1]
  · exact hx.1.symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem periodPrimeCoordinates_card_pow_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) : 2 ^ (periodPrimeCoordinates prime M).card ≤ M := by
  classical
  let A := periodPrimeCoordinates prime M
  have hsub : A.image prime ⊆ M.primeFactors := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime i, (mem_periodPrimeCoordinates prime M i).mp hi, hM.ne'⟩
  have hcard : A.card ≤ M.primeFactors.card := by
    rw [← Finset.card_image_of_injective A hinj]
    exact Finset.card_le_card hsub
  calc
    2 ^ A.card ≤ 2 ^ M.primeFactors.card := Nat.pow_le_pow_right (by norm_num) hcard
    _ = ∏ _p ∈ M.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ M.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le
    _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)

theorem periodPrimeCoordinates_card_log_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) :
    (periodPrimeCoordinates prime M).card * Real.log 2 ≤ Real.log M := by
  have hpow : (2 : ℝ) ^ (periodPrimeCoordinates prime M).card ≤ M := by
    exact_mod_cast periodPrimeCoordinates_card_pow_le prime hprime hinj hM
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow

theorem periodPrimeCoordinates_card_le {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    {M : ℕ} (hM : 0 < M) {B : ℝ} (hMB : (M : ℝ) ≤ Real.exp B) :
    ((periodPrimeCoordinates prime M).card : ℝ) ≤ 2 * B := by
  have h := (periodPrimeCoordinates_card_log_le prime hprime hinj hM).trans
    ((Real.log_le_iff_le_exp (by exact_mod_cast hM)).mpr hMB)
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    linarith
  have hc : (0 : ℝ) ≤ (periodPrimeCoordinates prime M).card := Nat.cast_nonneg _
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem selectedPrimePowers_pairwise_coprime {ι : Type*}
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime) :
    Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  intro heq
  exact hij (hinj heq)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem initialResiduePrimeMask_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (hM : 0 < M) (p : ℝ) (hp : 0 ≤ p) (hMp : (M : ℝ) ≤ Real.exp p)
    (hqp : ∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p)
    (mandatory : Finset ι) (hmandatory : (mandatory.card : ℝ) ≤ p) :
    let K := mandatory ∪ periodPrimeCoordinates prime M
    (K.card : ℝ) ≤ 3 * p ∧
      ((M.lcm (∏ i ∈ K, prime i ^ power i) : ℕ) : ℝ) ≤ Real.exp (p + 3 * p ^ 2) := by
  dsimp only
  let K := mandatory ∪ periodPrimeCoordinates prime M
  have hperiod := periodPrimeCoordinates_card_le prime hprime hinj hM hMp
  have hcardNat := Finset.card_union_le mandatory (periodPrimeCoordinates prime M)
  have hcard : (K.card : ℝ) ≤ 3 * p := by
    have hcardReal : (K.card : ℝ) ≤ mandatory.card + (periodPrimeCoordinates prime M).card := by
      exact_mod_cast hcardNat
    linarith
  refine ⟨hcard, ?_⟩
  have hprod : ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) ≤ Real.exp (3 * p ^ 2) := by
    rw [Nat.cast_prod]
    calc
      (∏ i ∈ K, ((prime i ^ power i : ℕ) : ℝ)) ≤ ∏ _i ∈ K, Real.exp p :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hqp i)
      _ = Real.exp ((K.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
      _ ≤ Real.exp (3 * p ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hcard hp]
  have hprodpos : 0 < ∏ i ∈ K, prime i ^ power i :=
    Finset.prod_pos (fun i _ => pow_pos (hprime i).pos _)
  have hlcm : ((M.lcm (∏ i ∈ K, prime i ^ power i) : ℕ) : ℝ) ≤
      (M : ℝ) * ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hM hprodpos) (Nat.lcm_dvd_mul M _)
  calc
    _ ≤ (M : ℝ) * ((∏ i ∈ K, prime i ^ power i : ℕ) : ℝ) := hlcm
    _ ≤ Real.exp p * Real.exp (3 * p ^ 2) := mul_le_mul hMp hprod (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + 3 * p ^ 2) := (Real.exp_add _ _).symm

theorem initialResidueCombined_coprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (M : ℕ) (K : Finset ι) (hcovered : periodPrimeCoordinates prime M ⊆ K)
    (j : ι) (hj : j ∉ K) :
    (M.lcm (∏ i ∈ K, prime i ^ power i)).Coprime (prime j ^ power j) := by
  have hM : M.Coprime (prime j ^ power j) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply (hprime j).coprime_iff_not_dvd.mpr
    intro hd
    exact hj (hcovered ((mem_periodPrimeCoordinates prime M j).mpr hd))
  have hK : (∏ i ∈ K, prime i ^ power i).Coprime (prime j ^ power j) := by
    apply Nat.coprime_prod_left_iff.mpr
    intro i hi
    apply selectedPrimePowers_pairwise_coprime prime power hprime hinj
    intro heq
    exact hj (heq ▸ hi)
  exact Nat.Coprime.of_dvd_left (Nat.lcm_dvd_mul M _) (Nat.coprime_mul_iff_left.mpr ⟨hM, hK⟩)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateTreeBatch
namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem exists_query_batch
    (Good : Finset ι → (∀ i, Value i) → Prop) (batch : Finset ι) (d : ℕ) :
    ∀ (I : Finset ι) (x : ∀ i, Value i), Disjoint I batch →
    (∀ y : ∀ i, Value i, (∀ i ∈ I, y i = x i) →
      ∃ tree : CoordinateDecisionTree ι Value, Valid Good (I ∪ batch) y tree d) →
    ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (batch.card + d) := by
  classical
  induction batch using Finset.induction_on with
  | empty =>
    intro I x hdisjoint continuation
    simpa only [Finset.union_empty, Finset.card_empty, Nat.zero_add] using
      continuation x (fun _ _ => rfl)
  | @insert i batch fresh ih =>
    intro I x hdisjoint continuation
    have hi : i ∉ I := by
      intro hi
      exact Finset.disjoint_left.mp hdisjoint hi (Finset.mem_insert_self _ _)
    have hIB : Disjoint (insert i I) batch := by
      apply Finset.disjoint_left.mpr
      intro j hj hbatch
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact fresh hbatch
      · exact Finset.disjoint_left.mp hdisjoint hj (Finset.mem_insert_of_mem hbatch)
    have hchildren : ∀ value : Value i, ∃ tree : CoordinateDecisionTree ι Value,
        Valid Good (insert i I) (Function.update x i value) tree (batch.card + d) := by
      intro value
      apply ih (insert i I) (Function.update x i value) hIB
      intro y hy
      have hbase : ∀ j ∈ I, y j = x j := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        have h := hy j (Finset.mem_insert_of_mem hj)
        simpa only [Function.update_of_ne hji] using h
      have hunion : insert i I ∪ batch = I ∪ insert i batch := by ext j; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      simpa only [hunion] using continuation y hbase
    choose children hchildren using hchildren
    have hcard : (insert i batch).card + d = (batch.card + d) + 1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    rw [hcard]
    exact ⟨.split i children, .split hi hchildren⟩

end Erdos3.CoordinateDecisionTree

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CoprimeResiduePhysicalStability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, x i = y i) :
    residuePrimeCoordinateMean f lo N M a q I x = residuePrimeCoordinateMean f lo N M a q I y := by
  classical
  let e : ResiduePrimeCoordinateCell lo N M a q I x ≃ ResiduePrimeCoordinateCell lo N M a q I y :=
    Equiv.subtypeEquivRight (fun z => ⟨fun hz i hi => (hz i hi).trans (hxy i hi),
      fun hz i hi => (hz i hi).trans (hxy i hi).symm⟩)
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem ResiduePrimeCoordinateStable.congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {M : ℕ} {a : σ → ℤ} {q : ι → ℕ}
    {r : ℕ} {δ : ℝ} {I : Finset ι} {x y : ∀ i, σ → ZMod (q i)}
    (h : ResiduePrimeCoordinateStable f lo N M a q r δ I x) (hxy : ∀ i ∈ I, x i = y i) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I y := by
  intro J hIJ hJ z hyz hnonempty
  rw [← residuePrimeCoordinateMean_congr_assignment f lo N M a q I x y hxy]
  exact h J hIJ hJ z (fun i hi => (hyz i hi).trans (hxy i hi).symm) hnonempty

theorem residuePrimeCoordinateStable_of_empty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hempty : ¬ Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  obtain ⟨z⟩ := hnonempty
  exact False.elim (hempty ⟨⟨z.val, fun i hi =>
    (z.property i (Finset.mem_union_left J hi)).trans (hxy i hi)⟩⟩)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I x = f (fun j => isEmptyElim j) := by
  classical
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x) :=
    ⟨⟨(fun j => isEmptyElim j), fun _ _ => Subsingleton.elim _ _⟩⟩
  unfold residuePrimeCoordinateMean
  calc
    (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)) =
        𝔼 _z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => isEmptyElim j) := by
      apply Finset.expect_congr rfl
      intro z _
      exact congrArg f (Subsingleton.elim _ _)
    _ = _ := Fintype.expect_const _

theorem residuePrimeCoordinateStable_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I x := by
  intro J _ _ y _ _
  rw [residuePrimeCoordinateMean_of_isEmpty, residuePrimeCoordinateMean_of_isEmpty, sub_self, norm_zero]
  exact hδ

theorem exists_residue_stable_tree_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (mandatory : Finset ι) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)),
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable f lo N M a q r δ I x)
        ∅ (fun _ _ => 0) tree mandatory.card := by
  have h := CoordinateDecisionTree.exists_query_batch
    (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable f lo N M a q r δ I x)
    mandatory 0 ∅ (fun _ _ => 0) (by simp) (by
      intro y _
      refine ⟨.leaf, .leaf ⟨?_, residuePrimeCoordinateStable_of_isEmpty f lo N M a q r δ hδ _ y⟩⟩
      simp only [Finset.empty_union, Finset.Subset.refl])
  simpa only [Nat.add_zero] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_lcm {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) (u : ResiduePrimeCoordinateCell lo N M a q I x) :
    residuePrimeCoordinateMean f lo N M a q I x =
      physicalResidueMean f lo N (M.lcm (∏ i ∈ I, q i)) (fun j => (u.val j).val) := by
  classical
  exact Fintype.expect_equiv (residuePrimeCoordinateCell_lcmEquiv lo N M a q hcop I x u)
    _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateProduct_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (I : Finset ι) (p : ℝ) (hq : ∀ i, (q i : ℝ) ≤ Real.exp p) :
    ((∏ i ∈ I, q i : ℕ) : ℝ) ≤ Real.exp (p * I.card) := by
  rw [Nat.cast_prod]
  calc
    (∏ i ∈ I, (q i : ℝ)) ≤ ∏ _i ∈ I, Real.exp p :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hq i)
    _ = Real.exp ((I.card : ℝ) * p) := by rw [Finset.prod_const, Real.exp_nat_mul]
    _ = Real.exp (p * I.card) := by rw [mul_comm]

theorem residuePrimeModulus_le_exp {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (I : Finset ι) (M : ℕ) (hM : 0 < M)
    (A B D : ℝ) (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp A)
    (hq : ∀ i, (q i : ℝ) ≤ Real.exp B) (hcard : (I.card : ℝ) ≤ D) :
    ((M.lcm (∏ i ∈ I, q i) : ℕ) : ℝ) ≤ Real.exp (A + B * D) := by
  have hp := primeCoordinateProduct_le_exp q I B hq
  have hp' := hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcard hB))
  have hprodpos : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => hqpos i)
  have hlcm : ((M.lcm (∏ i ∈ I, q i) : ℕ) : ℝ) ≤ (M : ℝ) * ((∏ i ∈ I, q i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hM hprodpos) (Nat.lcm_dvd_mul M _)
  calc
    _ ≤ (M : ℝ) * ((∏ i ∈ I, q i : ℕ) : ℝ) := hlcm
    _ ≤ Real.exp A * Real.exp (B * D) := mul_le_mul hmodulus hp' (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (A + B * D) := (Real.exp_add _ _).symm

theorem residuePrimeCell_log_cost {ι σ : Type*} [DecidableEq ι]
    (H N : σ → ℕ) (lo u : σ → ℤ) (M : ℕ) (hM : 0 < M)
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (I : Finset ι) (A B C D : ℝ)
    (hB : 0 ≤ B) (hmodulus : (M : ℝ) ≤ Real.exp A) (hq : ∀ i, (q i : ℝ) ≤ Real.exp B)
    (hcard : (I.card : ℝ) ≤ D) (hwidth : ∀ j, Real.exp (-C) * (H j : ℝ) ≤ (N j : ℝ))
    (hlarge : ∀ j, Real.exp (C + (A + B * D) + 2) ≤ (H j : ℝ)) :
    ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I, q i)) u (C + (A + B * D) + 2) := by
  have hpositive : 0 < M.lcm (∏ i ∈ I, q i) := by
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (Finset.prod_pos (fun i _ => hqpos i)).ne')
  apply residueSliceLogCostLE_of_bounds H N lo u _ C (A + B * D) hpositive
    (residuePrimeModulus_le_exp q hqpos I M hM A B D hB hmodulus hq hcard) hwidth
  intro j
  calc
    Real.exp (A + B * D + 2) = Real.exp (-C) * Real.exp (C + (A + B * D) + 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-C) * (H j : ℝ) := mul_le_mul_of_nonneg_left (hlarge j) (Real.exp_pos _).le
    _ ≤ (N j : ℝ) := hwidth j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (S : Finset {i // i ∉ K}) (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i) :
    residuePrimeCoordinateMean f lo N M a q (K ∪ S.image Subtype.val) x =
      residuePrimeCoordinateMean f lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val)
        (fun i : {i // i ∉ K} => q i.val) S (fun i => x i.val) := by
  classical
  exact Fintype.expect_equiv (residuePrimeCoordinateOutsideEquiv lo N M a q hcop K base u S x hx)
    _ _ (fun _ => rfl)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ResidueSliceUpperComparison.on_prime_cell {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent lo a : σ → ℤ} {H N : σ → ℕ} {P level ε : ℝ}
    (hupper : ResidueSliceUpperComparison h g parent H P level ε)
    (hbox : PhysicalSubbox parent H lo N) (M : ℕ) (hM : 0 < M)
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hcost : ∀ u : σ → ℤ, ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I, q i)) u P)
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)) :
    (residuePrimeCoordinateMean h lo N M a q I x).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε := by
  obtain ⟨u⟩ := hne
  have hpositive : 0 < M.lcm (∏ i ∈ I, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (Finset.prod_pos (fun i _ => hqpos i)).ne')
  have hslice := hupper lo N _ (fun j => (u.val j).val) hpositive hbox (hcost _)
  rw [residuePrimeCoordinateMean_lcm h lo N M a q hcop I x u,
    residuePrimeCoordinateMean_lcm g lo N M a q hcop I x u]
  exact hslice

theorem ResiduePrimeCoordinateStable.refinement_upper_bound {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    {r : ℕ} {δ level ε : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (hstable : ResiduePrimeCoordinateStable g lo N M a q r δ I x) (hlevel : 0 ≤ level)
    (J : Finset ι) (hIJ : Disjoint I J) (hJ : J.card ≤ r)
    (y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, y i = x i)
    (hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q (I ∪ J) y))
    (hupper : (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q (I ∪ J) y).re + ε) :
    (residuePrimeCoordinateMean h lo N M a q (I ∪ J) y).re ≤
      level * (residuePrimeCoordinateMean g lo N M a q I x).re + ε + level * δ := by
  have hs := hstable J hIJ hJ y hxy hne
  have hr := (Complex.abs_re_le_norm (residuePrimeCoordinateMean g lo N M a q I x -
    residuePrimeCoordinateMean g lo N M a q (I ∪ J) y)).trans hs
  rw [Complex.sub_re] at hr
  have hmean : (residuePrimeCoordinateMean g lo N M a q (I ∪ J) y).re ≤
      (residuePrimeCoordinateMean g lo N M a q I x).re + δ := by
    have hh := (abs_le.mp hr).1
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hmean hlevel
  nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ResiduePrimeCoordinateStable.of_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (r : ℕ) (δ : ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i, σ → ZMod (q i)) (hx : ∀ i ∈ K, x i = base i)
    (hstable : ResiduePrimeCoordinateStable f lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) r δ S (fun i => x i.val)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ (K ∪ S.image Subtype.val) x := by
  classical
  intro J hdisjoint hcard y hagree hnonempty
  let J' : Finset {i // i ∉ K} := J.subtype (fun i => i ∉ K)
  have hout : ∀ i ∈ J, i ∉ K := by
    intro i hi hK
    exact Finset.disjoint_left.mp hdisjoint (Finset.mem_union_left _ hK) hi
  have himage : J'.image Subtype.val = J := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_subtype.mp hj
    · intro hi
      exact Finset.mem_image.mpr ⟨⟨i, hout i hi⟩, Finset.mem_subtype.mpr hi, rfl⟩
  have hcard' : J'.card ≤ r := by
    have heq : J'.card = J.card := by
      rw [← himage, Finset.card_image_of_injective J' Subtype.val_injective]
    exact heq ▸ hcard
  have hdisjoint' : Disjoint S J' := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hdisjoint
      (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩)) (Finset.mem_subtype.mp hj)
  have hbasey : ∀ i ∈ K, y i = base i :=
    fun i hi => (hagree i (Finset.mem_union_left _ hi)).trans (hx i hi)
  have hunion : (K ∪ S.image Subtype.val) ∪ J = K ∪ (S ∪ J').image Subtype.val := by
    rw [Finset.image_union, himage, Finset.union_assoc]
  have hnonempty' : Nonempty (ResiduePrimeCoordinateCell lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) (S ∪ J') (fun i => y i.val)) := by
    rw [hunion] at hnonempty
    obtain ⟨z⟩ := hnonempty
    exact ⟨residuePrimeCoordinateOutsideEquiv lo N M a q hcop K base u (S ∪ J') y hbasey z⟩
  rw [residuePrimeCoordinateMean_outside f lo N M a q hcop K base u S x hx, hunion,
    residuePrimeCoordinateMean_outside f lo N M a q hcop K base u (S ∪ J') y hbasey]
  apply hstable J' hdisjoint' hcard' (fun i => y i.val) _ hnonempty'
  intro i hi
  exact hagree i.val (Finset.mem_union_right K (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

theorem ResiduePrimeCoordinateStable.lift_outside {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (r : ℕ) (δ : ℝ) (S : Finset {i // i ∉ K})
    (x : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    (hstable : ResiduePrimeCoordinateStable f lo N (M.lcm (∏ i ∈ K, q i))
      (fun j => (u.val j).val) (fun i : {i // i ∉ K} => q i.val) r δ S x) :
    ResiduePrimeCoordinateStable f lo N M a q r δ (K ∪ S.image Subtype.val)
      (CoordinateDecisionTree.outsideAssignment K base x) := by
  apply ResiduePrimeCoordinateStable.of_outside f lo N M a q hcop K base u r δ S
    (CoordinateDecisionTree.outsideAssignment K base x)
  · intro i hi
    simp only [CoordinateDecisionTree.outsideAssignment, hi, dite_true]
  · have heq : (fun i : {i // i ∉ K} =>
        CoordinateDecisionTree.outsideAssignment K base x i.val) = x := by
      funext i
      simp only [CoordinateDecisionTree.outsideAssignment, i.property, dite_false]
    rw [heq]
    exact hstable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CountedSlicePrimeStability
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_residue_prime_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (N j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  classical
  obtain ⟨E₀, _, hstability⟩ := exists_coprime_residue_physical_stability_s2.{u, v, w} s
  let P : Polynomial ℕ := 3 * Polynomial.X + 1 +
    (Polynomial.X + 3 * Polynomial.X ^ 2 + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hlarge
  let q : ι → ℕ := fun i => prime i ^ power i
  let K := mandatory ∪ periodPrimeCoordinates prime M
  let cap := p + 3 * p ^ 2
  let depth : ℕ := ⌈(cap + 2) ^ E₀⌉₊
  let Good := fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable T.eval lo N M a q r δ I x
  have hp0 : 0 ≤ p := by linarith
  have hcap : p ≤ cap := by dsimp only [cap]; nlinarith [sq_nonneg p]
  have hcap0 : 0 ≤ cap := hp0.trans hcap
  have hpower : 3 * p + 1 + (cap + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, cap, Polynomial.eval₂_pow] using hpoly p hp0
  have hK := initialResiduePrimeMask_bounds prime power hprime hinj M hM p hp0 hmodulus hprimeBound mandatory hmandatory
  have hKcard : (K.card : ℝ) ≤ 3 * p := hK.1
  have hQ : ((M.lcm (∏ i ∈ K, q i) : ℕ) : ℝ) ≤ Real.exp cap := hK.2
  have hQpos : 0 < M.lcm (∏ i ∈ K, q i) := by
    apply Nat.pos_of_ne_zero
    apply Nat.lcm_ne_zero hM.ne'
    exact (Finset.prod_pos (fun i _ => pow_pos (hprime i).pos (power i))).ne'
  have hside : ∀ j, Real.exp ((cap + 2) ^ E₀) ≤ (N j : ℝ) := by
    intro j
    apply le_trans _ (hlarge j)
    apply Real.exp_le_exp.mpr
    linarith
  have hbranches : ∀ base : ∀ i, σ → ZMod (q i), ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)),
      CoordinateDecisionTree.Valid Good K base tree depth := by
    intro base
    by_cases hnonempty : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base)
    · obtain ⟨u⟩ := hnonempty
      obtain ⟨tree, d', hd', htree⟩ := hstability D cap δ (hp.trans hcap) (hσ.trans hcap) hδ
        (hδinv.trans (Real.exp_le_exp.mpr hcap)) T hpositive (hcomplexity.mono hcap)
        (fun i : {i // i ∉ K} => prime i.val) (fun i => power i.val)
        (fun i => hprime i.val) (fun i j hij => Subtype.ext (hinj hij))
        (fun i => (hprimeBound i.val).trans (Real.exp_le_exp.mpr hcap))
        ∅ r (by simpa only [Finset.card_empty, Nat.cast_zero] using hcap0) (hr.trans hcap)
        lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val) hQpos hQ
        (fun i => initialResidueCombined_coprime prime power hprime hinj M K
          Finset.subset_union_right i.val i.property) hside
      have hsub := htree.map (fun _ _ h => h.2)
      have hlift := hsub.liftOutside K base (fun S x hx =>
        (show Good (K ∪ S.image Subtype.val) (CoordinateDecisionTree.outsideAssignment K base x) from
          ⟨Finset.subset_union_left.trans Finset.subset_union_left,
            hx.lift_outside T.eval lo N M a q
              (selectedPrimePowers_pairwise_coprime prime power hprime hinj) K base u r δ S x⟩))
      have hroot : CoordinateDecisionTree.Valid Good K
          (CoordinateDecisionTree.outsideAssignment K base (fun _ _ => 0)) (tree.liftOutside K) d' := by
        simpa only [Finset.image_empty, Finset.union_empty] using hlift
      have hroot' := hroot.congr_assignment (fun I x y hxy hx =>
        (show Good I y from ⟨hx.1, hx.2.congr_assignment hxy⟩)) base (by
          intro i hi
          simp only [CoordinateDecisionTree.outsideAssignment, hi, dite_true])
      have hdepth : d' ≤ depth := by
        exact_mod_cast hd'.trans (Nat.le_ceil ((cap + 2) ^ E₀))
      exact ⟨tree.liftOutside K, hroot'.mono hdepth⟩
    · exact ⟨.leaf, .leaf ⟨Finset.subset_union_left,
        residuePrimeCoordinateStable_of_empty T.eval lo N M a q r δ K base hnonempty⟩⟩
  obtain ⟨tree, htree⟩ := CoordinateDecisionTree.exists_query_batch Good K depth ∅ (fun _ _ => 0)
    (by simp) (fun base _ => by simpa only [Finset.empty_union] using hbranches base)
  refine ⟨tree, K.card + depth, ?_, htree⟩
  have hceil : (depth : ℝ) ≤ (cap + 2) ^ E₀ + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ (cap + 2) ^ E₀ by positivity)).le
  rw [Nat.cast_add]
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_prescribed_slice_prime_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤ (N j : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_residue_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hmodulus hwidth hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : p + (p + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hside : ∀ j, Real.exp ((p + 2) ^ E₀) ≤ (N j : ℝ) := by
    intro j
    have hparent := (Real.exp_le_exp.mpr hpower).trans (hlarge j)
    calc
      Real.exp ((p + 2) ^ E₀) = Real.exp (-p) * Real.exp (p + (p + 2) ^ E₀) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * (H j : ℝ) := mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le
      _ ≤ (N j : ℝ) := hwidth j
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hside
  exact ⟨tree, depth, hdepth.trans (by linarith), htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_counted_slice_prime_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  classical
  obtain ⟨E₀, _, hstability⟩ := exists_prescribed_slice_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := (Polynomial.X + 4) ^ E₀ + Polynomial.X + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hcount hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : (p + 4) ^ E₀ + p + 2 ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hnonneg : 0 ≤ (p + 4) ^ E₀ := by positivity
  rcases isEmpty_or_nonempty σ with hempty | hnonempty
  · let := hempty
    obtain ⟨tree, htree⟩ := exists_residue_stable_tree_of_isEmpty T.eval lo N M a
      (fun i => prime i ^ power i) r δ hδ.le mandatory
    exact ⟨tree, mandatory.card, hmandatory.trans (by linarith), htree⟩
  · let := hnonempty
    have hcost := fun j => residue_slice_counting_cost (lo j) (a j) (H j) (N j) M p hM (hNH j)
      ((Real.exp_le_exp.mpr (show p + 2 ≤ (p + 2) ^ E by linarith)).trans (hlarge j)) (hcount j)
    have hmodulus : (M : ℝ) ≤ Real.exp (p + 2) := (hcost (Classical.choice hnonempty)).1
    have hpinc : p ≤ p + 2 := by linarith
    have hwidth : ∀ j, Real.exp (-(p + 2)) * (H j : ℝ) ≤ (N j : ℝ) := by
      intro j
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (Nat.cast_nonneg (H j))).trans (hcost j).2
    have hsize : ∀ j, Real.exp ((p + 2 + 2) ^ E₀) ≤ (H j : ℝ) := by
      intro j
      apply le_trans _ (hlarge j)
      apply Real.exp_le_exp.mpr
      have heq : p + 2 + 2 = p + 4 := by ring
      rw [heq]
      linarith
    obtain ⟨tree, depth, hdepth, htree⟩ := hstability D (p + 2) δ (hp.trans hpinc)
      (hσ.trans hpinc) hδ (hδinv.trans (Real.exp_le_exp.mpr hpinc))
      T hpositive (hcomplexity.mono hpinc) prime power hprime hinj
      (fun i => (hprimeBound i).trans (Real.exp_le_exp.mpr hpinc))
      mandatory r (hmandatory.trans hpinc) (hr.trans hpinc) H N lo a M hM hmodulus hwidth hsize
    refine ⟨tree, depth, ?_, htree⟩
    have heq : p + 2 + 2 = p + 4 := by ring
    rw [heq] at hdepth
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStableBoxCongruence
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_congr_on_box {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I x = residuePrimeCoordinateMean g lo N M a q I x := by
  classical
  unfold residuePrimeCoordinateMean
  apply Finset.expect_congr rfl
  intro z _
  apply hfg
  apply (mem_translatedIntegerBox lo N _).mpr
  intro j
  exact Finset.mem_Ico.mp (Finset.mem_filter.mp (z.val j).property).1

theorem ResiduePrimeCoordinateStable.congr_on_box {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f g : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {M : ℕ} {a : σ → ℤ} {q : ι → ℕ}
    {r : ℕ} {δ : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (h : ResiduePrimeCoordinateStable f lo N M a q r δ I x)
    (hfg : ∀ z ∈ translatedIntegerBox lo N, f z = g z) :
    ResiduePrimeCoordinateStable g lo N M a q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  rw [← residuePrimeCoordinateMean_congr_on_box f g lo N M a q hfg I x,
    ← residuePrimeCoordinateMean_congr_on_box f g lo N M a q hfg (I ∪ J) y]
  exact h J hIJ hJ y hxy hnonempty

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StablePrimeUpperComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CoordinateDecisionTree.Valid.with_slice_upper_comparison {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {parent lo a : σ → ℤ} {H N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    {r : ℕ} {δ P level ε : ℝ} {mandatory I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    {tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i))} {d : ℕ}
    (htree : CoordinateDecisionTree.Valid
      (fun A z => mandatory ⊆ A ∧ ResiduePrimeCoordinateStable g lo N M a q r δ A z ∧
        ∀ J : Finset ι, J.card ≤ r → ∀ u : σ → ℤ,
          ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ A ∪ J, q i)) u P) I x tree d)
    (hupper : ResidueSliceUpperComparison h g parent H P level ε)
    (hbox : PhysicalSubbox parent H lo N) (hM : 0 < M) (hqpos : ∀ i, 0 < q i)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (hlevel : 0 ≤ level) :
    CoordinateDecisionTree.Valid
      (fun A z => mandatory ⊆ A ∧ ResiduePrimeCoordinateStable g lo N M a q r δ A z ∧
        PrimeRefinementUpperBound h g lo N M a q r level ε δ A z) I x tree d := by
  apply htree.map
  intro A z hz
  refine ⟨hz.1, hz.2.1, ?_⟩
  intro J hAJ hJ y hzy hne
  apply hz.2.1.refinement_upper_bound hlevel J hAJ hJ y hzy hne
  exact hupper.on_prime_cell hbox M hM q hqpos hcop (A ∪ J) y (hz.2.2 J hJ) hne

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BaselineNoIncrementTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_baseline_marginal_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ z ∈ translatedIntegerBox lo N, (T.eval z).im = 0 ∧ 0 ≤ (T.eval z).re ∧ (T.eval z).re ≤ 1) →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_counted_slice_prime_stability.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount hlarge
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T.intervalClip
    T.intervalClip_unitInterval ((T.intervalClip_complexityLE p).mpr hcomplexity)
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hcount hlarge
  refine ⟨tree, depth, hdepth, htree.map ?_⟩
  intro I x hx
  exact ⟨hx.1, hx.2.congr_on_box (fun z hz => T.intervalClip_eval z (hunit z hz))⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_baseline_stable_slice_costs (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ z ∈ translatedIntegerBox lo N, (T.eval z).im = 0 ∧ 0 ≤ (T.eval z).re ∧ (T.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          ∀ J : Finset ι, J.card ≤ r → ∀ u : σ → ℤ,
            ResidueSliceLogCostLE H lo N (M.lcm (∏ i ∈ I ∪ J, prime i ^ power i)) u ((p + 2) ^ E))
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_baseline_marginal_stability.{u, v, w} s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 2 + X * ((X + 2) ^ E₀ + X)) + 2
  let P := (X + 2) ^ E₀ + Q + X + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount hlarge
  let B := (p + 2) ^ E₀
  let C := p + (p + 2 + p * (B + p)) + 2
  have hp0 : 0 ≤ p := by linarith
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hpower : B + C + p + 2 ≤ (p + 2) ^ E := by
    simpa [X, Q, P, B, C, Polynomial.eval₂_pow] using hpoly p hp0
  have hB : B ≤ (p + 2) ^ E := by linarith
  have hC : C ≤ (p + 2) ^ E := by linarith
  have hsmall : p + 2 ≤ (p + 2) ^ E := by linarith
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hunit hcount
    (fun j => (Real.exp_le_exp.mpr hB).trans (hlarge j))
  have hwidth : ∀ j, Real.exp (-p) * (H j : ℝ) ≤ (N j : ℝ) := by
    intro j
    exact (hcount j).trans (by exact_mod_cast residueIndexLength_le_width (lo j) (a j) (N j) M hM)
  have hcardTree := htree.with_card_budget depth (by simp)
  refine ⟨tree, depth, hdepth.trans hB, hcardTree.map ?_⟩
  intro I x hx
  refine ⟨hx.1.1, hx.1.2, ?_⟩
  intro J hJ u j
  have hcard : ((I ∪ J).card : ℝ) ≤ B + p := by
    have hunion : ((I ∪ J).card : ℝ) ≤ (I.card : ℝ) + J.card := by
      exact_mod_cast Finset.card_union_le I J
    have hI : (I.card : ℝ) ≤ depth := by exact_mod_cast hx.2
    have hJR : (J.card : ℝ) ≤ r := by exact_mod_cast hJ
    linarith
  have hinitial := residue_slice_counting_cost (lo j) (a j) (H j) (N j) M p hM (hNH j)
    ((Real.exp_le_exp.mpr hsmall).trans (hlarge j)) (hcount j)
  have hcost := residuePrimeCell_log_cost H N lo u M hM
    (fun i => prime i ^ power i) (fun i => pow_pos (hprime i).pos _) (I ∪ J)
    (p + 2) p p (B + p) hp0 hinitial.1 hprimeBound hcard hwidth
    (fun k => (Real.exp_le_exp.mpr hC).trans (hlarge k))
  exact (hcost.mono hC) j

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_baseline_comparison_tree_s2_oai (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ g : D.Niltest (fun _ : σ => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (parent : σ → ℤ) (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M →
    PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N M a p →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∀ (h : (σ → ℤ) → ℂ) (level ε : ℝ), 0 ≤ level →
    ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level ε →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable g.eval lo N M a (fun i => prime i ^ power i) r δ I x ∧
          PrimeRefinementUpperBound h g.eval lo N M a (fun i => prime i ^ power i) r level ε δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_baseline_stable_slice_costs.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv g hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr parent H N lo a M hM
    hbox hunit hcost hlarge h level ε hlevel hupper
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv g hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM
    hbox.length_le hunit hcost hlarge
  refine ⟨tree, depth, hdepth, ?_⟩
  exact htree.with_slice_upper_comparison hupper hbox hM
    (fun i => pow_pos (hprime i).pos _) (selectedPrimePowers_pairwise_coprime prime power hprime hinj) hlevel

end Erdos3

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.Erdos3.exists_baseline_comparison_tree_s2_oai.{u, v, w} := @OAI.Erdos3.exists_baseline_comparison_tree_s2_oai.{u, v, w}
