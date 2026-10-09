-- Prove2me | solution 1 for OAI.Erdos3.residuePrimeCoordinateCell_nonempty_of_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:22.128661+00:00
-- url     : https://prove2.me/submissions/fd02bf8d-dfc7-44ff-beb5-410577b0f022

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_mul_prod_one_add_le_one {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) :
    (1 - ∑ i ∈ S, e i) * (∏ i ∈ S, (1 + e i)) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have heS : ∀ i ∈ S, 0 ≤ e i := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg heS
    have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [heS i hi])
    have hstep : (1 - (e a + ∑ i ∈ S, e i)) * (1 + e a) ≤ 1 - ∑ i ∈ S, e i := by
      nlinarith [mul_nonneg hea hs, sq_nonneg (e a)]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep hp).trans (ih heS)

theorem prod_one_add_le_one_add_twice_sum {ι : Type*} (S : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ S, 0 ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    (∏ i ∈ S, (1 + e i)) ≤ 1 + 2 * ∑ i ∈ S, e i := by
  have h := one_sub_sum_mul_prod_one_add_le_one S e he
  have hs := Finset.sum_nonneg he
  have hp : 0 ≤ ∏ i ∈ S, (1 + e i) := Finset.prod_nonneg (fun i hi => by linarith [he i hi])
  have hp2 : (∏ i ∈ S, (1 + e i)) ≤ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hp2 hs]

theorem positive_prod_sub_one_le_twice_sum {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, 0 ≤ e i)
    (herror : ∀ i ∈ S, |f i - 1| ≤ e i) (hsmall : (∑ i ∈ S, e i) ≤ 1 / 2) :
    |(∏ i ∈ S, f i) - 1| ≤ 2 * ∑ i ∈ S, e i := by
  have hs := Finset.sum_nonneg he
  have he1 (i) (hi : i ∈ S) : e i ≤ 1 :=
    (Finset.single_le_sum he hi).trans (hsmall.trans (by norm_num))
  have hlo := one_sub_sum_le_positive_prod S f e hf (fun i hi => ⟨he i hi, he1 i hi⟩)
    (fun i hi => by have h := (abs_le.mp (herror i hi)).1; linarith)
  have hhi : (∏ i ∈ S, f i) ≤ 1 + 2 * ∑ i ∈ S, e i := by
    apply (Finset.prod_le_prod hf (fun index hindex => ?_)).trans
      (prod_one_add_le_one_add_twice_sum S e he hsmall)
    have hupper := (abs_le.mp (herror index hindex)).2
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

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

end Erdos3

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

theorem scalarResidue_relative_count_error (a b r v : ℤ) (hab : a < b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1| ≤ (r : ℝ) / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_absolute_error a b r v hab.le hr
  have heq : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r /
      ((b - a : ℤ) : ℝ) - 1 =
      (((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
        ((b - a : ℤ) : ℝ) / r) * ((r : ℝ) / ((b - a : ℤ) : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos hrR hL)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (div_nonneg hrR.le hL.le)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rectangularResidueCount_eq_card {I : Type*} [Fintype I] [DecidableEq I] (a b r v : I → ℤ) :
    rectangularResidueCount a b r v = Fintype.card
      (∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))) := by
  classical
  rw [Fintype.card_pi]
  simp [rectangularResidueCount, integerResidueCount]

theorem rectangularResidueCount_relative_error {I : Type*} [Fintype I]
    (a b r v : I → ℤ) (hab : ∀ i, a i < b i) (hr : ∀ i, 0 < r i)
    (hsmall : (∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) ≤ 1 / 2) :
    |(∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) - integerRectangleVolume a b| ≤
      (2 * ∑ i, (r i : ℝ) / ((b i - a i : ℤ) : ℝ)) * integerRectangleVolume a b := by
  let L : I → ℝ := fun i => ((b i - a i : ℤ) : ℝ)
  let c : I → ℝ := fun i => integerResidueCount (a i) (b i) (r i) (v i)
  let f : I → ℝ := fun i => c i * r i / L i
  let e : I → ℝ := fun i => (r i : ℝ) / L i
  have hL (i) : 0 < L i := by
    dsimp only [L]
    exact_mod_cast sub_pos.mpr (hab i)
  have hrR (i) : (0 : ℝ) < r i := by exact_mod_cast hr i
  have hV : 0 < integerRectangleVolume a b := Finset.prod_pos (fun i _ => hL i)
  have hprod := positive_prod_sub_one_le_twice_sum Finset.univ f e
    (fun i _ => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hrR i).le) (hL i).le)
    (fun i _ => (div_pos (hrR i) (hL i)).le)
    (fun i _ => scalarResidue_relative_count_error (a i) (b i) (r i) (v i) (hab i) (hr i)) hsmall
  have heq : (∏ i, f i) * integerRectangleVolume a b =
      (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
    change (∏ i, f i) * (∏ i, L i) = _
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i, f i * L i) = ∏ i, c i * r i := by
        apply Finset.prod_congr rfl
        intro i _
        exact div_mul_cancel₀ (c i * r i) (hL i).ne'
      _ = (∏ i, (r i : ℝ)) * (rectangularResidueCount a b r v : ℝ) := by
        simp only [Finset.prod_mul_distrib, rectangularResidueCount, Nat.cast_prod, c]
        ring
  calc
    _ = |((∏ i, f i) - 1) * integerRectangleVolume a b| := by
      rw [← heq]
      congr 1
      ring
    _ = |(∏ i, f i) - 1| * integerRectangleVolume a b := by rw [abs_mul, abs_of_pos hV]
    _ ≤ (2 * ∑ i, e i) * integerRectangleVolume a b := mul_le_mul_of_nonneg_right hprod hV.le

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T : ι → ℕ) [∀ i, NeZero (T i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerResidueBox_lengths_pos {I : Type*} (a b r v : I → ℤ)
    (hr : ∀ i, 0 < r i) (hbox : Nonempty (IntegerResidueBox a b r v)) :
    ∀ i, 0 < residueIndexLength (a i) (b i) (r i) (v i) := by
  obtain ⟨x⟩ := hbox
  intro i
  rw [residueIndexLength_eq_card (a i) (b i) (r i) (v i) (hr i)]
  exact Finset.card_pos.mpr ⟨(x i).val, (x i).property⟩

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {X : Type*} (N H : X → ℕ) (lo a : X → ℤ) (M : ℕ)
    (hM : 0 < M) (hbox : PhysicalSubbox (fun _ => 0) N lo H)
    (hne : ∀ i, 0 < residueIndexLength (lo i) (lo i + H i) M (a i))

end ResidueBoxSlice
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductReferenceFiber
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x = ∏ i ∈ S, (μ i).weight (x i) := by
  classical
  have hind : ∀ y : ∀ i, X i, productFiberIndicator S x y =
      ∏ i, (if i ∈ S then if y i = x i then (1 : ℝ) else 0 else 1) := by
    intro y
    unfold productFiberIndicator
    split_ifs with h
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, h i hi, ite_true]
      · simp only [hi, ite_false]
    · push Not at h
      obtain ⟨i, hi, heq⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, heq, ite_true, ite_false]
  simp only [productFiberMass, hind, FiniteProbabilityWeights.pi, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (y : X i) => (μ i).weight y *
    (if i ∈ S then if y = x i then (1 : ℝ) else 0 else 1))]
  have hsum : ∀ i, (∑ y : X i, (μ i).weight y * (if i ∈ S then if y = x i then 1 else 0 else 1)) =
      if i ∈ S then (μ i).weight (x i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [hi]
    · simpa only [hi, ite_false, mul_one] using (μ i).total
  simp only [hsum]
  rw [Finset.prod_ite]
  simp

theorem productFiberMass_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi (fun i => FiniteProbabilityWeights.uniform (X i))).weight S x =
      ∏ i ∈ S, (Fintype.card (X i) : ℝ)⁻¹ := by
  rw [productFiberMass_pi]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_prime_coordinate_integer_anchor {ι σ : Type*} [DecidableEq ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    ∃ u : σ → ℤ, ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨v, hv⟩ := ih
    have hc : (q i).Coprime (∏ k ∈ I, q k) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro k hk
      apply hcop
      intro heq
      exact hi (heq ▸ hk)
    have hu : ∀ j : σ, ∃ u : ℤ,
        u ≡ ((x i j).val : ℤ) [ZMOD (q i : ℤ)] ∧ u ≡ v j [ZMOD ((∏ k ∈ I, q k : ℕ) : ℤ)] := by
      intro j
      exact exists_integer_coprime_residues hc (x i j).val (v j)
    choose u hu using hu
    refine ⟨u, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with hki | hk
    · subst k
      funext j
      have h := (ZMod.intCast_eq_intCast_iff (u j) ((x i j).val : ℤ) (q i)).mpr (hu j).1
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h
    · funext j
      have hd : (q k : ℤ) ∣ ((∏ l ∈ I, q l : ℕ) : ℤ) := by
        exact_mod_cast Finset.dvd_prod_of_mem q hk
      have h := (ZMod.intCast_eq_intCast_iff (u j) (v j) (q k)).mpr ((hu j).2.of_dvd hd)
      exact h.trans (congrFun (hv k hk) j)

theorem primeCoordinateCell_eq_integer_anchor {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    primeCoordinateCell lo N q I x =
      primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) := by
  ext z
  simp only [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi).symm⟩
  · rintro ⟨hz, hx⟩
    exact ⟨hz, fun i hi => (hx i hi).trans (hu i hi)⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_fiber {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    productFiberMass (FiniteProbabilityWeights.pi (primeCoordinateReference (σ := σ) q)).weight I x =
      (((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ)⁻¹ := by
  change productFiberMass (FiniteProbabilityWeights.pi
    (fun i => FiniteProbabilityWeights.uniform (σ → ZMod (q i)))).weight I x = _
  rw [productFiberMass_uniform]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_pow]

theorem primeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateMassRatio lo N q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        (primeCoordinateCell lo N q I x).card / (translatedIntegerBox lo N).card := by
  rw [primeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateCell_card_residue {ι σ : Type*} [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i)) (u : σ → ℤ)
    (hu : ∀ i ∈ I, (fun j => (u j : ZMod (q i))) = x i) :
    (primeCoordinateCell lo N q I x).card =
      rectangularResidueCount lo (fun j => lo j + N j) (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u := by
  rw [primeCoordinateCell_eq_integer_anchor lo N q I x u hu]
  have hc := Fintype.card_congr (primeCoordinateCellEquiv lo N q hcop I u)
  rw [Fintype.card_coe] at hc
  exact hc.trans (rectangularResidueCount_eq_card _ _ _ _).symm

theorem primeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (hN : ∀ j, 0 < N j)
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι)
    (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j) ≤ 1 / 2) :
    |primeCoordinateMassRatio lo N q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) / N j := by
  obtain ⟨u, hu⟩ := exists_prime_coordinate_integer_anchor q hcop I x
  have hM : 0 < ∏ i ∈ I, q i := Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))
  have herr := rectangularResidueCount_relative_error lo (fun j => lo j + N j)
    (fun _ => ((∏ i ∈ I, q i : ℕ) : ℤ)) u
    (fun j => by have hj := hN j; omega) (fun _ => Nat.cast_pos.mpr hM)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using hsmall)
  have hcell := primeCoordinateCell_card_residue lo N q hcop I x u hu
  have hvolume : integerRectangleVolume lo (fun j => lo j + N j) =
      ((translatedIntegerBox lo N).card : ℝ) := by
    simp only [integerRectangleVolume, add_sub_cancel_left, Int.cast_natCast,
      translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
  rw [hvolume, ← hcell] at herr
  simp only [Finset.prod_const, Finset.card_univ, add_sub_cancel_left, Int.cast_natCast] at herr
  have hV : (0 : ℝ) < (translatedIntegerBox lo N).card := by
    simp only [translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod]
    exact Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (hN j))
  rw [primeCoordinateMassRatio_eq_count]
  calc
    _ = |((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ * (primeCoordinateCell lo N q I x).card -
        (translatedIntegerBox lo N).card| / (translatedIntegerBox lo N).card := by
      rw [← abs_of_pos hV, ← abs_div]
      congr 1
      rw [abs_of_pos hV]
      field_simp
    _ ≤ _ := (div_le_iff₀ hV).mpr herr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_eq_count {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I x =
      ((∏ i ∈ I, q i : ℕ) : ℝ) ^ Fintype.card σ *
        Fintype.card (ResiduePrimeCoordinateCell lo N M a q I x) /
        Fintype.card (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a) := by
  rw [residuePrimeCoordinateMassRatio, primeCoordinateReference_fiber, div_inv_eq_mul]
  ring

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMassRatio_affine {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMassRatio lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) =
    primeCoordinateMassRatio (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x := by
  have hc := Fintype.card_congr (residuePrimeCoordinateCellEquiv lo N M a q hM hcop I x)
  have hb := Fintype.card_congr (integerResidueBoxEquiv lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM))
  rw [Fintype.card_coe] at hc hb
  rw [residuePrimeCoordinateMassRatio_eq_count, primeCoordinateMassRatio_eq_count, ← hc, ← hb]

theorem residuePrimeCoordinateMassRatio_close {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) ≤ 1 / 2) :
    |residuePrimeCoordinateMassRatio lo N M a q I x - 1| ≤
      2 * ∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
        residueIndexLength (lo j) (lo j + N j) M (a j) := by
  let inv : ∀ i, σ → ZMod (q i) :=
    fun i => (affineResidueCoordinateEquiv M (q i) a (hcop i)).symm (x i)
  have hx : (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (inv i)) = x := by
    funext i
    exact Equiv.apply_symm_apply _ _
  have hlength := integerResidueBox_lengths_pos lo (fun j => lo j + N j)
    (fun _ => (M : ℤ)) a (fun _ => Nat.cast_pos.mpr hM) hne
  rw [← hx, residuePrimeCoordinateMassRatio_affine lo N M a q hM hcop I inv]
  exact primeCoordinateMassRatio_close _ _ hlength q hpair I inv hsmall

theorem residuePrimeCoordinateCell_nonempty_of_small {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i))
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hsmall : (∑ j, ((∏ i ∈ I, q i : ℕ) : ℝ) /
      residueIndexLength (lo j) (lo j + N j) M (a j)) < 1 / 2) :
    Nonempty (ResiduePrimeCoordinateCell lo N M a q I x) := by
  classical
  by_contra hc
  let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hc
  have he := residuePrimeCoordinateMassRatio_close lo N M a hne q hM hcop hpair I x hsmall.le
  simp only [residuePrimeCoordinateMassRatio, Fintype.card_of_isEmpty, Nat.cast_zero,
    zero_div, zero_sub, abs_neg, abs_one] at he
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.residuePrimeCoordinateCell_nonempty_of_small.{u_1, u_2} := @OAI.Erdos3.residuePrimeCoordinateCell_nonempty_of_small.{u_1, u_2}
