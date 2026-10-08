-- Prove2me | solution 1 for OAI.Erdos3.scalarCube_largeCokernel_probability_le_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:27:00.907156+00:00
-- url     : https://prove2.me/submissions/b7d8f532-c089-4a0b-bd62-835c8c228557

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014
import Theorems.Thm_OAI_Erdos3_largeCokernel_reciprocal_probability_le_of_card_le

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem latticeCharacterCoordinates_pow {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (n : ℕ) (i : I) :
    latticeCharacterCoordinates (χ ^ n) i = latticeCharacterCoordinates χ i ^ n := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem latticeCharacter_coordinate_order_dvd {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (a : ℕ) (hχ : χ ^ a = 1) (i : I) :
    orderOf (latticeCharacterCoordinates χ i) ∣ a :=
  orderOf_dvd_iff_pow_eq_one.mpr
    (congrArg (fun ψ : AddChar (I → ℤ) ℂ => ψ (Pi.single i 1)) hχ)

theorem latticeCharacter_coordinate_order_pos {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) (i : I) :
    0 < orderOf (latticeCharacterCoordinates χ i) :=
  Nat.pos_of_dvd_of_pos
    (latticeCharacter_coordinate_order_dvd χ (orderOf χ) (pow_orderOf_eq_one χ) i) hχ

theorem latticeCharacter_order_le_product {I : Type*} [Fintype I] [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    orderOf χ ≤ ∏ i, orderOf (latticeCharacterCoordinates χ i) := by
  have hpos : 0 < ∏ i, orderOf (latticeCharacterCoordinates χ i) :=
    Finset.prod_pos (fun i _ => latticeCharacter_coordinate_order_pos χ hχ i)
  apply Nat.le_of_dvd hpos
  apply orderOf_dvd_iff_pow_eq_one.mpr
  apply latticeCharacterCoordinates_injective
  funext i
  rw [latticeCharacterCoordinates_pow]
  change (latticeCharacterCoordinates χ i) ^ (∏ j, orderOf (latticeCharacterCoordinates χ j)) = 1
  apply orderOf_dvd_iff_pow_eq_one.mp
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem exists_coordinate_order_power_ge {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, 0 < orderOf (latticeCharacterCoordinates χ i) ∧
      orderOf χ ≤ orderOf (latticeCharacterCoordinates χ i) ^ Fintype.card I := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => orderOf (latticeCharacterCoordinates χ i)) Finset.univ_nonempty
  refine ⟨i, latticeCharacter_coordinate_order_pos χ hχ i, (latticeCharacter_order_le_product χ hχ).trans ?_⟩
  calc
    _ ≤ ∏ _j : I, orderOf (latticeCharacterCoordinates χ i) :=
      Finset.prod_le_prod' (fun coordinate hcoordinate => hi coordinate hcoordinate)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem exists_coordinate_order_rpow_ge {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, 0 < orderOf (latticeCharacterCoordinates χ i) ∧
      (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) ≤ orderOf (latticeCharacterCoordinates χ i) := by
  obtain ⟨i, hi, hpow⟩ := exists_coordinate_order_power_ge χ hχ
  refine ⟨i, hi, ?_⟩
  have hq : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hpowR : (orderOf χ : ℝ) ≤ (orderOf (latticeCharacterCoordinates χ i) : ℝ) ^ Fintype.card I := by
    exact_mod_cast hpow
  have hb : (0 : ℝ) ≤ orderOf (latticeCharacterCoordinates χ i) := Nat.cast_nonneg _
  calc
    _ ≤ ((orderOf (latticeCharacterCoordinates χ i) : ℝ) ^ Fintype.card I) ^
        (1 / (Fintype.card I : ℝ)) := Real.rpow_le_rpow (Nat.cast_nonneg _) hpowR (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb, mul_one_div_cancel hq.ne', Real.rpow_one]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AnnihilatingCoordinateResidue
namespace OAI

section

namespace Erdos3

theorem update_integerVector_sub {I : Type*} [DecidableEq I]
    (v : I → ℤ) (i : I) (x y : ℤ) :
    Function.update v i x - Function.update v i y = (x - y) • (Pi.single i 1 : I → ℤ) := by
  ext j
  by_cases hji : j = i
  · subst j; simp
  · simp [hji]

theorem annihilating_coordinate_difference_dvd {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I) {x y : ℤ}
    (hxy : χ (Function.update v i x) = χ (Function.update v i y)) :
    (orderOf (latticeCharacterCoordinates χ i) : ℤ) ∣ x - y := by
  have hn : χ (Function.update v i y) ≠ 0 := (χ.val_isUnit _).ne_zero
  have hd : χ (Function.update v i x - Function.update v i y) = 1 := by
    rw [χ.map_sub_eq_div, hxy, div_self hn]
  rw [update_integerVector_sub, χ.map_zsmul_eq_zpow] at hd
  change latticeCharacterCoordinates χ i ^ (x - y) = 1 at hd
  let u := (χ.val_isUnit (Pi.single i 1)).unit
  have hu : (u : ℂ) = latticeCharacterCoordinates χ i := (χ.val_isUnit _).unit_spec
  have hpow : u ^ (x - y) = 1 := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val, hu, Units.val_one] using hd
  have hdiv := orderOf_dvd_iff_zpow_eq_one.mpr hpow
  rwa [← orderOf_units, hu] at hdiv

theorem annihilating_coordinate_residue {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I) :
    ∃ r : ℤ, ∀ x, χ (Function.update v i x) = 1 →
      x ≡ r [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)] := by
  by_cases hex : ∃ r, χ (Function.update v i r) = 1
  · obtain ⟨r, hr⟩ := hex
    refine ⟨r, fun x hx => ?_⟩
    have hdiv := annihilating_coordinate_difference_dvd χ v i (hx.trans hr.symm)
    exact (show r ≡ x [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)] from
      Int.modEq_iff_dvd.mpr hdiv).symm
  · exact ⟨0, fun x hx => False.elim (hex ⟨x, hx⟩)⟩

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnnihilatorIntervalBound
namespace OAI

section

namespace Erdos3

theorem annihilatorInterval_card_le {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I)
    (hi : 0 < orderOf (latticeCharacterCoordinates χ i)) (a b : ℤ) (hab : a ≤ b) :
    ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / orderOf (latticeCharacterCoordinates χ i) + 1 := by
  classical
  obtain ⟨r, hr⟩ := annihilating_coordinate_residue χ v i
  have hsub : Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b) ⊆
      Finset.filter (fun x => x ≡ r [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)])
        (Finset.Ico a b) := by
    intro x hx
    obtain ⟨hxb, hχx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxb, hr x hχx⟩
  have hc : ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) ≤
      (Finset.filter (fun x => x ≡ r [ZMOD (orderOf (latticeCharacterCoordinates χ i) : ℤ)])
        (Finset.Ico a b)).card := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (by
    simpa only [Int.cast_natCast] using scalarResidue_card_real_le a b
      (orderOf (latticeCharacterCoordinates χ i) : ℤ) r hab (by exact_mod_cast hi))

theorem annihilatorInterval_probability_le {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I)
    (hi : 0 < orderOf (latticeCharacterCoordinates χ i)) (a b : ℤ) (hab : a < b) :
    ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) /
        ((b - a : ℤ) : ℝ) ≤
      1 / (orderOf (latticeCharacterCoordinates χ i) : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have hlen : (0 : ℝ) < (b - a : ℤ) := by exact_mod_cast sub_pos.mpr hab
  have hd : (0 : ℝ) < orderOf (latticeCharacterCoordinates χ i) := by exact_mod_cast hi
  apply (div_le_div_of_nonneg_right (annihilatorInterval_card_le χ v i hi a b hab.le) hlen.le).trans_eq
  field_simp

theorem exists_annihilating_coordinate_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    ∃ i, ∀ (v : I → ℤ) (a b : ℤ), a < b →
      ((Finset.filter (fun x => χ (Function.update v i x) = 1) (Finset.Ico a b)).card : ℝ) /
          ((b - a : ℤ) : ℝ) ≤
        1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ) := by
  obtain ⟨i, hi, hroot⟩ := exists_coordinate_order_rpow_ge χ hχ
  refine ⟨i, fun v a b hab => ?_⟩
  apply (annihilatorInterval_probability_le χ v i hi a b hab).trans
  exact add_le_add
    (one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hχ) _) hroot) le_rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DeterminantCutoffScale
namespace OAI

section

namespace Erdos3

theorem nat_monomial_root_le (n C L : ℕ) (hn : 0 < n) (hC : 1 ≤ C) :
    ((C * L ^ n : ℕ) : ℝ) ^ (1 / (n : ℝ)) ≤ (C : ℝ) * L := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : C * L ^ n ≤ (C * L) ^ n := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ (le_self_pow hC hn.ne')
  calc
    _ ≤ (((C * L : ℕ) : ℝ) ^ n) ^ (1 / (n : ℝ)) := by
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
      exact_mod_cast hpow
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
        mul_one_div_cancel hn', Real.rpow_one, Nat.cast_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteCoordinateSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_le_of_coordinate_slices {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (i : I) (f : (I → X) → ℝ) (C : ℝ)
    (hslice : ∀ x : I → X, (𝔼 a : X, f (Function.update x i a)) ≤ C) :
    (𝔼 x : I → X, f x) ≤ C := by
  classical
  let e := Equiv.funSplitAt i X
  have he := Fintype.expect_equiv e f (fun p => f (e.symm p)) (fun x => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_le Finset.univ_nonempty
  intro r _
  let x : I → X := e.symm (Classical.choice inferInstance, r)
  have hupdate (a : X) : e.symm (a, r) = Function.update x i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, x, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  simpa only [hupdate] using hslice x

end Erdos3

end

end OAI

end

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

theorem uniform_condition_weight_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (c : ℝ) (hc : 0 < c)
    (hmass : c ≤ (uniform Ω).mass G) (x : Ω) :
    ((uniform Ω).condition G hG).weight x ≤ c⁻¹ * (Fintype.card Ω : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹ := by positivity
  change (if x ∈ G then (Fintype.card Ω : ℝ)⁻¹ else 0) / (uniform Ω).mass G ≤ _
  by_cases hx : x ∈ G
  · rw [if_pos hx, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hc hmass) hcard
  · rw [if_neg hx, zero_div]
    positivity

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_le_of_weight_le {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (C : ℝ)
    (hw : ∀ x, p.weight x ≤ C * q.weight x) (E : Ω → Prop) :
    p.eventProbability E ≤ C * q.eventProbability E := by
  classical
  unfold eventProbability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx, hw x]

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

theorem integerBox_character_expect_le {I K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (a b : ℤ) (hab : a < b)
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    (𝔼 x : K → Finset.Ico a b, if χ (fun i => (x (e i) : ℤ)) = 1 then (1 : ℝ) else 0) ≤
      1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ) := by
  classical
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  obtain ⟨i, hi⟩ := exists_annihilating_coordinate_bound χ hχ
  apply expect_le_of_coordinate_slices (e i)
  intro x
  have hupdate (y : Finset.Ico a b) :
      (fun j => (Function.update x (e i) y (e j) : ℤ)) =
        Function.update (fun j => (x (e j) : ℤ)) i (y : ℤ) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, he.ne hji]
  simp_rw [hupdate]
  rw [integerInterval_indicator_expect a b hab.le
    (fun y => χ (Function.update (fun j => (x (e j) : ℤ)) i y) = 1)]
  exact hi _ a b hab

theorem integerBox_character_probability_le {I K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (a b : ℤ) (hab : a < b)
    (p : FiniteProbabilityWeights (K → Finset.Ico a b)) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x, p.weight x ≤ C * (Fintype.card (K → Finset.Ico a b) : ℝ)⁻¹)
    (χ : AddChar (I → ℤ) ℂ) (hχ : 0 < orderOf χ) :
    p.eventProbability (fun x => χ (fun i => (x (e i) : ℤ)) = 1) ≤
      C * (1 / (orderOf χ : ℝ) ^ (1 / (Fintype.card I : ℝ)) + 1 / ((b - a : ℤ) : ℝ)) := by
  classical
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  let u := FiniteProbabilityWeights.uniform (K → Finset.Ico a b)
  have h := p.eventProbability_le_of_weight_le u C hw
    (fun x => χ (fun i => (x (e i) : ℤ)) = 1)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC
  unfold FiniteProbabilityWeights.eventProbability
  rw [FiniteProbabilityWeights.uniform_mean]
  exact integerBox_character_expect_le e he a b hab χ hχ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerColumnMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

theorem integerColumnMinor_range_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I → J) :
    (A.submatrix id s).mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨s i, rfl⟩

theorem integerColumnMinor_det_bound {I J : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I J ℤ) (s : I → J) (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    (A.submatrix id s).det.natAbs ≤ (Fintype.card I).factorial * H ^ Fintype.card I :=
  integer_det_natAbs_le _ (fun i j => hA i (s j))

theorem nonzeroMinor_largeCokernelEvent {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) (B H : ℕ)
    (hbound : ∀ i j, (column j (x j) i).natAbs ≤ H)
    (hminor : ∃ s : I → J, ((sampledColumnMatrix column x).submatrix id s).det ≠ 0)
    (hB : B < integerCokernelExponent (sampledColumnMatrix column x).mulVecLin.range) :
    largeCokernelEvent column B ((Fintype.card I).factorial * H ^ Fintype.card I) x := by
  obtain ⟨s, hs⟩ := hminor
  exact ⟨_, hs, integerColumnMinor_range_le _ s,
    integerColumnMinor_det_bound _ s H hbound, hB⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BoxCokernelProbability
namespace OAI

section

namespace Erdos3

theorem reciprocal_interval_error_absorb (a l C D : ℝ) (ha : 0 < a) (hl : 0 < l)
    (hC : 0 ≤ C) (hscale : a ≤ D * l) :
    C * (1 / a + 1 / l) ≤ C * (1 + D) / a := by
  have h : 1 / l ≤ D / a := by
    apply (div_le_div_iff₀ hl ha).mpr
    simpa using hscale
  calc
    _ ≤ C * (1 / a + D / a) := mul_le_mul_of_nonneg_left (add_le_add le_rfl h) hC
    _ = _ := by ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

theorem integerScalarCubeSet_card_lower (I : Type*) [Fintype I] [DecidableEq I] (L H : ℕ)
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) :
    H ^ (Fintype.card I + 1) ≤ (integerScalarCubeSet I L).card := by
  classical
  have hHL' : H ≤ L := by nlinarith
  let point (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((x i).val : ℤ), Finset.mem_Ico.mpr ⟨by omega, by have := (x i).isLt; omega⟩⟩
  have hpoint (x : Option I → Fin H) : point x ∈ integerScalarCubeSet I L :=
    (mem_integerScalarCubeSet L _).mpr (integerScalarCube_small_positive hH hHL x)
  let e : (Option I → Fin H) → ↥(integerScalarCubeSet I L) := fun x => ⟨point x, hpoint x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥(integerScalarCubeSet I L) => (z.val i : ℤ)) h
    change ((x i).val : ℤ) = ((y i).val : ℤ) at hi
    exact_mod_cast hi
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity

theorem integerScalarCubeReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) :
    (integerScalarCubeDensityCap I)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  let n := Fintype.card I + 1
  let H := L / n
  have hn : 0 < n := by dsimp [n]; omega
  have hH : 0 < H := Nat.div_pos hsize hn
  have hHL : n * H ≤ L := Nat.mul_div_le L n
  have hc := integerScalarCubeSet_card_lower I L H hH hHL
  have hfloor : (L : ℝ) ≤ 2 * (n : ℝ) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hratio : 1 / (4 * (n : ℝ)) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    _ = (1 / (4 * (n : ℝ))) ^ n := by
      simp only [integerScalarCubeDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem integerScalarCubeWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (x : IntegerScalarCubeBox I L) :
    (integerScalarCubeWeights I L hL).weight x ≤
      integerScalarCubeDensityCap I * (Fintype.card (IntegerScalarCubeBox I L) : ℝ)⁻¹ := by
  classical
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_weight_le (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) ((integerScalarCubeDensityCap I)⁻¹)
    (inv_pos.mpr (integerScalarCubeDensityCap_pos I))
    (integerScalarCubeReference_mass_lower I L hL hsize) x
  simpa only [integerScalarCubeWeights, integerScalarCubeReference, inv_inv] using h

open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxCokernel_probability_le_of_card_le {I J K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (p : ∀ j, FiniteProbabilityWeights (K → Finset.Ico (lo j) (hi j)))
    (B R : ℕ) (hB : 0 < B) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J)
    (hw : ∀ j x, (p j).weight x ≤
      C * (Fintype.card (K → Finset.Ico (lo j) (hi j)) : ℝ)⁻¹)
    (hscale : ∀ j, (R : ℝ) ^ (1 / (Fintype.card I : ℝ)) ≤
      D * ((hi j - lo j : ℤ) : ℝ)) :
    (FiniteProbabilityWeights.pi p).eventProbability
        (largeCokernelEvent (fun _j x i => (x (e i) : ℤ)) B R) ≤
      (C * (1 + D)) ^ Fintype.card J / (B : ℝ) := by
  apply largeCokernel_reciprocal_probability_le_of_card_le p _ B R hB (C * (1 + D))
    (mul_nonneg hC (by positivity)) hJ
  intro a haB haR χ hχ j
  have ha : 0 < a := by omega
  have hχpos : 0 < orderOf χ := by omega
  have h := integerBox_character_probability_le e he (lo j) (hi j) (hlen j)
    (p j) C hC (hw j) χ hχpos
  rw [hχ] at h
  apply h.trans
  apply reciprocal_interval_error_absorb _ _ C D
    (Real.rpow_pos_of_pos (by exact_mod_cast ha) _) (by exact_mod_cast sub_pos.mpr (hlen j)) hC
  exact (Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast haR) (by positivity)).trans
    (hscale j)

theorem scalarCube_largeCokernel_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (L B : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) (hB : 0 < B)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (scalarCubeLargeCokernelEvent B) ≤
      (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^
        Fintype.card J / (B : ℝ) := by
  let R := (Fintype.card I).factorial * L ^ Fintype.card I
  have hbound := boxCokernel_probability_le_of_card_le
    (I := I) (J := J) (K := Option I) Option.some (Option.some_injective I)
    (fun _ => -(L : ℤ)) (fun _ => (L : ℤ)) (fun _ => by omega)
    (fun _ => integerScalarCubeWeights I L hL) B R hB
    (integerScalarCubeDensityCap I) ((Fintype.card I).factorial : ℝ)
    (integerScalarCubeDensityCap_pos I).le (Nat.cast_nonneg _) hJ
    (fun _ x => integerScalarCubeWeights_weight_le I L hL hsize x) (fun _ => ?_)
  · apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hbound
    intro x hx
    apply nonzeroMinor_largeCokernelEvent _ x B L _ hx.1 hx.2
    intro i j
    have h := Finset.mem_Ico.mp (x j (some i)).property
    have ha : |(x j (some i) : ℤ)| ≤ (L : ℤ) := abs_le.mpr ⟨h.1, h.2.le⟩
    have hn : (((x j (some i) : ℤ).natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by
      simpa only [Int.natCast_natAbs] using ha
    exact_mod_cast hn
  · have h := nat_monomial_root_le (Fintype.card I) (Fintype.card I).factorial L
      Fintype.card_pos (Nat.factorial_pos _)
    apply h.trans
    push_cast
    nlinarith [show (0 : ℝ) ≤ (Fintype.card I).factorial from Nat.cast_nonneg _]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

variable (selection : Fin dim ↪ G) (M : ℕ)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)

include hbases htest

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.scalarCube_largeCokernel_probability_le_of_card_le.{u_1, u_2} := @OAI.Erdos3.scalarCube_largeCokernel_probability_le_of_card_le.{u_1, u_2}
