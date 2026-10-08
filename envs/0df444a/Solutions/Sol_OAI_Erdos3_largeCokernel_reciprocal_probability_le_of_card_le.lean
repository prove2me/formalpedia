-- Prove2me | solution 1 for OAI.Erdos3.largeCokernel_reciprocal_probability_le_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:25:20.520206+00:00
-- url     : https://prove2.me/submissions/9657898d-3dca-4c0e-868f-b7af62667b60

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem reciprocal_square_le_reciprocal_difference {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) + 1 := by positivity
  calc
    _ ≤ 1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      one_div_le_one_div_of_le (mul_pos hnR hp) (by nlinarith)
    _ = _ := by field_simp; ring

theorem finite_shifted_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N ≤ n) :
    (∑ n ∈ S, 1 / ((n : ℝ) + 1) ^ 2) ≤ 1 / (N : ℝ) := by
  let B := max N (S.sup id + 1)
  have hNB : N ≤ B := Nat.le_max_left _ _
  have hsub : S ⊆ Finset.Ico N B := by
    intro n hn
    apply Finset.mem_Ico.mpr
    exact ⟨hS n hn, (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)).trans_le (Nat.le_max_right _ _)⟩
  have htel : (∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) =
      1 / (N : ℝ) - 1 / (B : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_sub_neg] using
      Finset.sum_Ico_sub (fun n : ℕ => -(1 / (n : ℝ))) hNB
  calc
    _ ≤ ∑ n ∈ Finset.Ico N B, 1 / ((n : ℝ) + 1) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Ico N B, (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact reciprocal_square_le_reciprocal_difference (hN.trans_le (Finset.mem_Ico.mp hn).1)
    _ = 1 / (N : ℝ) - 1 / (B : ℝ) := htel
    _ ≤ 1 / (N : ℝ) := sub_le_self _ (by positivity)

theorem finite_reciprocal_square_tail (S : Finset ℕ) {N : ℕ} (hN : 0 < N)
    (hS : ∀ n ∈ S, N < n) :
    (∑ n ∈ S, 1 / (n : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  have hinj : Set.InjOn (fun n : ℕ => n - 1) S := by
    intro n hn m hm h
    change n - 1 = m - 1 at h
    have hn' := hS n hn
    have hm' := hS m hm
    omega
  have hshift : (∑ n ∈ S.image (fun n : ℕ => (n - 1 : ℕ)), 1 / ((n : ℝ) + 1) ^ 2) =
      ∑ n ∈ S, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have heq : n - 1 + 1 = n := by have h := hS n hn; omega
    have hr : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast heq
    rw [hr]
  rw [← hshift]
  apply finite_shifted_reciprocal_square_tail _ hN
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have h := hS m hm
  omega

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

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

theorem torsionLatticeCharacter_card_le (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype.card (TorsionLatticeCharacter I a) ≤ a ^ Fintype.card I := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective torsionCharacterCoordinates
    (torsionCharacterCoordinates_injective (I := I) (a := a))
  have hc : Fintype.card (rootsOfUnity a ℂ) = a := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  rw [Fintype.card_fun, hc] at h
  exact h

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PrimePowerCharacterScaling
namespace OAI

section

namespace Erdos3

theorem finiteCharacter_exponent (G : Type*) [AddCommGroup G] [Finite G] :
    Monoid.exponent (AddChar G ℂ) = AddMonoid.exponent G := by
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro χ
    ext x
    rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, AddMonoid.exponent_nsmul_eq_zero]
    exact χ.map_zero_eq_one
  · apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
    intro x
    apply AddChar.forall_apply_eq_zero.mp
    intro χ
    rw [AddChar.map_nsmul_eq_pow]
    have h := congrArg (fun ψ : AddChar G ℂ => ψ x) (Monoid.pow_exponent_eq_one χ)
    exact h

theorem exists_character_order_eq_exponent (G : Type*) [AddCommGroup G] [Finite G] :
    ∃ χ : AddChar G ℂ, orderOf χ = AddMonoid.exponent G := by
  obtain ⟨χ, hχ⟩ := Monoid.exists_orderOf_eq_exponent
    (G := AddChar G ℂ) Monoid.ExponentExists.of_finite
  exact ⟨χ, hχ.trans (finiteCharacter_exponent G)⟩

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

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixImage_natAbs_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : (A.det.natAbs : ℤ) • y ∈ A.mulVecLin.range :=
  integerMatrixImage_multiple_smul A Int.dvd_natAbs_self y

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

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

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerCokernelExponent
namespace OAI

section

namespace Erdos3

theorem integerCokernel_finite {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Finite ((I → ℤ) ⧸ L.toAddSubgroup) := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hindex : L.toAddSubgroup.index ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h
    exact (pow_ne_zero _ (NeZero.ne m)) h.symm
  let : L.toAddSubgroup.FiniteIndex := ⟨hindex⟩
  infer_instance

theorem integerCokernelExponent_pos {I : Type*} (L : Submodule ℤ (I → ℤ))
    [Finite ((I → ℤ) ⧸ L.toAddSubgroup)] : 0 < integerCokernelExponent L :=
  AddMonoid.ExponentExists.of_finite.exponent_pos

theorem integerCokernelExponent_dvd_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    integerCokernelExponent L ∣ m := by
  apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.toAddSubgroup x
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  change m • z ∈ L
  have h := hperiod ((integerScalarLattice_mem (m : ℤ) _).mpr ⟨z, rfl⟩)
  simpa only [natCast_zsmul] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CokernelCharacterWitness
namespace OAI

section

namespace Erdos3

theorem integerCokernel_character {I : Type*} (L : Submodule ℤ (I → ℤ))
    [Finite ((I → ℤ) ⧸ L.toAddSubgroup)] :
    ∃ χ : AddChar (I → ℤ) ℂ, orderOf χ = integerCokernelExponent L ∧
      ∀ x ∈ L, χ x = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_character_order_eq_exponent ((I → ℤ) ⧸ L.toAddSubgroup)
  let q := QuotientAddGroup.mk' L.toAddSubgroup
  refine ⟨characterPullback q ψ,
    (characterPullback_order q (QuotientAddGroup.mk'_surjective _) ψ).trans hψ, ?_⟩
  intro x hx
  change ψ (q x) = 1
  have hzero : q x = 0 := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact hx
  rw [hzero, ψ.map_zero_eq_one]

theorem integerLattice_pivot_period {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hAin : A.mulVecLin.range ≤ L) :
    integerScalarLattice I (A.det.natAbs : ℤ) ≤ L := by
  rintro y ⟨z, rfl⟩
  change (A.det.natAbs : ℤ) • z ∈ L
  exact hAin (integerMatrixImage_natAbs_smul A z)

theorem integerCokernelExponent_le_det {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (hAin : A.mulVecLin.range ≤ L) :
    0 < integerCokernelExponent L ∧ integerCokernelExponent L ≤ A.det.natAbs := by
  let : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hA⟩
  have hp := integerLattice_pivot_period L A hAin
  let : Finite ((I → ℤ) ⧸ L.toAddSubgroup) := integerCokernel_finite L A.det.natAbs hp
  exact ⟨integerCokernelExponent_pos L,
    Nat.le_of_dvd (Int.natAbs_pos.mpr hA) (integerCokernelExponent_dvd_period L A.det.natAbs hp)⟩

theorem exists_bounded_annihilating_character {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (hAin : A.mulVecLin.range ≤ L) (B : ℕ) (hB : B < integerCokernelExponent L) :
    ∃ χ : AddChar (I → ℤ) ℂ,
      B < orderOf χ ∧ orderOf χ ≤ A.det.natAbs ∧ ∀ x ∈ L, χ x = 1 := by
  let : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hA⟩
  let : Finite ((I → ℤ) ⧸ L.toAddSubgroup) :=
    integerCokernel_finite L A.det.natAbs (integerLattice_pivot_period L A hAin)
  obtain ⟨χ, hχ, hann⟩ := integerCokernel_character L
  refine ⟨χ, ?_, ?_, hann⟩
  · rwa [hχ]
  · rw [hχ]
    exact (integerCokernelExponent_le_det L A hA hAin).2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ElementaryCharacterTail
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_positiveOrders_eq_Ioc (f : ℕ → ℝ) (B R : ℕ) :
    (∑ a : Fin R, if B < a.val + 1 then f (a.val + 1) else 0) =
      ∑ a ∈ Finset.Ioc B R, f a := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases hBR : B ≤ R
    · rw [Finset.sum_Ioc_succ_top hBR]
      simp only [show B < R + 1 by omega, ite_true]
    · have hRB : R + 1 ≤ B := by omega
      simp [Finset.Ioc_eq_empty_of_le hRB, Finset.Ioc_eq_empty_of_le (by omega : R ≤ B),
        show ¬ B < R + 1 by omega]

theorem finite_positiveOrder_reciprocal_tail (B R : ℕ) (hB : 0 < B) :
    (∑ a : Fin R, if B < a.val + 1 then 1 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0) ≤
      1 / (B : ℝ) := by
  rw [sum_positiveOrders_eq_Ioc (fun a => 1 / (a : ℝ) ^ 2) B R]
  exact finite_reciprocal_square_tail (Finset.Ioc B R) hB
    (fun _ h => (Finset.mem_Ioc.mp h).1)

theorem character_root_power_cancel (a C : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    a ^ n * (C / a ^ (1 / (n : ℝ))) ^ (n * (n + 2)) =
      C ^ (n * (n + 2)) / a ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : (a ^ (1 / (n : ℝ))) ^ n = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    rw [one_div_mul_cancel hn', Real.rpow_one]
  have hpow : (a ^ (1 / (n : ℝ))) ^ (n * (n + 2)) = a ^ (n + 2) := by
    rw [pow_mul, hroot]
  rw [div_pow, hpow, pow_add]
  field_simp

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

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

theorem eventProbability_false {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) (hE : ∀ x, ¬ E x) : p.eventProbability E = 0 := by
  classical
  simp only [eventProbability, hE, ite_false]
  exact p.mean_const 0

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IndependentCharacterEvents
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentCharacterEvent_probability_le {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (χ : AddChar (I → ℤ) ℂ) {q : ℝ}
    (hsingle : ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q) :
    (FiniteProbabilityWeights.pi p).eventProbability (fun x => ∀ j, χ (column j (x j)) = 1) ≤
      q ^ Fintype.card J := by
  rw [FiniteProbabilityWeights.eventProbability_pi p (fun j x => χ (column j x) = 1)]
  calc
    _ ≤ ∏ _j : J, q := Finset.prod_le_prod
      (fun j _ => (p j).eventProbability_nonneg _) (fun j _ => hsingle j)
    _ = _ := by simp

theorem largeOrderAnnihilator_probability_le {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (bad : (∀ j, Ω j) → Prop) (B R : ℕ) (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hbad : ∀ x, bad x → ∃ χ : AddChar (I → ℤ) ℂ,
      B < orderOf χ ∧ orderOf χ ≤ R ∧ ∀ j, χ (column j (x j)) = 1)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q a) :
    (FiniteProbabilityWeights.pi p).eventProbability bad ≤
      ∑ a : Fin R, if B < a.val + 1 then
        ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I * q (a.val + 1) ^ Fintype.card J else 0 := by
  classical
  let C := Σ a : Fin R, TorsionLatticeCharacter I (a.val + 1)
  let F : C → (∀ j, Ω j) → Prop := fun c x =>
    B < c.1.val + 1 ∧ orderOf c.2.val = c.1.val + 1 ∧ ∀ j, c.2.val (column j (x j)) = 1
  have hcover (x) (hx : bad x) : ∃ c, F c x := by
    obtain ⟨χ, hB, hR, hann⟩ := hbad x hx
    let a : Fin R := ⟨orderOf χ - 1, by omega⟩
    have ha : a.val + 1 = orderOf χ := by dsimp [a]; omega
    let c : TorsionLatticeCharacter I (a.val + 1) := ⟨χ, by rw [ha]; exact pow_orderOf_eq_one χ⟩
    refine ⟨⟨a, c⟩, ?_⟩
    change B < a.val + 1 ∧ orderOf χ = a.val + 1 ∧ ∀ j, χ (column j (x j)) = 1
    exact ⟨by rwa [ha], ha.symm, hann⟩
  apply ((FiniteProbabilityWeights.pi p).eventProbability_union_bound bad F hcover).trans
  change (∑ c : Σ a : Fin R, TorsionLatticeCharacter I (a.val + 1),
    (FiniteProbabilityWeights.pi p).eventProbability (F c)) ≤ _
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro a _
  have hterm (χ : TorsionLatticeCharacter I (a.val + 1)) :
      (FiniteProbabilityWeights.pi p).eventProbability (F ⟨a, χ⟩) ≤
        if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0 := by
    by_cases hB : B < a.val + 1
    · rw [if_pos hB]
      by_cases ho : orderOf χ.val = a.val + 1
      · apply ((FiniteProbabilityWeights.pi p).eventProbability_mono _ _ (fun _ h => h.2.2)).trans
        exact independentCharacterEvent_probability_le p column χ.val
          (hsingle _ hB (by omega) χ.val ho)
      · rw [(FiniteProbabilityWeights.pi p).eventProbability_false _ (fun _ h => ho h.2.1)]
        exact pow_nonneg (hq _) _
    · rw [if_neg hB,
        (FiniteProbabilityWeights.pi p).eventProbability_false _ (fun _ h => hB h.1)]
  calc
    _ ≤ ∑ _χ : TorsionLatticeCharacter I (a.val + 1),
        if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0 :=
      Finset.sum_le_sum (fun χ _ => hterm χ)
    _ = (Fintype.card (TorsionLatticeCharacter I (a.val + 1)) : ℝ) *
        (if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0) := by simp
    _ ≤ ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I *
        (if B < a.val + 1 then q (a.val + 1) ^ Fintype.card J else 0) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast torsionLatticeCharacter_card_le I (a.val + 1)
      · split_ifs
        · exact pow_nonneg (hq _) _
        · exact le_rfl
    _ = _ := by split_ifs <;> simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.LargeCokernelProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem sampledColumn_mem_range {I J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (x : ∀ j, Ω j) (j : J) :
    column j (x j) ∈ (sampledColumnMatrix column x).mulVecLin.range := by
  refine ⟨Pi.single j 1, ?_⟩
  exact Matrix.mulVec_single_one _ _

theorem largeCokernelEvent_character {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} (column : ∀ j, Ω j → I → ℤ) (B R : ℕ) (x : ∀ j, Ω j)
    (hx : largeCokernelEvent column B R x) :
    ∃ χ : AddChar (I → ℤ) ℂ, B < orderOf χ ∧ orderOf χ ≤ R ∧
      ∀ j, χ (column j (x j)) = 1 := by
  obtain ⟨A, hA, hAin, hAR, hB⟩ := hx
  obtain ⟨χ, hχB, hχA, hann⟩ := exists_bounded_annihilating_character
    (sampledColumnMatrix column x).mulVecLin.range A hA hAin B hB
  exact ⟨χ, hχB, hχA.trans hAR,
    fun j => hann _ (sampledColumn_mem_range column x j)⟩

theorem largeCokernel_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (q : ℕ → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤ q a) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      ∑ a : Fin R, if B < a.val + 1 then
        ((a.val + 1 : ℕ) : ℝ) ^ Fintype.card I * q (a.val + 1) ^ Fintype.card J else 0 :=
  largeOrderAnnihilator_probability_le p column _ B R q hq
    (largeCokernelEvent_character column B R) hsingle

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem character_root_power_cancel_le {a C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    {n k : ℕ} (hn : 0 < n) (hk : n * (n + 2) ≤ k) :
    a ^ n * (C / a ^ (1 / (n : ℝ))) ^ k ≤ C ^ k / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hr0 : 0 < a ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos ha0 _
  have hr1 : 1 ≤ a ^ (1 / (n : ℝ)) :=
    Real.one_le_rpow ha (by positivity)
  have hi1 : 1 / a ^ (1 / (n : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hr0).mpr
    simpa using hr1
  have hpow := pow_le_pow_of_le_one (le_of_lt (one_div_pos.mpr hr0)) hi1 hk
  calc
    _ = C ^ k * (a ^ n * (1 / a ^ (1 / (n : ℝ))) ^ k) := by
      rw [div_eq_mul_one_div, mul_pow]
      ring
    _ ≤ C ^ k * (a ^ n * (1 / a ^ (1 / (n : ℝ))) ^ (n * (n + 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (pow_nonneg ha0.le _))
        (pow_nonneg hC _)
    _ = C ^ k / a ^ 2 := by
      rw [character_root_power_cancel a 1 ha0 n hn]
      simp only [one_pow]
      ring

theorem finite_character_reciprocal_tail_of_le (B R n k : ℕ)
    (hB : 0 < B) (hn : 0 < n) (hk : n * (n + 2) ≤ k)
    (C : ℝ) (hC : 0 ≤ C) :
    (∑ a : Fin R, if B < a.val + 1 then
      ((a.val + 1 : ℕ) : ℝ) ^ n *
        (C / ((a.val + 1 : ℕ) : ℝ) ^ (1 / (n : ℝ))) ^ k else 0) ≤
      C ^ k / (B : ℝ) := by
  calc
    _ ≤ C ^ k * ∑ a : Fin R,
        if B < a.val + 1 then 1 / ((a.val + 1 : ℕ) : ℝ) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      split_ifs with h
      · simpa only [one_div, div_eq_mul_inv, one_mul] using
          character_root_power_cancel_le (a := ((a.val + 1 : ℕ) : ℝ))
            (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a.val)) hC hn hk
      · simp
    _ ≤ C ^ k / (B : ℝ) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (finite_positiveOrder_reciprocal_tail B R hB)
        (pow_nonneg hC _)

theorem largeCokernel_reciprocal_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (hB : 0 < B) (C : ℝ) (hC : 0 ≤ C)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤
        C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ))) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      C ^ Fintype.card J / (B : ℝ) := by
  have h := largeCokernel_probability_le p column B R
    (fun a => C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ)))
    (fun a => div_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg a) _)) hsingle
  exact h.trans (finite_character_reciprocal_tail_of_le B R (Fintype.card I) (Fintype.card J)
    hB Fintype.card_pos hJ C hC)

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

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.largeCokernel_reciprocal_probability_le_of_card_le.{u_1, u_2, u_3} := @OAI.Erdos3.largeCokernel_reciprocal_probability_le_of_card_le.{u_1, u_2, u_3}
