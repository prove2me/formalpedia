-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate15.certificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:57:36.418731+00:00
-- url     : https://prove2.me/submissions/22801e70-dacc-4d3b-9fcb-41de80e99d49

import Mathlib
import Definitions.Def_OAIQ030L003
import Definitions.Def_OAIQ030L035
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_Certificate15_rows_checked
import Theorems.Thm_OAI_LaughlinGap_RealOccupation_fourCertificate_of_tables

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

lemma uCoefficient_eq_fast (c z T p : ℕ) : uCoefficient c z T p = uFast c z T p := by
  simp only [uCoefficient,uFast,chooseFast_eq]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma vCoefficient_eq_fast (D T r p j k : ℕ) : vCoefficient D T r p j k = vFast D T r p j k := by
  simp only [vCoefficient,vFast,uCoefficient_eq_fast]

lemma fourTermCoefficient_eq_eval (D r : ℕ) (a : FourTerm D) :
    fourTermCoefficient D r a = fourTermEval D r a := by
  simp only [fourTermCoefficient,fourTermEval,vCoefficient_eq_fast]

lemma fourColumn_eq_fiber {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25))
    (s : Finset (FourTerm D)) (hs : ∀ a, (fourTermLabels hD a).toFinset=A ↔ a ∈ s) :
    fourColumn hD r A = ∑ a ∈ s, fourTermEval D r a * Occupation.wordSign (fourTermLabels hD a) := by
  simp only [fourColumn,hs,fourTermCoefficient_eq_eval,Finset.sum_ite_mem,Finset.univ_inter]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntegerFourRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four Rows. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma uFast_eq_int (c z T p : ℕ) : uFast c z T p = (uInt c z T p:ℚ) := by
  simp [uFast,uInt]

end LaughlinGap.Spin
namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma vFast_eq_int (D T r p j k : ℕ) : vFast D T r p j k = (vInt D T r p j k:ℚ) := by
  simp [vFast,vInt,uFast_eq_int]

lemma fourSumEval_eq_integer (a : Fin 8) (D s : ℕ) (i k : Fin 9) :
    (exactRows a).fourSumEval D s i k = (fourSumInteger a D s i k:ℚ)/10000000 := by
  simp only [RationalRow.fourSumEval,fourSumInteger,exactRows,vFast_eq_int,Int.cast_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs
  · push_cast; ring
  · simp

lemma fourRowWeight_eq {D : ℕ} (hD : D ≤ 23) (a : Fin 8) (i k : Fin 9) :
    fourRowFactor a.val D i.val k.val / (100000000000000:ℚ) =
      (fourRowWeight D a i k:ℚ) / fourMatrixDenominator D := by
  by_cases h : D ≤ a.val+i.val+k.val
  · simp only [fourRowFactor,fourRowWeight,ite_eq_left h,fourMatrixDenominator]
    have hT : a.val+i.val+k.val ≤ 23 := by have := a.isLt; have := i.isLt; have := k.isLt; omega
    have he : 2*(a.val+i.val+k.val)+a.val ≤ 53 := by
      have := a.isLt; have := i.isLt; have := k.isLt; omega
    have hf : (a.val+i.val+k.val-D).factorial *
        (23-D).descFactorial (23-(a.val+i.val+k.val)) = (23-D).factorial := by
      convert Nat.factorial_mul_descFactorial (show 23-(a.val+i.val+k.val) ≤ 23-D by omega) using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      omega
    have hp : (2:ℚ)^(2*(a.val+i.val+k.val)+a.val) *
        2^(53-(2*(a.val+i.val+k.val)+a.val)) = (2:ℚ)^53 := by
      rw [← pow_add,Nat.add_sub_of_le he]
    have hfc : ((a.val+i.val+k.val-D).factorial:ℚ) *
        ((23-D).descFactorial (23-(a.val+i.val+k.val)):ℚ) = ((23-D).factorial:ℚ) := by
      exact_mod_cast hf
    push_cast
    field_simp
    nlinarith [hp,hfc]
  · simp [fourRowFactor,fourRowWeight,h]

lemma exactFourEval_eq {D : ℕ} (hD : D ≤ 23) (u v : ℕ) :
    (∑ a : Fin 8, (exactRows a).fourMatrixEval D u v) = exactFourEval D u v := by
  simp only [RationalRow.fourMatrixEval,fourSumEval_eq_integer,exactFourEval,exactFourInteger,
    Int.cast_neg,Int.cast_sum,Int.cast_mul,Finset.sum_neg_distrib,neg_div,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := fourRowWeight_eq hD a i k
  calc
    _ = (fourRowFactor a.val D i.val k.val/100000000000000) *
        (fourSumInteger a D u i k:ℚ) * (fourSumInteger a D v k i:ℚ) := by dsimp [exactRows]; ring
    _ = _ := by rw [hh]; ring

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastFourKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Four Keys. -/

noncomputable section


namespace LaughlinGap.RealOccupation

lemma fourKeys_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (rep : Fin K → FourTerm D)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (hrep : ∀ a, (fourTermLabels hD (rep a)).Nodup ∧ (fourTermLabels hD (rep a)).toFinset=keys a) :
    fourKeys hD = Finset.univ.image keys := by
  ext A
  constructor
  · intro h
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨index b,Finset.mem_univ _,(cover b (Finset.mem_filter.mp hb).2).symm⟩
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨rep a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hrep a).1⟩,(hrep a).2⟩

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma checkFourTerms_sound {D : ℕ} (P : FourTerm D → Prop) [DecidablePred P]
    (h : checkFourTerms D (fun b => decide (P b)) = true) : ∀ b, P b := by
  rintro ⟨n,j,x⟩
  have hn := List.all_eq_true.mp h n (List.mem_finRange n)
  have hj := List.all_eq_true.mp hn j (List.mem_finRange j)
  exact of_decide_eq_true (List.all_eq_true.mp hj x (List.mem_finRange x))

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma fourFibers_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (fibers : Fin K → Finset (FourTerm D))
    (hi : Function.Injective keys) (hcard : ∀ a, (keys a).card=4)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (fiberCover : ∀ b, (fourTermLabels hD b).Nodup → b ∈ fibers (index b))
    (fiberSound : ∀ a, ∀ b ∈ fibers a, (fourTermLabels hD b).toFinset=keys a) :
    ∀ a b, (fourTermLabels hD b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a b
  constructor
  · intro h
    have hn : (fourTermLabels hD b).Nodup := by
      apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(fourTermLabels hD b) : Multiset (Fin 25)))).mp
      change (fourTermLabels hD b).toFinset.card=(fourTermLabels hD b).length
      rw [h,hcard]
      rfl
    have hind : index b=a := hi ((cover b hn).symm.trans h)
    simpa only [hind] using fiberCover b hn
  · exact fiberSound a b

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma checkFourFibersSound_sound {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (fibers : Fin K → Finset (FourTerm D))
    (h : checkFourFibersSound hD keys fibers=true) :
    ∀ a b, b ∈ fibers a → (fourTermLabels hD b).toFinset=keys a := by
  intro a b hb
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  exact @of_decide_eq_true _ (Finset.decidableDforallFinset (s := fibers a)) ha b hb

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Certificate. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

lemma rational_ldl_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M L : Matrix κ κ ℚ) (d : κ → ℚ) (hd : ∀ i, 0 ≤ d i)
    (he : M = L * Matrix.diagonal d * L.transpose) :
    (M.map (algebraMap ℚ ℂ)).PosSemidef := by
  have hp : (Matrix.diagonal (fun i => (d i:ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    simpa only [← Complex.ofReal_ratCast,Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im,
      and_true] using (Rat.cast_nonneg (K := ℝ)).mpr (hd i)
  have hh := hp.mul_mul_conjTranspose_same (L.map (algebraMap ℚ ℂ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [he,Matrix.map_mul,Matrix.map_mul]
  congr 1
  · congr 1
    ext i j
    by_cases h : i=j <;> simp [h]
  · ext i j
    simp [Matrix.conjTranspose_apply]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Tables. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

lemma rationalCreatedGram_of_columns {D : ℕ} (hD : D ≤ 23) {K : ℕ}
    (keys : Fin K → Finset (Fin 25)) (cols : Matrix (Fin ((D+1)/2)) (Fin K) ℚ)
    (hk : fourKeys hD=Finset.univ.image keys) (hi : Function.Injective keys)
    (hc : ∀ u a, fourColumn hD (2*u.val+1) (keys a)=cols u a)
    (u v : Fin ((D+1)/2)) :
    rationalCreatedGram hD ((fourCopyEquiv D).symm u) ((fourCopyEquiv D).symm v) =
      ∑ a : Fin K, cols u a * cols v a / setFactorial (keys a) := by
  unfold rationalCreatedGram
  rw [hk,Finset.sum_image (fun _ _ _ _ h => hi h)]
  simp only [fourCopyEquiv_symm_val,hc]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CheckedTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Tables. -/

noncomputable section


namespace LaughlinGap.Arithmetic

lemma checkVector_sound {n : ℕ} {α : Type*} [DecidableEq α]
    (A B : Fin n → α) (h : checkVector A B = true) : ∀ i, A i = B i := by
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

end LaughlinGap.Arithmetic

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate15

lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 8,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 8,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 7,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 7,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 6,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 6,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 5,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 5,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 4,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 4,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 3,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 3,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 2,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover_13 : ∀ j : Fin 7, ∀ x : Fin 2,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨13,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨13,j,x⟩).toFinset=keys (keyIndex 13 j x) := by decide +kernel
lemma cover_14 : ∀ j : Fin 7, ∀ x : Fin 1,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨14,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨14,j,x⟩).toFinset=keys (keyIndex 14 j x) := by decide +kernel
lemma cover_15 : ∀ j : Fin 8, ∀ x : Fin 1,
  (fourTermLabels (by omega : 15 ≤ 23) ⟨15,j,x⟩).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) ⟨15,j,x⟩).toFinset=keys (keyIndex 15 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 15, (fourTermLabels (by omega : 15 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 15 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
  · exact cover_9 j x
  · exact cover_10 j x
  · exact cover_11 j x
  · exact cover_12 j x
  · exact cover_13 j x
  · exact cover_14 j x
  · exact cover_15 j x
lemma representatives_checked : ∀ a : Fin 23,
  (fourTermLabels (by omega : 15 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 15 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 15 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 15 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 23, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 15,
    (fourTermLabels (by omega : 15 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 23, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 15 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 23, ∀ b : FourTerm 15,
    (fourTermLabels (by omega : 15 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 15 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(0 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(1 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(2 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(3 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(4 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(5 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_6 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(6 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_7 : ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*(7 : Fin 8).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 8, ∀ v : Fin 23, (∑ b ∈ fibers v, fourTermEval 15 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 15 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
  · exact columns_checked_6
  · exact columns_checked_7
lemma gram_checked_0 : ∀ v : Fin 8, (∑ a : Fin 23, columns (0 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 8, (∑ a : Fin 23, columns (1 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 8, (∑ a : Fin 23, columns (2 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 8, (∑ a : Fin 23, columns (3 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 8, (∑ a : Fin 23, columns (4 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 8, (∑ a : Fin 23, columns (5 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_6 : ∀ v : Fin 8, (∑ a : Fin 23, columns (6 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_7 : ∀ v : Fin 8, (∑ a : Fin 23, columns (7 : Fin 8) a * columns v a / setFactorial (keys a)) = Z 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 8, ∀ v : Fin 8, (∑ a : Fin 23, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
  · exact gram_checked_6
  · exact gram_checked_7
lemma product_checked_0 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (0 : Fin 8) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (1 : Fin 8) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (2 : Fin 8) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (3 : Fin 8) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (4 : Fin 8) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (5 : Fin 8) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_6 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (6 : Fin 8) v = W 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_7 : ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) (7 : Fin 8) v = W 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 8, ∀ v : Fin 8, (Z * tableComparison 15 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
  · exact product_checked_6
  · exact product_checked_7
lemma compression_checked_0 : ∀ v : Fin 8, (W * Z) (0 : Fin 8) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 8, (W * Z) (1 : Fin 8) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 8, (W * Z) (2 : Fin 8) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 8, (W * Z) (3 : Fin 8) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 8, (W * Z) (4 : Fin 8) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_5 : ∀ v : Fin 8, (W * Z) (5 : Fin 8) v = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_6 : ∀ v : Fin 8, (W * Z) (6 : Fin 8) v = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_7 : ∀ v : Fin 8, (W * Z) (7 : Fin 8) v = M 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 8, ∀ v : Fin 8, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
  · exact compression_checked_5
  · exact compression_checked_6
  · exact compression_checked_7
lemma ldl_checked_0 : ∀ v : Fin 8, (∑ k : Fin 8, L (0 : Fin 8) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 8, (∑ k : Fin 8, L (1 : Fin 8) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 8, (∑ k : Fin 8, L (2 : Fin 8) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 8, (∑ k : Fin 8, L (3 : Fin 8) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 8, (∑ k : Fin 8, L (4 : Fin 8) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 8, (∑ k : Fin 8, L (5 : Fin 8) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_6 : ∀ v : Fin 8, (∑ k : Fin 8, L (6 : Fin 8) k * diag k * L v k) = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_7 : ∀ v : Fin 8, (∑ k : Fin 8, L (7 : Fin 8) k * diag k * L v k) = M 7 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 8, ∀ v : Fin 8, (∑ k : Fin 8, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
  · exact ldl_checked_6
  · exact ldl_checked_7
lemma diag_checked : ∀ u : Fin 8, 0 ≤ diag u := by decide +kernel
lemma certificate_oai : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 15 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 15 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 15 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 15 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 15 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate15
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate15.certificate_oai := @OAI.LaughlinGap.RealOccupation.Certificate15.certificate_oai
