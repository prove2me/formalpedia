-- Prove2me | solution 1 for HorodeckiBoundKey.recurrence_output
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:36:53.830201+00:00
-- url     : https://prove2.me/submissions/7b12d43e-54f9-44bb-a27c-fa4711998f73

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_keyPower
import Definitions.Def_HorodeckiBoundKey_localPair
import Definitions.Def_HorodeckiBoundKey_repetitionDecoder
import Definitions.Def_HorodeckiBoundKey_recurrenceNorm
import Definitions.Def_HorodeckiBoundKey_recurrenceOutput

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (hidingFamily)

namespace RecurrenceAux

open scoped MatrixOrder
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key bipartiteCopies hidingOne hidingTwo
  symmetricWerner antisymmetricWerner)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section BC
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Sums over `n`-tuples of pairs factor through `Fin n → I × J`. -/
lemma sum_pairs_prod (n : ℕ) (f : Fin n → I × J → ℂ) :
    ∑ z : (Fin n → I) × (Fin n → J), ∏ t, f t (z.1 t, z.2 t) = ∏ t, ∑ w, f t w := by
  rw [Fintype.prod_sum]
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => I) (fun _ => J)).symm
    _ _ (fun z => rfl))

lemma bc_mul (A B : Op (I × J)) (n : ℕ) :
    bipartiteCopies A n * bipartiteCopies B n = bipartiteCopies (A * B) n := by
  ext x y
  simp only [Matrix.mul_apply, bipartiteCopies]
  simp_rw [← Finset.prod_mul_distrib]
  exact sum_pairs_prod n (fun t w => A (x.1 t, x.2 t) w * B w (y.1 t, y.2 t))

lemma bc_trace (A : Op (I × J)) (n : ℕ) :
    (bipartiteCopies A n).trace = A.trace ^ n := by
  simp only [Matrix.trace, Matrix.diag, bipartiteCopies]
  rw [sum_pairs_prod n (fun _ w => A w w), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma bc_conjTranspose (A : Op (I × J)) (n : ℕ) :
    (bipartiteCopies A n)ᴴ = bipartiteCopies Aᴴ n := by
  ext x y
  simp only [Matrix.conjTranspose_apply, bipartiteCopies]
  rw [show star (∏ t, A (y.1 t, y.2 t) (x.1 t, x.2 t)) =
      (starRingEnd ℂ) (∏ t, A (y.1 t, y.2 t) (x.1 t, x.2 t)) from rfl, map_prod]
  rfl

lemma bc_smul (c : ℂ) (A : Op (I × J)) (n : ℕ) :
    bipartiteCopies (c • A) n = (c ^ n) • bipartiteCopies A n := by
  ext x y
  simp only [bipartiteCopies, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable [DecidableEq I] [DecidableEq J]

lemma bc_psd {A : Op (I × J)} (hA : A.PosSemidef) (n : ℕ) :
    (bipartiteCopies A n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, Matrix.star_eq_conjTranspose, ← bc_mul, ← bc_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end BC

section Werner
variable {d : ℕ}

lemma swap_mul_swap : (swapMatrix (I := Fin d)) * swapMatrix = 1 := by
  ext x y
  simp only [Matrix.mul_apply, swapMatrix, Matrix.one_apply]
  rw [Finset.sum_eq_single (x.2, x.1)]
  · by_cases h : x = y
    · subst h; simp
    · simp only [and_self, if_true, one_mul, h, if_false]
      split_ifs with h1
      · exact absurd (Prod.ext h1.2.symm h1.1.symm) (by simpa [eq_comm] using h) 
      · rfl
  · intro z _ hz
    split_ifs with h1 h2
    · exact absurd (Prod.ext h1.2.symm h1.1.symm) hz
    · simp
    · simp
    · simp
  · simp

lemma swap_conjTranspose : (swapMatrix (I := Fin d))ᴴ = swapMatrix := by
  ext x y
  simp only [Matrix.conjTranspose_apply, swapMatrix]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd ⟨h1.2.symm, h1.1.symm⟩ h2
  · exact absurd ⟨h2.2.symm, h2.1.symm⟩ h1
  · simp

lemma swap_trace : (swapMatrix (I := Fin d)).trace = d := by
  simp only [Matrix.trace, Matrix.diag, swapMatrix, Fintype.sum_prod_type]
  have : ∀ x : Fin d, (∑ y : Fin d, if x = y ∧ y = x then (1:ℂ) else 0) = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  rw [Finset.sum_congr rfl (fun x _ => this x)]
  simp

lemma one_trace : (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ).trace = (d : ℂ) ^ 2 := by
  simp [Matrix.trace_one, sq]


lemma sub_mul_add_swap : (1 - swapMatrix (I := Fin d)) * (1 + swapMatrix) = 0 := by
  rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, swap_mul_swap]; abel

lemma add_mul_sub_swap : (1 + swapMatrix (I := Fin d)) * (1 - swapMatrix) = 0 := by
  rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, swap_mul_swap]; abel

lemma anti_mul_sym : antisymmetricWerner d * symmetricWerner d = 0 := by
  rw [antisymmetricWerner, symmetricWerner, Matrix.smul_mul, Matrix.mul_smul, sub_mul_add_swap,
    smul_zero, smul_zero]

lemma sym_mul_anti : symmetricWerner d * antisymmetricWerner d = 0 := by
  rw [antisymmetricWerner, symmetricWerner, Matrix.smul_mul, Matrix.mul_smul, add_mul_sub_swap,
    smul_zero, smul_zero]

lemma sym_herm : (symmetricWerner d)ᴴ = symmetricWerner d := by
  simp [symmetricWerner, Matrix.conjTranspose_smul, swap_conjTranspose]

lemma anti_herm : (antisymmetricWerner d)ᴴ = antisymmetricWerner d := by
  simp [antisymmetricWerner, Matrix.conjTranspose_smul, swap_conjTranspose]

lemma sym_trace (hd : 1 ≤ d) : (symmetricWerner d).trace = 1 := by
  simp only [symmetricWerner, Matrix.trace_smul, Matrix.trace_add, swap_trace, one_trace,
    smul_eq_mul]
  have : ((d : ℂ) ^ 2 + d) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) ^ 2 + d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      positivity
    exact_mod_cast this.ne'
  field_simp

lemma anti_trace (hd : 2 ≤ d) : (antisymmetricWerner d).trace = 1 := by
  simp only [antisymmetricWerner, Matrix.trace_smul, Matrix.trace_sub, swap_trace, one_trace,
    smul_eq_mul]
  have : ((d : ℂ) ^ 2 - d) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) ^ 2 - d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    exact_mod_cast this.ne'
  rw [inv_mul_cancel₀ this]

lemma one_add_swap_psd : (1 + swapMatrix (I := Fin d)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 + swapMatrix (I := Fin d))
  have e : (1 + swapMatrix (I := Fin d))ᴴ * (1 + swapMatrix (I := Fin d)) =
      (2 : ℂ) • (1 + swapMatrix (I := Fin d)) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, swap_conjTranspose]
    simp only [mul_add, add_mul, one_mul, mul_one, swap_mul_swap]
    rw [two_smul]; abel
  rw [e] at h
  have := h.smul (a := ((1/2 : ℝ) : ℂ)) (Complex.zero_le_real.mpr (by norm_num))
  rwa [smul_smul, show ((1/2 : ℝ) : ℂ) * 2 = 1 by push_cast; norm_num, one_smul] at this

lemma one_sub_swap_psd : (1 - swapMatrix (I := Fin d)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - swapMatrix (I := Fin d))
  have e : (1 - swapMatrix (I := Fin d))ᴴ * (1 - swapMatrix (I := Fin d)) =
      (2 : ℂ) • (1 - swapMatrix (I := Fin d)) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, swap_conjTranspose]
    simp only [mul_sub, sub_mul, one_mul, mul_one, swap_mul_swap]
    rw [two_smul]; abel
  rw [e] at h
  have := h.smul (a := ((1/2 : ℝ) : ℂ)) (Complex.zero_le_real.mpr (by norm_num))
  rwa [smul_smul, show ((1/2 : ℝ) : ℂ) * 2 = 1 by push_cast; norm_num, one_smul] at this

lemma sym_psd : (symmetricWerner d).PosSemidef := by
  unfold symmetricWerner
  have : ((d : ℂ) ^ 2 + d)⁻¹ = (((d : ℝ) ^ 2 + d)⁻¹ : ℝ) := by push_cast; rfl
  rw [this]
  exact one_add_swap_psd.smul (Complex.zero_le_real.mpr (by positivity))

lemma anti_psd (hd : 2 ≤ d) : (antisymmetricWerner d).PosSemidef := by
  unfold antisymmetricWerner
  have : ((d : ℂ) ^ 2 - d)⁻¹ = (((d : ℝ) ^ 2 - d)⁻¹ : ℝ) := by push_cast; rfl
  rw [this]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact one_sub_swap_psd.smul (Complex.zero_le_real.mpr (inv_nonneg.mpr (by nlinarith)))

end Werner

section Hiding

variable {d : ℕ}

/-- The single-copy state `(ϱ_s + ϱ_a)/2` of `τ₁`. -/
lemma half_mul_sym :
    ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) * symmetricWerner d =
      (1/2 : ℂ) • (symmetricWerner d * symmetricWerner d) := by
  rw [Matrix.smul_mul, add_mul, anti_mul_sym, add_zero]

lemma sym_mul_half :
    symmetricWerner d * ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)) =
      (1/2 : ℂ) • (symmetricWerner d * symmetricWerner d) := by
  rw [Matrix.mul_smul, mul_add, sym_mul_anti, add_zero]

lemma half_herm :
    ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d))ᴴ =
      (1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, sym_herm, anti_herm]
  congr 1
  simp

lemma half_trace (hd : 2 ≤ d) :
    ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)).trace = 1 := by
  rw [Matrix.trace_smul, Matrix.trace_add, sym_trace (by omega), anti_trace hd]
  norm_num

lemma half_psd (hd : 2 ≤ d) :
    ((1/2 : ℂ) • (symmetricWerner d + antisymmetricWerner d)).PosSemidef := by
  have : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact (sym_psd.add (anti_psd hd)).smul (Complex.zero_le_real.mpr (by norm_num))

variable (l : ℕ)

lemma tau1_mul_tau0 : hidingOne d l * hidingTwo d l =
    ((1/2 : ℂ) ^ l) • (hidingTwo d l * hidingTwo d l) := by
  unfold hidingOne hidingTwo
  rw [bc_mul, half_mul_sym, bc_smul, bc_mul]

lemma tau0_mul_tau1 : hidingTwo d l * hidingOne d l =
    ((1/2 : ℂ) ^ l) • (hidingTwo d l * hidingTwo d l) := by
  unfold hidingOne hidingTwo
  rw [bc_mul, sym_mul_half, bc_smul, bc_mul]

lemma tau1_herm : (hidingOne d l)ᴴ = hidingOne d l := by
  unfold hidingOne; rw [bc_conjTranspose, half_herm]

lemma tau0_herm : (hidingTwo d l)ᴴ = hidingTwo d l := by
  unfold hidingTwo; rw [bc_conjTranspose, sym_herm]

lemma tau1_trace (hd : 2 ≤ d) : (hidingOne d l).trace = 1 := by
  unfold hidingOne; rw [bc_trace, half_trace hd, one_pow]

lemma tau0_trace (hd : 1 ≤ d) : (hidingTwo d l).trace = 1 := by
  unfold hidingTwo; rw [bc_trace, sym_trace hd, one_pow]

lemma tau1_psd (hd : 2 ≤ d) : (hidingOne d l).PosSemidef := by
  unfold hidingOne; exact bc_psd (half_psd hd) l

lemma tau0_psd : (hidingTwo d l).PosSemidef := by
  unfold hidingTwo; exact bc_psd sym_psd l

end Hiding

section KeyPower

variable {S T : Type*} [Fintype S] [Fintype T]

/-- Sums over `n` copies of `Key 2 × (S × T)` factor. -/
lemma sum_triples_prod (n : ℕ) (f : Fin n → Key 2 × (S × T) → ℂ) :
    ∑ z : (Fin n → Key 2) × ((Fin n → S) × (Fin n → T)),
      ∏ t, f t (z.1 t, (z.2.1 t, z.2.2 t)) = ∏ t, ∑ w, f t w := by
  rw [Fintype.prod_sum]
  let e : (Fin n → Key 2 × (S × T)) ≃ (Fin n → Key 2) × ((Fin n → S) × (Fin n → T)) :=
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Key 2) (fun _ => S × T)).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => S) (fun _ => T)))
  exact (Fintype.sum_equiv e.symm _ _ (fun z => rfl))

lemma kp_mul (A B : Op (Key 2 × (S × T))) (n : ℕ) :
    HorodeckiBoundKey.keyPower A n * HorodeckiBoundKey.keyPower B n =
      HorodeckiBoundKey.keyPower (A * B) n := by
  ext x y
  simp only [Matrix.mul_apply, HorodeckiBoundKey.keyPower]
  simp_rw [← Finset.prod_mul_distrib]
  exact sum_triples_prod n
    (fun t w => A (x.1 t, (x.2.1 t, x.2.2 t)) w * B w (y.1 t, (y.2.1 t, y.2.2 t)))

lemma kp_conjTranspose (A : Op (Key 2 × (S × T))) (n : ℕ) :
    (HorodeckiBoundKey.keyPower A n)ᴴ = HorodeckiBoundKey.keyPower Aᴴ n := by
  ext x y
  simp only [Matrix.conjTranspose_apply, HorodeckiBoundKey.keyPower]
  rw [show star (∏ t, A (y.1 t, (y.2.1 t, y.2.2 t)) (x.1 t, (x.2.1 t, x.2.2 t))) =
      (starRingEnd ℂ) (∏ t, A (y.1 t, (y.2.1 t, y.2.2 t)) (x.1 t, (x.2.1 t, x.2.2 t))) from rfl,
    map_prod]
  rfl

variable [DecidableEq S] [DecidableEq T]

lemma kp_psd {A : Op (Key 2 × (S × T))} (hA : A.PosSemidef) (n : ℕ) :
    (HorodeckiBoundKey.keyPower A n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB, Matrix.star_eq_conjTranspose, ← kp_mul, ← kp_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end KeyPower

section Decoder

variable {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ}

/-- `(J† ⊗ J† ⊗ 1)` is the 0/1 matrix selecting `x = (a.1, …, a.1; shields a.2)`. -/
lemma localPair_apply (a : Key 2 × ((Fin n → S) × (Fin n → S)))
    (x : (Fin n → Key 2) × ((Fin n → S) × (Fin n → S))) :
    HorodeckiBoundKey.localPair (HorodeckiBoundKey.repetitionDecoder n S)
        (HorodeckiBoundKey.repetitionDecoder n S) a x =
      if ((fun _ => a.1, a.2) : (Fin n → Key 2) × ((Fin n → S) × (Fin n → S))) = x
      then 1 else 0 := by
  simp only [HorodeckiBoundKey.localPair, HorodeckiBoundKey.repetitionDecoder]
  by_cases hx : ((fun _ => a.1, a.2) : (Fin n → Key 2) × ((Fin n → S) × (Fin n → S))) = x
  · subst hx; simp
  · rw [if_neg hx]
    by_cases h1 : (∀ i, (x.1 i).1 = a.1.1) ∧ x.2.1 = a.2.1
    · by_cases h2 : (∀ i, (x.1 i).2 = a.1.2) ∧ x.2.2 = a.2.2
      · exfalso; apply hx
        refine Prod.ext (funext fun i => Prod.ext (h1.1 i).symm (h2.1 i).symm)
          (Prod.ext h1.2.symm h2.2.symm)
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma decode_apply (K : Matrix ((Fin n → Key 2) × ((Fin n → S) × (Fin n → S)))
      ((Fin n → Key 2) × ((Fin n → S) × (Fin n → S))) ℂ)
    (a b : Key 2 × ((Fin n → S) × (Fin n → S))) :
    (HorodeckiBoundKey.localPair (HorodeckiBoundKey.repetitionDecoder n S)
        (HorodeckiBoundKey.repetitionDecoder n S) * K *
      (HorodeckiBoundKey.localPair (HorodeckiBoundKey.repetitionDecoder n S)
        (HorodeckiBoundKey.repetitionDecoder n S))ᴴ) a b =
      K (fun _ => a.1, a.2) (fun _ => b.1, b.2) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, localPair_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [apply_ite (star : ℂ → ℂ), star_one, star_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Decoder

section Family

variable {d l : ℕ}

/-- `|Φ⁺⟩` direction (unnormalised `e₀₀ + e₁₁`) as a row. -/
def Bplus : Matrix Unit (Key 2) ℂ := fun _ b => if b = (0,0) ∨ b = (1,1) then 1 else 0

/-- `|Φ⁻⟩` direction (unnormalised `e₀₀ − e₁₁`) as a row. -/
def Bminus : Matrix Unit (Key 2) ℂ :=
  fun _ b => if b = (0,0) then 1 else if b = (1,1) then -1 else 0

/-- Projector onto `span{e₀₁, e₁₀}`. -/
def Dodd : Matrix (Key 2) (Key 2) ℂ :=
  Matrix.diagonal (fun k => if k = (0,1) ∨ k = (1,0) then 1 else 0)

lemma family_decomp (p : ℝ) :
    hidingFamily p d l =
      ((p/2 : ℝ) : ℂ) • (Matrix.kronecker (Bplusᴴ * Bplus) (hidingOne d l) +
        Matrix.kronecker (Bminusᴴ * Bminus) (hidingTwo d l)) +
      ((1/2 - p : ℝ) : ℂ) • Matrix.kronecker Dodd (hidingTwo d l) := by
  ext ⟨⟨i, j⟩, s⟩ ⟨⟨i', j'⟩, s'⟩
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [hidingFamily, Matrix.kronecker, Matrix.kroneckerMap_apply, Bplus, Bminus, Dodd,
      Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

lemma Dodd_psd : Dodd.PosSemidef := by
  refine Matrix.PosSemidef.diagonal (fun k => ?_)
  show (0:ℂ) ≤ if k = (0,1) ∨ k = (1,0) then 1 else 0
  split_ifs <;> norm_num

lemma family_psd (p : ℝ) (hd : 2 ≤ d) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    (hidingFamily p d l).PosSemidef := by
  rw [family_decomp]
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.smul (Matrix.PosSemidef.add
    ((Matrix.posSemidef_conjTranspose_mul_self _).kronecker (tau1_psd l hd))
    ((Matrix.posSemidef_conjTranspose_mul_self _).kronecker (tau0_psd l)))
    (Complex.zero_le_real.mpr (by linarith)))
    (Matrix.PosSemidef.smul (Dodd_psd.kronecker (tau0_psd l))
    (Complex.zero_le_real.mpr (by linarith)))

end Family

end RecurrenceAux

open RecurrenceAux in
open QAlgorithms.Papers.Independent.Dependency50.P24 (bipartiteCopies hidingOne hidingTwo) in
open HorodeckiBoundKey in
theorem solution (p : ℝ) (d l n : ℕ) (hd : 2 ≤ d) (hl : 1 ≤ l) (hn : 1 ≤ n)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    localPair (repetitionDecoder n (Fin l → Fin d)) (repetitionDecoder n (Fin l → Fin d)) *
        keyPower (hidingFamily p d l) n *
        (localPair (repetitionDecoder n (Fin l → Fin d))
          (repetitionDecoder n (Fin l → Fin d)))ᴴ =
      ((recurrenceNorm p n : ℝ) : ℂ) • recurrenceOutput p d l n ∧
    0 < recurrenceNorm p n ∧ IsDensityMatrix (recurrenceOutput p d l n) := by
  have hn0 : n ≠ 0 := by omega
  have hNpos : 0 < recurrenceNorm p n := by
    unfold recurrenceNorm
    rcases eq_or_lt_of_le hp0 with h | h
    · subst h
      have : (0:ℝ) < (1/2 - 0) ^ n := by positivity
      rw [zero_pow hn0]
      linarith
    · have : 0 < p ^ n := pow_pos h n
      have : 0 ≤ (1/2 - p) ^ n := pow_nonneg (by linarith) n
      linarith
  have hNne : ((recurrenceNorm p n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hEq : localPair (repetitionDecoder n (Fin l → Fin d)) (repetitionDecoder n (Fin l → Fin d)) *
        keyPower (hidingFamily p d l) n *
        (localPair (repetitionDecoder n (Fin l → Fin d))
          (repetitionDecoder n (Fin l → Fin d)))ᴴ =
      ((recurrenceNorm p n : ℝ) : ℂ) • recurrenceOutput p d l n := by
    ext ⟨k, s⟩ ⟨k', s'⟩
    rw [decode_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [keyPower, hidingFamily, recurrenceOutput]
    rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
    simp only [bipartiteCopies, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul]
    by_cases h1 : (k = (0,0) ∧ k' = (0,0)) ∨ (k = (1,1) ∧ k' = (1,1))
    · simp only [h1, if_true]
      refine Finset.prod_congr rfl fun i _ => ?_
      ring
    · by_cases h2 : (k = (0,0) ∧ k' = (1,1)) ∨ (k = (1,1) ∧ k' = (0,0))
      · simp only [h1, h2, if_true, if_false]
      · by_cases h3 : (k = (0,1) ∧ k' = (0,1)) ∨ (k = (1,0) ∧ k' = (1,0))
        · simp only [h1, h2, h3, if_true, if_false]
        · simp only [h1, h2, h3, if_false]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_pow hn0]
  refine ⟨hEq, hNpos, ?_, ?_⟩
  · -- positivity: `ρ′ = N⁻¹ (J†⊗J†⊗1) ρ^{⊗n} (J⊗J⊗1)`
    have hR : recurrenceOutput p d l n = (((recurrenceNorm p n)⁻¹ : ℝ) : ℂ) •
        (localPair (repetitionDecoder n (Fin l → Fin d)) (repetitionDecoder n (Fin l → Fin d)) *
          keyPower (hidingFamily p d l) n *
          (localPair (repetitionDecoder n (Fin l → Fin d))
            (repetitionDecoder n (Fin l → Fin d)))ᴴ) := by
      rw [hEq, smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hNne, one_smul]
    rw [hR]
    exact ((kp_psd (family_psd p hd hp0 hp) n).mul_mul_conjTranspose_same _).smul
      (Complex.zero_le_real.mpr (inv_nonneg.mpr hNpos.le))
  · -- trace one
    have hblock : ∀ (k : Fin 2 × Fin 2) (M : Op ((Fin l → Fin d) × (Fin l → Fin d))),
        (∀ sh sh', recurrenceOutput p d l n (k, sh) (k, sh') =
          ((recurrenceNorm p n : ℝ) : ℂ)⁻¹ * bipartiteCopies M n sh sh') →
        (∑ sh, recurrenceOutput p d l n (k, sh) (k, sh)) =
          ((recurrenceNorm p n : ℝ) : ℂ)⁻¹ * M.trace ^ n := by
      intro k M hM
      simp only [hM, ← Finset.mul_sum]
      rw [← bc_trace]
      rfl
    have h00 := hblock (0,0) (((p/2 : ℝ) : ℂ) • (hidingTwo d l + hidingOne d l))
      (fun sh sh' => by simp [recurrenceOutput])
    have h11 := hblock (1,1) (((p/2 : ℝ) : ℂ) • (hidingTwo d l + hidingOne d l))
      (fun sh sh' => by simp [recurrenceOutput])
    have h01 := hblock (0,1) (((1/2 - p : ℝ) : ℂ) • hidingTwo d l)
      (fun sh sh' => by simp [recurrenceOutput])
    have h10 := hblock (1,0) (((1/2 - p : ℝ) : ℂ) • hidingTwo d l)
      (fun sh sh' => by simp [recurrenceOutput])
    rw [Matrix.trace]
    simp only [Matrix.diag]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two, h00, h01, h10, h11]
    simp only [Matrix.trace_smul, Matrix.trace_add, tau0_trace l (by omega : 1 ≤ d),
      tau1_trace l hd, smul_eq_mul]
    conv_rhs => rw [← inv_mul_cancel₀ hNne]
    unfold recurrenceNorm
    push_cast
    ring
