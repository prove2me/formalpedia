-- Prove2me | solution 1 for HorodeckiBoundKey.corner_trace_norm
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:29:59.422317+00:00
-- url     : https://prove2.me/submissions/4613b2d3-0c63-47ea-8e1f-176dcc940212

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42
import Definitions.Def_HorodeckiBoundKey_recurrenceOutput
import Definitions.Def_HorodeckiBoundKey_cornerNormValue

open QAlgorithms QAlgorithms.Papers.Independent
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P24 (keyBlock)

namespace CornerAux

open scoped MatrixOrder
open QAlgorithms.Papers.Independent.Dependency50.P24 (bipartiteCopies hidingOne hidingTwo
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

/-- Algebraic core: if `AB = BA = q B²` then `(A − B)² = (A + (1 − 2q) B)²`. -/
lemma sq_sub_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (q : ℂ)
    (hAB : A * B = q • (B * B)) (hBA : B * A = q • (B * B)) :
    (A - B) * (A - B) = (A + (1 - 2 * q) • B) * (A + (1 - 2 * q) • B) := by
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, hAB, hBA,
    smul_smul]
  module

/-- For `B ⪰ 0`, `√(B·B) = B`. -/
lemma cfc_sqrt_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℂ}
    (hB : B.PosSemidef) : cfc Real.sqrt (B * B) = B := by
  have hs : IsSelfAdjoint B := hB.1.isSelfAdjoint
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ B) := fun f =>
    (Matrix.finite_real_spectrum (A := B)).continuousOn f
  have h1 : B * B = cfc (fun x : ℝ => x * x) B := by
    rw [cfc_mul (fun x => x) (fun x => x) B (hfin _) (hfin _), cfc_id' ℝ B hs]
  rw [h1, ← cfc_comp Real.sqrt (fun x : ℝ => x * x) B hs
    ((Set.Finite.image _ (Matrix.finite_real_spectrum (A := B))).continuousOn _) (hfin _)]
  conv_rhs => rw [← cfc_id' ℝ B hs]
  exact cfc_congr fun x hx => Real.sqrt_mul_self (spectrum_nonneg_of_nonneg hB.nonneg hx)

lemma final_arith (p : ℝ) (l n : ℕ) (hp0 : 0 < p) (hp : p ≤ 1/2) :
    (HorodeckiBoundKey.recurrenceNorm p n)⁻¹ * (p/2)^n * (2 - 2 * (1/2)^l)^n =
      HorodeckiBoundKey.cornerNormValue p l n := by
  unfold HorodeckiBoundKey.recurrenceNorm HorodeckiBoundKey.cornerNormValue
  have h1 : (1 - 2*p)/(2*p) = (1/2 - p)/p := by field_simp
  have hpn : 0 < p^n := pow_pos hp0 n
  have hq : 0 ≤ (1/2 - p)^n := pow_nonneg (by linarith) n
  have e1 : (p/2)^n * (2 - 2*(1/2)^l)^n = p^n * (1 - 1/2^l)^n := by
    rw [← mul_pow, ← mul_pow, one_div_pow]; congr 1; ring
  rw [mul_assoc, e1, h1, div_pow]
  have hN : 0 < 2 * p ^ n + 2 * (1 / 2 - p) ^ n := by positivity
  field_simp

end CornerAux

open CornerAux in
open QAlgorithms.Papers.Independent.Dependency50.P24 (bipartiteCopies hidingOne hidingTwo) in
theorem solution (p : ℝ) (d l n : ℕ) (hd : 2 ≤ d) (hl : 1 ≤ l) (hn : 1 ≤ n)
    (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    traceNorm (keyBlock (HorodeckiBoundKey.recurrenceOutput p d l n) (0,0) (1,1)) =
      HorodeckiBoundKey.cornerNormValue p l n := by
  set N := HorodeckiBoundKey.recurrenceNorm p n with hN
  have hNpos : 0 < N := by
    have : 0 ≤ (1/2 - p) := by linarith
    have : 0 < p ^ n := pow_pos hp0 n
    simp only [hN, HorodeckiBoundKey.recurrenceNorm]
    positivity
  set κ : ℝ := N⁻¹ * (p/2)^n with hκ
  have hκ0 : 0 ≤ κ := by positivity
  -- the corner block is `κ · (τ₁ − τ₀)^{⊗n}`
  have hX : keyBlock (HorodeckiBoundKey.recurrenceOutput p d l n) (0,0) (1,1) =
      (κ : ℂ) • bipartiteCopies (hidingOne d l - hidingTwo d l) n := by
    have h01 : ((1 : Fin 2), (1 : Fin 2)) ≠ ((0 : Fin 2), (0 : Fin 2)) := by decide
    ext s t
    simp only [keyBlock, HorodeckiBoundKey.recurrenceOutput, h01, h01.symm, and_false,
      false_and, or_false, false_or, and_self, if_false, if_true, bc_smul, Matrix.smul_apply,
      smul_eq_mul, hκ]
    push_cast
    ring
  -- `|τ₁ − τ₀| = τ₁ + c τ₀` with `c = 1 − 2^{1−l}`
  set q : ℂ := (1/2 : ℂ) ^ l with hq
  set c : ℂ := 1 - 2 * q with hc
  have hc_real : c = ((1 - 2 * (1/2 : ℝ) ^ l : ℝ) : ℂ) := by simp [hc, hq]
  have hc0 : (0 : ℂ) ≤ c := by
    rw [hc_real]
    refine Complex.zero_le_real.mpr ?_
    have : (1/2 : ℝ) ^ l ≤ 1/2 := by
      calc (1/2 : ℝ) ^ l ≤ (1/2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hl
        _ = 1/2 := by norm_num
    linarith
  set E := hidingOne d l + c • hidingTwo d l with hE
  have hD : (hidingOne d l - hidingTwo d l)ᴴ = hidingOne d l - hidingTwo d l := by
    rw [Matrix.conjTranspose_sub, tau1_herm, tau0_herm]
  have hDD : (hidingOne d l - hidingTwo d l) * (hidingOne d l - hidingTwo d l) = E * E :=
    sq_sub_eq _ _ q (tau1_mul_tau0 l) (tau0_mul_tau1 l)
  have hEpsd : E.PosSemidef := (tau1_psd l hd).add ((tau0_psd l).smul hc0)
  set B := (κ : ℂ) • bipartiteCopies E n with hB
  have hBpsd : B.PosSemidef := (bc_psd hEpsd n).smul (Complex.zero_le_real.mpr hκ0)
  have hXX : (keyBlock (HorodeckiBoundKey.recurrenceOutput p d l n) (0,0) (1,1))ᴴ *
      keyBlock (HorodeckiBoundKey.recurrenceOutput p d l n) (0,0) (1,1) = B * B := by
    rw [hX, Matrix.conjTranspose_smul, bc_conjTranspose, hD, hB]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, bc_mul, hDD]
    congr 1
    simp
  unfold traceNorm
  rw [hXX, cfc_sqrt_mul_self hBpsd, hB, Matrix.trace_smul, bc_trace, hE, Matrix.trace_add,
    Matrix.trace_smul, tau1_trace l hd, tau0_trace l (by omega), hc_real]
  rw [← final_arith p l n hp0 hp]
  have : ((1 : ℂ) + ((1 - 2 * (1/2 : ℝ) ^ l : ℝ) : ℂ) • (1 : ℂ)) =
      ((2 - 2 * (1/2 : ℝ) ^ l : ℝ) : ℂ) := by
    simp only [smul_eq_mul, mul_one]; push_cast; ring
  rw [this, smul_eq_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, hκ]
