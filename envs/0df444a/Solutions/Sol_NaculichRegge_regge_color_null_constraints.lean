-- Prove2me | solution 1 for NaculichRegge.regge_color_null_constraints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:14:15.405121+00:00
-- url     : https://prove2.me/submissions/191c1f44-e70a-45d1-8f49-846d1c829f22

import Definitions.Def_NaculichRegge_TraceBasis

namespace S216NR
open Polynomial NaculichRegge Matrix

lemma Tt2_mulVec (v : ColorVec) : Tt2 *ᵥ v = ![X * v 0 - v 5, C 2 * (X * v 1) + v 3 + v 5,
    X * v 2 - v 3, C 2 * v 1 + C 2 * (X * v 3), -(C 2 * v 0) - C 2 * v 2,
    C 2 * v 1 + C 2 * (X * v 5)] := by
  have h2 : (C 2 : ℂ[X]) = 2 := map_ofNat C 2
  ext1 i; fin_cases i <;> simp [h2, Tt2, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring

lemma Tsu2_mulVec (v : ColorVec) : Tsu2 *ᵥ v = ![-(C (1/2) * (X * v 0)) - v 4 - C (1/2) * v 5,
    -(C (1/2) * v 3) + C (1/2) * v 5, C (1/2) * (X * v 2) + C (1/2) * v 3 + v 4,
    v 1 + C 2 * v 2 + X * v 3, -v 0 + v 2, -(C 2 * v 0) - v 1 - X * v 5] := by
  have h2 : (C 2 : ℂ[X]) = 2 := map_ofNat C 2
  ext1 i; fin_cases i <;> simp [h2, Tsu2, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring

lemma coeff_Xm (p : ℂ[X]) (d : ℕ) : (X * p).coeff d = if d = 0 then 0 else p.coeff (d - 1) := by
  rcases d with _ | d <;> simp [coeff_X_mul]



def SupA (ℓ : ℕ) (v : ColorVec) : Prop := ∀ d, ¬ (d ≤ ℓ ∧ (d + ℓ) % 2 = 0) →
  (v 0).coeff d = 0 ∧ (v 1).coeff d = 0 ∧ (v 2).coeff d = 0

def SupB (ℓ : ℕ) (v : ColorVec) : Prop := ∀ d, ¬ (d + 1 ≤ ℓ ∧ (d + 1 + ℓ) % 2 = 0) →
  (v 3).coeff d = 0 ∧ (v 4).coeff d = 0 ∧ (v 5).coeff d = 0

def NCe (v : ColorVec) : Prop :=
  6 * ((v 0).coeff 2 + (v 1).coeff 2 + (v 2).coeff 2) - ((v 3).coeff 1 + (v 4).coeff 1 + (v 5).coeff 1) = 0 ∧
  (v 3).coeff 1 - 2 * (v 4).coeff 1 + (v 5).coeff 1 + (v 0).coeff 0 - 2 * (v 1).coeff 0 + (v 2).coeff 0 = 0 ∧
  (v 3).coeff 1 - (v 5).coeff 1 + (v 0).coeff 0 - (v 2).coeff 0 = 0 ∧
  (v 0).coeff 0 + (v 1).coeff 0 + (v 2).coeff 0 = 0

def NCo (v : ColorVec) : Prop :=
  6 * ((v 0).coeff 3 + (v 1).coeff 3 + (v 2).coeff 3) - ((v 3).coeff 2 + (v 4).coeff 2 + (v 5).coeff 2)
    + 2 * ((v 0).coeff 1 + (v 1).coeff 1 + (v 2).coeff 1) = 0 ∧
  6 * ((v 0).coeff 1 + (v 1).coeff 1 + (v 2).coeff 1) - ((v 3).coeff 0 + (v 4).coeff 0 + (v 5).coeff 0) = 0 ∧
  (v 3).coeff 0 - 2 * (v 4).coeff 0 + (v 5).coeff 0 = 0 ∧
  (v 3).coeff 0 - (v 5).coeff 0 = 0

def NC : ℕ → ColorVec → Prop
  | 0, v => (v 0).coeff 0 + (v 2).coeff 0 = 0
  | 1, v => (v 3).coeff 0 - (v 4).coeff 0 = 0 ∧ (v 4).coeff 0 - (v 5).coeff 0 = 0 ∧
      (v 3).coeff 0 - 2 * (v 0).coeff 1 - 2 * (v 2).coeff 1 = 0
  | n + 2, v => if n % 2 = 0 then NCe v else NCo v

def InS (ℓ : ℕ) (v : ColorVec) : Prop := SupA ℓ v ∧ SupB ℓ v ∧ (v 1).coeff ℓ = 0 ∧ NC ℓ v

lemma InS_sub {ℓ : ℕ} {v w : ColorVec} (hv : InS ℓ v) (hw : InS ℓ w) : InS ℓ (v - w) := by
  obtain ⟨hA, hB, hc, hN⟩ := hv
  obtain ⟨kA, kB, kc, kN⟩ := hw
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_⟩
  · obtain ⟨a0, a1, a2⟩ := hA d hd; obtain ⟨b0, b1, b2⟩ := kA d hd
    simp [a0, a1, a2, b0, b1, b2]
  · obtain ⟨a0, a1, a2⟩ := hB d hd; obtain ⟨b0, b1, b2⟩ := kB d hd
    simp [a0, a1, a2, b0, b1, b2]
  · simp [hc, kc]
  · rcases ℓ with _ | _ | n
    · simp only [NC, Pi.sub_apply, coeff_sub] at *; linear_combination hN - kN
    · simp only [NC, Pi.sub_apply, coeff_sub] at *
      obtain ⟨h1, h2, h3⟩ := hN; obtain ⟨k1, k2, k3⟩ := kN
      exact ⟨by linear_combination h1 - k1, by linear_combination h2 - k2,
        by linear_combination h3 - k3⟩
    · simp only [NC] at *
      split_ifs at * with hn
      · simp only [NCe, Pi.sub_apply, coeff_sub] at *
        obtain ⟨h1, h2, h3, h4⟩ := hN; obtain ⟨k1, k2, k3, k4⟩ := kN
        exact ⟨by linear_combination h1 - k1, by linear_combination h2 - k2,
          by linear_combination h3 - k3, by linear_combination h4 - k4⟩
      · simp only [NCo, Pi.sub_apply, coeff_sub] at *
        obtain ⟨h1, h2, h3, h4⟩ := hN; obtain ⟨k1, k2, k3, k4⟩ := kN
        exact ⟨by linear_combination h1 - k1, by linear_combination h2 - k2,
          by linear_combination h3 - k3, by linear_combination h4 - k4⟩

lemma NC_succ_even (n : ℕ) (hn : n % 2 = 0) (v : ColorVec) :
    NC (n + 2) v = NCe v ∧ NC (n + 1 + 2) v = NCo v := by
  simp only [NC, hn, if_true]; simp only [show ¬ ((n + 1) % 2 = 0) by omega, if_false]; simp

lemma NC_succ_odd (n : ℕ) (hn : n % 2 = 1) (v : ColorVec) :
    NC (n + 2) v = NCo v ∧ NC (n + 1 + 2) v = NCe v := by
  simp only [NC, show ¬ (n % 2 = 0) by omega, if_false]
  simp only [show (n + 1) % 2 = 0 by omega, if_true]; simp

lemma step_Tt (ℓ : ℕ) (v : ColorVec) (hv : InS ℓ v) : InS (ℓ + 1) (Tt2 *ᵥ v) := by
  obtain ⟨hA, hB, hc, hN⟩ := hv
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_⟩
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hB 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hA e (by omega); obtain ⟨b3, b4, b5⟩ := hB (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hA 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hB e (by omega); obtain ⟨b3, b4, b5⟩ := hA (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · obtain ⟨b3, b4, b5⟩ := hB (ℓ + 1) (by omega)
    simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b5, hc]
  · rcases ℓ with _ | _ | n
    · obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [z3, z5] at *
      exact ⟨by linear_combination 2 * hN + 2 * hc, by linear_combination -2 * hN - 2 * hc,
        by linear_combination -2 * hN + 2 * hc⟩
    · obtain ⟨y0, y1, y2⟩ := hA 0 (by omega); obtain ⟨x0, x1, x2⟩ := hA 2 (by omega)
      obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC, NCe] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [y0, y1, y2, x0, x1, x2, z3, z4, z5] at *
      obtain ⟨h0, h1, h2⟩ := hN
      exact ⟨by linear_combination 2 * h0 + 2 * h1 - 4 * h2 + 8 * hc,
        by linear_combination h0 + h1 - 2 * h2 + 4 * hc, by linear_combination 3 * h0 + 3 * h1,
        by linear_combination⟩
    · rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · rw [(NC_succ_even n hn _).1] at hN; rw [(NC_succ_even n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination 4/3 * h0 - 2/3 * h1 + 8/3 * h3, by linear_combination 8 * h3,
          by linear_combination 4 * h3, by linear_combination⟩
      · rw [(NC_succ_odd n hn _).1] at hN; rw [(NC_succ_odd n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination 4/3 * h1 - 2/3 * h2, by linear_combination 2/3 * h1 - 1/3 * h2,
          by linear_combination 3 * h3, by linear_combination⟩

lemma step_Ts (ℓ : ℕ) (v : ColorVec) (hv : InS ℓ v) : InS (ℓ + 1) (Tsu2 *ᵥ v) := by
  obtain ⟨hA, hB, hc, hN⟩ := hv
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_⟩
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hB 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hA e (by omega); obtain ⟨b3, b4, b5⟩ := hB (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hA 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hB e (by omega); obtain ⟨b3, b4, b5⟩ := hA (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · obtain ⟨b3, b4, b5⟩ := hB (ℓ + 1) (by omega)
    simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5, hc]
  · rcases ℓ with _ | _ | n
    · obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [z3, z5] at *
      exact ⟨by linear_combination hN + hc, by linear_combination hN + hc, by linear_combination hN + hc⟩
    · obtain ⟨y0, y1, y2⟩ := hA 0 (by omega); obtain ⟨x0, x1, x2⟩ := hA 2 (by omega)
      obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC, NCe] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [y0, y1, y2, x0, x1, x2, z3, z4, z5] at *
      obtain ⟨h0, h1, h2⟩ := hN
      exact ⟨by linear_combination -h0 - h1, by linear_combination 5/2 * h0 + 5/2 * h1, by linear_combination 3/2 * h0 - 1/2 * h1 - h2 + 2 * hc, by linear_combination⟩
    · rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · rw [(NC_succ_even n hn _).1] at hN; rw [(NC_succ_even n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination -h2, by linear_combination, by linear_combination, by linear_combination 2 * h3⟩
      · rw [(NC_succ_odd n hn _).1] at hN; rw [(NC_succ_odd n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination -h3, by linear_combination 5/2 * h3, by linear_combination 1/3 * h1 + 5/6 * h2, by linear_combination⟩

lemma step_X (ℓ : ℕ) (v : ColorVec) (hv : InS ℓ v) : InS (ℓ + 1) ((X : ℂ[X]) • v) := by
  obtain ⟨hA, hB, hc, hN⟩ := hv
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_⟩
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hB 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hA e (by omega); obtain ⟨b3, b4, b5⟩ := hB (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · rcases d with _ | e
    · obtain ⟨b3, b4, b5⟩ := hA 0 (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5]
    · obtain ⟨a0, a1, a2⟩ := hB e (by omega); obtain ⟨b3, b4, b5⟩ := hA (e + 1) (by omega)
      simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [a0, a1, a2, b3, b4, b5]
  · obtain ⟨b3, b4, b5⟩ := hB (ℓ + 1) (by omega)
    simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp [b3, b4, b5, hc]
  · rcases ℓ with _ | _ | n
    · obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [z3, z5] at *
      exact ⟨trivial, trivial, by linear_combination -2 * hN⟩
    · obtain ⟨y0, y1, y2⟩ := hA 0 (by omega); obtain ⟨x0, x1, x2⟩ := hA 2 (by omega)
      obtain ⟨z3, z4, z5⟩ := hB 1 (by omega)
      simp only [NC, NCe] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]; simp only [y0, y1, y2, x0, x1, x2, z3, z4, z5] at *
      obtain ⟨h0, h1, h2⟩ := hN
      exact ⟨by linear_combination 2 * h0 + h1 - 3 * h2 + 6 * hc, by linear_combination h0 - h1, by linear_combination h0 + h1, trivial⟩
    · rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · rw [(NC_succ_even n hn _).1] at hN; rw [(NC_succ_even n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination h0 + 2 * h3, by linear_combination 6 * h3, trivial, trivial⟩
      · rw [(NC_succ_odd n hn _).1] at hN; rw [(NC_succ_odd n hn _).2]
        simp only [NCe, NCo] at *; simp only [Tsu2_mulVec, Tt2_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val, coeff_add, coeff_sub, coeff_neg, coeff_C_mul, coeff_Xm, Nat.reduceEqDiff, Nat.reduceSub, OfNat.ofNat_ne_zero, one_ne_zero, ite_false, ite_true, mul_zero, add_zero, zero_add, sub_zero, zero_sub, neg_zero, Nat.add_one_sub_one, Nat.add_one_ne_zero]
        obtain ⟨h0, h1, h2, h3⟩ := hN
        exact ⟨by linear_combination h1, by linear_combination h2, by linear_combination h3, trivial⟩


def GoodOp (d : ℕ) (M : ColorOp) : Prop := ∀ ℓ v, InS ℓ v → InS (ℓ + d) (M *ᵥ v)

lemma good_mul {a b : ℕ} {A B : ColorOp} (hA : GoodOp a A) (hB : GoodOp b B) :
    GoodOp (b + a) (A * B) := by
  intro ℓ v hv; rw [← Matrix.mulVec_mulVec, ← add_assoc]; exact hA _ _ (hB _ _ hv)

lemma good_sub {d : ℕ} {A B : ColorOp} (hA : GoodOp d A) (hB : GoodOp d B) :
    GoodOp d (A - B) := by
  intro ℓ v hv; rw [Matrix.sub_mulVec]; exact InS_sub (hA _ _ hv) (hB _ _ hv)

lemma good_comm {a b : ℕ} {A B : ColorOp} (hA : GoodOp a A) (hB : GoodOp b B) :
    GoodOp (a + b) (NaculichRegge.comm A B) := by
  unfold NaculichRegge.comm
  apply good_sub
  · rw [add_comm]; exact good_mul hA hB
  · exact good_mul hB hA

lemma good_Tt : GoodOp 1 Tt2 := step_Tt
lemma good_Ts : GoodOp 1 Tsu2 := step_Ts

lemma good_one : GoodOp 0 1 := by intro ℓ v hv; simpa using hv

lemma good_pow (n : ℕ) : GoodOp n (Tsu2 ^ n) := by
  induction n with
  | zero => simpa using good_one
  | succ n ih => rw [pow_succ, add_comm]; exact good_mul ih good_Ts

lemma good_it1 (n : ℕ) : GoodOp (n + 1) ((NaculichRegge.comm Tt2)^[n] Tsu2) := by
  induction n with
  | zero => simpa using good_Ts
  | succ n ih =>
    rw [Function.iterate_succ_apply', show n + 1 + 1 = 1 + (n + 1) by ring]
    exact good_comm good_Tt ih

lemma good_it2 (n : ℕ) : GoodOp (n + 2) ((NaculichRegge.comm Tsu2)^[n] (NaculichRegge.comm Tt2 Tsu2)) := by
  induction n with
  | zero => simpa using good_comm good_Tt good_Ts
  | succ n ih =>
    rw [Function.iterate_succ_apply', show n + 1 + 2 = 1 + (n + 2) by ring]
    exact good_comm good_Ts ih

lemma good_regge (i k : ℕ) (h : IsReggeIndex i k) : GoodOp i (reggeOp i k) := by
  unfold reggeOp
  unfold IsReggeIndex at h
  split_ifs with h0 h1 h2 h3
  · subst h0; exact good_one
  · exact good_pow i
  · have := good_it1 (i - 1); rwa [Nat.sub_add_cancel (by omega)] at this
  · have := good_it2 (i - 2); rwa [Nat.sub_add_cancel (by omega)] at this
  · exfalso; omega

lemma C00_InS : InS 0 C00 := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, ?_, ?_⟩
  · have : d ≠ 0 := by omega
    simp [C00, coeff_one, this]
  · simp [C00]
  · simp [C00]
  · simp [NC, C00]

lemma Xpow_InS (n : ℕ) : InS n ((X : ℂ[X]) ^ n • C00) := by
  induction n with
  | zero => simpa using C00_InS
  | succ n ih => rw [pow_succ', mul_smul]; exact step_X _ _ ih

lemma regge_InS (ℓ i k : ℕ) (h : IsReggeIndex i k) (hi : i ≤ ℓ) :
    InS ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) := by
  unfold reggeColor
  rw [← Matrix.mulVec_smul]
  have := good_regge i k h (ℓ - i) _ (Xpow_InS (ℓ - i))
  rwa [Nat.sub_add_cancel hi] at this

lemma sum_split (f : ℕ → ℂ) (o L : ℕ) (h0 : ∀ lam, lam ≤ o → f lam = 0) :
    ∑ lam ∈ Finset.Icc 1 (o + L), f lam = ∑ j ∈ Finset.range L, f (o + j + 1) := by
  induction L with
  | zero => simp only [add_zero, Finset.range_zero, Finset.sum_empty]
            exact Finset.sum_eq_zero fun x hx => h0 x (Finset.mem_Icc.1 hx).2
  | succ L ih => rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma ec (ℓ m j : ℕ) (s : Fin 6) (dg : ℕ) (v : ColorVec) (hs : s.val = j % 6)
    (hd : dg = if j % 6 < 3 then ℓ - 2 * (m + j / 6) else ℓ - 2 * (m + j / 6) - 1)
    (hr : 6 * m + j + 1 ≤ 3 * ℓ + 3) : extCoord ℓ v (6 * m + j + 1) = (v s).coeff dg := by
  unfold extCoord extSlot extDegree
  rw [if_pos (by omega)]
  have h1 : (6 * m + j + 1 - 1) % 6 = j % 6 := by omega
  have h2 : (6 * m + j + 1 - 1) / 6 = m + j / 6 := by omega
  have hs' : (⟨(6 * m + j + 1 - 1) % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = s := by
    ext; simp only [h1, hs]
  rw [hs', h1, h2, hd]

lemma nv_even (m j : ℕ) (r : Fin 4) :
    nullVector (2 * m + 2) r (6 * m + j + 1) = (twoLoopNull r).getD j 0 := by
  unfold nullVector
  rw [if_pos ⟨m + 1, by ring⟩, if_neg (by omega)]
  congr 1; omega

lemma nv_odd (m j : ℕ) (r : Fin 4) :
    nullVector (2 * m + 1 + 2) r (6 * m + j + 1) = (threeLoopNull r).getD j 0 := by
  unfold nullVector
  rw [if_neg (Nat.not_even_iff_odd.mpr ⟨m + 1, by ring⟩), if_neg (by omega)]
  congr 1; omega


lemma final (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (v : ColorVec) (hv : InS ℓ v) :
    (∀ r : Fin 4, ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3), nullVector ℓ r lam * extCoord ℓ v lam = 0) ∧
      extCoord ℓ v 2 = 0 := by
  obtain ⟨hA, hB, hc, hN⟩ := hv
  refine ⟨fun r => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 2 := ⟨ℓ - 2, by omega⟩
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [(NC_succ_even (2 * m) (by omega) v).1] at hN
      obtain ⟨h0, h1, h2, h3⟩ := hN
      rw [show 3 * (2 * m + 2) + 3 = 6 * m + 9 by ring, sum_split _ (6 * m) 9 (fun lam hl => by
        rw [nullVector, if_pos ⟨m + 1, by ring⟩, if_pos (by omega), zero_mul])]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, nv_even]
      rw [ec _ m 0 0 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 1 1 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 2 2 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 3 3 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 4 4 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 5 5 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 6 0 0 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 7 1 0 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 8 2 0 v (by decide) (by split_ifs <;> omega) (by omega)]
      fin_cases r <;> simp [twoLoopNull]
      · linear_combination h0
      · linear_combination h1
      · linear_combination h2
      · linear_combination h3
    · rw [(NC_succ_odd (2 * m + 1) (by omega) v).1] at hN
      obtain ⟨h0, h1, h2, h3⟩ := hN
      rw [show 3 * (2 * m + 1 + 2) + 3 = 6 * m + 12 by ring, sum_split _ (6 * m) 12 (fun lam hl => by
        rw [nullVector, if_neg (Nat.not_even_iff_odd.mpr ⟨m + 1, by ring⟩), if_pos (by omega),
          zero_mul])]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, nv_odd]
      rw [ec _ m 0 0 3 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 1 1 3 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 2 2 3 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 3 3 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 4 4 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 5 5 2 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 6 0 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 7 1 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 8 2 1 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 9 3 0 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 10 4 0 v (by decide) (by split_ifs <;> omega) (by omega), ec _ m 11 5 0 v (by decide) (by split_ifs <;> omega) (by omega)]
      fin_cases r <;> simp [threeLoopNull]
      · linear_combination h0
      · linear_combination h1
      · linear_combination h2
      · linear_combination h3
  · simp [extCoord, extSlot, extDegree, hc]

end S216NR

open Polynomial NaculichRegge in
theorem solution (ℓ i k : ℕ) (hℓ : 2 ≤ ℓ) (h : IsReggeIndex i k) (hi : i ≤ ℓ) :
    (∀ r : Fin 4, ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3),
        nullVector ℓ r lam * extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) lam = 0) ∧
      extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) 2 = 0 :=
  S216NR.final ℓ hℓ _ (S216NR.regge_InS ℓ i k h hi)
