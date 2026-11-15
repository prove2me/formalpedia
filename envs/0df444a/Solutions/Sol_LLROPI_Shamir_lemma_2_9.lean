-- Prove2me | solution 1 for LLROPI.Shamir.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:13:57.929599+00:00
-- url     : https://prove2.me/submissions/78258d86-089e-44f0-8fb8-dab38ba29982

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

private lemma shift_sum {V : Type*} [AddCommGroup V] [Fintype V]
    (f : V → ℂ) (a : V) : (∑ x, f (x + a)) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight a) f

open Classical in
private lemma finite_cs {V : Type*} [AddCommGroup V] [Fintype V]
    (H : AddSubgroup V) (G P : V → ℂ)
    (hinv : ∀ x, ∀ h : H, G (x + h) = G x) (hbdd : ∀ x, ‖G x‖ ≤ 1) :
    let C : ℂ := ∑ x, ∑ h : H, P x * star (P (x + h))
    C.im = 0 ∧
      (Fintype.card H : ℝ) * ‖∑ x, G x * P x‖ ^ 2 ≤ (Fintype.card V : ℝ) * C.re := by
  classical
  let R : V → ℂ := fun x => ∑ h : H, P (x + h)
  let h : ℝ := Fintype.card H
  have hp : 0 < h := by dsimp [h]; exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty H from ⟨0⟩)
  have hcn : (Fintype.card H : ℂ) ≠ 0 := by
    have hn : (Fintype.card H : ℝ) ≠ 0 := hp.ne'
    exact_mod_cast hn
  have hR (x : V) (a : H) : R (x + a) = R x := by
    have he := Equiv.sum_comp (Equiv.addLeft a) (fun b : H => P (x + b))
    simpa [R, Equiv.addLeft, add_assoc] using he
  have avg (A : V → ℂ) (hi : ∀ x, ∀ a : H, A (x + a) = A x) :
      (∑ x, A x * R x) = (Fintype.card H : ℂ) * (∑ x, A x * P x) := by
    calc
      _ = ∑ a : H, ∑ x, A x * P (x + a) := by simp only [R, Finset.mul_sum]; rw [Finset.sum_comm]
      _ = ∑ a : H, ∑ x, A (x + a) * P (x + a) := by simp only [hi]
      _ = ∑ a : H, ∑ x, A x * P x := by
        apply Finset.sum_congr rfl
        intro a _
        exact shift_sum (fun x => A x * P x) a
      _ = _ := by simp [nsmul_eq_mul]
  have hGP := avg G hinv
  have henergy := avg (fun x => star (R x)) (fun x a => by rw [hR])
  let E : ℝ := ∑ x, ‖R x‖ ^ 2
  have hC : (∑ x, ∑ a : H, P x * star (P (x + a))) = (E : ℂ) / (Fintype.card H : ℂ) := by
    apply (eq_div_iff hcn).mpr
    calc
      _ = (Fintype.card H : ℂ) * ∑ x, star (R x) * P x := by
        simp only [R, star_sum, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = ∑ x, star (R x) * R x := henergy.symm
      _ = (E : ℂ) := by
        dsimp [E]
        push_cast
        apply Finset.sum_congr rfl
        intro x _
        simp [Complex.mul_conj, mul_comm, Complex.normSq_eq_norm_sq]
  have hn : ‖∑ x, G x * R x‖ ≤ ∑ x, ‖R x‖ := by
    calc
      _ ≤ ∑ x, ‖G x * R x‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hbdd x))
  have hsq : ‖∑ x, G x * R x‖ ^ 2 ≤ (Fintype.card V : ℝ) * E := by
    calc
      _ ≤ (∑ x, ‖R x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ _ := by simpa [E] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun x => ‖R x‖))
  have hnorm : ‖∑ x, G x * R x‖ ^ 2 = h ^ 2 * ‖∑ x, G x * P x‖ ^ 2 := by
    rw [hGP, norm_mul, mul_pow]
    simp [h, Complex.norm_natCast]
  dsimp only
  rw [hC]
  have hr : ((E : ℂ) / (Fintype.card H : ℂ)).re = E / h := by simp [h, Complex.div_ofReal_re]
  have hi : ((E : ℂ) / (Fintype.card H : ℂ)).im = 0 := by simp
  refine ⟨hi, ?_⟩
  rw [hr]
  rw [hnorm] at hsq
  have hout : h * ‖∑ x, G x * P x‖ ^ 2 ≤ ((Fintype.card V : ℝ) * E) / h :=
    (le_div_iff₀ hp).mpr (by nlinarith [hsq])
  simpa only [h, mul_div_assoc] using hout

open Classical in
theorem solution (p : ℕ) [Fact p.Prime] (k : ℕ) (G P : (Fin k → ZMod p) → ℂ)
    (K : Submodule (ZMod p) (Fin k → ZMod p))
    (hinv : ∀ x, ∀ h ∈ K, G (x + h) = G x) (hbdd : ∀ x, ‖G x‖ ≤ 1) :
    ((∑ x : Fin k → ZMod p, ∑ h ∈ Finset.univ.filter (fun h => h ∈ K), P x * star (P (x + h))) /
        ((p : ℂ) ^ k * ((Finset.univ.filter (fun h => h ∈ K)).card : ℂ))).im = 0 ∧
    ‖(∑ x : Fin k → ZMod p, G x * P x) / (p : ℂ) ^ k‖ ^ 2 ≤
      ((∑ x : Fin k → ZMod p, ∑ h ∈ Finset.univ.filter (fun h => h ∈ K), P x * star (P (x + h))) /
        ((p : ℂ) ^ k * ((Finset.univ.filter (fun h => h ∈ K)).card : ℂ))).re := by
  classical
  let V := Fin k → ZMod p
  let C : ℂ := ∑ x : V, ∑ h : K, P x * star (P (x + h))
  have h := finite_cs K.toAddSubgroup G P (fun x a => hinv x a a.property) hbdd
  change C.im = 0 ∧ _ at h
  have cardV : Fintype.card V = p ^ k := by simp [V, Fintype.card_fun]
  have cardH : Fintype.card K = (Finset.univ.filter (fun h : V => h ∈ K)).card := by
    exact Fintype.card_subtype (fun h : V => h ∈ K)
  have hp : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hh : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty K from ⟨0⟩)
  have hC : (∑ x : V, ∑ h ∈ Finset.univ.filter (fun h : V => h ∈ K), P x * star (P (x + h))) = C := by
    dsimp [C]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp only [Finset.subtype_univ]
    rfl
  have hden : ((p : ℂ) ^ k * (Fintype.card K : ℂ)) =
      ((((p : ℝ) ^ k * (Fintype.card K : ℝ)) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hre : (C / ((p : ℂ) ^ k * (Fintype.card K : ℂ))).re = C.re / ((p : ℝ) ^ k * (Fintype.card K : ℝ)) := by
    rw [hden, Complex.div_ofReal_re]
  have him : (C / ((p : ℂ) ^ k * (Fintype.card K : ℂ))).im = 0 := by
    rw [hden, Complex.div_ofReal_im, h.1, zero_div]
  rw [hC, ← cardH]
  refine ⟨him, ?_⟩
  rw [hre, norm_div, norm_pow, Complex.norm_natCast, div_pow]
  have hcard : Fintype.card K.toAddSubgroup = Fintype.card K := by
    exact Fintype.card_congr
      { toFun := fun a => ⟨a.1, a.2⟩
        invFun := fun a => ⟨a.1, a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [cardV, hcard] at h
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) (mul_pos hp hh)).mpr
  have hb : (Fintype.card K : ℝ) * ‖∑ x, G x * P x‖ ^ 2 ≤ (p : ℝ) ^ k * C.re := by
    convert h.2 using 1 <;> simp only [Nat.cast_pow] <;> rfl
  have he := mul_le_mul_of_nonneg_left hb hp.le
  nlinarith [he]

#print axioms solution





