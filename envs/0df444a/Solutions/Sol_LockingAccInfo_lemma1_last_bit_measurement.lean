-- Prove2me | solution 1 for LockingAccInfo.lemma1_last_bit_measurement
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:58:50.393242+00:00
-- url     : https://prove2.me/submissions/141be2ea-0d90-42c7-92f6-775c4167b53e

import Mathlib
import Definitions.Def_LockingAccInfo_lockState
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
open QAlgorithms (IsPOVM effectProb)

namespace Aux_Locking_l1
open QMaxCutSDP.Rounding Matrix

lemma pauli_sq (a : Fin 3) (β γ : Fin 2) :
    ∑ δ : Fin 2, pauli a.succ β δ * pauli a.succ δ γ = if β = γ then 1 else 0 := by
  fin_cases a <;> fin_cases β <;> fin_cases γ <;> simp [pauli, Fin.sum_univ_two]

lemma pauli_herm (a : Fin 3) (β γ : Fin 2) : star (pauli a.succ γ β) = pauli a.succ β γ := by
  fin_cases a <;> fin_cases β <;> fin_cases γ <;> simp [pauli]

lemma pauli_trace (a : Fin 3) : ∑ β : Fin 2, pauli a.succ β β = 0 := by
  fin_cases a <;> simp [pauli, Fin.sum_univ_two]

lemma P_sq {m : ℕ} (y : Fin m → Fin 3) :
    pauliString (fun i => (y i).succ) * pauliString (fun i => (y i).succ) = 1 := by
  classical
  ext x z
  rw [Matrix.mul_apply]
  simp only [pauliString]
  rw [show (∑ w : Fin m → Fin 2, (∏ i, pauli (y i).succ (x i) (w i)) * ∏ i, pauli (y i).succ (w i) (z i))
      = ∑ w : Fin m → Fin 2, ∏ i, (pauli (y i).succ (x i) (w i) * pauli (y i).succ (w i) (z i)) by
    simp only [Finset.prod_mul_distrib]]
  rw [← Fintype.prod_sum (fun i δ => pauli (y i).succ (x i) δ * pauli (y i).succ δ (z i))]
  simp only [pauli_sq, Matrix.one_apply]
  by_cases hxz : x = z
  · subst hxz; simp
  · rw [if_neg hxz]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ z i := by
      by_contra h; push_neg at h; exact hxz (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma P_herm {m : ℕ} (y : Fin m → Fin 3) :
    (pauliString (fun i => (y i).succ)).IsHermitian := by
  ext x z
  simp only [conjTranspose_apply, pauliString, star_prod, pauli_herm]

lemma P_trace {m : ℕ} (hm : 1 ≤ m) (y : Fin m → Fin 3) :
    (pauliString (fun i => (y i).succ)).trace = 0 := by
  classical
  unfold trace
  simp only [diag_apply, pauliString]
  rw [← Fintype.prod_sum (fun i δ => pauli (y i).succ δ δ)]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hm⟩) (pauli_trace _)

end Aux_Locking_l1

open QMaxCutSDP.Rounding Matrix Aux_Locking_l1 ComplexOrder in
theorem solution (m : ℕ) (hm : 1 ≤ m) (y : Fin m → Fin 3) :
    ∃ M : Bool → Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ, IsPOVM M ∧
      ∀ x x' : Bool, effectProb (M x') (LockingAccInfo.lockState x y) = if x' = x then 1 else 0 := by
  classical
  set P := pauliString (fun i => (y i).succ) with hP
  let s : Bool → ℂ := fun b => if b then -1 else 1
  have hs2 : ∀ b, s b * s b = 1 := by intro b; cases b <;> simp [s]
  have hsstar : ∀ b, star (s b) = s b := by intro b; cases b <;> simp [s]
  refine ⟨fun b => (1 / 2 : ℂ) • (1 + s b • P), ⟨fun b => ?_, ?_⟩, fun x x' => ?_⟩
  · -- projector, hence PSD
    set Q := (1 / 2 : ℂ) • (1 + s b • P) with hQ
    have hQh : Qᴴ = Q := by
      rw [hQ, conjTranspose_smul, conjTranspose_add, conjTranspose_one, conjTranspose_smul,
        (P_herm y).eq, hsstar]
      congr 1
      simp
    have hPP : (s b • P) * (s b • P) = 1 := by
      rw [smul_mul_smul_comm, P_sq, hs2, one_smul]
    have hQ2 : Qᴴ * Q = Q := by
      rw [hQh, hQ, smul_mul_smul_comm, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hPP]
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    have := posSemidef_conjTranspose_mul_self Q
    rwa [hQ2] at this
  · simp only [Fintype.sum_bool, s, if_true, Bool.false_eq_true, if_false]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    ring
  · unfold effectProb LockingAccInfo.lockState
    rw [← hP]
    have hlock : (if x then (-1 : ℂ) else 1) = s x := rfl
    rw [hlock]
    have e : (1 / 2 : ℂ) • (1 + s x' • P) * (((2 : ℂ) ^ m)⁻¹ • (1 + s x • P))
        = ((1 / 2 : ℂ) * ((2 : ℂ) ^ m)⁻¹) • (1 + (s x' + s x) • P + (s x' * s x) • 1) := by
      rw [smul_mul_smul_comm, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, smul_mul_smul_comm, P_sq, add_smul]
      congr 1
      abel
    have h2 : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
    have htr : ((1 / 2 : ℂ) • (1 + s x' • P) * (((2 : ℂ) ^ m)⁻¹ • (1 + s x • P))).trace
        = if x' = x then 1 else 0 := by
      rw [e, trace_smul, trace_add, trace_add, trace_smul, trace_smul, P_trace hm, trace_one]
      simp only [Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_zero, add_zero]
      push_cast
      cases x <;> cases x' <;> simp [s] <;> field_simp <;> ring
    rw [htr]
    split_ifs <;> simp
