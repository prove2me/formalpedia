-- Prove2me | solution 1 for GlobalTheory.PMonE.exists_window_radii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:17:33.052127+00:00
-- url     : https://prove2.me/submissions/4a2ec94a-882a-417b-8687-157f11aed403

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWindowRadii

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
namespace _root_.GlobalTheory.PMonE
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp
end _root_.GlobalTheory.PMonE
end GlobalTheory.PMonE
