-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.Red.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:39:36.967035+00:00
-- url     : https://prove2.me/submissions/8c5defa0-b6e8-4304-8db5-61fb9ba4b852

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_add
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_neg
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_zero
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_mul_left
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_mul_right
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_eq_smul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_exists_pow_close
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_T_commuting_integral_matrix_topnil
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_mul
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_one
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_pow
import Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
namespace GlobalTheory.UnitDiscAlg.Red
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  intro E _ _ _ n N ϖ hN hB h0 _ hu y hyN hy
  have hred := GlobalTheory.T.commuting_integral_matrix_topnil E n N hN hB
  obtain ⟨a, b, hab, hsm⟩ := exists_pow_close y hy
  have hcy : Commute y N := hyN
  have step : ∀ k, a ≤ k → Sm (y ^ (k + (b - a)) - y ^ k) := by
    intro k hk
    have e1 : y ^ (k + (b - a)) - y ^ k = y ^ (k - a) * (y ^ b - y ^ a) := by
      rw [mul_sub, ← pow_add, ← pow_add]
      congr 2 <;> omega
    rw [e1]
    exact sm_mul_left (integ_pow hy _) hsm
  have per : ∀ k, a ≤ k → ∀ j, Sm (y ^ (k + j * (b - a)) - y ^ k) := by
    intro k hk j
    induction j with
    | zero => simpa using (sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E))
    | succ j ih =>
      have e2 : y ^ (k + (j + 1) * (b - a)) - y ^ k
          = (y ^ (k + j * (b - a) + (b - a)) - y ^ (k + j * (b - a)))
            + (y ^ (k + j * (b - a)) - y ^ k) := by
        rw [show k + (j + 1) * (b - a) = k + j * (b - a) + (b - a) by ring]
        abel
      rw [e2]
      exact sm_add (step _ (by omega)) ih
  set M := (b - a) * (a + 1) with hMdef
  have hpos : 1 ≤ b - a := by omega
  have hMa : a + 1 ≤ M := by
    rw [hMdef]; nlinarith
  have hidem : Sm (y ^ M * y ^ M - y ^ M) := by
    rw [← pow_add]
    have := per M (by omega) (a + 1)
    rwa [show M + (a + 1) * (b - a) = M + M by rw [hMdef]; ring] at this
  set x := y ^ M with hx
  have hxi : ∀ i j, ‖x i j‖ ≤ 1 := integ_pow hy M
  have hxN : Commute x N := hcy.pow_left M
  have hyx : Commute y x := (Commute.refl y).pow_right M
  have h1i : ∀ i j, ‖((1 : Matrix (Fin n) (Fin n) E) - x) i j‖ ≤ 1 := integ_sub integ_one hxi

  have hwM : Sm ((y * (1 - x)) ^ M) := by
    have hc : Commute y (1 - x) := (Commute.one_right y).sub_right hyx
    rw [hc.mul_pow, ← hx]
    obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    rw [hm, pow_succ', ← mul_assoc]
    apply sm_mul_right _ (integ_pow h1i m)
    have : x * (1 - x) = -(x * x - x) := by rw [mul_sub, mul_one]; abel
    rw [this]
    exact sm_neg hidem
  have hwN : Commute (y * (1 - x)) N := hcy.mul_left ((Commute.one_left N).sub_left hxN)
  have hw : Sm (y * (1 - x)) :=
    hred (y * (1 - x)) hwN.eq (integ_mul hy h1i) M hwM
  have hc1 : Commute (x * x - x) N := (hxN.mul_left hxN).sub_left hxN
  obtain ⟨a₁, ha₁N, ha₁i, ha₁⟩ := sm_eq_smul h0 hu hidem hc1.eq
  obtain ⟨a₂, ha₂N, ha₂i, ha₂⟩ := sm_eq_smul h0 hu hw hwN.eq
  have hyz : y * y ^ (M - 1) = x := by
    rw [hx, ← pow_succ']; congr 1; omega
  refine ⟨x, y ^ (M - 1), a₁, a₂, a₁, ⟨hxN.eq, (hcy.pow_left _).eq, ha₁N, ha₂N, ha₁N⟩,
    fun i j => ⟨hxi i j, integ_pow hy _ i j, ha₁i i j, ha₂i i j, ha₁i i j⟩, ha₁, ha₂, ?_⟩
  rw [hyz, ha₁]
end GlobalTheory.UnitDiscAlg.Red
