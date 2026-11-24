-- Prove2me | solution 1 for GlobalTheory.siegel_unip_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:45.142722+00:00
-- url     : https://prove2.me/submissions/5281215e-2847-4cc5-8db8-00264d3e7e52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SiegelUnipotentAntidiagonalCorner
import Theorems.Thm_GlobalTheory_SiegelUnip_adR_mul_dgC
import Theorems.Thm_GlobalTheory_SiegelUnip_adR_mul_adC
import Theorems.Thm_GlobalTheory_SiegelUnip_dbl_mul_dgC
import Theorems.Thm_GlobalTheory_SiegelUnip_dgC_tr_mul_dbl
import Theorems.Thm_GlobalTheory_SiegelUnip_dgC_tr_dbl_dgC
import Theorems.Thm_GlobalTheory_SiegelUnip_adR_tr
import Theorems.Thm_GlobalTheory_SiegelUnip_dgC_map
import Theorems.Thm_GlobalTheory_SiegelUnip_adR_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix GlobalTheory.SiegelUnip
namespace GlobalTheory
theorem _root_.solution : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  intro R₀ R _ _ _ _ c n J₀ x hx
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := dgC n R * x * adR n R with hN
  have hNN : N * N = 0 := by
    rw [hN, show dgC n R * x * adR n R * (dgC n R * x * adR n R) = dgC n R * x * (adR n R * dgC n R) * x * adR n R by
      simp only [Matrix.mul_assoc], adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
  have hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
  have hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hsq]; abel
  have hc2 : c (⅟(2 : R)) = ⅟(2 : R) := by
    refine (invOf_eq_right_inv ?_).symm
    have := congrArg c (mul_invOf_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at this
  have hNc : N.map c = dgC n R * x.map c * adR n R := by
    change (dgC n R * x * adR n R).map (c.toRingHom : R → R) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg₂ _ (congrArg₂ _ (dgC_map c) rfl) (adR_map c)
  have hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (dgC n R * x.map c * adR n R) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]
    congr 1
    ext i j
    simp [hc2]
  have hNt : Nᵀ = adC n R * xᵀ * (dgC n R)ᵀ := by
    rw [hN, transpose_mul, transpose_mul, adR_tr, Matrix.mul_assoc]
  have hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀ := by
    rw [hPc, transpose_add, transpose_one, transpose_smul, hNt]
    have e1 : dbl J₀ * (dgC n R * x.map c * adR n R) = adC n R * (J₀ * x.map c) * adR n R := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dbl_mul_dgC]; simp only [Matrix.mul_assoc]
    have e2 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ = adC n R * (xᵀ * J₀) * adR n R := by
      rw [Matrix.mul_assoc, dgC_tr_mul_dbl]; simp only [Matrix.mul_assoc]
    have e3 : adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) = 0 := by
      rw [show adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R) =
        adC n R * xᵀ * ((dgC n R)ᵀ * dbl J₀ * dgC n R) * x.map c * adR n R by simp only [Matrix.mul_assoc],
        dgC_tr_dbl_dgC]
      simp
    have e4 : adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]
    calc (1 + ⅟(2 : R) • (adC n R * xᵀ * (dgC n R)ᵀ)) * dbl J₀ * (1 + ⅟(2 : R) • (dgC n R * x.map c * adR n R))
        = dbl J₀ + ⅟(2 : R) • (dbl J₀ * (dgC n R * x.map c * adR n R)) +
          ⅟(2 : R) • (adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀) +
          (⅟(2 : R) * ⅟(2 : R)) • (adC n R * xᵀ * (dgC n R)ᵀ * dbl J₀ * (dgC n R * x.map c * adR n R)) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; abel
      _ = dbl J₀ + ⅟(2 : R) • (adC n R * (J₀ * x.map c) * adR n R + adC n R * (xᵀ * J₀) * adR n R) := by
          rw [e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]
      _ = dbl J₀ := by rw [e4, smul_zero, add_zero]
  let u : GL (Fin n ⊕ Fin n) R := ⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩
  refine ⟨⟨u, hmem⟩, ?_, fun h => ?_⟩
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have hpd : N * dgC n R = 0 := by rw [hN, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]
    have key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * dgC n R =
        dgC n R * (1 : Matrix (Fin n) (Fin n) R) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]
    exact key
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have e : adR n R * (h * N) * adC n R = (2 : R) • (adR n R * h * dgC n R * x) := by
      rw [hN, show adR n R * (h * (dgC n R * x * adR n R)) * adC n R = adR n R * h * dgC n R * x * (adR n R * adC n R) by
        simp only [Matrix.mul_assoc], adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]
    rw [mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul,
      invOf_mul_self, one_smul, Matrix.mul_assoc (adR n R) h]
    rfl
end GlobalTheory
