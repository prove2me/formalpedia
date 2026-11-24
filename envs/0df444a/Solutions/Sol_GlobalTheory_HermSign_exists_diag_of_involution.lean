-- Prove2me | solution 1 for GlobalTheory.HermSign.exists_diag_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:47:13.088108+00:00
-- url     : https://prove2.me/submissions/24b70585-f9cb-47fa-978e-fdf662b9b468

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_exists_perm_sgn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {r m n : ℕ} (hr : r = m + n) (G K : Matrix (Fin r) (Fin r) ℂ)
    (hG : G.IsHermitian) (hK : K * K = 1) (hB : (K * G).PosDef) (ht : K.trace = (m : ℂ) - n) :
    ∃ N : Matrix (Fin r) (Fin r) ℂ, N.det ≠ 0 ∧
      Nᴴ * G * N = diagonal fun a : Fin r => ((FD.sgn m (a : ℕ) : ℝ) : ℂ) := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hP
  have hPd : IsUnit P.det := by
    have := hB.det_pos.ne'
    rw [hP, det_mul] at this
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul this)
  have hPi : P * P⁻¹ = 1 := mul_nonsing_inv _ hPd
  have hPi' : P⁻¹ * P = 1 := nonsing_inv_mul _ hPd
  have hPh : Pᴴ * P⁻¹ᴴ = 1 := by rw [← conjTranspose_mul, hPi', conjTranspose_one]
  have hPh' : P⁻¹ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
  set T := P⁻¹ᴴ * G * P⁻¹ with hT
  have hTh : T.IsHermitian := isHermitian_conjTranspose_mul_mul _ hG
  have hGK : G = K * (Pᴴ * P) := by rw [← hP, ← mul_assoc, hK, one_mul]
  have hT2 : T = P⁻¹ᴴ * K * Pᴴ := by
    rw [hT, hGK]; simp only [mul_assoc, hPi, mul_one]
  have hTT : T * T = 1 := by
    rw [hT2]
    calc P⁻¹ᴴ * K * Pᴴ * (P⁻¹ᴴ * K * Pᴴ) = P⁻¹ᴴ * (K * (Pᴴ * P⁻¹ᴴ) * K) * Pᴴ := by
          simp only [mul_assoc]
      _ = 1 := by rw [hPh, mul_one, hK, mul_one, hPh']
  have hTt : T.trace = (m : ℂ) - n := by
    rw [hT2, trace_mul_comm, ← mul_assoc, hPh, one_mul, ht]
  set U : Matrix (Fin r) (Fin r) ℂ := hTh.eigenvectorUnitary.1 with hU
  set d : Fin r → ℂ := RCLike.ofReal ∘ hTh.eigenvalues with hd
  have hUU : U * Uᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  have hUU' : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hD : Uᴴ * T * U = diagonal d := by
    have := hTh.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hdd : ∀ a, d a * d a = 1 := by
    have : diagonal d * diagonal d = 1 := by
      rw [← hD]
      calc Uᴴ * T * U * (Uᴴ * T * U) = Uᴴ * (T * (U * Uᴴ) * T) * U := by simp only [mul_assoc]
        _ = 1 := by rw [hUU, mul_one, hTT, mul_one, hUU']
    rw [diagonal_mul_diagonal, ← diagonal_one] at this
    exact fun a => congrFun (diagonal_injective this) a
  have hds : ∑ a, d a = (m : ℂ) - n := by
    rw [← trace_diagonal, ← hD, trace_mul_comm, ← mul_assoc, hUU, one_mul, hTt]
  obtain ⟨σ, hσ⟩ := exists_perm_sgn hr d hdd hds
  refine ⟨(P⁻¹ * U).submatrix id σ, ?_, ?_⟩
  · rw [det_permute', det_mul]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    · exact left_ne_zero_of_mul_eq_one (b := P.det) (by rw [← det_mul, hPi', det_one])
    · exact left_ne_zero_of_mul_eq_one (b := Uᴴ.det) (by rw [← det_mul, hUU, det_one])
  · have : ((P⁻¹ * U).submatrix id σ)ᴴ * G * (P⁻¹ * U).submatrix id σ =
        (Uᴴ * T * U).submatrix σ σ := by
      have e : Uᴴ * T * U = (P⁻¹ * U)ᴴ * G * (P⁻¹ * U) := by
        rw [hT, conjTranspose_mul]; simp only [mul_assoc]
      rw [e]; ext a b; simp [mul_apply]
    rw [this, hD, submatrix_diagonal_equiv]
    congr 1; funext a; exact hσ a
end GlobalTheory.HermSign
