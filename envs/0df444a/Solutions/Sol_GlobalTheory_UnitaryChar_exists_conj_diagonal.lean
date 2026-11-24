-- Prove2me | solution 1 for GlobalTheory.UnitaryChar.exists_conj_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:13.874159+00:00
-- url     : https://prove2.me/submissions/3cf4a4d8-19b0-4891-adee-d285a38cf0d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}
namespace GlobalTheory.UnitaryChar
theorem _root_.solution (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℂ),
      ((V⁻¹ * u * V : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
  obtain ⟨z, hz1, hz⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ∉ spectrum ℂ (u : Matrix (Fin n) (Fin n) ℂ) := by
    have hfin := Matrix.finite_spectrum (u : Matrix (Fin n) (Fin n) ℂ)
    have hinf : (Metric.sphere (0 : ℂ) 1).Infinite := by
      have hc : IsConnected (Metric.sphere (0 : ℂ) 1) :=
        isConnected_sphere (by simp) 0 zero_le_one
      refine hc.isPreconnected.infinite_of_nontrivial ⟨1, by simp, -1, by simp, by norm_num⟩
    obtain ⟨z, h1, h2⟩ := hinf.exists_notMem_finite hfin
    exact ⟨z, by simpa using h1, h2⟩
  have hzz : star z * z = 1 := by
    rw [mul_comm]; simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]
  set U : Matrix (Fin n) (Fin n) ℂ := (u : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : star U * U = 1 := u.2.1
  have hA : IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
    have := spectrum.notMem_iff.1 hz
    rwa [Algebra.algebraMap_eq_smul_one] at this
  obtain ⟨B, hAB, hBA⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ, (z • 1 - U) * B = 1 ∧ B * (z • 1 - U) = 1 :=
    isUnit_iff_exists.1 hA
  have hBA' : star B * (star z • 1 - star U) = 1 := by
    have := congrArg star hAB
    simpa [star_mul, star_smul] using this
  have key : z • B + star z • star B = 1 := by
    have h1 : (star z • 1 - star U) * (z • 1 - U) =
        z • (star z • 1 - star U) + star z • (z • (1 : Matrix (Fin n) (Fin n) ℂ) - U) := by
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hUU, smul_sub,
        smul_smul, hzz, mul_comm z (star z), one_smul]
      abel
    have h2 : star B * ((star z • 1 - star U) * (z • 1 - U)) * B = 1 := by
      rw [← mul_assoc, hBA', one_mul, hAB]
    rw [h1, mul_add, add_mul, mul_smul_comm, hBA', mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
      mul_assoc, hAB, one_mul, mul_one] at h2
    exact h2
  have hH : (Complex.I • (z • B - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))).IsHermitian := by
    have h3 : star z • star B = 1 - z • B := by rw [← key]; abel
    change star _ = _
    rw [star_smul, star_sub, star_smul, h3, star_smul]
    simp only [star_one, RCLike.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  have hs := hH.conjStarAlgAut_star_eigenvectorUnitary
  set V := hH.eigenvectorUnitary
  generalize (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℂ) = e at hs
  rw [Unitary.conjStarAlgAut_star_apply] at hs
  set W : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) with hW
  have hWW : star W * W = 1 := V.2.1
  have hWW' : W * star W = 1 := V.2.2
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  have hB : star W * B * W = diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) := by
    have h4 : diagonal (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) =
        z⁻¹ • ((-Complex.I) • diagonal e + (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases h : i = j <;> simp [diagonal_apply, one_apply, h]
    rw [h4, ← hs]
    simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, hWW, smul_smul, neg_mul,
      Complex.I_mul_I, neg_neg, one_smul, sub_add_cancel, inv_mul_cancel₀ hz0]
  generalize (fun i => z⁻¹ * (-Complex.I * e i + 1 / 2)) = b at hB
  have h5 : (z • 1 - star W * U * W) * diagonal b = 1 := by
    have h6 : z • 1 - star W * U * W = star W * (z • 1 - U) * W := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hWW]
    rw [h6, ← hB]
    calc star W * (z • 1 - U) * W * (star W * B * W)
        = star W * ((z • 1 - U) * (W * star W) * B) * W := by simp only [mul_assoc]
      _ = 1 := by rw [hWW', mul_one, hAB, mul_one, hWW]
  refine ⟨V, fun i => (star W * U * W) i i, ?_⟩
  change star W * U * W = _
  ext i j
  by_cases h : i = j
  · subst h; simp
  · have h7 := congrFun (congrFun h5 i) j
    have h8 := congrFun (congrFun h5 j) j
    rw [mul_diagonal] at h7 h8
    rw [one_apply_eq] at h8
    have hb : b j ≠ 0 := right_ne_zero_of_mul_eq_one h8
    rw [one_apply_ne h, mul_eq_zero] at h7
    rw [diagonal_apply_ne _ h]
    simpa [one_apply_ne h] using h7.resolve_right hb
end GlobalTheory.UnitaryChar
