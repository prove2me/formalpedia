-- Prove2me | solution 1 for MDPFinance.MeanVariance.mvd_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:27:48.665691+00:00
-- url     : https://prove2.me/submissions/6b5306ee-5ffe-4e1d-8213-e12a0a1e2ccc

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance.F622

open MDPFinance.MeanVariance Matrix

/-- Linear algebra core: if `C = Σ + e eᵀ` with `Σ` positive definite and `e ≠ 0`, then
`0 < eᵀ C⁻¹ e < 1`. -/
theorem ell_bounds_of {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (e : Fin d → ℝ) (he : e ≠ 0) (C : Matrix (Fin d) (Fin d) ℝ)
    (hC : C = S + Matrix.vecMulVec e e) :
    0 < e ⬝ᵥ (C⁻¹ *ᵥ e) ∧ e ⬝ᵥ (C⁻¹ *ᵥ e) < 1 := by
  have hmul : ∀ x : Fin d → ℝ, C *ᵥ x = S *ᵥ x + (e ⬝ᵥ x) • e := by
    intro x
    rw [hC, Matrix.add_mulVec]
    congr 1
    ext i
    simp [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have hq : ∀ x : Fin d → ℝ, x ⬝ᵥ (C *ᵥ x) = x ⬝ᵥ (S *ᵥ x) + (e ⬝ᵥ x) ^ 2 := by
    intro x
    rw [hmul, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm x e]
    ring
  have hSpos : ∀ x : Fin d → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (S *ᵥ x) := by
    intro x hx
    simpa using hS.dotProduct_mulVec_pos hx
  have hinj : Function.Injective C.mulVec := by
    intro a b hab
    by_contra hne
    have hx : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : C *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have := hq (a - b)
    rw [h0, dotProduct_zero] at this
    have := hSpos _ hx
    nlinarith [sq_nonneg (e ⬝ᵥ (a - b))]
  have hunit : IsUnit C := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hunit
  set v := C⁻¹ *ᵥ e with hv
  have hCv : C *ᵥ v = e := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h
    apply he
    rw [← hCv, h, Matrix.mulVec_zero]
  have key := hq v
  rw [hCv, dotProduct_comm v e] at key
  have hpos := hSpos v hvne
  constructor
  · nlinarith [sq_nonneg (e ⬝ᵥ v)]
  · nlinarith [sq_nonneg (e ⬝ᵥ v)]

theorem cmat_eq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (n : ℕ)
    (h1 : 1 ≤ n) (h2 : n ≤ M.N) :
    M.Cmat n = Matrix.of (fun j k =>
      ∫ ω, (M.R n ω j - ∫ ω', M.R n ω' j ∂M.measIP) * (M.R n ω k - ∫ ω', M.R n ω' k ∂M.measIP)
        ∂M.measIP) + Matrix.vecMulVec (M.Evec n) (M.Evec n) := by
  have := M.isProb
  ext j k
  have hj := M.hR_L2 n h1 h2 j
  have hk := M.hR_L2 n h1 h2 k
  have ij : Integrable (fun ω => M.R n ω j) M.measIP := hj.integrable (by norm_num)
  have ik : Integrable (fun ω => M.R n ω k) M.measIP := hk.integrable (by norm_num)
  have ijk : Integrable (fun ω => M.R n ω j * M.R n ω k) M.measIP := hj.integrable_mul hk
  set a := ∫ ω', M.R n ω' j ∂M.measIP with ha
  set b := ∫ ω', M.R n ω' k ∂M.measIP with hb
  have hexp : (fun ω => (M.R n ω j - a) * (M.R n ω k - b)) =
      fun ω => (M.R n ω j * M.R n ω k - (b * M.R n ω j + a * M.R n ω k)) + a * b := by
    funext ω; ring
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.vecMulVec_apply, MVMarket.Cmat,
    MVMarket.Evec]
  have i3 : Integrable (fun ω => b * M.R n ω j) M.measIP := ij.const_mul b
  have i4 : Integrable (fun ω => a * M.R n ω k) M.measIP := ik.const_mul a
  have i2 : Integrable (fun ω => b * M.R n ω j + a * M.R n ω k) M.measIP := i3.add i4
  have i1 : Integrable (fun ω => M.R n ω j * M.R n ω k - (b * M.R n ω j + a * M.R n ω k))
      M.measIP := ijk.sub i2
  rw [hexp, integral_add i1 (integrable_const _), integral_sub ijk i2, integral_add i3 i4,
    integral_const_mul, integral_const_mul, integral_const]
  simp [← ha, ← hb]
  ring

theorem ell_bounds {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (n : ℕ)
    (h1 : 1 ≤ n) (h2 : n ≤ M.N) : 0 < M.ell n ∧ M.ell n < 1 :=
  ell_bounds_of _ (M.hCov_posdef n h1 h2) (M.Evec n) (M.hR_mean_ne n h1 h2) (M.Cmat n)
    (cmat_eq M n h1 h2)

end MDPFinance.MeanVariance.F622

open MDPFinance.MeanVariance in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1))) :
    ∀ n < M.N, 0 < dseq n ∧ dseq n < 1 := by
  have aux : ∀ k n, n + k + 1 = M.N → 0 < dseq n ∧ dseq n < 1 := by
    intro k
    induction k with
    | zero =>
      intro n hn
      have hl := MDPFinance.MeanVariance.F622.ell_bounds M (n + 1) (by omega) (by omega)
      rw [hdrec n (by omega), show n + 1 = M.N by omega, hdN]
      rw [show n + 1 = M.N by omega] at hl
      constructor <;> nlinarith [hl.1, hl.2]
    | succ k ih =>
      intro n hn
      have hl := MDPFinance.MeanVariance.F622.ell_bounds M (n + 1) (by omega) (by omega)
      have h' := ih (n + 1) (by omega)
      rw [hdrec n (by omega)]
      constructor
      · exact mul_pos h'.1 (by linarith [hl.2])
      · nlinarith [h'.1, h'.2, hl.1, hl.2]
  intro n hn
  exact aux (M.N - n - 1) n (by omega)
