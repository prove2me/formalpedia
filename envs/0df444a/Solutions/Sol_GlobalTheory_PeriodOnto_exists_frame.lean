-- Prove2me | solution 1 for GlobalTheory.PeriodOnto.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:35.699856+00:00
-- url     : https://prove2.me/submissions/68d27daa-9539-4485-a37b-bf644629ac68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
import Theorems.Thm_GlobalTheory_PeriodOnto_comm_sgnMat_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {r q : ℕ} (G M Mi : Matrix (Fin r) (Fin r) ℂ) (hM : M * Mi = 1)
    (hc : sgnMat r q * (Miᵀ * G * Mi.map conj) = (Miᵀ * G * Mi.map conj) * sgnMat r q)
    (hp : (sgnMat r q * (Miᵀ * G * Mi.map conj)).PosDef) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, x.det ≠ 0 ∧ (sgnMat r q * (xᵀ * G * x.map conj)).PosDef ∧
      ∀ (v : Fin r → ℂ) (a : Fin r),
        ((a : ℕ) < q → (v ᵥ* (G * x.map conj)) a = (M *ᵥ v) a) ∧
        (¬ (a : ℕ) < q → (x⁻¹ *ᵥ v) a = (M *ᵥ v) a) := by
  set A := Miᵀ * G * Mi.map conj with hA
  have hM' : Mi * M = 1 := mul_eq_one_comm.mp hM
  have hoff := (comm_sgnMat_iff A).mp hc
  let N : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun a b => if (a : ℕ) < q then A a b else (1 : Matrix (Fin r) (Fin r) ℂ) a b
  have hNc : sgnMat r q * N = N * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    by_cases ha : (a : ℕ) < q
    · simp [N, ha, hoff a b hab]
    · have : a ≠ b := by rintro rfl; simp at hab
      simp [N, ha, this]
  have hNu : IsUnit N := by
    rw [← mulVec_injective_iff_isUnit]
    have : ∀ u, N *ᵥ u = 0 → u = 0 := by
      intro u hu
      by_contra hne
      have h1 := hp.dotProduct_mulVec_pos hne
      have h2 : star u ⬝ᵥ ((sgnMat r q * A) *ᵥ u) = 0 := by
        rw [← mulVec_mulVec]
        refine Finset.sum_eq_zero fun a _ => ?_
        have ha := congrFun hu a
        by_cases hq : (a : ℕ) < q
        · have : (A *ᵥ u) a = 0 := by simpa [N, mulVec, dotProduct, hq] using ha
          simp [sgnMat, mulVec_diagonal, this]
        · have : u a = 0 := by simpa [N, mulVec, dotProduct, hq, one_apply] using ha
          simp [this]
      exact h1.ne' h2
    intro u u' huu
    have := this (u - u') (by rw [mulVec_sub, huu, sub_self])
    exact sub_eq_zero.mp this
  obtain ⟨Y, hNY⟩ := hNu.exists_right_inv
  have hYN : Y * N = 1 := mul_eq_one_comm.mp hNY
  have hYc : sgnMat r q * Y = Y * sgnMat r q := by
    calc sgnMat r q * Y = Y * (N * sgnMat r q) * Y := by rw [← Matrix.mul_assoc Y, hYN, Matrix.one_mul]
      _ = Y * sgnMat r q := by rw [← hNc, Matrix.mul_assoc, Matrix.mul_assoc, hNY, Matrix.mul_one]
  have hcc : ∀ Z : Matrix (Fin r) (Fin r) ℂ, (Z.map conj).map conj = Z := by
    intro Z; ext a b; simp
  have hinv : (N.map conj * M) * (Mi * Y.map conj) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, hM, Matrix.one_mul, ← Matrix.map_mul, hNY]
    simp
  have hYT : (Y.map conj)ᵀ = Yᴴ := by ext a b; simp [conjTranspose_apply]
  have hYHc : sgnMat r q * Yᴴ = Yᴴ * sgnMat r q := by
    rw [comm_sgnMat_iff]
    intro a b hab
    have := (comm_sgnMat_iff Y).mp hYc b a (fun h => hab h.symm)
    simp [conjTranspose_apply, this]
  refine ⟨Mi * Y.map conj, ?_, ?_, fun v a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · intro h0
    have := congrArg Matrix.det hinv
    rw [det_mul (N.map conj * M), h0] at this
    simp at this
  · have : sgnMat r q * ((Mi * Y.map conj)ᵀ * G * (Mi * Y.map conj).map conj) =
        Yᴴ * (sgnMat r q * A) * Y := by
      rw [transpose_mul, Matrix.map_mul, hcc, hYT, ← Matrix.mul_assoc Yᴴ, ← hYHc, hA]
      simp only [Matrix.mul_assoc]
    rw [this]
    refine hp.conjTranspose_mul_mul_same ?_
    rw [mulVec_injective_iff_isUnit]
    exact IsUnit.of_mul_eq_one N hYN
  · have h1 : G * (Mi * Y.map conj).map conj = Mᵀ * (A * Y) := by
      rw [Matrix.map_mul, hcc, hA]
      simp only [← Matrix.mul_assoc]
      rw [← transpose_mul, hM', transpose_one, Matrix.one_mul]
    have hAY : sgnMat r q * (A * Y) = (A * Y) * sgnMat r q := by
      rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc A, hYc, Matrix.mul_assoc A]
    have h2 : ∀ c, (A * Y) c a = (1 : Matrix (Fin r) (Fin r) ℂ) c a := by
      intro c
      by_cases hcq : (c : ℕ) < q
      · rw [← hNY]; simp [Matrix.mul_apply, N, hcq]
      · have : c ≠ a := by rintro rfl; exact hcq ha
        rw [(comm_sgnMat_iff _).mp hAY c a (by simp [hcq, ha])]
        simp [this]
    rw [h1, ← vecMul_vecMul, vecMul_transpose]
    simp [vecMul, dotProduct, h2, one_apply]
  · rw [inv_eq_left_inv hinv, ← mulVec_mulVec]
    have h3 : ∀ c, (N.map conj) a c = if a = c then 1 else 0 := by
      intro c
      by_cases h : a = c
      · subst h; simp [N, ha]
      · simp [N, ha, h]
    generalize M *ᵥ v = w
    simp only [mulVec, dotProduct, h3]
    simp
end GlobalTheory.PeriodOnto
