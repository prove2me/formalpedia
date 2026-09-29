-- Prove2me | solution 1 for Leptogenesis.cpAsymmetry_total_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:00:56.173384+00:00
-- url     : https://prove2.me/submissions/a0842813-e1b7-416b-adca-30f199b9cc4e

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

set_option autoImplicit false

open Leptogenesis Matrix in
/-- Pasted from the proved sibling `casasIbarraR_orthogonal` (367f5d6d). -/
theorem lepto_casas_orth_tb (v : ℝ) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (hpos : ∀ i, 0 < masses i) :
    (casasIbarraR v M lam U masses)ᵀ * casasIbarraR v M lam U masses = 1 ∧
      casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ = 1 := by
  obtain ⟨hU, _, hmU⟩ := hdiag
  set Ds : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun i => ((Real.sqrt (masses i) : ℂ))⁻¹) with hDs
  set Dt : Matrix (Fin 3) (Fin 3) ℂ := diagonal (fun k => ((Real.sqrt (M k) : ℂ))⁻¹) with hDt
  have hm : lightMassMatrix v M lam =
      ((v : ℂ) * (v : ℂ)) • (lam * (Dt * Dt) * lamᵀ) := by
    have hDD : Dt * Dt = diagonal (fun k => ((M k : ℂ))⁻¹) := by
      rw [hDt, diagonal_mul_diagonal]
      congr 1
      funext k
      have h1 : ((Real.sqrt (M k) : ℂ)) * (Real.sqrt (M k) : ℂ) = (M k : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hM k).le]
      rw [← mul_inv, h1]
    rw [hDD]
    ext α β
    rw [Matrix.smul_apply, Matrix.mul_apply]
    simp only [lightMassMatrix, Matrix.mul_diagonal, transpose_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hU1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hU2 : Uᵀ * U.map (starRingEnd ℂ) = 1 := by
    have h := congrArg Matrix.transpose hU1
    rw [transpose_mul, transpose_one] at h
    have hc : (Uᴴ)ᵀ = U.map (starRingEnd ℂ) := by
      ext i j
      simp
    rw [hc] at h
    exact h
  have hRRt : casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ =
      Ds * (Uᵀ * lightMassMatrix v M lam * U) * Ds := by
    rw [hm]
    simp only [casasIbarraR, transpose_smul, transpose_mul, hDs, hDt, diagonal_transpose,
      transpose_transpose, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hmid : Uᵀ * lightMassMatrix v M lam * U = diagonal (fun i => (masses i : ℂ)) := by
    rw [hmU]
    calc Uᵀ * (U.map (starRingEnd ℂ) * diagonal (fun i => (masses i : ℂ)) * Uᴴ) * U
        = (Uᵀ * U.map (starRingEnd ℂ)) * diagonal (fun i => (masses i : ℂ)) * (Uᴴ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (masses i : ℂ)) := by rw [hU1, hU2, Matrix.one_mul, Matrix.mul_one]
  have hfin : casasIbarraR v M lam U masses * (casasIbarraR v M lam U masses)ᵀ = 1 := by
    rw [hRRt, hmid, hDs, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : (Real.sqrt (masses i) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (hpos i)).ne'
    have h1 : ((Real.sqrt (masses i) : ℂ)) * (Real.sqrt (masses i) : ℂ) = (masses i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
    rw [← h1]
    field_simp
  exact ⟨mul_eq_one_comm.mp hfin, hfin⟩

/-- Davidson–Ibarra core inequality: if `Im ∑ rᵢ² = 0` and `0 ≤ lo ≤ dᵢ ≤ hi`, then
`|∑ dᵢ² Im(rᵢ²)| ≤ (hi - lo) ∑ dᵢ |rᵢ|²`. -/
theorem lepto_key_ineq_tb (d : Fin 3 → ℝ) (r : Fin 3 → ℂ) (lo hi : ℝ)
    (hd : ∀ i, 0 < d i) (hlo : ∀ i, lo ≤ d i) (hhi : ∀ i, d i ≤ hi) (hlo0 : 0 ≤ lo)
    (hsum : (∑ i, r i ^ 2).im = 0) :
    |∑ i, d i ^ 2 * (r i ^ 2).im| ≤ (hi - lo) * ∑ i, d i * ‖r i‖ ^ 2 := by
  have hs : ∑ i, (r i ^ 2).im = 0 := by rw [← Complex.im_sum]; exact hsum
  have hrw : ∑ i, d i ^ 2 * (r i ^ 2).im = ∑ i, (d i ^ 2 - lo * hi) * (r i ^ 2).im := by
    have h : ∑ i, (d i ^ 2 - lo * hi) * (r i ^ 2).im =
        ∑ i, d i ^ 2 * (r i ^ 2).im - lo * hi * ∑ i, (r i ^ 2).im := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h, hs, mul_zero, sub_zero]
  rw [hrw, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  have hdi := hd i
  have hloi := hlo i
  have hhii := hhi i
  have h1 : |d i ^ 2 - lo * hi| ≤ (hi - lo) * d i := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d i + hi) (sub_nonneg.mpr hloi)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hhii) (by linarith : (0 : ℝ) ≤ d i + lo)]
  have h2 : |(r i ^ 2).im| ≤ ‖r i‖ ^ 2 := by
    calc |(r i ^ 2).im| ≤ ‖r i ^ 2‖ := Complex.abs_im_le_norm _
      _ = ‖r i‖ ^ 2 := norm_pow _ _
  calc |d i ^ 2 - lo * hi| * |(r i ^ 2).im| ≤ (hi - lo) * d i * ‖r i‖ ^ 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (by linarith) hdi.le)
    _ = (hi - lo) * (d i * ‖r i‖ ^ 2) := by ring

open Leptogenesis Matrix in
theorem solution (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ) (hM : ∀ k, 0 < M k)
    (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses) :
    |∑ α, cpAsymmetry v M lam α| ≤
      3 * M 0 * ((⨆ i, masses i) - ⨅ i, masses i) / (16 * Real.pi * v ^ 2) := by
  have hU : U ∈ Matrix.unitaryGroup (Fin 3) ℂ := hdiag.1
  have h0 : ∀ i, 0 ≤ masses i := hdiag.2.1
  have hmU := hdiag.2.2
  set S : ℝ := ∑ β, ‖lam β 0‖ ^ 2 with hSdef
  set hi : ℝ := ⨆ i, masses i with hhidef
  set lo : ℝ := ⨅ i, masses i with hlodef
  set Y : Matrix (Fin 3) (Fin 3) ℂ := Uᵀ * lam with hYdef
  have hhi_i : ∀ i, masses i ≤ hi := fun i => le_ciSup (Set.finite_range masses).bddAbove i
  have hlo_i : ∀ i, lo ≤ masses i := fun i => ciInf_le (Set.finite_range masses).bddBelow i
  have hlo0 : 0 ≤ lo := le_ciInf h0
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun β _ => by positivity)
  -- numerator of the total asymmetry
  have hnum : ∑ α, lam α 0 * ((lightMassMatrix v M lam).map (starRingEnd ℂ) * lam) α 0 =
      ∑ i, (masses i : ℂ) * Y i 0 ^ 2 := by
    have hconj : (lightMassMatrix v M lam).map (starRingEnd ℂ) =
        U * diagonal (fun i => (masses i : ℂ)) * Uᵀ := by
      rw [hmU, Matrix.map_mul, Matrix.map_mul]
      congr 2
      · ext i j
        simp
      · ext i j
        simp [Matrix.diagonal_apply]
        split_ifs <;> simp
      · ext i j
        simp
    rw [hconj, hYdef]
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
    ring
  have hc0 : 0 < 3 * M 0 / (16 * Real.pi * v ^ 2) := by
    have := hM 0
    positivity
  have hcp : ∑ α, cpAsymmetry v M lam α =
      3 * M 0 / (16 * Real.pi * v ^ 2) * ((∑ i, (masses i : ℂ) * Y i 0 ^ 2).im / S) := by
    simp only [cpAsymmetry]
    rw [← Finset.mul_sum, ← Finset.sum_div, ← Complex.im_sum, hnum]
  -- unitary invariance of the column norm
  have hnsq : ∀ w : Fin 3 → ℂ, ((∑ α, ‖w α‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [Complex.star_def, Complex.conj_mul']
  have hiso : ∀ (A : Matrix (Fin 3) (Fin 3) ℂ), Aᴴ * A = 1 → ∀ w : Fin 3 → ℂ,
      ∑ α, ‖(A *ᵥ w) α‖ ^ 2 = ∑ α, ‖w α‖ ^ 2 := by
    intro A hA w
    apply Complex.ofReal_injective
    rw [hnsq, hnsq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hA, one_mulVec]
  have hU3 : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hUt : (Uᵀ)ᴴ * Uᵀ = 1 := by
    have h := congrArg Matrix.transpose hU3
    rw [transpose_mul, transpose_one] at h
    have hc : (Uᵀ)ᴴ = (Uᴴ)ᵀ := by
      ext i j
      simp
    rw [hc]
    exact h
  have hSY : S = ∑ i, ‖Y i 0‖ ^ 2 := by
    have h := hiso _ hUt (fun j => lam j 0)
    have hY : ∀ i, (Uᵀ *ᵥ (fun j => lam j 0)) i = Y i 0 := by
      intro i
      simp [hYdef, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simp only [hY] at h
    rw [hSdef, h]
  -- the key bound on the numerator
  have hbound : |(∑ i, (masses i : ℂ) * Y i 0 ^ 2).im| ≤ (hi - lo) * S := by
    by_cases hall : ∀ i, 0 < masses i
    · set R : Matrix (Fin 3) (Fin 3) ℂ := casasIbarraR v M lam U masses with hRdef
      have hRR : Rᵀ * R = 1 := (lepto_casas_orth_tb v M hM lam U masses hdiag hall).1
      have hsum1 : ∑ i, R i 0 ^ 2 = 1 := by
        have h := congrFun (congrFun hRR 0) 0
        simpa [Matrix.mul_apply, sq] using h
      have hR : ∀ i, R i 0 = (v : ℂ) * (((Real.sqrt (masses i) : ℂ))⁻¹ * Y i 0 *
          ((Real.sqrt (M 0) : ℂ))⁻¹) := by
        intro i
        simp only [hRdef, casasIbarraR, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
        rw [Matrix.mul_assoc, Matrix.diagonal_mul]
      have hsd : ∀ i, ((Real.sqrt (masses i) : ℂ)) ^ 2 = (masses i : ℂ) := by
        intro i
        rw [← Complex.ofReal_pow, Real.sq_sqrt (h0 i)]
      have hsM : ((Real.sqrt (M 0) : ℂ)) ^ 2 = (M 0 : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (hM 0).le]
      have hR2 : ∀ i, R i 0 ^ 2 =
          (v : ℂ) ^ 2 * ((masses i : ℂ))⁻¹ * Y i 0 ^ 2 * ((M 0 : ℂ))⁻¹ := by
        intro i
        rw [hR i, show ((v : ℂ) * (((Real.sqrt (masses i) : ℂ))⁻¹ * Y i 0 *
          ((Real.sqrt (M 0) : ℂ))⁻¹)) ^ 2 = (v : ℂ) ^ 2 * (((Real.sqrt (masses i) : ℂ)) ^ 2)⁻¹ *
          Y i 0 ^ 2 * (((Real.sqrt (M 0) : ℂ)) ^ 2)⁻¹ by ring, hsd i, hsM]
      have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
      have hMC : (M 0 : ℂ) ≠ 0 := by exact_mod_cast (hM 0).ne'
      have hmC : ∀ i, (masses i : ℂ) ≠ 0 := fun i => by exact_mod_cast (hall i).ne'
      set K : ℝ := M 0 / v ^ 2 with hKdef
      have hK : 0 < K := by
        have := hM 0
        positivity
      have hterm : ∀ i, (masses i : ℂ) * Y i 0 ^ 2 =
          ((masses i ^ 2 * K : ℝ) : ℂ) * R i 0 ^ 2 := by
        intro i
        rw [hR2 i, hKdef]
        have := hmC i
        push_cast
        field_simp
      have hnorm : ∀ i, ‖Y i 0‖ ^ 2 = masses i * K * ‖R i 0‖ ^ 2 := by
        intro i
        have h := congrArg (fun z : ℂ => ‖z‖) (hR2 i)
        simp only [norm_pow, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hv, abs_of_pos (hall i), abs_of_pos (hM 0)] at h
        rw [h, hKdef]
        have := hall i
        have := hM 0
        field_simp
      have him : (∑ i, (masses i : ℂ) * Y i 0 ^ 2).im =
          K * ∑ i, masses i ^ 2 * (R i 0 ^ 2).im := by
        rw [Complex.im_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hterm i, Complex.im_ofReal_mul]
        ring
      have hSR : S = K * ∑ i, masses i * ‖R i 0‖ ^ 2 := by
        rw [hSY, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hnorm i]
        ring
      have hkey := lepto_key_ineq_tb masses (fun i => R i 0) lo hi hall hlo_i hhi_i hlo0
        (by rw [hsum1]; simp)
      rw [him, hSR, abs_mul, abs_of_pos hK]
      calc K * |∑ i, masses i ^ 2 * (R i 0 ^ 2).im|
          ≤ K * ((hi - lo) * ∑ i, masses i * ‖R i 0‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hkey hK.le
        _ = (hi - lo) * (K * ∑ i, masses i * ‖R i 0‖ ^ 2) := by ring
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hlo' : lo ≤ 0 := (hlo_i j).trans hj
      have h1 : |(∑ i, (masses i : ℂ) * Y i 0 ^ 2).im| ≤ ∑ i, masses i * ‖Y i 0‖ ^ 2 := by
        calc |(∑ i, (masses i : ℂ) * Y i 0 ^ 2).im| ≤ ‖∑ i, (masses i : ℂ) * Y i 0 ^ 2‖ :=
              Complex.abs_im_le_norm _
          _ ≤ ∑ i, ‖(masses i : ℂ) * Y i 0 ^ 2‖ := norm_sum_le _ _
          _ = ∑ i, masses i * ‖Y i 0‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 i)]
      have h2 : ∑ i, masses i * ‖Y i 0‖ ^ 2 ≤ hi * S := by
        rw [hSY, Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hhi_i i) (by positivity))
      have h3 : hi * S ≤ (hi - lo) * S := mul_le_mul_of_nonneg_right (by linarith) hS0
      exact h1.trans (h2.trans h3)
  -- conclude
  rw [hcp, abs_mul, abs_of_pos hc0]
  have hrw : 3 * M 0 * (hi - lo) / (16 * Real.pi * v ^ 2) =
      3 * M 0 / (16 * Real.pi * v ^ 2) * (hi - lo) := by ring
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ hc0.le
  rcases hS0.eq_or_lt with hSz | hSp
  · rw [← hSz, div_zero, abs_zero]
    linarith [hlo_i 0, hhi_i 0]
  · rw [abs_div, abs_of_pos hSp, div_le_iff₀ hSp]
    exact hbound
