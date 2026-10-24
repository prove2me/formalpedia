-- Prove2me | solution 1 for HighDimStat.Pca.pca_basic_inequality_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:00:35.446862+00:00
-- url     : https://prove2.me/submissions/3b2a0bf3-a536-4dd9-8f02-57ab69bf711b

import Mathlib
import Definitions.Def_HighDimStat_Pca_IsMaximalUnitEigenvector
import Definitions.Def_HighDimStat_Pca_HasEigengap
import Definitions.Def_HighDimStat_Pca_PsiPCA

namespace PA88
open Matrix

lemma symm_bil {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.IsSymm) (u v : Fin d → ℝ) :
    u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  rw [dotProduct_mulVec, ← hM.eq, vecMul_transpose, dotProduct_comm, hM.eq]

lemma sumsq {d : ℕ} (v : Fin d → ℝ) : ∑ j, (v j) ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

lemma quad {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    ∑ i, v i * (M *ᵥ v) i = v ⬝ᵥ (M *ᵥ v) := rfl

/-- homogenization -/
lemma homog {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (S : (Fin d → ℝ) → Prop)
    (hS : ∀ (c : ℝ) v, S v → S (c • v)) (a : ℝ)
    (h : ∀ v, v ⬝ᵥ v = 1 → S v → v ⬝ᵥ (M *ᵥ v) ≤ a) :
    ∀ v, S v → v ⬝ᵥ (M *ᵥ v) ≤ a * (v ⬝ᵥ v) := by
  intro v hv
  by_cases h0 : v ⬝ᵥ v = 0
  · rw [dotProduct_self_eq_zero.mp h0]; simp
  have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_star_nonneg v) (Ne.symm h0)
  set s := v ⬝ᵥ v
  have hr : Real.sqrt s ^ 2 = s := Real.sq_sqrt hpos.le
  have hrp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hpos
  have hu := h ((Real.sqrt s)⁻¹ • v) (by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp; linarith) (hS _ _ hv)
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hu
  have : v ⬝ᵥ (M *ᵥ v) = (Real.sqrt s)^2 * ((Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * v ⬝ᵥ (M *ᵥ v))) := by
    field_simp
  rw [this, hr]; nlinarith

end PA88

open HighDimStat.Pca Matrix in
theorem solution {d : ℕ} (M P : Matrix (Fin d) (Fin d) ℝ)
    (hMsymm : M.IsSymm) (hPsymm : P.IsSymm)
    (θstar θhat : Fin d → ℝ) (ν : ℝ)
    (hmax_star : IsMaximalUnitEigenvector M θstar)
    (hgap : HasEigengap M θstar ν)
    (hmax_hat : IsMaximalUnitEigenvector (M + P) θhat) :
    ν * (1 - (∑ j, θhat j * θstar j) ^ 2) ≤
      |psiPCA P θstar (fun j => θhat j - θstar j)| := by
  obtain ⟨h1s, hms⟩ := hmax_star
  obtain ⟨hν, hg⟩ := hgap
  obtain ⟨h1h, hmh⟩ := hmax_hat
  simp only [PA88.sumsq, PA88.quad] at *
  set L := θstar ⬝ᵥ (M *ᵥ θstar)
  have hMax := PA88.homog M (fun _ => True) (fun _ _ _ => trivial) L
    (fun v hv _ => hms v hv) 
  have hGap := PA88.homog M (fun v => v ⬝ᵥ θstar = 0)
    (fun c v hv => by simp [smul_dotProduct, hv]) (L - ν) (fun v hv h => hg v hv h)
  have hH := hmh θstar h1s
  set c := θhat ⬝ᵥ θstar
  set w := θhat - c • θstar with hw
  have hwθ : w ⬝ᵥ θstar = 0 := by
    simp [w, sub_dotProduct, smul_dotProduct, h1s, c]
  -- cross term vanishes
  set b := w ⬝ᵥ (M *ᵥ θstar)
  set q := w ⬝ᵥ (M *ᵥ w)
  set n := w ⬝ᵥ w
  have hexp : ∀ t : ℝ, (θstar + t • w) ⬝ᵥ (M *ᵥ (θstar + t • w)) = L + 2 * t * b + t^2 * q := by
    intro t
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [PA88.symm_bil hMsymm θstar w]; ring
  have hnorm : ∀ t : ℝ, (θstar + t • w) ⬝ᵥ (θstar + t • w) = 1 + t^2 * n := by
    intro t
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm θstar w, hwθ, h1s]; ring
  have hq : q ≤ (L - ν) * n := hGap w hwθ
  have hb : b = 0 := by
    have ht : ∀ t : ℝ, 2 * t * b + t^2 * (q - L * n) ≤ 0 := by
      intro t; have := hMax (θstar + t • w) trivial
      rw [hexp, hnorm] at this; nlinarith
    have hn0 : 0 ≤ n := dotProduct_self_star_nonneg w
    set K := L * n - q
    have hK : 0 ≤ K := by nlinarith
    have h1 := ht (b / (K + 1))
    have hK1 : 0 < K + 1 := by linarith
    have : 2 * (b / (K+1)) * b + (b/(K+1))^2 * (q - L * n) = b^2 * (K + 2) / (K+1)^2 := by
      field_simp; ring
    rw [this] at h1
    have : b^2 * (K+2) ≤ 0 := by
      have := div_nonpos_iff.mp h1
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · nlinarith [sq_nonneg (K+1)]
      · exact h
    nlinarith [sq_nonneg b]
  have hθ : θhat = c • θstar + w := by simp [w]
  have hn : n = 1 - c^2 := by
    have := h1h; rw [hθ] at this
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_comm θstar w, hwθ, h1s] at this; linarith
  have hQ : θhat ⬝ᵥ (M *ᵥ θhat) = c^2 * L + q := by
    rw [hθ]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [PA88.symm_bil hMsymm θstar w]; simp only [b] at hb; rw [hb]; ring
  have hpsi : psiPCA P θstar (fun j => θhat j - θstar j) =
      θhat ⬝ᵥ (P *ᵥ θhat) - θstar ⬝ᵥ (P *ᵥ θstar) := by
    unfold psiPCA
    rw [PA88.quad P (fun j => θhat j - θstar j)]
    change (θhat - θstar) ⬝ᵥ (P *ᵥ (θhat - θstar)) + 2 * ((θhat - θstar) ⬝ᵥ (P *ᵥ θstar)) = _
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [PA88.symm_bil hPsymm θstar θhat]; ring
  have hH' : θstar ⬝ᵥ (M *ᵥ θstar) + θstar ⬝ᵥ (P *ᵥ θstar) ≤
      θhat ⬝ᵥ (M *ᵥ θhat) + θhat ⬝ᵥ (P *ᵥ θhat) := by
    simpa [add_mulVec, dotProduct_add] using hH
  rw [hpsi]
  refine le_trans ?_ (le_abs_self _)
  change ν * (1 - c^2) ≤ _
  rw [hn] at hq
  rw [hQ] at hH'
  linarith
