-- Prove2me | solution 1 for HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1e53565a-0ffa-54a9-870c-de4563dcb90f

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_mem linePow coe_linePow binarySubst_line IsEichlerIntegral"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial
open scoped Manifold MatrixGroups ModularForm

namespace DetPosAux

variable {n : ℕ}

theorem slash_apply_of_det_pos (f : ℍ → ℂ) (k : ℤ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.val.det) (τ : ℍ) :
    (f ∣[k] β) τ = f (β • τ) * (↑β.val.det) ^ (k - 1) * denom β ↑τ ^ (-k) := by
  have hβ' : 0 < β.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [ModularForm.slash_apply, σ, if_pos hβ', ContinuousAlgEquiv.refl_apply]
  have habs : |β.det.val| = β.val.det := by
    rw [abs_of_pos hβ', Matrix.GeneralLinearGroup.val_det_apply]
  rw [habs]

theorem hasDerivAt_comp_smul_of_det_pos {G : ℍ → ℂ} {g : ℂ}
    {β : GL (Fin 2) ℝ} (hβ : 0 < β.val.det) (τ : ℍ)
    (hG : HasDerivAt (G ∘ ofComplex) g ↑(β • τ)) :
    HasDerivAt (fun z : ℂ => G (β • ofComplex z)) (g * (↑β.val.det / denom β ↑τ ^ 2)) ↑τ := by
  have hfun : (fun z : ℂ => G (β • ofComplex z))
      = (G ∘ ofComplex) ∘ fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) g ((fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG
  have hinner : HasDerivAt (fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) (↑β.val.det / denom β ↑τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hβ τ).hasDerivAt
  have hcomp := houter.comp (↑τ : ℂ) hinner
  rwa [← hfun] at hcomp

def degExps (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

theorem mem_degExps_iff (d : Fin 2 →₀ ℕ) : d ∈ degExps n ↔ d.degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degExps, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp
    omega
  · intro h
    refine ⟨d 0, by omega, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      omega

theorem eq_sum_degExps {K : Type*} [CommRing K] {p : MvPolynomial (Fin 2) K} (hp : p ∈ BinaryForm K n) :
    p = ∑ e ∈ degExps n, monomial e (coeff e p) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : d ∈ degExps n
  · rw [Finset.sum_eq_single d (fun e _ hne => if_neg hne) (fun h => (h hd).elim), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun e he => if_neg (fun h : e = d => hd (h ▸ he)))]
    exact ((mem_homogeneousSubmodule n p).mp hp).coeff_eq_zero (by rwa [mem_degExps_iff] at hd)

theorem coeff_binarySubst_eq_sum {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) ℤ) (v : ↥(BinaryForm K n))
    (d : Fin 2 →₀ ℕ) :
    coeff d (binarySubst K M (v : MvPolynomial (Fin 2) K))
      = ∑ e ∈ degExps n, coeff e (v : MvPolynomial (Fin 2) K) * coeff d (binarySubst K M (monomial e 1)) := by
  conv_lhs => rw [eq_sum_degExps v.2, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show monomial e (coeff e (v : MvPolynomial (Fin 2) K)) = coeff e (v : MvPolynomial (Fin 2) K) • monomial e (1 : K) by
      rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, smul_eq_mul]

theorem binarySubst_adjugate_linePow {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) (τ : ℍ) :
    binarySubst ℂ M.adjugate ((linePow n ((β • τ : ℍ) : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = ((M.det : ℂ) / denom β ↑τ) ^ n • ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := by
  have hdet : (0 : ℝ) < β.val.det := by
    rw [hβM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact_mod_cast hM
  have hdet' : 0 < (↑(Matrix.GeneralLinearGroup.det β) : ℝ) := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have hden : denom β (τ : ℂ) ≠ 0 := denom_ne_zero β τ
  have hβe : ∀ i j, (β : Matrix (Fin 2) (Fin 2) ℝ) i j = (M i j : ℝ) := fun i j => by
    rw [hβM]; rfl
  rw [coe_linePow, coe_linePow, map_pow, binarySubst_line, smul_eq_C_mul, C_pow, ← mul_pow]
  congr 1
  set x : ℂ := (M.det : ℂ) / denom β ↑τ with hx
  have hz : ((β • τ : ℍ) : ℂ) = num β ↑τ / denom β ↑τ := coe_smul_of_det_pos hdet' τ
  have hnum : num β ↑τ = (M 0 0 : ℂ) * ↑τ + (M 0 1 : ℂ) := by
    simp [num, hβe]
  have hdenE : denom β ↑τ = (M 1 0 : ℂ) * ↑τ + (M 1 1 : ℂ) := by
    simp [denom, hβe]
  have a00 : M.adjugate 0 0 = M 1 1 := by simp [Matrix.adjugate_fin_two]
  have a01 : M.adjugate 0 1 = -M 0 1 := by simp [Matrix.adjugate_fin_two]
  have a10 : M.adjugate 1 0 = -M 1 0 := by simp [Matrix.adjugate_fin_two]
  have a11 : M.adjugate 1 1 = M 0 0 := by simp [Matrix.adjugate_fin_two]
  have e0 : ((M.adjugate 0 0 : ℤ) : ℂ) * ((β • τ : ℍ) : ℂ) + ((M.adjugate 0 1 : ℤ) : ℂ) = x * ↑τ := by
    rw [a00, a01, hz, hx]
    field_simp
    rw [hnum, hdenE, Matrix.det_fin_two]
    push_cast
    ring
  have e1 : ((M.adjugate 1 0 : ℤ) : ℂ) * ((β • τ : ℍ) : ℂ) + ((M.adjugate 1 1 : ℤ) : ℂ) = x := by
    rw [a10, a11, hz, hx]
    field_simp
    rw [hnum, hdenE, Matrix.det_fin_two]
    push_cast
    ring
  rw [e0, e1, map_mul]
  ring

end DetPosAux

end HeckeEis

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul.HeckeEis HeckeEis.DetPosAux UpperHalfPlane MvPolynomial in
theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hF : HeckeEis.IsEichlerIntegral n f F)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] β)
      (fun τ => ((HeckeEis.binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => HeckeEis.binarySubst_mem ℂ M.adjugate h)) (F (β • τ))) := by
  intro d τ
  have hdet : (0 : ℝ) < β.val.det := by
    rw [hβM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]
    exact_mod_cast hM
  have hdetM : (β.val.det : ℂ) = (M.det : ℂ) := by
    rw [hβM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simp
  have hden : denom β (τ : ℂ) ≠ 0 := denom_ne_zero β τ

  set c : ℂ := f (β • τ) * (↑β.val.det / denom β ↑τ ^ 2) with hc

  have hH : ∀ e : Fin 2 →₀ ℕ, HasDerivAt
      (fun z : ℂ => coeff e ((F (β • ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (coeff e (((c • linePow n ((β • τ : ℍ) : ℂ)) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) ↑τ := by
    intro e
    have h1 := hasDerivAt_comp_smul_of_det_pos (G := fun w : ℍ => coeff e ((F w : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      hdet τ (hF e (β • τ))
    refine h1.congr_deriv ?_
    rw [Submodule.coe_smul, coeff_smul, smul_eq_mul, hc]
    ring

  have hfun : (fun z : ℂ => coeff d ((((binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => binarySubst_mem ℂ M.adjugate h)) (F (β • ofComplex z)) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      = fun z : ℂ => ∑ e ∈ degExps n,
          coeff e ((F (β • ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
            * coeff d (binarySubst ℂ M.adjugate (monomial e 1)) := by
    funext z
    exact coeff_binarySubst_eq_sum M.adjugate (F (β • ofComplex z)) d
  rw [hfun]
  have h2 : HasDerivAt (fun z : ℂ => ∑ e ∈ degExps n,
          coeff e ((F (β • ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
            * coeff d (binarySubst ℂ M.adjugate (monomial e 1)))
      (∑ e ∈ degExps n, coeff e (((c • linePow n ((β • τ : ℍ) : ℂ)) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
            * coeff d (binarySubst ℂ M.adjugate (monomial e 1))) ↑τ :=
    HasDerivAt.fun_sum fun e _ => (hH e).mul_const _
  refine h2.congr_deriv ?_
  rw [← coeff_binarySubst_eq_sum M.adjugate (c • linePow n ((β • τ : ℍ) : ℂ)) d, Submodule.coe_smul, map_smul,
    binarySubst_adjugate_linePow hM hβM τ, smul_smul, coeff_smul, smul_eq_mul,
    slash_apply_of_det_pos f _ hdet τ, hc, hdetM]

  congr 1
  rw [show (n : ℤ) + 2 - 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    show (-((n : ℤ) + 2)) = -(((n + 2 : ℕ) : ℤ)) by push_cast; ring, zpow_neg, zpow_natCast]
  rw [div_pow]
  field_simp
  ring

end

end S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul (solution)
