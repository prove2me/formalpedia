-- Prove2me | solution 1 for HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8012da71-d21f-5ef3-9871-a367f571f51e

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul
import Theorems.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const
import Theorems.Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm

set_option autoImplicit false

open UpperHalfPlane MvPolynomial CongruenceSubgroup Matrix
open scoped MatrixGroups ModularForm Manifold

namespace R1TPH

theorem det_map_algebraMap (M : Matrix (Fin 2) (Fin 2) ℤ) : (M.map (algebraMap ℤ ℝ)).det = (M.det : ℝ) := by
  have h := (algebraMap ℤ ℝ).map_det M
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]; rfl

noncomputable def glOf (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.map (algebraMap ℤ ℝ)) (by
    rw [det_map_algebraMap]; exact_mod_cast hM)

@[scoped simp] theorem coe_glOf (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    ((glOf M hM : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ) := rfl

theorem glOf_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hAB : (A * B).det ≠ 0) :
    glOf (A * B) hAB = glOf A hA * glOf B hB := by
  refine Units.ext ?_
  change (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ)
  exact Matrix.map_mul

theorem glOf_coe_SL (γ : SL(2, ℤ)) (h : ((γ : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0) :
    glOf (γ : Matrix (Fin 2) (Fin 2) ℤ) h = (γ : GL (Fin 2) ℝ) := by
  refine Units.ext ?_
  rfl

theorem det_glOf (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    ((glOf M hM).det : ℝ) = (M.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_glOf, det_map_algebraMap]

section Beta

variable (N ℓ : ℕ) [NeZero ℓ]

def alphaAdj : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

omit [NeZero ℓ] in
theorem adjugate_alphaMat : (HeckeEis.alphaMat ℓ).adjugate = alphaAdj ℓ := by
  rw [HeckeEis.alphaMat, Matrix.adjugate_fin_two_of, alphaAdj]
  simp

omit [NeZero ℓ] in
theorem alphaAdj_mul_alphaMat : alphaAdj ℓ * HeckeEis.alphaMat ℓ = (ℓ : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [alphaAdj, HeckeEis.alphaMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp

omit [NeZero ℓ] in
theorem alphaMat_mul_alphaAdj : HeckeEis.alphaMat ℓ * alphaAdj ℓ = (ℓ : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [alphaAdj, HeckeEis.alphaMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp

abbrev Mx (x : Gamma0 N) : Matrix (Fin 2) (Fin 2) ℤ := ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)

omit [NeZero ℓ] in
theorem Mx_mul (x y : Gamma0 N) : Mx N (x * y) = Mx N x * Mx N y := by
  simp [Mx, Matrix.SpecialLinearGroup.coe_mul]

omit [NeZero ℓ] in
theorem Mx_mul_inv_self (x : Gamma0 N) : Mx N x * Mx N x⁻¹ = 1 := by
  rw [← Mx_mul, mul_inv_cancel]; simp [Mx]

omit [NeZero ℓ] in
theorem Mx_inv_mul_self (x : Gamma0 N) : Mx N x⁻¹ * Mx N x = 1 := by
  rw [← Mx_mul, inv_mul_cancel]; simp [Mx]

omit [NeZero ℓ] in
theorem det_Mx (x : Gamma0 N) : (Mx N x).det = 1 := by simp [Mx]

omit [NeZero ℓ] in

theorem adjugate_Mx_inv (x : Gamma0 N) : (Mx N x⁻¹).adjugate = Mx N x := by
  have h : ((((x : SL(2, ℤ))⁻¹)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((x : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).adjugate :=
    Matrix.SpecialLinearGroup.coe_inv _
  rw [inv_inv] at h
  simpa [Mx] using h.symm

theorem alphaAdj_mul_heckeConj (t : ↥(HeckeEis.heckeUpper N ℓ)) :
    alphaAdj ℓ * Mx N (HeckeEis.heckeConj N ℓ t) = Mx N (t : Gamma0 N) * alphaAdj ℓ := by
  have hℓ : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne ℓ)
  have key := HeckeEis.heckeConjMat_mul_alphaMat ((HeckeEis.mem_heckeUpper N ℓ).mp t.2)
  change alphaAdj ℓ * HeckeEis.heckeConjMat ℓ (Mx N (t : Gamma0 N)) = _
  have lhs : alphaAdj ℓ * (HeckeEis.heckeConjMat ℓ (Mx N (t : Gamma0 N)) * HeckeEis.alphaMat ℓ) * alphaAdj ℓ
      = (ℓ : ℤ) • (alphaAdj ℓ * HeckeEis.heckeConjMat ℓ (Mx N (t : Gamma0 N))) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, alphaMat_mul_alphaAdj, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
  have rhs : alphaAdj ℓ * (HeckeEis.alphaMat ℓ * Mx N (t : Gamma0 N)) * alphaAdj ℓ
      = (ℓ : ℤ) • (Mx N (t : Gamma0 N) * alphaAdj ℓ) := by
    rw [← Matrix.mul_assoc, alphaAdj_mul_alphaMat, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
  have e : (ℓ : ℤ) • (alphaAdj ℓ * HeckeEis.heckeConjMat ℓ (Mx N (t : Gamma0 N)))
      = (ℓ : ℤ) • (Mx N (t : Gamma0 N) * alphaAdj ℓ) := by
    rw [← lhs, ← rhs, key]
  exact smul_right_injective (Matrix (Fin 2) (Fin 2) ℤ) hℓ e

noncomputable def beta (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : Matrix (Fin 2) (Fin 2) ℤ :=
  HeckeEis.alphaMat ℓ * Mx N (q.out)⁻¹

omit [NeZero ℓ] in
theorem det_beta (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : (beta N ℓ q).det = (ℓ : ℤ) := by
  rw [beta, Matrix.det_mul, HeckeEis.det_alphaMat, det_Mx, mul_one]

theorem det_beta_ne_zero (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : (beta N ℓ q).det ≠ 0 := by
  rw [det_beta]; exact Int.natCast_ne_zero.mpr (NeZero.ne ℓ)

theorem det_beta_pos (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : 0 < (beta N ℓ q).det := by
  rw [det_beta]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

omit [NeZero ℓ] in

theorem adjugate_beta (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) :
    (beta N ℓ q).adjugate = Mx N q.out * alphaAdj ℓ := by
  rw [beta, Matrix.adjugate_mul_distrib, adjugate_alphaMat, adjugate_Mx_inv]

omit [NeZero ℓ] in

theorem Mx_transferAux (g : Gamma0 N) (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) :
    Mx N (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q : Gamma0 N) = Mx N (g • q).out⁻¹ * Mx N g * Mx N q.out := by
  rw [HeckeEis.coe_transferAux, Mx_mul, Mx_mul, Matrix.mul_assoc]

theorem beta_smul_mul (g : Gamma0 N) (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) :
    beta N ℓ (g • q) * Mx N g
      = Mx N (HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q)) * beta N ℓ q := by
  have key := HeckeEis.heckeConjMat_mul_alphaMat
    ((HeckeEis.mem_heckeUpper N ℓ).mp (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q).2)
  have key' : HeckeEis.heckeConjMat ℓ (Mx N (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q : Gamma0 N))
      * HeckeEis.alphaMat ℓ = HeckeEis.alphaMat ℓ * (Mx N (g • q).out⁻¹ * Mx N g * Mx N q.out) := by
    rw [← Mx_transferAux]; exact key
  change _ = HeckeEis.heckeConjMat ℓ (Mx N (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q : Gamma0 N))
    * (HeckeEis.alphaMat ℓ * _)
  rw [← Matrix.mul_assoc, key', beta]
  simp only [Matrix.mul_assoc, Mx_mul_inv_self, Matrix.mul_one]

theorem adjugate_beta_smul_mul (g : Gamma0 N) (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) :
    (beta N ℓ (g • q)).adjugate * Mx N (HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q))
      = Mx N g * (beta N ℓ q).adjugate := by
  rw [adjugate_beta, adjugate_beta, Matrix.mul_assoc, alphaAdj_mul_heckeConj, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Mx_transferAux, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Mx_mul_inv_self, Matrix.one_mul]

noncomputable def betaGL (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : GL (Fin 2) ℝ :=
  glOf (beta N ℓ q) (det_beta_ne_zero N ℓ q)

theorem det_betaGL_pos (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) : 0 < ((betaGL N ℓ q).det : ℝ) := by
  rw [betaGL, det_glOf]; exact_mod_cast det_beta_pos N ℓ q

theorem betaGL_smul_mul (g : Gamma0 N) (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) :
    betaGL N ℓ (g • q) * ((g : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (((HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q) : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) * betaGL N ℓ q := by
  have h1 : (Mx N g).det ≠ 0 := by rw [det_Mx]; exact one_ne_zero
  have h2 : (Mx N (HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q))).det ≠ 0 := by
    rw [det_Mx]; exact one_ne_zero
  rw [betaGL, betaGL, ← glOf_coe_SL _ h1, ← glOf_coe_SL _ h2,
    ← glOf_mul _ _ _ _ (by rw [Matrix.det_mul]; exact mul_ne_zero (det_beta_ne_zero N ℓ _) h1),
    ← glOf_mul _ _ _ _ (by rw [Matrix.det_mul]; exact mul_ne_zero h2 (det_beta_ne_zero N ℓ _))]
  congr 1
  exact beta_smul_mul N ℓ g q

theorem betaGL_smul_smul (g : Gamma0 N) (q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ) (τ : ℍ) :
    betaGL N ℓ (g • q) • ((g : SL(2, ℤ)) • τ)
      = ((HeckeEis.heckeConj N ℓ (HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q) : Gamma0 N) : SL(2, ℤ)) •
          (betaGL N ℓ q • τ) := by
  rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, ← mul_smul, ← mul_smul, betaGL_smul_mul]

end Beta

section Transform

variable (N ℓ : ℕ) [NeZero ℓ] (n : ℕ)

noncomputable abbrev rho : Representation ℂ (Gamma0 N) ↥(HeckeEis.BinaryForm ℂ n) :=
  (HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype

noncomputable def heckeTransform (F : ℍ → ↥(HeckeEis.BinaryForm ℂ n)) : ℍ → ↥(HeckeEis.BinaryForm ℂ n) :=
  fun τ =>
    letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ,
      HeckeEis.binaryFormRep ℂ n (beta N ℓ q).adjugate (F (betaGL N ℓ q • τ))

variable {N ℓ n}

theorem heckeTransform_smul_sub (F : ℍ → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEquivariantPrimitiveWith (rho N n) F) (g : Gamma0 N) (τ : ℍ) :
    heckeTransform N ℓ n F ((g : SL(2, ℤ)) • τ) - rho N n g (heckeTransform N ℓ n F τ)
      = HeckeEis.coeffHeckeFun N ℓ (rho N n) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) hF.cocycle g := by
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  rw [HeckeEis.coeffHeckeFun_apply, heckeTransform, heckeTransform, map_sum]

  rw [← (Fintype.sum_bijective (g • ·) (MulAction.bijective g)
    (fun q => HeckeEis.binaryFormRep ℂ n (beta N ℓ (g • q)).adjugate (F (betaGL N ℓ (g • q) • ((g : SL(2, ℤ)) • τ))))
    _ (fun q => rfl))]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  set t := HeckeEis.transferAux (HeckeEis.heckeUpper N ℓ) g q with ht
  set c : Gamma0 N := HeckeEis.heckeConj N ℓ t with hc
  rw [betaGL_smul_smul, hF.apply_smul c, map_add]

  have h1 : HeckeEis.binaryFormRep ℂ n (beta N ℓ (g • q)).adjugate ((rho N n) c (F (betaGL N ℓ q • τ)))
      = (rho N n) g (HeckeEis.binaryFormRep ℂ n (beta N ℓ q).adjugate (F (betaGL N ℓ q • τ))) := by
    change HeckeEis.binaryFormRep ℂ n (beta N ℓ (g • q)).adjugate
        (HeckeEis.binaryFormRepSL ℂ n (c : SL(2, ℤ)) (F (betaGL N ℓ q • τ)))
      = HeckeEis.binaryFormRepSL ℂ n (g : SL(2, ℤ)) (HeckeEis.binaryFormRep ℂ n (beta N ℓ q).adjugate (F (betaGL N ℓ q • τ)))
    rw [HeckeEis.binaryFormRepSL_apply_eq_binaryFormRep, HeckeEis.binaryFormRepSL_apply_eq_binaryFormRep,
      ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hc, ht, adjugate_beta_smul_mul]
  have h2 : HeckeEis.binaryFormRep ℂ n (beta N ℓ (g • q)).adjugate (hF.cocycle c)
      = (rho N n) (g • q).out (HeckeEis.binaryFormAlphaAdj ℂ n ℓ (hF.cocycle c)) := by
    change _ = HeckeEis.binaryFormRepSL ℂ n (((g • q).out : Gamma0 N) : SL(2, ℤ)) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ (hF.cocycle c))
    rw [HeckeEis.binaryFormRepSL_apply_eq_binaryFormRep, HeckeEis.binaryFormAlphaAdj_eq_binaryFormRep,
      ← Module.End.mul_apply, ← map_mul, adjugate_beta]
    rfl
  rw [h1, h2, add_sub_cancel_right]

theorem isEquivariantPrimitiveWith_heckeTransform (F : ℍ → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEquivariantPrimitiveWith (rho N n) F) :
    HeckeEis.IsEquivariantPrimitiveWith (rho N n) (heckeTransform N ℓ n F) :=
  fun g => ⟨_, fun τ => heckeTransform_smul_sub F hF g τ⟩

theorem cocycle_heckeTransform (F : ℍ → ↥(HeckeEis.BinaryForm ℂ n))
    (hF : HeckeEis.IsEquivariantPrimitiveWith (rho N n) F) :
    (isEquivariantPrimitiveWith_heckeTransform (ℓ := ℓ) F hF).cocycle
      = HeckeEis.coeffHeckeFun N ℓ (rho N n) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) hF.cocycle := by
  funext g
  exact heckeTransform_smul_sub F hF g UpperHalfPlane.I

end Transform

section Analytic

variable {n : ℕ}

theorem isEichlerIntegral_sum {ι : Type*} (s : Finset ι) {g : ι → ℍ → ℂ}
    {G : ι → ℍ → ↥(HeckeEis.BinaryForm ℂ n)} (h : ∀ i ∈ s, HeckeEis.IsEichlerIntegral n (g i) (G i)) :
    HeckeEis.IsEichlerIntegral n (∑ i ∈ s, g i) (fun τ => ∑ i ∈ s, G i τ) := by
  intro d τ
  have hsum := HasDerivAt.fun_sum (u := s) (fun i hi => h i hi d τ)
  simp only [← Finset.sum_mul] at hsum
  refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv ?_
  · simp only [Submodule.coe_sum, MvPolynomial.coeff_sum]
  · rw [Finset.sum_apply]

variable {N ℓ : ℕ} [NeZero ℓ]

theorem isEichlerIntegral_heckeTransform {f : ℍ → ℂ} {F : ℍ → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) :
    letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    HeckeEis.IsEichlerIntegral n (∑ q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ, f ∣[((n : ℤ) + 2)] betaGL N ℓ q)
      (heckeTransform N ℓ n F) := by
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  refine isEichlerIntegral_sum (Finset.univ : Finset (Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ)) fun q _ => ?_
  exact hF.binarySubst_adjugate_comp_smul (det_beta_pos N ℓ q) (coe_glOf _ _)

end Analytic

section Cosets

variable (N : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (k : ℤ)

def uMat (ℓ : ℕ) (b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, b; 0, (ℓ : ℤ)]

theorem det_uMat (ℓ : ℕ) (b : ℤ) : (uMat ℓ b).det = ℓ := by
  rw [uMat, Matrix.det_fin_two_of]; ring

theorem T_zpow_mul_uMat (ℓ : ℕ) (c b : ℤ) :
    ((ModularGroup.T ^ c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * uMat ℓ b = uMat ℓ (b + c * ℓ) := by
  rw [ModularGroup.coe_T_zpow, uMat, uMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {N k}
variable (f : ℍ → ℂ) (hf : ∀ γ ∈ Gamma0 N, f ∣[k] (γ : SL(2, ℤ)) = f)
include hf

omit hℓ hℓN in

theorem slash_glOf_Mx_mul (γ : Gamma0 N) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det ≠ 0)
    (h : (Mx N γ * B).det ≠ 0) :
    f ∣[k] glOf (Mx N γ * B) h = f ∣[k] glOf B hB := by
  have h1 : (Mx N γ).det ≠ 0 := by rw [det_Mx]; exact one_ne_zero
  rw [glOf_mul _ _ h1 hB, SlashAction.slash_mul, glOf_coe_SL, ← ModularForm.SL_slash, hf _ γ.2]

omit hℓ hℓN in

theorem slash_uMat_eq_of_dvd (b b' : ℤ) (hbb : (ℓ : ℤ) ∣ b - b') (h : (uMat ℓ b).det ≠ 0) (h' : (uMat ℓ b').det ≠ 0) :
    f ∣[k] glOf (uMat ℓ b) h = f ∣[k] glOf (uMat ℓ b') h' := by
  obtain ⟨c, hc⟩ := hbb
  have hT : (ModularGroup.T ^ c : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp
  have e : uMat ℓ b = Mx N ⟨ModularGroup.T ^ c, hT⟩ * uMat ℓ b' := by
    change uMat ℓ b = ((ModularGroup.T ^ c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * uMat ℓ b'
    rw [T_zpow_mul_uMat]; congr 1; linear_combination hc
  have h2 : (Mx N ⟨ModularGroup.T ^ c, hT⟩ * uMat ℓ b').det ≠ 0 := by rw [← e]; exact h
  calc f ∣[k] glOf (uMat ℓ b) h = f ∣[k] glOf (Mx N ⟨ModularGroup.T ^ c, hT⟩ * uMat ℓ b') h2 := by
          congr 1; exact Units.ext (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ)) e)
    _ = f ∣[k] glOf (uMat ℓ b') h' := slash_glOf_Mx_mul f hf _ _ h' h2

omit hℓ hℓN in

theorem slash_glOf_alphaMat_mul_inv (γ : Gamma0 N) (h : Gamma0 N) (hh : h ∈ HeckeEis.heckeUpper N ℓ) [NeZero ℓ]
    (h1 : (HeckeEis.alphaMat ℓ * Mx N (γ * h)⁻¹).det ≠ 0) (h2 : (HeckeEis.alphaMat ℓ * Mx N γ⁻¹).det ≠ 0) :
    f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N (γ * h)⁻¹) h1 = f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N γ⁻¹) h2 := by
  have hh' : h⁻¹ ∈ HeckeEis.heckeUpper N ℓ := inv_mem hh
  have key := HeckeEis.heckeConjMat_mul_alphaMat ((HeckeEis.mem_heckeUpper N ℓ).mp hh')

  have e : HeckeEis.alphaMat ℓ * Mx N (γ * h)⁻¹
      = Mx N (HeckeEis.heckeConj N ℓ ⟨h⁻¹, hh'⟩) * (HeckeEis.alphaMat ℓ * Mx N γ⁻¹) := by
    change _ = HeckeEis.heckeConjMat ℓ (Mx N h⁻¹) * (HeckeEis.alphaMat ℓ * Mx N γ⁻¹)
    rw [← Matrix.mul_assoc, key, _root_.mul_inv_rev, Mx_mul, Matrix.mul_assoc]
  have h3 : (Mx N (HeckeEis.heckeConj N ℓ ⟨h⁻¹, hh'⟩) * (HeckeEis.alphaMat ℓ * Mx N γ⁻¹)).det ≠ 0 := by rw [← e]; exact h1
  calc f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N (γ * h)⁻¹) h1
      = f ∣[k] glOf (Mx N (HeckeEis.heckeConj N ℓ ⟨h⁻¹, hh'⟩) * (HeckeEis.alphaMat ℓ * Mx N γ⁻¹)) h3 := by
          congr 1; exact Units.ext (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ)) e)
    _ = f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N γ⁻¹) h2 := slash_glOf_Mx_mul f hf _ _ h2 h3

end Cosets

section Transversal

variable (N : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
include hℓ hℓN

theorem exists_bezout : ∃ uv : ℤ × ℤ, uv.1 * ℓ + uv.2 * N = 1 := by
  obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.mpr (hℓ.coprime_iff_not_dvd.mpr hℓN)
  exact ⟨(u, v), h⟩

noncomputable def bez : ℤ × ℤ := (exists_bezout N hℓ hℓN).choose

theorem bez_spec : (bez N hℓ hℓN).1 * ℓ + (bez N hℓ hℓN).2 * N = 1 := (exists_bezout N hℓ hℓN).choose_spec

noncomputable def gInf : Gamma0 N :=
  ⟨⟨!![(bez N hℓ hℓN).1, -(bez N hℓ hℓN).2; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination bez_spec N hℓ hℓN⟩, by
    rw [Gamma0_mem]; simp⟩

noncomputable def gOne : Gamma0 N :=
  ⟨⟨!![1, (bez N hℓ hℓN).2; -(N : ℤ), (bez N hℓ hℓN).1 * ℓ], by
    rw [Matrix.det_fin_two_of]; linear_combination bez_spec N hℓ hℓN⟩, by
    rw [Gamma0_mem]; simp⟩

theorem Mx_gInf_inv : Mx N (gInf N hℓ hℓN)⁻¹ = !![(ℓ : ℤ), (bez N hℓ hℓN).2; -(N : ℤ), (bez N hℓ hℓN).1] := by
  change (((gInf N hℓ hℓN : Gamma0 N) : SL(2, ℤ))⁻¹ : SL(2, ℤ)).1 = _
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j; fin_cases i <;> fin_cases j <;> simp [gInf]

theorem alphaMat_mul_Mx_gInf_inv :
    HeckeEis.alphaMat ℓ * Mx N (gInf N hℓ hℓN)⁻¹ = Mx N (gOne N hℓ hℓN) * alphaAdj ℓ := by
  rw [Mx_gInf_inv, HeckeEis.alphaMat, alphaAdj]
  change !![1, 0; 0, (ℓ : ℤ)] * _ = !![1, (bez N hℓ hℓN).2; -(N : ℤ), (bez N hℓ hℓN).1 * ℓ] * _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

omit hℓ hℓN in
theorem T_zpow_mem_Gamma0 (j : ℤ) : (ModularGroup.T ^ j : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp

def gT (j : ℤ) : Gamma0 N := ⟨ModularGroup.T ^ j, T_zpow_mem_Gamma0 N j⟩

omit hℓ hℓN in
theorem alphaMat_mul_Mx_gT_inv (ℓ : ℕ) (j : ℤ) :
    HeckeEis.alphaMat ℓ * Mx N (gT N j)⁻¹ = uMat ℓ (-j) := by
  have : Mx N (gT N j)⁻¹ = ((ModularGroup.T ^ (-j) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    change (((ModularGroup.T ^ j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [_root_.zpow_neg]
  rw [this, ModularGroup.coe_T_zpow, HeckeEis.alphaMat, uMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def rep : Option (Fin ℓ) → Gamma0 N
  | none => gInf N hℓ hℓN
  | some j => gT N (j : ℤ)

omit hℓ hℓN in

theorem mem_heckeUpper_iff_cast (x : Gamma0 N) :
    x ∈ HeckeEis.heckeUpper N ℓ ↔ (((Mx N x) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [HeckeEis.mem_heckeUpper, ZMod.intCast_zmod_eq_zero_iff_dvd]

omit hℓ hℓN in
theorem cast_ell_eq_zero : ((ℓ : ℤ) : ZMod ℓ) = 0 := by simp

theorem cast_bez_snd_ne_zero : (((bez N hℓ hℓN).2 : ℤ) : ZMod ℓ) ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro h0
  have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) (bez_spec N hℓ hℓN)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, zero_add, h0,
    zero_mul, Int.cast_one] at h
  exact zero_ne_one h

theorem exists_rep_inv_mul_mem (γ : Gamma0 N) :
    ∃ o : Option (Fin ℓ), (rep N hℓ hℓN o)⁻¹ * γ ∈ HeckeEis.heckeUpper N ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  set a : ℤ := Mx N γ 0 0
  set b : ℤ := Mx N γ 0 1
  set c : ℤ := Mx N γ 1 0
  set d : ℤ := Mx N γ 1 1
  have hγ : Mx N γ = !![a, b; c, d] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  by_cases hd : ((d : ℤ) : ZMod ℓ) = 0
  · refine ⟨none, ?_⟩
    rw [mem_heckeUpper_iff_cast, Mx_mul]
    rw [show rep N hℓ hℓN none = gInf N hℓ hℓN from rfl, Mx_gInf_inv, hγ]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  ·
    set jz : ZMod ℓ := (b : ZMod ℓ) * ((d : ℤ) : ZMod ℓ)⁻¹ with hjz
    refine ⟨some ⟨jz.val, ZMod.val_lt jz⟩, ?_⟩
    rw [mem_heckeUpper_iff_cast, Mx_mul]
    have hinv : Mx N (gT N ((⟨jz.val, ZMod.val_lt jz⟩ : Fin ℓ) : ℤ))⁻¹
        = ((ModularGroup.T ^ (-(jz.val : ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      change (((ModularGroup.T ^ ((jz.val : ℕ) : ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
      rw [_root_.zpow_neg]
    rw [show rep N hℓ hℓN (some ⟨jz.val, ZMod.val_lt jz⟩) = gT N ((⟨jz.val, ZMod.val_lt jz⟩ : Fin ℓ) : ℤ) from rfl,
      hinv, ModularGroup.coe_T_zpow, hγ]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul]
    push_cast
    rw [ZMod.natCast_zmod_val, hjz, neg_mul, mul_assoc, inv_mul_cancel₀ hd, mul_one, add_neg_cancel]

theorem rep_injective_mod (o o' : Option (Fin ℓ))
    (h : (rep N hℓ hℓN o)⁻¹ * rep N hℓ hℓN o' ∈ HeckeEis.heckeUpper N ℓ) : o = o' := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hinvInf := Mx_gInf_inv N hℓ hℓN
  have hinvT : ∀ j : ℤ, Mx N (gT N j)⁻¹ = ((ModularGroup.T ^ (-j) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    intro j
    change (((ModularGroup.T ^ j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [_root_.zpow_neg]
  have hv := cast_bez_snd_ne_zero N hℓ hℓN
  rw [mem_heckeUpper_iff_cast, Mx_mul] at h
  rcases o with _ | j <;> rcases o' with _ | j'
  · rfl
  · exfalso
    rw [show rep N hℓ hℓN none = gInf N hℓ hℓN from rfl,
      show rep N hℓ hℓN (some j') = gT N (j' : ℤ) from rfl, hinvInf] at h
    change ((((!![(ℓ : ℤ), (bez N hℓ hℓN).2; -(N : ℤ), (bez N hℓ hℓN).1]
      * ((ModularGroup.T ^ ((j' : ℕ) : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 : ℤ) : ZMod ℓ)) = 0 at h
    rw [ModularGroup.coe_T_zpow] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact hv h
  · exfalso
    rw [show rep N hℓ hℓN none = gInf N hℓ hℓN from rfl,
      show rep N hℓ hℓN (some j) = gT N (j : ℤ) from rfl, hinvT] at h
    change (((((ModularGroup.T ^ (-((j : ℕ) : ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      * !![(bez N hℓ hℓN).1, -(bez N hℓ hℓN).2; (N : ℤ), (ℓ : ℤ)]) 0 1 : ℤ) : ZMod ℓ) = 0 at h
    rw [ModularGroup.coe_T_zpow] at h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    exact hv h
  · rw [show rep N hℓ hℓN (some j) = gT N (j : ℤ) from rfl,
      show rep N hℓ hℓN (some j') = gT N (j' : ℤ) from rfl, hinvT] at h
    change (((((ModularGroup.T ^ (-((j : ℕ) : ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      * ((ModularGroup.T ^ ((j' : ℕ) : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 : ℤ) : ZMod ℓ) = 0 at h
    rw [ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow] at h
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, one_mul, mul_one, Int.cast_add, Int.cast_neg, Int.cast_natCast] at h

    have h' : ((j' : ℕ) : ZMod ℓ) = ((j : ℕ) : ZMod ℓ) := by linear_combination h
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
    rw [Nat.mod_eq_of_lt j'.2, Nat.mod_eq_of_lt j.2] at hmod
    exact congrArg some (Fin.ext hmod).symm

end Transversal

section SumIdentity

variable (N : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (k : ℤ)
  (f : ℍ → ℂ) (hf : ∀ γ ∈ Gamma0 N, f ∣[k] (γ : SL(2, ℤ)) = f)

include hℓ hℓN in

theorem rep_mk_bijective [NeZero ℓ] :
    Function.Bijective (fun o : Option (Fin ℓ) =>
      (QuotientGroup.mk (rep N hℓ hℓN o) : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ)) := by
  refine ⟨fun o o' h => rep_injective_mod N hℓ hℓN o o' (QuotientGroup.eq.mp h), fun q => ?_⟩
  obtain ⟨o, ho⟩ := exists_rep_inv_mul_mem N hℓ hℓN q.out
  exact ⟨o, (QuotientGroup.eq.mpr ho).trans q.out_eq'⟩

theorem glOf_uMat_natCast [NeZero ℓ] (j : ℕ) (h : (uMat ℓ (j : ℤ)).det ≠ 0) :
    glOf (uMat ℓ (j : ℤ)) h = ModularForm.heckeMatrix ℓ j := by
  refine Units.ext ?_
  rw [coe_glOf, ModularForm.val_heckeMatrix (NeZero.ne ℓ)]
  ext i i'; fin_cases i <;> fin_cases i' <;> simp [uMat]

theorem glOf_alphaAdj [NeZero ℓ] (h : (alphaAdj ℓ).det ≠ 0) :
    glOf (alphaAdj ℓ) h = ModularForm.heckeDiagMatrix ℓ := by
  refine Units.ext ?_
  rw [coe_glOf, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ)]
  ext i i'; fin_cases i <;> fin_cases i' <;> simp [alphaAdj]

theorem det_uMat_ne_zero [NeZero ℓ] (b : ℤ) : (uMat ℓ b).det ≠ 0 := by
  rw [det_uMat]; exact Int.natCast_ne_zero.mpr (NeZero.ne ℓ)

noncomputable def Ub [NeZero ℓ] (b : ℤ) : ℍ → ℂ := f ∣[k] glOf (uMat ℓ b) (det_uMat_ne_zero b)

noncomputable def Wz [NeZero ℓ] (z : ZMod ℓ) : ℍ → ℂ := Ub (ℓ := ℓ) k f (z.val : ℤ)

include hf in
theorem Ub_eq_Wz [NeZero ℓ] (b : ℤ) : Ub (ℓ := ℓ) k f b = Wz k f (b : ZMod ℓ) := by
  unfold Wz Ub
  refine slash_uMat_eq_of_dvd f hf b _ ⟨b / ℓ, ?_⟩ _ _
  rw [ZMod.val_intCast, Int.emod_def]; ring

theorem natCast_zmod_bijective [NeZero ℓ] : Function.Bijective (fun j : Fin ℓ => ((j : ℕ) : ZMod ℓ)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun j j' h => ?_, by simp [ZMod.card]⟩
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt j'.2] at hmod
  exact Fin.ext hmod

include hf in

theorem sum_Ub_neg [NeZero ℓ] :
    ∑ j : Fin ℓ, Ub (ℓ := ℓ) k f (-((j : ℕ) : ℤ)) = ModularForm.heckeU k ℓ f := by
  have h1 : ∀ j : Fin ℓ, Ub (ℓ := ℓ) k f (-((j : ℕ) : ℤ)) = Wz k f (-(((j : ℕ) : ZMod ℓ))) := by
    intro j; rw [Ub_eq_Wz N k f hf]; push_cast; rfl
  have h2 : ∀ j : Fin ℓ, Wz k f (((j : ℕ) : ZMod ℓ)) = f ∣[k] ModularForm.heckeMatrix ℓ j := by
    intro j
    unfold Wz Ub
    rw [← glOf_uMat_natCast (j : ℕ) (det_uMat_ne_zero _)]
    congr 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.2]
  calc ∑ j : Fin ℓ, Ub (ℓ := ℓ) k f (-((j : ℕ) : ℤ))
      = ∑ j : Fin ℓ, Wz k f (-(((j : ℕ) : ZMod ℓ))) := Fintype.sum_congr _ _ h1
    _ = ∑ z : ZMod ℓ, Wz k f (-z) :=
          Fintype.sum_bijective _ (natCast_zmod_bijective (ℓ := ℓ)) _ (fun z => Wz k f (-z)) (fun _ => rfl)
    _ = ∑ z : ZMod ℓ, Wz k f z := Equiv.sum_comp (Equiv.neg (ZMod ℓ)) (Wz k f)
    _ = ∑ j : Fin ℓ, Wz k f (((j : ℕ) : ZMod ℓ)) :=
          (Fintype.sum_bijective _ (natCast_zmod_bijective (ℓ := ℓ)) _ (Wz k f) (fun _ => rfl)).symm
    _ = ∑ j : Fin ℓ, f ∣[k] ModularForm.heckeMatrix ℓ j := Fintype.sum_congr _ _ h2
    _ = ModularForm.heckeU k ℓ f := by
          rw [ModularForm.heckeU_def, ← Fin.sum_univ_eq_sum_range]

include hℓ hℓN hf in

theorem sum_slash_betaGL [NeZero ℓ] :
    letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ HeckeEis.heckeUpper N ℓ, f ∣[k] betaGL N ℓ q = ModularForm.heckeT k ℓ f := by
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  have hdet : ∀ γ : Gamma0 N, (HeckeEis.alphaMat ℓ * Mx N γ⁻¹).det ≠ 0 := by
    intro γ; rw [Matrix.det_mul, HeckeEis.det_alphaMat, det_Mx, mul_one]; exact Int.natCast_ne_zero.mpr (NeZero.ne ℓ)

  rw [← Fintype.sum_bijective _ (rep_mk_bijective N hℓ hℓN)
    (fun o => f ∣[k] betaGL N ℓ (QuotientGroup.mk (rep N hℓ hℓN o))) _ (fun o => rfl)]

  have hterm : ∀ o : Option (Fin ℓ), f ∣[k] betaGL N ℓ (QuotientGroup.mk (rep N hℓ hℓN o))
      = f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N (rep N hℓ hℓN o)⁻¹) (hdet _) := by
    intro o
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (HeckeEis.heckeUpper N ℓ) (rep N hℓ hℓN o)
    have h1 : (HeckeEis.alphaMat ℓ * Mx N (rep N hℓ hℓN o * h)⁻¹).det ≠ 0 := hdet _
    have e : betaGL N ℓ (QuotientGroup.mk (rep N hℓ hℓN o)) = glOf (HeckeEis.alphaMat ℓ * Mx N (rep N hℓ hℓN o * h)⁻¹) h1 :=
      Units.ext (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ)) (by rw [beta, hh]))
    rw [e]
    exact slash_glOf_alphaMat_mul_inv f hf (rep N hℓ hℓN o) h h.2 h1 (hdet _)
  rw [Fintype.sum_congr _ _ hterm, Fintype.sum_option, ModularForm.heckeT_eq_heckeU_add, add_comm]
  congr 1
  ·
    have hj : ∀ j : Fin ℓ, f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N (rep N hℓ hℓN (some j))⁻¹) (hdet _)
        = Ub (ℓ := ℓ) k f (-((j : ℕ) : ℤ)) := by
      intro j
      unfold Ub
      congr 1
      exact Units.ext (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ))
        (alphaMat_mul_Mx_gT_inv N ℓ (j : ℤ)))
    rw [Fintype.sum_congr _ _ hj, sum_Ub_neg N k f hf]
  ·
    have h1 : (Mx N (gOne N hℓ hℓN) * alphaAdj ℓ).det ≠ 0 := by rw [← alphaMat_mul_Mx_gInf_inv]; exact hdet _
    have hA : (alphaAdj ℓ).det ≠ 0 := by
      rw [alphaAdj, Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]
    calc f ∣[k] glOf (HeckeEis.alphaMat ℓ * Mx N (rep N hℓ hℓN none)⁻¹) (hdet _)
        = f ∣[k] glOf (Mx N (gOne N hℓ hℓN) * alphaAdj ℓ) h1 := by
            congr 1
            exact Units.ext (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ))
              (alphaMat_mul_Mx_gInf_inv N hℓ hℓN))
      _ = f ∣[k] glOf (alphaAdj ℓ) hA := slash_glOf_Mx_mul f hf _ _ hA h1
      _ = f ∣[k] ModularForm.heckeDiagMatrix ℓ := by rw [glOf_alphaAdj]

end SumIdentity

end R1TPH
p2m_reactivate "P2MW.S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm.R1TPH"

open R1TPH in

theorem solution (N : ℕ) [NeZero N] (n : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N)
    (T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ]
      HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeEis.IsCoeffHeckeOnH1 N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) T)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
    (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (F' : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n))
    (hEI' : HeckeEis.IsEichlerIntegral n (ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f) F')
    (hF' : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F') :
    T (HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩) =
      HeckeEis.coeffH1Mk ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        ⟨hF'.cocycle, hF'.cocycle_mem_coeffCocycles⟩ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  have hf : ∀ γ ∈ Gamma0 N, (⇑f) ∣[((n : ℤ) + 2)] (γ : SL(2, ℤ)) = ⇑f := fun γ hγ =>
    SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)

  have hFT : HeckeEis.IsEichlerIntegral n (⇑(ModularForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f)) (heckeTransform N ℓ n F) := by
    have h := isEichlerIntegral_heckeTransform (N := N) (ℓ := ℓ) hEI
    rw [sum_slash_betaGL N hℓ hℓN ((n : ℤ) + 2) (⇑f) hf] at h
    rwa [← ModularForm.coe_heckeTLin_apply ((n : ℤ) + 2) hℓ hℓN f] at h
  have hFTeq := isEquivariantPrimitiveWith_heckeTransform (ℓ := ℓ) F hF
  have hcoc := cocycle_heckeTransform (ℓ := ℓ) F hF

  obtain ⟨w, hw1, hw2⟩ := hT ⟨hF.cocycle, hF.cocycle_mem_coeffCocycles⟩
  have hw : w = ⟨hFTeq.cocycle, hFTeq.cocycle_mem_coeffCocycles⟩ := Subtype.ext (hw1.trans hcoc.symm)
  rw [hw2, hw]

  obtain ⟨v, hv⟩ := hFT.exists_sub_eq_const hEI'
  have hcob := hFTeq.cocycle_sub_cocycle_mem_coeffCoboundaries hF' hv
  exact (Submodule.Quotient.eq _).mpr hcob

end S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm
end P2MW
export P2MW.S_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm (solution)
