-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/df2db858-3014-5fbc-bbb2-302ebfb56969

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B1bCellGodement

variable (p : HeightOneSpectrum (𝓞 ℚ))

def topRows (Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) :=
  Matrix.of fun i k => Y (Fin.castSucc i) k

def leftBlock (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
  Matrix.of fun i j => Z i (Fin.castSucc j)

def rowpad (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) :=
  Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ) (fun k' : Fin 2 => h i k') k

theorem rowpad_apply_zero (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (i : Fin 2) : rowpad p h i 0 = h i 0 := rfl
theorem rowpad_apply_one (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (i : Fin 2) : rowpad p h i 1 = h i 1 := rfl
theorem rowpad_apply_two (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (i : Fin 2) : rowpad p h i 2 = 0 := rfl

theorem rowpad_mul (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :
    rowpad p h * Y = h * topRows p Y := by
  ext i k
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, rowpad_apply_zero, rowpad_apply_one,
    rowpad_apply_two, topRows, Matrix.of_apply, zero_mul, add_zero]
  rfl

theorem topRows_mul (A B : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :
    topRows p (A * B) = topRows p A * B := by
  ext i k
  simp only [topRows, Matrix.mul_apply, Matrix.of_apply]

theorem leftBlock_mul (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    leftBlock p (h * Z) = h * leftBlock p Z := by
  ext i j
  simp only [leftBlock, Matrix.mul_apply, Matrix.of_apply]

theorem leftBlock_apply (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (i j : Fin 2) :
    leftBlock p Z i j = Z i (Fin.castSucc j) := rfl

theorem det_leftBlock (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    (leftBlock p Z).det = Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 := by
  rw [Matrix.det_fin_two]
  rfl

theorem antidiagonal3_mul_apply (M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) (i j : Fin 3) :
    ((antidiagonal3 p : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * M) i j = M (Fin.rev i) j := by
  rw [antidiagonal3_coe]
  fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem det_antidiagonal3 : ((antidiagonal3 p : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)).det = -1 := by
  rw [antidiagonal3_coe, Matrix.det_fin_three]
  simp

theorem charExt_inv' (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (x : p.adicCompletion ℚ) :
    charExt χ x⁻¹ = (charExt χ x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [charExt_of_ne_zero χ (inv_ne_zero hx), charExt_of_ne_zero χ hx,
      show Units.mk0 x⁻¹ (inv_ne_zero hx) = (Units.mk0 x hx)⁻¹ from Units.ext (by simp), map_inv, Units.val_inv_eq_inv_val]

theorem norm_eq_modulus (x : p.adicCompletion ℚ) : ((modulus x : ℝ)) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem antidiagonal2_mul_apply_one (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (j : Fin 3) :
    (((antidiagonal2 p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z) 1 j = Z 0 j := by
  rw [antidiagonal2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_antidiagonal2_val :
    (((Matrix.GeneralLinearGroup.det (antidiagonal2 p) : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact gl2Det_antidiagonal2 p

theorem minor02_mul (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) (Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) :
    (h * Z) 0 0 * (h * Z) 1 2 - (h * Z) 0 2 * (h * Z) 1 0 = h.det * (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem cpow_half_threeHalves (m : ℝ) (hm : 0 < m) :
    ((m⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((m : ℝ) : ℂ) ^ (3 / 2 : ℂ) = (m : ℂ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (inv_pos.mpr hm).le, ← Complex.ofReal_cpow hm.le, ← Complex.ofReal_mul,
    Real.inv_rpow hm.le, ← Real.rpow_neg hm.le, ← Real.rpow_add hm]
  norm_num

theorem w0_entry (Y T : LocalGL3 p) (i j : Fin 3) :
    ((antidiagonal3 p * Y * T : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      ((Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) (Fin.rev i) j := by
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact antidiagonal3_mul_apply p _ i j

theorem cellSectionOf_w0 (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ)
    (Y T : LocalGL3 p) (M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
    (hM : M = (Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :
    cellSectionOf p lam Φ (antidiagonal3 p * Y * T) =
      ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
      (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
      ((charExt (lam 0) (M 0 0 * M 1 1 - M 0 1 * M 1 0))⁻¹ * ((‖M 0 0 * M 1 1 - M 0 1 * M 1 0‖⁻¹ : ℝ) : ℂ) *
        charExt (lam 1) (-(M 0 0 * M 1 1 - M 0 1 * M 1 0) / M 0 0) *
        charExt (lam 2) (M 0 0) * ((‖M 0 0‖⁻¹ : ℝ) : ℂ) *
        Φ ![M 0 1 / M 0 0, M 0 2 / M 0 0, (M 0 0 * M 1 2 - M 0 2 * M 1 0) / (M 0 0 * M 1 1 - M 0 1 * M 1 0)]) := by
  have he : ∀ i j, gl3Entry p (antidiagonal3 p * Y * T) i j = M (Fin.rev i) j := fun i j => by
    rw [gl3Entry, w0_entry, hM]
  have h20 : gl3Entry p (antidiagonal3 p * Y * T) 2 0 = M 0 0 := he 2 0
  have h21 : gl3Entry p (antidiagonal3 p * Y * T) 2 1 = M 0 1 := he 2 1
  have h22 : gl3Entry p (antidiagonal3 p * Y * T) 2 2 = M 0 2 := he 2 2
  have h10 : gl3Entry p (antidiagonal3 p * Y * T) 1 0 = M 1 0 := he 1 0
  have h11 : gl3Entry p (antidiagonal3 p * Y * T) 1 1 = M 1 1 := he 1 1
  have h12 : gl3Entry p (antidiagonal3 p * Y * T) 1 2 = M 1 2 := he 1 2
  have hcorner : cornerEntry p (antidiagonal3 p * Y * T) = M 0 0 := h20
  have hlower : lowerMinor p (antidiagonal3 p * Y * T) = -(M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
    rw [lowerMinor, h10, h21, h11, h20]; ring
  have houter : outerMinor p (antidiagonal3 p * Y * T) = M 1 0 * M 0 2 - M 1 2 * M 0 0 := by
    rw [outerMinor, h10, h22, h12, h20]
  have hdet : gl3Det p (antidiagonal3 p * Y * T) =
      -(((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) *
        ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) := by
    rw [gl3Det, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_antidiagonal3,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    ring
  have hnY : ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) =
      ((‖((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    rw [norm_eq_modulus]
  have hnT : ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) =
      ((‖((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ : ℝ) : ℂ) := by
    rw [norm_eq_modulus]
  rw [hnY, hnT]
  by_cases hmem : antidiagonal3 p * Y * T ∈ bigCell3 p
  · rw [cellSectionOf_apply_of_mem p lam Φ hmem]
    obtain ⟨hc, hl⟩ := (mem_bigCell3_iff p _).mp hmem
    rw [hcorner] at hc
    rw [hlower] at hl
    have hD : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := fun h => hl (by rw [h, neg_zero])
    have hratio : cellRatio p (antidiagonal3 p * Y * T) =
        ![M 0 1 / M 0 0, M 0 2 / M 0 0, (M 0 0 * M 1 2 - M 0 2 * M 1 0) / (M 0 0 * M 1 1 - M 0 1 * M 1 0)] := by
      have e0 : cellRatio p (antidiagonal3 p * Y * T) 0 = M 0 1 / M 0 0 := by
        show gl3Entry p _ 2 1 / cornerEntry p _ = _; rw [h21, hcorner]
      have e1 : cellRatio p (antidiagonal3 p * Y * T) 1 = M 0 2 / M 0 0 := by
        show gl3Entry p _ 2 2 / cornerEntry p _ = _; rw [h22, hcorner]
      have e2 : cellRatio p (antidiagonal3 p * Y * T) 2 =
          (M 0 0 * M 1 2 - M 0 2 * M 1 0) / (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
        show outerMinor p _ / lowerMinor p _ = _
        rw [houter, hlower, ← neg_div_neg_eq, neg_neg]
        ring
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
    rw [hratio]
    unfold cellValue
    rw [hdet, hlower, hcorner, neg_div_neg_eq]
    have hu : (((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) *
        ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) /
          (M 0 0 * M 1 1 - M 0 1 * M 1 0) =
        (((Matrix.GeneralLinearGroup.det Y * Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ)) :
            p.adicCompletion ℚ) * (M 0 0 * M 1 1 - M 0 1 * M 1 0)⁻¹ := by
      rw [Units.val_mul, div_eq_mul_inv]
    rw [hu, charExt_units_mul, charExt_inv', map_mul, Units.val_mul, norm_mul, Units.val_mul, norm_mul, norm_inv]
    push_cast
    ring
  · rw [cellSectionOf_apply_of_notMem p lam Φ hmem]
    rw [mem_bigCell3_iff, hcorner, hlower, not_and_or] at hmem
    rcases hmem with h | h
    · rw [not_ne_iff] at h
      rw [h, charExt_zero]
      ring
    · rw [not_ne_iff, neg_eq_zero] at h
      rw [h, charExt_zero, inv_zero]
      ring

end B1bCellGodement

open B1bCellGodement in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →
    ∀ Y : LocalGL3 p,
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)) μ₂ ∧
      cellSectionOf p lam Φ (antidiagonal3 p * Y * T) =
        ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) ∂μ₂ ∧
      ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          ‖φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)‖ ∂μ₂ =
        ‖cellSectionOf p lam Φ (antidiagonal3 p * Y * T)‖ *
          (‖((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ)‖ * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)))⁻¹ := by
  intro μ₂ hμ K hKo hKc φsec hφ Y
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  obtain ⟨hsc, hlc, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hsc
  haveI := hlc
  haveI : μ₂.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1
  set M : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ) :=
    (Y : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) with hM
  set Z₀ : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := topRows p M with hZ₀
  set s₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := leftBlock p Z₀ with hs₀
  have hZ : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      (Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
          (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
        : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
        ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
        (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z₀ := by
    intro h
    show rowpad p (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * _ * _ = _
    rw [rowpad_mul, Matrix.mul_assoc, ← topRows_mul]

  set C : ℂ := ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
      (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
      ((charExt (lam 0) s₀.det)⁻¹ * ((‖s₀.det‖⁻¹ : ℝ) : ℂ) *
        charExt (lam 1) (-s₀.det / Z₀ 0 0) * charExt (lam 2) (Z₀ 0 0) * ((‖Z₀ 0 0‖⁻¹ : ℝ) : ℂ) *
        Φ ![Z₀ 0 1 / Z₀ 0 0, Z₀ 0 2 / Z₀ 0 0, (Z₀ 0 0 * Z₀ 1 2 - Z₀ 0 2 * Z₀ 1 0) / s₀.det]) with hC
  clear_value C
  have hpt : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      φsec ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
          (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
            : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
          ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
        (antidiagonal2 p * h⁻¹) *
        ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) =
      (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ))
        ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * s₀) * C := by
    intro h
    rw [hφ]
    dsimp only
    rw [hZ h]
    have hs : (Matrix.of fun i j => (((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z₀) i (Fin.castSucc j)) =
        (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * s₀ := leftBlock_mul p _ _
    have hN : (((antidiagonal2 p * h⁻¹ : GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z₀) =
        ((antidiagonal2 p : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z₀ := by
      rw [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) Z₀,
        Units.inv_mul, Matrix.one_mul]
    rw [hs, hN, antidiagonal2_mul_apply_one, antidiagonal2_mul_apply_one, antidiagonal2_mul_apply_one, minor02_mul,
      Matrix.det_mul, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, Units.val_mul, det_antidiagonal2_val,
      Units.val_inv_eq_inv_val]

    set dh : p.adicCompletion ℚ := ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) with hdh
    have hdh0 : dh ≠ 0 := (Matrix.GeneralLinearGroup.det h).ne_zero
    by_cases hmem : (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * s₀ ∈
        Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))
    · rw [Set.indicator_of_mem hmem]
      have e1 : -1 * dh⁻¹ * (dh * s₀.det) / Z₀ 0 0 = -s₀.det / Z₀ 0 0 := by
        rw [show -1 * dh⁻¹ * (dh * s₀.det) = -s₀.det by field_simp]
      have e2 : dh * (Z₀ 0 0 * Z₀ 1 2 - Z₀ 0 2 * Z₀ 1 0) / (dh * s₀.det) =
          (Z₀ 0 0 * Z₀ 1 2 - Z₀ 0 2 * Z₀ 1 0) / s₀.det := mul_div_mul_left _ _ hdh0
      rw [e1, e2, charExt_units_mul, norm_eq_modulus p (-1 * dh⁻¹), norm_eq_modulus p dh, norm_mul, norm_mul, norm_neg,
        norm_one, one_mul, norm_inv]
      have hn : 0 < ‖dh‖ := norm_pos_iff.mpr hdh0
      have hcp := cpow_half_threeHalves ‖dh‖ hn
      have hl0 : (((lam 0) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hn0 : ((‖dh‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have key : (((lam 0) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)⁻¹ * (((lam 0) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          (((‖dh‖ : ℝ) : ℂ)⁻¹ * (((‖dh‖⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((‖dh‖ : ℝ) : ℂ) ^ (3 / 2 : ℂ))) = 1 := by
        rw [hcp, inv_mul_cancel₀ hl0, inv_mul_cancel₀ hn0, one_mul]
      calc _ = ((((lam 0) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ)⁻¹ * (((lam 0) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          (((‖dh‖ : ℝ) : ℂ)⁻¹ * (((‖dh‖⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * ((‖dh‖ : ℝ) : ℂ) ^ (3 / 2 : ℂ)))) * C := by
            rw [hC]; push_cast; ring
        _ = 1 * C := by rw [key]
    · rw [Set.indicator_of_notMem hmem]
      simp

  haveI : μ₂.IsOpenPosMeasure := inferInstance
  have hKpos : μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ≠ 0 :=
    (hKo.measure_pos μ₂ ⟨1, K.one_mem⟩).ne'
  have hKlt : μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hKc.measure_lt_top
  have hKreal : (((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hKpos hKlt.ne).ne'
  have hsdet : s₀.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_leftBlock p Z₀
  have hF1 : cellSectionOf p lam Φ (antidiagonal3 p * Y * T) =
      ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
      (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
      ((charExt (lam 0) s₀.det)⁻¹ * ((‖s₀.det‖⁻¹ : ℝ) : ℂ) *
        charExt (lam 1) (-s₀.det / Z₀ 0 0) * charExt (lam 2) (Z₀ 0 0) * ((‖Z₀ 0 0‖⁻¹ : ℝ) : ℂ) *
        Φ ![Z₀ 0 1 / Z₀ 0 0, Z₀ 0 2 / Z₀ 0 0, (Z₀ 0 0 * Z₀ 1 2 - Z₀ 0 2 * Z₀ 1 0) / s₀.det]) := by
    rw [hsdet]
    exact cellSectionOf_w0 p lam Φ Y T M hM
  simp_rw [hpt]
  by_cases hdet : s₀.det = 0
  ·
    have hzero : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ))
          ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * s₀) = 0 := by
      intro h
      apply Set.indicator_of_notMem
      rintro ⟨k, -, hkeq⟩
      apply (Matrix.GeneralLinearGroup.det k).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply, hkeq, Matrix.det_mul, hdet, mul_zero]
    simp_rw [hzero, zero_mul]
    have hcs : cellSectionOf p lam Φ (antidiagonal3 p * Y * T) = 0 := by
      rw [hF1, hdet, charExt_zero, inv_zero]
      ring
    refine ⟨integrable_zero _ _ _, ?_, ?_⟩
    · rw [integral_zero, mul_zero, hcs]
    · simp [hcs]
  ·
    set s₁ : GL (Fin 2) (p.adicCompletion ℚ) := Matrix.GeneralLinearGroup.mkOfDetNeZero s₀ hdet with hs₁def
    have hs₁ : (s₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = s₀ := rfl
    set A : Set (GL (Fin 2) (p.adicCompletion ℚ)) := (fun g => g * s₁) ⁻¹' (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) with hA
    have hind : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ))
          ((h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * s₀) * C = A.indicator (fun _ => C) h := by
      intro h
      by_cases hk : h * s₁ ∈ K
      · rw [Set.indicator_of_mem (show h ∈ A from hk), Set.indicator_of_mem, one_mul]
        exact ⟨h * s₁, hk, by rw [Units.val_mul, hs₁]⟩
      · rw [Set.indicator_of_notMem (show h ∉ A from hk), Set.indicator_of_notMem, zero_mul]
        rintro ⟨k, hkK, hkeq⟩
        apply hk
        have : k = h * s₁ := Units.ext (by rw [hkeq, Units.val_mul, hs₁])
        rwa [← this]
    simp_rw [hind]
    have hAmeas : MeasurableSet A := hKc.isClosed.measurableSet.preimage (measurable_mul_const s₁)
    have hμA : μ₂ A = μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) := measure_preimage_mul_right μ₂ s₁ _
    have hAlt : μ₂ A < ⊤ := hμA ▸ hKlt
    have hint : Integrable (A.indicator fun _ => C) μ₂ :=
      (integrableOn_const hAlt.ne).integrable_indicator hAmeas
    have hval : ∫ h, A.indicator (fun _ => C) h ∂μ₂ =
        (((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℝ) : ℂ) * C := by
      rw [integral_indicator_const C hAmeas]
      show (μ₂ A).toReal • C = _
      rw [hμA, Complex.real_smul]
    have hμC : (((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℝ) : ℂ) * C =
        (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
        ((charExt (lam 0) s₀.det)⁻¹ * ((‖s₀.det‖⁻¹ : ℝ) : ℂ) *
          charExt (lam 1) (-s₀.det / Z₀ 0 0) * charExt (lam 2) (Z₀ 0 0) * ((‖Z₀ 0 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![Z₀ 0 1 / Z₀ 0 0, Z₀ 0 2 / Z₀ 0 0, (Z₀ 0 0 * Z₀ 1 2 - Z₀ 0 2 * Z₀ 1 0) / s₀.det]) := by
      rw [hC, show ∀ (x y z : ℂ), x * (x⁻¹ * y * z) = (x * x⁻¹) * y * z from fun x y z => by ring, mul_inv_cancel₀ hKreal,
        one_mul]
    refine ⟨hint, ?_, ?_⟩
    · rw [hval, hμC, hF1]
      ring
    · simp_rw [norm_indicator_eq_indicator_norm]
      rw [integral_indicator_const _ hAmeas]
      show (μ₂ A).toReal • ‖C‖ = _
      rw [hμA, smul_eq_mul]
      have hcs : cellSectionOf p lam Φ (antidiagonal3 p * Y * T) =
          ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            ((((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℝ) : ℂ) * C) := by
        rw [hF1, hμC]; ring
      rw [hcs, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      have h1 : ‖(((lam 0) (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Units.ne_zero _)
      have h2 : ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) ≠ 0 := by
        exact_mod_cast modulus_ne_zero (Matrix.GeneralLinearGroup.det Y).ne_zero
      field_simp

end

end S_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum (solution)
