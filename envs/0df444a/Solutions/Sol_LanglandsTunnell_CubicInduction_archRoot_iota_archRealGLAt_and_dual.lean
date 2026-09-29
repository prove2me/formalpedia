-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archRoot_iota_archRealGLAt_and_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/87b49a11-538f-5b37-b55a-10b9432aced5

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws23K2

open NumberField.InfinitePlace
open scoped Matrix

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hR

abbrev eR : (default : InfinitePlace ℚ).Completion ≃+* ℝ := ringEquivRealOfIsReal hR

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = default := Subsingleton.elim _ _

theorem norm_eR_symm (x : ℝ) : ‖eR.symm x‖ = |x| := by
  have h := norm_ringEquivRealOfIsReal hR (eR.symm x)
  rw [RingEquiv.apply_symm_apply] at h
  rw [← h, Real.norm_eq_abs]

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 default = eR.symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  show archMatrixUpdate ℚ default ((glEquivOfRingEquiv (ringEquivRealOfIsReal hR).symm M :
    GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem archPlaceComponent3_apply (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((archPlaceComponent3 ℚ default g : GL (Fin 3) (default : InfinitePlace ℚ).Completion) :
        Matrix (Fin 3) (Fin 3) (default : InfinitePlace ℚ).Completion) i j =
      (((g : Matrix (Fin 3) (Fin 3) 𝔸) i j).1) default := rfl

def E (h : GL (Fin 2) ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![(h : Matrix (Fin 2) (Fin 2) ℝ) 0 0, (h : Matrix (Fin 2) (Fin 2) ℝ) 0 1, 0],
    ![(h : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1, 0],
    ![0, 0, 1]]

def D (h : GL (Fin 2) ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, 0, 1],
    ![((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1, ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1, 0],
    ![((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0, ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0, 0]]

@[scoped simp] theorem E_00 (h : GL (Fin 2) ℝ) : E h 0 0 = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := rfl
@[scoped simp] theorem E_01 (h : GL (Fin 2) ℝ) : E h 0 1 = (h : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := rfl
@[scoped simp] theorem E_02 (h : GL (Fin 2) ℝ) : E h 0 2 = 0 := rfl
@[scoped simp] theorem E_10 (h : GL (Fin 2) ℝ) : E h 1 0 = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := rfl
@[scoped simp] theorem E_11 (h : GL (Fin 2) ℝ) : E h 1 1 = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := rfl
@[scoped simp] theorem E_12 (h : GL (Fin 2) ℝ) : E h 1 2 = 0 := rfl
@[scoped simp] theorem E_20 (h : GL (Fin 2) ℝ) : E h 2 0 = 0 := rfl
@[scoped simp] theorem E_21 (h : GL (Fin 2) ℝ) : E h 2 1 = 0 := rfl
@[scoped simp] theorem E_22 (h : GL (Fin 2) ℝ) : E h 2 2 = 1 := rfl

@[scoped simp] theorem D_00 (h : GL (Fin 2) ℝ) : D h 0 0 = 0 := rfl
@[scoped simp] theorem D_01 (h : GL (Fin 2) ℝ) : D h 0 1 = 0 := rfl
@[scoped simp] theorem D_02 (h : GL (Fin 2) ℝ) : D h 0 2 = 1 := rfl
@[scoped simp] theorem D_10 (h : GL (Fin 2) ℝ) : D h 1 0 = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := rfl
@[scoped simp] theorem D_11 (h : GL (Fin 2) ℝ) : D h 1 1 = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := rfl
@[scoped simp] theorem D_12 (h : GL (Fin 2) ℝ) : D h 1 2 = 0 := rfl
@[scoped simp] theorem D_20 (h : GL (Fin 2) ℝ) : D h 2 0 = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := rfl
@[scoped simp] theorem D_21 (h : GL (Fin 2) ℝ) : D h 2 1 = ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := rfl
@[scoped simp] theorem D_22 (h : GL (Fin 2) ℝ) : D h 2 2 = 0 := rfl

theorem iotaR_matInv_fst (h : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((((ιR h : G2) : Matrix (Fin 2) (Fin 2) 𝔸))⁻¹ i j).1 default =
      eR.symm (((h : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ i j) := by
  rw [← Matrix.coe_units_inv, ← Matrix.coe_units_inv, ← map_inv]
  exact iotaR_fst _ _ _

theorem fst_zero_default : ((0 : 𝔸).1) default = 0 := rfl
theorem fst_one_default : ((1 : 𝔸).1) default = 1 := rfl

theorem entries_iota (h : GL (Fin 2) ℝ) (i j : Fin 3) :
    ((archPlaceComponent3 ℚ default (iota (𝓞 ℚ) ℚ (ιR h)) : GL (Fin 3) (default : InfinitePlace ℚ).Completion) :
        Matrix (Fin 3) (Fin 3) (default : InfinitePlace ℚ).Completion) i j = eR.symm (E h i j) := by
  rw [archPlaceComponent3_apply]
  change ((embedMat2 ((ιR h : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1) default = _
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, E, iotaR_fst, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      fst_zero_default, fst_one_default]

theorem entries_dual (h : GL (Fin 2) ℝ) (i j : Fin 3) :
    ((archPlaceComponent3 ℚ default (longWeyl3 * transposeInv3 (iota (𝓞 ℚ) ℚ (ιR h))) :
        GL (Fin 3) (default : InfinitePlace ℚ).Completion) :
        Matrix (Fin 3) (Fin 3) (default : InfinitePlace ℚ).Completion) i j = eR.symm (D h i j) := by
  rw [archPlaceComponent3_apply]
  have hinv : ((transposeInv3 (iota (𝓞 ℚ) ℚ (ιR h)) : GL (Fin 3) 𝔸) : Matrix (Fin 3) (Fin 3) 𝔸) =
      (embedMat2 ((ιR h⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸))ᵀ := by
    change (((iota (𝓞 ℚ) ℚ (ιR h))⁻¹ : GL (Fin 3) 𝔸) : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ = _
    rw [← map_inv, ← map_inv]
    rfl
  rw [Units.val_mul, hinv, longWeyl3_coe]
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, D, iotaR_fst, iotaR_matInv_fst, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      fst_zero_default, fst_one_default, Prod.fst_add, Prod.fst_mul]

theorem sizes_of_entries (k : GL (Fin 3) (default : InfinitePlace ℚ).Completion) (m : Fin 3 → Fin 3 → ℝ)
    (hk : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (default : InfinitePlace ℚ).Completion) i j = eR.symm (m i j)) :
    detSize k = |(Matrix.of m).det| ∧
      lastRowEucl k = Real.sqrt (m 2 0 ^ 2 + m 2 1 ^ 2 + m 2 2 ^ 2) ∧
      minorEucl k = Real.sqrt ((m 1 0 * m 2 1 - m 1 1 * m 2 0) ^ 2 + (m 1 0 * m 2 2 - m 1 2 * m 2 0) ^ 2 +
        (m 1 1 * m 2 2 - m 1 2 * m 2 1) ^ 2) := by
  have hmat : (k : Matrix (Fin 3) (Fin 3) (default : InfinitePlace ℚ).Completion) =
      (eR.symm : ℝ →+* (default : InfinitePlace ℚ).Completion).mapMatrix (Matrix.of m) := by
    ext i j; rw [hk]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [detSize, hmat, ← RingHom.map_det]
    exact norm_eR_symm _
  · rw [lastRowEucl, hk, hk, hk, norm_eR_symm, norm_eR_symm, norm_eR_symm, sq_abs, sq_abs, sq_abs]
  · simp only [minorEucl, bottomMinor, hk, ← map_mul, ← map_sub, norm_eR_symm, sq_abs]

theorem det_E (h : GL (Fin 2) ℝ) : (Matrix.of (E h)).det = (h : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [E]

theorem det_D (h : GL (Fin 2) ℝ) : (Matrix.of (D h)).det = -((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [D]; ring

theorem inv_entries (h : GL (Fin 2) ℝ) :
    ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 / (h : Matrix (Fin 2) (Fin 2) ℝ).det ∧
    ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 / (h : Matrix (Fin 2) (Fin 2) ℝ).det ∧
    ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = ((h : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
  have hdet : (h : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := (Matrix.GeneralLinearGroup.det h).ne_zero ∘ by
    intro h0; rw [← Matrix.GeneralLinearGroup.val_det_apply] at h0; exact Units.ne_zero _ h0 |>.elim
  have hinv : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (h : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ :=
    Matrix.coe_units_inv h
  refine ⟨?_, ?_, ?_⟩
  · rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']; simp; field_simp
  · rw [hinv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']; simp; field_simp
  · rw [hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

end Ws23K2
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual.Ws23K2"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual.Ws23K2"

theorem solution (h : GL (Fin 2) ℝ) (w : InfinitePlace ℚ) :
    archRoot₁ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₁ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) := by
  obtain rfl := Ws23K2.infinitePlace_eq w

  set a : ℝ := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 0 with ha
  set b : ℝ := (h : Matrix (Fin 2) (Fin 2) ℝ) 1 1 with hb
  set d : ℝ := (h : Matrix (Fin 2) (Fin 2) ℝ).det with hd
  have hdet : (Matrix.GeneralLinearGroup.det h : ℝ) = d := Matrix.GeneralLinearGroup.val_det_apply h
  have hd0 : d ≠ 0 := by rw [← hdet]; exact (Matrix.GeneralLinearGroup.det h).ne_zero
  have hr0 : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    apply hd0
    rw [hd, Matrix.det_fin_two, ← ha, ← hb, ha0, hb0]; ring
  have hrpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hr0)

  obtain ⟨d₁, r₁, m₁⟩ := Ws23K2.sizes_of_entries _ _ (Ws23K2.entries_iota h)

  obtain ⟨d₂, r₂, m₂⟩ := Ws23K2.sizes_of_entries _ _ (Ws23K2.entries_dual h)
  obtain ⟨i00, i10, idet⟩ := Ws23K2.inv_entries h
  simp only [archRoot₁, archRoot₂, d₁, r₁, m₁, d₂, r₂, m₂, Ws23K2.det_E, Ws23K2.det_D,
    Ws23K2.E_00, Ws23K2.E_01, Ws23K2.E_02, Ws23K2.E_10, Ws23K2.E_11, Ws23K2.E_12, Ws23K2.E_20,
    Ws23K2.E_21, Ws23K2.E_22, Ws23K2.D_00, Ws23K2.D_01, Ws23K2.D_02, Ws23K2.D_10, Ws23K2.D_11,
    Ws23K2.D_12, Ws23K2.D_20, Ws23K2.D_21, Ws23K2.D_22, i00, i10, idet, hdet, abs_neg, abs_inv]
  rw [← ha, ← hb, ← hd]
  have hsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (le_of_lt hrpos)
  have habs : |d| ≠ 0 := abs_ne_zero.2 hd0
  have e1 : (0 : ℝ) ^ 2 + 0 ^ 2 + 1 ^ 2 = 1 := by norm_num
  have e2 : (a * 0 - b * 0) ^ 2 + (a * 1 - 0 * 0) ^ 2 + (b * 1 - 0 * 0) ^ 2 = a ^ 2 + b ^ 2 := by ring
  have e3 : (b / d) ^ 2 + (-a / d) ^ 2 + (0 : ℝ) ^ 2 = (a ^ 2 + b ^ 2) / d ^ 2 := by field_simp; ring
  have e4 : (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (-a / d) -
      ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * (b / d)) ^ 2 +
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * 0 - 0 * (b / d)) ^ 2 +
      (((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * 0 - 0 * (-a / d)) ^ 2 = (d⁻¹) ^ 2 := by
    have hdet' : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = d⁻¹ := by rw [idet]
    rw [Matrix.det_fin_two, i00, i10] at hdet'
    have : ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (-a / d) -
        ((h⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * (b / d) = -d⁻¹ := by linear_combination -hdet'
    rw [this]; ring
  rw [e1, e2, e3, e4, Real.sqrt_one, Real.sqrt_div' _ (sq_nonneg d), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsq]; ring
  · ring
  · rw [abs_inv]; field_simp
  · rw [abs_inv, div_pow, hsq]; field_simp

end S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual (solution)
