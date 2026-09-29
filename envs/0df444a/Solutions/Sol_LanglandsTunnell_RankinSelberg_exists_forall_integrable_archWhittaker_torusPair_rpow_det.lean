-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_archWhittaker_torusPair_rpow_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/117aca3d-7d46-5c77-a544-eddc91c59a44

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
import Theorems.Thm_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual
import Theorems.Thm_LanglandsTunnell_RankinSelberg_norm_archWhittaker_upperUnit_mul_rowIsometry
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top
import Theorems.Thm_LanglandsTunnell_Converse_exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Matrix ENNReal NNReal

noncomputable section

namespace Ws23ArchM

abbrev hR : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev 𝔸 : Type := AdeleRing (𝓞 ℚ) ℚ
abbrev ιR : GL (Fin 2) ℝ →* G2 := archRealGLAt hR

abbrev Φ : GL (Fin 2) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  (archComponent3 (𝓞 ℚ) ℚ).comp ((iota (𝓞 ℚ) ℚ).comp ιR)

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = default := Subsingleton.elim _ _

theorem iotaR_fst (M : GL (Fin 2) ℝ) (i j : Fin 2) (v : InfinitePlace ℚ) :
    (((ιR M : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 v =
      (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm ((M : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  obtain rfl := infinitePlace_eq v
  show archMatrixUpdate ℚ default ((glEquivOfRingEquiv (ringEquivRealOfIsReal hR).symm M :
    GL (Fin 2) (default : InfinitePlace ℚ).Completion) : Matrix _ _ _) i j default = _
  rw [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]

theorem val_Φ_apply (h : GL (Fin 2) ℝ) (i j : Fin 3) :
    ((Φ h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      (embedMat2 ((ιR h : G2) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 := rfl

theorem continuous_ringEquivRealOfIsReal_symm (v : InfinitePlace ℚ) :
    Continuous (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm := by
  have h := (isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous
  refine h.congr fun x => ?_
  rw [IsometryEquiv.symm_apply_eq]
  exact ((ringEquivRealOfIsReal (IsTotallyReal.isReal v)).apply_symm_apply x).symm

theorem continuous_ιR_entry (a b : Fin 2) (v : InfinitePlace ℚ) :
    Continuous fun h : GL (Fin 2) ℝ => (((ιR h : G2) : Matrix (Fin 2) (Fin 2) 𝔸) a b).1 v := by
  simp_rw [iotaR_fst]
  exact (continuous_ringEquivRealOfIsReal_symm v).comp (Units.continuous_val.matrix_elem a b)

theorem continuous_val_Φ :
    Continuous fun h : GL (Fin 2) ℝ =>
      ((Φ h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := by
  refine continuous_matrix fun i j => ?_
  refine continuous_pi fun v => ?_
  simp_rw [val_Φ_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.reduceFinMk] <;>
    first
      | exact continuous_ιR_entry _ _ v
      | exact continuous_const

theorem continuous_Φ : Continuous fun h : GL (Fin 2) ℝ => Φ h := by
  refine Units.continuous_iff.2 ⟨continuous_val_Φ, ?_⟩
  have : (fun h : GL (Fin 2) ℝ => (Φ h).inv) =
      fun h => ((Φ h⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := by
    funext h; rw [Units.inv_eq_val_inv, map_inv]
  show Continuous fun h : GL (Fin 2) ℝ => (Φ h).inv
  rw [this]
  exact continuous_val_Φ.comp continuous_inv

theorem continuous_transposeInv : Continuous (RSCarrier.transposeInv : GL (Fin 2) ℝ → GL (Fin 2) ℝ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) ℝ => (((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 2) ℝ => ((g : Matrix (Fin 2) (Fin 2) ℝ))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem continuous_transposeInv3 :
    Continuous (transposeInv3 : GL (Fin 3) (InfiniteAdeleRing ℚ) → GL (Fin 3) (InfiniteAdeleRing ℚ)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) (InfiniteAdeleRing ℚ) => ((g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem continuous_absDet :
    Continuous fun hA : GL (Fin 2) ℝ => (((|(Matrix.GeneralLinearGroup.det hA : ℝ)| : ℝ) : ℂ)) := by
  have : (fun hA : GL (Fin 2) ℝ => ((Matrix.GeneralLinearGroup.det hA : ℝˣ) : ℝ)) =
      fun hA : GL (Fin 2) ℝ => ((hA : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det :=
    funext fun hA => Matrix.GeneralLinearGroup.val_det_apply hA
  have hdet : Continuous fun hA : GL (Fin 2) ℝ => ((Matrix.GeneralLinearGroup.det hA : ℝˣ) : ℝ) := by
    rw [this]; exact Units.continuous_val.matrix_det
  exact Complex.continuous_ofReal.comp (continuous_abs.comp hdet)

end Ws23ArchM

namespace Ws23ArchP

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem coe_upperUnit (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((upperUnit a b t ha ht : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_upperUnit_inv (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (((upperUnit a b t ha ht)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a⁻¹, -(b * a⁻¹ * t⁻¹); 0, t⁻¹] := by
  have hmul : (!![a⁻¹, -(b * a⁻¹ * t⁻¹); 0, t⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; 0, t] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, ha, ht]; try (field_simp; ring))
  rw [Matrix.coe_units_inv, coe_upperUnit]
  exact Matrix.inv_eq_left_inv hmul

theorem det_upperUnit (a b t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (Matrix.GeneralLinearGroup.det (upperUnit a b t ha ht) : ℝ) = a * t := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_upperUnit, Matrix.det_fin_two_of]
  ring

theorem coe_transposeInv (g : GL (Fin 2) ℝ) :
    ((transposeInv g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))ᵀ := rfl

theorem transposeInv_mul (g h : GL (Fin 2) ℝ) : transposeInv (g * h) = transposeInv g * transposeInv h := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_transposeInv, coe_transposeInv, coe_transposeInv, mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv_upperUnit_diag (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    transposeInv (upperUnit a 0 t ha ht) = upperUnit a⁻¹ 0 t⁻¹ (inv_ne_zero ha) (inv_ne_zero ht) := by
  refine Units.ext ?_
  rw [coe_transposeInv, coe_upperUnit_inv, coe_upperUnit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rowIsometry_rows {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 = 1 ∧
    (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 = 1 ∧
    (k : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 0 +
      (k : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (k : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := by
  obtain ⟨-, h⟩ := hk
  have h10 := h 1 0
  have h01 := h 0 1
  have h11 := h 1 1
  simp only [Real.norm_eq_abs, sq_abs, one_mul, zero_mul, add_zero, zero_add] at h10 h01 h11
  refine ⟨by nlinarith [h10], by nlinarith [h01], ?_⟩
  nlinarith [h10, h01, h11]

theorem abs_det_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    |(Matrix.GeneralLinearGroup.det k : ℝ)| = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← Real.norm_eq_abs]
  exact hk.1

theorem det_eq_one_or_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    (Matrix.GeneralLinearGroup.det k : ℝ) = 1 ∨ (Matrix.GeneralLinearGroup.det k : ℝ) = -1 :=
  abs_eq (zero_le_one) |>.1 (abs_det_of_mem hk)

theorem mul_transpose_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) :
    (k : Matrix (Fin 2) (Fin 2) ℝ) * (k : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1 := by
  obtain ⟨h1, h2, h3⟩ := rowIsometry_rows hk
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> nlinarith [h1, h2, h3]

theorem transposeInv_of_mem {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) : transposeInv k = k := by
  refine Units.ext ?_
  rw [coe_transposeInv, Matrix.coe_units_inv, Matrix.inv_eq_right_inv (mul_transpose_of_mem hk),
    Matrix.transpose_transpose]

theorem secondRow_upperUnit_mul {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    ((upperUnit a 0 t ha ht * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 +
        ((upperUnit a 0 t ha ht * k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 = t ^ 2 := by
  obtain ⟨-, h2, -⟩ := rowIsometry_rows hk
  rw [Units.val_mul, coe_upperUnit]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [h2]

theorem secondRow_unipotent_mul (x : ℝ) (g : GL (Fin 2) ℝ) (j : Fin 2) :
    ((unipotentGL2 x * g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 j = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 j := by
  rw [Units.val_mul]
  simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_unipotent_mul (x : ℝ) (g : GL (Fin 2) ℝ) :
    (Matrix.GeneralLinearGroup.det (unipotentGL2 x * g) : ℝ) = (Matrix.GeneralLinearGroup.det g : ℝ) := by
  rw [map_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
  simp [unipotentGL2, Matrix.det_fin_two_of]

section Weyl
variable (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
include hw₀R

theorem w₀R_mem : w₀R ∈ rowIsometrySubgroup ℝ := by
  refine ⟨?_, fun x y => ?_⟩
  · rw [hw₀R, Matrix.det_fin_two_of]; norm_num
  · rw [hw₀R]; simp; ring

theorem coe_w₀R_inv : (((w₀R⁻¹ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0] := by
  rw [Matrix.coe_units_inv, hw₀R]
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w₀R_mul_transposeInv_unipotent (x : ℝ) :
    w₀R * transposeInv (unipotentGL2 x) = unipotentGL2 (-x) * w₀R := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInv, hw₀R]
  have : (((unipotentGL2 x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, -x; 0, 1] := rfl
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

theorem w₀R_mul_upperUnit_diag (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    w₀R * upperUnit a 0 t ha ht = upperUnit t 0 a ht ha * w₀R := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_upperUnit, coe_upperUnit, hw₀R]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Weyl

def dd (g : GL (Fin 2) ℝ) : ℝ := |(Matrix.GeneralLinearGroup.det g : ℝ)|

def rr (g : GL (Fin 2) ℝ) : ℝ := Real.sqrt ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2)

theorem dd_pos (g : GL (Fin 2) ℝ) : 0 < dd g := abs_pos.2 (Matrix.GeneralLinearGroup.det g).ne_zero

theorem rr_sq (g : GL (Fin 2) ℝ) : rr g ^ 2 = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem rr_pos (g : GL (Fin 2) ℝ) : 0 < rr g := by
  unfold rr
  apply Real.sqrt_pos.2
  by_contra h
  have h0 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0), sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]
  have h1 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 0 := by nlinarith [sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0), sq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1)]
  have hdet : (Matrix.GeneralLinearGroup.det g : ℝ) = 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h0, h1]
    ring
  exact (Matrix.GeneralLinearGroup.det g).ne_zero hdet

theorem continuous_dd : Continuous dd := by
  have : (fun g : GL (Fin 2) ℝ => (Matrix.GeneralLinearGroup.det g : ℝ)) =
      fun g => ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det :=
    funext fun g => Matrix.GeneralLinearGroup.val_det_apply g
  unfold dd
  rw [show (fun g : GL (Fin 2) ℝ => |(Matrix.GeneralLinearGroup.det g : ℝ)|) =
    fun g => |((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| from funext fun g => by rw [Matrix.GeneralLinearGroup.val_det_apply]]
  exact continuous_abs.comp Units.continuous_val.matrix_det

theorem continuous_rr : Continuous rr := by
  unfold rr
  exact Real.continuous_sqrt.comp (((Units.continuous_val.matrix_elem 1 0).pow 2).add
    ((Units.continuous_val.matrix_elem 1 1).pow 2))

def bnd (τ N : ℕ) (C : ℝ) (g : GL (Fin 2) ℝ) : ℝ :=
  C / ((dd g / rr g) ^ τ * (1 + (dd g / rr g ^ 2 + rr g)) ^ N)

theorem bnd_denom_pos (τ N : ℕ) (g : GL (Fin 2) ℝ) : 0 < (dd g / rr g) ^ τ * (1 + (dd g / rr g ^ 2 + rr g)) ^ N := by
  have h1 := dd_pos g
  have h2 := rr_pos g
  positivity

theorem continuous_bnd (τ N : ℕ) (C : ℝ) : Continuous (bnd τ N C) := by
  unfold bnd
  refine continuous_const.div ?_ fun g => (bnd_denom_pos τ N g).ne'
  exact ((continuous_dd.div continuous_rr fun g => (rr_pos g).ne').pow τ).mul
    ((continuous_const.add ((continuous_dd.div (continuous_rr.pow 2) fun g => (pow_pos (rr_pos g) 2).ne').add
      continuous_rr)).pow N)

theorem dd_unipotent_mul (x : ℝ) (g : GL (Fin 2) ℝ) : dd (unipotentGL2 x * g) = dd g := by
  unfold dd
  rw [det_unipotent_mul]

theorem rr_unipotent_mul (x : ℝ) (g : GL (Fin 2) ℝ) : rr (unipotentGL2 x * g) = rr g := by
  unfold rr
  rw [secondRow_unipotent_mul, secondRow_unipotent_mul]

theorem bnd_unipotent_mul (τ N : ℕ) (C : ℝ) (x : ℝ) (g : GL (Fin 2) ℝ) :
    bnd τ N C (unipotentGL2 x * g) = bnd τ N C g := by
  unfold bnd
  rw [dd_unipotent_mul, rr_unipotent_mul]

theorem dd_torus {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    dd (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) = t ^ 2 * y := by
  unfold dd
  rw [map_mul, Units.val_mul, abs_mul, abs_det_of_mem hk, mul_one, det_upperUnit,
    abs_of_pos (by positivity)]
  ring

theorem rr_torus {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    rr (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) = t := by
  unfold rr
  rw [secondRow_upperUnit_mul hk, Real.sqrt_sq ht.le]

theorem bnd_torus {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (τ N : ℕ) (C : ℝ) :
    bnd τ N C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) = C / ((t * y) ^ τ * (1 + (y + t)) ^ N) := by
  unfold bnd
  rw [dd_torus hk hy ht, rr_torus hk hy ht]
  have h1 : t ^ 2 * y / t = t * y := by field_simp
  have h2 : t ^ 2 * y / t ^ 2 = y := by field_simp
  rw [h1, h2]

theorem prod_infinitePlace {f : InfinitePlace ℚ → ℝ} : ∏ w : InfinitePlace ℚ, f w = f default := by
  rw [Finset.prod_eq_single_of_mem default (Finset.mem_univ _) fun w _ hw => absurd (Subsingleton.elim w default) hw]

theorem sum_infinitePlace {f : InfinitePlace ℚ → ℝ} : ∑ w : InfinitePlace ℚ, f w = f default := by
  rw [Finset.sum_eq_single_of_mem default (Finset.mem_univ _) fun w _ hw => absurd (Subsingleton.elim w default) hw]

theorem coe_archComponent3 (G : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((archComponent3 (𝓞 ℚ) ℚ G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      (((G : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 := rfl

theorem coe_archComponent3' (G : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((archComponent3 (𝓞 ℚ) ℚ G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((((G : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)) := rfl

theorem archComponent3_longWeyl3_mul_transposeInv3 (G : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archComponent3 (𝓞 ℚ) ℚ (longWeyl3 * transposeInv3 G) = longWeyl3 * transposeInv3 (archComponent3 (𝓞 ℚ) ℚ G) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_archComponent3', Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul]
  congr 1
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i l) =
      (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i l
    fin_cases i <;> fin_cases l <;> simp

theorem norm_Warch_le (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (τ N : ℕ) (C : ℝ)
    (hb : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ, ‖Warch (archComponent3 (𝓞 ℚ) ℚ G)‖ ≤
      C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w G * archRoot₂ ℚ w G) ^ τ * (1 + archRootSum ℚ G) ^ N))
    (g : GL (Fin 2) ℝ) :
    ‖Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))‖
        ≤ bnd τ N C g ∧
      ‖dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))‖ ≤ bnd τ N C g := by
  have hr := rr_pos g
  have hK2 := fun w => LanglandsTunnell.CubicInduction.archRoot_iota_archRealGLAt_and_dual g w
  have hrr : Real.sqrt ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2) = rr g := rfl
  have hdd : |(Matrix.GeneralLinearGroup.det g : ℝ)| = dd g := rfl
  have e1 : dd g / rr g ^ 2 * rr g = dd g / rr g := by field_simp
  have e2 : rr g * (dd g / rr g ^ 2) = dd g / rr g := by rw [mul_comm]; exact e1
  constructor
  · refine (hb _).trans (le_of_eq ?_)
    unfold bnd archRootSum
    rw [prod_infinitePlace, sum_infinitePlace, (hK2 default).1, (hK2 default).2.1, hrr, ← rr_sq, hdd, e1]
  · rw [dualWhittakerFn3_apply, ← archComponent3_longWeyl3_mul_transposeInv3]
    refine (hb _).trans (le_of_eq ?_)
    unfold bnd archRootSum
    rw [prod_infinitePlace, sum_infinitePlace, (hK2 default).2.2.1, (hK2 default).2.2.2, hrr, ← rr_sq, hdd, e2,
      add_comm (rr g)]

section Majorants

variable (WA : GL (Fin 2) ℝ → ℂ) (w₀R : GL (Fin 2) ℝ)

def H1 (σ : ℝ) (τ N : ℕ) (C : ℝ) (g : GL (Fin 2) ℝ) : ℝ≥0∞ :=
  ‖WA g‖ₑ * ENNReal.ofReal (bnd τ N C g) * ENNReal.ofReal (dd g ^ (σ - 1 / 2))

def H2 (σ : ℝ) (τ N : ℕ) (C : ℝ) (g : GL (Fin 2) ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (dd g) * ‖WA (w₀R * transposeInv g)‖ₑ * ENNReal.ofReal (bnd τ N C g) * ENNReal.ofReal (dd g ^ (σ - 1 / 2))

variable {WA}

theorem measurable_H1 [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] (hWAc : Continuous WA)
    (σ : ℝ) (τ N : ℕ) (C : ℝ) : Measurable (H1 WA σ τ N C) := by
  unfold H1
  refine ((hWAc.measurable.enorm).mul (continuous_bnd τ N C).measurable.ennreal_ofReal).mul ?_
  exact (continuous_dd.measurable.pow_const _).ennreal_ofReal

theorem measurable_H2 [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)] (hWAc : Continuous WA)
    (σ : ℝ) (τ N : ℕ) (C : ℝ) : Measurable (H2 WA w₀R σ τ N C) := by
  unfold H2
  refine ((continuous_dd.measurable.ennreal_ofReal.mul
    (hWAc.comp (continuous_const.mul Ws23ArchM.continuous_transposeInv)).measurable.enorm).mul
    (continuous_bnd τ N C).measurable.ennreal_ofReal).mul ?_
  exact (continuous_dd.measurable.pow_const _).ennreal_ofReal

theorem norm_exp_two_pi_I (x : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem H1_unipotent_mul (hWAN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      WA (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA h)
    (σ : ℝ) (τ N : ℕ) (C : ℝ) (x : ℝ) (g : GL (Fin 2) ℝ) :
    H1 WA σ τ N C (unipotentGL2 x * g) = H1 WA σ τ N C g := by
  unfold H1
  rw [hWAN, enorm_mul, ← ofReal_norm_eq_enorm (Complex.exp _), norm_exp_two_pi_I, ENNReal.ofReal_one, one_mul,
    bnd_unipotent_mul, dd_unipotent_mul]

theorem H2_unipotent_mul (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (hWAN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      WA (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA h)
    (σ : ℝ) (τ N : ℕ) (C : ℝ) (x : ℝ) (g : GL (Fin 2) ℝ) :
    H2 WA w₀R σ τ N C (unipotentGL2 x * g) = H2 WA w₀R σ τ N C g := by
  unfold H2
  rw [transposeInv_mul, show w₀R * (transposeInv (unipotentGL2 x) * transposeInv g) =
      unipotentGL2 (-x) * (w₀R * transposeInv g) from by
        rw [← _root_.mul_assoc, w₀R_mul_transposeInv_unipotent w₀R hw₀R, _root_.mul_assoc],
    hWAN, enorm_mul, ← ofReal_norm_eq_enorm (Complex.exp _), norm_exp_two_pi_I, ENNReal.ofReal_one, one_mul,
    bnd_unipotent_mul, dd_unipotent_mul]

theorem norm_cpow_dd (g : GL (Fin 2) ℝ) (s : ℂ) :
    ‖((dd g : ℝ) : ℂ) ^ (s - 1 / 2)‖ = dd g ^ (s.re - 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (dd_pos g)]
  simp

theorem enorm_integrand₁_le (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (τ N : ℕ) (C : ℝ)
    (hb : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ, ‖Warch (archComponent3 (𝓞 ℚ) ℚ G)‖ ≤
      C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w G * archRoot₂ ℚ w G) ^ τ * (1 + archRootSum ℚ G) ^ N))
    (s : ℂ) (g : GL (Fin 2) ℝ) :
    ‖(WA g * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
        (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))‖ₑ ≤ H1 WA s.re τ N C g := by
  unfold H1
  rw [enorm_mul, enorm_mul, ← ofReal_norm_eq_enorm (Warch _), ← ofReal_norm_eq_enorm (_ ^ _),
    show |(Matrix.GeneralLinearGroup.det g : ℝ)| = dd g from rfl, norm_cpow_dd]
  gcongr
  exact (norm_Warch_le Warch τ N C hb g).1

theorem enorm_integrand₂_le (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (τ N : ℕ) (C : ℝ)
    (hb : ∀ G : AdelicGL 3 (𝓞 ℚ) ℚ, ‖Warch (archComponent3 (𝓞 ℚ) ℚ G)‖ ≤
      C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w G * archRoot₂ ℚ w G) ^ τ * (1 + archRootSum ℚ G) ^ N))
    (s : ℂ) (g : GL (Fin 2) ℝ) :
    ‖((((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) * WA (w₀R * RSCarrier.transposeInv g)) *
          dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ
            (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
        (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))‖ₑ ≤ H2 WA w₀R s.re τ N C g := by
  unfold H2
  rw [enorm_mul, enorm_mul, enorm_mul, ← ofReal_norm_eq_enorm (dualWhittakerFn3 Warch _),
    ← ofReal_norm_eq_enorm (_ ^ _), ← ofReal_norm_eq_enorm ((_ : ℝ) : ℂ),
    show |(Matrix.GeneralLinearGroup.det g : ℝ)| = dd g from rfl, norm_cpow_dd, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (dd_pos g)]
  gcongr
  exact (norm_Warch_le Warch τ N C hb g).2

end Majorants

section Torus

variable (P : RealArchParam) (kw : ZMod 2 → InfinitePlace ℚ → ℤ) (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
  (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
  (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
      WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
        = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
            (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
  (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
  (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
include hWAZ hWAK hWAt

theorem enorm_WA_torus_le (par : ZMod 2) {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ)
    {t₁ t₂ : ℝ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) :
    ‖WA par (upperUnit t₁ 0 t₂ h₁ h₂ * k)‖ₑ ≤
      ENNReal.ofReal (|t₂| ^ (P.centralExponent.re + 1)) *
        (‖Wr par default (t₁ / t₂)‖ₑ + ‖Wr par default (-(t₁ / t₂))‖ₑ) := by
  rw [← ofReal_norm_eq_enorm,
    LanglandsTunnell.RankinSelberg.norm_archWhittaker_upperUnit_mul_rowIsometry P kw Wr WA hWAZ hWAK hWAt par t₁ t₂
      h₁ h₂ k hk,
    ENNReal.ofReal_mul (by positivity), ofReal_norm_eq_enorm]
  gcongr
  rcases det_eq_one_or_of_mem hk with hd | hd
  · rw [hd, Complex.ofReal_one, one_mul]
    exact le_self_add
  · rw [hd, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, neg_div]
    exact le_add_self

theorem H1_torus_le (par : ZMod 2) (σ : ℝ) (τ N : ℕ) (C : ℝ) {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ)
    {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    H1 (WA par) σ τ N C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) ≤
      ENNReal.ofReal (t ^ (P.centralExponent.re + 1)) * (‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ) *
        ENNReal.ofReal (C / ((t * y) ^ τ * (1 + (y + t)) ^ N)) * ENNReal.ofReal ((t ^ 2 * y) ^ (σ - 1 / 2)) := by
  unfold H1
  rw [bnd_torus hk hy ht, dd_torus hk hy ht]
  gcongr
  have := enorm_WA_torus_le P kw Wr WA hWAZ hWAK hWAt par hk (mul_pos ht hy).ne' ht.ne'
  have e : ((t * y : ℝ) : ℂ) / (t : ℂ) = (y : ℂ) := by
    rw [Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.2 ht.ne']
  rwa [abs_of_pos ht, e] at this

theorem H2_torus_le (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (par : ZMod 2) (σ : ℝ) (τ N : ℕ) (C : ℝ) {k : GL (Fin 2) ℝ} (hk : k ∈ rowIsometrySubgroup ℝ)
    {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    H2 (WA par) w₀R σ τ N C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) ≤
      ENNReal.ofReal (t ^ 2 * y) *
        (ENNReal.ofReal (((t * y)⁻¹) ^ (P.centralExponent.re + 1)) * (‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ)) *
        ENNReal.ofReal (C / ((t * y) ^ τ * (1 + (y + t)) ^ N)) * ENNReal.ofReal ((t ^ 2 * y) ^ (σ - 1 / 2)) := by
  unfold H2
  rw [bnd_torus hk hy ht, dd_torus hk hy ht]
  gcongr
  have hwk : w₀R * k ∈ rowIsometrySubgroup ℝ := mul_mem (w₀R_mem w₀R hw₀R) hk
  rw [transposeInv_mul, transposeInv_of_mem hk, transposeInv_upperUnit_diag, ← mul_assoc,
    w₀R_mul_upperUnit_diag w₀R hw₀R, mul_assoc]
  have := enorm_WA_torus_le P kw Wr WA hWAZ hWAK hWAt par hwk (inv_ne_zero ht.ne') (inv_ne_zero (mul_pos ht hy).ne')
  have e : ((t⁻¹ : ℝ) : ℂ) / (((t * y)⁻¹ : ℝ) : ℂ) = (y : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.2 ht.ne', Complex.ofReal_ne_zero.2 hy.ne']
  rwa [abs_of_pos (inv_pos.2 (mul_pos ht hy)), e] at this

end Torus

section RealBounds

theorem rpow_collect₁ {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (α σ : ℝ) (τ : ℕ) :
    t ^ α * ((t * y) ^ τ)⁻¹ * (t ^ 2 * y) ^ (σ - 1 / 2) * ((y ^ 2)⁻¹ * t⁻¹) =
      t ^ (α - τ + 2 * σ - 2) * y ^ (σ - τ - 5 / 2) := by
  obtain ⟨L, rfl⟩ : ∃ L, t = Real.exp L := ⟨Real.log t, (Real.exp_log ht).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, y = Real.exp M := ⟨Real.log y, (Real.exp_log hy).symm⟩
  simp only [← Real.exp_add, ← Real.exp_neg, ← Real.exp_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem rpow_collect₂ {t y : ℝ} (ht : 0 < t) (hy : 0 < y) (α σ : ℝ) (τ : ℕ) :
    t ^ 2 * y * ((t * y)⁻¹ ^ α * (((t * y) ^ τ)⁻¹ * (t ^ 2 * y) ^ (σ - 1 / 2) * ((y ^ 2)⁻¹ * t⁻¹))) =
      t ^ (2 * σ - α - τ) * y ^ (σ - α - τ - 3 / 2) := by
  obtain ⟨L, rfl⟩ : ∃ L, t = Real.exp L := ⟨Real.log t, (Real.exp_log ht).symm⟩
  obtain ⟨M, rfl⟩ : ∃ M, y = Real.exp M := ⟨Real.log y, (Real.exp_log hy).symm⟩
  simp only [← Real.exp_add, ← Real.exp_neg, ← Real.exp_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem one_add_pow_le {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (M : ℕ) :
    (1 + t) ^ M ≤ (1 + (y + t)) ^ (2 * M) := by
  rw [pow_mul]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

theorem torus_real_bound {t y C X a b : ℝ} (ht : 0 < t) (hy : 0 < y) (hC : 0 ≤ C) (τ M : ℕ)
    (hX : X * (((t * y) ^ τ)⁻¹ * ((y ^ 2)⁻¹ * t⁻¹)) = t ^ a * y ^ b) (hX0 : 0 ≤ X) :
    X * (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * ((y ^ 2)⁻¹ * t⁻¹) ≤
      C * (t ^ a / (1 + t) ^ M) * y ^ b := by
  have hpos : 0 < (1 + (y + t)) ^ (2 * M) := by positivity
  have hpos' : 0 < (1 + t) ^ M := by positivity
  have key : X * (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * ((y ^ 2)⁻¹ * t⁻¹) =
      C * (t ^ a * y ^ b) * ((1 + (y + t)) ^ (2 * M))⁻¹ := by
    rw [← hX]
    field_simp
  rw [key, show C * (t ^ a / (1 + t) ^ M) * y ^ b = C * (t ^ a * y ^ b) * ((1 + t) ^ M)⁻¹ from by
    field_simp]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos' (one_add_pow_le ht.le hy.le M))
    (mul_nonneg hC (by rw [← hX]; positivity))

end RealBounds

section Finiteness

open Set

theorem integrableOn_rpow_div_one_add_pow {a : ℝ} {M : ℕ} (ha : -1 < a) (hM : a + 1 < M) :
    IntegrableOn (fun t : ℝ => t ^ a / (1 + t) ^ M) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hcont : ContinuousOn (fun t : ℝ => t ^ a / (1 + t) ^ M) (Ioi 0) := by
    refine ContinuousOn.div (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_ fun t ht => ?_
    · exact (continuousOn_const.add continuousOn_id).pow M
    · exact (pow_pos (by linarith [mem_Ioi.1 ht]) M).ne'
  refine IntegrableOn.union ?_ ?_
  · have hg : IntegrableOn (fun t : ℝ => t ^ a) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (intervalIntegral.intervalIntegrable_rpow' ha)
    refine hg.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have h1 : 1 ≤ (1 + t) ^ M := one_le_pow₀ (by linarith [ht.1])
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg ht.1.le a) (by positivity))]
    exact div_le_self (Real.rpow_nonneg ht.1.le a) h1
  · have hg : IntegrableOn (fun t : ℝ => t ^ (a - M)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hg.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg ht0.le a) (by positivity)),
      Real.rpow_sub ht0, Real.rpow_natCast]
    gcongr
    linarith [mem_Ioi.1 ht]

theorem lintegral_rpow_div_one_add_pow_lt_top {a : ℝ} {M : ℕ} (ha : -1 < a) (hM : a + 1 < M) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ a / (1 + t) ^ M) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun t => ?_) (integrableOn_rpow_div_one_add_pow ha hM).2
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

theorem lintegral_quadrant_prod_lt_top {φ ψ : ℝ → ℝ≥0∞} (hψ : AEMeasurable ψ (volume.restrict (Ioi 0)))
    (hφ : AEMeasurable φ (volume.restrict (Ioi 0)))
    (hψi : ∫⁻ y in Ioi (0 : ℝ), ψ y < ⊤) (hφi : ∫⁻ t in Ioi (0 : ℝ), φ t < ⊤) :
    ∫⁻ r in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), ψ r.1 * φ r.2 < ⊤ := by
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) from rfl,
    ← Measure.prod_restrict, lintegral_prod_mul hψ hφ]
  exact ENNReal.mul_lt_top hψi hφi

end Finiteness

section Topology

scoped instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem locallyCompactSpace_GL : LocallyCompactSpace (GL (Fin 2) ℝ) := by infer_instance

theorem secondCountableTopology_GL : SecondCountableTopology (GL (Fin 2) ℝ) :=
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem mem_realUnipotent_iff (g : GL (Fin 2) ℝ) :
    g ∈ (realUnipotent : Subgroup (GL (Fin 2) ℝ)) ↔
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem isClosed_realUnipotent : IsClosed ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) =
      ((fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_assoc]
    exact mem_realUnipotent_iff g
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

def orthSet : Set (Matrix (Fin 2) (Fin 2) ℝ) := {A | A * Aᵀ = 1}

theorem isCompact_orthSet : IsCompact orthSet := by

  let S : Set (Fin 2 → Fin 2 → ℝ) := {A | Matrix.of A * (Matrix.of A)ᵀ = 1}
  have hS : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq ((continuous_id.matrix_mul continuous_id.matrix_transpose)) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → Fin 2 → ℝ)) (r := 1)).subset fun A hA => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      have hrow : A i 0 ^ 2 + A i 1 ^ 2 = 1 := by
        have := congrFun (congrFun hA i) i
        simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, sq] using this
      rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
      fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> nlinarith [sq_nonneg (A i 0), sq_nonneg (A i 1)]
  have : orthSet = Matrix.of '' S := by
    ext A
    constructor
    · intro hA
      exact ⟨A, hA, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact hB
  rw [this]
  exact hS.image continuous_id

theorem mem_rowIsometrySubgroup_of_orth {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A * Aᵀ = 1) (hA' : Aᵀ * A = 1) :
    (⟨A, Aᵀ, hA, hA'⟩ : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup ℝ := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 h01
  refine ⟨?_, fun x y => ?_⟩
  · show ‖A.det‖ = 1
    have hdet : A.det ^ 2 = 1 := by
      have := congrArg Matrix.det hA
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at this
    rw [Real.norm_eq_abs, ← sq_eq_sq₀ (abs_nonneg _) zero_le_one, sq_abs, hdet, one_pow]
  · show ‖x * A 0 0 + y * A 1 0‖ ^ 2 + ‖x * A 0 1 + y * A 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    linear_combination x ^ 2 * h00 + y ^ 2 * h11 + 2 * x * y * h01

theorem isCompact_rowIsometrySubgroup :
    IsCompact ((rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) := by
  let f : orthSet → GL (Fin 2) ℝ := fun A => ⟨A.1, A.1ᵀ, A.2, mul_eq_one_comm.1 A.2⟩
  have hf : Continuous f := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact continuous_subtype_val.matrix_transpose
  have hrange : ((rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) = Set.range f := by
    ext k
    constructor
    · intro hk
      refine ⟨⟨(k : Matrix (Fin 2) (Fin 2) ℝ), mul_transpose_of_mem hk⟩, Units.ext rfl⟩
    · rintro ⟨A, rfl⟩
      exact mem_rowIsometrySubgroup_of_orth A.2 (mul_eq_one_comm.1 A.2)
  rw [hrange]
  haveI : CompactSpace orthSet := isCompact_iff_compactSpace.1 isCompact_orthSet
  exact isCompact_range hf

theorem isClosed_rowIsometrySubgroup :
    IsClosed ((rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) :=
  isCompact_rowIsometrySubgroup.isClosed

theorem measurable_weight {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.ennreal_tsum fun n => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

end Topology

section TorusWeight

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

def Gfun (Wr : ℂ → ℂ) (C a b : ℝ) (M : ℕ) (r : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal C * ((‖Wr r.1‖ₑ + ‖Wr (-r.1)‖ₑ) * ENNReal.ofReal (r.1 ^ b)) *
    ENNReal.ofReal (r.2 ^ a / (1 + r.2) ^ M)

variable (P : RealArchParam) (kw : ZMod 2 → InfinitePlace ℚ → ℤ) (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
  (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
  (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
      WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
        = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
            (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
  (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
  (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
include hWAZ hWAK hWAt

theorem H1_weight_le (par : ZMod 2) (σ : ℝ) (τ M : ℕ) {C : ℝ} (hC : 0 ≤ C) {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    H1 (WA par) σ τ (2 * M) C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) *
        ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹) ≤
      Gfun (Wr par default) C (P.centralExponent.re + 1 - τ + 2 * σ - 2) (σ - τ - 5 / 2) M (y, t) := by
  set α : ℝ := P.centralExponent.re + 1 with hα
  set S : ℝ≥0∞ := ‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ with hS
  have hD : 0 < (t * y) ^ τ * (1 + (y + t)) ^ (2 * M) := by positivity
  have h1 : 0 ≤ t ^ α := Real.rpow_nonneg ht.le _
  have h2 : 0 ≤ C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M)) := div_nonneg hC hD.le
  have h3 : 0 ≤ (t ^ 2 * y) ^ (σ - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have h4 : 0 ≤ (y ^ 2)⁻¹ * t⁻¹ := by positivity
  calc H1 (WA par) σ τ (2 * M) C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) * ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹)
      ≤ (ENNReal.ofReal (t ^ α) * S * ENNReal.ofReal (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) *
          ENNReal.ofReal ((t ^ 2 * y) ^ (σ - 1 / 2))) * ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹) :=
        mul_le_mul_left (H1_torus_le P kw Wr WA hWAZ hWAK hWAt par σ τ (2 * M) C hk hy ht) _
    _ = S * ENNReal.ofReal (t ^ α * (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) *
          (t ^ 2 * y) ^ (σ - 1 / 2) * ((y ^ 2)⁻¹ * t⁻¹)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1 h2) h3), ENNReal.ofReal_mul (mul_nonneg h1 h2),
          ENNReal.ofReal_mul h1]
        ring
    _ ≤ S * ENNReal.ofReal (C * (t ^ (α - τ + 2 * σ - 2) / (1 + t) ^ M) * y ^ (σ - τ - 5 / 2)) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        rw [show t ^ α * (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * (t ^ 2 * y) ^ (σ - 1 / 2) * ((y ^ 2)⁻¹ * t⁻¹)
          = (t ^ α * (t ^ 2 * y) ^ (σ - 1 / 2)) * (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * ((y ^ 2)⁻¹ * t⁻¹)
          from by ring]
        refine torus_real_bound ht hy hC τ M ?_ (mul_nonneg h1 h3)
        rw [← rpow_collect₁ ht hy α σ τ]
        ring
    _ = Gfun (Wr par default) C (α - τ + 2 * σ - 2) (σ - τ - 5 / 2) M (y, t) := by
        unfold Gfun
        have h5 : 0 ≤ t ^ (α - τ + 2 * σ - 2) / (1 + t) ^ M := by positivity
        rw [ENNReal.ofReal_mul (mul_nonneg hC h5), ENNReal.ofReal_mul hC]
        ring

theorem H2_weight_le (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (par : ZMod 2) (σ : ℝ) (τ M : ℕ) {C : ℝ} (hC : 0 ≤ C) {k : GL (Fin 2) ℝ}
    (hk : k ∈ rowIsometrySubgroup ℝ) {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    H2 (WA par) w₀R σ τ (2 * M) C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) *
        ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹) ≤
      Gfun (Wr par default) C (2 * σ - (P.centralExponent.re + 1) - τ) (σ - (P.centralExponent.re + 1) - τ - 3 / 2)
        M (y, t) := by
  set α : ℝ := P.centralExponent.re + 1 with hα
  set S : ℝ≥0∞ := ‖Wr par default y‖ₑ + ‖Wr par default (-y)‖ₑ with hS
  have hD : 0 < (t * y) ^ τ * (1 + (y + t)) ^ (2 * M) := by positivity
  have h0 : 0 ≤ t ^ 2 * y := by positivity
  have h1 : 0 ≤ ((t * y)⁻¹) ^ α := Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M)) := div_nonneg hC hD.le
  have h3 : 0 ≤ (t ^ 2 * y) ^ (σ - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have h4 : 0 ≤ (y ^ 2)⁻¹ * t⁻¹ := by positivity
  calc H2 (WA par) w₀R σ τ (2 * M) C (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) *
        ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹)
      ≤ (ENNReal.ofReal (t ^ 2 * y) * (ENNReal.ofReal (((t * y)⁻¹) ^ α) * S) *
          ENNReal.ofReal (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * ENNReal.ofReal ((t ^ 2 * y) ^ (σ - 1 / 2))) *
          ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹) :=
        mul_le_mul_left (H2_torus_le P kw Wr WA hWAZ hWAK hWAt w₀R hw₀R par σ τ (2 * M) C hk hy ht) _
    _ = S * ENNReal.ofReal ((t ^ 2 * y * ((t * y)⁻¹) ^ α * (t ^ 2 * y) ^ (σ - 1 / 2)) *
          (C / ((t * y) ^ τ * (1 + (y + t)) ^ (2 * M))) * ((y ^ 2)⁻¹ * t⁻¹)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg h0 h1) h3) h2),
          ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h0 h1) h3), ENNReal.ofReal_mul (mul_nonneg h0 h1),
          ENNReal.ofReal_mul h0]
        ring
    _ ≤ S * ENNReal.ofReal (C * (t ^ (2 * σ - α - τ) / (1 + t) ^ M) * y ^ (σ - α - τ - 3 / 2)) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        refine torus_real_bound ht hy hC τ M ?_ (mul_nonneg (mul_nonneg h0 h1) h3)
        rw [← rpow_collect₂ ht hy α σ τ]
        ring
    _ = Gfun (Wr par default) C (2 * σ - α - τ) (σ - α - τ - 3 / 2) M (y, t) := by
        unfold Gfun
        have h5 : 0 ≤ t ^ (2 * σ - α - τ) / (1 + t) ^ M := by positivity
        rw [ENNReal.ofReal_mul (mul_nonneg hC h5), ENNReal.ofReal_mul hC]
        ring

end TorusWeight

theorem lintegral_Gfun_lt_top {Wr : ℂ → ℂ} {C a b : ℝ} {M : ℕ} (ha : -1 < a) (hM : a + 1 < M)
    (hm₁ : AEMeasurable (fun y : ℝ => Wr y) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hm₂ : AEMeasurable (fun y : ℝ => Wr (-y)) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hb : ∫⁻ y in Set.Ioi (0 : ℝ), (‖Wr y‖ₑ + ‖Wr (-y)‖ₑ) * ENNReal.ofReal (y ^ b) < ⊤) :
    ∫⁻ r in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), Gfun Wr C a b M r < ⊤ := by
  have hG : ∀ r : ℝ × ℝ, Gfun Wr C a b M r = ENNReal.ofReal C *
      (((‖Wr r.1‖ₑ + ‖Wr (-r.1)‖ₑ) * ENNReal.ofReal (r.1 ^ b)) * ENNReal.ofReal (r.2 ^ a / (1 + r.2) ^ M)) :=
    fun r => by unfold Gfun; ring
  simp_rw [hG]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine lintegral_quadrant_prod_lt_top (ψ := fun y => (‖Wr y‖ₑ + ‖Wr (-y)‖ₑ) * ENNReal.ofReal (y ^ b))
    (φ := fun t => ENNReal.ofReal (t ^ a / (1 + t) ^ M)) ?_ ?_ hb (lintegral_rpow_div_one_add_pow_lt_top ha hM)
  · exact (hm₁.enorm.add hm₂.enorm).mul (measurable_id.pow_const b).ennreal_ofReal.aemeasurable
  · exact ((measurable_id.pow_const a).div ((measurable_const.add measurable_id).pow_const M)).ennreal_ofReal.aemeasurable

end Ws23ArchP
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det.Ws23ArchP"

namespace Ws23ArchP

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem lintegral_lt_top_of_majorant :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : Measure realUnipotent) [μN.IsHaarMeasure]
    (ν : Measure (rowIsometrySubgroup ℝ)) [ν.IsHaarMeasure] (_hν : ν Set.univ < ⊤)
    (C₀ : ℝ≥0∞) (_hC₀ : C₀ ≠ ⊤)
    (_hK1 : ∀ (H : GL (Fin 2) ℝ → ENNReal), Measurable H →
        (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, H (n * g) = H g) →
        MeasureTheory.lintegral RSCarrier.archMeasure (fun g => H g * HaarQuotient.density realUnipotent μN g) ≤
          C₀ * MeasureTheory.lintegral ν (fun k : rowIsometrySubgroup ℝ =>
            MeasureTheory.lintegral (volume : Measure (ℝ × ℝ)) (fun q : ℝ × ℝ =>
              if h : 0 < q.1 ∧ 0 < q.2 then
                H (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
                  ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹)
              else 0)))
    (Φ : GL (Fin 2) ℝ → ℂ) (_hΦ : Measurable Φ)
    (H : GL (Fin 2) ℝ → ℝ≥0∞) (_hH : Measurable H) (_hHN : ∀ (x : ℝ) (g : GL (Fin 2) ℝ), H (unipotentGL2 x * g) = H g)
    (_hΦH : ∀ g, ‖Φ g‖ₑ ≤ H g)
    (G : ℝ × ℝ → ℝ≥0∞) (_hG : ∫⁻ r in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G r < ⊤)
    (_hHG : ∀ {k : GL (Fin 2) ℝ}, k ∈ rowIsometrySubgroup ℝ → ∀ {y t : ℝ} (hy : 0 < y) (ht : 0 < t),
      H (upperUnit (t * y) 0 t (mul_pos ht hy).ne' ht.ne' * k) * ENNReal.ofReal ((y ^ 2)⁻¹ * t⁻¹) ≤ G (y, t)),
    ∫⁻ g, ‖Φ g‖ₑ ∂((RSCarrier.archMeasure).withDensity (HaarQuotient.density realUnipotent μN)) < ⊤ := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  intro μN _ ν _ hν C₀ hC₀ hK1 Φ hΦ H hH hHN hΦH G hG hHG
  haveI := secondCountableTopology_GL
  haveI : LocallyCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    isClosed_realUnipotent.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (realUnipotent : Subgroup (GL (Fin 2) ℝ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (realUnipotent : Subgroup (GL (Fin 2) ℝ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  haveI : SFinite μN := instSFiniteOfSigmaFinite
  have hDm : Measurable (HaarQuotient.density realUnipotent μN) := measurable_density _ _
  have hN : ∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, H (n * g) = H g := by
    rintro n ⟨a, rfl⟩ g
    exact hHN a.toAdd g
  calc ∫⁻ g, ‖Φ g‖ₑ ∂((RSCarrier.archMeasure).withDensity (HaarQuotient.density realUnipotent μN))
      = ∫⁻ g, HaarQuotient.density realUnipotent μN g * ‖Φ g‖ₑ ∂(RSCarrier.archMeasure) :=
        lintegral_withDensity_eq_lintegral_mul _ hDm hΦ.enorm
    _ ≤ ∫⁻ g, H g * HaarQuotient.density realUnipotent μN g ∂(RSCarrier.archMeasure) :=
        lintegral_mono fun g => by rw [mul_comm]; exact mul_le_mul_left (hΦH g) _
    _ ≤ C₀ * ∫⁻ k, ∫⁻ q : ℝ × ℝ, (if h : 0 < q.1 ∧ 0 < q.2 then
            H (upperUnit (q.2 * q.1) 0 q.2 (mul_pos h.2 h.1).ne' h.2.ne' * (k : GL (Fin 2) ℝ)) *
              ENNReal.ofReal ((q.1 ^ 2)⁻¹ * q.2⁻¹) else 0) ∂volume ∂ν := hK1 H hH hN
    _ ≤ C₀ * ∫⁻ k, ∫⁻ q : ℝ × ℝ, (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator G q ∂volume ∂ν := by
        refine mul_le_mul_right (lintegral_mono fun k => lintegral_mono fun q => ?_) _
        by_cases h : 0 < q.1 ∧ 0 < q.2
        · rw [dif_pos h, Set.indicator_of_mem (show q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) from Set.mem_prod.2 ⟨h.1, h.2⟩) G]
          exact hHG k.2 h.1 h.2
        · rw [dif_neg h]
          exact zero_le
    _ = C₀ * ((∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G q ∂volume) * ν Set.univ) := by
        have e1 : ∫⁻ q : ℝ × ℝ, (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)).indicator G q ∂volume =
            ∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G q ∂volume :=
          lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioi) _
        have e2 : ∫⁻ _k : (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)),
            (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G q ∂volume) ∂ν =
            (∫⁻ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G q ∂volume) * ν Set.univ := lintegral_const _
        rw [← e2]
        congr 1
        exact lintegral_congr fun k => e1
    _ < ⊤ := ENNReal.mul_lt_top hC₀.lt_top (ENNReal.mul_lt_top hG hν)

end Ws23ArchP
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det.Ws23ArchP"

open Ws23ArchP AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates in
open scoped Classical in

theorem solution
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * x) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])

    (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (hWarch : (Continuous Warch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖Warch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)))
    (par₀ : ZMod 2) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μN : MeasureTheory.Measure RSCarrier.realUnipotent) [μN.IsHaarMeasure],
    ∃ σI : ℝ,
      (∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
        (fun g : GL (Fin 2) ℝ =>
          (WA par₀ g * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))) ∧
      (∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
        (fun g : GL (Fin 2) ℝ =>
          ((((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv g)) *
              dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
            (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
  intro μN _

  obtain ⟨s₁, hL1, hm₁, hm₂⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_lintegral_norm_torusProfile_mul_rpow_lt_top P Wr hWr1 hWr2 hWr3 hWr4 par₀
  obtain ⟨hWc, τ, hdecay⟩ := hWarch
  set α : ℝ := P.centralExponent.re + 1 with hα

  haveI := secondCountableTopology_GL
  haveI := locallyCompactSpace_GL
  haveI : SecondCountableTopology (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    isClosed_rowIsometrySubgroup.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : CompactSpace (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) :=
    isCompact_iff_compactSpace.1 isCompact_rowIsometrySubgroup
  let ν : Measure (rowIsometrySubgroup ℝ : Subgroup (GL (Fin 2) ℝ)) := Measure.haar
  have hν : ν Set.univ < ⊤ := IsCompact.measure_lt_top isCompact_univ
  obtain ⟨C₀, hC₀, hK1⟩ :=
    LanglandsTunnell.Converse.exists_lintegral_mul_density_archMeasure_le_lintegral_iwasawa μN ν

  refine ⟨|α| + τ + |s₁| + 3, fun s hs => ?_, fun s hs => ?_⟩
  ·
    set σ : ℝ := s.re with hσ
    have hαa := le_abs_self α
    have hαb := neg_abs_le α
    have hsa := le_abs_self s₁
    have hsb := neg_abs_le s₁
    have ha : -1 < α - τ + 2 * σ - 2 := by linarith
    have hb : s₁ < σ - τ - 5 / 2 := by linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (α - τ + 2 * σ - 2 + 1)
    obtain ⟨C, hC⟩ := hdecay (2 * M)
    have hC0 : 0 ≤ C := by
      have h := (norm_nonneg _).trans (norm_Warch_le Warch τ (2 * M) C hC 1).1
      unfold bnd at h
      rcases div_nonneg_iff.1 h with h' | h'
      · exact h'.1
      · exact absurd h'.2 (not_le.2 (bnd_denom_pos τ (2 * M) 1))
    have hΦm : Measurable (fun g : GL (Fin 2) ℝ =>
        (WA par₀ g * Warch (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
          (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) :=
      (((hWAc par₀).mul (hWc.comp Ws23ArchM.continuous_Φ)).measurable).mul
        (Ws23ArchM.continuous_absDet.measurable.pow_const _)
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    exact lintegral_lt_top_of_majorant μN ν hν C₀ hC₀ hK1 _ hΦm (H1 (WA par₀) σ τ (2 * M) C)
      (measurable_H1 (hWAc par₀) σ τ (2 * M) C) (H1_unipotent_mul (hWAN par₀) σ τ (2 * M) C)
      (enorm_integrand₁_le Warch τ (2 * M) C hC s)
      (Gfun (Wr par₀ default) C (α - τ + 2 * σ - 2) (σ - τ - 5 / 2) M)
      (lintegral_Gfun_lt_top ha hM hm₁ hm₂ (hL1 _ hb))
      (fun hk y t hy ht => H1_weight_le P kw Wr WA hWAZ hWAK hWAt par₀ σ τ M hC0 hk hy ht)
  ·
    set σ : ℝ := s.re with hσ
    have hαa := le_abs_self α
    have hαb := neg_abs_le α
    have hsa := le_abs_self s₁
    have hsb := neg_abs_le s₁
    have ha : -1 < 2 * σ - α - τ := by linarith
    have hb : s₁ < σ - α - τ - 3 / 2 := by linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * σ - α - τ + 1)
    obtain ⟨C, hC⟩ := hdecay (2 * M)
    have hC0 : 0 ≤ C := by
      have h := (norm_nonneg _).trans (norm_Warch_le Warch τ (2 * M) C hC 1).1
      unfold bnd at h
      rcases div_nonneg_iff.1 h with h' | h'
      · exact h'.1
      · exact absurd h'.2 (not_le.2 (bnd_denom_pos τ (2 * M) 1))
    have hΦm : Measurable (fun g : GL (Fin 2) ℝ =>
        ((((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv g)) *
            dualWhittakerFn3 Warch (archComponent3 (𝓞 ℚ) ℚ
              (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
          (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) := by
      refine Measurable.mul ?_ (Ws23ArchM.continuous_absDet.measurable.pow_const _)
      refine ((Ws23ArchM.continuous_absDet.mul ((hWAc par₀).comp
        (continuous_const.mul Ws23ArchM.continuous_transposeInv))).mul ?_).measurable
      simp_rw [dualWhittakerFn3_apply]
      exact hWc.comp (continuous_const.mul (Ws23ArchM.continuous_transposeInv3.comp Ws23ArchM.continuous_Φ))
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    exact lintegral_lt_top_of_majorant μN ν hν C₀ hC₀ hK1 _ hΦm (H2 (WA par₀) w₀R σ τ (2 * M) C)
      (measurable_H2 w₀R (hWAc par₀) σ τ (2 * M) C) (H2_unipotent_mul w₀R hw₀R (hWAN par₀) σ τ (2 * M) C)
      (enorm_integrand₂_le w₀R Warch τ (2 * M) C hC s)
      (Gfun (Wr par₀ default) C (2 * σ - α - τ) (σ - α - τ - 3 / 2) M)
      (lintegral_Gfun_lt_top ha hM hm₁ hm₂ (hL1 _ hb))
      (fun hk y t hy ht => H2_weight_le P kw Wr WA hWAZ hWAK hWAt w₀R hw₀R par₀ σ τ M hC0 hk hy ht)

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det.Ws23ArchP"

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_archWhittaker_torusPair_rpow_det (solution)
