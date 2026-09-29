-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9b9f187c-0ad6-5d50-a5be-2926c850e86b

import Mathlib
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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_rational_godementZeta2_whittaker_of_forall_torusZeta_fe
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Mathlib.Analysis.Matrix.Normed
import Theorems.Thm_LanglandsTunnell_CubicInduction_isSchwartzBruhat_matFourier22
import Theorems.Thm_LanglandsTunnell_RankinSelberg_matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_matFourier22_mul_eq_integral_mul_matFourier22
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val Submodule.finiteAdeleEvalAt_tmul Submodule.val_finiteIdeleDiagonal_apply QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors ENNReal NNReal
open NumberField.AdelicLevel (diagOne)
noncomputable section

open scoped Matrix

namespace E3ReduceSupply

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

def L32 (x : Qp) : LocalGL3 p where
  val := !![1, 0, 0; 0, 1, 0; 0, x, 1]
  inv := !![1, 0, 0; 0, 1, 0; 0, -x, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

def X (g : G2) : LocalGL3 p := longWeyl3 * transposeInv3 (iotaGL g) * longWeyl3

theorem X_def (g : G2) : X p g = longWeyl3 * transposeInv3 (iotaGL g) * longWeyl3 := rfl

theorem unipotent_coe' (x : Qp) : ((unipotent x : G2) : Matrix (Fin 2) (Fin 2) Qp) = !![1, x; 0, 1] := rfl

theorem diagUnitGL2_coe' (x : Qpˣ) : ((diagUnitGL2 x : G2) : Matrix (Fin 2) (Fin 2) Qp) = !![(x : Qp), 0; 0, 1] := rfl

theorem L32_coe (x : Qp) : ((L32 p x : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp) = !![1, 0, 0; 0, 1, 0; 0, x, 1] := rfl

theorem diagonal3_coe (a : Fin 3 → Qpˣ) :
    ((diagonal3 p a : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp) = Matrix.diagonal fun i => (a i : Qp) := rfl

theorem diagonal3_coe' (a b c : (Qp)ˣ) :
    ((diagonal3 p ![a, b, c] : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp) = !![(a : Qp), 0, 0; 0, (b : Qp), 0; 0, 0, (c : Qp)] := by
  rw [diagonal3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem scalar2_coe (u : Qpˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : Matrix (Fin 2) (Fin 2) Qp) = !![(u : Qp), 0; 0, (u : Qp)] := by
  show Matrix.scalar (Fin 2) (u : Qp) = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar]

theorem w0_mul_w0 (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0]) : w₀p * w₀p = 1 := by
  apply Units.ext
  rw [Units.val_mul, hw₀p, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem w0_inv (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0]) : w₀p⁻¹ = w₀p :=
  inv_eq_of_mul_eq_one_right (w0_mul_w0 p w₀p hw₀p)

theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : LocalGL3 p) * longWeyl3 = 1 := by
  apply Units.ext
  rw [Units.val_mul, longWeyl3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_lower (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0]) (x : Qp) :
    ((w₀p * unipotent x * w₀p : G2) : Matrix (Fin 2) (Fin 2) Qp) = !![1, 0; x, 1] := by
  rw [Units.val_mul, Units.val_mul, hw₀p, unipotent_coe']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_cell (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0]) (d a : Qpˣ) (x : Qp) :
    ((diagUnits2 d a * (w₀p * unipotent (-x) * w₀p) : G2) : Matrix (Fin 2) (Fin 2) Qp) =
      !![(d : Qp), 0; -((a : Qp) * x), (a : Qp)] := by
  rw [Units.val_mul, coe_lower p w₀p hw₀p, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transposeInv3_mul (g h : LocalGL3 p) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  show (((g * h)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp)ᵀ =
    (((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp))ᵀ * (((h⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp))ᵀ
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_eq_of_mul_transpose_eq_one (u v : LocalGL3 p)
    (h : (u : Matrix (Fin 3) (Fin 3) Qp) * (v : Matrix (Fin 3) (Fin 3) Qp)ᵀ = 1) : transposeInv3 u = v := by
  apply Units.ext
  show (((u⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp))ᵀ = (v : Matrix (Fin 3) (Fin 3) Qp)
  rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv h, Matrix.transpose_transpose]

theorem transposeInvN_eq_of_mul_transpose_eq_one (u v : G2)
    (h : (u : Matrix (Fin 2) (Fin 2) Qp) * (v : Matrix (Fin 2) (Fin 2) Qp)ᵀ = 1) : transposeInvN (Fin 2) u = v := by
  apply Units.ext
  rw [coe_transposeInvN, Matrix.coe_units_inv, Matrix.inv_eq_right_inv h, Matrix.transpose_transpose]

theorem exists_eq_unipotent_of_mem_range (n : G2) (hn : n ∈ (unipotentGL2Hom (R := Qp)).range) :
    ∃ y : Qp, n = unipotent y := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨Multiplicative.toAdd m, Units.ext rfl⟩

theorem unipotent_mem_range (y : Qp) : (unipotent y : G2) ∈ (unipotentGL2Hom (R := Qp)).range :=
  ⟨Multiplicative.ofAdd y, Units.ext rfl⟩

theorem entry11_unipotent_mul (y : Qp) (g : G2) :
    ((unipotent y * g : G2) : Matrix (Fin 2) (Fin 2) Qp) 1 1 = (g : Matrix (Fin 2) (Fin 2) Qp) 1 1 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotent_coe']
  simp

theorem entry10_unipotent_mul (y : Qp) (g : G2) :
    ((unipotent y * g : G2) : Matrix (Fin 2) (Fin 2) Qp) 1 0 = (g : Matrix (Fin 2) (Fin 2) Qp) 1 0 := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotent_coe']
  simp

theorem det_unipotent' (y : Qp) : Matrix.GeneralLinearGroup.det (unipotent y : G2) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_coe', Matrix.det_fin_two_of]
  simp

theorem det_unipotent_mul (y : Qp) (g : G2) :
    Matrix.GeneralLinearGroup.det (unipotent y * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, det_unipotent', one_mul]

theorem cell_entry11 (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (d a : Qpˣ) (x : Qp) :
    ((diagUnits2 d a * (w₀p * unipotent (-x) * w₀p) : G2) : Matrix (Fin 2) (Fin 2) Qp) 1 1 = (a : Qp) := by
  rw [coe_cell p w₀p hw₀p]; simp

theorem cell_entry10 (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (d a : Qpˣ) (x : Qp) :
    ((diagUnits2 d a * (w₀p * unipotent (-x) * w₀p) : G2) : Matrix (Fin 2) (Fin 2) Qp) 1 0 = -((a : Qp) * x) := by
  rw [coe_cell p w₀p hw₀p]; simp

theorem cell_det (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (d a : Qpˣ) (x : Qp) :
    Matrix.GeneralLinearGroup.det (diagUnits2 d a * (w₀p * unipotent (-x) * w₀p)) = d * a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_cell p w₀p hw₀p, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem cell_dualArg (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (d a : Qpˣ) (x : Qp) :
    w₀p * transposeInvN (Fin 2) (diagUnits2 d a * (w₀p * unipotent (-x) * w₀p)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent x) := by
  have key : transposeInvN (Fin 2) (diagUnits2 d a * (w₀p * unipotent (-x) * w₀p)) =
      w₀p * (Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent x)) := by
    apply transposeInvN_eq_of_mul_transpose_eq_one
    rw [coe_cell p w₀p hw₀p, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hw₀p, scalar2_coe,
      diagUnitGL2_coe', unipotent_coe', Units.val_inv_eq_inv_val, Units.val_mul, Units.val_inv_eq_inv_val]
    have ha : (a : Qp) ≠ 0 := a.ne_zero
    have hd : (d : Qp) ≠ 0 := d.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring
  rw [key, ← mul_assoc, w0_mul_w0 p w₀p hw₀p, one_mul]

theorem dualArg_unipotent_mul (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (y : Qp) (g : G2) :
    w₀p * transposeInvN (Fin 2) (unipotent y * g) = unipotent (-y) * (w₀p * transposeInvN (Fin 2) g) := by
  have key : transposeInvN (Fin 2) (unipotent y : G2) = w₀p * unipotent (-y) * w₀p := by
    apply transposeInvN_eq_of_mul_transpose_eq_one
    rw [coe_lower p w₀p hw₀p, unipotent_coe']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  rw [transposeInvN_mul, key, ← mul_assoc, ← mul_assoc, ← mul_assoc, w0_mul_w0 p w₀p hw₀p, one_mul, mul_assoc]

theorem iotaGL_unipotent (y : Qp) : iotaGL (unipotent y : G2) = upperUnipotent3 y 0 0 := by
  have : (unipotent y : G2) = unipotentGL2 y := Units.ext rfl
  rw [this, iotaGL_unipotentGL2]

theorem X_unipotent_mul (y : Qp) (g : G2) :
    X p (unipotent y * g) = upperUnipotent3 0 (-y) 0 * X p g := by
  have key : transposeInv3 (iotaGL (unipotent y : G2)) = longWeyl3 * upperUnipotent3 0 (-y) 0 * longWeyl3 := by
    apply transposeInv3_eq_of_mul_transpose_eq_one
    rw [iotaGL_unipotent, Units.val_mul, Units.val_mul, longWeyl3_coe, upperUnipotent3_coe, upperUnipotent3_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  rw [X_def, X_def, map_mul, transposeInv3_mul, key]
  have hw := longWeyl3_mul_longWeyl3 p
  calc longWeyl3 * (longWeyl3 * upperUnipotent3 0 (-y) 0 * longWeyl3 * transposeInv3 (iotaGL g)) * longWeyl3
      = (longWeyl3 * longWeyl3) * upperUnipotent3 0 (-y) 0 * (longWeyl3 * transposeInv3 (iotaGL g) * longWeyl3) := by
        group
    _ = upperUnipotent3 0 (-y) 0 * (longWeyl3 * transposeInv3 (iotaGL g) * longWeyl3) := by rw [hw, one_mul]

theorem X_cell (w₀p : G2) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) Qp) = !![0, 1; 1, 0])
    (d a : Qpˣ) (x : Qp) :
    X p (diagUnits2 d a * (w₀p * unipotent (-x) * w₀p)) = diagonal3 p ![1, a⁻¹, d⁻¹] * L32 p x := by
  have key : transposeInv3 (iotaGL (diagUnits2 d a * (w₀p * unipotent (-x) * w₀p) : G2)) =
      longWeyl3 * (diagonal3 p ![1, a⁻¹, d⁻¹] * L32 p x) * longWeyl3 := by
    apply transposeInv3_eq_of_mul_transpose_eq_one
    rw [coe_iotaGL, coe_cell p w₀p hw₀p, Units.val_mul, Units.val_mul, Units.val_mul, longWeyl3_coe, diagonal3_coe',
      L32_coe, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_one]
    have ha : (a : Qp) ≠ 0 := a.ne_zero
    have hd : (d : Qp) ≠ 0 := d.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, embedMat2] <;> ring
  rw [X_def, key]
  have hw := longWeyl3_mul_longWeyl3 p
  calc longWeyl3 * (longWeyl3 * (diagonal3 p ![1, a⁻¹, d⁻¹] * L32 p x) * longWeyl3) * longWeyl3
      = (longWeyl3 * longWeyl3) * (diagonal3 p ![1, a⁻¹, d⁻¹] * L32 p x) * (longWeyl3 * longWeyl3) := by group
    _ = diagonal3 p ![1, a⁻¹, d⁻¹] * L32 p x := by rw [hw, one_mul, mul_one]

theorem modulus_eq_one_of_valued_eq_one (t : Qp) (ht : Valued.v t = 1) : modulus t = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p t]
  ext
  rw [coe_nnnorm, NumberField.FinitePlace.norm_def, ht, map_one]

theorem continuous_of_rightInvariant {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (F : G → ℂ) (hF : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, F (g * k) = F g) :
    Continuous F := by
  obtain ⟨U, hU, hinv⟩ := hF
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show F (g * k) ∈ s
    rw [hinv k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

theorem continuous_entry (i j : Fin 2) : Continuous (fun g : G2 => (g : Matrix (Fin 2) (Fin 2) Qp) i j) :=
  Units.continuous_val.matrix_elem i j

theorem continuous_inv_entry (i j : Fin 2) : Continuous (fun g : G2 => ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) Qp) i j) :=
  Units.continuous_coe_inv.matrix_elem i j

theorem continuous_inv_entry' (i j : Fin 2) :
    Continuous (fun g : G2 => ((g : Matrix (Fin 2) (Fin 2) Qp)⁻¹) i j) := by
  have h := continuous_inv_entry p i j
  simp only [Matrix.coe_units_inv] at h
  exact h

theorem continuous_iotaGL : Continuous (iotaGL : G2 → LocalGL3 p) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : G2 => ((iotaGL g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp)
    simp only [coe_iotaGL, embedMat2]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact continuous_const | exact continuous_entry p _ _
  · show Continuous fun g : G2 => (((iotaGL g)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp)
    simp only [← map_inv, coe_iotaGL, embedMat2]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;>
      first | exact continuous_const | exact continuous_inv_entry p _ _ | exact continuous_inv_entry' p _ _

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 p → LocalGL3 p) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : LocalGL3 p => ((transposeInv3 g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp)
    exact (@Units.continuous_coe_inv (Matrix (Fin 3) (Fin 3) Qp) _ _).matrix_transpose
  · show Continuous fun g : LocalGL3 p => (((transposeInv3 g)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) Qp)
    exact (@Units.continuous_val (Matrix (Fin 3) (Fin 3) Qp) _ _).matrix_transpose

theorem continuous_transposeInvN : Continuous (transposeInvN (Fin 2) : G2 → G2) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : G2 => ((transposeInvN (Fin 2) g : G2) : Matrix (Fin 2) (Fin 2) Qp)
    simp only [coe_transposeInvN]
    exact (@Units.continuous_coe_inv (Matrix (Fin 2) (Fin 2) Qp) _ _).matrix_transpose
  · show Continuous fun g : G2 => (((transposeInvN (Fin 2) g)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) Qp)
    simp only [coe_inv_transposeInvN]
    exact (@Units.continuous_val (Matrix (Fin 2) (Fin 2) Qp) _ _).matrix_transpose

theorem continuous_X : Continuous (X p) :=
  (continuous_const.mul ((continuous_transposeInv3 p).comp (continuous_iotaGL p))).mul continuous_const

theorem continuous_dualArg (w₀p : G2) : Continuous (fun g : G2 => w₀p * transposeInvN (Fin 2) g) :=
  continuous_const.mul (continuous_transposeInvN p)

theorem continuous_modulus_det :
    Continuous (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ))) := by
  have h : (fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ))) =
      fun g : G2 => ‖((g : Matrix (Fin 2) (Fin 2) Qp)).det‖ := by
    funext g
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm,
      Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  exact (Units.continuous_val.matrix_det).norm

theorem modulus_det_pos (g : G2) : 0 < ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ)) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm, norm_pos_iff]
  exact (Matrix.GeneralLinearGroup.det g).ne_zero

theorem isCompact_localLevelOne :
    IsCompact (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) := by
  have h : (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G2) = AutomorphicForm.localIntegralSet ℚ p := by
    ext k
    rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, AutomorphicForm.mem_localIntegralSet]
    constructor
    · intro hk; exact ⟨hk.1.integral, hk.2.integral⟩
    · intro hk
      have aux : ∀ m : Matrix (Fin 2) (Fin 2) Qp, (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) →
          AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := fun m hm =>
        ⟨hm, by rw [AdelicLevel.idealBound_top]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0),
          by
            rw [AdelicLevel.idealBound_top, sub_eq_add_neg]
            exact (Valuation.map_add _ _ _).trans (max_le
              ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 1)) (by simp))⟩
      exact ⟨aux _ hk.1, aux _ hk.2⟩
  rw [h]; exact AutomorphicForm.isCompact_localIntegralSet ℚ p

end E3ReduceSupply

end

noncomputable section

namespace E3ReduceSupplyF

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ

theorem level_zero :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : Qp, Valued.v x ≤ WithZero.exp k → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
    (NumberField.StandardAddChar.psiLocal ℚ p) hk (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem level_zero_inv :
    (∀ x : Qp, Valued.v x ≤ WithZero.exp (0 : ℤ) → (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x = 1) ∧
      ∃ x : Qp, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x ≠ 1 := by
  obtain ⟨h0, h1⟩ := level_zero p
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [AddChar.inv_apply]; exact h0 (-x) (by rwa [Valuation.map_neg])
  · obtain ⟨x, hx, hne⟩ := h1
    refine ⟨-x, by rwa [Valuation.map_neg], ?_⟩
    rwa [AddChar.inv_apply, neg_neg]

theorem selfDualHaarAt_eq :
    selfDualHaarAt ℚ p = @Measure.addHaarMeasure (p.adicCompletion ℚ) _ _ _ (localBorel ℚ p)
      (borelSpace_localBorel ℚ p) (integersPositiveCompacts ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
  simp

private theorem _root_.E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

p2m_export "E3ReduceSupplyF" "isAddHaarMeasure_selfDualHaarAt"
theorem isSchwartzBruhat_tateFourier_psiLocal_inv (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h0, h1⟩ := level_zero_inv p
  exact LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier ℚ p (selfDualHaarAt ℚ p)
    ((NumberField.StandardAddChar.psiLocal ℚ p)⁻¹) 0 h0 h1 φ hφ

theorem continuous_tateFourier_of_isSchwartzBruhat (φ : Qp → ℂ) (hφ : IsSchwartzBruhat φ) :
    letI := localBorel ℚ p
    Continuous (tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ) :=
  (isSchwartzBruhat_tateFourier_psiLocal_inv p φ hφ).1.continuous

end E3ReduceSupplyF

namespace RCgB

section LocalField

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)

def qR : ℝ := ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ)

theorem one_lt_qR : 1 < qR v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [qR]; exact_mod_cast this

theorem qR_pos : 0 < qR v := zero_lt_one.trans (one_lt_qR v)

theorem qR_ne_zero : qR v ≠ 0 := (qR_pos v).ne'

theorem norm_le_one_iff (x : F) : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem norm_eq_one_iff (x : F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

theorem norm_eq_zpow_of_v_eq_exp (x : F) (m : ℤ) (hx : Valued.v x = WithZero.exp m) : ‖x‖ = qR v ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero,
    NNReal.coe_zpow, qR]
  congr 1

theorem coe_modulus_eq_norm (x : F) : ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm]

variable {v}

theorem uniformizer_ne_zero {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem norm_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    ‖ϖ ^ k‖ = qR v ^ (-k) :=
  norm_eq_zpow_of_v_eq_exp v _ _ (v_uniformizer_zpow hϖ k)

end LocalField

section Kzero

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral v h1, isLocalLevelOne_top_of_integral v h2⟩

theorem coe_kzero_eq_localIntegralSet : ((kzero v : Subgroup G) : Set G) = localIntegralSet ℚ v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet ℚ v

theorem isCompact_kzero : IsCompact ((kzero v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet ℚ v

variable {v}

theorem v_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : Valued.v ((k : Mat) i j) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (((mem_kzero_iff v k).mp hk).1 i j)

theorem norm_entry_le_one {k : G} (hk : k ∈ kzero v) (i j : Fin 2) : ‖(k : Mat) i j‖ ≤ 1 :=
  (norm_le_one_iff v _).mpr (v_entry_le_one hk i j)

theorem v_det_le_one_of_integral {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
      ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
    _ ≤ 1 := by
        refine max_le ?_ ?_
        · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
        · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one {k : G} (hk : k ∈ kzero v) : Valued.v (k : Mat).det = 1 := by
  have h1 : Valued.v (k : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one hk)
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := v_det_le_one_of_integral (v_entry_le_one (inv_mem hk))
  have hprod : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hprod.symm
    _ ≤ Valued.v (k : Mat).det * 1 := by gcongr
    _ = Valued.v (k : Mat).det := mul_one _

theorem norm_det_eq_one {k : G} (hk : k ∈ kzero v) : ‖(k : Mat).det‖ = 1 :=
  (norm_eq_one_iff v _).mpr (v_det_eq_one hk)

theorem max_norm_bottom_row_eq_one {k : G} (hk : k ∈ kzero v) :
    max ‖(k : Mat) 1 0‖ ‖(k : Mat) 1 1‖ = 1 := by
  have hle := v_entry_le_one hk

  have hdet : (1 : WithZero (Multiplicative ℤ)) ≤ max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := by
    rw [← v_det_eq_one hk, Matrix.det_fin_two]
    calc Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0)
        ≤ max (Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1)) (Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0)) :=
          Valuation.map_sub _ _ _
      _ ≤ max (Valued.v ((k : Mat) 1 1)) (Valued.v ((k : Mat) 1 0)) := by
          refine max_le_max ?_ ?_
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 0)
          · rw [map_mul]; exact mul_le_of_le_one_left' (hle 0 1)
      _ = max (Valued.v ((k : Mat) 1 0)) (Valued.v ((k : Mat) 1 1)) := max_comm _ _
  have hn0 : ‖(k : Mat) 1 0‖ ≤ 1 := norm_entry_le_one hk 1 0
  have hn1 : ‖(k : Mat) 1 1‖ ≤ 1 := norm_entry_le_one hk 1 1
  rcases le_max_iff.mp hdet with h | h
  · have h' : Valued.v ((k : Mat) 1 0) = 1 := le_antisymm (hle 1 0) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_left hn1
  · have h' : Valued.v ((k : Mat) 1 1) = 1 := le_antisymm (hle 1 1) h
    rw [(norm_eq_one_iff v _).mpr h']
    exact max_eq_right hn0

end Kzero

section Torus

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F), 0;
    0, ((b⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    ((diagU v a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    (diagU v a b)⁻¹ = diagU v a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU v a b : G) : Mat) * ((diagU v a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagU_mul (a b a' b' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
    diagU v a b * diagU v a' b' = diagU v (a * a') (b * b') := by
  refine Units.ext ?_
  change ((diagU v a b : G) : Mat) * ((diagU v a' b' : G) : Mat) = ((diagU v (a * a') (b * b') : G) : Mat)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagUHom : (HeightOneSpectrum.adicCompletion ℚ v)ˣ × (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* G where
  toFun p := diagU v p.1 p.2
  map_one' := by
    refine Units.ext ?_
    change ((diagU v 1 1 : G) : Mat) = 1
    rw [coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p p' := (diagU_mul v p.1 p.2 p'.1 p'.2).symm

theorem diagU_zpow (a b : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (n : ℤ) :
    (diagU v a b) ^ n = diagU v (a ^ n) (b ^ n) := by
  change (diagUHom v (a, b)) ^ n = diagUHom v ((a, b) ^ n)
  rw [map_zpow]

variable {v}
variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

def piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ :=
  Units.mk0 (algebraMap (O) (F) ϖ) hπ

@[scoped simp] theorem coe_piUnit (hπ : algebraMap (O) (F) ϖ ≠ 0) : ((piUnit hπ : _ˣ) : F) = algebraMap (O) (F) ϖ := rfl

theorem coe_piUnit_zpow (hπ : algebraMap (O) (F) ϖ ≠ 0) (k : ℤ) :
    (((piUnit hπ) ^ k : _ˣ) : F) = (algebraMap (O) (F) ϖ) ^ k := by
  rw [Units.val_zpow_eq_zpow_val, coe_piUnit]

theorem scalarPi_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = diagU v (piUnit hπ) (piUnit hπ) := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [scalarPi, piUnit]

theorem diagZ_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (d : ℤ) :
    diagZ (algebraMap (O) (F) ϖ) hπ d = diagU v (piUnit hπ ^ d) 1 := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

theorem shellRep_eq_diagU (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagU v (piUnit hπ ^ (dn.2 + dn.1)) (piUnit hπ ^ dn.2) := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, zpow_add, mul_one]

theorem shellRep_eq_diagZ_mul (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 := by
  rw [scalarPi_eq_diagU hπ, diagZ_eq_diagU hπ, diagU_zpow, diagU_mul, diagU_mul, mul_one, one_mul, mul_comm]

theorem scalarPi_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    scalarPi (algebraMap (O) (F) ϖ) hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, piUnit, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem scalarPi_zpow_eq_scalar (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n = Matrix.GeneralLinearGroup.scalar (Fin 2) (piUnit hπ ^ n) := by
  rw [scalarPi_eq_scalar hπ, map_zpow]

end Torus

end RCgB
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace BPhi

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem exists_radius_of_isLocallyConstant_of_hasCompactSupport {X : Type*} [MetricSpace X]
    (f : X → ℂ) (hlc : IsLocallyConstant f) (hcs : HasCompactSupport f) :
    ∃ δ > 0, ∀ x y : X, dist x y < δ → f x = f y := by
  obtain ⟨δ, hδ, hU⟩ := lebesgue_number_lemma_of_metric (ι := X) (c := fun i => {y | f y = f i}) hcs
    (fun i => hlc.isOpen_fiber (f i)) (fun x _ => Set.mem_iUnion.2 ⟨x, rfl⟩)
  refine ⟨δ, hδ, ?_⟩
  have key : ∀ x ∈ tsupport f, ∀ y, dist x y < δ → f x = f y := by
    intro x hx y hxy
    obtain ⟨i, hi⟩ := hU x hx
    have h1 : f x = f i := hi (Metric.mem_ball_self hδ)
    have h2 : f y = f i := hi (by rw [Metric.mem_ball, dist_comm]; exact hxy)
    rw [h1, h2]
  intro x y hxy
  by_cases hx : x ∈ tsupport f
  · exact key x hx y hxy
  by_cases hy : y ∈ tsupport f
  · exact (key y hy x (by rw [dist_comm]; exact hxy)).symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

theorem isLocallyConstant_psiLocal : IsLocallyConstant (fun t : F => (psiLocal ℚ p t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]; exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h1 : psiLocal ℚ p (y - x) = 1 := by
    apply (E3ReduceSupplyF.level_zero p).1
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_psiLocal : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) :=
  (isLocallyConstant_psiLocal p).continuous

theorem norm_le_zpow_iff {ϖ : O} (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ)) (x : F) (m : ℤ) :
    ‖x‖ ≤ RCgB.qR p ^ m ↔ Valued.v x ≤ WithZero.exp m := by
  have h := RCgB.norm_uniformizer_zpow (v := p) hϖ (-m)
  rw [neg_neg] at h
  rw [← h, Valued.toNormedField.norm_le_iff, RCgB.v_uniformizer_zpow hϖ, neg_neg]

theorem exists_constancy_exponent (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ c : ℤ, ∀ X Y : Mat, (∀ i j, ‖Y i j‖ ≤ RCgB.qR p ^ (-c)) → Φ (X + Y) = Φ X := by
  letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
  obtain ⟨δ, hδ, hunif⟩ := exists_radius_of_isLocallyConstant_of_hasCompactSupport Φ hΦ hΦc

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (RCgB.qR p)⁻¹ ^ n < δ :=
    exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ (RCgB.one_lt_qR p))
  refine ⟨n, fun X Y hY => ?_⟩
  refine (hunif X (X + Y) ?_).symm
  rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
  refine lt_of_le_of_lt ?_ hn
  rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  exact (Matrix.norm_le_iff (zpow_nonneg (RCgB.qR_pos p).le _)).2 hY

theorem exists_support_exponent (Φ : Mat → ℂ) (hΦc : HasCompactSupport Φ) :
    ∃ M : ℤ, ∀ X : Mat, Φ X ≠ 0 → ∀ i j, ‖X i j‖ ≤ RCgB.qR p ^ M := by
  letI : NormedAddCommGroup Mat := Matrix.normedAddCommGroup
  obtain ⟨R, hR⟩ := hΦc.isCompact.isBounded.subset_closedBall 0 |>.imp fun R h => h

  obtain ⟨n, hn⟩ : ∃ n : ℕ, R < RCgB.qR p ^ n := pow_unbounded_of_one_lt R (RCgB.one_lt_qR p)
  refine ⟨n, fun X hX i j => ?_⟩
  have hXs : X ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hX)
  have h1 : ‖X‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hXs
  rw [zpow_natCast]
  exact ((Matrix.norm_entry_le_entrywise_sup_norm X).trans h1).trans hn.le

theorem exists_bound (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ A : ℝ, ∀ X : Mat, ‖Φ X‖ ≤ A :=
  hΦ.continuous.bounded_above_of_compact_support hΦc

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}

theorem diagUnitGL2_eq_diagU (w : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    (diagUnitGL2 w : G) = RCgB.diagU p w 1 :=
  Units.ext (by rw [RCgB.coe_diagU, coe_diagUnitGL2]; simp)

theorem shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) (n₁ n₂ : ℤ) (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (k : G) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n₂ * diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n₁ * u) * k =
      RCgB.diagU p (RCgB.piUnit hπ ^ n₂ * (RCgB.piUnit hπ ^ n₁ * u)) (RCgB.piUnit hπ ^ n₂) * k := by
  rw [RCgB.scalarPi_eq_diagU hπ, RCgB.diagU_zpow, diagUnitGL2_eq_diagU, RCgB.diagU_mul, mul_one]
  rfl

theorem unipotent_mul_diagU_mul_apply (x : F) (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (k : G) :
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 1 0 = (b : F) * (k : Mat) 1 0 ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 1 1 = (b : F) * (k : Mat) 1 1 ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 0 = (a : F) * (k : Mat) 0 0 + x * ((b : F) * (k : Mat) 1 0) ∧
    ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 1 = (a : F) * (k : Mat) 0 1 + x * ((b : F) * (k : Mat) 1 1) := by
  have hu : ((unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl
  simp only [Units.val_mul, hu, RCgB.coe_diagU, Matrix.mul_apply, Fin.sum_univ_two]
  simp

end BPhi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace BPhi

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem unipotent_coe'' (x : F) : ((unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem unipotent_mul_apply (x : F) (g : G) (j : Fin 2) :
    ((unipotent x * g : G) : Mat) 1 j = (g : Mat) 1 j ∧
    ((unipotent x * g : G) : Mat) 0 j = (g : Mat) 0 j + x * (g : Mat) 1 j := by
  simp only [Units.val_mul, unipotent_coe'', Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j <;> simp

theorem continuous_unipotent_mul_coe (g : G) : Continuous fun x : F => ((unipotent x * g : G) : Mat) := by
  have : (fun x : F => ((unipotent x * g : G) : Mat)) = fun x => (!![(1 : F), x; 0, 1] : Mat) * (g : Mat) := by
    funext x; rw [Units.val_mul, unipotent_coe'']
  rw [this]
  refine Continuous.mul ?_ continuous_const
  refine continuous_matrix ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const] <;>
    first | exact continuous_const | exact continuous_id

theorem norm_sub_le_max' (a b : F) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_add_mul_le {a b c d : F} {B : ℝ} (hc : ‖c‖ ≤ 1) (hd : ‖d‖ ≤ 1) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖a * c + b * d‖ ≤ B := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hc).trans ha
  · rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hd).trans hb

theorem norm_diag_le_of_kzero (x : F) (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) {k : G} (hk : k ∈ RCgB.kzero p)
    {B : ℝ} (h0 : ‖((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 0‖ ≤ B)
    (h1 : ‖((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) 0 1‖ ≤ B) :
    ‖(a : F)‖ ≤ B ∧ ‖x * (b : F)‖ ≤ B := by
  have hkinv := RCgB.norm_entry_le_one (inv_mem hk)
  set N : Mat := ((unipotent x * (RCgB.diagU p a b * k) : G) : Mat) with hN
  have hprod : N * ((k⁻¹ : G) : Mat) = ((unipotent x * RCgB.diagU p a b : G) : Mat) := by
    rw [hN, ← Units.val_mul]; congr 1; group
  have hval : ((unipotent x * RCgB.diagU p a b : G) : Mat) = !![(a : F), x * (b : F); 0, (b : F)] := by
    rw [Units.val_mul, unipotent_coe'', RCgB.coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : (a : F) = N 0 0 * ((k⁻¹ : G) : Mat) 0 0 + N 0 1 * ((k⁻¹ : G) : Mat) 1 0 := by
    have := congrFun (congrFun hprod 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hval] at this
    simpa using this.symm
  have e01 : x * (b : F) = N 0 0 * ((k⁻¹ : G) : Mat) 0 1 + N 0 1 * ((k⁻¹ : G) : Mat) 1 1 := by
    have := congrFun (congrFun hprod 0) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, hval] at this
    simpa using this.symm
  exact ⟨e00 ▸ norm_add_mul_le p (hkinv 0 0) (hkinv 1 0) h0 h1, e01 ▸ norm_add_mul_le p (hkinv 0 1) (hkinv 1 1) h0 h1⟩

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ p}

theorem norm_piUnit_zpow (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (n : ℤ) :
    ‖((RCgB.piUnit hπ ^ n : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)‖ = RCgB.qR p ^ (-n) := by
  rw [RCgB.coe_piUnit_zpow, RCgB.norm_uniformizer_zpow hϖ]

theorem shellZ_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) (d n₂ : ℤ) (k : G) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ n₂ * diagZ (algebraMap (O) (F) ϖ) hπ d * k =
      RCgB.diagU p (RCgB.piUnit hπ ^ n₂ * RCgB.piUnit hπ ^ d) (RCgB.piUnit hπ ^ n₂) * k := by
  rw [RCgB.scalarPi_eq_diagU hπ, RCgB.diagU_zpow, RCgB.diagZ_eq_diagU hπ, RCgB.diagU_mul, mul_one]

end BPhi
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLGlue

open NumberField.StandardAddChar

theorem integrable_and_integral_setIntegral_translate'
    {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (Ω : Set G) (hΩm : MeasurableSet Ω) (hΩ : μ Ω < ⊤)
    (F : G → ℂ) (hFm : Measurable F) (hF : Integrable F μ) (m : G → G) (hm : Continuous m) :
    Integrable (fun h : G => ∫ k in Ω, F (m k * h) ∂μ) μ ∧
      ∫ h : G, (∫ k in Ω, F (m k * h) ∂μ) ∂μ = ((μ Ω).toReal : ℂ) * ∫ h : G, F h ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict Ω) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  set f : G × G → ℂ := fun z => F (m z.1 * z.2) with hf
  have hfm : Measurable f := hFm.comp ((hm.comp continuous_fst).mul continuous_snd).measurable
  have hsec : ∀ k, Integrable (fun h => f (k, h)) μ := fun k => by
    simp only [hf]; exact hF.comp_mul_left (m k)
  have hnorm : ∀ k, ∫ h, ‖f (k, h)‖ ∂μ = ∫ h, ‖F h‖ ∂μ := fun k => by
    simp only [hf]; exact integral_mul_left_eq_self (fun h => ‖F h‖) (m k)
  have hint : Integrable f ((μ.restrict Ω).prod μ) := by
    rw [integrable_prod_iff hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hsec, ?_⟩
    simp_rw [hnorm]
    exact integrable_const _
  refine ⟨?_, ?_⟩
  · have h := hint.integral_prod_right
    exact h
  · have hint' : Integrable (Function.uncurry fun (h : G) (k : G) => F (m k * h)) (μ.prod (μ.restrict Ω)) :=
      hint.swap
    rw [integral_integral_swap hint']
    have : ∀ k, ∫ h, F (m k * h) ∂μ = ∫ h, F h ∂μ := fun k => integral_mul_left_eq_self F (m k)
    simp_rw [this]
    rw [setIntegral_const, Complex.real_smul]
    rfl

theorem comp_mul_mem_span {G : Type*} [Group G] (w₀ : G → ℂ)
    {w : G → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₀ (g * h))) (h : G) :
    (fun x => w (x * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w₀ (g * h)) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g; simp [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]; exact Submodule.smul_mem _ a hx

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem exists_isOpen_subgroup_forall_apply_mul_eq
    (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ W : Subgroup G2, IsOpen (W : Set G2) ∧ ∀ k ∈ W, ∀ X : Mat, Φ (((k : G2) : Mat) * X) = Φ X := by
  classical
  obtain ⟨c, hc⟩ := BPhi.exists_constancy_exponent p Φ hΦ hΦc
  obtain ⟨M, hM⟩ := BPhi.exists_support_exponent p Φ hΦc
  have hq0 := RCgB.qR_pos p
  have hM' : ∀ X : Mat, (∃ i j, RCgB.qR p ^ M < ‖X i j‖) → Φ X = 0 := by
    intro X ⟨i, j, hij⟩; by_contra h; exact absurd (hM X h i j) (not_le.2 hij)
  let W : Subgroup G2 :=
    { carrier := {k' | ∀ X : Mat, Φ (((k' : G2) : Mat) * X) = Φ X}
      one_mem' := by intro X; simp
      mul_mem' := by
        intro a b ha hb X
        rw [Units.val_mul, mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha X
        have := ha (((a⁻¹ : G2) : Mat) * X)
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at this
        exact this.symm }
  refine ⟨W, ?_, fun k hk X => hk X⟩
  apply Subgroup.isOpen_of_mem_nhds
  have hr : (0 : ℝ) < RCgB.qR p ^ (-(M + c)) := zpow_pos hq0 _
  set V : Set G2 := {k' | ∀ i j, ‖((((k' : G2) : Mat)) - 1) i j‖ ≤ RCgB.qR p ^ (-(M + c))} with hV
  have hVopen : IsOpen V := by
    have : V = ⋂ i : Fin 2, ⋂ j : Fin 2,
        (fun k' : G2 => (((k' : G2) : Mat) - 1) i j) ⁻¹' Metric.closedBall 0 (RCgB.qR p ^ (-(M + c))) := by
      ext k'; simp [hV, Metric.mem_closedBall, dist_zero_right]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage
      ((Continuous.matrix_elem (Units.continuous_val.sub continuous_const) i j))
  have h1V : (1 : G2) ∈ V := by
    intro i j
    simp only [Units.val_one, sub_self, Matrix.zero_apply, norm_zero]
    exact le_of_lt hr
  refine Filter.mem_of_superset (Filter.inter_mem (hVopen.mem_nhds h1V)
    ((RCgB.isOpen_kzero p).mem_nhds (one_mem _))) ?_
  rintro k' ⟨hk'V, hk'K⟩ X
  show Φ (((k' : G2) : Mat) * X) = Φ X
  by_cases hX : ∀ i j, ‖X i j‖ ≤ RCgB.qR p ^ M
  · have hsplit : ((k' : G2) : Mat) * X = X + (((k' : G2) : Mat) - 1) * X := by
      rw [sub_mul, one_mul, add_sub_cancel]
    rw [hsplit]
    apply hc
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have hb : ∀ l, ‖(((k' : G2) : Mat) - 1) i l * X l j‖ ≤ RCgB.qR p ^ (-c) := by
      intro l
      rw [norm_mul]
      calc ‖(((k' : G2) : Mat) - 1) i l‖ * ‖X l j‖ ≤ RCgB.qR p ^ (-(M + c)) * RCgB.qR p ^ M :=
            mul_le_mul (hk'V i l) (hX l j) (norm_nonneg _) (zpow_nonneg hq0.le _)
        _ = RCgB.qR p ^ (-c) := by rw [← zpow_add₀ hq0.ne']; congr 1; ring
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb 0) (hb 1))
  · push_neg at hX
    obtain ⟨i, j, hij⟩ := hX
    rw [hM' X ⟨i, j, hij⟩]
    by_contra hne
    have hbox := hM _ hne
    have hkinv := RCgB.norm_entry_le_one (inv_mem hk'K)
    have hXeq : X = (((k'⁻¹ : G2)) : Mat) * ((((k' : G2)) : Mat) * X) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have : ‖X i j‖ ≤ RCgB.qR p ^ M := by
      rw [hXeq, Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hkinv i 0)).trans (hbox 0 j)
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (hkinv i 1)).trans (hbox 1 j)
    exact absurd hij (not_lt.2 this)

theorem continuous_det2 : Continuous (fun g : G2 => (Matrix.GeneralLinearGroup.det g : (F)ˣ)) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous (Units.val ∘ fun g : G2 => Matrix.GeneralLinearGroup.det g)
    have : (Units.val ∘ fun g : G2 => Matrix.GeneralLinearGroup.det g) = fun g : G2 => ((g : G2) : Mat).det := by
      funext g; simp [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact (continuous_id.matrix_det).comp Units.continuous_val
  · show Continuous (fun g : G2 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (F)ˣ) : F))
    have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (F)ˣ) : F)) =
        fun g : G2 => (((g⁻¹ : G2) : Mat)).det := by
      funext g; rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact (continuous_id.matrix_det).comp (Units.continuous_val.comp continuous_inv)

theorem exists_compact_open_subgroup_le
    (U W : Subgroup G2) (hU : IsOpen (U : Set G2)) (hW : IsOpen (W : Set G2))
    (χ : (F)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Ω : Subgroup G2, IsOpen (Ω : Set G2) ∧ IsCompact (Ω : Set G2) ∧ Ω ≤ U ∧ Ω ≤ W ∧
      ∀ k ∈ Ω, ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1 ∧
        modulus ((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F) = 1 := by
  set Kχ : Subgroup G2 := (χ.comp (Matrix.GeneralLinearGroup.det : G2 →* (F)ˣ)).ker with hKχ
  have hKχopen : IsOpen (Kχ : Set G2) := by
    have : (Kχ : Set G2) = (fun g : G2 => χ (Matrix.GeneralLinearGroup.det g)) ⁻¹' {1} := by
      ext g; simp [hKχ, MonoidHom.mem_ker]
    rw [this]
    exact (hχ.isOpen_fiber 1).preimage (continuous_det2 p)
  refine ⟨U ⊓ W ⊓ RCgB.kzero p ⊓ Kχ, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Subgroup.coe_inf]
    exact ((hU.inter hW).inter (RCgB.isOpen_kzero p)).inter hKχopen
  · have hopen : IsOpen ((U ⊓ W ⊓ RCgB.kzero p ⊓ Kχ : Subgroup G2) : Set G2) := by
      simp only [Subgroup.coe_inf]
      exact ((hU.inter hW).inter (RCgB.isOpen_kzero p)).inter hKχopen
    refine (RCgB.isCompact_kzero p).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) ?_
    intro k hk
    simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe] at hk
    exact hk.1.2
  · exact le_trans (le_trans inf_le_left inf_le_left) inf_le_left
  · exact le_trans (le_trans inf_le_left inf_le_left) inf_le_right
  · intro k hk
    have hk' : k ∈ RCgB.kzero p ∧ k ∈ Kχ := ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2, (Subgroup.mem_inf.1 hk).2⟩
    refine ⟨?_, ?_⟩
    · have := hk'.2
      rw [hKχ, MonoidHom.mem_ker] at this
      simpa using congrArg Units.val this
    · have h1 : ‖((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F)‖ = 1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]; exact RCgB.norm_det_eq_one hk'.1
      have h2 := RCgB.coe_modulus_eq_norm p ((Matrix.GeneralLinearGroup.det k : (F)ˣ) : F)
      rw [h1] at h2
      exact_mod_cast h2

def mulLeftHomeo (a : G2) : Mat ≃ₜ Mat where
  toFun X := ((a : G2) : Mat) * X
  invFun X := ((a⁻¹ : G2) : Mat) * X
  left_inv X := by simp [← mul_assoc, ← Units.val_mul]
  right_inv X := by simp [← mul_assoc, ← Units.val_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem isLocallyConstant_and_hasCompactSupport_comp_mul
    (Φ : Mat → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (a : G2) :
    IsLocallyConstant (fun X : Mat => Φ (((a : G2) : Mat) * X)) ∧
      HasCompactSupport (fun X : Mat => Φ (((a : G2) : Mat) * X)) :=
  ⟨hΦ.comp_continuous (continuous_const.mul continuous_id), hΦc.comp_homeomorph (mulLeftHomeo p a)⟩

end GJJLGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLGlue

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem isLocallyConstant_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {Y : Type*} (f : H → Y) (U : Subgroup H) (hU : IsOpen (U : Set H)) (hinv : ∀ k ∈ U, ∀ g, f (g * k) = f g) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hS : IsOpen {h : H | g⁻¹ * h ∈ U} := hU.preimage (continuous_const.mul continuous_id)
  have hmem : g ∈ {h : H | g⁻¹ * h ∈ U} := by
    simp only [Set.mem_setOf_eq, inv_mul_cancel]; exact U.one_mem
  filter_upwards [hS.mem_nhds hmem] with h hh
  have := hinv (g⁻¹ * h) hh g
  rw [mul_inv_cancel_left] at this
  exact this

theorem isLocallyConstant_of_mem_span (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : G2 → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G2, w₂base (g * k) = w₂base g)
    {w : G2 → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h))) :
    IsLocallyConstant w := by
  have hb : IsLocallyConstant w₂base :=
    isLocallyConstant_of_rightInvariant w₂base _ (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2 hw₂K
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    exact hb.comp_continuous (continuous_id.mul continuous_const)
  | zero => exact IsLocallyConstant.const 0
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx =>
    show IsLocallyConstant (fun g => a • x g)
    exact IsLocallyConstant.mul (IsLocallyConstant.const a) hx

theorem modulus_mul' (x y : F) : modulus (x * y) = modulus x * modulus y := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_mul]

theorem modulus_pos' {x : F} (hx : x ≠ 0) : 0 < ((modulus x : ℝ≥0) : ℝ) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]; exact norm_pos_iff.2 hx

theorem cpow_ne_zero'' {q : ℂ} (hq : q ≠ 0) (a : ℂ) : q ^ a ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _

theorem continuous_chi_det (χ : (F)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Continuous fun g : G2 => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
  Units.continuous_val.comp (hχ.continuous.comp (continuous_det2 p))

theorem continuous_modulus_det_cpow (s : ℂ) :
    Continuous fun g : G2 => ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ s :=
  (Complex.continuous_ofReal.comp (E3ReduceSupply.continuous_modulus_det p)).cpow continuous_const
    (fun g => Or.inl (by simpa only [Function.comp_apply, Complex.ofReal_re] using E3ReduceSupply.modulus_det_pos p g))

end GJJLGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLGlueAlg

open Polynomial

theorem sum_mul_prod_eval_eq {n : ℕ} (β : Fin n → ℂ) (e : Fin n → ℤ) (m : Fin n → ℤ) (Z : Fin n → ℂ)
    (P Q : Fin n → ℂ[X]) (y : ℂ) (hy : y ≠ 0)
    (h : ∀ i, Z i * (Q i).eval y⁻¹ = y ^ (m i) * (P i).eval y⁻¹) :
    (∑ i, β i * y ^ (e i) * Z i) * (∏ i, Q i).eval y⁻¹ =
      y ^ (∑ i, |e i + m i|) *
        (∑ i, C (β i) * X ^ ((∑ j, |e j + m j|) - (e i + m i)).toNat * P i * ∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹ := by
  classical
  set M : ℤ := ∑ j, |e j + m j| with hM
  have hMi : ∀ i, e i + m i ≤ M := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |e j + m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  rw [Finset.sum_mul, eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hprod : (∏ j, Q j).eval y⁻¹ = (Q i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹ := by
    rw [← eval_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [hprod, eval_mul, eval_mul, eval_mul, eval_C, eval_pow, eval_X]
  have hd : ((M - (e i + m i)).toNat : ℤ) = M - (e i + m i) := Int.toNat_of_nonneg (by linarith [hMi i])
  have key : y ^ M * (y⁻¹) ^ (M - (e i + m i)).toNat = y ^ (e i) * y ^ (m i) := by
    rw [inv_pow, ← zpow_natCast, hd, ← zpow_neg, ← zpow_add₀ hy, ← zpow_add₀ hy]
    congr 1; ring
  calc β i * y ^ (e i) * Z i * ((Q i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹)
      = β i * y ^ (e i) * (Z i * (Q i).eval y⁻¹) * (∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹ := by ring
    _ = β i * y ^ (e i) * (y ^ (m i) * (P i).eval y⁻¹) * (∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹ := by rw [h i]
    _ = β i * (y ^ M * (y⁻¹) ^ (M - (e i + m i)).toNat) * (P i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y⁻¹ := by
        rw [key]; ring
    _ = _ := by ring

theorem prod_ne_zero' {n : ℕ} (Q : Fin n → ℂ[X]) (hQ : ∀ i, Q i ≠ 0) : (∏ i, Q i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => hQ i

theorem fe_sum {n : ℕ} (β : Fin n → ℂ) (v m md : Fin n → ℤ) (P Pd Q Qd : Fin n → ℂ[X]) (E y : ℂ) (hy : y ≠ 0)
    (hfe : ∀ i, (y ^ (md i) * (Pd i).eval y⁻¹) * (Q i).eval y = E * (y ^ (-(m i)) * (P i).eval y) * (Qd i).eval y⁻¹) :
    (y ^ (∑ j, |(-v j) + md j|) *
        (∑ i, C (β i) * X ^ ((∑ j, |(-v j) + md j|) - ((-v i) + md i)).toNat * Pd i * ∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹) *
      (∏ i, Q i).eval y =
    E * (y ^ (-(∑ j, |v j + m j|)) *
        (∑ i, C (β i) * X ^ ((∑ j, |v j + m j|) - (v i + m i)).toNat * P i * ∏ j ∈ Finset.univ.erase i, Q j).eval y) *
      (∏ i, Qd i).eval y⁻¹ := by
  classical
  set M : ℤ := ∑ j, |v j + m j| with hM
  set Md : ℤ := ∑ j, |(-v j) + md j| with hMd
  have hMi : ∀ i, v i + m i ≤ M := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |v j + m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hMdi : ∀ i, (-v i) + md i ≤ Md := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |(-v j) + md j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))

  rw [eval_finset_sum, eval_finset_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hQ : (∏ j, Q j).eval y = (Q i).eval y * (∏ j ∈ Finset.univ.erase i, Q j).eval y := by
    rw [← eval_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hQd : (∏ j, Qd j).eval y⁻¹ = (Qd i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹ := by
    rw [← eval_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [hQ, hQd]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have hd : ((M - (v i + m i)).toNat : ℤ) = M - (v i + m i) := Int.toNat_of_nonneg (by linarith [hMi i])
  have hdd : ((Md - ((-v i) + md i)).toNat : ℤ) = Md - ((-v i) + md i) := Int.toNat_of_nonneg (by linarith [hMdi i])
  have k1 : y ^ Md * (y⁻¹) ^ (Md - ((-v i) + md i)).toNat = y ^ (-(v i)) * y ^ (md i) := by
    rw [inv_pow, ← zpow_natCast, hdd, ← zpow_neg, ← zpow_add₀ hy, ← zpow_add₀ hy]; congr 1; ring
  have k2 : y ^ (-M) * y ^ (M - (v i + m i)).toNat = y ^ (-(v i)) * y ^ (-(m i)) := by
    rw [← zpow_natCast, hd, ← zpow_add₀ hy, ← zpow_add₀ hy]; congr 1; ring
  calc y ^ Md * (β i * (y⁻¹) ^ (Md - ((-v i) + md i)).toNat * (Pd i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹) *
        ((Q i).eval y * (∏ j ∈ Finset.univ.erase i, Q j).eval y)
      = β i * (y ^ Md * (y⁻¹) ^ (Md - ((-v i) + md i)).toNat) *
          (((Pd i).eval y⁻¹) * (Q i).eval y) * (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y := by ring
    _ = β i * y ^ (-(v i)) * ((y ^ (md i) * (Pd i).eval y⁻¹) * (Q i).eval y) *
          (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y := by rw [k1]; ring
    _ = β i * y ^ (-(v i)) * (E * (y ^ (-(m i)) * (P i).eval y) * (Qd i).eval y⁻¹) *
          (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Q j).eval y := by rw [hfe i]
    _ = E * (β i * (y ^ (-(v i)) * y ^ (-(m i))) * (P i).eval y * (∏ j ∈ Finset.univ.erase i, Q j).eval y) *
          ((Qd i).eval y⁻¹ * (∏ j ∈ Finset.univ.erase i, Qd j).eval y⁻¹) := by ring
    _ = _ := by rw [← k2]; ring

end GJJLGlueAlg
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLGlueAlg

theorem natCast_zpow_cpow (N : ℕ) (hN : 0 < N) (k : ℤ) (z : ℂ) :
    (((N : ℂ)) ^ k) ^ z = (N : ℂ) ^ ((k : ℂ) * z) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ((N : ℂ) ^ k) = (((N : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  have hpos : (0 : ℝ) < (N : ℝ) ^ k := zpow_pos hNr k
  rw [h1, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, Real.log_zpow,
    Complex.cpow_def_of_ne_zero hNc, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

end GJJLGlueAlg
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

open Polynomial

namespace J3cKit

theorem cpow_neg_mul_nat (q : ℝ) (a : ℕ) (s : ℂ) :
    ((q : ℂ) ^ (-s)) ^ a = (q : ℂ) ^ (-((a : ℂ) * s)) := by
  rw [← Complex.cpow_nat_mul]; congr 1; ring

theorem forall_cpow_mul_eval_eq_of_halfPlane (q : ℝ) (hq : 1 < q) (A B : ℂ[X]) (m k : ℤ) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re →
      (q : ℂ) ^ ((m : ℂ) * s) * A.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((k : ℂ) * s) * B.eval ((q : ℂ) ^ (-s))) :
    ∀ s : ℂ, (q : ℂ) ^ ((m : ℂ) * s) * A.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((k : ℂ) * s) * B.eval ((q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'

  set c : ℤ := max m k with hc
  set a : ℕ := (c - m).toNat with ha
  set b : ℕ := (c - k).toNat with hb
  have ham : ((a : ℤ)) = c - m := by rw [ha, Int.toNat_of_nonneg (sub_nonneg.2 (le_max_left m k))]
  have hbk : ((b : ℤ)) = c - k := by rw [hb, Int.toNat_of_nonneg (sub_nonneg.2 (le_max_right m k))]

  have hscale : ∀ (n : ℤ) (d : ℕ), ((d : ℤ)) = c - n → ∀ s : ℂ,
      (q : ℂ) ^ ((n : ℂ) * s) = (q : ℂ) ^ ((c : ℂ) * s) * ((q : ℂ) ^ (-s)) ^ d := by
    intro n d hd s
    rw [cpow_neg_mul_nat q, ← Complex.cpow_add _ _ hq0]
    congr 1
    have : (d : ℂ) = (c : ℂ) - (n : ℂ) := by exact_mod_cast hd
    rw [this]; ring
  set A' : ℂ[X] := X ^ a * A with hA'
  set B' : ℂ[X] := X ^ b * B with hB'

  have hAB : A' = B' := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : (fun t : ℝ => ((q : ℂ) ^ (-(t : ℂ)))) '' Set.Ioi σ ⊆ {x | eval x A' = eval x B'} := by
      rintro x ⟨t, ht, rfl⟩
      simp only [Set.mem_setOf_eq, hA', hB', eval_mul, eval_pow, eval_X]
      have hts : σ < ((t : ℂ)).re := by simpa using ht
      have h1 := h (t : ℂ) hts
      rw [hscale m a ham, hscale k b hbk] at h1
      have hc0 : (q : ℂ) ^ ((c : ℂ) * (t : ℂ)) ≠ 0 := fun h0 => hq0 ((Complex.cpow_eq_zero_iff _ _).1 h0).1
      have h2 : (q : ℂ) ^ ((c : ℂ) * (t : ℂ)) * (((q : ℂ) ^ (-(t : ℂ))) ^ a * A.eval ((q : ℂ) ^ (-(t : ℂ)))) =
          (q : ℂ) ^ ((c : ℂ) * (t : ℂ)) * (((q : ℂ) ^ (-(t : ℂ))) ^ b * B.eval ((q : ℂ) ^ (-(t : ℂ)))) := by
        simpa [mul_assoc] using h1
      exact mul_left_cancel₀ hc0 h2
    refine Set.Infinite.mono hsub ((Set.Ioi_infinite σ).image ?_)

    intro t₁ _ t₂ _ heq
    have hpos : (0 : ℝ) < q := zero_lt_one.trans hq
    have key : ∀ t : ℝ, ((q : ℂ) ^ (-(t : ℂ))) = (((q : ℝ) ^ (-t) : ℝ) : ℂ) := by
      intro t
      rw [Complex.ofReal_cpow hpos.le, Complex.ofReal_neg]
    have heq' : (q : ℝ) ^ (-t₁) = (q : ℝ) ^ (-t₂) := by
      have h3 := heq
      simp only [key] at h3
      exact_mod_cast h3
    have h4 : -t₁ = -t₂ := by
      have hlog := congrArg Real.log heq'
      rw [Real.log_rpow hpos, Real.log_rpow hpos] at hlog
      have hlq : Real.log q ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hq.ne'
      exact mul_right_cancel₀ hlq hlog
    linarith
  intro s
  rw [hscale m a ham, hscale k b hbk]
  have h5 := congrArg (fun R : ℂ[X] => R.eval ((q : ℂ) ^ (-s))) hAB
  simp only [hA', hB', eval_mul, eval_pow, eval_X] at h5
  rw [mul_assoc, mul_assoc, h5]

theorem exists_poly_of_finset_sum (q : ℝ) (hq : 1 < q) (S : Finset ℤ) (c : ℤ → ℂ) :
    ∃ (R : ℂ[X]) (M : ℤ), ∀ s : ℂ,
      ∑ n ∈ S, c n * (q : ℂ) ^ (-(n : ℂ) * s) = (q : ℂ) ^ ((M : ℂ) * s) * R.eval ((q : ℂ) ^ (-s)) := by
  classical
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'

  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ n ∈ S, 0 ≤ n + M := by
    refine ⟨∑ n ∈ S, |n|, fun n hn => ?_⟩
    have h1 : |n| ≤ ∑ k ∈ S, |k| := Finset.single_le_sum (f := fun k : ℤ => |k|) (fun k _ => abs_nonneg k) hn
    have h2 : -n ≤ |n| := neg_le_abs n
    linarith
  refine ⟨∑ n ∈ S, Polynomial.C (c n) * X ^ (n + M).toNat, M, fun s => ?_⟩
  rw [Polynomial.eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, cpow_neg_mul_nat q,
    mul_left_comm, ← Complex.cpow_add _ _ hq0]
  congr 2
  have : (((n + M).toNat : ℕ) : ℂ) = (n : ℂ) + (M : ℂ) := by
    have h := Int.toNat_of_nonneg (hM n hn)
    exact_mod_cast h
  rw [this]; ring

end J3cKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLParseval

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

def shuffle : (α × α) × (α × α) ≃ᵐ (α × α) × (α × α) :=
  (MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl α).prodCongr
      ((MeasurableEquiv.prodAssoc.symm.trans (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl α))).trans
        MeasurableEquiv.prodAssoc))).trans
  MeasurableEquiv.prodAssoc.symm

theorem shuffle_apply (x : (α × α) × (α × α)) : shuffle x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) := rfl

theorem measurePreserving_shuffle (μ : Measure α) [SFinite μ] :
    MeasurePreserving (shuffle (α := α)) ((μ.prod μ).prod (μ.prod μ)) ((μ.prod μ).prod (μ.prod μ)) := by
  have h1 := measurePreserving_prodAssoc μ μ (μ.prod μ)
  have h2 : MeasurePreserving (fun x : α × ((α × α) × α) => (x.1, ((x.2.1.2, x.2.1.1), x.2.2)))
      (μ.prod ((μ.prod μ).prod μ)) (μ.prod ((μ.prod μ).prod μ)) :=
    (MeasurePreserving.id μ).prod ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).prod (MeasurePreserving.id μ))
  have h3 := measurePreserving_prodAssoc μ μ μ
  have h3' := h3.symm MeasurableEquiv.prodAssoc
  have h4 : MeasurePreserving (fun x : α × (α × (α × α)) => (x.1, ((x.2.1, x.2.2.1), x.2.2.2)))
      (μ.prod (μ.prod (μ.prod μ))) (μ.prod ((μ.prod μ).prod μ)) := (MeasurePreserving.id μ).prod h3'
  have h5 : MeasurePreserving (fun x : α × ((α × α) × α) => (x.1, (x.2.1.1, (x.2.1.2, x.2.2))))
      (μ.prod ((μ.prod μ).prod μ)) (μ.prod (μ.prod (μ.prod μ))) := (MeasurePreserving.id μ).prod h3
  have h6 := (measurePreserving_prodAssoc μ μ (μ.prod μ)).symm MeasurableEquiv.prodAssoc
  have : (shuffle (α := α) : (α × α) × (α × α) → (α × α) × (α × α)) =
      (MeasurableEquiv.prodAssoc.symm : α × (α × (α × α)) → (α × α) × (α × α)) ∘
        (fun x : α × ((α × α) × α) => (x.1, (x.2.1.1, (x.2.1.2, x.2.2)))) ∘
        (fun x : α × ((α × α) × α) => (x.1, ((x.2.1.2, x.2.1.1), x.2.2))) ∘
        (fun x : α × (α × (α × α)) => (x.1, ((x.2.1, x.2.2.1), x.2.2.2))) ∘
        (MeasurableEquiv.prodAssoc : (α × α) × (α × α) → α × (α × (α × α))) := by
    funext x; rfl
  rw [this]
  exact h6.comp (h5.comp (h2.comp (h4.comp h1)))

def rowEquiv : (Fin 2 → Fin 2 → α) ≃ᵐ (α × α) × (α × α) :=
  (MeasurableEquiv.finTwoArrow (α := Fin 2 → α)).trans
    (MeasurableEquiv.finTwoArrow.prodCongr MeasurableEquiv.finTwoArrow)

theorem rowEquiv_apply (X : Fin 2 → Fin 2 → α) : rowEquiv X = ((X 0 0, X 0 1), (X 1 0, X 1 1)) := rfl

theorem measurePreserving_rowEquiv (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (rowEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  have : (rowEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α)) =
      (fun z : (Fin 2 → α) × (Fin 2 → α) => (MeasurableEquiv.finTwoArrow z.1, MeasurableEquiv.finTwoArrow z.2)) ∘
        (MeasurableEquiv.finTwoArrow : (Fin 2 → Fin 2 → α) → (Fin 2 → α) × (Fin 2 → α)) := by
    funext X; rfl
  rw [this]
  exact ((measurePreserving_finTwoArrow μ).prod (measurePreserving_finTwoArrow μ)).comp
    (measurePreserving_finTwoArrow (Measure.pi fun _ : Fin 2 => μ))

def colEquiv : (Fin 2 → Fin 2 → α) ≃ᵐ (α × α) × (α × α) := rowEquiv.trans shuffle

theorem colEquiv_apply (X : Fin 2 → Fin 2 → α) : colEquiv X = ((X 0 0, X 1 0), (X 0 1, X 1 1)) := rfl

theorem measurePreserving_colEquiv (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (colEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  have : (colEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α)) = shuffle ∘ rowEquiv := rfl
  rw [this]
  exact (measurePreserving_shuffle μ).comp (measurePreserving_rowEquiv μ)

end GJJLParseval
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLParseval

open NumberField.StandardAddChar

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem isLocallyConstant_psiLocal : IsLocallyConstant (fun t : F => (psiLocal ℚ p t : ℂ)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F)) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : F => y - x) ⁻¹' (p.adicCompletionIntegers ℚ : Set F) := by
    simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]; exact zero_mem _
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have h1 : psiLocal ℚ p (y - x) = 1 := by
    apply (E3ReduceSupplyF.level_zero p).1
    rw [WithZero.exp_zero]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
  have : y = (y - x) + x := by ring
  rw [this, AddChar.map_add_eq_mul, h1, one_mul]

theorem continuous_psiLocal : Continuous (fun t : F => (psiLocal ℚ p t : ℂ)) :=
  (isLocallyConstant_psiLocal p).continuous

theorem setCol22_setCol22_colEquiv (X Y : Matrix (Fin 2) (Fin 2) F) :
    setCol22 p (setCol22 p X 0 (Y 0 0, Y 1 0)) 1 (Y 0 1, Y 1 1) = Y := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [setCol22_apply]

end GJJLParseval
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLParseval

open MeasureTheory

section Transpose

variable {α : Type*} [MeasurableSpace α]

def transposeEquiv : (Fin 2 → Fin 2 → α) ≃ᵐ (Fin 2 → Fin 2 → α) := colEquiv.trans rowEquiv.symm

theorem transposeEquiv_apply (X : Fin 2 → Fin 2 → α) : transposeEquiv X = fun i j => X j i := by
  apply rowEquiv.injective
  show rowEquiv (rowEquiv.symm (colEquiv X)) = _
  rw [MeasurableEquiv.apply_symm_apply, colEquiv_apply, rowEquiv_apply]

theorem measurePreserving_transposeEquiv (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (transposeEquiv : (Fin 2 → Fin 2 → α) → (Fin 2 → Fin 2 → α))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ)
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) := by
  have : (transposeEquiv : (Fin 2 → Fin 2 → α) → (Fin 2 → Fin 2 → α)) =
      (rowEquiv.symm : (α × α) × (α × α) → (Fin 2 → Fin 2 → α)) ∘
        (colEquiv : (Fin 2 → Fin 2 → α) → (α × α) × (α × α)) := rfl
  rw [this]
  exact ((measurePreserving_rowEquiv μ).symm rowEquiv).comp (measurePreserving_colEquiv μ)

theorem integral_comp_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [SigmaFinite μ] (f : (Fin 2 → Fin 2 → α) → E) :
    ∫ X, f (fun i j => X j i) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) =
      ∫ X, f X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ) := by
  have h := (measurePreserving_transposeEquiv μ).integral_comp' (f := transposeEquiv) f
  simpa only [transposeEquiv_apply] using h

end Transpose
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem matFourier22_eq_integral
    (φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ)
    (X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) φ X =
      ∫ Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
        φ Y * NumberField.StandardAddChar.psiLocal ℚ p
          (Y 0 1 * X 0 1 + Y 1 1 * X 1 1 + (Y 0 0 * X 0 0 + Y 1 0 * X 1 0))
        ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  have hψc := continuous_psiLocal p
  set μ4 : Measure (Fin 2 → Fin 2 → p.adicCompletion ℚ) :=
    Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p with hμ4
  haveI hσ2 : SigmaFinite (Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := inferInstance
  haveI hσ4 : SigmaFinite μ4 := by rw [hμ4]; infer_instance
  have hcolc : Continuous (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
      (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)) := by
    have : (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
        (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)) =
        fun Y => ((Y 0 0, Y 1 0), (Y 0 1, Y 1 1)) := funext fun Y => colEquiv_apply Y
    rw [this]
    fun_prop
  have hcolset : ∀ (c : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ)),
      (colEquiv : (Fin 2 → Fin 2 → p.adicCompletion ℚ) →
        (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ))
          (setCol22 p (setCol22 p X 0 c.1) 1 c.2) = c := by
    intro c
    rw [colEquiv_apply]
    ext <;> simp [setCol22_apply]
  have hφcont : Continuous φ := hφ.continuous
  set Mx : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ) →
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := fun c => setCol22 p (setCol22 p X 0 c.1) 1 c.2 with hMx
  have hMxc : Continuous Mx := by
    rw [hMx]
    refine continuous_pi fun i => continuous_pi fun k => ?_
    fin_cases i <;> fin_cases k <;> simp [setCol22_apply] <;> fun_prop
  set G : (p.adicCompletion ℚ × p.adicCompletion ℚ) × (p.adicCompletion ℚ × p.adicCompletion ℚ) → ℂ := fun c =>
    φ (Mx c) * (NumberField.StandardAddChar.psiLocal ℚ p (c.2.1 * X 0 1 + c.2.2 * X 1 1) *
      NumberField.StandardAddChar.psiLocal ℚ p (c.1.1 * X 0 0 + c.1.2 * X 1 0)) with hG
  have hGc : Continuous G := by
    rw [hG]
    exact (hφcont.comp hMxc).mul ((hψc.comp (by fun_prop)).mul (hψc.comp (by fun_prop)))
  have hGsupp : HasCompactSupport G := by
    refine HasCompactSupport.intro' ((hφc.isCompact.image hcolc)) ((hφc.isCompact.image hcolc).isClosed) ?_
    intro c hc
    rw [hG]
    simp only
    have : φ (Mx c) = 0 := by
      by_contra hne
      apply hc
      refine ⟨Mx c, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
      rw [hMx]; exact hcolset c
    rw [this, zero_mul]
  have hGint : Integrable G (((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)).prod
      ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) :=
    hGc.integrable_of_hasCompactSupport hGsupp
  rw [matFourier22_eq, colFourier22_apply]
  have hinner : ∀ u : p.adicCompletion ℚ × p.adicCompletion ℚ,
      colFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) 1 φ (setCol22 p X 0 u) *
          NumberField.StandardAddChar.psiLocal ℚ p (u.1 * X 0 0 + u.2 * X 1 0) =
        ∫ u' : p.adicCompletion ℚ × p.adicCompletion ℚ, G (u, u')
          ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
    intro u
    rw [colFourier22_apply, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u' => ?_)
    rw [hG, hMx]
    simp only [setCol22_apply]
    simp
    ring
  simp_rw [hinner]
  rw [← integral_prod _ hGint, ← (measurePreserving_colEquiv (selfDualHaarAt ℚ p)).integral_comp' (f := colEquiv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  rw [hG]
  simp only [colEquiv_apply]
  rw [hMx]
  simp only
  rw [setCol22_setCol22_colEquiv p X Y, ← AddChar.map_add_eq_mul]

theorem integral_comp_transpose_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → E) :
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), f (Matrix.transpose X)
        ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) =
      ∫ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ), f X
        ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  exact integral_comp_transpose (selfDualHaarAt ℚ p) f

theorem matFourier22_comp_transpose (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun Y => Φ (Matrix.transpose Y)) X =
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (Matrix.transpose X) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p

  have hTc : Continuous (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Matrix.transpose Y) :=
    continuous_id.matrix_transpose
  let T : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) ≃ₜ Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
    { toEquiv := ⟨Matrix.transpose, Matrix.transpose, fun Y => Matrix.transpose_transpose Y,
        fun Y => Matrix.transpose_transpose Y⟩
      continuous_toFun := hTc
      continuous_invFun := hTc }
  have hΦT : IsLocallyConstant (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (Matrix.transpose Y)) :=
    hΦ.comp_continuous hTc
  have hΦTc : HasCompactSupport (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (Matrix.transpose Y)) :=
    hΦc.comp_homeomorph T
  rw [matFourier22_eq_integral p _ hΦT hΦTc, matFourier22_eq_integral p _ hΦ hΦc]
  rw [← integral_comp_transpose_eq p (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
    Φ Y * NumberField.StandardAddChar.psiLocal ℚ p
      (Y 0 1 * (Matrix.transpose X) 0 1 + Y 1 1 * (Matrix.transpose X) 1 1 +
        (Y 0 0 * (Matrix.transpose X) 0 0 + Y 1 0 * (Matrix.transpose X) 1 0)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  simp only [Matrix.transpose_apply, Matrix.transpose_transpose]
  congr 1
  congr 1
  ring

end GJJLParseval
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

namespace GJJLParseval

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem isLocallyConstant_and_hasCompactSupport_comp_transpose
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    IsLocallyConstant (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (Matrix.transpose Y)) ∧
      HasCompactSupport (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (Matrix.transpose Y)) := by
  have hTc : Continuous (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Matrix.transpose Y) :=
    continuous_id.matrix_transpose
  let T : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) ≃ₜ Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
    { toEquiv := ⟨Matrix.transpose, Matrix.transpose, fun Y => Matrix.transpose_transpose Y,
        fun Y => Matrix.transpose_transpose Y⟩
      continuous_toFun := hTc
      continuous_invFun := hTc }
  exact ⟨hΦ.comp_continuous hTc, hΦc.comp_homeomorph T⟩

end GJJLParseval
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.TateLocal Topology
open scoped NNReal ENNReal

namespace ALLTWIST
namespace TSE

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

section Kv

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem norm_eq_zpow_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

theorem modulus_of_valued {x : (v.adicCompletion K)} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    modulus x = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ m := by
  rw [← NNReal.coe_inj, coe_modulus_of_valued v hx, NNReal.coe_zpow, NNReal.coe_natCast]

theorem absNorm_pos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  positivity

private theorem _root_.ALLTWIST.TSE.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

p2m_export "ALLTWIST.TSE" "one_lt_absNorm"
theorem two_le_absNorm : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    omega
  exact_mod_cast h2

theorem isClosed_ball (k : ℤ) : IsClosed {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isClosed_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem _root_.ALLTWIST.TSE.isOpen_ball (k : ℤ) : IsOpen {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : (v.adicCompletion K)) ≠ 0 := Units.ne_zero _
  have h := isOpen_setOf_valued_le v _ ht
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

p2m_export "ALLTWIST.TSE" "isOpen_ball"

theorem sphere_eq_diff (k : ℤ) :
    {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k}
      = {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp k} \
          {y : (v.adicCompletion K) | Valued.v y ≤ WithZero.exp (k - 1)} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · intro hy
    refine ⟨hy.le, fun h => ?_⟩
    rw [hy, WithZero.exp_le_exp] at h
    omega
  · rintro ⟨h1, h2⟩
    have hne : Valued.v y ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hne).symm⟩
    rw [hm, WithZero.exp_le_exp] at h1 h2
    rw [hm]
    congr 1
    omega

theorem isClosed_sphere (k : ℤ) : IsClosed {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isClosed_ball v _).sdiff (isOpen_ball v _)

theorem isOpen_sphere (k : ℤ) : IsOpen {u : (v.adicCompletion K) | Valued.v u = WithZero.exp k} := by
  rw [sphere_eq_diff]
  exact (isOpen_ball v _).sdiff (isClosed_ball v _)

theorem coe_integers_eq :
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = {x | Valued.v x ≤ WithZero.exp 0} := by
  ext x
  rw [WithZero.exp_zero]
  exact HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v

theorem isCompact_ball_zero : IsCompact {x : (v.adicCompletion K) | Valued.v x ≤ WithZero.exp 0} := by
  rw [← coe_integers_eq]
  exact isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers K) from inferInstance)

theorem isCompact_units_setF : IsCompact {u : (v.adicCompletion K) | Valued.v u = 1} := by
  refine (isCompact_ball_zero v).of_isClosed_subset ?_ ?_
  · have := isClosed_sphere v 0
    rwa [WithZero.exp_zero] at this
  · intro u hu
    have hu' : Valued.v u = 1 := hu
    show Valued.v u ≤ WithZero.exp 0
    rw [hu', WithZero.exp_zero]

def USet : Set (v.adicCompletion K)ˣ := {u : (v.adicCompletion K)ˣ | Valued.v (u : (v.adicCompletion K)) = 1}

def shell (n : ℤ) : Set (v.adicCompletion K)ˣ :=
  {y : (v.adicCompletion K)ˣ | Valued.v (y : (v.adicCompletion K)) = WithZero.exp (-n)}

theorem shell_zero : shell v 0 = USet v := by
  ext y; simp [shell, USet]

theorem image_val_USet : Units.val '' USet v = {u : (v.adicCompletion K) | Valued.v u = 1} := by
  ext x
  simp only [Set.mem_image, USet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hx]; exact one_ne_zero)
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem isCompact_USet : IsCompact (USet v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_USet]
  exact isCompact_units_setF v

theorem isClosed_shell (n : ℤ) : IsClosed (shell v n) :=
  (isClosed_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_shell (n : ℤ) : IsOpen (shell v n) :=
  (isOpen_sphere v (-n)).preimage Units.continuous_val

theorem isOpen_USet : IsOpen (USet v) := by rw [← shell_zero]; exact isOpen_shell v 0

theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro y hym hyn
  simp only [shell, Set.mem_setOf_eq] at hym hyn
  rw [hym] at hyn
  exact hmn (by have := WithZero.exp_injective hyn; omega)

theorem iUnion_shell : (⋃ n, shell v n) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, shell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  exact ⟨-m, by rw [hm, neg_neg]⟩

theorem exists_valued_eq_exp (y : (v.adicCompletion K)ˣ) :
    ∃ m : ℤ, Valued.v (y : (v.adicCompletion K)) = WithZero.exp m := by
  have hne : Valued.v (y : (v.adicCompletion K)) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  exact ⟨_, (WithZero.exp_log hne).symm⟩

theorem preimage_shell (n : ℤ) :
    (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) ⁻¹' shell v n = USet v := by
  ext u
  simp only [Set.mem_preimage, shell, USet, Set.mem_setOf_eq, Units.val_mul, map_mul,
    valued_uniformizerUnit_zpow]
  constructor
  · intro h
    have hne : (WithZero.exp (-n) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v (u : (v.adicCompletion K))
        = (WithZero.exp (-n))⁻¹ * (WithZero.exp (-n) * Valued.v (u : (v.adicCompletion K))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = 1 := by rw [h, inv_mul_cancel₀ hne]
  · intro h
    rw [h, mul_one]

theorem mul_mem_shell (n : ℤ) {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    uniformizerUnit K v ^ n * u ∈ shell v n := by
  have := preimage_shell v n
  rw [Set.ext_iff] at this
  exact (this u).mpr hu

theorem preimage_mul_left_shell (n : ℤ) {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) :
    (fun y : (v.adicCompletion K)ˣ => u₀ * y) ⁻¹' shell v n = shell v n := by
  ext y
  have hu₀' : Valued.v (u₀ : (v.adicCompletion K)) = 1 := hu₀
  simp only [Set.mem_preimage, shell, Set.mem_setOf_eq, Units.val_mul, map_mul, hu₀', one_mul]

theorem modulus_shell {n : ℤ} {y : (v.adicCompletion K)ˣ} (hy : y ∈ shell v n) :
    modulus (y : (v.adicCompletion K)) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_of_valued v hy

theorem modulus_uniformizer_zpow_mul {n : ℤ} {u : (v.adicCompletion K)ˣ} (hu : u ∈ USet v) :
    modulus ((uniformizerUnit K v ^ n * u : (v.adicCompletion K)ˣ) : (v.adicCompletion K))
      = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-n) :=
  modulus_shell v (n := n) (mul_mem_shell v n hu)

theorem isLocallyConstant_of_forall_mul {X : Type*} (f : (v.adicCompletion K)ˣ → X)
    (W : Set (v.adicCompletion K)ˣ) (hW : IsOpen W) (h1 : (1 : (v.adicCompletion K)ˣ) ∈ W)
    (h : ∀ y, ∀ u ∈ W, f (y * u) = f y) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hopen : IsOpen ((fun u => y * u) '' W) := isOpenMap_mul_left y W hW
  have hmem : y ∈ (fun u => y * u) '' W := ⟨1, h1, mul_one y⟩
  filter_upwards [hopen.mem_nhds hmem] with z hz
  obtain ⟨u, hu, rfl⟩ := hz
  exact h y u hu

theorem isOpen_setOf_valued_sub_one_le (k : ℤ) :
    IsOpen {u : (v.adicCompletion K)ˣ | Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp k} := by
  have hc : Continuous fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K) - 1 :=
    Units.continuous_val.sub continuous_const
  exact (isOpen_ball v k).preimage hc

theorem valued_eq_one_of_valued_sub_one_lt {x : v.adicCompletion K} (hx : Valued.v (x - 1) < 1) :
    Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v hx
  rwa [show (1 : v.adicCompletion K) + (x - 1) = x by ring] at this

theorem valued_sub_one_le_one_of_valued_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) :
    Valued.v (x - 1) ≤ 1 := by
  refine (Valuation.map_sub Valued.v x 1).trans ?_
  rw [hx, Valuation.map_one, max_self]

theorem exists_bound_USet (f : (v.adicCompletion K)ˣ → ℂ) (hf : IsLocallyConstant f) :
    ∃ B : ℝ, ∀ u ∈ USet v, ‖f u‖ ≤ B :=
  (isCompact_USet v).exists_bound_of_continuousOn hf.continuous.continuousOn

theorem continuous_diagOne :
    Continuous (diagOne : (v.adicCompletion K)ˣ → GL (Fin 2) (v.adicCompletion K)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous (fun t : (v.adicCompletion K)ˣ => Matrix.diagonal ![(t : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first | exact continuous_const | exact Units.continuous_val
  · change Continuous (fun t : (v.adicCompletion K)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1])
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;>
      first
        | exact continuous_const
        | exact (Units.continuous_val.inv₀ fun a => a.ne_zero)

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

scoped instance borelSpace_unitsKv : BorelSpace (v.adicCompletion K)ˣ := borelSpace_units

scoped instance measurableMul_unitsKv : MeasurableMul (v.adicCompletion K)ˣ := by infer_instance

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell v n) := (isClosed_shell v n).measurableSet

theorem measurableSet_USet : MeasurableSet (USet v) := by rw [← shell_zero]; exact measurableSet_shell v 0

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

def mulHaar : Measure (v.adicCompletion K)ˣ := Measure.comap Units.val (mulMeasure μ)

scoped instance isHaarMeasure_mulHaar : (mulHaar v μ).IsHaarMeasure :=
  isHaarMeasure_comap_val_mulMeasure K v μ

theorem mulHaar_USet_lt_top : mulHaar v μ (USet v) < ⊤ := (isCompact_USet v).measure_lt_top

theorem setIntegral_shell_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f y ∂(mulHaar v μ)
      = ∫ u in USet v, f (uniformizerUnit K v ^ n * u) ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_shell]

theorem setIntegral_shell_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℤ)
    {u₀ : (v.adicCompletion K)ˣ} (hu₀ : u₀ ∈ USet v) (f : (v.adicCompletion K)ˣ → E) :
    ∫ y in shell v n, f (u₀ * y) ∂(mulHaar v μ) = ∫ y in shell v n, f y ∂(mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun y : (v.adicCompletion K)ˣ => u₀ * y) (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun y : (v.adicCompletion K)ˣ => u₀ * y) :=
    (MeasurableEquiv.mulLeft u₀).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ f (shell v n), preimage_mul_left_shell v n hu₀]

theorem integrableOn_shell_iff {E : Type*} [NormedAddCommGroup E] (n : ℤ) (f : (v.adicCompletion K)ˣ → E) :
    IntegrableOn f (shell v n) (mulHaar v μ) ↔
      IntegrableOn (fun u => f (uniformizerUnit K v ^ n * u)) (USet v) (mulHaar v μ) := by
  have h₁ : MeasurePreserving (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u)
      (mulHaar v μ) (mulHaar v μ) :=
    measurePreserving_mul_left (mulHaar v μ) _
  have h₂ : MeasurableEmbedding (fun u : (v.adicCompletion K)ˣ => uniformizerUnit K v ^ n * u) :=
    (MeasurableEquiv.mulLeft (uniformizerUnit K v ^ n)).measurableEmbedding
  rw [← h₁.integrableOn_comp_preimage h₂ (f := f) (s := shell v n), preimage_shell]
  rfl

theorem integrableOn_USet_of_bound (g : (v.adicCompletion K)ˣ → ℂ) (hg : Measurable g) (R : ℝ)
    (hR : ∀ u ∈ USet v, ‖g u‖ ≤ R) : IntegrableOn g (USet v) (mulHaar v μ) := by
  have hfin : mulHaar v μ (USet v) < ⊤ := mulHaar_USet_lt_top v μ
  haveI : IsFiniteMeasure ((mulHaar v μ).restrict (USet v)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine Integrable.mono' (integrable_const R) hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_USet v)]
  exact Filter.Eventually.of_forall hR

theorem integrable_and_hasSum_shell
    (φ : (v.adicCompletion K)ˣ → ℂ) (hφ : IsLocallyConstant φ)
    (C : ℝ) (M : ℕ)
    (hC : ∀ y : (v.adicCompletion K)ˣ, ‖φ y‖ ≤ C * max 1 ((modulus (y : v.adicCompletion K)) ^ M)⁻¹)
    (c₀ : ℝ) (hc₀ : ∀ y : (v.adicCompletion K)ˣ, c₀ < modulus (y : v.adicCompletion K) → φ y = 0)
    (ν : (v.adicCompletion K)ˣ →* ℂˣ) (hν : IsLocallyConstant fun y : (v.adicCompletion K)ˣ => ((ν y : ℂˣ) : ℂ))
    (B : ℝ) (hB : ∀ u ∈ USet v, ‖((ν u : ℂˣ) : ℂ)‖ ≤ B)
    (k₂ : ℕ) (hk₂ : ‖((ν (uniformizerUnit K v) : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k₂)
    (z : ℂ) (hz : (M : ℝ) + k₂ < z.re) :
    Integrable (fun y : (v.adicCompletion K)ˣ =>
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z) (mulHaar v μ) ∧
    HasSum (fun n : ℤ => ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ))
      (∫ y, φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)) ∧
    (∀ n : ℤ, ∫ y in shell v n,
        φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z ∂(mulHaar v μ)
      = (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) *
          ∫ y in shell v n, φ y * ((ν y : ℂˣ) : ℂ) ∂(mulHaar v μ)) := by

  set ϖ : (v.adicCompletion K)ˣ := uniformizerUnit K v with hϖ
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hN
  set μx : Measure (v.adicCompletion K)ˣ := mulHaar v μ with hμx
  set f : (v.adicCompletion K)ˣ → ℂ := fun y =>
    φ y * ((ν y : ℂˣ) : ℂ) * ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z with hf
  set F : (v.adicCompletion K)ˣ → ℂ := fun y => φ y * ((ν y : ℂˣ) : ℂ) with hF
  have hNpos : 0 < N := absNorm_pos v
  have hN1 : 1 < N := one_lt_absNorm v
  have hNC0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by rw [← hN]; exact hNpos.ne'
    exact_mod_cast h0
  set σ : ℝ := z.re with hσ
  set t : ℝ := ‖((ν ϖ : ℂˣ) : ℂ)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _

  set cst : ℤ → ℂ := fun n => (Ideal.absNorm v.asIdeal : ℂ) ^ (-((n : ℂ) * z)) with hcst
  have hnorm_cst : ∀ n : ℤ, ‖cst n‖ = N ^ (-(n : ℝ) * σ) := by
    intro n
    rw [hcst]
    simp only
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))]
    congr 1
    simp [hσ]

  have hmodC : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n →
      ((modulus (y : v.adicCompletion K) : ℝ) : ℂ) ^ z = cst n := by
    intro n y hy
    have hm := modulus_shell v hy
    rw [hcst]
    simp only
    rw [hm, NNReal.coe_zpow, NNReal.coe_natCast]
    have hr : (0 : ℝ) < N ^ (-n) := zpow_pos hNpos _
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.cpow_def_of_ne_zero hNC0]
    congr 1
    have hlog1 : Complex.log ((N ^ (-n) : ℝ) : ℂ) = ((Real.log (N ^ (-n)) : ℝ) : ℂ) :=
      (Complex.ofReal_log hr.le).symm
    have hlog2 : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = ((Real.log N : ℝ) : ℂ) := by
      rw [show (Ideal.absNorm v.asIdeal : ℂ) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by push_cast; rfl]
      exact (Complex.ofReal_log hNpos.le).symm
    rw [hlog1, hlog2, Real.log_zpow]
    push_cast
    ring
  have hfF : ∀ (n : ℤ) (y : (v.adicCompletion K)ˣ), y ∈ shell v n → f y = cst n * F y := by
    intro n y hy
    simp only [hf, hF]
    rw [hmodC n y hy]
    ring

  have hF_cont : Continuous F := hφ.continuous.mul hν.continuous
  have hFn_meas : ∀ n : ℤ, Measurable fun u : (v.adicCompletion K)ˣ => F (ϖ ^ n * u) := fun n =>
    (hF_cont.comp (continuous_const_mul (ϖ ^ n))).measurable

  have hνn : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ),
      ((ν (ϖ ^ n * u) : ℂˣ) : ℂ) = ((ν ϖ : ℂˣ) : ℂ) ^ n * ((ν u : ℂˣ) : ℂ) := by
    intro n u
    rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val]

  set B' : ℝ := max B 0 with hB'
  set C' : ℝ := max C 0 with hC'
  set R : ℤ → ℝ := fun n => C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) * (t ^ n * B') with hR
  have hR_nonneg : ∀ n, 0 ≤ R n := fun n =>
    mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))
      (mul_nonneg (zpow_nonneg ht0 _) (le_max_right _ _))
  have hmax_le : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v →
      ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹ : NNReal) : ℝ)
        ≤ N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
    intro n u hu
    rw [modulus_uniformizer_zpow_mul v (n := n) hu]
    push_cast
    rw [← hN, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
    refine max_le ?_ ?_
    · exact Real.one_le_rpow hN1.le (by positivity)
    · rw [← Real.rpow_intCast]
      refine Real.rpow_le_rpow_of_exponent_le hN1.le ?_
      push_cast
      have h1 : (n : ℝ) ≤ ((max n 0 : ℤ) : ℝ) := by exact_mod_cast le_max_left n 0
      have h1' : (n : ℝ) ≤ max (n : ℝ) 0 := le_max_left _ _
      have h2 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_le_mul_of_nonneg_left h1' h2]
  have hF_bound : ∀ (n : ℤ) (u : (v.adicCompletion K)ˣ), u ∈ USet v → ‖F (ϖ ^ n * u)‖ ≤ R n := by
    intro n u hu
    simp only [hF, hR]
    rw [norm_mul]
    have h1 : ‖φ (ϖ ^ n * u)‖ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := by
      refine (hC _).trans ?_
      have hm := hmax_le n u hu
      have hmn : (0 : ℝ) ≤ ((max 1 ((modulus ((ϖ ^ n * u : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ^ M)⁻¹
          : NNReal) : ℝ) := NNReal.coe_nonneg _
      calc C * _ ≤ C' * _ := mul_le_mul_of_nonneg_right (le_max_left C 0) hmn
        _ ≤ C' * N ^ ((M : ℝ) * (max n 0 : ℤ)) := mul_le_mul_of_nonneg_left hm (le_max_right _ _)
    have h2 : ‖((ν (ϖ ^ n * u) : ℂˣ) : ℂ)‖ ≤ t ^ n * B' := by
      rw [hνn, norm_mul, norm_zpow, ← ht]
      exact mul_le_mul_of_nonneg_left ((hB u hu).trans (le_max_left _ _)) (zpow_nonneg ht0 _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hNpos.le _))

  have hFn_int : ∀ n : ℤ, IntegrableOn (fun u => F (ϖ ^ n * u)) (USet v) μx := fun n =>
    integrableOn_USet_of_bound v μ _ (hFn_meas n) (R n) (hF_bound n)
  have hF_shell : ∀ n : ℤ, IntegrableOn F (shell v n) μx := by
    intro n
    rw [hμx, integrableOn_shell_iff v μ n F]
    exact hFn_int n
  have hf_shell : ∀ n : ℤ, IntegrableOn f (shell v n) μx := by
    intro n
    refine IntegrableOn.congr_fun (f := fun y => cst n * F y) ?_ ?_ (measurableSet_shell v n)
    · exact (hF_shell n).const_mul (cst n)
    · intro y hy
      exact (hfF n y hy).symm

  set V : ℝ := μx.real (USet v) with hV
  have hV_nonneg : 0 ≤ V := measureReal_nonneg
  have hnorm_shell : ∀ n : ℤ, ∫ y in shell v n, ‖f y‖ ∂μx ≤ N ^ (-(n : ℝ) * σ) * (R n * V) := by
    intro n
    have h1 : ∫ y in shell v n, ‖f y‖ ∂μx = ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx := by
      rw [hμx]
      exact setIntegral_shell_eq v μ n (fun y => ‖f y‖)
    rw [h1]
    have h2 : ∫ u in USet v, ‖f (ϖ ^ n * u)‖ ∂μx ≤ ∫ u in USet v, N ^ (-(n : ℝ) * σ) * R n ∂μx := by
      refine setIntegral_mono_on ?_ ?_ (measurableSet_USet v) ?_
      · exact ((integrableOn_shell_iff v μ n f).mp (hf_shell n)).norm
      · exact integrableOn_const ((mulHaar_USet_lt_top v μ).ne)
      · intro u hu
        rw [hfF n (ϖ ^ n * u) (mul_mem_shell v n hu), norm_mul, hnorm_cst n]
        exact mul_le_mul_of_nonneg_left (hF_bound n u hu) (Real.rpow_nonneg hNpos.le _)
    refine h2.trans ?_
    rw [setIntegral_const, smul_eq_mul, hV]
    nlinarith [hR_nonneg n, hV_nonneg, Real.rpow_nonneg hNpos.le (-(n : ℝ) * σ)]

  set K₀ : ℕ := ⌈c₀⌉₊ with hK₀
  have hfar : ∀ k : ℕ, K₀ ≤ k → ∫ y in shell v (-((k : ℤ) + 1)), ‖f y‖ ∂μx = 0 := by
    intro k hk
    refine (setIntegral_congr_fun (measurableSet_shell v _) fun y hy => ?_).trans (integral_zero _ _)
    have hm : (modulus (y : v.adicCompletion K) : ℝ) = N ^ ((k : ℤ) + 1) := by
      rw [modulus_shell v hy, neg_neg, NNReal.coe_zpow, NNReal.coe_natCast]
    have hbig : c₀ < modulus (y : v.adicCompletion K) := by
      rw [hm, zpow_add_one₀ hNpos.ne', zpow_natCast]
      have hk' : c₀ ≤ (k : ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast hk)
      have hpow : (k : ℝ) + 1 ≤ N ^ k := by
        have h2N : (2 : ℝ) ≤ N := two_le_absNorm v
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ N - 1 by linarith) k
        rw [add_sub_cancel] at this
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [this, mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ N - 1 by linarith) hk0]
      nlinarith [hpow, pow_pos hNpos k]
    show ‖f y‖ = 0
    rw [hf]
    simp only
    rw [hc₀ y hbig, zero_mul, zero_mul, norm_zero]

  have hsumm : Summable fun n : ℤ => ∫ y in shell v n, ‖f y‖ ∂μx := by
    have hnn : ∀ n : ℤ, 0 ≤ ∫ y in shell v n, ‖f y‖ ∂μx := fun n => integral_nonneg fun _ => norm_nonneg _
    refine Summable.of_nat_of_neg_add_one ?_ ?_
    ·
      set r : ℝ := N ^ ((M : ℝ) + k₂ - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hNpos.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by rw [hσ] at hz; linarith)
      refine Summable.of_nonneg_of_le (fun n => hnn n) (fun n => ?_)
        ((summable_geometric_of_lt_one hr0 hr1).mul_left (C' * B' * V))
      refine (hnorm_shell n).trans ?_
      simp only [hR]
      rw [show ((max (n : ℤ) 0 : ℤ) : ℝ) = n by simp, zpow_natCast]

      have htn : t ^ n ≤ N ^ ((k₂ : ℝ) * n) := by
        calc t ^ n ≤ (N ^ k₂) ^ n := pow_le_pow_left₀ ht0 hk₂ n
          _ = N ^ ((k₂ : ℝ) * n) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hrn : r ^ n = N ^ (((M : ℝ) + k₂ - σ) * n) := by
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      have hpos1 : 0 ≤ N ^ (-((n : ℤ) : ℝ) * σ) := Real.rpow_nonneg hNpos.le _
      have hpos2 : 0 ≤ N ^ ((M : ℝ) * n) := Real.rpow_nonneg hNpos.le _
      have hC'0 : 0 ≤ C' := le_max_right _ _
      have hB'0 : 0 ≤ B' := le_max_right _ _
      calc N ^ (-((n : ℤ) : ℝ) * σ) * (C' * N ^ ((M : ℝ) * n) * (t ^ n * B') * V)
          = C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * t ^ n := by ring
        _ ≤ C' * B' * V * (N ^ (-((n : ℤ) : ℝ) * σ) * N ^ ((M : ℝ) * n)) * N ^ ((k₂ : ℝ) * n) := by
            refine mul_le_mul_of_nonneg_left htn ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg hC'0 hB'0) hV_nonneg) (mul_nonneg hpos1 hpos2)
        _ = C' * B' * V * r ^ n := by
            rw [hrn, ← Real.rpow_add hNpos, mul_assoc (C' * B' * V), ← Real.rpow_add hNpos]
            congr 2
            push_cast
            ring
    ·
      refine summable_of_ne_finset_zero (s := Finset.range K₀) fun k hk => ?_
      rw [Finset.mem_range, not_lt] at hk
      exact hfar k hk

  have hint : Integrable f μx := by
    have := integrableOn_iUnion_of_summable_integral_norm hf_shell hsumm
    rwa [iUnion_shell, integrableOn_univ] at this
  refine ⟨hint, ?_, ?_⟩
  ·
    have hsum := hasSum_integral_iUnion (measurableSet_shell v) (pairwise_disjoint_shell v)
      (by rw [iUnion_shell]; exact hint.integrableOn)
    rwa [iUnion_shell, Measure.restrict_univ] at hsum
  ·
    intro n
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (measurableSet_shell v n) fun y hy => hfF n y hy

end Kv
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

section Span

variable {G : Type*} [Group G]

theorem translate_mem_span (W₀ : G → ℂ) {W : G → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))) (h : G) :
    (fun g => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)) := by
  induction hW using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g
    simp only [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ihx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]
    exact Submodule.smul_mem _ a ihx

theorem span_le_span_of_mem (W₀ W₁ : G → ℂ)
    (h : W₀ ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h))) :
    Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h))
      ≤ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₁ (g * h)) :=
  Submodule.span_le.mpr (by rintro _ ⟨h', rfl⟩; exact translate_mem_span W₁ h h')

theorem law_of_mem_span {X : Type*} (W₀ : G → ℂ) (n : X → G) (ψ : X → ℂ)
    (hlaw : ∀ (x : X) (g : G), W₀ (n x * g) = ψ x * W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∀ (x : X) (g : G), W (n x * g) = ψ x * W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    intro x g
    show W₀ (n x * g * h) = ψ x * W₀ (g * h)
    rw [mul_assoc, hlaw]
  | zero => intro x g; simp
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    intro x g
    simp only [Pi.add_apply]
    rw [ih₁, ih₂, mul_add]
  | smul a W' _ ih =>
    intro x g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ih]
    ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem smooth_of_mem_span (W₀ : G → ℂ) (K₀ : Subgroup G) (hK₀ : IsOpen (K₀ : Set G))
    (hfix : ∀ k ∈ K₀, ∀ g : G, W₀ (g * k) = W₀ g) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)),
      ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g := by
  intro W hW
  induction hW using Submodule.span_induction with
  | mem W' hW' =>
    obtain ⟨h, rfl⟩ := hW'
    refine ⟨K₀.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hK₀.preimage ?_
      show Continuous fun k : G => (MulAut.conj h⁻¹) k
      simp only [MulAut.conj_apply, inv_inv]
      fun_prop
    · intro k hk g
      rw [Subgroup.mem_comap] at hk
      have hk' : h⁻¹ * k * h ∈ K₀ := by
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hk
      show W₀ (g * k * h) = W₀ (g * h)
      calc W₀ (g * k * h) = W₀ (g * h * (h⁻¹ * k * h)) := by group
        _ = W₀ (g * h) := hfix _ hk' _
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ ih₁ ih₂ =>
    obtain ⟨U₁, hU₁, h₁⟩ := ih₁
    obtain ⟨U₂, hU₂, h₂⟩ := ih₂
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => ?_⟩
    simp only [Pi.add_apply]
    rw [h₁ k hk.1 g, h₂ k hk.2 g]
  | smul a W' _ ih =>
    obtain ⟨U, hU, h⟩ := ih
    refine ⟨U, hU, fun k hk g => ?_⟩
    simp only [Pi.smul_apply]
    rw [h k hk g]

end Span
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB"

private theorem _root_.ALLTWIST.TSE.isAddHaarMeasure_selfDualHaarAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    letI := localBorel K v
    (selfDualHaarAt K v).IsAddHaarMeasure := by
  letI := localBorel K v
  haveI : BorelSpace (v.adicCompletion K) := borelSpace_localBorel K v
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))).ne'
  have hdef : selfDualHaarAt K v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

p2m_export "ALLTWIST.TSE" "isAddHaarMeasure_selfDualHaarAt"
end ALLTWIST.TSE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE"

noncomputable section

namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

def dshell (n : ℤ) : Set G2 :=
  {g | Valued.v (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) = WithZero.exp (-n)}

theorem mem_dshell {n : ℤ} {g : G2} :
    g ∈ dshell p n ↔ Valued.v (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) = WithZero.exp (-n) := Iff.rfl

theorem pairwise_disjoint_dshell : Pairwise (Function.onFun Disjoint (dshell p)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro g hm hn
  rw [mem_dshell] at hm hn
  rw [hm] at hn
  exact hmn (by have := WithZero.exp_injective hn; omega)

theorem iUnion_dshell : (⋃ n, dshell p n) = Set.univ := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hne : Valued.v (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log hne).symm⟩
  exact ⟨-m, by rw [mem_dshell, hm, neg_neg]⟩

theorem continuous_det_coe : Continuous fun g : G2 => (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) := by
  have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp))) =
      fun g : G2 => ((g : M2)).det := by
    funext g; rfl
  rw [this]
  exact (continuous_id.matrix_det).comp Units.continuous_val

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

scoped instance : BorelSpace G2 := borelSpace_localGLBorel ℚ p
scoped instance : BorelSpace Qp := borelSpace_localBorel ℚ p

theorem measurableSet_dshell (n : ℤ) : MeasurableSet (dshell p n) := by
  have : dshell p n = (fun g : G2 => (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp))) ⁻¹'
      {u : Qp | Valued.v u = WithZero.exp (-n)} := rfl
  rw [this]
  exact ((ALLTWIST.TSE.isClosed_sphere p (-n)).preimage (continuous_det_coe p)).measurableSet

theorem modulus_det_of_mem_dshell {n : ℤ} {g : G2} (hg : g ∈ dshell p n) :
    ((modulus (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) : ℝ) : ℂ) =
      (((Ideal.absNorm p.asIdeal : ℝ) ^ (-n) : ℝ) : ℂ) := by
  congr 1
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p, coe_nnnorm]
  rw [mem_dshell] at hg
  rw [NumberField.FinitePlace.norm_def, hg,
    show (WithZero.exp (-n)) = ((Multiplicative.ofAdd (-n) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem cpow_absNorm_zpow (m : ℤ) (e : ℂ) :
    (((Ideal.absNorm p.asIdeal : ℝ) ^ m : ℝ) : ℂ) ^ e = (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * e) := by
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    have : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
    positivity
  have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ m := zpow_pos hN m
  have h1 : ((((Ideal.absNorm p.asIdeal : ℝ)) ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h2 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2]
  congr 1
  rw [← Complex.ofReal_log hpos.le, Real.log_zpow,
    show ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) : ℂ) from
      (Complex.ofReal_natCast _).symm,
    ← Complex.ofReal_log hN.le]
  push_cast
  ring

theorem integral_eq_sum_dshell (μ₂ : Measure G2) (F h : G2 → ℂ) (hF : Integrable F μ₂) (a : ℤ → ℂ)
    (hFh : ∀ n, ∀ g ∈ dshell p n, F g = a n * h g)
    (S : Finset ℤ) (hS : ∀ n, n ∉ S → (∫ g in dshell p n, h g ∂μ₂) = 0) :
    (∫ g, F g ∂μ₂) = ∑ n ∈ S, (∫ g in dshell p n, h g ∂μ₂) * a n := by
  have hsum : HasSum (fun n : ℤ => ∫ g in dshell p n, F g ∂μ₂) (∫ g, F g ∂μ₂) := by
    have h := hasSum_integral_iUnion (μ := μ₂) (f := F) (fun n => measurableSet_dshell p n)
      (pairwise_disjoint_dshell p) (by rw [iUnion_dshell]; exact hF.integrableOn)
    rwa [iUnion_dshell, Measure.restrict_univ] at h
  have hterm : ∀ n : ℤ, (∫ g in dshell p n, F g ∂μ₂) = (∫ g in dshell p n, h g ∂μ₂) * a n := by
    intro n
    rw [setIntegral_congr_fun (measurableSet_dshell p n) (hFh n), integral_const_mul, mul_comm]
  have hzero : ∀ n ∉ S, (∫ g in dshell p n, F g ∂μ₂) = 0 := by
    intro n hn; rw [hterm n, hS n hn, zero_mul]
  have hfin : HasSum (fun n : ℤ => ∫ g in dshell p n, F g ∂μ₂) (∑ n ∈ S, ∫ g in dshell p n, F g ∂μ₂) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [hsum.unique hfin]
  exact Finset.sum_congr rfl fun n _ => hterm n

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

private theorem _root_.ShellFin.one_lt_absNorm : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := ALLTWIST.TSE.one_lt_absNorm p

p2m_export "ShellFin" "one_lt_absNorm"

theorem norm_det_of_mem_dshell {n : ℤ} {g : G2} (hg : g ∈ dshell p n) :
    ‖((g : M2)).det‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) := by
  have : ((g : M2)).det = (((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)) := rfl
  rw [this]
  exact ALLTWIST.TSE.norm_eq_zpow_of_valued p hg

theorem exists_forall_lt_apply_eq_zero (Ψ : M2 → ℂ) (hΨcs : HasCompactSupport Ψ) :
    ∃ n₁ : ℤ, ∀ n < n₁, ∀ g ∈ dshell p n, Ψ (g : M2) = 0 := by
  obtain ⟨R, hR⟩ := hΨcs.isCompact.exists_bound_of_continuousOn (f := fun X : M2 => X.det)
    (continuous_id.matrix_det).continuousOn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R (one_lt_absNorm p)
  refine ⟨-(k : ℤ), fun n hn g hg => ?_⟩
  by_contra hne
  have hmem : (g : M2) ∈ tsupport Ψ := subset_tsupport _ hne
  have h1 := hR _ hmem
  rw [norm_det_of_mem_dshell p hg] at h1
  have h2 : (Ideal.absNorm p.asIdeal : ℝ) ^ (k : ℕ) ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ (one_lt_absNorm p).le (by omega)
  linarith

theorem setIntegral_dshell_eq_zero_of_sum_translate_eq_zero (μ₂ : Measure G2) [μ₂.IsMulRightInvariant]
    (c : G2 → ℂ) (ξ : (Qp)ˣ →* ℂˣ) (n : ℤ)
    (X : Finset G2) (hXne : X.Nonempty) (hXdet : ∀ u ∈ X, Matrix.GeneralLinearGroup.det u = 1)
    (hcanc : ∀ g : G2, ∑ u ∈ X, c (g * u) = 0)
    (hint : Integrable (fun g => (dshell p n).indicator (fun g => c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) g) μ₂) :
    (∫ g in dshell p n, c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0 := by
  set f : G2 → ℂ := (dshell p n).indicator (fun g => c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) with hf
  have hI : (∫ g in dshell p n, c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = ∫ g, f g ∂μ₂ :=
    (integral_indicator (measurableSet_dshell p n)).symm
  rw [hI]

  have htr : ∀ u ∈ X, (∫ g, f (g * u) ∂μ₂) = ∫ g, f g ∂μ₂ := fun u _ => integral_mul_right_eq_self f u
  have hfu : ∀ u ∈ X, ∀ g : G2, f (g * u) =
      (dshell p n).indicator (fun g => c (g * u) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) g := by
    intro u hu g
    have hdet : Matrix.GeneralLinearGroup.det (g * u) = Matrix.GeneralLinearGroup.det g := by
      rw [map_mul, hXdet u hu, mul_one]
    have hmem : (g * u ∈ dshell p n) ↔ (g ∈ dshell p n) := by rw [mem_dshell, mem_dshell, hdet]
    simp only [hf]
    by_cases hg : g ∈ dshell p n
    · rw [Set.indicator_of_mem (hmem.2 hg), Set.indicator_of_mem hg, hdet]
    · rw [Set.indicator_of_notMem (fun h => hg (hmem.1 h)), Set.indicator_of_notMem hg]
  have hcard : (X.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hXne).ne'
  have hsum : (X.card : ℂ) * ∫ g, f g ∂μ₂ = ∑ u ∈ X, ∫ g, f (g * u) ∂μ₂ := by
    rw [Finset.sum_congr rfl htr, Finset.sum_const, nsmul_eq_mul]
  have hint' : ∀ u ∈ X, Integrable (fun g => f (g * u)) μ₂ := fun u _ => hint.comp_mul_right u
  rw [← integral_finsetSum X hint'] at hsum
  have hzero : (fun g => ∑ u ∈ X, f (g * u)) = fun _ => 0 := by
    funext g
    rw [Finset.sum_congr rfl (fun u hu => hfu u hu g)]
    by_cases hg : g ∈ dshell p n
    · simp only [Set.indicator_of_mem hg, ← Finset.sum_mul, hcanc g, zero_mul]
    · simp only [Set.indicator_of_notMem hg, Finset.sum_const_zero]
  rw [hzero, integral_zero] at hsum
  exact (mul_eq_zero.1 hsum).resolve_left hcard

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem coe_scalar_mul_apply (z : (Qp)ˣ) (g : G2) (i j : Fin 2) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2)) i j = (z : Qp) * (g : M2) i j := by
  have e4 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M2) = Matrix.diagonal fun _ => (z : Qp) := rfl
  rw [Units.val_mul, e4, Matrix.diagonal_mul]

theorem det_scalar_mul (z : (Qp)ˣ) (g : G2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2).det = (z : Qp) ^ 2 * (g : M2).det := by
  have e4 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M2) = Matrix.diagonal fun _ => (z : Qp) := rfl
  rw [Units.val_mul, Matrix.det_mul, e4, Matrix.det_diagonal, Fin.prod_const]

theorem exists_forall_le_apply_eq_apply_zero (Ψ : M2 → ℂ) (hΨlc : IsLocallyConstant Ψ)
    (c : G2 → ℂ) (C : Set G2) (hC : IsCompact C)
    (hcZ : ∀ g : G2, c g ≠ 0 → ∃ z : (Qp)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C) :
    ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → ∀ g ∈ dshell p n, c g ≠ 0 → Ψ (g : M2) = Ψ 0 := by
  letI : NormedAddCommGroup M2 := Matrix.normedAddCommGroup

  have hU : IsOpen {X : M2 | Ψ X = Ψ 0} := hΨlc.isOpen_fiber (Ψ 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 rfl

  by_cases hCne : C.Nonempty
  swap
  · refine ⟨0, fun n _ g _ hcg => ?_⟩
    obtain ⟨z, hz⟩ := hcZ g hcg
    exact absurd ⟨_, hz⟩ hCne
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn (f := fun k : G2 => ((k : M2) : M2))
    Units.continuous_val.continuousOn
  have hdetcont : Continuous fun k : G2 => ‖((k : M2)).det‖ := (continuous_id.matrix_det.comp Units.continuous_val).norm
  obtain ⟨k₀, hk₀C, hk₀⟩ := hC.exists_isMinOn hCne hdetcont.continuousOn
  set r : ℝ := ‖((k₀ : G2) : M2).det‖ with hr
  have hrpos : 0 < r := by
    rw [hr, norm_pos_iff]
    exact (Matrix.GeneralLinearGroup.det k₀).ne_zero
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR k₀ hk₀C)

  have hN1 := one_lt_absNorm p
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R ^ 2 / (r * ε ^ 2)) hN1
  refine ⟨k, fun n hn g hg hcg => ?_⟩
  obtain ⟨z, hz⟩ := hcZ g hcg
  apply hball
  rw [Metric.mem_ball, dist_zero_right, Matrix.norm_lt_iff hε]
  intro i j

  have hzne : (z : Qp) ≠ 0 := z.ne_zero
  have hz0 : 0 < ‖(z : Qp)‖ := norm_pos_iff.2 hzne
  have hentry : (g : M2) i j = (z : Qp)⁻¹ * (((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2)) i j := by
    rw [coe_scalar_mul_apply, ← mul_assoc, inv_mul_cancel₀ hzne, one_mul]
  have hkR : ‖(((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2)) i j‖ ≤ R :=
    (Matrix.norm_entry_le_entrywise_sup_norm _).trans (hR _ hz)
  have hdet : ‖(z : Qp)‖ ^ 2 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) ≥ r := by
    have h1 := hk₀ hz
    simp only [Set.mem_setOf_eq] at h1
    rw [det_scalar_mul, norm_mul, norm_pow, norm_det_of_mem_dshell p hg] at h1
    rw [hr]; exact h1

  have hNn : (Ideal.absNorm p.asIdeal : ℝ) ^ (-n) ≤ ((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hN1.le (by omega)
  have hNkpos : 0 < (Ideal.absNorm p.asIdeal : ℝ) ^ k := pow_pos (by linarith) k

  have hz2 : r * (Ideal.absNorm p.asIdeal : ℝ) ^ k ≤ ‖(z : Qp)‖ ^ 2 := by
    have : r ≤ ‖(z : Qp)‖ ^ 2 * ((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹ :=
      hdet.le.trans (mul_le_mul_of_nonneg_left hNn (sq_nonneg _))
    rwa [← div_eq_mul_inv, le_div_iff₀ hNkpos] at this

  rw [hentry, norm_mul, norm_inv]
  have hgoal : (‖(z : Qp)‖⁻¹ * ‖(((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2)) i j‖) ^ 2 < ε ^ 2 := by
    rw [mul_pow, inv_pow]
    calc (‖(z : Qp)‖ ^ 2)⁻¹ * ‖(((Matrix.GeneralLinearGroup.scalar (Fin 2) z * g : G2) : M2)) i j‖ ^ 2
        ≤ (r * (Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹ * R ^ 2 := by
          apply mul_le_mul
          · exact inv_anti₀ (mul_pos hrpos hNkpos) hz2
          · exact pow_le_pow_left₀ (norm_nonneg _) hkR 2
          · positivity
          · positivity
      _ < ε ^ 2 := by
          rw [inv_mul_eq_div, div_lt_iff₀ (mul_pos hrpos hNkpos)]
          have := hk
          rw [div_lt_iff₀ (mul_pos hrpos (pow_pos hε 2))] at this
          nlinarith
  exact (pow_lt_pow_iff_left₀ (by positivity) hε.le two_ne_zero).1 hgoal

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem setIntegral_dshell_eq_zero_of_integral_translate_eq_zero [MeasurableMul₂ G2]
    (μ₂ : Measure G2) [SFinite μ₂] [μ₂.IsMulRightInvariant]
    (ν' : Measure G2) [IsFiniteMeasure ν'] (hν'ne : ν' Set.univ ≠ 0)
    (hν'det : ν' {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} = 0)
    (c : G2 → ℂ) (ξ : (Qp)ˣ →* ℂˣ) (n : ℤ)
    (hcanc : ∀ g : G2, (∫ u, c (g * u) ∂ν') = 0)
    (hint : Integrable (fun g => (dshell p n).indicator (fun g => c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) g) μ₂) :
    (∫ g in dshell p n, c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0 := by
  set f : G2 → ℂ := (dshell p n).indicator (fun g => c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) with hf
  have hI : (∫ g in dshell p n, c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = ∫ g, f g ∂μ₂ :=
    (integral_indicator (measurableSet_dshell p n)).symm
  rw [hI]

  have hT : MeasurePreserving (fun z : G2 × G2 => (z.1 * z.2, z.2)) (μ₂.prod ν') (μ₂.prod ν') :=
    measurePreserving_mul_prod μ₂ ν'
  have hfst : Integrable (fun z : G2 × G2 => f z.1) (μ₂.prod ν') := hint.comp_fst ν'
  have hF : Integrable (fun z : G2 × G2 => f (z.1 * z.2)) (μ₂.prod ν') := by
    have := (hT.integrable_comp hfst.aestronglyMeasurable).2 hfst
    exact this

  have h1 : (∫ z : G2 × G2, f (z.1 * z.2) ∂(μ₂.prod ν')) = ∫ u, (∫ g, f g ∂μ₂) ∂ν' := by
    rw [← integral_prod_swap]
    rw [integral_prod (fun z : G2 × G2 => f (z.swap.1 * z.swap.2)) hF.swap]
    simp only [Prod.swap_prod_mk]
    congr 1; funext u
    exact integral_mul_right_eq_self f u
  have h2 : (∫ z : G2 × G2, f (z.1 * z.2) ∂(μ₂.prod ν')) = ∫ g, (∫ u, f (g * u) ∂ν') ∂μ₂ := integral_prod _ hF

  have hinner : ∀ g : G2, (∫ u, f (g * u) ∂ν') = 0 := by
    intro g
    have hae : (fun u => f (g * u)) =ᵐ[ν']
        fun u => (dshell p n).indicator (fun g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) g * c (g * u) := by
      have : ∀ᵐ u ∂ν', Matrix.GeneralLinearGroup.det u = 1 := by
        rw [ae_iff]; simpa using hν'det
      filter_upwards [this] with u hu
      have hdet : Matrix.GeneralLinearGroup.det (g * u) = Matrix.GeneralLinearGroup.det g := by
        rw [map_mul, hu, mul_one]
      have hmem : (g * u ∈ dshell p n) ↔ (g ∈ dshell p n) := by rw [mem_dshell, mem_dshell, hdet]
      simp only [hf]
      by_cases hg : g ∈ dshell p n
      · rw [Set.indicator_of_mem (hmem.2 hg), Set.indicator_of_mem hg, hdet, mul_comm]
      · rw [Set.indicator_of_notMem (fun h => hg (hmem.1 h)), Set.indicator_of_notMem hg, zero_mul]
    rw [integral_congr_ae hae, integral_const_mul, hcanc g, mul_zero]
  rw [h1] at h2
  simp only [hinner, integral_zero, integral_const, smul_eq_mul] at h2

  have hν : (ν'.real Set.univ : ℝ) ≠ 0 := by
    rw [measureReal_def]; exact (ENNReal.toReal_pos hν'ne (measure_ne_top ν' _)).ne'
  have h3 : ((ν'.real Set.univ : ℝ) : ℂ) * ∫ g, f g ∂μ₂ = 0 := by
    simpa [Complex.real_smul] using h2
  exact (mul_eq_zero.1 h3).resolve_left (by exact_mod_cast hν)

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem unipotent_coe (x : Qp) : ((unipotent x : G2) : M2) = !![1, x; 0, 1] := rfl

theorem unipotent_add (x y : Qp) : (unipotent x : G2) * unipotent y = unipotent (x + y) := by
  apply Units.ext
  simp only [Units.val_mul, unipotent_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem det_unipotent (x : Qp) : Matrix.GeneralLinearGroup.det (unipotent x : G2) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotent_coe, Matrix.det_fin_two_of]
  simp

theorem continuous_unipotent : Continuous fun x : Qp => (unipotent x : G2) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun x : Qp => ((unipotent x : G2) : M2)
    simp only [unipotent_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ x : Qp, ((unipotent x : G2)⁻¹ : G2) = unipotent (-x) := by
      intro x
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, unipotent_add, neg_add_cancel]
      apply Units.ext; simp only [unipotent_coe, Units.val_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    change Continuous fun x : Qp => (((unipotent x : G2)⁻¹ : G2) : M2)
    simp only [this, unipotent_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

def ball (k : ℤ) : Set Qp := {x : Qp | Valued.v x ≤ WithZero.exp k}

theorem add_mem_ball {k : ℤ} {x t : Qp} (hx : x ∈ ball p k) (ht : t ∈ ball p k) : x + t ∈ ball p k :=
  (Valuation.map_add_le_max' Valued.v x t).trans (max_le hx ht)

theorem preimage_add_ball {k : ℤ} {t : Qp} (ht : t ∈ ball p k) :
    (fun x : Qp => x + t) ⁻¹' ball p k = ball p k := by
  ext x
  simp only [Set.mem_preimage]
  constructor
  · intro h
    have : x = (x + t) + (-t) := by ring
    rw [this]
    refine add_mem_ball p h ?_
    show Valued.v (-t) ≤ _
    rw [Valuation.map_neg]; exact ht
  · intro h; exact add_mem_ball p h ht

private theorem _root_.ShellFin.isOpen_ball (k : ℤ) : IsOpen (ball p k) := ALLTWIST.TSE.isOpen_ball p k
p2m_export "ShellFin" "isOpen_ball"
private theorem _root_.ShellFin.isClosed_ball (k : ℤ) : IsClosed (ball p k) := ALLTWIST.TSE.isClosed_ball p k
p2m_export "ShellFin" "isClosed_ball"
theorem measurableSet_ball (k : ℤ) : MeasurableSet (ball p k) := (isClosed_ball p k).measurableSet

theorem isCompact_ball (k : ℤ) : IsCompact (ball p k) := by

  set t : Qp := ((NumberField.AdelicLevel.uniformizerUnit ℚ p ^ (-k) : (Qp)ˣ) : Qp) with ht
  have hvt : Valued.v t = WithZero.exp k := by
    rw [ht, ALLTWIST.TSE.valued_uniformizerUnit_zpow, neg_neg]
  have ht0 : t ≠ 0 := by rw [ht]; exact Units.ne_zero _
  have : ball p k = (fun x : Qp => t * x) '' {x : Qp | Valued.v x ≤ WithZero.exp 0} := by
    ext y
    simp only [ball, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hy
      refine ⟨t⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel₀ ht0, one_mul]⟩
      rw [map_mul, map_inv₀, hvt, WithZero.exp_zero]
      calc (WithZero.exp k)⁻¹ * Valued.v y ≤ (WithZero.exp k)⁻¹ * WithZero.exp k :=
            mul_le_mul_right hy _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨x, hx, rfl⟩
      rw [WithZero.exp_zero] at hx
      rw [map_mul, hvt]
      calc WithZero.exp k * Valued.v x ≤ WithZero.exp k * 1 := mul_le_mul_right hx _
        _ = WithZero.exp k := mul_one _
  rw [this]
  exact (ALLTWIST.TSE.isCompact_ball_zero p).image (continuous_const.mul continuous_id)

theorem setIntegral_ball_comp_add (μ : Measure Qp) [μ.IsAddRightInvariant] {k : ℤ} {t : Qp} (ht : t ∈ ball p k)
    (F : Qp → ℂ) :
    ∫ x in ball p k, F (x + t) ∂μ = ∫ x in ball p k, F x ∂μ := by
  have h₁ : MeasurePreserving (fun x : Qp => x + t) μ μ := measurePreserving_add_right μ t
  have h₂ : MeasurableEmbedding (fun x : Qp => x + t) := (MeasurableEquiv.addRight t).measurableEmbedding
  rw [← h₁.setIntegral_preimage_emb h₂ F (ball p k), preimage_add_ball p ht]

theorem isLocallyConstant_coeff_unipotent (μ₂ : Measure G2) (Ω : Set G2) (W : G2 → ℂ)
    (U : Subgroup G2) (hU : IsOpen (U : Set G2)) (hW : ∀ k ∈ U, ∀ g : G2, W (g * k) = W g) (g : G2) :
    IsLocallyConstant fun x : Qp => ∫ k in Ω, W (k * (g * unipotent x)) ∂μ₂ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpre : IsOpen ((fun y : Qp => (unipotent y : G2)) ⁻¹' (U : Set G2)) := hU.preimage (continuous_unipotent p)
  have h0 : (0 : Qp) ∈ (fun y : Qp => (unipotent y : G2)) ⁻¹' (U : Set G2) := by
    show (unipotent (0 : Qp) : G2) ∈ (U : Set G2)
    have : (unipotent (0 : Qp) : G2) = 1 := by
      apply Units.ext; simp only [unipotent_coe, Units.val_one]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this]; exact U.one_mem
  have hnhds : {y : Qp | (unipotent (y - x) : G2) ∈ (U : Set G2)} ∈ nhds x := by
    have hc : Continuous fun y : Qp => y - x := continuous_id.sub continuous_const
    have : {y : Qp | (unipotent (y - x) : G2) ∈ (U : Set G2)} = (fun y => y - x) ⁻¹' ((fun y : Qp => (unipotent y : G2)) ⁻¹' (U : Set G2)) := rfl
    rw [this]
    exact (hpre.preimage hc).mem_nhds (by simp [h0, show (unipotent (x - x) : G2) ∈ (U : Set G2) from by rw [sub_self]; exact h0])
  filter_upwards [hnhds] with y hy
  congr 1; funext k
  have : g * unipotent y = g * unipotent x * unipotent (y - x) := by
    rw [mul_assoc, unipotent_add, add_sub_cancel]
  rw [this, ← mul_assoc k, ← mul_assoc, hW _ hy]

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem exists_finset_integral_eq_sum_dshell' [MeasurableMul₂ G2] (μ₂ : Measure G2) [SFinite μ₂] [μ₂.IsMulRightInvariant]
    (Ψ : M2 → ℂ) (hΨlc : IsLocallyConstant Ψ) (hΨcs : HasCompactSupport Ψ)
    (c : G2 → ℂ) (C : Set G2) (hC : IsCompact C)
    (hcZ : ∀ g : G2, c g ≠ 0 → ∃ z : (Qp)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C)
    (ν' : Measure G2) [IsFiniteMeasure ν'] (hν'ne : ν' Set.univ ≠ 0)
    (hν'det : ν' {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} = 0)
    (hcanc : ∀ g : G2, (∫ u, c (g * u) ∂ν') = 0)
    (ξ : (Qp)ˣ →* ℂˣ) (z₀ : ℂ)
    (hint₀ : Integrable (fun g : G2 => c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ z₀) μ₂) :
    ∃ S : Finset ℤ,
      (∀ n, n ∉ S → (∫ g in dshell p n, c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0) ∧
      ∀ z : ℂ, Integrable (fun g : G2 => c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ z) μ₂ →
        (∫ g, c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ z ∂μ₂) =
          ∑ n ∈ S, (∫ g in dshell p n, c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z) := by
  have hN0 : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by
    have := one_lt_absNorm p
    exact_mod_cast (show (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 by linarith)

  have hmod : ∀ (n : ℤ) (z : ℂ), ∀ g ∈ dshell p n,
      ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ z =
        (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z) := by
    intro n z g hg
    rw [modulus_det_of_mem_dshell p hg, cpow_absNorm_zpow]
    congr 1
    push_cast
    ring
  obtain ⟨n₁, hn₁⟩ := exists_forall_lt_apply_eq_zero p Ψ hΨcs
  obtain ⟨n₂, hn₂⟩ := exists_forall_le_apply_eq_apply_zero p Ψ hΨlc c C hC hcZ

  have hdeep : ∀ n, n₂ ≤ n → ∀ g ∈ dshell p n, c g * Ψ (g : M2) = c g * Ψ 0 := by
    intro n hn g hg
    by_cases hcg : c g = 0
    · rw [hcg, zero_mul, zero_mul]
    · rw [hn₂ n hn g hg hcg]
  refine ⟨Finset.Ico n₁ n₂, fun n hn => ?_, fun z hint => ?_⟩
  · simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
    rcases hn with hn | hn
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro g hg; rw [hn₁ n hn g hg]; ring
    ·
      rw [setIntegral_congr_fun (measurableSet_dshell p n)
        (fun g hg => by rw [hdeep n hn g hg]; ring :
          ∀ g ∈ dshell p n, c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
            Ψ 0 * (c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)))]
      rw [integral_const_mul]
      by_cases hΨ0 : Ψ 0 = 0
      · rw [hΨ0, zero_mul]
      rw [setIntegral_dshell_eq_zero_of_integral_translate_eq_zero p μ₂ ν' hν'ne hν'det c ξ n hcanc ?_, mul_zero]

      have hI := (hint₀.indicator (measurableSet_dshell p n)).const_mul ((Ψ 0)⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀))
      refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
      by_cases hg : g ∈ dshell p n
      · simp only [Set.indicator_of_mem hg]
        rw [hmod n z₀ g hg, hdeep n hn g hg]
        have hNN : (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀) = 1 := by
          rw [← Complex.cpow_add _ _ hN0, show (n : ℂ) * z₀ + -(n : ℂ) * z₀ = 0 by ring, Complex.cpow_zero]
        calc (Ψ 0)⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) *
              (c g * Ψ 0 * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀))
            = c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((Ψ 0)⁻¹ * Ψ 0) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀)) := by ring
          _ = c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by rw [inv_mul_cancel₀ hΨ0, hNN]; ring
      · simp only [Set.indicator_of_notMem hg, mul_zero]
  · exact integral_eq_sum_dshell p μ₂ _ _ hint (fun n => (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z))
      (fun n g hg => by rw [hmod n z g hg]; ring) (Finset.Ico n₁ n₂) (fun n hn => by

        simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hn
        rcases hn with hn | hn
        · apply setIntegral_eq_zero_of_forall_eq_zero
          intro g hg; rw [hn₁ n hn g hg]; ring
        · rw [setIntegral_congr_fun (measurableSet_dshell p n)
            (fun g hg => by rw [hdeep n hn g hg]; ring :
              ∀ g ∈ dshell p n, c g * Ψ (g : M2) * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
                Ψ 0 * (c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)))]
          rw [integral_const_mul]
          by_cases hΨ0 : Ψ 0 = 0
          · rw [hΨ0, zero_mul]
          rw [setIntegral_dshell_eq_zero_of_integral_translate_eq_zero p μ₂ ν' hν'ne hν'det c ξ n hcanc ?_, mul_zero]
          have hI := (hint₀.indicator (measurableSet_dshell p n)).const_mul ((Ψ 0)⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀))
          refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
          by_cases hg : g ∈ dshell p n
          · simp only [Set.indicator_of_mem hg]
            rw [hmod n z₀ g hg, hdeep n hn g hg]
            have hNN : (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀) = 1 := by
              rw [← Complex.cpow_add _ _ hN0, show (n : ℂ) * z₀ + -(n : ℂ) * z₀ = 0 by ring, Complex.cpow_zero]
            calc (Ψ 0)⁻¹ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) *
                  (c g * Ψ 0 * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀))
                = c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((Ψ 0)⁻¹ * Ψ 0) *
                    ((Ideal.absNorm p.asIdeal : ℂ) ^ ((n : ℂ) * z₀) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * z₀)) := by ring
              _ = c g * ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by rw [inv_mul_cancel₀ hΨ0, hNN]; ring
          · simp only [Set.indicator_of_notMem hg, mul_zero])

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem exists_mem_ball (t : Qp) : ∃ k : ℤ, t ∈ ball p k := by
  by_cases ht : t = 0
  · exact ⟨0, by simp [ball, ht]⟩
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v t = WithZero.exp m :=
      ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 ht)).symm⟩
    exact ⟨m, by simp [ball, hm]⟩

theorem ball_mono {k k' : ℤ} (h : k ≤ k') : ball p k ⊆ ball p k' :=
  fun x hx => le_trans hx (WithZero.exp_le_exp.2 h)

theorem exists_forall_setIntegral_ball_coeff_eq_zero (μ₂ : Measure G2) [IsFiniteMeasureOnCompacts μ₂] (Ω : Set G2) (hΩc : IsCompact Ω)
    (hΩm : MeasurableSet Ω) (μ : Measure Qp) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (w : G2 → ℂ)
    (hw : w ∈ Submodule.span ℂ {D : G2 → ℂ | ∃ W' : G2 → ℂ,
      (∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W' (g * k) = W' g) ∧
      ∃ t : Qp, D = fun g : G2 => W' (g * unipotent t) - W' g}) :
    ∃ k : ℤ, ∀ g : G2,
      (∫ x in ball p k, (∫ kk in Ω, w (kk * (g * unipotent x)) ∂μ₂) ∂μ) = 0 := by
  classical
  obtain ⟨n, f, D, hsum⟩ := Submodule.mem_span_set'.1 hw

  have hD : ∀ i : Fin n, ∃ W' : G2 → ℂ, (∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W' (g * k) = W' g) ∧
      ∃ t : Qp, ((D i : G2 → ℂ)) = fun g : G2 => W' (g * unipotent t) - W' g := fun i => (D i).2
  choose W' hWsm t hDt using hD

  have hk : ∃ k : ℤ, ∀ i, t i ∈ ball p k := by
    choose ks hks using fun i => exists_mem_ball p (t i)
    refine ⟨∑ i, |ks i|, fun i => ball_mono p ?_ (hks i)⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |ks j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, fun g => ?_⟩

  have hWlc : ∀ i, IsLocallyConstant (W' i) := by
    intro i
    obtain ⟨U, hU, hinv⟩ := hWsm i
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    have hopen : IsOpen ((fun u => g₀ * u) '' (U : Set G2)) := (Homeomorph.mulLeft g₀).isOpenMap _ hU
    filter_upwards [hopen.mem_nhds ⟨1, U.one_mem, mul_one g₀⟩] with z hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact hinv u hu g₀
  have hIntΩ : ∀ i (h : G2), IntegrableOn (fun kk => W' i (kk * h)) Ω μ₂ := fun i h =>
    ((hWlc i).continuous.comp (continuous_id.mul continuous_const)).continuousOn.integrableOn_compact hΩc

  have hwpt : ∀ h : G2, w h = ∑ i, f i * (W' i (h * unipotent (t i)) - W' i h) := by
    intro h
    have := congrFun hsum h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hDt i]

  set I : Fin n → Qp → ℂ := fun i x => ∫ kk in Ω, W' i (kk * (g * unipotent x)) ∂μ₂ with hI
  have hcoeff : ∀ x : Qp, (∫ kk in Ω, w (kk * (g * unipotent x)) ∂μ₂) = ∑ i, f i * (I i (x + t i) - I i x) := by
    intro x
    simp only [hI]
    rw [show (fun kk => w (kk * (g * unipotent x))) = fun kk => ∑ i, f i * (W' i (kk * (g * unipotent (x + t i))) - W' i (kk * (g * unipotent x))) by
      funext kk; rw [hwpt]; refine Finset.sum_congr rfl fun i _ => ?_; rw [mul_assoc, mul_assoc, unipotent_add]]
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Integrable (fun kk => f i * (W' i (kk * (g * unipotent (x + t i))) - W' i (kk * (g * unipotent x))))
          (μ₂.restrict Ω) :=
      fun i _ => ((hIntΩ i (g * unipotent (x + t i))).sub (hIntΩ i (g * unipotent x))).const_mul (f i)
    rw [integral_finsetSum _ hterm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_sub (hIntΩ i _) (hIntΩ i _)]

  have hIlc : ∀ i, IsLocallyConstant (I i) := by
    intro i
    obtain ⟨U, hU, hinv⟩ := hWsm i
    exact isLocallyConstant_coeff_unipotent p μ₂ Ω (W' i) U hU hinv g
  have hIint : ∀ i, IntegrableOn (I i) (ball p k) μ := fun i =>
    (hIlc i).continuous.continuousOn.integrableOn_compact (isCompact_ball p k)
  have hIint' : ∀ i, IntegrableOn (fun x => I i (x + t i)) (ball p k) μ := fun i =>
    ((hIlc i).continuous.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact (isCompact_ball p k)
  rw [setIntegral_congr_fun (measurableSet_ball p k) (fun x _ => hcoeff x)]
  have hterm2 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun x => f i * (I i (x + t i) - I i x)) (μ.restrict (ball p k)) :=
    fun i _ => ((hIint' i).sub (hIint i)).const_mul (f i)
  rw [integral_finsetSum _ hterm2]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, integral_sub (hIint' i) (hIint i), setIntegral_ball_comp_add p μ (hk i) (I i), sub_self,
    mul_zero]

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem hShell_main
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hSC : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))) (hLC : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)))
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦlc : IsLocallyConstant Φ) (hΦcs : HasCompactSupport Φ)
    (σ₂ : ℝ)
    (hi : ∀ s : ℂ, σ₂ < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂)
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩΦ : ∀ k ∈ Ω, ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      Φ (((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X) = Φ X)
    (hΩχ : ∀ k ∈ Ω, ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1)
    (hΩdet : ∀ k ∈ Ω, modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1) :
    ∃ S : Finset ℤ,
      (∀ n, n ∉ S → (∫ g in {g : GL (Fin 2) (p.adicCompletion ℚ) |
          Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) = WithZero.exp (-n)},
        (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0) ∧
      ∀ s : ℂ, σ₂ < s.re →
        (∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) *
            Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂) =
          ∑ n ∈ S, (∫ g in {g : GL (Fin 2) (p.adicCompletion ℚ) |
              Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) = WithZero.exp (-n)},
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * (s + 1 / 2)) := by
  haveI := hSC
  haveI := hLC
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : μ₂.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1
  set c₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun g => ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂ with hc₀
  show ∃ S : Finset ℤ, (∀ n, n ∉ S → (∫ g in dshell p n, c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0) ∧ ∀ s : ℂ, σ₂ < s.re →
        (∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂) =
          ∑ n ∈ S, (∫ g in dshell p n, c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * (s + 1 / 2))
  have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
  have hΩfin : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hΩc.measure_lt_top
  have hwlc : IsLocallyConstant w := GJJLGlue.isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw

  have hIntc : ∀ s : ℂ, σ₂ < s.re → Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ := by
    intro s hs
    set Fs : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
      w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) with hFs
    have hFint : Integrable Fs μ₂ := hi s hs
    have hFm : Measurable Fs := by
      refine Continuous.measurable ?_
      exact ((hwlc.continuous.mul (hΦlc.continuous.comp Units.continuous_val)).mul
        (GJJLGlue.continuous_chi_det p χ hχ)).mul (GJJLGlue.continuous_modulus_det_cpow p (s + 1 / 2))
    obtain ⟨hT, -⟩ := GJJLGlue.integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))
      hΩm hΩfin Fs hFm hFint id continuous_id
    refine hT.congr (Filter.Eventually.of_forall fun h => ?_)
    show (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fs (id k * h) ∂μ₂) = _
    have hpt : ∀ k ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fs (id k * h) =
        w (k * h) * (Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) := by
      intro k hk
      simp only [hFs, id]
      rw [Units.val_mul, hΩΦ k hk, map_mul, map_mul, Units.val_mul,
        hΩχ k hk, one_mul, Units.val_mul, GJJLGlue.modulus_mul' p, hΩdet k hk, one_mul]
      ring
    rw [setIntegral_congr_fun hΩm hpt, integral_mul_const, hc₀]
    ring

  obtain ⟨C, hC, hcZ'⟩ := LanglandsTunnell.RankinSelberg.exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
    p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp μ₂ Ω hΩo hΩc 1 w hw
  have hcZ : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ g ≠ 0 →
      ∃ z : (p.adicCompletion ℚ)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C := by
    intro g hg
    apply hcZ' g
    simpa only [one_mul, hc₀] using hg

  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := ALLTWIST.TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  have hK₁ := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hspan : w ∈ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ |
      ∃ W' : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
        (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
          ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W' (g * k) = W' g) ∧
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} := by
    have hJ := AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcusp w hw
    refine Submodule.span_mono ?_ hJ
    rintro D ⟨W', hW'V, t, rfl⟩
    exact ⟨W', ALLTWIST.TSE.smooth_of_mem_span w₂base _ hK₁ hw₂K W' hW'V, t, rfl⟩
  obtain ⟨kB, hkB⟩ := ShellFin.exists_forall_setIntegral_ball_coeff_eq_zero p μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))
    hΩc hΩm (selfDualHaarAt ℚ p) w hspan

  have hBfin : (selfDualHaarAt ℚ p) (ShellFin.ball p kB) < ⊤ := (ShellFin.isCompact_ball p kB).measure_lt_top
  haveI : IsFiniteMeasure ((selfDualHaarAt ℚ p).restrict (ShellFin.ball p kB)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  set ν' : Measure (GL (Fin 2) (p.adicCompletion ℚ)) :=
    Measure.map (fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)))
      ((selfDualHaarAt ℚ p).restrict (ShellFin.ball p kB)) with hν'
  have hnm : Measurable fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) :=
    (ShellFin.continuous_unipotent p).measurable
  haveI : IsFiniteMeasure ν' := Measure.isFiniteMeasure_map _ _
  have hν'ne : ν' Set.univ ≠ 0 := by
    rw [hν', Measure.map_apply hnm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
    exact ((ShellFin.isOpen_ball p kB).measure_pos _ ⟨0, by simp [ShellFin.ball]⟩).ne'
  have hν'det : ν' {u : GL (Fin 2) (p.adicCompletion ℚ) | Matrix.GeneralLinearGroup.det u ≠ 1} = 0 := by
    have hms : MeasurableSet {u : GL (Fin 2) (p.adicCompletion ℚ) | Matrix.GeneralLinearGroup.det u ≠ 1} := by
      have : {u : GL (Fin 2) (p.adicCompletion ℚ) | Matrix.GeneralLinearGroup.det u ≠ 1} =
          (fun u : GL (Fin 2) (p.adicCompletion ℚ) => (((Matrix.GeneralLinearGroup.det u : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))) ⁻¹' {1}ᶜ := by
        ext u; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq, Units.val_eq_one]
      rw [this]
      exact (isClosed_singleton.preimage (ShellFin.continuous_det_coe p)).measurableSet.compl
    rw [hν', Measure.map_apply hnm hms]
    have : (fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ))) ⁻¹'
        {u : GL (Fin 2) (p.adicCompletion ℚ) | Matrix.GeneralLinearGroup.det u ≠ 1} = ∅ := by
      ext x; simp [ShellFin.det_unipotent]
    rw [this, measure_empty]

  obtain ⟨Uw, hUw, hwU⟩ := ALLTWIST.TSE.smooth_of_mem_span w₂base _ hK₁ hw₂K w hw
  have hc₀cont : Continuous c₀ := by
    refine E3ReduceSupply.continuous_of_rightInvariant c₀ ⟨Uw, hUw, fun k hk g => ?_⟩
    simp only [hc₀]
    congr 1; funext kk; rw [← mul_assoc, hwU k hk]
  have hcanc : ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ u, c₀ (g * u) ∂ν') = 0 := by
    intro g
    have hmeas : AEStronglyMeasurable (fun u : GL (Fin 2) (p.adicCompletion ℚ) => c₀ (g * u)) ν' :=
      (hc₀cont.comp (continuous_mul_left g)).aestronglyMeasurable
    rw [hν'] at hmeas ⊢
    rw [integral_map hnm.aemeasurable hmeas]
    have := hkB g
    simpa only [hc₀] using this

  obtain ⟨S, hS0, hS⟩ := ShellFin.exists_finset_integral_eq_sum_dshell' p μ₂ Φ hΦlc hΦcs c₀ C hC hcZ ν' hν'ne hν'det
    hcanc χ ((σ₂ : ℂ) + 1 + 1 / 2) (hIntc ((σ₂ : ℂ) + 1) (by simp))
  exact ⟨S, fun n hn => hS0 n hn, fun s hs => hS (s + 1 / 2) (hIntc s hs)⟩

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

noncomputable section
namespace ShellFin

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "Qp" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)
local notation "M2" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem det_transposeInvN (g : G2) :
    Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    coe_transposeInvN, Matrix.det_transpose, ← Matrix.det_mul, Matrix.coe_units_inv, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit), Matrix.det_one, Units.val_one]

theorem transposeInvN_scalar (z : (Qp)ˣ) :
    transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ := by
  have e4 : ∀ u : (Qp)ˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : M2) = Matrix.diagonal fun _ => (u : Qp) := fun _ => rfl
  have hinv : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ := by
    rw [← map_inv]
  apply Units.ext
  rw [coe_transposeInvN, hinv, e4, Matrix.diagonal_transpose]

theorem modulus_det_transposeInvN (g : G2) :
    modulus ((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) g) : (Qp)ˣ) : Qp) =
      (modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp))⁻¹ := by
  rw [det_transposeInvN, Units.val_inv_eq_inv_val]
  have h0 : ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) ≠ 0 := Units.ne_zero _
  have h : modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp)⁻¹ * modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) = 1 := by
    rw [← modulus_mul, inv_mul_cancel₀ h0, modulus_one]
  exact eq_inv_of_mul_eq_one_left h

theorem modulus_coe_unit_inv (u : (Qp)ˣ) : modulus ((u⁻¹ : (Qp)ˣ) : Qp) = (modulus (u : Qp))⁻¹ := by
  rw [Units.val_inv_eq_inv_val]
  have h0 : (u : Qp) ≠ 0 := Units.ne_zero _
  have h : modulus (u : Qp)⁻¹ * modulus (u : Qp) = 1 := by
    rw [← modulus_mul, inv_mul_cancel₀ h0, modulus_one]
  exact eq_inv_of_mul_eq_one_left h

theorem hShelld_main
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (hSC : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))) (hLC : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)))
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦlc : IsLocallyConstant Φ) (hΦcs : HasCompactSupport Φ)
    (σ₃ : ℝ)
    (hiii : ∀ s : ℂ, σ₃ < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        w (transposeInvN (Fin 2) g) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂)
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩΦ : ∀ k ∈ Ω, ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
      Φ (((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X) = Φ X)
    (hΩχ : ∀ k ∈ Ω, ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1)
    (hΩdet : ∀ k ∈ Ω, modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1) :
    ∃ S : Finset ℤ,
      (∀ n, n ∉ S → (∫ g in {g : GL (Fin 2) (p.adicCompletion ℚ) |
          Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) = WithZero.exp (-n)},
        (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0) ∧
      ∀ s : ℂ, σ₃ < s.re →
        (∫ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂) =
          ∑ n ∈ S, (∫ g in {g : GL (Fin 2) (p.adicCompletion ℚ) |
              Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) = WithZero.exp (-n)},
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) *
              matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * (s + 3 / 2)) := by
  haveI := hSC
  haveI := hLC
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : μ₂.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1
  haveI : (selfDualHaarAt ℚ p).IsAddHaarMeasure := ALLTWIST.TSE.isAddHaarMeasure_selfDualHaarAt ℚ p
  set c₀ : G2 → ℂ := fun g => ∫ k in (Ω : Set G2), w (k * g) ∂μ₂ with hc₀
  set c' : G2 → ℂ := fun g => c₀ (transposeInvN (Fin 2) g) with hc'
  show ∃ S : Finset ℤ, (∀ n, n ∉ S → (∫ g in dshell p n, c' g * (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (g : M2) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = 0) ∧ ∀ s : ℂ, σ₃ < s.re →
        (∫ g : G2, c' g * (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (g : M2) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂) =
          ∑ n ∈ S, (∫ g in dshell p n, c' g * (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (g : M2) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-(n : ℂ) * (s + 3 / 2))
  have hΩm : MeasurableSet (Ω : Set G2) := hΩo.measurableSet
  have hΩfin : μ₂ (Ω : Set G2) < ⊤ := hΩc.measure_lt_top
  have hK₁ := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2
  have hwlc : IsLocallyConstant w := GJJLGlue.isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw

  obtain ⟨hψ0, hψ1⟩ := E3ReduceSupplyF.level_zero p
  have hΨSB : IsSchwartzBruhat (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) :=
    LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 hψ0 hψ1 Φ ⟨hΦlc, hΦcs⟩

  have hΨinv : ∀ k ∈ Ω, ∀ X : M2, (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (((transposeInvN (Fin 2) k : G2) : M2) * X) = (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) X := by
    intro k hk X
    have hkinv : k⁻¹ ∈ Ω := Ω.inv_mem hk
    have h := LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p (NumberField.StandardAddChar.psiLocal ℚ p) k⁻¹ Φ X
    have hfun : (fun Y : M2 => Φ ((((k⁻¹)⁻¹ : G2) : M2) * Y)) = Φ := by
      funext Y; rw [inv_inv]; exact hΩΦ k hk Y
    rw [hfun, hΩdet k⁻¹ hkinv] at h
    simp only [NNReal.coe_one, Complex.ofReal_one, one_pow, one_mul] at h
    rw [h, coe_transposeInvN]

  have hιι : ∀ g : G2, transposeInvN (Fin 2) (transposeInvN (Fin 2) g) = g := fun g => transposeInvN_transposeInvN (Fin 2) g
  have hιmul : ∀ g h : G2, transposeInvN (Fin 2) (g * h) = transposeInvN (Fin 2) g * transposeInvN (Fin 2) h := fun g h => transposeInvN_mul (Fin 2) g h
  have hιcont : Continuous (transposeInvN (Fin 2) : G2 → G2) := E3ReduceSupply.continuous_transposeInvN p

  have hIntc : ∀ s : ℂ, σ₃ < s.re → Integrable (fun g : G2 => c' g * (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (g : M2) *
      ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ := by
    intro s hs
    set Fs : G2 → ℂ := fun g => w (transposeInvN (Fin 2) g) * (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (g : M2) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ (s + 3 / 2) with hFs
    have hFint : Integrable Fs μ₂ := hiii s hs
    have hχ' : IsLocallyConstant (χ⁻¹ : (Qp)ˣ →* ℂˣ) := by
      have : ((χ⁻¹ : (Qp)ˣ →* ℂˣ) : (Qp)ˣ → ℂˣ) = fun y => (χ y)⁻¹ := by funext y; rfl
      rw [this]; exact hχ.comp (fun u : ℂˣ => u⁻¹)
    have hFm : Measurable Fs := by
      refine Continuous.measurable ?_
      exact (((hwlc.continuous.comp hιcont).mul (hΨSB.1.continuous.comp Units.continuous_val)).mul
        (GJJLGlue.continuous_chi_det p χ⁻¹ hχ')).mul (GJJLGlue.continuous_modulus_det_cpow p (s + 3 / 2))
    obtain ⟨hT, -⟩ := GJJLGlue.integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set G2) hΩm hΩfin Fs hFm hFint (transposeInvN (Fin 2)) hιcont
    refine hT.congr (Filter.Eventually.of_forall fun h => ?_)
    show (∫ k in (Ω : Set G2), Fs (transposeInvN (Fin 2) k * h) ∂μ₂) = _
    have hpt : ∀ k ∈ (Ω : Set G2), Fs (transposeInvN (Fin 2) k * h) =
        w (k * transposeInvN (Fin 2) h) * ((matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) (h : M2) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (Qp)ˣ) : Qp) : ℝ) : ℂ) ^ (s + 3 / 2)) := by
      intro k hk
      simp only [hFs]
      rw [hιmul, hιι, Units.val_mul, hΨinv k hk, map_mul, det_transposeInvN, map_mul, map_inv, Units.val_mul,
        MonoidHom.inv_apply, inv_inv, hΩχ k hk, one_mul, Units.val_mul, GJJLGlue.modulus_mul' p,
        modulus_coe_unit_inv, hΩdet k hk, inv_one, one_mul]
      ring
    rw [setIntegral_congr_fun hΩm hpt, integral_mul_const, hc', hc₀]
    ring

  obtain ⟨C, hC, hcZ'⟩ := LanglandsTunnell.RankinSelberg.exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
    p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp μ₂ Ω hΩo hΩc 1 w hw
  have hcZ : ∀ g : G2, c' g ≠ 0 → ∃ z : (Qp)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ transposeInvN (Fin 2) '' C := by
    intro g hg
    have hg' : (∫ k in (Ω : Set G2), w (1 * k * transposeInvN (Fin 2) g) ∂μ₂) ≠ 0 := by simpa only [one_mul, hc', hc₀] using hg
    obtain ⟨z, hz⟩ := hcZ' (transposeInvN (Fin 2) g) hg'
    refine ⟨z⁻¹, ⟨_, hz, ?_⟩⟩
    rw [hιmul, hιι, transposeInvN_scalar]

  set w' : G2 → ℂ := fun g => w (g * wJ) with hw'
  have hw'V := ALLTWIST.TSE.translate_mem_span w₂base hw wJ
  have hspan : w' ∈ Submodule.span ℂ {D : G2 → ℂ | ∃ W' : G2 → ℂ,
      (∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W' (g * k) = W' g) ∧
      ∃ t : Qp, D = fun g : G2 => W' (g * unipotent t) - W' g} := by
    have hJ := AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
      p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcusp w' hw'V
    refine Submodule.span_mono ?_ hJ
    rintro D ⟨W', hW'V, t, rfl⟩
    exact ⟨W', ALLTWIST.TSE.smooth_of_mem_span w₂base _ hK₁ hw₂K W' hW'V, t, rfl⟩
  obtain ⟨kB, hkB⟩ := exists_forall_setIntegral_ball_coeff_eq_zero p μ₂ (Ω : Set G2) hΩc hΩm (selfDualHaarAt ℚ p) w' hspan
  have hBfin : (selfDualHaarAt ℚ p) (ball p kB) < ⊤ := (isCompact_ball p kB).measure_lt_top
  haveI : IsFiniteMeasure ((selfDualHaarAt ℚ p).restrict (ball p kB)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  set nn : Qp → G2 := fun x => transposeInvN (Fin 2) (wJ⁻¹ * unipotent x * wJ) with hnn
  have hnncont : Continuous nn := hιcont.comp ((continuous_const.mul (continuous_unipotent p)).mul continuous_const)
  have hnm : Measurable nn := hnncont.measurable
  set ν' : Measure G2 := Measure.map nn ((selfDualHaarAt ℚ p).restrict (ball p kB)) with hν'
  haveI : IsFiniteMeasure ν' := Measure.isFiniteMeasure_map _ _
  have hν'ne : ν' Set.univ ≠ 0 := by
    rw [hν', Measure.map_apply hnm MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
    exact ((isOpen_ball p kB).measure_pos _ ⟨0, by simp [ball]⟩).ne'
  have hdetnn : ∀ x : Qp, Matrix.GeneralLinearGroup.det (nn x) = 1 := by
    intro x
    simp only [hnn, det_transposeInvN, map_mul, det_unipotent, mul_one, map_inv, inv_mul_cancel, inv_one]
  have hν'det : ν' {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} = 0 := by
    have hms : MeasurableSet {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} := by
      have : {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} =
          (fun u : G2 => (((Matrix.GeneralLinearGroup.det u : (Qp)ˣ) : Qp))) ⁻¹' {1}ᶜ := by
        ext u; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq, Units.val_eq_one]
      rw [this]
      exact (isClosed_singleton.preimage (continuous_det_coe p)).measurableSet.compl
    rw [hν', Measure.map_apply hnm hms]
    have : nn ⁻¹' {u : G2 | Matrix.GeneralLinearGroup.det u ≠ 1} = ∅ := by
      ext x; simp [hdetnn]
    rw [this, measure_empty]

  obtain ⟨Uw, hUw, hwU⟩ := ALLTWIST.TSE.smooth_of_mem_span w₂base _ hK₁ hw₂K w hw
  have hc₀cont : Continuous c₀ := by
    refine E3ReduceSupply.continuous_of_rightInvariant c₀ ⟨Uw, hUw, fun k hk g => ?_⟩
    simp only [hc₀]
    congr 1; funext kk; rw [← mul_assoc, hwU k hk]
  have hc'cont : Continuous c' := hc₀cont.comp hιcont
  have hcanc : ∀ g : G2, (∫ u, c' (g * u) ∂ν') = 0 := by
    intro g
    have hmeas : AEStronglyMeasurable (fun u : G2 => c' (g * u)) ν' := (hc'cont.comp (continuous_mul_left g)).aestronglyMeasurable
    rw [hν'] at hmeas ⊢
    rw [integral_map hnm.aemeasurable hmeas]
    have key : ∀ x : Qp, c' (g * nn x) = ∫ kk in (Ω : Set G2), w' (kk * (transposeInvN (Fin 2) g * wJ⁻¹ * unipotent x)) ∂μ₂ := by
      intro x
      simp only [hc', hc₀, hnn, hw', hιmul, hιι]
      congr 1; funext kk
      simp only [mul_assoc]
    simp_rw [key]
    exact hkB (transposeInvN (Fin 2) g * wJ⁻¹)
  obtain ⟨S, hS0, hS⟩ := exists_finset_integral_eq_sum_dshell' p μ₂ (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) hΨSB.1 hΨSB.2 c' (transposeInvN (Fin 2) '' C) (hC.image hιcont) hcZ ν' hν'ne hν'det
    hcanc χ⁻¹ ((σ₃ : ℂ) + 1 + 3 / 2) (hIntc ((σ₃ : ℂ) + 1) (by simp))
  exact ⟨S, fun n hn => hS0 n hn, fun s hs => hS (s + 3 / 2) (hIntc s hs)⟩

end ShellFin
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"
end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

open scoped Classical

namespace J3cFE

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

theorem shellB_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hSC : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))) (hLC : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)))
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w wK : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ) (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (Φh : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ)
    (ΦK : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ)
    (hΦK : ΦK = fun X =>
      if h : X.det ≠ 0 then
        wK (diagOne (Units.mk0 X.det h)) *
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (1 * k * (Matrix.GeneralLinearGroup.mkOfDetNeZero X h)⁻¹) ∂μ₂) *
          (((modulus X.det : ℝ) : ℂ))⁻¹
      else 0)
    (n : ℤ)
    (hwKf : ∀ y : (p.adicCompletion ℚ)ˣ, wK (diagOne y) = (((χ y : ℂˣ) : ℂ))⁻¹ *
      (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-n) then (1 : ℂ) else 0))
    (κ : ℝ) (hκ : 0 < κ)
    (hHL : ∀ (f : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ), Integrable f μ₂ →
      Integrable (fun X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =>
          if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
        (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) ∧
      ∫ g, f g ∂μ₂ =
        (κ : ℂ) * ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
          (if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
          ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p))
    (sB : ℂ)
    (hIB : Integrable (fun g : (GL (Fin 2) (p.adicCompletion ℚ)) =>
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) * Φh (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) : ℝ) : ℂ) ^ sB) μ₂) :
    (∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(n))},
        (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) * Φh (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) =
      (κ : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ n *
        ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), Φh X * ΦK (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by

  haveI := hSC
  haveI := hLC
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hqzne : ∀ k : ℤ, (q ^ k : ℂ) ≠ 0 := fun k => zpow_ne_zero k hq0

  obtain ⟨-, -, -, hmodshell, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have hmodU : ∀ (k : ℤ) (y : (p.adicCompletion ℚ)ˣ), Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-k) →
      ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) = q ^ (-k) := by
    intro k y hy
    have h := hmodshell k y hy
    rw [h, hq]; push_cast; rfl
  have hmodM : ∀ (k : ℤ) (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))), X.det ≠ 0 → Valued.v X.det = WithZero.exp (-k) →
      ((modulus X.det : ℝ) : ℂ) = q ^ (-k) := by
    intro k X hX hv
    have h := hmodU k (Units.mk0 X.det hX) (by rwa [Units.val_mk0])
    rwa [Units.val_mk0] at h

  have hdetc : Continuous fun g : (GL (Fin 2) (p.adicCompletion ℚ)) => ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) :=
    Units.continuous_val.comp (GJJLGlue.continuous_det2 p)
  have hshellm : ∀ k : ℤ, MeasurableSet {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(k))} := by
    intro k
    have hopen : IsOpen {x : (p.adicCompletion ℚ) | Valued.v x = WithZero.exp (-k)} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hx' : Valued.v x = WithZero.exp (-k) := hx
      have hne : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [hx']; exact WithZero.coe_ne_zero
      have h := Valued.locally_const hne
      simpa only [hx'] using h
    exact (hopen.preimage hdetc).measurableSet

  have hcoe : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0),
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero X hX : (GL (Fin 2) (p.adicCompletion ℚ))) : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = X := fun X hX => rfl
  have hdetG : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0),
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero X hX) = Units.mk0 X.det hX :=
    fun X hX => Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mk0, hcoe X hX])
  have hmk : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0) (hXt : (Matrix.transpose X).det ≠ 0),
      Units.mk0 (Matrix.transpose X).det hXt = Units.mk0 X.det hX :=
    fun X hX hXt => Units.ext (by rw [Units.val_mk0, Units.val_mk0, Matrix.det_transpose])

  have hmkG : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0) (hXt : (Matrix.transpose X).det ≠ 0),
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transpose X) hXt)⁻¹ =
        transposeInvN (Fin 2) (Matrix.GeneralLinearGroup.mkOfDetNeZero X hX) := by
    intro X hX hXt
    refine Units.ext ?_
    rw [Matrix.coe_units_inv, coe_transposeInvN, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hcoe X hX,
      hcoe _ hXt]

  obtain ⟨gB, hgB⟩ : ∃ gB : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ, gB = fun g =>
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) * Φh (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ fB : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ, fB = ({g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(n))}).indicator gB := ⟨_, rfl⟩
  have hBn : (∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(n))},
        (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) * Φh (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = ∫ g, fB g ∂μ₂ := by
    rw [hfB, integral_indicator (hshellm n), hgB]
  have hfBint : Integrable fB μ₂ := by
    have hI := ((hIB).mul_const ((q ^ (-n)) ^ sB)⁻¹).indicator (hshellm n)
    refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hfB, hgB, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hg : Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) = WithZero.exp (-n)
    · rw [if_pos hg, if_pos hg, hmodU n _ hg, mul_inv_cancel_right₀ (GJJLGlue.cpow_ne_zero'' (hqzne (-n)) _)]
    · rw [if_neg hg, if_neg hg]
  obtain ⟨-, hHLB⟩ := hHL fB hfBint
  have hE3 : ∀ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
      (if h : X.det ≠ 0 then fB (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) *
          ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0) =
        q ^ n * (Φh X * ΦK (Matrix.transpose X)) := by
    intro X
    by_cases hX : X.det = 0
    · have hXt : ¬ (Matrix.transpose X).det ≠ 0 := by rw [Matrix.det_transpose]; exact not_not.2 hX
      rw [dif_neg (not_not.2 hX)]
      simp only [hΦK, dif_neg hXt, mul_zero]
    · have hXt : (Matrix.transpose X).det ≠ 0 := by rwa [Matrix.det_transpose]
      rw [dif_pos hX]
      simp only [hΦK, dif_pos hXt, hfB, Set.indicator_apply, hgB, Set.mem_setOf_eq]
      have hmt : ((modulus (Matrix.transpose X).det : ℝ) : ℂ) = ((modulus X.det : ℝ) : ℂ) := by
        rw [Matrix.det_transpose]
      simp only [hmk X hX hXt, hmkG X hX hXt, hwKf, one_mul, hmt, hcoe, hdetG X hX, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.GeneralLinearGroup.val_det_apply]
      by_cases hs : Valued.v X.det = WithZero.exp (-n)
      · simp only [if_pos hs, hmodM n X hX hs]
        have hχne : ((χ (Units.mk0 X.det hX) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        rw [zpow_neg]
        field_simp
        all_goals ring
      · simp only [if_neg hs]
        all_goals simp
  rw [hBn, hHLB]
  simp_rw [hE3]
  have hc : (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), q ^ n * (Φh X * ΦK (Matrix.transpose X)) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) =
      q ^ n * ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), Φh X * ΦK (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := integral_const_mul _ _
  rw [hc, mul_assoc]

theorem parseval_transpose
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ) (hΦlc : IsLocallyConstant Φ) (hΦcs : HasCompactSupport Φ)
    (ΦK : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ) (hΦKlc : IsLocallyConstant ΦK) (hΦKcs : HasCompactSupport ΦK) :
    (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ X * ΦK (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) =
      ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), Φ (Matrix.transpose X) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) ΦK X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨hΦTlc, hΦTcs⟩ := GJJLParseval.isLocallyConstant_and_hasCompactSupport_comp_transpose p Φ hΦlc hΦcs
  have h1 := GJJLParseval.integral_comp_transpose_eq p
    (fun X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) => matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (Matrix.transpose X) * ΦK X)
  simp only [Matrix.transpose_transpose] at h1
  have h2 : ∀ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (Matrix.transpose X) =
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun Y : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) => Φ (Matrix.transpose Y)) X :=
    fun X => (GJJLParseval.matFourier22_comp_transpose p Φ hΦlc hΦcs X).symm
  have h3 := LanglandsTunnell.RankinSelberg.integral_matFourier22_mul_eq_integral_mul_matFourier22 p
    (fun Y : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) => Φ (Matrix.transpose Y)) ΦK hΦTlc hΦTcs hΦKlc hΦKcs
  beta_reduce at h3
  rw [h1]
  simp_rw [h2]
  exact h3

theorem shellA_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hSC : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))) (hLC : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)))
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (χ θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (w wK : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ) (wJ : (GL (Fin 2) (p.adicCompletion ℚ))) (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (Φ : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ) (ΦK : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ)
    (E₀ : ℂ) (e₀ n : ℤ)
    (hwJ' : ∀ y : (p.adicCompletion ℚ)ˣ, wK (diagOne y * wJ) =
      E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ : ℤ) : ℂ) / 2) * ((χ y : ℂˣ) : ℂ) * ((θ₀ y : ℂˣ) : ℂ) *
        (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-(e₀ - n)) then (1 : ℂ) else 0))
    (hFK : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (h : X.det ≠ 0),
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) ΦK X =
        wK (diagOne (Units.mk0 X.det h) * wJ) *
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (1 * k * Matrix.GeneralLinearGroup.mkOfDetNeZero (X.transpose)
            (by rwa [Matrix.det_transpose])) ∂μ₂) *
          (((modulus X.det : ℝ) : ℂ))⁻¹ * (((θ₀ (Units.mk0 X.det h) : ℂˣ) : ℂ))⁻¹)
    (κ : ℝ) (hκ : 0 < κ)
    (hHL : ∀ (f : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ), Integrable f μ₂ →
      Integrable (fun X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =>
          if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
        (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) ∧
      ∫ g, f g ∂μ₂ =
        (κ : ℂ) * ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
          (if h : X.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) * ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0)
          ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p))
    (sA : ℂ)
    (hIA : Integrable (fun g : (GL (Fin 2) (p.adicCompletion ℚ)) =>
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) : ℝ) : ℂ) ^ sA) μ₂) :
    (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), Φ (Matrix.transpose X) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) ΦK X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) =
      E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ : ℤ) : ℂ) / 2) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(e₀ - n)) *
        (κ : ℂ)⁻¹ *
        ∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(e₀ - n))},
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂ := by

  haveI := hSC
  haveI := hLC
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p
  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hqzne : ∀ k : ℤ, (q ^ k : ℂ) ≠ 0 := fun k => zpow_ne_zero k hq0

  obtain ⟨-, -, -, hmodshell, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p
  have hmodU : ∀ (k : ℤ) (y : (p.adicCompletion ℚ)ˣ), Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-k) →
      ((modulus (y : (p.adicCompletion ℚ)) : ℝ) : ℂ) = q ^ (-k) := by
    intro k y hy
    have h := hmodshell k y hy
    rw [h, hq]; push_cast; rfl
  have hmodM : ∀ (k : ℤ) (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))), X.det ≠ 0 → Valued.v X.det = WithZero.exp (-k) →
      ((modulus X.det : ℝ) : ℂ) = q ^ (-k) := by
    intro k X hX hv
    have h := hmodU k (Units.mk0 X.det hX) (by rwa [Units.val_mk0])
    rwa [Units.val_mk0] at h

  have hdetc : Continuous fun g : (GL (Fin 2) (p.adicCompletion ℚ)) => ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) :=
    Units.continuous_val.comp (GJJLGlue.continuous_det2 p)
  have hshellm : ∀ k : ℤ, MeasurableSet {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(k))} := by
    intro k
    have hopen : IsOpen {x : (p.adicCompletion ℚ) | Valued.v x = WithZero.exp (-k)} := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      have hx' : Valued.v x = WithZero.exp (-k) := hx
      have hne : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := by rw [hx']; exact WithZero.coe_ne_zero
      have h := Valued.locally_const hne
      simpa only [hx'] using h
    exact (hopen.preimage hdetc).measurableSet

  have hcoe : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0),
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero X hX : (GL (Fin 2) (p.adicCompletion ℚ))) : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) = X := fun X hX => rfl
  have hdetG : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0),
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero X hX) = Units.mk0 X.det hX :=
    fun X hX => Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mk0, hcoe X hX])
  have hmk : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (hX : X.det ≠ 0) (hXt : (Matrix.transpose X).det ≠ 0),
      Units.mk0 (Matrix.transpose X).det hXt = Units.mk0 X.det hX :=
    fun X hX hXt => Units.ext (by rw [Units.val_mk0, Units.val_mk0, Matrix.det_transpose])

  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hae : ∀ᵐ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p), X.det ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun X hX => ?_)
      (LanglandsTunnell.RankinSelberg.measure_pi_selfDualHaarAt_setOf_apply_eq_zero_or_det_eq_zero p)
    exact Or.inr (not_not.1 hX)
  obtain ⟨gA, hgA⟩ : ∃ gA : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ, gA = fun g => (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨fA, hfA⟩ : ∃ fA : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ, fA = ({g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(e₀ - n))}).indicator gA := ⟨_, rfl⟩
  have hAn : (∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(e₀ - n))},
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) = ∫ g, fA g ∂μ₂ := by
    rw [hfA, integral_indicator (hshellm (e₀ - n)), hgA]
  have hfAint : Integrable fA μ₂ := by
    have hI := ((hIA).mul_const ((q ^ (-(e₀ - n))) ^ sA)⁻¹).indicator (hshellm (e₀ - n))
    refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hfA, hgA, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hg : Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) = WithZero.exp (-(e₀ - n))
    · rw [if_pos hg, if_pos hg, hmodU (e₀ - n) _ hg,
        mul_inv_cancel_right₀ (GJJLGlue.cpow_ne_zero'' (hqzne (-(e₀ - n))) _)]
    · rw [if_neg hg, if_neg hg]
  obtain ⟨-, hHLA⟩ := hHL fA hfAint
  obtain ⟨HLA, hHLAdef⟩ : ∃ HLA : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ, HLA = fun X =>
    if h : X.det ≠ 0 then fA (Matrix.GeneralLinearGroup.mkOfDetNeZero X h) *
      ((((modulus X.det : ℝ) : ℂ)) ^ 2)⁻¹ else 0 := ⟨_, rfl⟩
  rw [← hHLAdef] at hHLA
  have hB3 : (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), Φ (Matrix.transpose X) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) ΦK X ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) =
      (E₀ * q ^ (((e₀ : ℤ) : ℂ) / 2) * q ^ (-(e₀ - n))) * ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), HLA (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) := by
    have hc : (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), (E₀ * q ^ (((e₀ : ℤ) : ℂ) / 2) * q ^ (-(e₀ - n))) * HLA (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) =
        (E₀ * q ^ (((e₀ : ℤ) : ℂ) / 2) * q ^ (-(e₀ - n))) * ∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), HLA (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p) :=
      integral_const_mul _ _
    rw [← hc]
    refine integral_congr_ae ?_
    filter_upwards [hae] with X hX
    have hXt : Matrix.det (Matrix.transpose X) ≠ 0 := by rwa [Matrix.det_transpose]
    rw [hFK X hX, hwJ' (Units.mk0 (Matrix.det X) hX)]
    simp only [hHLAdef, dif_pos hXt, hfA, Set.indicator_apply, hgA, Set.mem_setOf_eq]
    have hmt : ((modulus (Matrix.det (Matrix.transpose X)) : ℝ) : ℂ) = ((modulus (Matrix.det X) : ℝ) : ℂ) := by
      rw [Matrix.det_transpose]
    have hvt : Valued.v (Matrix.det (Matrix.transpose X)) = Valued.v (Matrix.det X) := by rw [Matrix.det_transpose]
    have hc₀T : (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (1 * k * Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transpose X)
        (by rwa [Matrix.det_transpose])) ∂μ₂) =
        ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transpose X) hXt) ∂μ₂ := by
      simp only [one_mul]
    rw [hc₀T]
    simp only [Units.val_mk0, hdetG _ hXt, hmk X hX hXt, hmt, hvt, hcoe, Matrix.GeneralLinearGroup.val_det_apply]
    by_cases hs : Valued.v (Matrix.det X) = WithZero.exp (-(e₀ - n))
    · simp only [if_pos hs, hmodM (e₀ - n) X hX hs]
      have hθne : ((θ₀ (Units.mk0 (Matrix.det X) hX) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      rw [zpow_neg]
      field_simp
      all_goals ring
    · simp only [if_neg hs]
      all_goals simp
  have hB4 : (∫ X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)), HLA (Matrix.transpose X) ∂(Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) = (κ : ℂ)⁻¹ * ∫ g, fA g ∂μ₂ := by
    rw [GJJLParseval.integral_comp_transpose_eq p HLA, hHLA, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]
  rw [hB3, hB4, ← hAn, hq]
  ring

theorem shellFE_main
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    (hSC : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ))) (hLC : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)))
    (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (w : (GL (Fin 2) (p.adicCompletion ℚ)) → ℂ)
    (hw : w ∈ Submodule.span ℂ (Set.range fun h : (GL (Fin 2) (p.adicCompletion ℚ)) => fun g : (GL (Fin 2) (p.adicCompletion ℚ)) => w₂base (g * h)))
    (Φ : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ) (hΦlc : IsLocallyConstant Φ) (hΦcs : HasCompactSupport Φ)
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩo : IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (σ₂ σ₃ : ℝ)
    (hIntA : ∀ s : ℂ, σ₂ < s.re → Integrable (fun g : (GL (Fin 2) (p.adicCompletion ℚ)) =>
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂)
    (hIntB : ∀ s : ℂ, σ₃ < s.re → Integrable (fun g : (GL (Fin 2) (p.adicCompletion ℚ)) =>
      (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) *
        matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) :
    ∀ n : ℤ,
      (∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(n))},
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * transposeInvN (Fin 2) g) ∂μ₂) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂) =
        E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((2 * (n : ℂ)) - (e₀ : ℂ) / 2) *
          ∫ g in {g : (GL (Fin 2) (p.adicCompletion ℚ)) | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))) = WithZero.exp (-(e₀ - n))},
            (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂) * Φ (g : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂ := by
  intro n
  haveI := hSC
  haveI := hLC
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p

  obtain ⟨cχ, hcχ⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p χ hχ.continuous

  obtain ⟨wK, hwKV, hwKf⟩ :=
    AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne p N hN w₂base
      hw₂law hw₂K hw₂ne hw₂irr
      (fun y : (p.adicCompletion ℚ)ˣ => (((χ y : ℂˣ) : ℂ))⁻¹ *
        (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-n) then (1 : ℂ) else 0))
      n n cχ
      (by
        intro y hy
        have hne : Valued.v (y : (p.adicCompletion ℚ)) ≠ WithZero.exp (-n) := by
          rcases hy with h | h
          · exact ne_of_gt h
          · exact ne_of_lt h
        simp only [if_neg hne, mul_zero])
      (by
        intro y u hu hle
        have hχu : χ u = 1 := hcχ.1 u ⟨hu, Or.inr hle⟩
        have hv : Valued.v ((y * u : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) = Valued.v (y : (p.adicCompletion ℚ)) := by
          rw [Units.val_mul, Valuation.map_mul, hu, mul_one]
        simp only [map_mul, hχu, mul_one, hv])

  have hwJ' := LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ E₀ e₀ hfe hcusp n wK hwKV hwKf

  obtain ⟨ΦK, hΦK⟩ : ∃ ΦK : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) → ℂ, ΦK = fun X =>
    if h : X.det ≠ 0 then
      wK (diagOne (Units.mk0 X.det h)) *
        (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (1 * k * (Matrix.GeneralLinearGroup.mkOfDetNeZero X h)⁻¹) ∂μ₂) *
        (((modulus X.det : ℝ) : ℂ))⁻¹
    else 0 := ⟨_, rfl⟩
  have hFKall :=
    LanglandsTunnell.RankinSelberg.matFourier22_kirillov_det_mul_coefficient_eq_of_cuspidal p θ₀ N hN w₂base
      hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp μ₂ Ω hΩo hΩc 1 w hw wK hwKV
  have hΦKlc : IsLocallyConstant ΦK := by rw [hΦK]; exact hFKall.1.1
  have hΦKcs : HasCompactSupport ΦK := by rw [hΦK]; exact hFKall.1.2
  have hFK : ∀ (X : (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) (h : X.det ≠ 0),
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) ΦK X =
        wK (diagOne (Units.mk0 X.det h) * wJ) *
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (1 * k * Matrix.GeneralLinearGroup.mkOfDetNeZero (X.transpose)
            (by rwa [Matrix.det_transpose])) ∂μ₂) *
          (((modulus X.det : ℝ) : ℂ))⁻¹ * (((θ₀ (Units.mk0 X.det h) : ℂˣ) : ℂ))⁻¹ := by
    intro X h; rw [hΦK]; exact hFKall.2 X h
  clear hFKall

  obtain ⟨κ, hκ, hHL⟩ := LanglandsTunnell.RankinSelberg.exists_pos_forall_integral_haar_eq_mul_integral_pi_det_inv_sq p μ₂
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'

  obtain ⟨hΦhlc, hΦhcs⟩ : IsLocallyConstant (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) ∧ HasCompactSupport (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) := by
    obtain ⟨hl0, hl1⟩ := E3ReduceSupplyF.level_zero p
    exact LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 hl0 hl1 Φ ⟨hΦlc, hΦcs⟩
  have hs₃ : σ₃ < (((σ₃ + 1 : ℝ) : ℂ)).re := by simp
  have hs₂ : σ₂ < (((σ₂ + 1 : ℝ) : ℂ)).re := by simp
  rw [shellB_eq p hSC hLC μ₂ χ w wK Ω (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) ΦK hΦK n hwKf κ hκ hHL _ (hIntB _ hs₃),
    parseval_transpose p Φ hΦlc hΦcs ΦK hΦKlc hΦKcs,
    shellA_eq p hSC hLC μ₂ χ θ₀ w wK wJ Ω Φ ΦK E₀ e₀ n hwJ' hFK κ hκ hHL _ (hIntA _ hs₂)]

  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
  have hexp : (q ^ n * q ^ (-(e₀ - n)) * q ^ (((e₀ : ℤ) : ℂ) / 2) : ℂ) = q ^ ((2 * (n : ℂ)) - (e₀ : ℂ) / 2) := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_intCast, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  rw [← hexp]
  field_simp
  all_goals ring

end J3cFE
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.RCgB P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ALLTWIST.TSE P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal.ShellFin"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
          ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ), Q ≠ 0 → Qd ≠ 0 →

            (∀ s : ℂ, σ₂ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) →

            (∀ s : ℂ, σ₂ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + 1 / 2) * Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ, σ₃ < s.re →
              Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                w (transposeInvN (Fin 2) g) *
                  matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                  ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) →

            (∀ s : ℂ, σ₃ < s.re →
              godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
                  (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) * Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) →

            (∀ s : ℂ,
              ((1 : Polynomial ℂ)).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) *
                  Q.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) =
                ((Polynomial.C E₀).eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-e₀ : ℤ) : ℂ) * s)) *
                  ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                  Qd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) := by
  intro μ₂ _ w hw Φ hΦlc hΦcs P Pd Q Qd m md σ₂ σ₃ hQ hQd hi hii hiii hiv
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  obtain ⟨hSC, hLC, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI := hLC

  set q : ℂ := (Ideal.absNorm p.asIdeal : ℂ) with hq
  have hq1 : 1 < (Ideal.absNorm p.asIdeal : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hqR : q = ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) := by rw [hq]; norm_cast
  set Z : ℂ → ℂ := fun s => godementZeta2 p μ₂ w Φ χ (s + 1 / 2) with hZ
  set Zd : ℂ → ℂ := fun s => godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
      (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) with hZd

  obtain ⟨P₁, Pd₁, m₁, md₁, σa, σb, -, hP₁', -, hPd₁'⟩ :=
    LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_of_forall_torusZeta_fe p θ₀ N hN w₂base
      hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ E₀ e₀ hfe μ₂ w hw Φ hΦlc hΦcs
  have hP₁ : ∀ s : ℂ, σa < s.re → Z s = q ^ ((m₁ : ℂ) * s) * P₁.eval (q ^ (-s)) := fun s hs => hP₁' s hs
  have hPd₁ : ∀ s : ℂ, σb < s.re → Zd s = q ^ ((md₁ : ℂ) * s) * Pd₁.eval (q ^ (-s)) := fun s hs => hPd₁' s hs

  have hFE : ∀ s : ℂ, q ^ ((md₁ : ℂ) * s) * Pd₁.eval (q ^ (-s)) =
      E₀ * q ^ (-(e₀ : ℂ) * s) * (q ^ ((m₁ : ℂ) * (-s)) * P₁.eval (q ^ (-(-s)))) := by

    have hΩ : ∃ Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
        IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        (∀ k ∈ Ω, ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
          Φ (((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X) = Φ X) ∧
        (∀ k ∈ Ω, ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1) ∧
        (∀ k ∈ Ω, modulus ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1) := by
      obtain ⟨W, hWo, hW⟩ := GJJLGlue.exists_isOpen_subgroup_forall_apply_mul_eq p Φ hΦlc hΦcs
      obtain ⟨Ω, hΩo, hΩc, hΩW, -, hΩk⟩ := GJJLGlue.exists_compact_open_subgroup_le p W W hWo hWo χ hχ
      exact ⟨Ω, hΩo, hΩc, fun k hk X => hW k (hΩW hk) X, fun k hk => (hΩk k hk).1, fun k hk => (hΩk k hk).2⟩
    obtain ⟨Ω, hΩo, hΩc, hΩΦ, hΩχ, hΩdet⟩ := hΩ

    set c₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
      fun g => ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (k * g) ∂μ₂ with hc₀

    have hAvgI : ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
        Z s = ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          ∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂ := by
      intro s hs
      set Fs : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
        w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) with hFs
      have hFint : Integrable Fs μ₂ := hi s hs
      have hwlc : IsLocallyConstant w := GJJLGlue.isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw
      have hFm : Measurable Fs := by
        refine Continuous.measurable ?_
        exact ((hwlc.continuous.mul (hΦlc.continuous.comp Units.continuous_val)).mul
          (GJJLGlue.continuous_chi_det p χ hχ)).mul (GJJLGlue.continuous_modulus_det_cpow p (s + 1 / 2))
      have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
      have hΩfin : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hΩc.measure_lt_top
      obtain ⟨hI, hT⟩ := GJJLGlue.integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))
        hΩm hΩfin Fs hFm hFint id continuous_id

      have hinner : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fs (id k * h) ∂μ₂) =
            c₀ h * Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) := by
        intro h
        have hpt : ∀ k ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fs (id k * h) =
            w (k * h) * (Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) := by
          intro k hk
          simp only [hFs, id]
          rw [Units.val_mul, hΩΦ k hk, map_mul, map_mul, Units.val_mul,
            hΩχ k hk, one_mul, Units.val_mul, GJJLGlue.modulus_mul' p, hΩdet k hk, one_mul]
          ring
        rw [setIntegral_congr_fun hΩm hpt, integral_mul_const, hc₀]
        ring
      simp_rw [hinner] at hI hT
      have hμne : ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) ≠ 0 := by
        have hpos : 0 < μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measure_pos μ₂ ⟨1, Ω.one_mem⟩
        exact_mod_cast (ENNReal.toReal_pos hpos.ne' hΩfin.ne).ne'
      have hZs : Z s = ∫ g, Fs g ∂μ₂ := by rw [hZ]; simp only; rw [godementZeta2_apply]
      refine ⟨hI, ?_⟩
      rw [hZs, hT, ← mul_assoc, inv_mul_cancel₀ hμne, one_mul]
    have hAvg : ∀ s : ℂ, σ₂ < s.re →
        Z s = ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          ∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂ :=
      fun s hs => (hAvgI s hs).2
    have hIntA : ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ :=
      fun s hs => (hAvgI s hs).1
    have hAvgdI : ∀ s : ℂ, σ₃ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => c₀ (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ ∧
        Zd s = ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          ∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂ := by
      intro s hs
      set Φh : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ :=
        matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ with hΦh
      set Fd : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
        w (transposeInvN (Fin 2) g) * Φh (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) with hFd
      have hFint : Integrable Fd μ₂ := hiii s hs
      have hwlc : IsLocallyConstant w := GJJLGlue.isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw

      have hΦhlc : IsLocallyConstant Φh := by
        obtain ⟨hl0, hl1⟩ := E3ReduceSupplyF.level_zero p
        rw [hΦh]
        exact (LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 hl0 hl1 Φ ⟨hΦlc, hΦcs⟩).1
      have hχi : IsLocallyConstant (χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
        have : ((χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun y => (χ y)⁻¹ := by
          funext y; rfl
        rw [this]; exact hχ.comp (fun z => z⁻¹)
      have hFm : Measurable Fd := by
        refine Continuous.measurable ?_
        exact (((hwlc.continuous.comp (E3ReduceSupply.continuous_transposeInvN p)).mul
          (hΦhlc.continuous.comp Units.continuous_val)).mul
          (GJJLGlue.continuous_chi_det p χ⁻¹ hχi)).mul (GJJLGlue.continuous_modulus_det_cpow p (s + 3 / 2))
      have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
      have hΩfin : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hΩc.measure_lt_top
      obtain ⟨hI, hT⟩ := GJJLGlue.integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))
        hΩm hΩfin Fd hFm hFint (transposeInvN (Fin 2)) (E3ReduceSupply.continuous_transposeInvN p)

      have hdetT : ∀ k : GL (Fin 2) (p.adicCompletion ℚ),
          Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) k) = Matrix.GeneralLinearGroup.det k⁻¹ := by
        intro k
        refine Units.ext ?_
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN,
          Matrix.det_transpose]
      have hΦhinv : ∀ k ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), ∀ X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ),
          Φh (((transposeInvN (Fin 2) k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X) = Φh X := by
        intro k hk X
        have hk' : k⁻¹ ∈ Ω := Ω.inv_mem hk
        have h1 := LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p (NumberField.StandardAddChar.psiLocal ℚ p) k⁻¹ Φ X
        have hfun : (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
            Φ ((((k⁻¹)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Y)) = Φ := by
          funext Y; rw [inv_inv]; exact hΩΦ k hk Y
        rw [hfun, hΩdet k⁻¹ hk'] at h1
        rw [hΦh, coe_transposeInvN]
        simpa using h1.symm
      have hinner : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fd (transposeInvN (Fin 2) k * h) ∂μ₂) =
            c₀ (transposeInvN (Fin 2) h) * Φh (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) := by
        intro h
        have hpt : ∀ k ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fd (transposeInvN (Fin 2) k * h) =
            w (k * transposeInvN (Fin 2) h) * (Φh (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) := by
          intro k hk
          have hk' : k⁻¹ ∈ Ω := Ω.inv_mem hk
          simp only [hFd]
          rw [transposeInvN_mul, transposeInvN_transposeInvN, Units.val_mul, hΦhinv k hk, map_mul, hdetT, map_mul,
            Units.val_mul, Units.val_mul, GJJLGlue.modulus_mul' p, hΩdet k⁻¹ hk', one_mul]
          have hχ1 : ((χ⁻¹ (Matrix.GeneralLinearGroup.det k⁻¹) : ℂˣ) : ℂ) = 1 := by
            rw [MonoidHom.inv_apply, map_inv, map_inv, inv_inv]; exact hΩχ k hk
          rw [hχ1, one_mul]
          ring
        rw [setIntegral_congr_fun hΩm hpt, integral_mul_const, hc₀]
        ring
      simp_rw [hinner] at hI hT
      have hμne : ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) ≠ 0 := by
        have hpos : 0 < μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measure_pos μ₂ ⟨1, Ω.one_mem⟩
        exact_mod_cast (ENNReal.toReal_pos hpos.ne' hΩfin.ne).ne'
      have hZs : Zd s = ∫ g, Fd g ∂μ₂ := by rw [hZd]; simp only; rw [godementZeta2_apply]
      refine ⟨hI, ?_⟩
      rw [hZs, hT, ← mul_assoc, inv_mul_cancel₀ hμne, one_mul]
    have hAvgd : ∀ s : ℂ, σ₃ < s.re →
        Zd s = ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          ∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂ :=
      fun s hs => (hAvgdI s hs).2
    have hIntB : ∀ s : ℂ, σ₃ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) => c₀ (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ :=
      fun s hs => (hAvgdI s hs).1

    set shell : ℤ → Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
      fun n => {g | Valued.v (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) =
        WithZero.exp (-n)} with hshell
    set A : ℤ → ℂ := fun n => ∫ g in shell n, c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂ with hA
    set B : ℤ → ℂ := fun n => ∫ g in shell n, c₀ (transposeInvN (Fin 2) g) *
        matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) ∂μ₂ with hB

    have hShell : ∃ S : Finset ℤ, (∀ n, n ∉ S → A n = 0) ∧ ∀ s : ℂ, σ₂ < s.re →
        (∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2) ∂μ₂) =
          ∑ n ∈ S, A n * q ^ (-(n : ℂ) * (s + 1 / 2)) :=

      ShellFin.hShell_main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp χ hχ hSC hLC μ₂ w hw Φ hΦlc hΦcs
        σ₂ hi Ω hΩo hΩc hΩΦ hΩχ hΩdet
    have hShelld : ∃ Sd : Finset ℤ, (∀ n, n ∉ Sd → B n = 0) ∧ ∀ s : ℂ, σ₃ < s.re →
        (∫ g : GL (Fin 2) (p.adicCompletion ℚ), c₀ (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2) ∂μ₂) =
          ∑ n ∈ Sd, B n * q ^ (-(n : ℂ) * (s + 3 / 2)) :=

      ShellFin.hShelld_main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral hcusp wJ χ hχ hSC hLC μ₂ w hw Φ hΦlc hΦcs
        σ₃ hiii Ω hΩo hΩc hΩΦ hΩχ hΩdet

    have hShellFE : ∀ n : ℤ, B n = E₀ * q ^ ((2 * (n : ℂ)) - (e₀ : ℂ) / 2) * A (e₀ - n) :=

      J3cFE.shellFE_main p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ E₀ e₀ hfe hcusp
        hSC hLC μ₂ w hw Φ hΦlc hΦcs Ω hΩo hΩc σ₂ σ₃ hIntA hIntB

    classical
    obtain ⟨S, hAS, hSsum⟩ := hShell
    obtain ⟨Sd, hBSd, hSdsum⟩ := hShelld
    have hq0 : q ≠ 0 := by
      rw [hq]; exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)).ne'
    have hqpow : ∀ a b : ℂ, q ^ a * q ^ b = q ^ (a + b) := fun a b => (Complex.cpow_add _ _ hq0).symm
    set μΩ : ℂ := (((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ))⁻¹ with hμΩ
    set cA : ℤ → ℂ := fun n => μΩ * A n * q ^ (-(n : ℂ) / 2) with hcA
    set cB : ℤ → ℂ := fun n => μΩ * B n * q ^ (-(3 * (n : ℂ)) / 2) with hcB

    have hZsum : ∀ s : ℂ, max σ₂ σa < s.re →
        q ^ ((m₁ : ℂ) * s) * P₁.eval (q ^ (-s)) = ∑ n ∈ S, cA n * q ^ (-(n : ℂ) * s) := by
      intro s hs
      rw [← hP₁ s (lt_of_le_of_lt (le_max_right _ _) hs), hAvg s (lt_of_le_of_lt (le_max_left _ _) hs),
        hSsum s (lt_of_le_of_lt (le_max_left _ _) hs), Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hcA, hμΩ]
      rw [mul_assoc, mul_assoc, hqpow]
      congr 2; ring
    have hZdsum : ∀ s : ℂ, max σ₃ σb < s.re →
        q ^ ((md₁ : ℂ) * s) * Pd₁.eval (q ^ (-s)) = ∑ n ∈ Sd, cB n * q ^ (-(n : ℂ) * s) := by
      intro s hs
      rw [← hPd₁ s (lt_of_le_of_lt (le_max_right _ _) hs), hAvgd s (lt_of_le_of_lt (le_max_left _ _) hs),
        hSdsum s (lt_of_le_of_lt (le_max_left _ _) hs), Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hcB, hμΩ]
      rw [mul_assoc, mul_assoc, hqpow]
      congr 2; ring
    obtain ⟨RA, MA, hRA⟩ := J3cKit.exists_poly_of_finset_sum (Ideal.absNorm p.asIdeal : ℝ) hq1 S cA
    obtain ⟨RB, MB, hRB⟩ := J3cKit.exists_poly_of_finset_sum (Ideal.absNorm p.asIdeal : ℝ) hq1 Sd cB
    have hZall : ∀ s : ℂ, q ^ ((m₁ : ℂ) * s) * P₁.eval (q ^ (-s)) = ∑ n ∈ S, cA n * q ^ (-(n : ℂ) * s) := by
      intro s
      have h1 := J3cKit.forall_cpow_mul_eval_eq_of_halfPlane (Ideal.absNorm p.asIdeal : ℝ) hq1 P₁ RA m₁ MA (max σ₂ σa)
        (fun s hs => by
          have h2 := hZsum s hs
          rw [hqR] at h2; rw [h2]; exact hRA s) s
      have h3 := hRA s
      rw [← hqR] at h1 h3
      rw [h1, ← h3]
    have hZdall : ∀ s : ℂ, q ^ ((md₁ : ℂ) * s) * Pd₁.eval (q ^ (-s)) = ∑ n ∈ Sd, cB n * q ^ (-(n : ℂ) * s) := by
      intro s
      have h1 := J3cKit.forall_cpow_mul_eval_eq_of_halfPlane (Ideal.absNorm p.asIdeal : ℝ) hq1 Pd₁ RB md₁ MB (max σ₃ σb)
        (fun s hs => by
          have h2 := hZdsum s hs
          rw [hqR] at h2; rw [h2]; exact hRB s) s
      have h3 := hRB s
      rw [← hqR] at h1 h3
      rw [h1, ← h3]

    have hcoef : ∀ n : ℤ, cB n = E₀ * cA (e₀ - n) := by
      intro n
      simp only [hcA, hcB, hShellFE n]
      push_cast
      rw [show μΩ * (E₀ * q ^ (2 * (n : ℂ) - (e₀ : ℂ) / 2) * A (e₀ - n)) * q ^ (-(3 * (n : ℂ)) / 2) =
          E₀ * (μΩ * A (e₀ - n)) * (q ^ (2 * (n : ℂ) - (e₀ : ℂ) / 2) * q ^ (-(3 * (n : ℂ)) / 2)) by ring, hqpow]
      rw [show (2 * (n : ℂ) - (e₀ : ℂ) / 2 + -(3 * (n : ℂ)) / 2) = (-((e₀ : ℂ) - (n : ℂ)) / 2) by ring]
      ring

    have hcA0 : ∀ n, n ∉ S → cA n = 0 := fun n hn => by simp only [hcA, hAS n hn]; ring
    have hcB0 : ∀ n, n ∉ Sd → cB n = 0 := fun n hn => by simp only [hcB, hBSd n hn]; ring
    intro s
    rw [hZdall s]
    have hneg := hZall (-s)
    simp only [neg_neg] at hneg
    rw [show q ^ ((m₁ : ℂ) * -s) * P₁.eval (q ^ (- -s)) = ∑ n ∈ S, cA n * q ^ (-(n : ℂ) * -s) by
      simpa only [neg_neg] using hneg]

    set T : Finset ℤ := Sd ∪ S.image (fun k => e₀ - k) with hT
    have hL1 : ∑ n ∈ Sd, cB n * q ^ (-(n : ℂ) * s) = ∑ n ∈ T, cB n * q ^ (-(n : ℂ) * s) := by
      apply Finset.sum_subset (Finset.subset_union_left)
      intro n _ hn; rw [hcB0 n hn, zero_mul]
    have hR1 : ∑ k ∈ S, cA k * q ^ (-(k : ℂ) * -s) = ∑ n ∈ S.image (fun k => e₀ - k), cA (e₀ - n) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s) := by
      rw [Finset.sum_image (fun a _ b _ (h : e₀ - a = e₀ - b) => by linarith)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [sub_sub_cancel]
    have hR2 : ∑ n ∈ S.image (fun k => e₀ - k), cA (e₀ - n) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s) =
        ∑ n ∈ T, cA (e₀ - n) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s) := by
      apply Finset.sum_subset (Finset.subset_union_right)
      intro n _ hn
      have : e₀ - n ∉ S := by
        intro hmem; apply hn; exact Finset.mem_image.2 ⟨e₀ - n, hmem, by ring⟩
      rw [hcA0 _ this, zero_mul]
    have hterm : ∀ n : ℤ, cB n * q ^ (-(n : ℂ) * s) =
        E₀ * q ^ (-(e₀ : ℂ) * s) * (cA (e₀ - n) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s)) := by
      intro n
      rw [hcoef n]
      have hx : q ^ (-(e₀ : ℂ) * s) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s) = q ^ (-(n : ℂ) * s) := by
        rw [hqpow]; congr 1; push_cast; ring
      calc E₀ * cA (e₀ - n) * q ^ (-(n : ℂ) * s)
          = E₀ * cA (e₀ - n) * (q ^ (-(e₀ : ℂ) * s) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s)) := by rw [hx]
        _ = E₀ * q ^ (-(e₀ : ℂ) * s) * (cA (e₀ - n) * q ^ (-((e₀ - n : ℤ) : ℂ) * -s)) := by ring
    rw [hL1, hR1, hR2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n

  have hR : ∀ s : ℂ, q ^ ((m : ℂ) * s) * P.eval (q ^ (-s)) = q ^ ((m₁ : ℂ) * s) * (P₁ * Q).eval (q ^ (-s)) := by
    have h0 : ∀ s : ℂ, max σ₂ σa < s.re →
        q ^ ((m : ℂ) * s) * P.eval (q ^ (-s)) = q ^ ((m₁ : ℂ) * s) * (P₁ * Q).eval (q ^ (-s)) := by
      intro s hs
      rw [Polynomial.eval_mul, ← mul_assoc, ← hP₁ s (lt_of_le_of_lt (le_max_right _ _) hs),
        ← hii s (lt_of_le_of_lt (le_max_left _ _) hs)]
    intro s
    have := J3cKit.forall_cpow_mul_eval_eq_of_halfPlane (Ideal.absNorm p.asIdeal : ℝ) hq1 P (P₁ * Q) m m₁ (max σ₂ σa)
      (fun s hs => by simpa only [hqR] using h0 s hs) s
    simpa only [hqR] using this
  have hRd : ∀ s : ℂ, q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s)) = q ^ ((md₁ : ℂ) * s) * (Pd₁ * Qd).eval (q ^ (-s)) := by
    have h0 : ∀ s : ℂ, max σ₃ σb < s.re →
        q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s)) = q ^ ((md₁ : ℂ) * s) * (Pd₁ * Qd).eval (q ^ (-s)) := by
      intro s hs
      rw [Polynomial.eval_mul, ← mul_assoc, ← hPd₁ s (lt_of_le_of_lt (le_max_right _ _) hs),
        ← hiv s (lt_of_le_of_lt (le_max_left _ _) hs)]
    intro s
    have := J3cKit.forall_cpow_mul_eval_eq_of_halfPlane (Ideal.absNorm p.asIdeal : ℝ) hq1 Pd (Pd₁ * Qd) md md₁ (max σ₃ σb)
      (fun s hs => by simpa only [hqR] using h0 s hs) s
    simpa only [hqR] using this

  intro s
  have hRneg := hR (-s)
  simp only [neg_neg, Polynomial.eval_mul] at hRneg
  rw [Polynomial.eval_one, Polynomial.eval_C, one_mul, hRd s, Polynomial.eval_mul, ← mul_assoc, hFE s]
  simp only [neg_neg]
  rw [show q ^ ((m : ℂ) * -s) * P.eval (q ^ s) = q ^ ((m₁ : ℂ) * -s) * (P₁.eval (q ^ s) * Q.eval (q ^ s)) from hRneg]
  push_cast
  ring

end
end S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_godementZeta2_whittaker_clearedFE_of_forall_torusZeta_fe_of_cuspidal (solution)
