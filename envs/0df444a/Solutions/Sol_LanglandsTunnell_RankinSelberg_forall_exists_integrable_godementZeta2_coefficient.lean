-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c20c26a2-3b71-55d2-be10-92e47290bfeb

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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
import Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_comp_inv_mul_eq
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option maxHeartbeats 1600000

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

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  rw [selfDualHaarAt_eq p]
  infer_instance

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

namespace GJWRed

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G2" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M22" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

theorem continuous_scalar : Continuous (fun z : Fˣ => (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)) := by
  have hval : ∀ z : Fˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22) = Matrix.diagonal (fun _ => (z : F)) :=
    fun z => rfl
  have hinv : ∀ z : Fˣ, (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22) = Matrix.diagonal (fun _ => ((z⁻¹ : Fˣ) : F)) :=
    fun z => by rw [← map_inv]; rfl
  rw [Units.continuous_iff]
  have e1 : (fun z : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22)) =
      fun z : Fˣ => Matrix.diagonal (fun _ : Fin 2 => (z : F)) := funext hval
  have e2 : (fun z : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22)) =
      fun z : Fˣ => Matrix.diagonal (fun _ : Fin 2 => ((z⁻¹ : Fˣ) : F)) := funext hinv
  refine ⟨?_, ?_⟩
  · show Continuous fun z : Fˣ => ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : M22)
    rw [e1]
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_val
    · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const
  · show Continuous fun z : Fˣ => (((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2)⁻¹ : G2) : M22)
    rw [e2]
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]; exact Units.continuous_val.comp continuous_inv
    · simp only [Matrix.diagonal_apply_ne _ h]; exact continuous_const

theorem isLocallyConstant_central (θ₀ : Fˣ →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : G2 → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G2, w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hcentral : ∀ (z : Fˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g) :
    IsLocallyConstant θ₀ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, w₂base g₀ ≠ 0 := by
    by_contra h; push Not at h; exact hw₂ne (funext h)

  have htriv : ∀ z : Fˣ, (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N → θ₀ z = 1 := by
    intro z hz
    have h1 := hcentral z g₀
    have hcomm : (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) * g₀ = g₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
      apply Units.ext
      show Matrix.diagonal (fun _ => (z : F)) * (g₀ : M22) = (g₀ : M22) * Matrix.diagonal (fun _ => (z : F))
      rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [hcomm, hw₂K _ hz] at h1
    have : ((θ₀ z : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hg₀ (h1.symm.trans (one_mul _).symm)
      exact this
    exact Units.val_eq_one.1 this
  have hopen : IsOpen {z : Fˣ | (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N} :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2.preimage (continuous_scalar p)
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z₀
  have hmem : z₀ ∈ (fun z => z₀⁻¹ * z) ⁻¹' {z : Fˣ | (Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N} := by
    simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel, map_one]; exact one_mem _
  filter_upwards [(hopen.preimage (continuous_const.mul continuous_id)).mem_nhds hmem] with z hz
  have h1 : θ₀ (z₀⁻¹ * z) = 1 := htriv (z₀⁻¹ * z) hz
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem measurePreserving_conj
    (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure G2) [μ₂.IsHaarMeasure], MeasurePreserving (fun g : G2 => wJ * g * wJ⁻¹) μ₂ μ₂ := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology M22 := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology M22ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := M22)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology G2 := Units.isEmbedding_embedProduct.secondCountableTopology
  intro μ₂ _
  have h4 : wJ⁻¹ ^ 4 = 1 := by
    rw [inv_pow, inv_eq_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hwJ, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hmod : Measure.modularCharacterFun (wJ⁻¹) = 1 := by
    have : (Measure.modularCharacter (G := G2)) wJ⁻¹ ^ 4 = 1 := by rw [← map_pow, h4, map_one]
    exact (pow_eq_one_iff_of_nonneg (by simp) (by norm_num)).1 this
  have hR : MeasurePreserving (fun g : G2 => g * wJ⁻¹) μ₂ μ₂ :=
    ⟨measurable_mul_const _, by rw [Measure.map_right_mul_eq_modularCharacterFun_smul, hmod, one_smul]⟩
  have hL : MeasurePreserving (fun g : G2 => wJ * g) μ₂ μ₂ := measurePreserving_mul_left μ₂ wJ
  have : (fun g : G2 => wJ * g * wJ⁻¹) = (fun g : G2 => g * wJ⁻¹) ∘ (fun g : G2 => wJ * g) := by
    funext g; rfl
  rw [this]
  exact hR.comp hL

theorem transposeInvN_conj (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) (h : G2) :
    transposeInvN (Fin 2) (wJ⁻¹ * h * wJ) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det h)⁻¹ * h := by
  have hwJdet : ((wJ : M22)).det = 1 := by rw [hwJ, Matrix.det_fin_two_of]; ring
  have hwJinv : ((wJ⁻¹ : G2) : M22) = !![0, -1; 1, 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, hwJdet, Ring.inverse_one, one_smul, hwJ]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hsc : ∀ u : Fˣ, ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : M22) = Matrix.diagonal (fun _ => (u : F)) := fun u => rfl
  apply Units.ext
  rw [coe_transposeInvN, Units.val_mul, hsc]
  have hinv : (((wJ⁻¹ * h * wJ)⁻¹ : G2) : M22) = ((wJ⁻¹ : G2) : M22) * ((h⁻¹ : G2) : M22) * (wJ : M22) := by
    rw [show (wJ⁻¹ * h * wJ)⁻¹ = wJ⁻¹ * h⁻¹ * wJ by group]; rfl
  have hhinv : ((h⁻¹ : G2) : M22) = (((Matrix.GeneralLinearGroup.det h)⁻¹ : Fˣ) : F) •
      !![(h : M22) 1 1, -(h : M22) 0 1; -(h : M22) 1 0, (h : M22) 0 0] := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply,
      Ring.inverse_unit (Matrix.GeneralLinearGroup.det h)]
  rw [hinv, hhinv, hwJ, hwJinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.diagonal]

theorem transposeInvN_eq (wJ : G2) (hwJ : (wJ : M22) = !![0, 1; -1, 0]) (g : G2) :
    transposeInvN (Fin 2) g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g)⁻¹ * (wJ * g * wJ⁻¹) := by
  have h := transposeInvN_conj p wJ hwJ (wJ * g * wJ⁻¹)
  have hdet : Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul]
  rwa [show wJ⁻¹ * (wJ * g * wJ⁻¹) * wJ = g by group, hdet] at h

theorem central_of_mem_span (θ₀ : Fˣ →* ℂˣ) (w₂base : G2 → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w : G2 → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h))) :
    ∀ (z : Fˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro z g
    show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = ((θ₀ z : ℂˣ) : ℂ) * w₂base (g * h)
    rw [mul_assoc, hcentral]
  | zero => intro z g; simp
  | add x y _ _ hx hy => intro z g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul c x _ hx => intro z g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

end GJWRed
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient.RCgB"

open GJJLGlue in

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

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    :

    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (ℓ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] ℂ),
          (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
            ∀ k ∈ U, ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
              ℓ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => v (g * k)) = ℓ v) →
          ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
            ∃ (σ₂ σ₃ : ℝ),

              (∀ s : ℂ, σ₂ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g)) * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂) ∧

              (∀ s : ℂ, σ₃ < s.re →
                Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) g)) *
                    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
                    ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂) := by
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  intro μ₂ _ w hw ℓ hℓ Φ hΦ hΦc
  classical
  obtain ⟨U, hUopen, hUinv⟩ := hℓ
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  obtain ⟨hSC, hLC, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI := hLC

  obtain ⟨W, hWopen, hW⟩ := exists_isOpen_subgroup_forall_apply_mul_eq p Φ hΦ hΦc
  obtain ⟨Ω, hΩo, hΩc, hΩU, hΩW, hΩdet⟩ := exists_compact_open_subgroup_le p U W hUopen hWopen χ hχ
  have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩo.measurableSet
  have hΩfin : μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ⊤ := hΩc.measure_lt_top

  obtain ⟨n, g, a, hGJA⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_mem_span_apply_eq_sum_mul_setIntegral_translate_of_invariant_of_admissible
      p N hN w₂base hw₂K hw₂adm μ₂ Ω hΩo hΩc ℓ (fun k hk v hv => hUinv k (hΩU hk) v hv)

  have hc : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      ℓ (fun x => w (x * h)) = ∑ i, a i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g i * k * h) ∂μ₂ := by
    intro h
    rw [hGJA _ (comp_mul_mem_span w₂base hw h)]
    try simp only [mul_assoc]

  set Φi : Fin n → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun i X => Φ ((((g i)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X) with hΦi
  have hΦi_sb : ∀ i, IsLocallyConstant (Φi i) ∧ HasCompactSupport (Φi i) := fun i =>
    isLocallyConstant_and_hasCompactSupport_comp_mul p Φ hΦ hΦc (g i)⁻¹

  have hInt := fun i =>
    LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift
      p θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w hw (Φi i) (hΦi_sb i).1 (hΦi_sb i).2 (1 / 2)
  choose σ₂i hR1 using hInt

  set wJ : GL (Fin 2) (p.adicCompletion ℚ) := Matrix.GeneralLinearGroup.mkOfDetNeZero (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    (by rw [Matrix.det_fin_two_of]; norm_num) with hwJdef
  have hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0] := by rw [hwJdef]; rfl

  have hψ0 : ∀ x : (p.adicCompletion ℚ), Valued.v x ≤ WithZero.exp (0 : ℤ) → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    intro x hx
    apply LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]; exact hx
  have hψ1 : ∃ x : (p.adicCompletion ℚ), Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ NumberField.StandardAddChar.psiLocal ℚ p x ≠ 1 := by
    have h := (LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p
      (NumberField.StandardAddChar.psiLocal ℚ p) ⟨0, hψ0⟩ (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)).2
    rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat] at h
  have hθ : IsLocallyConstant θ₀ := GJWRed.isLocallyConstant_central p θ₀ N hN w₂base hw₂K hw₂ne hcentral
  have hcw : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g :=
    GJWRed.central_of_mem_span p θ₀ w₂base hcentral w hw
  have hχ' : IsLocallyConstant (θ₀⁻¹ * χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    have : ((θ₀⁻¹ * χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun z => (θ₀ z)⁻¹ * (χ z)⁻¹ := by
      funext z; rfl
    rw [this]
    exact (hθ.inv).mul hχ.inv

  have hIntD : ∀ i : Fin n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        w (transposeInvN (Fin 2) g) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i) (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ := by
    intro i
    set Φh : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i) with hΦh
    have hΦhSB : IsSchwartzBruhat Φh :=
      LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 hψ0 hψ1 (Φi i) ⟨(hΦi_sb i).1, (hΦi_sb i).2⟩
    set cj : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) :=
      fun X => ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X * (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) with hcj
    have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    set Φ' : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ := fun X => Φh (cj X) with hΦ'
    have hΦ'lc : IsLocallyConstant Φ' := hΦhSB.1.comp_continuous hcjc
    have hΦ'cs : HasCompactSupport Φ' := by
      refine HasCompactSupport.intro (hΦhSB.2.image (show Continuous (fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X * ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) from
        (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)) fun X hX => ?_
      show Φh (cj X) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hmem; apply hX
      refine ⟨cj X, hmem, ?_⟩
      show (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * X *
        (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) * ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = X
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    obtain ⟨σd, hId⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral (θ₀⁻¹ * χ⁻¹) hχ' μ₂ w hw Φ' hΦ'lc hΦ'cs (3 / 2)
    refine ⟨σd, fun s hs => ?_⟩
    have hF := hId s hs
    have hc := GJWRed.measurePreserving_conj p wJ hwJ μ₂
    have key : (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        w (transposeInvN (Fin 2) g) * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i) (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) =
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          w h * Φ' (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * (((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)) ∘
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => wJ * g * wJ⁻¹) := by
      funext g
      show _ = w (wJ * g * wJ⁻¹) * Φh (cj ((wJ * g * wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
        (((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹)) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) ^ (s + 3 / 2)
      simp only [hcj, hΦh]
      have hdet : Matrix.GeneralLinearGroup.det (wJ * g * wJ⁻¹) = Matrix.GeneralLinearGroup.det g := by
        rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (Matrix.GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul]
      have hconj : ((wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((wJ * g * wJ⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
        rw [← Units.val_mul, ← Units.val_mul, show wJ⁻¹ * (wJ * g * wJ⁻¹) * wJ = g by group]
      rw [hdet, hconj, GJWRed.transposeInvN_eq p wJ hwJ g, hcw, map_inv]
      have hθχ : ((((θ₀⁻¹ * χ⁻¹) (Matrix.GeneralLinearGroup.det g)) : ℂˣ) : ℂ) =
          (((θ₀ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      rw [hθχ]; ring
    rw [key]
    exact (hc.integrable_comp hF.aestronglyMeasurable).mpr hF
  choose σ₃i hR3 using hIntD

  have hwlc : IsLocallyConstant w := isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw
  have hwc : Continuous w := hwlc.continuous
  have hχc := continuous_chi_det p χ hχ
  have hΦic : ∀ i, Continuous (Φi i) := fun i => (hΦi_sb i).1.continuous

  set dI : Fin n → ℝ := fun i =>
    ((modulus ((Matrix.GeneralLinearGroup.det (g i) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0) : ℝ) with hdI
  have hdI_pos : ∀ i, 0 < dI i := fun i => by
    rw [hdI]; exact modulus_pos' p (Units.ne_zero _)
  have hχne : ∀ i, ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ) ≠ 0 := fun i => Units.ne_zero _

  set FF : Fin n → ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i s h =>
    w h * Φi i ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
      ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s with hFF
  have hFFm : ∀ i s, Measurable (FF i s) := by
    intro i s
    rw [hFF]
    exact (((hwc.mul ((hΦic i).comp Units.continuous_val)).mul hχc).mul (continuous_modulus_det_cpow p s)).measurable

  have hP1 : ∀ (s : ℂ) (i : Fin n), ∀ k ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      w (g i * k * h) *
        (Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) =
      ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (-s)) * FF i s (g i * k * h) := by
    intro s i k hk h
    have hkW : Φ (((k : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) =
        Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := hW k (hΩW hk) _
    obtain ⟨hχk, hmk⟩ := hΩdet k hk
    have hΦi_val : Φi i ((g i * k * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
        Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
      rw [hΦi]
      simp only [Units.val_mul, mul_assoc]
      rw [← mul_assoc (((g i)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)),
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact hkW
    have hχ_val : ((χ (Matrix.GeneralLinearGroup.det (g i * k * h)) : ℂˣ) : ℂ) =
        ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) := by
      rw [map_mul, map_mul, map_mul, map_mul, Units.val_mul, Units.val_mul, hχk, mul_one]
    have hmod_val : ((modulus ((Matrix.GeneralLinearGroup.det (g i * k * h) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s =
        ((dI i : ℝ) : ℂ) ^ s *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, modulus_mul', modulus_mul', hmk, mul_one, NNReal.coe_mul,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), hdI]
    rw [hFF]
    simp only
    rw [hΦi_val, hχ_val, hmod_val]
    have h1 : ((dI i : ℝ) : ℂ) ^ (-s) * ((dI i : ℝ) : ℂ) ^ s = 1 := by
      rw [Complex.cpow_neg, inv_mul_cancel₀ (cpow_ne_zero'' (by exact_mod_cast (hdI_pos i).ne') s)]
    have h2 : (((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ) = 1 :=
      inv_mul_cancel₀ (hχne i)

    calc _ = w (g i * k * h) * Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ)) *
          (((dI i : ℝ) : ℂ) ^ (-s) * ((dI i : ℝ) : ℂ) ^ s) := by rw [h1, h2, mul_one, mul_one]; ring
      _ = _ := by ring

  have hPrimal : ∀ s : ℂ, (∀ i, σ₂i i < s.re) →
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * h)) *
          Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 1 / 2)) μ₂ ∧
      godementZeta2 p μ₂ (fun h : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * h))) Φ χ (s + 1 / 2) =
        ∑ i, (a i * ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (-(s + 1 / 2)))) *
          godementZeta2 p μ₂ w (Φi i) χ (s + 1 / 2) := by
    intro s hs
    set S : ℂ := s + 1 / 2 with hS

    have hL := fun i => integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) hΩm hΩfin
      (FF i S) (hFFm i S) (by rw [hFF]; exact hR1 i s (hs i)) (fun k => g i * k)
      (continuous_const.mul continuous_id)

    have hL' : ∀ i, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), FF i S (g i * k * h) ∂μ₂) μ₂ ∧
        ∫ h, (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), FF i S (g i * k * h) ∂μ₂) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∫ h, FF i S h ∂μ₂ := fun i => hL i

    set C : Fin n → ℂ := fun i =>
      a i * ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (-S)) with hC
    have hI : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * h)) *
          Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S =
        ∑ i, C i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), FF i S (g i * k * h) ∂μ₂ := by
      intro h
      rw [hc h, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hin : (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g i * k * h) ∂μ₂) *
            (Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S) =
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (-S)) *
            ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), FF i S (g i * k * h) ∂μ₂ := by
        rw [← integral_mul_const, ← integral_const_mul]
        exact setIntegral_congr_fun hΩm fun k hk => hP1 S i k hk h
      rw [hC]
      calc _ = a i * ((∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g i * k * h) ∂μ₂) *
            (Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S)) := by ring
        _ = _ := by rw [hin]; ring
    have hIfun : (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * h)) *
          Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S) =
        fun h => ∑ i, C i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), FF i S (g i * k * h) ∂μ₂ := funext hI
    refine ⟨?_, ?_⟩
    · rw [hIfun]
      exact integrable_finsetSum _ fun i _ => (hL' i).1.const_mul _
    · rw [godementZeta2_apply]
      show (∫ h, ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * h)) *
          Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S ∂μ₂) = _
      rw [hIfun, integral_finsetSum _ (fun i _ => (hL' i).1.const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, (hL' i).2, godementZeta2_apply, hC, hFF]
      ring

  have hχinv_lc : IsLocallyConstant (χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) := by
    have : ((χ⁻¹ : (p.adicCompletion ℚ)ˣ →* ℂˣ) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun u => (χ u)⁻¹ := by
      funext u; rfl
    rw [this]; exact hχ.inv
  have hχic := continuous_chi_det p χ⁻¹ hχinv_lc
  have hFΦi : ∀ i, IsSchwartzBruhat (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i)) := fun i => by
    obtain ⟨h1, h2⟩ := E3ReduceSupplyF.level_zero p
    exact LanglandsTunnell.CubicInduction.isSchwartzBruhat_matFourier22 p _ 0 h1 h2 (Φi i) ⟨(hΦi_sb i).1, (hΦi_sb i).2⟩
  have hwιc : Continuous fun h : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) h) :=
    hwc.comp (E3ReduceSupply.continuous_transposeInvN p)

  set GG : Fin n → ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun i s h =>
    w (transposeInvN (Fin 2) h) *
      matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i) ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
      ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s with hGG
  have hGGm : ∀ i s, Measurable (GG i s) := by
    intro i s
    rw [hGG]
    exact (((hwιc.mul ((hFΦi i).1.continuous.comp Units.continuous_val)).mul hχic).mul (continuous_modulus_det_cpow p s)).measurable

  have hdetι : ∀ x : GL (Fin 2) (p.adicCompletion ℚ),
      Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) x) = (Matrix.GeneralLinearGroup.det x)⁻¹ := by
    intro x
    rw [← map_inv]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_transposeInvN, Matrix.det_transpose]

  have hD1 : ∀ (s : ℂ) (i : Fin n), ∀ k ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
      w (g i * k * transposeInvN (Fin 2) h) *
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s) =
      ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (s - 2)) *
        GG i s (transposeInvN (Fin 2) (g i * k) * h) := by
    intro s i k hk h
    obtain ⟨hχk, hmk⟩ := hΩdet k hk

    have harg : transposeInvN (Fin 2) (transposeInvN (Fin 2) (g i * k) * h) = g i * k * transposeInvN (Fin 2) h := by
      rw [transposeInvN_mul, transposeInvN_transposeInvN]

    have hfun : (fun Y : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        Φ ((((g i * k)⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Y)) = Φi i := by
      funext Y
      rw [hΦi]
      simp only
      rw [mul_inv_rev, Units.val_mul, mul_assoc]
      exact hW k⁻¹ (inv_mem (hΩW hk)) _
    have hcov := LanglandsTunnell.CubicInduction.matFourier22_comp_inv_mul_eq p (NumberField.StandardAddChar.psiLocal ℚ p) (g i * k) Φ
      ((transposeInvN (Fin 2) (g i * k) * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
    rw [hfun] at hcov
    have hX : Matrix.transpose (((g i * k : GL (Fin 2) (p.adicCompletion ℚ))) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
        ((transposeInvN (Fin 2) (g i * k) * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
        ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
      rw [Units.val_mul (transposeInvN (Fin 2) (g i * k)) h, coe_transposeInvN, ← mul_assoc, ← Matrix.transpose_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, one_mul]
    rw [hX] at hcov
    have hmodgk : ((modulus ((Matrix.GeneralLinearGroup.det (g i * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) =
        ((dI i : ℝ) : ℂ) := by
      rw [map_mul, Units.val_mul, modulus_mul', hmk, mul_one, hdI]
    rw [hmodgk] at hcov

    have hdIne : ((dI i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hdI_pos i).ne'
    have hFval : matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) =
        (((dI i : ℝ) : ℂ) ^ (2 : ℕ))⁻¹ *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i)
            ((transposeInvN (Fin 2) (g i * k) * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) := by
      rw [hcov, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdIne), one_mul]

    have hdet_val : Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) (g i * k) * h) =
        (Matrix.GeneralLinearGroup.det (g i))⁻¹ * (Matrix.GeneralLinearGroup.det k)⁻¹ * Matrix.GeneralLinearGroup.det h := by
      rw [map_mul, hdetι, map_mul, mul_inv]
    have hχ_val : ((χ⁻¹ (Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) (g i * k) * h)) : ℂˣ) : ℂ) =
        ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ) * ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) := by
      rw [hdet_val]
      simp [MonoidHom.inv_apply, map_mul, map_inv, mul_inv, Units.val_mul, hχk]
    have hmod_val : ((modulus ((Matrix.GeneralLinearGroup.det (transposeInvN (Fin 2) (g i * k) * h) : (p.adicCompletion ℚ)ˣ) :
          p.adicCompletion ℚ) : ℝ) : ℂ) ^ s =
        (((dI i : ℝ) : ℂ) ^ s)⁻¹ *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s := by
      rw [hdet_val, Units.val_mul, Units.val_mul, modulus_mul', modulus_mul']
      have hmkinv : modulus (((Matrix.GeneralLinearGroup.det k)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
        have := modulus_mul' p ((Matrix.GeneralLinearGroup.det k : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
          (((Matrix.GeneralLinearGroup.det k)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, hmk, one_mul] at this
        rw [← this, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_one]
      have hginv : (((modulus (((Matrix.GeneralLinearGroup.det (g i))⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0) : ℝ) : ℂ) =
          (((dI i : ℝ) : ℂ))⁻¹ := by
        have := modulus_mul' p ((Matrix.GeneralLinearGroup.det (g i) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
          (((Matrix.GeneralLinearGroup.det (g i))⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, nnnorm_one] at this
        have hm : modulus (((Matrix.GeneralLinearGroup.det (g i))⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) =
            (modulus ((Matrix.GeneralLinearGroup.det (g i) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ))⁻¹ :=
          eq_inv_of_mul_eq_one_right this.symm
        simp only [hdI, hm, NNReal.coe_inv, Complex.ofReal_inv]
      rw [hmkinv, mul_one, NNReal.coe_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
        hginv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (hdI_pos i).le]; exact Real.pi_ne_zero.symm)]
    rw [hGG]
    simp only
    rw [harg, hFval, hχ_val, hmod_val]
    have h2 : (((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ) = 1 :=
      inv_mul_cancel₀ (hχne i)
    have h3 : ((dI i : ℝ) : ℂ) ^ (s - 2) = ((dI i : ℝ) : ℂ) ^ s * (((dI i : ℝ) : ℂ) ^ (2 : ℕ))⁻¹ := by
      rw [Complex.cpow_sub _ _ hdIne, div_eq_mul_inv]
      congr 1
      norm_cast
    have h4 : ((dI i : ℝ) : ℂ) ^ s * (((dI i : ℝ) : ℂ) ^ s)⁻¹ = 1 := mul_inv_cancel₀ (cpow_ne_zero'' hdIne s)
    rw [h3]
    calc _ = w (g i * k * transposeInvN (Fin 2) h) *
          ((((dI i : ℝ) : ℂ) ^ (2 : ℕ))⁻¹ * matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i)
            ((transposeInvN (Fin 2) (g i * k) * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ s *
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ)) *
          (((dI i : ℝ) : ℂ) ^ s * (((dI i : ℝ) : ℂ) ^ s)⁻¹) := by rw [h2, h4, mul_one, mul_one]; ring
      _ = _ := by ring

  have hDual : ∀ s : ℂ, (∀ i, σ₃i i < s.re) →
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) h)) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ ∧
      godementZeta2 p μ₂ (fun h : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) h)))
          (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) χ⁻¹ (s + 3 / 2) =
        ∑ i, (a i * ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ ((s + 3 / 2) - 2))) *
          godementZeta2 p μ₂ (fun h : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) h))
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (Φi i)) χ⁻¹ (s + 3 / 2) := by
    intro s hs
    set S : ℂ := s + 3 / 2 with hS
    have hL := fun i => integrable_and_integral_setIntegral_translate' μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) hΩm hΩfin
      (GG i S) (hGGm i S) (by rw [hGG]; exact hR3 i s (hs i)) (fun k => transposeInvN (Fin 2) (g i * k))
      ((E3ReduceSupply.continuous_transposeInvN p).comp (continuous_const.mul continuous_id))
    have hL' : ∀ i, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), GG i S (transposeInvN (Fin 2) (g i * k) * h) ∂μ₂) μ₂ ∧
        ∫ h, (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), GG i S (transposeInvN (Fin 2) (g i * k) * h) ∂μ₂) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∫ h, GG i S h ∂μ₂ := fun i => hL i
    set C : Fin n → ℂ := fun i =>
      a i * ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (S - 2)) with hC
    have hI : ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) h)) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S =
        ∑ i, C i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), GG i S (transposeInvN (Fin 2) (g i * k) * h) ∂μ₂ := by
      intro h
      rw [hc (transposeInvN (Fin 2) h), Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hin : (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g i * k * transposeInvN (Fin 2) h) ∂μ₂) *
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S) =
          ((((χ (Matrix.GeneralLinearGroup.det (g i)) : ℂˣ) : ℂ))⁻¹ * ((dI i : ℝ) : ℂ) ^ (S - 2)) *
            ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), GG i S (transposeInvN (Fin 2) (g i * k) * h) ∂μ₂ := by
        rw [← integral_mul_const, ← integral_const_mul]
        exact setIntegral_congr_fun hΩm fun k hk => hD1 S i k hk h
      rw [hC]
      calc _ = a i * ((∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g i * k * transposeInvN (Fin 2) h) ∂μ₂) *
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S)) := by ring
        _ = _ := by rw [hin]; ring
    have hIfun : (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
        ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) h)) *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S) =
        fun h => ∑ i, C i * ∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), GG i S (transposeInvN (Fin 2) (g i * k) * h) ∂μ₂ :=
      funext hI
    refine ⟨?_, ?_⟩
    · rw [hIfun]
      exact integrable_finsetSum _ fun i _ => (hL' i).1.const_mul _
    · rw [godementZeta2_apply]
      show (∫ h, (fun h : GL (Fin 2) (p.adicCompletion ℚ) => ℓ (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * transposeInvN (Fin 2) h))) h *
          matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ (h : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          ((χ⁻¹ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ S ∂μ₂) = _
      simp only
      rw [hIfun, integral_finsetSum _ (fun i _ => (hL' i).1.const_mul _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, (hL' i).2, godementZeta2_apply, hC, hGG]
      ring

  have hσ₂ : ∀ s : ℂ, (∑ j, |σ₂i j|) < s.re → ∀ i, σ₂i i < s.re := fun s hs i =>
    lt_of_le_of_lt ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₂i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) hs
  have hσ₃ : ∀ s : ℂ, (∑ j, |σ₃i j|) < s.re → ∀ i, σ₃i i < s.re := fun s hs i =>
    lt_of_le_of_lt ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₃i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) hs
  exact ⟨∑ j, |σ₂i j|, ∑ j, |σ₃i j|, fun s hs => (hPrimal s (hσ₂ s hs)).1, fun s hs => (hDual s (hσ₃ s hs)).1⟩

end
end S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_coefficient (solution)
