-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0a457bb0-aaee-5661-8a28-a46ca087b250

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Mathlib.Analysis.Matrix.Normed
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_exists_integrable_godementZeta2_whittaker_shift
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors ENNReal NNReal
open NumberField.AdelicLevel (diagOne)

open scoped Classical

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

private def _root_.E3ReduceSupply.X (g : G2) : LocalGL3 p := longWeyl3 * transposeInv3 (iotaGL g) * longWeyl3

p2m_export "E3ReduceSupply" "X"
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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

namespace KEBody

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem measurable_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.mul measurable_const).mul
        (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

theorem measurable_density [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

end Density
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem unipotent_eq_unipotentGL2 (x : F) : (unipotent x : G2) = unipotentGL2 x :=
  Units.ext rfl

theorem unipotentGL2_neg_eq_inv (x : F) : (unipotentGL2 (-x) : G2) = (unipotentGL2 x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem continuous_unipotentGL2 : Continuous fun x : F => (unipotentGL2 x : G2) := by
  have hval : Continuous fun x : F => ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) F) := by
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j
    · simp only [unipotentGL2_coe, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [unipotentGL2_coe, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero]
      exact continuous_id
    · simp only [unipotentGL2_coe, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      exact continuous_const
    · simp only [unipotentGL2_coe, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact continuous_const
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun x : F => (((unipotentGL2 x : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) F)) =
      (fun x : F => ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) F)) ∘ (fun x : F => -x) := by
    funext x
    simp only [Function.comp_apply]
    rw [unipotentGL2_neg_eq_inv]
  rw [this]
  exact hval.comp continuous_neg

def φN (x : F) : ↥(unipotentGL2Hom (R := F)).range :=
  ⟨unipotentGL2 (-x), ⟨Multiplicative.ofAdd (-x), rfl⟩⟩

theorem coe_φN (x : F) : ((φN p x : ↥(unipotentGL2Hom (R := F)).range) : G2) = unipotentGL2 (-x) := rfl

theorem continuous_φN : Continuous (φN p) :=
  Continuous.subtype_mk ((continuous_unipotentGL2 p).comp continuous_neg) _

def ψN (n : ↥(unipotentGL2Hom (R := F)).range) : F := -(((n : G2) : Matrix (Fin 2) (Fin 2) F) 0 1)

theorem continuous_ψN : Continuous (ψN p) :=
  ((Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) 0 1)).neg

theorem ψN_φN (x : F) : ψN p (φN p x) = x := by
  simp [ψN, coe_φN, unipotentGL2_coe]

theorem φN_ψN (n : ↥(unipotentGL2Hom (R := F)).range) : φN p (ψN p n) = n := by
  obtain ⟨g, ⟨z, hz⟩⟩ := n
  apply Subtype.ext
  simp only [coe_φN, ψN]
  rw [← hz]
  change unipotentGL2 (-(-(((unipotentGL2 (Multiplicative.toAdd z) : G2) : Matrix (Fin 2) (Fin 2) F) 0 1))) =
    unipotentGL2 (Multiplicative.toAdd z)
  rw [neg_neg, unipotentGL2_coe]
  simp

theorem φN_surjective : Function.Surjective (φN p) := fun n => ⟨ψN p n, φN_ψN p n⟩

theorem mul_φN (a x : F) : φN p a * φN p x = φN p (x + a) := by
  apply Subtype.ext
  change unipotentGL2 (-a) * unipotentGL2 (-x) = unipotentGL2 (-(x + a))
  rw [← unipotentGL2_add]; congr 1; ring

theorem preimage_φN_eq_image_ψN (S : Set ↥(unipotentGL2Hom (R := F)).range) : φN p ⁻¹' S = ψN p '' S := by
  ext x
  constructor
  · intro hx; exact ⟨φN p x, hx, ψN_φN p x⟩
  · rintro ⟨n, hn, rfl⟩; show φN p (ψN p n) ∈ S; rw [φN_ψN]; exact hn

end KEBody
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

namespace PSB

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

theorem whittaker_of_mem_span (w₂base : G2 → ℂ)
    (hw₂law : ∀ (x : F) (g : G2), w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    {w : G2 → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h))) :
    ∀ (x : F) (g : G2), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h', rfl⟩ := hy
    intro x g
    show w₂base (unipotent x * g * h') = _ * w₂base (g * h')
    rw [mul_assoc, hw₂law]
  | zero => intro x g; simp
  | add a b _ _ ha hb => intro x g; simp only [Pi.add_apply, ha, hb, mul_add]
  | smul c a _ ha => intro x g; simp only [Pi.smul_apply, smul_eq_mul, ha]; ring

theorem exists_uniformizer : ∃ ϖ : p.adicCompletionIntegers ℚ,
    algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hv : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) p π
    have h2 : p.valuation ℚ (π : ℚ) = WithZero.exp (-1 : ℤ) := by
      rw [show (π : ℚ) = algebraMap (𝓞 ℚ) ℚ π from rfl, HeightOneSpectrum.valuation_of_algebraMap]; exact hπ
    first
      | (rw [h1]; exact h2)
      | (simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
           Valued.valuedCompletion_apply, HeightOneSpectrum.adicValued_apply] at h1 ⊢
         first | exact h2 | (rw [h1]; exact h2) | simpa using h2)
  have hmem : ((π : 𝓞 ℚ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · intro h0
    have : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 := by
      rw [show ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 from h0, map_zero]
    rw [hv] at this
    exact WithZero.coe_ne_zero this
  · exact hv

theorem exists_laurent_of_sum_monomials {ι : Type*} (S : Finset ι) (β : ι → ℂ) (k : ι → ℤ) (Nc : ℂ) (hN : Nc ≠ 0) :
    ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ,
      ∑ i ∈ S, β i * Nc ^ ((k i : ℂ) * s) = Nc ^ ((m : ℂ) * s) * P.eval (Nc ^ (-s)) := by
  classical
  set M : ℤ := ∑ j ∈ S, |k j| with hM
  have hMi : ∀ i ∈ S, k i ≤ M := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |k j|) (fun j _ => abs_nonneg _) hi)
  refine ⟨∑ i ∈ S, Polynomial.C (β i) * Polynomial.X ^ (M - k i).toNat, M, fun s => ?_⟩
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Complex.cpow_nat_mul]
  have hd : (((M - k i).toNat : ℕ) : ℂ) = (M : ℂ) - (k i : ℂ) := by
    have := Int.toNat_of_nonneg (show 0 ≤ M - k i by linarith [hMi i hi])
    exact_mod_cast this
  rw [hd]
  have : Nc ^ ((M : ℂ) * s) * (β i * Nc ^ (((M : ℂ) - (k i : ℂ)) * (-s))) = β i * (Nc ^ ((M : ℂ) * s) * Nc ^ (((M : ℂ) - (k i : ℂ)) * (-s))) := by
    ring
  rw [this, ← Complex.cpow_add _ _ hN]
  congr 2
  ring

end PSB
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent.RCgB"

open PSB KEBody in

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

    (htorus : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₀ : ℝ),
        ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))
    :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∀ (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
        ∀ s₀ : ℂ,
          ∃ (P : Polynomial ℂ) (m : ℤ) (σ : ℝ),
            ∀ s : ℂ, σ < s.re →
              godementZeta2 p μ₂ w Φ χ (s + s₀) =
                (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI iGL : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI iBGL : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ w hw Φ hΦ hΦc s₀
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  obtain ⟨hSC, hLC, hNcl, hNri⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hSC
  haveI := hLC
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3ReduceSupplyF.isAddHaarMeasure_selfDualHaarAt p

  obtain ⟨ϖ, hπ, hϖ⟩ := exists_uniformizer p
  set wJ : GL (Fin 2) (p.adicCompletion ℚ) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))
      (by rw [Matrix.det_fin_two_of]; norm_num) with hwJdef
  have hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0] := rfl

  have hwlc : IsLocallyConstant w := isLocallyConstant_of_mem_span p N hN w₂base hw₂K hw
  have hwc : Continuous w := hwlc.continuous
  have hwlaw := whittaker_of_mem_span p w₂base hw₂law hw

  obtain ⟨σb, hI⟩ := LanglandsTunnell.RankinSelberg.forall_exists_integrable_godementZeta2_whittaker_shift p θ₀ N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral χ hχ μ₂ w hw Φ hΦ hΦc s₀
  obtain ⟨-, ⟨UB, hUBo, hUB⟩, ⟨cP, MP, CP, hprof⟩⟩ :=
    LanglandsTunnell.RankinSelberg.exists_rowSlice_shell_profile_of_isLocallyConstant_of_hasCompactSupport p hπ hϖ Φ hΦ hΦc
  obtain ⟨nstar, cS, hSVD⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le p θ₀ N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ χ hχ htorus hπ hϖ μ₂ w hw Φ hΦ hΦc

  set B : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
    ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
      Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) ∂(selfDualHaarAt ℚ p) with hB
  have hBlc : IsLocallyConstant B := by
    refine isLocallyConstant_of_rightInvariant B UB hUBo fun k hk g => ?_
    rw [hB]; exact hUB k hk g
  have hχc : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
    have hdet : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) := by
      rw [Units.continuous_iff]
      constructor
      · show Continuous (Units.val ∘ fun g : GL (Fin 2) (p.adicCompletion ℚ) => Matrix.GeneralLinearGroup.det g)
        have : (Units.val ∘ fun g : GL (Fin 2) (p.adicCompletion ℚ) => Matrix.GeneralLinearGroup.det g) =
            fun g => ((g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det := by
          funext g; simp [Matrix.GeneralLinearGroup.val_det_apply]
        rw [this]; exact continuous_id.matrix_det.comp Units.continuous_val
      · show Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)
        have : (fun g : GL (Fin 2) (p.adicCompletion ℚ) => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) =
            fun g => (((g⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))).det := by
          funext g; rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [this]; exact continuous_id.matrix_det.comp (Units.continuous_val.comp continuous_inv)
    exact Units.continuous_val.comp (hχ.continuous.comp hdet)
  have hmodc : ∀ e : ℂ, Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ e := fun e =>
    (Complex.continuous_ofReal.comp (E3ReduceSupply.continuous_modulus_det p)).cpow continuous_const
      (fun g => Or.inl (by simpa only [Function.comp_apply, Complex.ofReal_re] using E3ReduceSupply.modulus_det_pos p g))

  have hφm : Measurable (φN p) := (continuous_φN p).measurable
  set μN : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range := Measure.map (φN p) (selfDualHaarAt ℚ p) with hμN
  haveI hμN1 : μN.IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    obtain ⟨a, rfl⟩ := φN_surjective p n
    rw [hμN, Measure.map_map (measurable_const_mul _) hφm]
    have : (fun x => φN p a * x) ∘ φN p = φN p ∘ fun x => x + a := by
      funext x; simp only [Function.comp_apply, mul_φN]
    rw [this, ← Measure.map_map hφm (measurable_add_const a), map_add_right_eq_self]
  haveI hμN2 : IsFiniteMeasureOnCompacts μN := by
    refine ⟨fun K hK => ?_⟩
    rw [hμN, Measure.map_apply hφm hK.measurableSet, preimage_φN_eq_image_ψN]
    exact (hK.image (continuous_ψN p)).measure_lt_top
  haveI hμN3 : μN.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hμN, Measure.map_apply hφm hU.measurableSet]
    refine (hU.preimage (continuous_φN p)).measure_ne_zero _ ?_
    obtain ⟨n, hn⟩ := hne
    obtain ⟨x, rfl⟩ := φN_surjective p n
    exact ⟨x, hn⟩
  haveI hμNH : μN.IsHaarMeasure := {}
  haveI : μN.IsMulRightInvariant := hNri μN
  set ρ := HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN with hρ
  have hρm : Measurable ρ := by rw [hρ]; exact measurable_density _ μN
  have hone : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      ∫⁻ x : p.adicCompletion ℚ, ρ (unipotentGL2 (-x) * g) ∂(selfDualHaarAt ℚ p) = 1 := by
    intro g
    have h : ∫⁻ n : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ρ ((n : GL (Fin 2) (p.adicCompletion ℚ)) * g) ∂μN = 1 := by
      rw [hρ]; exact HaarQuotient.lintegral_density_mul_eq_one _ hNcl μN g
    have hm : Measurable fun n : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range => ρ ((n : GL (Fin 2) (p.adicCompletion ℚ)) * g) :=
      hρm.comp ((continuous_subtype_val.mul continuous_const).measurable)
    rw [hμN, lintegral_map hm hφm] at h
    exact h

  obtain ⟨κ, hκ, hR1⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_godementZeta2_eq_mul_rsLocalIntegral_rowSlice p μ₂ μN

  set Fe : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun e g =>
    (B g * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) * w g *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ e with hFe
  have hFem : ∀ e, Measurable (Fe e) := fun e => by
    rw [hFe]; exact (((hBlc.continuous.mul hχc).mul hwc).mul (hmodc e)).measurable

  have hBN : ∀ (y : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      B (unipotent y * g) = NumberField.StandardAddChar.psiLocal ℚ p (-y) * B g := by
    intro y g
    rw [hB]
    simp only
    have : ∀ x : p.adicCompletion ℚ, (unipotent x * (unipotent y * g) : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent (x + y) * g := by
      intro x; rw [← mul_assoc, unipotent_eq_unipotentGL2, unipotent_eq_unipotentGL2, unipotent_eq_unipotentGL2, unipotentGL2_add]
    simp_rw [this]
    have htr := integral_add_right_eq_self (μ := selfDualHaarAt ℚ p)
      (fun x => NumberField.StandardAddChar.psiLocal ℚ p (x - y) *
        Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) y
    simp only [add_sub_cancel_right] at htr
    rw [htr, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x - y = -y + x by ring, AddChar.map_add_eq_mul]
    ring
  have hFeN : ∀ e, ∀ n ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      Fe e (n * g) = Fe e g := by
    rintro e n ⟨z, rfl⟩ g
    have hn : (unipotentGL2Hom z : GL (Fin 2) (p.adicCompletion ℚ)) = unipotent (Multiplicative.toAdd z) := by
      rw [unipotent_eq_unipotentGL2]; rfl
    rw [hFe]
    simp only
    rw [hn, hBN, hwlaw, map_mul, Matrix.GeneralLinearGroup.det (unipotent _) |> fun d => (rfl : d = d)]
    have hdet1 : Matrix.GeneralLinearGroup.det (unipotent (Multiplicative.toAdd z) : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      simp [unipotent, Matrix.det_fin_two_of]
    rw [hdet1, one_mul]
    have hψψ : NumberField.StandardAddChar.psiLocal ℚ p (-Multiplicative.toAdd z) * NumberField.StandardAddChar.psiLocal ℚ p (Multiplicative.toAdd z) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc _ = (NumberField.StandardAddChar.psiLocal ℚ p (-Multiplicative.toAdd z) * NumberField.StandardAddChar.psiLocal ℚ p (Multiplicative.toAdd z)) *
          ((B g * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) * w g *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ e) := by ring
      _ = _ := by rw [hψψ, one_mul]
  have hψc' : Continuous (fun t : p.adicCompletion ℚ => (NumberField.StandardAddChar.psiLocal ℚ p t : ℂ)) := BPhi.continuous_psiLocal p

  have hkey : ∀ G : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞, Measurable G →
      ∫⁻ g, (∫⁻ x : p.adicCompletion ℚ, G (unipotent x * g) ∂(selfDualHaarAt ℚ p)) ∂(μ₂.withDensity ρ) = ∫⁻ g, G g ∂μ₂ := by
    intro G hG
    have hjoint : Measurable fun z : GL (Fin 2) (p.adicCompletion ℚ) × p.adicCompletion ℚ => G (unipotent z.2 * z.1) := by
      refine hG.comp ?_
      have h1 : Continuous fun z : GL (Fin 2) (p.adicCompletion ℚ) × p.adicCompletion ℚ => (unipotent z.2 : GL (Fin 2) (p.adicCompletion ℚ)) := by
        simp_rw [unipotent_eq_unipotentGL2]
        exact (continuous_unipotentGL2 p).comp continuous_snd
      exact (h1.mul continuous_fst).measurable
    have hFavm : Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) => ∫⁻ x : p.adicCompletion ℚ, G (unipotent x * g) ∂(selfDualHaarAt ℚ p) :=
      hjoint.lintegral_prod_right'
    have h2 : ∀ x : p.adicCompletion ℚ,
        ∫⁻ g, ρ g * G (unipotent x * g) ∂μ₂ = ∫⁻ h, ρ (unipotentGL2 (-x) * h) * G h ∂μ₂ := by
      intro x
      have := lintegral_mul_left_eq_self (μ := μ₂) (fun h => ρ (unipotentGL2 (-x) * h) * G h) (unipotent x)
      rw [← this]
      congr 1
      funext g
      rw [unipotent_eq_unipotentGL2, ← mul_assoc, ← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero, one_mul]
    have hmeasA : AEMeasurable (Function.uncurry fun (g : GL (Fin 2) (p.adicCompletion ℚ)) (x : p.adicCompletion ℚ) =>
        ρ g * G (unipotent x * g)) (μ₂.prod (selfDualHaarAt ℚ p)) :=
      ((hρm.comp measurable_fst).mul hjoint).aemeasurable
    have hmeasB : AEMeasurable (Function.uncurry fun (x : p.adicCompletion ℚ) (h : GL (Fin 2) (p.adicCompletion ℚ)) =>
        ρ (unipotentGL2 (-x) * h) * G h) ((selfDualHaarAt ℚ p).prod μ₂) := by
      refine ((hρm.comp ?_).mul (hG.comp measurable_snd)).aemeasurable
      exact (((continuous_unipotentGL2 p).comp (continuous_neg.comp continuous_fst)).mul continuous_snd).measurable
    rw [lintegral_withDensity_eq_lintegral_mul _ hρm hFavm]
    calc ∫⁻ g, (ρ * fun g => ∫⁻ x : p.adicCompletion ℚ, G (unipotent x * g) ∂(selfDualHaarAt ℚ p)) g ∂μ₂
        = ∫⁻ g, ∫⁻ x, ρ g * G (unipotent x * g) ∂(selfDualHaarAt ℚ p) ∂μ₂ := by
          refine lintegral_congr fun g => ?_
          have hmx : Measurable fun x : p.adicCompletion ℚ => G (unipotent x * g) := by
            have hc : Continuous fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) * g := by
              simp_rw [unipotent_eq_unipotentGL2]; exact (continuous_unipotentGL2 p).mul continuous_const
            exact hG.comp hc.measurable
          rw [Pi.mul_apply, lintegral_const_mul _ hmx]
      _ = ∫⁻ x, ∫⁻ g, ρ g * G (unipotent x * g) ∂μ₂ ∂(selfDualHaarAt ℚ p) := lintegral_lintegral_swap hmeasA
      _ = ∫⁻ x, ∫⁻ h, ρ (unipotentGL2 (-x) * h) * G h ∂μ₂ ∂(selfDualHaarAt ℚ p) := by
          refine lintegral_congr fun x => ?_; exact h2 x
      _ = ∫⁻ h, ∫⁻ x, ρ (unipotentGL2 (-x) * h) * G h ∂(selfDualHaarAt ℚ p) ∂μ₂ := lintegral_lintegral_swap hmeasB
      _ = ∫⁻ h, G h ∂μ₂ := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun x : p.adicCompletion ℚ => ρ (unipotentGL2 (-x) * h) :=
            hρm.comp ((((continuous_unipotentGL2 p).comp continuous_neg).mul continuous_const).measurable)
          rw [lintegral_mul_const _ hm, hone h, one_mul]

  have hFint : ∀ s : ℂ, σb < s.re → Integrable (Fe (s + s₀ + 1 / 2 - 1 / 2)) (μ₂.withDensity ρ) := by
    intro s hs
    have hGJ := hI s hs
    set GJ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun g =>
      w g * Φ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀) with hGJdef
    have hGJm : Measurable GJ := by
      rw [hGJdef]
      exact (((hwc.mul (hΦ.continuous.comp Units.continuous_val)).mul hχc).mul (hmodc _)).measurable
    refine ⟨(hFem _).aestronglyMeasurable, ?_⟩

    have hpt : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        ‖Fe (s + s₀ + 1 / 2 - 1 / 2) g‖ₑ ≤ ∫⁻ x : p.adicCompletion ℚ, ‖GJ (unipotent x * g)‖ₑ ∂(selfDualHaarAt ℚ p) := by
      intro g
      have hexp : (s + s₀ + 1 / 2 - 1 / 2 : ℂ) = s + s₀ := by ring

      have hGJn : ∀ x : p.adicCompletion ℚ, GJ (unipotent x * g) =
          NumberField.StandardAddChar.psiLocal ℚ p x *
            (w g * Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
              ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)) := by
        intro x
        have hdet1 : Matrix.GeneralLinearGroup.det (unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) = Matrix.GeneralLinearGroup.det g := by
          rw [map_mul]
          have : Matrix.GeneralLinearGroup.det (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) = 1 := by
            apply Units.ext
            rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
            simp [unipotent, Matrix.det_fin_two_of]
          rw [this, one_mul]
        rw [hGJdef]
        simp only
        rw [hwlaw, hdet1]
        ring
      have hmeas : Measurable fun x : p.adicCompletion ℚ => GJ (unipotent x * g) := by
        have hc : Continuous fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) * g := by
          simp_rw [unipotent_eq_unipotentGL2]; exact (continuous_unipotentGL2 p).mul continuous_const
        exact hGJm.comp hc.measurable

      have hBle : ‖B g‖ₑ ≤ ∫⁻ x : p.adicCompletion ℚ, ‖NumberField.StandardAddChar.psiLocal ℚ p x *
          Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ₑ ∂(selfDualHaarAt ℚ p) := by
        rw [hB]; exact enorm_integral_le_lintegral_enorm _
      set c : ℝ≥0∞ := ‖w g * ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + s₀)‖ₑ with hc
      have hlhs : ‖Fe (s + s₀ + 1 / 2 - 1 / 2) g‖ₑ = ‖B g‖ₑ * c := by
        rw [hFe, hc]
        simp only
        rw [hexp, ← enorm_mul]
        congr 1; ring
      have hrhs : ∫⁻ x : p.adicCompletion ℚ, ‖GJ (unipotent x * g)‖ₑ ∂(selfDualHaarAt ℚ p) =
          (∫⁻ x : p.adicCompletion ℚ, ‖NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ₑ ∂(selfDualHaarAt ℚ p)) * c := by
        have hmx : Measurable fun x : p.adicCompletion ℚ => ‖NumberField.StandardAddChar.psiLocal ℚ p x *
            Φ ((unipotent x * g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))‖ₑ := by
          have hc1 : Continuous fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) * g := by
            have : (fun x : p.adicCompletion ℚ => (unipotent x : GL (Fin 2) (p.adicCompletion ℚ)) * g) =
                fun x => (unipotentGL2 x : GL (Fin 2) (p.adicCompletion ℚ)) * g := by
              funext x; rw [unipotent_eq_unipotentGL2]
            rw [this]; exact (continuous_unipotentGL2 p).mul continuous_const
          exact (hψc'.mul (hΦ.continuous.comp (Units.continuous_val.comp hc1))).measurable.enorm
        rw [← lintegral_mul_const _ hmx]
        refine lintegral_congr fun x => ?_
        rw [hGJn x, hc, ← enorm_mul]
        congr 1; ring
      rw [hlhs, hrhs]
      exact mul_le_mul_left hBle _
    calc ∫⁻ g, ‖Fe (s + s₀ + 1 / 2 - 1 / 2) g‖ₑ ∂(μ₂.withDensity ρ)
        ≤ ∫⁻ g, (∫⁻ x : p.adicCompletion ℚ, ‖GJ (unipotent x * g)‖ₑ ∂(selfDualHaarAt ℚ p)) ∂(μ₂.withDensity ρ) :=
          lintegral_mono hpt
      _ = ∫⁻ g, ‖GJ g‖ₑ ∂μ₂ := hkey (fun g => ‖GJ g‖ₑ) hGJm.enorm
      _ < ⊤ := by rw [hGJdef]; exact hGJ.2

  have hq0 := RCgB.qR_pos p
  have hqR : (RCgB.qR p : ℝ) = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
    simp [RCgB.qR]
  have hNpos : 0 < Ideal.absNorm p.asIdeal := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot)
  have hNc : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hdiagZ : ∀ n₁ : ℤ, diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ =
      diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₁ * 1) := by
    intro n₁
    apply Units.ext
    rw [mul_one]
    simp [diagZ, diagUnitGL2, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_zpow_eq_zpow_val]
  have hmodshell : ∀ (n₁ n₂ : ℤ), ∀ k ∈ (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      ((modulus ((Matrix.GeneralLinearGroup.det
        (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n₂ *
          diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ * k) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ≥0) : ℝ) =
        RCgB.qR p ^ (-(2 * n₂ + n₁)) := by
    intro n₁ n₂ k hk
    rw [RCgB.coe_modulus_eq_norm, map_mul, map_mul, map_zpow, Units.val_mul, Units.val_mul, Units.val_zpow_eq_zpow_val,
      norm_mul, norm_mul, norm_zpow, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply, RCgB.norm_det_eq_one hk, mul_one]
    have h1 : ((scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ (2 : ℤ) := by
      rw [show ((scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ, 0; 0,
          algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ] from rfl, Matrix.det_fin_two_of, zpow_two]
      ring
    have h2 : ((diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det = (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n₁ := by
      rw [show ((diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n₁ : GL (Fin 2) (p.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![(algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n₁, 0; 0, 1] from rfl,
        Matrix.det_fin_two_of]
      ring
    rw [h1, h2, ← norm_zpow, ← zpow_mul, RCgB.norm_uniformizer_zpow hϖ, RCgB.norm_uniformizer_zpow hϖ, ← zpow_add₀ hq0.ne']
    congr 1; ring

  have hK0m : MeasurableSet ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2.measurableSet

  set wt : ℤ × ℤ → ℂ := fun dn =>
    (((μN {x : ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range |
        (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ * (x : GL (Fin 2) (p.adicCompletion ℚ)) * (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤})⁻¹).toReal : ℂ) with hwt
  set Cst : ℤ × ℤ → ℂ := fun dn =>
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), (B (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) * ((χ (Matrix.GeneralLinearGroup.det (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k)) : ℂˣ) : ℂ)) * w (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) ∂μ₂ with hCst
  set Sfin : Finset (ℤ × ℤ) := Finset.Icc (-MP - cP) (max nstar (cS + MP)) ×ˢ Finset.Icc (-MP) cP with hSfin
  obtain ⟨P, m, hPm⟩ := exists_laurent_of_sum_monomials Sfin
    (fun dn => (κ : ℂ) * (wt dn * (Cst dn * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-(2 * dn.2 + dn.1) : ℤ) : ℂ) * s₀))))
    (fun dn => -(2 * dn.2 + dn.1)) (Ideal.absNorm p.asIdeal : ℂ) hNc
  refine ⟨P, m, σb, fun s hs => ?_⟩
  set e : ℂ := s + s₀ + 1 / 2 - 1 / 2 with he

  have hZ : godementZeta2 p μ₂ w Φ χ (s + s₀) = (κ : ℂ) * ∫ g, Fe e g ∂(μ₂.withDensity ρ) := by
    rw [hR1 w hwlc hwlaw Φ hΦ hΦc χ hχ (s + s₀) (hI s hs)]
    congr 1

  have hHS := (AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ p ϖ hπ hϖ μ₂ μN
    (Fe e) (hFem e) (hFeN e) (by rw [hρ] at hFint; exact hFint s hs)).2.2
  rw [← hρ] at hHS

  have hterm : ∀ dn : ℤ × ℤ, ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fe e (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) ∂μ₂ =
      Cst dn * ((RCgB.qR p ^ (-(2 * dn.2 + dn.1)) : ℝ) : ℂ) ^ e := by
    intro dn
    rw [hCst, ← integral_mul_const]
    refine setIntegral_congr_fun hK0m fun k hk => ?_
    rw [hFe]
    simp only
    rw [hmodshell dn.1 dn.2 k hk]
  have hzero : ∀ dn : ℤ × ℤ, dn ∉ Sfin → ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fe e (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) ∂μ₂ = 0 := by
    intro dn hdn
    rw [hSfin, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hdn
    by_cases h2 : -MP ≤ dn.2 ∧ dn.2 ≤ cP
    ·
      have h1 : ¬(-MP - cP ≤ dn.1 ∧ dn.1 ≤ max nstar (cS + MP)) := fun h1 => hdn ⟨h1, h2⟩
      rcases not_and_or.1 h1 with h1a | h1b
      ·
        refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
        have h3 := (hprof k hk dn.1 dn.2 1 (by simp)).2.2.1 (by push_neg at h1a; omega)
        rw [hFe]
        simp only
        rw [hB]
        simp only
        rw [hdiagZ, h3]
        simp
      ·
        push_neg at h1b
        have hn1 : nstar ≤ dn.1 := le_of_lt ((le_max_left _ _).trans_lt h1b)
        have hn2 : cS ≤ dn.1 + dn.2 := by
          have := (le_max_right _ _).trans_lt h1b
          omega
        have h4 := hSVD dn.1 dn.2 hn1 hn2 e
        rw [hFe]
        simp only
        rw [hB]
        exact h4
    ·
      refine setIntegral_eq_zero_of_forall_eq_zero fun k hk => ?_
      have hpk := hprof k hk dn.1 dn.2 1 (by simp)
      rw [hFe]
      simp only
      rw [hB]
      simp only
      rw [hdiagZ]
      rcases not_and_or.1 h2 with h2a | h2b
      · push_neg at h2a
        rw [hpk.2.1 h2a]; simp
      · push_neg at h2b
        rw [hpk.1 h2b]; simp

  have hsum : ∫ g, Fe e g ∂(μ₂.withDensity ρ) =
      ∑ dn ∈ Sfin, wt dn * ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))), Fe e (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ dn.1 * k) ∂μ₂ := by
    rw [← hHS.tsum_eq, tsum_eq_sum (s := Sfin)]
    · intro dn hdn
      show wt dn * _ = 0
      rw [hzero dn hdn, mul_zero]
  rw [hZ, hsum, ← hPm s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dn _ => ?_
  rw [hterm dn, hqR]
  push_cast
  rw [GJJLGlueAlg.natCast_zpow_cpow _ hNpos, he]
  have : (((-(2 * dn.2 + dn.1) : ℤ) : ℂ) * (s + s₀ + 1 / 2 - 1 / 2)) =
      ((-(2 * dn.2 + dn.1) : ℤ) : ℂ) * s₀ + ((-(2 * dn.2 + dn.1) : ℤ) : ℂ) * s := by ring
  rw [this, Complex.cpow_add _ _ hNc]
  push_cast
  ring

end
end
end S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_exists_laurent_godementZeta2_whittaker_shift_of_torusLaurent (solution)
