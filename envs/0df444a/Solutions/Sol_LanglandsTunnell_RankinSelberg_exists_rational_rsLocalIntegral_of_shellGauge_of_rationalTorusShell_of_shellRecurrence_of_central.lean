-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dbabc78b-e7c8-59fa-952c-ebe46ad45573

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
import Theorems.Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
import Theorems.Thm_AutomorphicForm_hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2
import Theorems.Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
import Theorems.Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

set_option maxHeartbeats 1600000

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal

noncomputable section

namespace RCg

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

theorem integrable_withDensity_of_lintegral_lt_top [IsTopologicalGroup G] [SecondCountableTopology G]
    [BorelSpace G] {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure G) (H : Subgroup G) (μH : Measure H) [SFinite μH]
    (Φ : G → E) (hΦ : Measurable Φ)
    (hfin : ∫⁻ g, (‖Φ g‖ₑ) * HaarQuotient.density H μH g ∂μ < ∞) :
    Integrable Φ (μ.withDensity (HaarQuotient.density H μH)) := by
  have hD := measurable_density H μH
  refine ⟨(hΦ.aestronglyMeasurable).mono_ac (withDensity_absolutelyContinuous μ _), ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul₀ hD.aemeasurable hΦ.enorm.aemeasurable]
  calc ∫⁻ g, (HaarQuotient.density H μH * fun g => ‖Φ g‖ₑ) g ∂μ
      = ∫⁻ g, ‖Φ g‖ₑ * HaarQuotient.density H μH g ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [Pi.mul_apply, mul_comm]
    _ < ∞ := hfin

end Density

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

section Iota

open LanglandsTunnell.CubicInduction

variable {L : Type*} [NormedField L]

theorem lastRowSup_iotaGL (g : GL (Fin 2) L) : lastRowSup (iotaGL g) = 1 := by
  simp [lastRowSup, coe_iotaGL, embedMat2]

theorem minorSup_iotaGL (g : GL (Fin 2) L) :
    minorSup (iotaGL g) = max ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ := by
  simp [minorSup, bottomMinor, coe_iotaGL, embedMat2]

theorem detSize_iotaGL (g : GL (Fin 2) L) : detSize (iotaGL g) = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
  rw [detSize, coe_iotaGL]
  congr 1
  simp [embedMat2, Matrix.det_fin_three, Matrix.det_fin_two]

end Iota

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

theorem shell_mul_apply_one (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) (k : G) (j : Fin 2) :
    ((scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k : G) : Mat) 1 j =
      (algebraMap (O) (F) ϖ) ^ dn.2 * (k : Mat) 1 j := by
  rw [shellRep_eq_diagU hπ, Units.val_mul, coe_diagU, Matrix.mul_apply, Fin.sum_univ_two, coe_piUnit_zpow]
  simp

theorem det_shell_mul (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) (k : G) :
    ((scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k : G) : Mat).det =
      (algebraMap (O) (F) ϖ) ^ (dn.2 + dn.1) * (algebraMap (O) (F) ϖ) ^ dn.2 * (k : Mat).det := by
  rw [shellRep_eq_diagU hπ, Units.val_mul, Matrix.det_mul, coe_diagU, Matrix.det_fin_two_of, coe_piUnit_zpow,
    coe_piUnit_zpow]
  ring

theorem minorSup_iotaGL_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) =
      qR v ^ (-dn.2) := by
  rw [minorSup_iotaGL, shell_mul_apply_one hπ, shell_mul_apply_one hπ, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg _), max_norm_bottom_row_eq_one hk, mul_one, norm_uniformizer_zpow hϖ]

theorem detSize_iotaGL_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    detSize (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) =
      qR v ^ (-(dn.2 + dn.1)) * qR v ^ (-dn.2) := by
  rw [detSize_iotaGL, det_shell_mul hπ, norm_mul, norm_mul, norm_det_eq_one hk, mul_one,
    norm_uniformizer_zpow hϖ, norm_uniformizer_zpow hϖ]

theorem rootOne_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    detSize (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) *
        lastRowSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) /
        minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) ^ 2 =
      qR v ^ (-dn.1) := by
  rw [detSize_iotaGL_shell hϖ hπ dn hk, lastRowSup_iotaGL, minorSup_iotaGL_shell hϖ hπ dn hk, mul_one]
  have hq := qR_ne_zero v
  rw [div_eq_iff (pow_ne_zero _ (zpow_ne_zero _ hq)), ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, ← zpow_add₀ hq]
  congr 1
  push_cast
  ring

theorem rootTwo_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    minorSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) /
        lastRowSup (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) ^ 2 =
      qR v ^ (-dn.2) := by
  rw [minorSup_iotaGL_shell hϖ hπ dn hk, lastRowSup_iotaGL, one_pow, div_one]

theorem coe_modulus_det_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det
            (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) :
              (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) : ℝ≥0) : ℝ) =
      qR v ^ (-(2 * dn.2 + dn.1)) := by
  rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply, det_shell_mul hπ, norm_mul, norm_mul,
    norm_det_eq_one hk, mul_one, norm_uniformizer_zpow hϖ, norm_uniformizer_zpow hϖ, ← zpow_add₀ (qR_ne_zero v)]
  congr 1
  ring

end Torus

section Unipotent

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range

theorem coe_unipotentGL2Hom (z : Multiplicative (HeightOneSpectrum.adicCompletion ℚ v)) :
    ((unipotentGL2Hom z : G) : Mat) = !![1, z.toAdd; 0, 1] := rfl

theorem coe_unip_eq :
    ((unip v : Subgroup G) : Set G) = {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip v : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unipotent_eq_unipotentGL2 (x : F) : UnramifiedWhittaker.unipotent x = (unipotentGL2 x : G) := by
  refine Units.ext ?_
  rw [unipotentGL2_coe]
  simp [UnramifiedWhittaker.unipotent]

theorem det_unipotentGL2 (x : F) : Matrix.GeneralLinearGroup.det (unipotentGL2 x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

variable {v}
variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem coe_diagU_inv_mul_unipotent_mul_diagU (a b a' b' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ)
    (z : Multiplicative (HeightOneSpectrum.adicCompletion ℚ v)) :
    ((((diagU v a b)⁻¹ * unipotentGL2Hom z * diagU v a' b' : G)) : Mat) =
      !![((a⁻¹ * a' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F),
          ((a⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) * z.toAdd * b';
        0, ((b⁻¹ * b' : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)] := by
  rw [diagU_inv, Units.val_mul, Units.val_mul, coe_diagU, coe_diagU, coe_unipotentGL2Hom]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem piUnit_conj_entry (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) (z : F) :
    (((piUnit hπ ^ (dn.2 + dn.1))⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) * z *
        ((piUnit hπ ^ dn.2 : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) =
      (((piUnit hπ ^ dn.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) * z := by
  have hϖ0 : algebraMap (O) (F) ϖ ≠ 0 := hπ
  rw [← zpow_neg, ← zpow_neg, coe_piUnit_zpow, coe_piUnit_zpow, coe_piUnit_zpow, mul_assoc, mul_comm z, ← mul_assoc,
    ← zpow_add₀ hϖ0]
  congr 2
  ring

theorem shellRep_inv_mul_unipotent_mul_shellRep (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ)
    (z : Multiplicative (HeightOneSpectrum.adicCompletion ℚ v)) :
    (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1)⁻¹ * unipotentGL2Hom z *
        (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1) =
      unipotentGL2Hom (Multiplicative.ofAdd
        ((((piUnit hπ ^ dn.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) * z.toAdd)) := by
  rw [shellRep_eq_diagU hπ]
  refine Units.ext ?_
  rw [coe_diagU_inv_mul_unipotent_mul_diagU, coe_unipotentGL2Hom, inv_mul_cancel, inv_mul_cancel, Units.val_one,
    toAdd_ofAdd, piUnit_conj_entry hπ]

theorem unipotentGL2Hom_mem_kzero_iff (z : Multiplicative (HeightOneSpectrum.adicCompletion ℚ v)) :
    (unipotentGL2Hom z : G) ∈ kzero v ↔ Valued.v z.toAdd ≤ 1 := by
  rw [mem_kzero_iff]
  have hinv : (((unipotentGL2Hom z : G)⁻¹ : G) : Mat) = !![1, -z.toAdd; 0, 1] := by
    rw [← map_inv]; rfl
  constructor
  · rintro ⟨h, -⟩
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (by simpa [coe_unipotentGL2Hom] using h 0 1)
  · intro hz
    have hz' : z.toAdd ∈ (O) := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hz
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [coe_unipotentGL2Hom]
      fin_cases i <;> fin_cases j <;> simp [hz', one_mem, zero_mem]
    · rw [hinv]
      fin_cases i <;> fin_cases j <;> simp [hz', one_mem, zero_mem]

theorem shellSlice_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    {x : ↥(unip v) |
        (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1)⁻¹ * (x : G) *
          (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1) ∈ kzero v} =
      (fun y : ↥(unip v) => ((y : G) : Mat) 0 1) ⁻¹'
        ((fun z => (((piUnit hπ ^ dn.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) * z) ⁻¹'
          {z : F | Valued.v z ≤ 1}) := by
  ext x
  obtain ⟨z, hz⟩ := x.2
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [← hz, shellRep_inv_mul_unipotent_mul_shellRep hπ, unipotentGL2Hom_mem_kzero_iff, toAdd_ofAdd,
    coe_unipotentGL2Hom]
  simp

theorem shellSlice_zero_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) :
    {x : ↥(unip v) |
        (scalarPi (algebraMap (O) (F) ϖ) hπ ^ (0 : ℤ × ℤ).2 * diagZ (algebraMap (O) (F) ϖ) hπ (0 : ℤ × ℤ).1)⁻¹ *
          (x : G) *
          (scalarPi (algebraMap (O) (F) ϖ) hπ ^ (0 : ℤ × ℤ).2 * diagZ (algebraMap (O) (F) ϖ) hπ (0 : ℤ × ℤ).1) ∈
            kzero v} =
      (fun y : ↥(unip v) => ((y : G) : Mat) 0 1) ⁻¹' {z : F | Valued.v z ≤ 1} := by
  rw [shellSlice_eq hπ]
  ext x
  simp

end Unipotent

section Topology

open LanglandsTunnell.CubicInduction

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem sFinite_unipHaar :
    letI := localGLBorel ℚ v
    ∀ (μN : Measure ↥(unip v)) [μN.IsHaarMeasure], SFinite μN := by
  intro μN _
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  haveI : SigmaCompactSpace ↥(unip v) := (isClosed_unip v).sigmaCompactSpace
  infer_instance

theorem continuous_iotaGL : Continuous fun g : G => (iotaGL g : G₃) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  have hci : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Mat) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : G, ((((iotaGL g : G₃)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F) = embedMat2 ((g⁻¹ : G) : Mat) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

private theorem _root_.RCg.continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

p2m_export "RCg" "continuous_of_rightInvariant"
end Topology

section Integrand

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def rsIntegrand (W : LocalGL3 v → ℂ) (g₃ : LocalGL3 v) (W₂ : G → ℂ) (s : ℂ) (g : G) : ℂ :=
  (W (iotaGL g * g₃) * W₂ g) *
    ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) ^ (s - 1 / 2)

theorem rsIntegrand_unipotent_mul {ψv : AddChar F ℂ}
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψv W) (g₃ : LocalGL3 v) {W₂ : G → ℂ}
    (hW₂ψ : ∀ (x : F) (g : G),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (s : ℂ) (x : ↥(unip v)) (g : G) :
    rsIntegrand W g₃ W₂ s ((x : G) * g) = rsIntegrand W g₃ W₂ s g := by
  obtain ⟨z, hz⟩ := x.2
  have hx : (x : G) = unipotentGL2 z.toAdd := by rw [← hz]; rfl
  unfold rsIntegrand
  rw [hx, map_mul, iotaGL_unipotentGL2, mul_assoc (upperUnipotent3 _ _ _), hW, map_mul, det_unipotentGL2, one_mul,
    ← unipotent_eq_unipotentGL2, hW₂ψ, hψinv, AddChar.inv_apply, add_zero]
  congr 1
  calc (NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * W (iotaGL g * g₃) *
        ((NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd * W₂ g)
      = ((NumberField.StandardAddChar.psiLocal ℚ v) (-z.toAdd) * (NumberField.StandardAddChar.psiLocal ℚ v) z.toAdd) *
          (W (iotaGL g * g₃) * W₂ g) := by ring
    _ = W (iotaGL g * g₃) * W₂ g := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem measurable_rsIntegrand {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (g₃ : LocalGL3 v) {W₂ : G → ℂ} {U₂ : Subgroup G} (hU₂ : IsOpen (U₂ : Set G))
    (hW₂K : ∀ (k g : G), k ∈ U₂ → W₂ (g * k) = W₂ g) (s : ℂ) :
    Measurable[localGLBorel ℚ v] (rsIntegrand W g₃ W₂ s) := by
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  obtain ⟨Uv, hUv, hWU⟩ := hsm
  have hWc : Continuous W := continuous_of_rightInvariant hUv hWU
  have hW₂c : Continuous W₂ := continuous_of_rightInvariant hU₂ fun k hk g => hW₂K k g hk
  have h1 : Continuous fun g : G => W (iotaGL g * g₃) := hWc.comp ((continuous_iotaGL v).mul continuous_const)
  have h3 : Continuous fun g : G =>
      ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) := by
    have : (fun g : G => ((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
      funext g
      rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))
  exact ((h1.mul hW₂c).measurable).mul (h3.measurable.pow_const _)

end Integrand

section RealBounds

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem qR_eq_natCast : qR v = (Ideal.absNorm v.asIdeal : ℝ) := NNReal.coe_natCast _

theorem one_le_qR : 1 ≤ qR v := (one_lt_qR v).le

theorem exists_cutoff (B : ℝ) : ∃ m₀ : ℤ, m₀ ≤ 0 ∧ ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt B (one_lt_qR v)
  refine ⟨-(j : ℤ), by omega, fun d hd => ?_⟩
  by_contra hlt
  have hlt : d < -(j : ℤ) := lt_of_not_ge hlt
  have h1 : qR v ^ (j : ℤ) ≤ qR v ^ (-d) := zpow_le_zpow_right₀ (one_le_qR v) (by omega)
  rw [zpow_natCast] at h1
  linarith

theorem summable_indicator_zpow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (m₀ : ℤ) :
    Summable fun d : ℤ => if m₀ ≤ d then r ^ d else 0 := by
  set f : ℤ → ℝ := fun d => if m₀ ≤ d then r ^ d else 0 with hf
  have hinj : Function.Injective fun j : ℕ => m₀ + (j : ℤ) := fun a b h => by
    simpa using h
  have hzero : ∀ x ∉ Set.range (fun j : ℕ => m₀ + (j : ℤ)), f x = 0 := by
    intro x hx
    have hlt : ¬ m₀ ≤ x := fun hle => hx ⟨(x - m₀).toNat, by simp; omega⟩
    simp [hf, hlt]
  rw [← hinj.summable_iff hzero]
  have hcomp : (f ∘ fun j : ℕ => m₀ + (j : ℤ)) = fun j : ℕ => r ^ m₀ * r ^ j := by
    funext j
    simp only [Function.comp_apply, hf]
    rw [if_pos (by omega), zpow_add₀ hr0.ne', zpow_natCast]
  rw [hcomp]
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_left _

theorem indicator_zpow_nonneg {r : ℝ} (hr0 : 0 < r) (m₀ d : ℤ) : 0 ≤ (if m₀ ≤ d then r ^ d else 0) := by
  split_ifs
  · exact (zpow_pos hr0 _).le
  · exact le_rfl

end RealBounds

section PartnerBound

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem scalar_mul_comm (u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (u : F) * (g : Mat) = (g : Mat) * Matrix.scalar (Fin 2) (u : F)
  exact (Matrix.scalar_commute (u : F) (fun r => mul_comm _ _) (g : Mat)).eq

theorem partner_shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (dn : ℤ × ℤ) (k : G) :
    W₂ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) =
      ((ω₂ (piUnit hπ) : ℂˣ) : ℂ) ^ dn.2 * W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) := by
  rw [shellRep_eq_diagZ_mul hπ, scalarPi_zpow_eq_scalar hπ, mul_assoc, scalar_mul_comm, ← mul_assoc, hW₂Z, map_zpow,
    Units.val_zpow_eq_zpow_val]

theorem norm_partner_shell_eq (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ}
    (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (dn : ℤ × ℤ) (k : G) :
    ‖W₂ (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ =
      ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ := by
  rw [partner_shell_eq hπ ω₂ hW₂Z, norm_mul, norm_zpow]

theorem exists_bound_on_shell (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (hW₂c : Continuous W₂) (d : ℤ) :
    ∃ M : ℝ, ∀ k ∈ kzero v, ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ M := by
  have hK : IsCompact ((fun k : G => diagZ (algebraMap (O) (F) ϖ) hπ d * k) '' ((kzero v : Subgroup G) : Set G)) :=
    (isCompact_kzero v).image (continuous_const.mul continuous_id)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hW₂c.continuousOn
  exact ⟨M, fun k hk => hM _ ⟨k, hk, rfl⟩⟩

theorem exists_partner_shell_bound (hπ : algebraMap (O) (F) ϖ ≠ 0) {W₂ : G → ℂ} (hW₂c : Continuous W₂)
    (hW₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m))
    (m₀ : ℤ) (hm₀ : m₀ ≤ 0) :
    ∃ (Cβ A' : ℝ), 0 ≤ Cβ ∧ 0 ≤ A' ∧ ∀ (d : ℤ), m₀ ≤ d → ∀ k ∈ kzero v,
      ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ Cβ * qR v ^ (A' * ((d : ℝ) - m₀)) := by
  obtain ⟨C, A, hgr⟩ := hW₂gr
  choose M hM using exists_bound_on_shell hπ hW₂c
  set M₀ : ℝ := ∑ d ∈ Finset.Ico m₀ 0, |M d| with hM₀
  have hM₀nn : 0 ≤ M₀ := Finset.sum_nonneg fun d _ => abs_nonneg _
  refine ⟨|C| + M₀, max A 0, by positivity, le_max_right _ _, fun d hd k hk => ?_⟩
  have hq1 := one_le_qR v
  have hexp_nn : 0 ≤ max A 0 * ((d : ℝ) - m₀) :=
    mul_nonneg (le_max_right _ _) (by exact_mod_cast sub_nonneg.mpr hd)
  have hpow1 : 1 ≤ qR v ^ (max A 0 * ((d : ℝ) - m₀)) := Real.one_le_rpow hq1 hexp_nn
  rcases lt_or_ge d 0 with hneg | hnn
  ·
    have hmem : d ∈ Finset.Ico m₀ 0 := Finset.mem_Ico.mpr ⟨hd, hneg⟩
    calc ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ M d := hM d k hk
      _ ≤ |M d| := le_abs_self _
      _ ≤ M₀ := Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hmem
      _ ≤ (|C| + M₀) * 1 := by rw [mul_one]; linarith [abs_nonneg C]
      _ ≤ (|C| + M₀) * qR v ^ (max A 0 * ((d : ℝ) - m₀)) := by gcongr
  ·
    have h1 : ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ C * qR v ^ (A * (d : ℝ)) := by
      rw [qR_eq_natCast]; exact hgr d hnn k hk
    have hpos : 0 ≤ qR v ^ (A * (d : ℝ)) := Real.rpow_nonneg (qR_pos v).le _
    have h2 : qR v ^ (A * (d : ℝ)) ≤ qR v ^ (max A 0 * ((d : ℝ) - m₀)) := by
      refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
      have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast hnn
      have hm0 : ((m₀ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hm₀
      calc A * (d : ℝ) ≤ max A 0 * (d : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
        _ ≤ max A 0 * ((d : ℝ) - m₀) := mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
    calc ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ C * qR v ^ (A * (d : ℝ)) := h1
      _ ≤ |C| * qR v ^ (A * (d : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self C) hpos
      _ ≤ (|C| + M₀) * qR v ^ (max A 0 * ((d : ℝ) - m₀)) :=
          mul_le_mul (by linarith) h2 hpos (by positivity)

end PartnerBound

section GaugeBound

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem gauge_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W' : LocalGL3 v → ℂ} {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) →
        W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) = 0) ∧
      ‖W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖ ≤
        |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
  have hq := qR_ne_zero v
  obtain ⟨hvan, hbd⟩ := hg (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))
  rw [rootOne_shell hϖ hπ dn hk, rootTwo_shell hϖ hπ dn hk] at hvan hbd
  have hpow : qR v ^ (-dn.1) * qR v ^ (-dn.2) = qR v ^ (-(dn.1 + dn.2)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  refine ⟨fun hmn => hvan fun hB => hmn ⟨hm₀ _ hB.1, hm₀ _ hB.2⟩, ?_⟩
  have hnn : 0 ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := mul_nonneg (abs_nonneg C) (zpow_nonneg (qR_pos v).le _)
  by_cases hB : qR v ^ (-dn.1) ≤ B ∧ qR v ^ (-dn.2) ≤ B
  · calc ‖W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖
        ≤ C / (qR v ^ (-dn.1) * qR v ^ (-dn.2)) ^ t := hbd hB
      _ = C * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
          rw [hpow, ← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_neg]
          congr 2; ring
      _ ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (zpow_nonneg (qR_pos v).le _)
  · rw [hvan hB, norm_zero]
    exact hnn

end GaugeBound

section Assembly

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem norm_cpow_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (s : ℂ) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    ‖((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det
            (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) :
              (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)‖ =
      qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)) := by
  rw [coe_modulus_det_shell hϖ hπ dn hk, Complex.norm_cpow_eq_rpow_re_of_pos (zpow_pos (qR_pos v) _),
    ← Real.rpow_intCast, ← Real.rpow_mul (qR_pos v).le]
  congr 1
  have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by simp [Complex.sub_re]
  rw [hre]
  push_cast
  ring

def rOne (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (A' σ : ℝ) : ℝ := qR v ^ ((t : ℝ) + A' + 3 / 2 - σ)

def rTwo (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (ρ σ : ℝ) : ℝ := ρ * qR v ^ ((t : ℝ) + 1 - 2 * σ)

theorem rOne_pos (t : ℕ) (A' σ : ℝ) : 0 < rOne v t A' σ := Real.rpow_pos_of_pos (qR_pos v) _

theorem rTwo_pos (t : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (σ : ℝ) : 0 < rTwo v t ρ σ :=
  mul_pos hρ (Real.rpow_pos_of_pos (qR_pos v) _)

def shellMajorant (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (A' σ ρ : ℝ) (m₀ : ℤ) (dn : ℤ × ℤ) : ℝ :=
  (if m₀ ≤ dn.1 then rOne v t A' σ ^ dn.1 else 0) * (if m₀ ≤ dn.2 then rTwo v t ρ σ ^ dn.2 else 0)

theorem shellMajorant_nonneg (t : ℕ) (A' σ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (m₀ : ℤ) (dn : ℤ × ℤ) :
    0 ≤ shellMajorant v t A' σ ρ m₀ dn :=
  mul_nonneg (indicator_zpow_nonneg (rOne_pos t A' σ) _ _) (indicator_zpow_nonneg (rTwo_pos t hρ σ) _ _)

theorem summable_shellMajorant (t : ℕ) (A' σ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (m₀ : ℤ)
    (h₁ : rOne v t A' σ < 1) (h₂ : rTwo v t ρ σ < 1) : Summable (shellMajorant v t A' σ ρ m₀) :=
  (summable_indicator_zpow (rOne_pos t A' σ) h₁ m₀).mul_of_nonneg (summable_indicator_zpow (rTwo_pos t hρ σ) h₂ m₀)
    (fun _ => indicator_zpow_nonneg (rOne_pos t A' σ) _ _) (fun _ => indicator_zpow_nonneg (rTwo_pos t hρ σ) _ _)

theorem shellMajorant_of_le (t : ℕ) (A' σ ρ : ℝ) {m₀ : ℤ} {dn : ℤ × ℤ} (h : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) :
    shellMajorant v t A' σ ρ m₀ dn = rOne v t A' σ ^ dn.1 * rTwo v t ρ σ ^ dn.2 := by
  rw [shellMajorant, if_pos h.1, if_pos h.2]

def shellPointwise (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (C Cβ A' σ ρ : ℝ) (m₀ : ℤ) (dn : ℤ × ℤ) : ℝ :=
  |C| * Cβ * (qR v ^ ((t : ℤ) * (dn.1 + dn.2)) * (ρ ^ dn.2 * qR v ^ (A' * ((dn.1 : ℝ) - m₀))) *
    qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)))

theorem shellPointwise_nonneg (t : ℕ) (C : ℝ) {Cβ : ℝ} (hCβ : 0 ≤ Cβ) (A' σ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (m₀ : ℤ)
    (dn : ℤ × ℤ) : 0 ≤ shellPointwise v t C Cβ A' σ ρ m₀ dn := by
  have hq := (qR_pos v).le
  unfold shellPointwise
  exact mul_nonneg (mul_nonneg (abs_nonneg C) hCβ) (mul_nonneg (mul_nonneg (zpow_nonneg hq _)
    (mul_nonneg (zpow_nonneg hρ.le _) (Real.rpow_nonneg hq _))) (Real.rpow_nonneg hq _))

theorem shell_algebra (t : ℕ) (A' σ ρ : ℝ) (m₀ : ℤ) (dn : ℤ × ℤ) :
    qR v ^ dn.1 * (qR v ^ ((t : ℤ) * (dn.1 + dn.2)) *
        (ρ ^ dn.2 * qR v ^ (A' * ((dn.1 : ℝ) - m₀))) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2))) =
      qR v ^ (-A' * (m₀ : ℝ)) * (rOne v t A' σ ^ dn.1 * rTwo v t ρ σ ^ dn.2) := by
  have hq := qR_pos v
  unfold rOne rTwo
  rw [mul_zpow, ← Real.rpow_intCast (qR v) dn.1, ← Real.rpow_intCast (qR v) ((t : ℤ) * (dn.1 + dn.2)),
    ← Real.rpow_intCast (qR v ^ ((t : ℝ) + A' + 3 / 2 - σ)) dn.1,
    ← Real.rpow_intCast (qR v ^ ((t : ℝ) + 1 - 2 * σ)) dn.2, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]

  have key : ∀ x y : ℝ, qR v ^ x * qR v ^ y = qR v ^ (x + y) := fun x y => (Real.rpow_add hq x y).symm
  calc qR v ^ ((dn.1 : ℤ) : ℝ) * (qR v ^ (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) *
          (ρ ^ dn.2 * qR v ^ (A' * ((dn.1 : ℝ) - m₀))) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)))
      = ρ ^ dn.2 * (qR v ^ ((dn.1 : ℤ) : ℝ) * qR v ^ (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) *
          qR v ^ (A' * ((dn.1 : ℝ) - m₀)) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2))) := by ring
    _ = ρ ^ dn.2 * qR v ^ (((dn.1 : ℤ) : ℝ) + (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) + A' * ((dn.1 : ℝ) - m₀) +
          (-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)) := by rw [key, key, key]
    _ = ρ ^ dn.2 * qR v ^ (-A' * (m₀ : ℝ) + ((t : ℝ) + A' + 3 / 2 - σ) * ((dn.1 : ℤ) : ℝ) +
          ((t : ℝ) + 1 - 2 * σ) * ((dn.2 : ℤ) : ℝ)) := by
        congr 2
        push_cast
        ring
    _ = qR v ^ (-A' * (m₀ : ℝ)) * (qR v ^ (((t : ℝ) + A' + 3 / 2 - σ) * ((dn.1 : ℤ) : ℝ)) *
          (ρ ^ dn.2 * qR v ^ (((t : ℝ) + 1 - 2 * σ) * ((dn.2 : ℤ) : ℝ)))) := by
        rw [← key, ← key]; ring

theorem qR_zpow_mul_shellPointwise (t : ℕ) (C Cβ A' σ ρ : ℝ) {m₀ : ℤ} {dn : ℤ × ℤ} (h : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) :
    qR v ^ dn.1 * shellPointwise v t C Cβ A' σ ρ m₀ dn =
      (|C| * Cβ * qR v ^ (-A' * (m₀ : ℝ))) * shellMajorant v t A' σ ρ m₀ dn := by
  rw [shellMajorant_of_le t A' σ ρ h, shellPointwise, mul_left_comm, shell_algebra]
  ring

theorem exists_abscissa (t : ℕ) {A' ρ : ℝ} (hA' : 0 ≤ A') (hρ : 0 < ρ) :
    ∃ σ₂ : ℝ, ∀ σ : ℝ, σ₂ < σ → rOne v t A' σ < 1 ∧ rTwo v t ρ σ < 1 := by
  have hq := one_lt_qR v
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ρ hq
  refine ⟨(t : ℝ) + A' + j + 2, fun σ hσ => ⟨?_, ?_⟩⟩
  · exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  · have h1 : qR v ^ ((t : ℝ) + 1 - 2 * σ) < qR v ^ (-(j : ℝ) - 3) :=
      Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
    have h2 : ρ * qR v ^ (-(j : ℝ) - 3) ≤ qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 3) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (qR_pos v).le _)
      rw [Real.rpow_natCast]; exact hj.le
    have h3 : qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 3) = qR v ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add (qR_pos v)]; congr 1; ring
    have h4 : qR v ^ (-(3 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
    calc ρ * qR v ^ ((t : ℝ) + 1 - 2 * σ) < ρ * qR v ^ (-(j : ℝ) - 3) := mul_lt_mul_of_pos_left h1 hρ
      _ ≤ qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 3) := h2
      _ = qR v ^ (-(3 : ℝ)) := h3
      _ < 1 := h4

theorem norm_rsIntegrand_shell_le
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W W' : LocalGL3 v → ℂ} {g₃ : LocalGL3 v}
    (hWW' : ∀ g : G, W (iotaGL g * g₃) = W' (iotaGL g))
    {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d)
    {W₂ : G → ℂ} (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    {Cβ A' : ℝ}
    (hβ : ∀ (d : ℤ), m₀ ≤ d → ∀ k ∈ kzero v,
      ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ Cβ * qR v ^ (A' * ((d : ℝ) - m₀)))
    (s : ℂ) (dn : ℤ × ℤ) (hd : m₀ ≤ dn.1) {k : G} (hk : k ∈ kzero v) :
    ‖rsIntegrand W g₃ W₂ s (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
      shellPointwise v t C Cβ A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn := by
  have hq := (qR_pos v).le
  have hW1 := (gauge_shell hϖ hπ hg hm₀ dn hk).2
  have hW2 : ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤ Cβ * qR v ^ (A' * ((dn.1 : ℝ) - m₀)) :=
    hβ dn.1 hd k hk
  unfold rsIntegrand shellPointwise
  rw [norm_mul, norm_mul, hWW', norm_partner_shell_eq hπ ω₂ hW₂Z, norm_cpow_shell hϖ hπ s dn hk]
  have hρn : 0 ≤ ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 := zpow_nonneg (norm_nonneg _) _
  calc ‖W' (iotaGL (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖ *
          (‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * ‖W₂ (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖) *
          qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2))
      ≤ (|C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2))) *
          (‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * (Cβ * qR v ^ (A' * ((dn.1 : ℝ) - m₀)))) *
          qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq _)
        exact mul_le_mul hW1 (mul_le_mul_of_nonneg_left hW2 hρn) (mul_nonneg hρn (norm_nonneg _))
          (mul_nonneg (abs_nonneg C) (zpow_nonneg hq _))
    _ = |C| * Cβ * (qR v ^ ((t : ℤ) * (dn.1 + dn.2)) *
          (‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * qR v ^ (A' * ((dn.1 : ℝ) - m₀))) *
          qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2))) := by ring

theorem rsIntegrand_shell_eq_zero
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W W' : LocalGL3 v → ℂ} {g₃ : LocalGL3 v}
    (hWW' : ∀ g : G, W (iotaGL g * g₃) = W' (iotaGL g))
    {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d) (W₂ : G → ℂ) (s : ℂ) (dn : ℤ × ℤ)
    (hmn : ¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2)) {k : G} (hk : k ∈ kzero v) :
    rsIntegrand W g₃ W₂ s (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0 := by
  unfold rsIntegrand
  rw [hWW', (gauge_shell hϖ hπ hg hm₀ dn hk).1 hmn, zero_mul, zero_mul]

end Assembly

end RCg
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal Topology

namespace RCp

noncomputable section

section Generic

theorem isLocallyConstant_of_mul_invariant {M X : Type*} [TopologicalSpace M] [Group M] [ContinuousMul M]
    (U : Set M) (hU : IsOpen U) (h1 : (1 : M) ∈ U) (f : M → X) (hf : ∀ x, ∀ h ∈ U, f (x * h) = f x) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun h => x * h) '' U) := isOpenMap_mul_left x U hU
  have hmem : x ∈ (fun h => x * h) '' U := ⟨1, h1, mul_one x⟩
  filter_upwards [hopen.mem_nhds hmem] with y hy
  obtain ⟨h, hh, rfl⟩ := hy
  exact hf x h hh

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem setIntegral_eq_setIntegral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulLeftInvariant] {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (k₀ : G) (hST : ∀ y, y ∈ T ↔ k₀⁻¹ * y ∈ S) (f : G → E) :
    ∫ y in T, f y ∂μ = ∫ x in S, f (k₀ * x) ∂μ := by
  rw [← integral_indicator hT, ← integral_indicator hS]
  have hpt : ∀ x, S.indicator (fun x => f (k₀ * x)) x = T.indicator f (k₀ * x) := by
    intro x
    by_cases hx : x ∈ S
    · have : k₀ * x ∈ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem this]
    · have : k₀ * x ∉ T := by rw [hST, inv_mul_cancel_left]; exact hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]
  simp_rw [hpt]
  exact (integral_mul_left_eq_self _ k₀).symm

theorem setIntegral_subgroup_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (hH : MeasurableSet (H : Set G))
    {k₀ : G} (hk₀ : k₀ ∈ H) (f : G → E) :
    ∫ x in (H : Set G), f (k₀ * x) ∂μ = ∫ x in (H : Set G), f x ∂μ := by
  refine (setIntegral_eq_setIntegral_comp_mul_left μ hH hH k₀ (fun y => ?_) f).symm
  simp only [SetLike.mem_coe]
  constructor
  · intro hy; exact H.mul_mem (H.inv_mem hk₀) hy
  · intro hy; simpa using H.mul_mem hk₀ hy

omit [MeasurableSpace G] [BorelSpace G] in

theorem continuous_of_rightInvariant {X : Type*} [TopologicalSpace X] {U : Subgroup G}
    (hU : IsOpen (U : Set G)) {f : G → X} (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f :=
  (isLocallyConstant_of_mul_invariant (U : Set G) hU U.one_mem f fun x h hh => hf h hh x).continuous

end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G₂" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

scoped instance borelSpace_units_adic : BorelSpace (HeightOneSpectrum.adicCompletion K v)ˣ := borelSpace_units

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

private scoped instance _root_.RCp.secondCountableTopology_localGL : SecondCountableTopology G₂ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

p2m_export "RCp" "secondCountableTopology_localGL"
scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G₂ := locallyCompactSpace_localGL K v

private abbrev _root_.RCp.kzero : Subgroup G₂ := AdelicDock.localLevelOne (𝓞 K) K v ⊤

p2m_export "RCp" "kzero"

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G₂) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G₂) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((kzero K v : Subgroup G₂) : Set G₂) = localIntegralSet K v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

private theorem _root_.RCp.isOpen_kzero : IsOpen ((kzero K v : Subgroup G₂) : Set G₂) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet K v

p2m_export "RCp" "isOpen_kzero"
private theorem _root_.RCp.isCompact_kzero : IsCompact ((kzero K v : Subgroup G₂) : Set G₂) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet K v

p2m_export "RCp" "isCompact_kzero"

theorem diagUnitGL2_mem_kzero {u : (HeightOneSpectrum.adicCompletion K v)ˣ} (hu : Valued.v (u : F) = 1) :
    diagUnitGL2 u ∈ kzero K v := by
  have hu' : Valued.v ((u⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  have hinv : (diagUnitGL2 u)⁻¹ = diagUnitGL2 u⁻¹ := by
    rw [← diagHom_apply, ← diagHom_apply, map_inv]
  rw [mem_kzero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnitGL2]
    fin_cases i <;> fin_cases j <;> simp [hu]
  · rw [hinv, HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagUnitGL2]
    have hu'' : (Valued.v (u : F))⁻¹ ≤ 1 := by rw [hu, inv_one]
    fin_cases i <;> fin_cases j <;> simp [hu'']

theorem valuation_det_of_mem_kzero {k : G₂} (hk : k ∈ kzero K v) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = 1 := by
  rw [mem_kzero_iff] at hk
  have hint : ∀ (m : Mat), (∀ i j, m i j ∈ (O)) → Valued.v m.det ≤ 1 := by
    intro m hm
    rw [Matrix.det_fin_two]
    have h := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm i j)
    calc Valued.v (m 0 0 * m 1 1 - m 0 1 * m 1 0)
        ≤ max (Valued.v (m 0 0 * m 1 1)) (Valued.v (m 0 1 * m 1 0)) := Valuation.map_sub _ _ _
      _ ≤ 1 := by
          refine max_le ?_ ?_
          · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
          · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)
  have h1 := hint _ hk.1
  have h2 := hint _ hk.2
  have hprod : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have : Valued.v ((k : Mat).det) * Valued.v (((k⁻¹ : G₂) : Mat).det) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [hprod] at this
  exact lt_irrefl _ this

variable (b : ℕ) (Kb : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))
  (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 K) K v ⊤)
  (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 K) K v ⊤,
    (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)

include hKbc in

theorem conj_diagUnitGL2_mem {k : G₂} (hk : k ∈ kzero K v) {h : (HeightOneSpectrum.adicCompletion K v)ˣ}
    (hh : h ∈ higherUnitsAt K v b) : k⁻¹ * diagUnitGL2 h * k ∈ Kb := by
  have hh1 : Valued.v (h : F) = 1 := hh.1
  have hmem : k⁻¹ * diagUnitGL2 h * k ∈ kzero K v :=
    (kzero K v).mul_mem ((kzero K v).mul_mem ((kzero K v).inv_mem hk) (diagUnitGL2_mem_kzero K v hh1)) hk
  refine hKbc _ hmem fun i j => ?_

  have hk' := (mem_kzero_iff K v k).mp hk
  have hkint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk'.1 i j)
  have hkiint := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hk'.2 i j)
  have hexp : (((k⁻¹ * diagUnitGL2 h * k : G₂) : Mat) - 1) =
      ((k⁻¹ : G₂) : Mat) * (((diagUnitGL2 h : G₂) : Mat) - 1) * (k : Mat) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    have : ((k⁻¹ : G₂) : Mat) * (k : Mat) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this]
    push_cast
    ring_nf

  have hd : ∀ i j, Valued.v ((((diagUnitGL2 h : G₂) : Mat) - 1) i j) ≤ WithZero.exp (-(b : ℤ)) := by
    intro i j
    rcases hh.2 with hb0 | hle
    · subst hb0
      fin_cases i <;> fin_cases j <;> simp
      calc Valued.v ((h : F) - 1) ≤ max (Valued.v (h : F)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
        _ ≤ 1 := by rw [hh1, map_one, max_self]
    · have hle' : Valued.v ((h : F) - 1) ≤ (WithZero.exp (b : ℤ))⁻¹ := by rwa [← WithZero.exp_neg]
      fin_cases i <;> fin_cases j <;> simp [hle']
  rw [hexp]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]

  have hterm : ∀ i l m j, Valued.v (((k⁻¹ : G₂) : Mat) i l * (((diagUnitGL2 h : G₂) : Mat) - 1) l m * (k : Mat) m j)
      ≤ WithZero.exp (-(b : ℤ)) := by
    intro i l m j
    rw [map_mul, map_mul]
    calc Valued.v (((k⁻¹ : G₂) : Mat) i l) * Valued.v ((((diagUnitGL2 h : G₂) : Mat) - 1) l m) * Valued.v ((k : Mat) m j)
        ≤ 1 * WithZero.exp (-(b : ℤ)) * 1 := by
          gcongr
          · exact hkiint i l
          · exact hd l m
          · exact hkint m j
      _ = WithZero.exp (-(b : ℤ)) := by rw [one_mul, mul_one]
  rw [add_mul, add_mul]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · exact (Valuation.map_add _ _ _).trans (max_le (hterm i 0 0 j) (hterm i 1 0 j))
  · exact (Valuation.map_add _ _ _).trans (max_le (hterm i 0 1 j) (hterm i 1 1 j))

scoped instance compactSpace_kzero : CompactSpace (kzero K v) :=
  isCompact_iff_compactSpace.mp (isCompact_kzero K v)

abbrev KbIn : Subgroup (kzero K v) := Kb.subgroupOf (kzero K v)

abbrev Q : Type := (kzero K v) ⧸ KbIn K v Kb

theorem finite_Q (hKb : IsOpen (Kb : Set G₂)) : Finite (Q K v Kb) :=
  Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hKb)

def rq (q : Q K v Kb) : G₂ := ((Quotient.out q : kzero K v) : G₂)

theorem rq_mem (q : Q K v Kb) : rq K v Kb q ∈ kzero K v := (Quotient.out q).2

def coset (q : Q K v Kb) : Set G₂ := {g | (rq K v Kb q)⁻¹ * g ∈ Kb}

theorem isOpen_coset (hKb : IsOpen (Kb : Set G₂)) (q : Q K v Kb) : IsOpen (coset K v Kb q) :=
  hKb.preimage (continuous_const.mul continuous_id)

include hKbK in
theorem coset_subset (q : Q K v Kb) : coset K v Kb q ⊆ (kzero K v : Set G₂) := by
  intro g hg
  have h1 : (rq K v Kb q)⁻¹ * g ∈ kzero K v := hKbK hg
  have : g = rq K v Kb q * ((rq K v Kb q)⁻¹ * g) := by rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, this]
  exact (kzero K v).mul_mem (rq_mem K v Kb q) h1

theorem mem_coset_iff_mk_eq {g : G₂} (hg : g ∈ kzero K v) (q : Q K v Kb) :
    g ∈ coset K v Kb q ↔ (QuotientGroup.mk (⟨g, hg⟩ : kzero K v) : Q K v Kb) = q := by
  have hq : (QuotientGroup.mk (Quotient.out q : kzero K v) : Q K v Kb) = q := Quotient.out_eq q
  conv_rhs => rw [← hq]
  rw [eq_comm, QuotientGroup.eq]
  rfl

include hKbK in
theorem pairwise_disjoint_coset : Pairwise (fun q q' : Q K v Kb => Disjoint (coset K v Kb q) (coset K v Kb q')) := by
  intro q q' hqq'
  rw [Set.disjoint_left]
  intro g hg hg'
  have hgK : g ∈ kzero K v := coset_subset K v Kb hKbK q hg
  apply hqq'
  rw [← (mem_coset_iff_mk_eq K v Kb hgK q).mp hg, ← (mem_coset_iff_mk_eq K v Kb hgK q').mp hg']

include hKbK in
theorem iUnion_coset : (⋃ q, coset K v Kb q) = (kzero K v : Set G₂) := by
  apply subset_antisymm
  · exact Set.iUnion_subset fun q => coset_subset K v Kb hKbK q
  · intro g hg
    rw [Set.mem_iUnion]
    exact ⟨QuotientGroup.mk (⟨g, hg⟩ : kzero K v), (mem_coset_iff_mk_eq K v Kb hg _).mpr rfl⟩

include hKbK in

theorem setIntegral_kzero_eq_sum [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂))
    (μ : Measure G₂) [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : G₂ → E)
    (hf : IntegrableOn f (kzero K v : Set G₂) μ) :
    ∫ x in (kzero K v : Set G₂), f x ∂μ = ∑ q : Q K v Kb, ∫ x in (Kb : Set G₂), f (rq K v Kb q * x) ∂μ := by
  have hU : (kzero K v : Set G₂) = ⋃ q ∈ (Finset.univ : Finset (Q K v Kb)), coset K v Kb q := by
    rw [← iUnion_coset K v Kb hKbK]
    simp
  rw [hU, integral_biUnion_finset _ (fun q _ => (isOpen_coset K v Kb hKb q).measurableSet)
    (fun q _ q' _ h => pairwise_disjoint_coset K v Kb hKbK h)
    (fun q _ => hf.mono_set (coset_subset K v Kb hKbK q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact setIntegral_eq_setIntegral_comp_mul_left μ hKb.measurableSet (isOpen_coset K v Kb hKb q).measurableSet
    (rq K v Kb q) (fun y => Iff.rfl) f

variable (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
  (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)

abbrev piU : (HeightOneSpectrum.adicCompletion K v)ˣ := Units.mk0 (algebraMap _ F ϖ) hπ

def rep (dn : ℤ × ℤ) : G₂ :=
  scalarPi (algebraMap _ F ϖ) hπ ^ dn.2 * diagZ (algebraMap _ F ϖ) hπ dn.1

theorem diagZ_eq_diagUnitGL2 (d : ℤ) : diagZ (algebraMap _ F ϖ) hπ d = diagUnitGL2 (piU K v ϖ hπ ^ d) := by
  refine Units.ext ?_
  rw [coe_diagUnitGL2]
  simp [diagZ, Units.val_zpow_eq_zpow_val]

theorem rep_mul_diagUnitGL2 (dn : ℤ × ℤ) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    rep K v ϖ hπ dn * diagUnitGL2 u =
      scalarPi (algebraMap _ F ϖ) hπ ^ dn.2 * diagUnitGL2 (piU K v ϖ hπ ^ dn.1 * u) := by
  rw [rep, diagZ_eq_diagUnitGL2, mul_assoc, ← diagHom_apply, ← diagHom_apply, ← diagHom_apply, ← map_mul]

theorem val_det_scalarPi :
    ((Matrix.GeneralLinearGroup.det (scalarPi (algebraMap _ F ϖ) hπ) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ * algebraMap _ F ϖ := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [scalarPi, Matrix.det_fin_two]

theorem val_det_diagZ (d : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ (algebraMap _ F ϖ) hπ d) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ ^ d := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [diagZ, Matrix.det_fin_two]

theorem val_det_rep (dn : ℤ × ℤ) :
    ((Matrix.GeneralLinearGroup.det (rep K v ϖ hπ dn) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)
      = algebraMap _ F ϖ ^ (dn.1 + 2 * dn.2) := by
  rw [rep, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, val_det_scalarPi, val_det_diagZ,
    ← pow_two, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπ]
  congr 1
  push_cast
  ring

theorem norm_uniformizer (hϖ : Valued.v (algebraMap _ F ϖ) = WithZero.exp (-1 : ℤ)) :
    ‖algebraMap _ F ϖ‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  simp

theorem norm_eq_one_of_valuation_eq_one {x : F} (hx : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

private theorem _root_.RCp.coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm K v x, coe_nnnorm]

p2m_export "RCp" "coe_modulus_eq_norm"

theorem modulus_det_rep (hϖ : Valued.v (algebraMap _ F ϖ) = WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    ((modulus ((Matrix.GeneralLinearGroup.det (rep K v ϖ hπ dn) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ)
        : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (((-(dn.1 + 2 * dn.2) : ℤ) : ℂ)) := by
  rw [coe_modulus_eq_norm, val_det_rep, norm_zpow, norm_uniformizer K v ϖ hϖ, inv_zpow', Complex.ofReal_zpow,
    ← Complex.cpow_intCast]
  push_cast
  rfl

theorem modulus_det_mul_of_mem_kzero (a : G₂) {k : G₂} (hk : k ∈ kzero K v) :
    (modulus ((Matrix.GeneralLinearGroup.det (a * k) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) =
      (modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) := by
  rw [map_mul, Units.val_mul, modulus_mul, NNReal.coe_mul, coe_modulus_eq_norm K v ((Matrix.GeneralLinearGroup.det k : _ˣ) : F),
    norm_eq_one_of_valuation_eq_one K v (valuation_det_of_mem_kzero K v hk), mul_one]

def sph : Set (HeightOneSpectrum.adicCompletion K v)ˣ := {u | Valued.v (u : F) = 1}

theorem val_eq_one_iff_norm_eq_one (x : F) : Valued.v x = 1 ↔ ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def]
  have h1 : (1 : ℝ) = ((1 : NNReal) : ℝ) := rfl
  rw [h1, NNReal.coe_inj, WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
    (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v))]

theorem image_val_sph : Units.val '' sph K v = Metric.sphere (0 : F) 1 := by
  ext x
  simp only [Set.mem_image, sph, Set.mem_setOf_eq, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (val_eq_one_iff_norm_eq_one K v _).mp hu
  · intro hx
    have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
    exact ⟨Units.mk0 x hx0, (val_eq_one_iff_norm_eq_one K v _).mpr hx, rfl⟩

theorem sph_eq_preimage : sph K v = Units.val ⁻¹' Metric.sphere (0 : F) 1 := by
  ext u
  simp only [sph, Set.mem_setOf_eq, Set.mem_preimage, mem_sphere_zero_iff_norm]
  exact val_eq_one_iff_norm_eq_one K v _

theorem isOpen_sph : IsOpen (sph K v) := by
  rw [sph_eq_preimage]
  exact (IsUltrametricDist.isOpen_sphere (0 : F) one_ne_zero).preimage Units.continuous_val

theorem isCompact_sph : IsCompact (sph K v) := by
  rw [Units.isEmbedding_val₀.isCompact_iff, image_val_sph]
  exact isCompact_sphere _ _

theorem one_mem_sph : (1 : (HeightOneSpectrum.adicCompletion K v)ˣ) ∈ sph K v := by
  simp [sph]

theorem measurableSet_sph : MeasurableSet (sph K v) := (isOpen_sph K v).measurableSet

theorem isOpen_higherUnitsAt : IsOpen (higherUnitsAt K v b) := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have : higherUnitsAt K v 0 = sph K v := by
      ext u; rw [mem_higherUnitsAt_zero_iff]; rfl
    rw [this]; exact isOpen_sph K v
  ·
    set r : ℝ := ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp (-(b : ℤ))) : NNReal) : ℝ)
      with hr
    have hrpos : 0 < r := by
      rw [hr]
      exact_mod_cast WithZeroMulInt.toNNReal_pos (NumberField.HeightOneSpectrum.absNorm_ne_zero v) WithZero.exp_ne_zero
    have hset : higherUnitsAt K v b = sph K v ∩ Units.val ⁻¹' Metric.closedBall (1 : F) r := by
      ext u
      simp only [mem_higherUnitsAt_iff, sph, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
      have hb0 : b ≠ 0 := by omega
      simp only [hb0, false_or]
      apply and_congr Iff.rfl
      rw [NumberField.FinitePlace.norm_def, hr, NNReal.coe_le_coe]
      exact ((WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le).symm
    rw [hset]
    exact (isOpen_sph K v).inter
      ((IsUltrametricDist.isOpen_closedBall (1 : F) hrpos.ne').preimage Units.continuous_val)

theorem continuous_of_higherUnits_invariant {X : Type*} [TopologicalSpace X]
    (f : (HeightOneSpectrum.adicCompletion K v)ˣ → X)
    (hf : ∀ u, ∀ h ∈ higherUnitsAt K v b, f (u * h) = f u) : Continuous f :=
  (isLocallyConstant_of_mul_invariant (higherUnitsAt K v b) (isOpen_higherUnitsAt K v b)
    (one_mem_higherUnitsAt K v b) f hf).continuous

theorem continuous_char {η : (HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ} {c : ℕ}
    (hη : HasConductorExponentAt K v η c) (hcb : c ≤ b) :
    Continuous fun u => ((η u : ℂˣ) : ℂ) := by
  refine continuous_of_higherUnits_invariant K v b _ fun u h hh => ?_
  have h1 : η h = 1 := hη.1 h (higherUnitsAt_antitone K v hcb hh)
  simp [map_mul, h1]

theorem continuous_diagUnitGL2 : Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => (diagUnitGL2 u : G₂) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_val
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const
  · have hinv : ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, ((diagUnitGL2 u : G₂)⁻¹ : G₂) = diagUnitGL2 u⁻¹ := by
      intro u; rw [← diagHom_apply, ← diagHom_apply, map_inv]
    have hfun : (fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((diagUnitGL2 u : G₂)⁻¹ : Units _).val) =
        fun u => ((diagUnitGL2 u⁻¹ : G₂) : Mat) := by
      funext u; rw [← hinv u]
    change Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((diagUnitGL2 u : G₂)⁻¹ : Units _).val
    rw [hfun]
    refine continuous_matrix fun i j => ?_
    have hci : Continuous fun u : (HeightOneSpectrum.adicCompletion K v)ˣ => ((u⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) :=
      Units.continuous_coe_inv
    fin_cases i <;> fin_cases j
    · simpa using hci
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using continuous_const

section Vanishing

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

def Sshell (a : G₂) : ℂ := ∫ k in (kzero K v : Set G₂), A (a * k) * B (a * k) ∂μ₂

def αfun (a r : G₂) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) : ℂ :=
  ∫ k in (Kb : Set G₂), A (a * diagUnitGL2 u * (r * k)) ∂μ₂

def βfun (a r : G₂) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) : ℂ := B (a * diagUnitGL2 u * r)

variable {A B}
variable (hAc : Continuous A) (hBc : Continuous B)
  (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v), B (g * k) = B g)
  [μ₂.IsHaarMeasure]

include hAc hBc in
theorem continuous_AB (a x : G₂) : Continuous fun k : G₂ => A (a * (x * k)) * B (a * (x * k)) :=
  (hAc.comp (continuous_const.mul (continuous_const.mul continuous_id))).mul
    (hBc.comp (continuous_const.mul (continuous_const.mul continuous_id)))

include hAc hBc in
theorem integrableOn_AB (a x : G₂) :
    IntegrableOn (fun k : G₂ => A (a * (x * k)) * B (a * (x * k))) (kzero K v : Set G₂) μ₂ :=
  (continuous_AB K v hAc hBc a x).continuousOn.integrableOn_compact (isCompact_kzero K v)

theorem setIntegral_unit_eq_Sshell (a : G₂) {u : (HeightOneSpectrum.adicCompletion K v)ˣ} (hu : Valued.v (u : F) = 1) :
    ∫ k in (kzero K v : Set G₂), A (a * (diagUnitGL2 u * k)) * B (a * (diagUnitGL2 u * k)) ∂μ₂ = Sshell K v A B μ₂ a :=
  setIntegral_subgroup_comp_mul_left μ₂ (kzero K v) (isOpen_kzero K v).measurableSet
    (diagUnitGL2_mem_kzero K v hu) (fun k => A (a * k) * B (a * k))

include hKbK hAc hBc hB in

theorem setIntegral_unit_eq_sum [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂)) (a : G₂)
    (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ∫ k in (kzero K v : Set G₂), A (a * (diagUnitGL2 u * k)) * B (a * (diagUnitGL2 u * k)) ∂μ₂ =
      ∑ q : Q K v Kb, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u := by
  rw [setIntegral_kzero_eq_sum K v Kb hKbK hKb μ₂ _ (integrableOn_AB K v μ₂ hAc hBc a (diagUnitGL2 u))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [αfun, βfun, ← integral_mul_const]
  refine setIntegral_congr_fun hKb.measurableSet fun k hk => ?_
  have h1 : a * (diagUnitGL2 u * (rq K v Kb q * k)) = a * diagUnitGL2 u * (rq K v Kb q * k) := by group
  have h2 : a * diagUnitGL2 u * (rq K v Kb q * k) = a * diagUnitGL2 u * rq K v Kb q * k := by group
  rw [h1, h2, hB k hk]

omit [μ₂.IsHaarMeasure] in
include hKbc hB in

theorem βfun_mul (a : G₂) {r : G₂} (hr : r ∈ kzero K v) (u : (HeightOneSpectrum.adicCompletion K v)ˣ)
    {h : (HeightOneSpectrum.adicCompletion K v)ˣ} (hh : h ∈ higherUnitsAt K v b) :
    βfun K v B a r (u * h) = βfun K v B a r u := by
  have hκ := conj_diagUnitGL2_mem K v b Kb hKbc hr hh
  rw [βfun, βfun, ← diagHom_apply, map_mul, diagHom_apply, diagHom_apply]
  have : a * (diagUnitGL2 u * diagUnitGL2 h) * r = a * diagUnitGL2 u * r * (r⁻¹ * diagUnitGL2 h * r) := by group
  rw [this, hB _ hκ]

include hKbc in

theorem αfun_mul (hKb : IsOpen (Kb : Set G₂)) (a : G₂) {r : G₂} (hr : r ∈ kzero K v)
    (u : (HeightOneSpectrum.adicCompletion K v)ˣ)
    {h : (HeightOneSpectrum.adicCompletion K v)ˣ} (hh : h ∈ higherUnitsAt K v b) :
    αfun K v Kb A μ₂ a r (u * h) = αfun K v Kb A μ₂ a r u := by
  have hκ := conj_diagUnitGL2_mem K v b Kb hKbc hr hh
  rw [αfun, αfun, ← diagHom_apply, map_mul, diagHom_apply, diagHom_apply]
  have hpt : ∀ k, a * (diagUnitGL2 u * diagUnitGL2 h) * (r * k) =
      a * diagUnitGL2 u * (r * ((r⁻¹ * diagUnitGL2 h * r) * k)) := fun k => by group
  simp_rw [hpt]
  exact setIntegral_subgroup_comp_mul_left μ₂ Kb hKb.measurableSet hκ (fun k => A (a * diagUnitGL2 u * (r * k)))

include hKbc hB in
theorem continuous_βfun (a : G₂) {r : G₂} (hr : r ∈ kzero K v) : Continuous (βfun K v B a r) :=
  continuous_of_higherUnits_invariant K v b _ fun u _ hh => βfun_mul K v b Kb hKbc hB a hr u hh

include hKbc in
theorem continuous_αfun (hKb : IsOpen (Kb : Set G₂)) (a : G₂) {r : G₂} (hr : r ∈ kzero K v) :
    Continuous (αfun K v Kb A μ₂ a r) :=
  continuous_of_higherUnits_invariant K v b _ fun u _ hh => αfun_mul K v b Kb hKbc μ₂ hKb a hr u hh

theorem measure_sph_ne (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure] :
    ν (sph K v) ≠ 0 ∧ ν (sph K v) ≠ ⊤ :=
  ⟨((isOpen_sph K v).measure_pos ν ⟨1, one_mem_sph K v⟩).ne', (isCompact_sph K v).measure_lt_top.ne⟩

include hKbK hKbc hAc hBc hB in

theorem Sshell_eq_zero [Fintype (Q K v Kb)] (hKb : IsOpen (Kb : Set G₂))
    (ν : Measure (HeightOneSpectrum.adicCompletion K v)ˣ) [ν.IsHaarMeasure]
    (S : Finset ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ))
    (hS1 : ∀ η ∈ S, ∃ m ≤ b, HasConductorExponentAt K v η m)
    (hS3 : ∀ g : (HeightOneSpectrum.adicCompletion K v)ˣ → ℂ,
      (∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 →
        ∀ h ∈ higherUnitsAt K v b, g (u * h) = g u) →
      ∃ c : ((HeightOneSpectrum.adicCompletion K v)ˣ →* ℂˣ) → ℂ,
        ∀ u : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (u : F) = 1 →
          g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ))
    (a : G₂)
    (hvan : ∀ q : Q K v Kb, ∀ η ∈ S,
      ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ) ∂ν = 0) :
    Sshell K v A B μ₂ a = 0 := by
  have hSph := measure_sph_ne K v ν
  have hreal : ν.real (sph K v) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]; exact hSph

  have hq : ∀ q : Q K v Kb,
      ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν = 0 := by
    intro q
    have hr := rq_mem K v Kb q
    obtain ⟨c, hc⟩ := hS3 (βfun K v B a (rq K v Kb q)) fun u _ h hh => βfun_mul K v b Kb hKbc hB a hr u hh
    have hαc := continuous_αfun K v b Kb hKbc μ₂ hKb a hr (A := A)
    calc ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν
        = ∫ u in sph K v, ∑ η ∈ S, c η * (αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ)) ∂ν := by
          refine setIntegral_congr_fun (measurableSet_sph K v) fun u hu => ?_
          rw [hc u hu, Finset.mul_sum]
          refine Finset.sum_congr rfl fun η _ => ?_
          ring
      _ = ∑ η ∈ S, ∫ u in sph K v, c η * (αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ)) ∂ν := by
          refine integral_finsetSum _ fun η hη => ?_
          obtain ⟨m, hmb, hηm⟩ := hS1 η hη
          exact ((hαc.mul (continuous_char K v b hηm hmb)).continuousOn.integrableOn_compact
            (isCompact_sph K v)).const_mul (c η)
      _ = ∑ η ∈ S, c η * ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * ((η u : ℂˣ) : ℂ) ∂ν := by
          refine Finset.sum_congr rfl fun η _ => ?_
          exact integral_const_mul _ _
      _ = 0 := by
          refine Finset.sum_eq_zero fun η hη => ?_
          rw [hvan q η hη, mul_zero]

  have key : ν.real (sph K v) • Sshell K v A B μ₂ a = 0 := by
    rw [← setIntegral_const]
    calc ∫ _ in sph K v, Sshell K v A B μ₂ a ∂ν
        = ∫ u in sph K v, ∑ q : Q K v Kb, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν := by
          refine setIntegral_congr_fun (measurableSet_sph K v) fun u hu => ?_
          rw [← setIntegral_unit_eq_Sshell K v μ₂ a hu, setIntegral_unit_eq_sum K v Kb hKbK μ₂ hAc hBc hB hKb a u]
      _ = ∑ q : Q K v Kb, ∫ u in sph K v, αfun K v Kb A μ₂ a (rq K v Kb q) u * βfun K v B a (rq K v Kb q) u ∂ν := by
          refine integral_finsetSum _ fun q _ => ?_
          have hr := rq_mem K v Kb q
          exact ((continuous_αfun K v b Kb hKbc μ₂ hKb a hr (A := A)).mul
            (continuous_βfun K v b Kb hKbc hB a hr)).continuousOn.integrableOn_compact (isCompact_sph K v)
      _ = 0 := Finset.sum_eq_zero fun q _ => hq q
  exact (smul_eq_zero.mp key).resolve_left hreal

end Vanishing
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

section Assembly

variable (A B : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ)
  (μ₂ : Measure (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)))

def fS (s : ℂ) (g : G₂) : ℂ :=
  (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)

abbrev qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem qC_ne_zero : qC K v ≠ 0 := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

theorem log_qC_im : (Complex.log (qC K v)).im = 0 := by
  rw [qC, show ((Ideal.absNorm v.asIdeal : ℂ)) = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) by norm_cast,
    ← Complex.ofReal_log (by positivity), Complex.ofReal_im]

theorem qC_cpow_cpow (y z : ℂ) (hy : y.im = 0) : ((qC K v) ^ y) ^ z = (qC K v) ^ (y * z) := by
  rw [Complex.cpow_mul]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos]
  · rw [Complex.mul_im, log_qC_im, hy]; simp [Real.pi_pos.le]

variable {A B}

theorem continuous_modulus_det :
    Continuous fun g : G₂ =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) := by
  have h : (fun g : G₂ => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ))
      = fun g : G₂ => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [h]
  exact Complex.continuous_ofReal.comp ((Units.continuous_val.matrix_det).norm)

theorem measurable_fS (hAc : Continuous A) (hBc : Continuous B) (s : ℂ) : Measurable (fS K v A B s) := by
  unfold fS
  exact (hAc.measurable.mul hBc.measurable).mul ((continuous_modulus_det K v).measurable.pow_const _)

theorem exists_eq_unipotent {x : G₂} (hx : x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range) :
    ∃ y : F, x = unipotent y := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨Multiplicative.toAdd z, Units.ext ?_⟩
  simp [unipotentGL2Hom, unipotent, unipotentGL2_coe]

theorem det_unipotent (y : F) : Matrix.GeneralLinearGroup.det (unipotent y : G₂) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [unipotent, Matrix.det_fin_two]

theorem fS_unip (hAB : ∀ (x : F) (g : G₂), A (unipotent x * g) * B (unipotent x * g) = A g * B g) (s : ℂ) :
    ∀ x ∈ (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range, ∀ g : G₂,
      fS K v A B s (x * g) = fS K v A B s g := by
  intro x hx g
  obtain ⟨y, rfl⟩ := exists_eq_unipotent K v hx
  rw [fS, fS, hAB, map_mul, det_unipotent, one_mul]

theorem setIntegral_fS_mul (s : ℂ) (a : G₂) :
    ∫ k in (kzero K v : Set G₂), fS K v A B s (a * k) ∂μ₂ =
      ((modulus ((Matrix.GeneralLinearGroup.det a : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2) *
        Sshell K v A B μ₂ a := by
  rw [Sshell, ← integral_const_mul]
  refine setIntegral_congr_fun (isOpen_kzero K v).measurableSet fun k hk => ?_
  rw [fS, modulus_det_mul_of_mem_kzero K v a hk, mul_comm]

variable (ϖ' : HeightOneSpectrum.adicCompletionIntegers K v)
  (hπ' : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ' ≠ 0)

def eExp (dn : ℤ × ℤ) : ℤ := dn.1 + 2 * dn.2

def mShift (T' : Finset (ℤ × ℤ)) : ℤ := ∑ dn ∈ T', |eExp dn|

theorem mShift_add_nonneg (T' : Finset (ℤ × ℤ)) {dn : ℤ × ℤ} (hdn : dn ∈ T') : 0 ≤ mShift T' + eExp dn := by
  have h1 : |eExp dn| ≤ mShift T' :=
    Finset.single_le_sum (f := fun dn => |eExp dn|) (fun _ _ => abs_nonneg _) hdn
  have h2 : -eExp dn ≤ |eExp dn| := neg_le_abs _
  omega

def coef (w : ℤ × ℤ → ℝ) (dn : ℤ × ℤ) : ℂ :=
  ((w dn : ℝ) : ℂ) * Sshell K v A B μ₂ (rep K v ϖ' hπ' dn) * (qC K v) ^ (((eExp dn : ℤ) : ℂ) / 2)

def poly (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ)) : Polynomial ℂ :=
  ∑ dn ∈ T', Polynomial.C (coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn) * Polynomial.X ^ (mShift T' + eExp dn).toNat

theorem shell_term_eq (hϖ : Valued.v (algebraMap _ F ϖ') = WithZero.exp (-1 : ℤ)) (w : ℤ × ℤ → ℝ) (s : ℂ) (dn : ℤ × ℤ) :
    ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂ =
      coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
  rw [setIntegral_fS_mul, modulus_det_rep K v ϖ' hπ' hϖ, coef, qC_cpow_cpow]
  · have hexp : (((-(dn.1 + 2 * dn.2) : ℤ) : ℂ)) * (s - 1 / 2) =
        ((eExp dn : ℤ) : ℂ) / 2 + (-((eExp dn : ℤ) : ℂ) * s) := by
      simp only [eExp]; push_cast; ring
    rw [hexp, Complex.cpow_add _ _ (qC_ne_zero K v)]
    ring
  · push_cast; simp

theorem poly_term_eq (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ)) (s : ℂ) {dn : ℤ × ℤ} (hdn : dn ∈ T') :
    (qC K v) ^ ((mShift T' : ℂ) * s) *
        (coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * ((qC K v) ^ (-s)) ^ (mShift T' + eExp dn).toNat) =
      coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
  have hN : (((mShift T' + eExp dn).toNat : ℕ) : ℂ) = ((mShift T' : ℤ) : ℂ) + ((eExp dn : ℤ) : ℂ) := by
    have := Int.toNat_of_nonneg (mShift_add_nonneg T' hdn)
    exact_mod_cast this
  rw [← Complex.cpow_nat_mul, hN, mul_left_comm, ← Complex.cpow_add _ _ (qC_ne_zero K v)]
  congr 2
  ring

theorem finish (hϖ : Valued.v (algebraMap _ F ϖ') = WithZero.exp (-1 : ℤ)) (w : ℤ × ℤ → ℝ) (T' : Finset (ℤ × ℤ))
    (hS0 : ∀ dn : ℤ × ℤ, dn ∉ T' → Sshell K v A B μ₂ (rep K v ϖ' hπ' dn) = 0) (s Ψ : ℂ)
    (hHS : HasSum (fun dn : ℤ × ℤ =>
      ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂) Ψ) :
    Ψ = (qC K v) ^ ((mShift T' : ℂ) * s) * (poly K v μ₂ ϖ' hπ' (A := A) (B := B) w T').eval ((qC K v) ^ (-s)) := by
  have hfun : (fun dn : ℤ × ℤ =>
      ((w dn : ℝ) : ℂ) * ∫ k in (kzero K v : Set G₂), fS K v A B s (rep K v ϖ' hπ' dn * k) ∂μ₂) =
      fun dn => coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) := by
    funext dn; exact shell_term_eq K v μ₂ ϖ' hπ' hϖ w s dn
  rw [hfun] at hHS
  have hzero : ∀ dn ∉ T', coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s) = 0 := by
    intro dn hdn
    rw [coef, hS0 dn hdn]; ring
  have hfin : HasSum (fun dn => coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s))
      (∑ dn ∈ T', coef K v μ₂ ϖ' hπ' (A := A) (B := B) w dn * (qC K v) ^ (-((eExp dn : ℤ) : ℂ) * s)) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [hHS.unique hfin, poly, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dn hdn => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact (poly_term_eq K v μ₂ ϖ' hπ' w T' s hdn).symm

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg"

end RCp
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCu

open MeasureTheory
open scoped NNReal

variable (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

section UnitsMeasure

attribute [local instance] LanglandsTunnell.TateLocal.localBorel

theorem borelSpace_loc : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v

attribute [local instance] borelSpace_loc

theorem borelSpace_locUnits : BorelSpace (v.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have h : (inferInstance : TopologicalSpace (v.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) inferInstance :=
    Units.isEmbedding_val₀.eq_induced
  show MeasurableSpace.comap Units.val (borel (v.adicCompletion ℚ)) = borel (v.adicCompletion ℚ)ˣ
  exact ((congrArg (fun t => @borel (v.adicCompletion ℚ)ˣ t) h).trans borel_comap).symm

attribute [local instance] borelSpace_locUnits

theorem isAddHaarMeasure_selfDualHaarAt : (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2))
    • Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v) :
      Measure (v.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem isHaarMeasure_locMul :
    (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) :
      Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ v (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)

end UnitsMeasure
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

end RCu
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

namespace RCm

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

theorem qC_eq_qR : RCp.qC ℚ v = ((RCg.qR v : ℝ) : ℂ) := by
  rw [RCp.qC, RCg.qR_eq_natCast]; norm_cast

theorem norm_qC_cpow (z : ℂ) : ‖(RCp.qC ℚ v) ^ z‖ = RCg.qR v ^ z.re := by
  rw [qC_eq_qR, Complex.norm_cpow_eq_rpow_re_of_pos (RCg.qR_pos v)]

theorem cpow_ne_zero' {q : ℂ} (hq : q ≠ 0) (a : ℂ) : q ^ a ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _

theorem cpow_zpow (x : ℂ) (y : ℂ) (n : ℤ) : (x ^ y) ^ n = x ^ ((n : ℂ) * y) := by
  rw [Complex.cpow_int_mul]

theorem weight_identity (ωp : ℂ) (s : ℂ) (dn : ℤ × ℤ) :
    (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) * ωp ^ dn.2 =
      ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * ωp) ^ dn.2 *
        ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2) := by
  have hq := RCp.qC_ne_zero ℚ v
  rw [cpow_zpow, cpow_zpow, mul_zpow, ← Complex.cpow_intCast (RCp.qC ℚ v) dn.2]
  rw [← Complex.cpow_add _ _ hq]
  have : (RCp.qC ℚ v) ^ ((dn.1 : ℂ) * (3 / 2)) * ((RCp.qC ℚ v) ^ ((dn.2 : ℤ) : ℂ) * ωp ^ dn.2) *
      (RCp.qC ℚ v) ^ ((((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2 : ℤ) : ℂ) * -s) =
      (RCp.qC ℚ v) ^ ((dn.1 : ℂ) * (3 / 2) + ((dn.2 : ℤ) : ℂ) + (((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2 : ℤ) : ℂ) * -s) * ωp ^ dn.2 := by
    rw [Complex.cpow_add _ _ hq, Complex.cpow_add _ _ hq]; ring
  rw [this]
  congr 1
  congr 1
  push_cast
  ring

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCm

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem norm_fS_shell_le
    (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {A B : G → ℂ} {m₀ : ℤ} {t : ℕ} {CA : ℝ}
    (hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)))
    (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      B (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * B g)
    {Cβ A' : ℝ}
    (hβ : ∀ (d : ℤ), m₀ ≤ d → ∀ k ∈ RCg.kzero v,
      ‖B (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ Cβ * RCg.qR v ^ (A' * ((d : ℝ) - m₀)))
    (s : ℂ) (dn : ℤ × ℤ) (hd : m₀ ≤ dn.1) {k : G} (hk : k ∈ RCg.kzero v) :
    ‖RCp.fS ℚ v A B s (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
      RCg.shellPointwise v t CA Cβ A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn := by
  have hq := (RCg.qR_pos v).le
  have hW1 := (hsh dn k hk).2
  have hW1' : ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
      |CA| * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)) :=
    hW1.trans (mul_le_mul_of_nonneg_right (le_abs_self CA) (zpow_nonneg hq _))
  have hW2 : ‖B (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤ Cβ * RCg.qR v ^ (A' * ((dn.1 : ℝ) - m₀)) :=
    hβ dn.1 hd k hk
  unfold RCp.fS RCg.shellPointwise
  rw [norm_mul, norm_mul, RCg.norm_partner_shell_eq hπ ω₂ hW₂Z, RCg.norm_cpow_shell hϖ hπ s dn hk]
  have hρn : 0 ≤ ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 := zpow_nonneg (norm_nonneg _) _
  calc ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ *
          (‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * ‖B (diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖) *
          RCg.qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2))
      ≤ (|CA| * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2))) *
          (‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * (Cβ * RCg.qR v ^ (A' * ((dn.1 : ℝ) - m₀)))) *
          RCg.qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq _)
        exact mul_le_mul hW1' (mul_le_mul_of_nonneg_left hW2 hρn) (mul_nonneg hρn (norm_nonneg _))
          (mul_nonneg (abs_nonneg CA) (zpow_nonneg hq _))
    _ = |CA| * Cβ * (RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)) *
          (‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ ^ dn.2 * RCg.qR v ^ (A' * ((dn.1 : ℝ) - m₀))) *
          RCg.qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2))) := by ring

theorem fS_shell_eq_zero
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {A : G → ℂ} {m₀ : ℤ} {t : ℕ} {CA : ℝ}
    (hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)))
    (B : G → ℂ) (s : ℂ) (dn : ℤ × ℤ)
    (hmn : ¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2)) {k : G} (hk : k ∈ RCg.kzero v) :
    RCp.fS ℚ v A B s (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0 := by
  unfold RCp.fS
  rw [(hsh dn k hk).1 hmn, zero_mul, zero_mul]

theorem integrable_fS
    (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {A B : G → ℂ} (hAc : Continuous A) (hBc : Continuous B)
    (hAB : ∀ (x : F) (g : G), A (unipotent x * g) * B (unipotent x * g) = A g * B g)
    {m₀ : ℤ} {t : ℕ} {CA : ℝ}
    (hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)))
    (ω₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      B (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * B g)
    {Cβ A' : ℝ} (hCβ : 0 ≤ Cβ)
    (hβ : ∀ (d : ℤ), m₀ ≤ d → ∀ k ∈ RCg.kzero v,
      ‖B (diagZ (algebraMap (O) (F) ϖ) hπ d * k)‖ ≤ Cβ * RCg.qR v ^ (A' * ((d : ℝ) - m₀)))
    (hρ : 0 < ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖)
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (μN : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range) [μN.IsHaarMeasure]
    (s : ℂ) (hr₁ : RCg.rOne v t A' s.re < 1) (hr₂ : RCg.rTwo v t ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ s.re < 1) :
    Integrable (RCp.fS ℚ v A B s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range μN)) := by
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := RCg.secondCountableTopology_localGL v
  haveI : SFinite μN := RCg.sFinite_unipHaar v μN
  have hΦm : Measurable (RCp.fS ℚ v A B s) := RCp.measurable_fS ℚ v hAc hBc s
  refine RCg.integrable_withDensity_of_lintegral_lt_top μ₂ (RCg.unip v) μN _ hΦm ?_

  have hΨN : ∀ x ∈ RCg.unip v, ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      (fun g => ‖RCp.fS ℚ v A B s g‖ₑ) (x * g) = (fun g => ‖RCp.fS ℚ v A B s g‖ₑ) g := by
    intro x hx g
    show ‖RCp.fS ℚ v A B s (x * g)‖ₑ = ‖RCp.fS ℚ v A B s g‖ₑ
    rw [RCp.fS_unip ℚ v hAB s x hx g]
  obtain ⟨hsl, hsum⟩ := AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2 ℚ v ϖ hπ hϖ μ₂ μN
    (fun g => ‖RCp.fS ℚ v A B s g‖ₑ) hΦm.enorm hΨN
  rw [hsum]

  have hE₁0 : μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) ≠ 0 := by
    have := (hsl 0).1
    rwa [RCg.shellSlice_zero_eq hπ] at this
  have hc₀ : (μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hE₁0
  have hK₀ : μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))) < ∞ :=
    (RCg.isCompact_kzero v).measure_lt_top
  have hKr : 0 ≤ |CA| * Cβ * RCg.qR v ^ (-A' * (m₀ : ℝ)) :=
    mul_nonneg (mul_nonneg (abs_nonneg CA) hCβ) (Real.rpow_nonneg (RCg.qR_pos v).le _)
  have hg_nn := RCg.shellMajorant_nonneg (v := v) t A' s.re hρ m₀
  have hg_sum := RCg.summable_shellMajorant (v := v) t A' s.re hρ m₀ hr₁ hr₂

  have hterm : ∀ dn : ℤ × ℤ,
      (μN {x : ↥(RCg.unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          RCg.kzero v})⁻¹ *
        ∫⁻ k in ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖RCp.fS ℚ v A B s
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ₑ ∂μ₂ ≤
      ((μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
        μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
        ENNReal.ofReal ((|CA| * Cβ * RCg.qR v ^ (-A' * (m₀ : ℝ))) *
          RCg.shellMajorant v t A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
    intro dn

    have hslice : μN {x : ↥(RCg.unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          RCg.kzero v} =
        ENNReal.ofReal (RCg.qR v ^ (-dn.1)) *
          μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) := by
      rw [RCg.shellSlice_eq hπ dn, LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq v μN (RCg.piUnit hπ ^ dn.1),
        ← ENNReal.ofReal_coe_nnreal, RCg.coe_modulus_eq_norm, RCg.coe_piUnit_zpow, RCg.norm_uniformizer_zpow hϖ]
    have hqd : 0 < RCg.qR v ^ (-dn.1) := zpow_pos (RCg.qR_pos v) _
    have hinv : (μN {x : ↥(RCg.unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          RCg.kzero v})⁻¹ =
        ENNReal.ofReal (RCg.qR v ^ dn.1) *
          (μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ := by
      rw [hslice, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hqd).ne') (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_inv_of_pos hqd, ← zpow_neg, neg_neg]
    have hmeasK : MeasurableSet ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))) := (RCg.isOpen_kzero v).measurableSet
    by_cases hmn : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2
    ·
      have hpt : ∀ k ∈ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖RCp.fS ℚ v A B s
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 *
                k)‖ₑ ≤
            ENNReal.ofReal (RCg.shellPointwise v t CA Cβ A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
        intro k hk
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (norm_fS_shell_le v hϖ hπ hsh ω₂ hW₂Z hβ s dn hmn.1 hk)
      have hRnn := RCg.shellPointwise_nonneg (v := v) t CA hCβ A' s.re hρ m₀ dn
      calc _ ≤ (μN {x : ↥(RCg.unip v) |
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
                (x : GL (Fin 2) (v.adicCompletion ℚ)) *
                (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                  diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈ RCg.kzero v})⁻¹ *
            ∫⁻ k in ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
              ENNReal.ofReal (RCg.shellPointwise v t CA Cβ A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) ∂μ₂ :=
            mul_le_mul' le_rfl (setLIntegral_mono' hmeasK hpt)
        _ = (ENNReal.ofReal (RCg.qR v ^ dn.1) *
              (μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹) *
              (ENNReal.ofReal (RCg.shellPointwise v t CA Cβ A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) *
                μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) := by
            rw [hinv, setLIntegral_const]
        _ = ((μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
              μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
              (ENNReal.ofReal (RCg.qR v ^ dn.1) *
                ENNReal.ofReal (RCg.shellPointwise v t CA Cβ A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn)) := by ring
        _ = _ := by
            rw [← ENNReal.ofReal_mul (zpow_nonneg (RCg.qR_pos v).le _), RCg.qR_zpow_mul_shellPointwise t CA Cβ A' s.re _ hmn]
    ·
      have hzero : ∀ k ∈ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖RCp.fS ℚ v A B s
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 *
                k)‖ₑ ≤ 0 := by
        intro k hk
        rw [fS_shell_eq_zero v hπ hsh B s dn hmn hk, enorm_zero]
      have hint : ∫⁻ k in ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖RCp.fS ℚ v A B s
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ₑ
            ∂μ₂ = 0 :=
        le_antisymm ((setLIntegral_mono' hmeasK hzero).trans (by rw [setLIntegral_const, zero_mul])) bot_le
      rw [hint, mul_zero]
      exact bot_le

  calc _ ≤ ∑' dn : ℤ × ℤ,
        ((μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
          ENNReal.ofReal ((|CA| * Cβ * RCg.qR v ^ (-A' * (m₀ : ℝ))) *
            RCg.shellMajorant v t A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := ENNReal.tsum_le_tsum hterm
    _ = ((μN ((fun y : ↥(RCg.unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((RCg.kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
          ENNReal.ofReal (∑' dn : ℤ × ℤ, (|CA| * Cβ * RCg.qR v ^ (-A' * (m₀ : ℝ))) *
            RCg.shellMajorant v t A' s.re ‖((ω₂ (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun dn => mul_nonneg hKr (hg_nn dn)) (hg_sum.mul_left _)]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hc₀.lt_top hK₀) ENNReal.ofReal_lt_top

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCm

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem piece_bound_real (q ρ : ℝ) (hq : 1 ≤ q) (hρ : 0 < ρ) (t : ℕ) (A'' σ : ℝ) (m₀ : ℤ) (hm₀ : m₀ ≤ 0)
    (n : ℤ × ℤ) (hn : m₀ ≤ n.1 ∧ m₀ ≤ n.2) :
    q ^ ((t : ℝ) * ((n.1 : ℝ) + (n.2 : ℝ))) * q ^ (A'' * ((max n.1 0 : ℤ) : ℝ)) *
        ((q ^ ((3 : ℝ) / 2)) ^ n.1 * (q * ρ) ^ n.2 * (q ^ (-σ)) ^ (n.1 + 2 * n.2)) ≤
      q ^ (-(max A'' 0) * (m₀ : ℝ)) *
        ((q ^ ((t : ℝ) + max A'' 0 + 3 / 2 - σ)) ^ n.1 * (ρ * q ^ ((t : ℝ) + 1 - 2 * σ)) ^ n.2) := by
  have hq0 : 0 < q := one_pos.trans_le hq
  have key : ∀ x y : ℝ, q ^ x * q ^ y = q ^ (x + y) := fun x y => (Real.rpow_add hq0 x y).symm
  rw [mul_zpow, mul_zpow, ← Real.rpow_intCast (q ^ ((3 : ℝ) / 2)) n.1, ← Real.rpow_mul hq0.le,
    ← Real.rpow_intCast q n.2, ← Real.rpow_intCast (q ^ (-σ)) (n.1 + 2 * n.2), ← Real.rpow_mul hq0.le,
    ← Real.rpow_intCast (q ^ ((t : ℝ) + max A'' 0 + 3 / 2 - σ)) n.1, ← Real.rpow_mul hq0.le,
    ← Real.rpow_intCast (q ^ ((t : ℝ) + 1 - 2 * σ)) n.2, ← Real.rpow_mul hq0.le]
  have hρn : 0 ≤ ρ ^ n.2 := zpow_nonneg hρ.le _
  calc q ^ ((t : ℝ) * ((n.1 : ℝ) + (n.2 : ℝ))) * q ^ (A'' * ((max n.1 0 : ℤ) : ℝ)) *
        (q ^ ((3 : ℝ) / 2 * ((n.1 : ℤ) : ℝ)) * (q ^ ((n.2 : ℤ) : ℝ) * ρ ^ n.2) *
          q ^ (-σ * (((n.1 + 2 * n.2 : ℤ)) : ℝ)))
      = ρ ^ n.2 * q ^ ((t : ℝ) * ((n.1 : ℝ) + (n.2 : ℝ)) + A'' * ((max n.1 0 : ℤ) : ℝ) +
          (3 : ℝ) / 2 * ((n.1 : ℤ) : ℝ) + ((n.2 : ℤ) : ℝ) + (-σ * (((n.1 + 2 * n.2 : ℤ)) : ℝ))) := by
        rw [← key, ← key, ← key, ← key]; ring
    _ ≤ ρ ^ n.2 * q ^ (-(max A'' 0) * (m₀ : ℝ) + ((t : ℝ) + max A'' 0 + 3 / 2 - σ) * ((n.1 : ℤ) : ℝ) +
          ((t : ℝ) + 1 - 2 * σ) * ((n.2 : ℤ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq ?_) hρn
        have h1 : (m₀ : ℝ) ≤ (n.1 : ℝ) := by exact_mod_cast hn.1
        have h2 : (m₀ : ℝ) ≤ 0 := by exact_mod_cast hm₀
        have hA : A'' ≤ max A'' 0 := le_max_left _ _
        have hA0 : 0 ≤ max A'' 0 := le_max_right _ _
        have hmax : A'' * (max (n.1 : ℝ) 0) ≤ max A'' 0 * ((n.1 : ℝ) - (m₀ : ℝ)) := by
          rcases le_or_gt 0 (n.1 : ℝ) with h0 | h0
          · rw [max_eq_left h0]
            nlinarith
          · rw [max_eq_right h0.le]
            nlinarith
        push_cast
        nlinarith [hmax]
    _ = q ^ (-(max A'' 0) * (m₀ : ℝ)) * (q ^ (((t : ℝ) + max A'' 0 + 3 / 2 - σ) * ((n.1 : ℤ) : ℝ)) *
          (ρ ^ n.2 * q ^ (((t : ℝ) + 1 - 2 * σ) * ((n.2 : ℤ) : ℝ)))) := by
        rw [← key, ← key]; ring

theorem norm_A_shell_le
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {A : G → ℂ} {m₀ : ℤ} {t : ℕ} {CA : ℝ}
    (hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)))
    (Kb : Subgroup G) (hKbK : Kb ≤ RCg.kzero v) {k₀ : G} (hk₀ : k₀ ∈ RCg.kzero v)
    (n : ℤ × ℤ) {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ} (hu : Valued.v (u : F) = 1) {k : G} (hk : k ∈ Kb) :
    ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
        diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k))‖ ≤
      (if m₀ ≤ n.1 ∧ m₀ ≤ n.2 then |CA| * RCg.qR v ^ ((t : ℤ) * (n.1 + n.2)) else 0) := by
  have hmem : diagUnitGL2 u * (k₀ * k) ∈ RCg.kzero v :=
    Subgroup.mul_mem _ (RCp.diagUnitGL2_mem_kzero ℚ v hu) (Subgroup.mul_mem _ hk₀ (hKbK hk))
  have hrw : scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k) =
      scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 * diagZ (algebraMap (O) (F) ϖ) hπ n.1 * (diagUnitGL2 u * (k₀ * k)) := by
    have h := RCp.rep_mul_diagUnitGL2 ℚ v ϖ hπ n u
    simp only [RCp.rep] at h
    rw [← h]; group
  rw [hrw]
  obtain ⟨hvan, hbd⟩ := hsh n _ hmem
  split_ifs with hc
  · exact hbd.trans (mul_le_mul_of_nonneg_right (le_abs_self CA) (zpow_nonneg (RCg.qR_pos v).le _))
  · rw [hvan hc, norm_zero]

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCm

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem weight_toReal
    (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ)) (hπ : algebraMap (O) (F) ϖ ≠ 0)
    (μN : Measure ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range) [μN.IsHaarMeasure]
    (dn : ℤ × ℤ) :
    ((μN {x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range |
        (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1)⁻¹ * (x : G) *
          (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1) ∈
        AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤})⁻¹).toReal =
      RCg.qR v ^ dn.1 *
        ((μN ((fun y : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range =>
            ((y : G) : Mat) 0 1) ⁻¹' {z : F | Valued.v z ≤ 1}))⁻¹).toReal := by
  have hslice : μN {x : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range |
        (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1)⁻¹ * (x : G) *
          (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1) ∈
        AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤} =
      ENNReal.ofReal (RCg.qR v ^ (-dn.1)) *
        μN ((fun y : ↥(unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion ℚ v)).range =>
            ((y : G) : Mat) 0 1) ⁻¹' {z : F | Valued.v z ≤ 1}) := by
    have h1 := congrArg (fun S => μN S) (RCg.shellSlice_eq (v := v) hπ dn)
    refine h1.trans ?_
    beta_reduce
    rw [LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq v μN (RCg.piUnit hπ ^ dn.1),
      ← ENNReal.ofReal_coe_nnreal, RCg.coe_modulus_eq_norm, RCg.coe_piUnit_zpow, RCg.norm_uniformizer_zpow hϖ]
  have hqd : 0 < RCg.qR v ^ (-dn.1) := zpow_pos (RCg.qR_pos v) _
  rw [hslice, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hqd).ne') (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_inv_of_pos hqd, ← zpow_neg, neg_neg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (zpow_nonneg (RCg.qR_pos v).le _)]

theorem setIntegral_fS_shell
    (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ)) (hπ : algebraMap (O) (F) ϖ ≠ 0)
    (A B : G → ℂ) (μ₂ : Measure G) [μ₂.IsHaarMeasure] (s : ℂ) (dn : ℤ × ℤ) :
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup G) : Set G),
        RCp.fS ℚ v A B s (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) ∂μ₂ =
      (RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
        ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup G) : Set G),
          A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) *
          B (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) ∂μ₂ := by
  have h := RCp.setIntegral_fS_mul ℚ v μ₂ s (RCp.rep ℚ v ϖ hπ dn) (A := A) (B := B)
  rw [RCp.modulus_det_rep ℚ v ϖ hπ hϖ dn, RCp.qC_cpow_cpow] at h
  · exact h
  · norm_cast

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCm

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem norm_qC_cpow_zpow (z : ℂ) (n : ℤ) : ‖((RCp.qC ℚ v) ^ z) ^ n‖ = (RCg.qR v ^ z.re) ^ n := by
  rw [norm_zpow, norm_qC_cpow]

theorem norm_qC : ‖RCp.qC ℚ v‖ = RCg.qR v := by
  rw [qC_eq_qR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (RCg.qR_pos v)]

theorem summable_piece
    (hϖ : Valued.v (algebraMap (O) (F) ϖ) = WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {A : G → ℂ} {m₀ : ℤ} {t : ℕ} {CA : ℝ}
    (hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)‖ ≤
        CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)))
    (hm₀ : m₀ ≤ 0)
    (Kb : Subgroup G) (hKb : IsOpen (Kb : Set G)) (hKbK : Kb ≤ RCg.kzero v)
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (ν : Measure (HeightOneSpectrum.adicCompletion ℚ v)ˣ) [ν.IsHaarMeasure]
    {k₀ : G} (hk₀ : k₀ ∈ RCg.kzero v)
    (η : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)
    (hηc : Continuous fun u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ => ((η u : ℂˣ) : ℂ))
    (c : ℤ → ℂ) {C' A'' : ℝ} (hc : ∀ m : ℤ, ‖c m‖ ≤ C' * RCg.qR v ^ (A'' * ((max m 0 : ℤ) : ℝ)))
    (ωp : ℂ) (hωp : ωp ≠ 0) (s : ℂ)
    (hr₁ : RCg.rOne v t (max A'' 0) s.re < 1) (hr₂ : RCg.rTwo v t ‖ωp‖ s.re < 1) :
    Summable (fun n : ℤ × ℤ =>
      (∫ u in {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ | Valued.v (u : HeightOneSpectrum.adicCompletion ℚ v) = 1},
          (∫ k in ((Kb : Subgroup G) : Set G),
              A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
                diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) *
        c n.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ n.1 * ((RCp.qC ℚ v) * ωp) ^ n.2 *
        ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * n.1 + (2 : ℤ) * n.2)) := by

  have hq1 : 1 ≤ RCg.qR v := RCg.one_le_qR v
  have hq0 : 0 < RCg.qR v := RCg.qR_pos v
  have hρ : 0 < ‖ωp‖ := norm_pos_iff.mpr hωp

  have hsph : {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ | Valued.v (u : HeightOneSpectrum.adicCompletion ℚ v) = 1} =
      RCp.sph ℚ v := rfl

  obtain ⟨Mη, hMη⟩ := (RCp.isCompact_sph ℚ v).exists_bound_of_continuousOn hηc.continuousOn
  have hMη0 : 0 ≤ Mη := le_trans (norm_nonneg _) (hMη 1 (RCp.one_mem_sph ℚ v))

  have hKbfin : μ₂ ((Kb : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx => hKbK hx)) (RCg.isCompact_kzero v).measure_lt_top
  have hsphfin : ν (RCp.sph ℚ v) < ⊤ := lt_top_iff_ne_top.2 (RCp.measure_sph_ne ℚ v ν).2
  have hC' : 0 ≤ C' := by
    have h := hc 0
    simp only [max_self, Int.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h
    exact (norm_nonneg _).trans h

  set Kc : ℝ := |CA| * (μ₂ ((Kb : Subgroup G) : Set G)).toReal * Mη * (ν (RCp.sph ℚ v)).toReal * C' *
      RCg.qR v ^ (-(max A'' 0) * (m₀ : ℝ)) with hKc
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg) hMη0)
      ENNReal.toReal_nonneg) hC') (Real.rpow_nonneg hq0.le _)
  refine Summable.of_norm_bounded
    ((RCg.summable_shellMajorant (v := v) t (max A'' 0) s.re hρ m₀ hr₁ hr₂).mul_left Kc) (fun n => ?_)

  have hinner : ∀ u ∈ RCp.sph ℚ v,
      ‖∫ k in ((Kb : Subgroup G) : Set G),
          A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
            diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂‖ ≤
        (if m₀ ≤ n.1 ∧ m₀ ≤ n.2 then |CA| * RCg.qR v ^ ((t : ℤ) * (n.1 + n.2)) else 0) *
          (μ₂ ((Kb : Subgroup G) : Set G)).toReal := by
    intro u hu
    exact norm_setIntegral_le_of_norm_le_const hKbfin
      (fun k hk => norm_A_shell_le v hπ hsh Kb hKbK hk₀ n hu hk)

  have houter :
      ‖∫ u in {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ | Valued.v (u : HeightOneSpectrum.adicCompletion ℚ v) = 1},
          (∫ k in ((Kb : Subgroup G) : Set G),
              A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
                diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν‖ ≤
        ((if m₀ ≤ n.1 ∧ m₀ ≤ n.2 then |CA| * RCg.qR v ^ ((t : ℤ) * (n.1 + n.2)) else 0) *
          (μ₂ ((Kb : Subgroup G) : Set G)).toReal * Mη) * (ν (RCp.sph ℚ v)).toReal := by
    rw [hsph]
    refine norm_setIntegral_le_of_norm_le_const hsphfin (fun u hu => ?_)
    rw [norm_mul]
    exact mul_le_mul (hinner u hu) (hMη u hu) (norm_nonneg _)
      (mul_nonneg (by split_ifs <;> first | exact mul_nonneg (abs_nonneg _) (zpow_nonneg hq0.le _) | exact le_rfl)
        ENNReal.toReal_nonneg)

  have hw1 : ‖((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ n.1‖ = (RCg.qR v ^ ((3 : ℝ) / 2)) ^ n.1 := by
    rw [norm_qC_cpow_zpow]; norm_num
  have hw2 : ‖((RCp.qC ℚ v) * ωp) ^ n.2‖ = (RCg.qR v * ‖ωp‖) ^ n.2 := by
    rw [norm_zpow, norm_mul, norm_qC]
  have hw3 : ‖((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * n.1 + (2 : ℤ) * n.2)‖ = (RCg.qR v ^ (-s.re)) ^ (n.1 + 2 * n.2) := by
    rw [norm_qC_cpow_zpow, Complex.neg_re, one_mul]
  by_cases hcone : m₀ ≤ n.1 ∧ m₀ ≤ n.2
  ·
    rw [if_pos hcone] at houter
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hw1, hw2, hw3, RCg.shellMajorant_of_le t (max A'' 0) s.re ‖ωp‖ hcone]
    have hpb := piece_bound_real (RCg.qR v) ‖ωp‖ hq1 hρ t A'' s.re m₀ hm₀ n hcone
    have hzpow : RCg.qR v ^ ((t : ℤ) * (n.1 + n.2)) = RCg.qR v ^ ((t : ℝ) * ((n.1 : ℝ) + (n.2 : ℝ))) := by
      rw [← Real.rpow_intCast]; push_cast; ring_nf
    have hcn := hc n.1

    calc _ ≤ (|CA| * RCg.qR v ^ ((t : ℤ) * (n.1 + n.2)) * (μ₂ ((Kb : Subgroup G) : Set G)).toReal * Mη *
              (ν (RCp.sph ℚ v)).toReal) * (C' * RCg.qR v ^ (A'' * ((max n.1 0 : ℤ) : ℝ))) *
            ((RCg.qR v ^ ((3 : ℝ) / 2)) ^ n.1 * (RCg.qR v * ‖ωp‖) ^ n.2 * (RCg.qR v ^ (-s.re)) ^ (n.1 + 2 * n.2)) := by
          have h0 : 0 ≤ (RCg.qR v ^ ((3 : ℝ) / 2)) ^ n.1 * (RCg.qR v * ‖ωp‖) ^ n.2 * (RCg.qR v ^ (-s.re)) ^ (n.1 + 2 * n.2) :=
            mul_nonneg (mul_nonneg (zpow_nonneg (Real.rpow_nonneg hq0.le _) _)
              (zpow_nonneg (mul_nonneg hq0.le (norm_nonneg _)) _)) (zpow_nonneg (Real.rpow_nonneg hq0.le _) _)
          calc _ = ‖∫ u in {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ | Valued.v (u : HeightOneSpectrum.adicCompletion ℚ v) = 1},
                (∫ k in ((Kb : Subgroup G) : Set G),
                  A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν‖ *
                ‖c n.1‖ * ((RCg.qR v ^ ((3 : ℝ) / 2)) ^ n.1 * (RCg.qR v * ‖ωp‖) ^ n.2 * (RCg.qR v ^ (-s.re)) ^ (n.1 + 2 * n.2)) := by
                  ring
            _ ≤ _ := by
                  apply mul_le_mul_of_nonneg_right _ h0
                  exact mul_le_mul houter hcn (norm_nonneg _)
                    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (zpow_nonneg hq0.le _))
                      ENNReal.toReal_nonneg) hMη0) ENNReal.toReal_nonneg)
      _ = (|CA| * (μ₂ ((Kb : Subgroup G) : Set G)).toReal * Mη * (ν (RCp.sph ℚ v)).toReal * C') *
            (RCg.qR v ^ ((t : ℝ) * ((n.1 : ℝ) + (n.2 : ℝ))) * RCg.qR v ^ (A'' * ((max n.1 0 : ℤ) : ℝ)) *
              ((RCg.qR v ^ ((3 : ℝ) / 2)) ^ n.1 * (RCg.qR v * ‖ωp‖) ^ n.2 * (RCg.qR v ^ (-s.re)) ^ (n.1 + 2 * n.2))) := by
          rw [hzpow]; ring
      _ ≤ (|CA| * (μ₂ ((Kb : Subgroup G) : Set G)).toReal * Mη * (ν (RCp.sph ℚ v)).toReal * C') *
            (RCg.qR v ^ (-(max A'' 0) * (m₀ : ℝ)) *
              ((RCg.qR v ^ ((t : ℝ) + max A'' 0 + 3 / 2 - s.re)) ^ n.1 *
                (‖ωp‖ * RCg.qR v ^ ((t : ℝ) + 1 - 2 * s.re)) ^ n.2)) := by
          apply mul_le_mul_of_nonneg_left hpb
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg) hMη0)
            ENNReal.toReal_nonneg) hC'
      _ = Kc * (RCg.rOne v t (max A'' 0) s.re ^ n.1 * RCg.rTwo v t ‖ωp‖ s.re ^ n.2) := by
          rw [hKc, RCg.rOne, RCg.rTwo]; ring
  ·
    have hzero : (∫ u in {u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ | Valued.v (u : HeightOneSpectrum.adicCompletion ℚ v) = 1},
          (∫ k in ((Kb : Subgroup G) : Set G),
              A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
                diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ) ∂ν) = 0 := by
      rw [hsph]
      refine setIntegral_eq_zero_of_forall_eq_zero (fun u hu => ?_)
      have hin : (∫ k in ((Kb : Subgroup G) : Set G),
              A (scalarPi (algebraMap (O) (F) ϖ) hπ ^ n.2 *
                diagUnitGL2 (Units.mk0 (algebraMap (O) (F) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero (fun k hk => ?_)
        have h := norm_A_shell_le v hπ hsh Kb hKbK hk₀ n hu hk
        rw [if_neg hcone] at h
        exact norm_le_zero_iff.mp h
      rw [hin, zero_mul]
    rw [hzero]
    simp only [zero_mul, norm_zero]
    exact mul_nonneg hKc0 (RCg.shellMajorant_nonneg (v := v) t (max A'' 0) s.re hρ m₀ n)

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

namespace RCm

open Polynomial Finset

theorem rational_of_pieces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℂ) (hq : q ≠ 0) (κ : ℂ)
    (P Q : ι → Polynomial ℂ) (m : ι → ℤ) (hQ : ∀ i, Q i ≠ 0) :
    ∃ (Ptot Qtot : Polynomial ℂ) (mtot : ℤ), Qtot ≠ 0 ∧
      ∀ (s : ℂ) (S : ι → ℂ),
        (∀ i, S i * (Q i).eval (q ^ (-s)) = (q ^ (-s)) ^ (m i) * (P i).eval (q ^ (-s))) →
        (κ * ∑ i, S i) * Qtot.eval (q ^ (-s)) = q ^ ((mtot : ℂ) * s) * Ptot.eval (q ^ (-s)) := by
  classical
  obtain ⟨mlow, hmlow⟩ : ∃ mlow : ℤ, mlow = -∑ i, |m i| := ⟨_, rfl⟩
  have hle : ∀ i, mlow ≤ m i := fun i => by
    have h1 : |m i| ≤ ∑ j, |m j| := Finset.single_le_sum (fun j _ => abs_nonneg (m j)) (Finset.mem_univ i)
    have h2 : -|m i| ≤ m i := neg_abs_le (m i)
    omega
  refine ⟨C κ * ∑ i, X ^ (m i - mlow).toNat * P i * ∏ j ∈ univ.erase i, Q j, ∏ i, Q i, -mlow,
    Finset.prod_ne_zero_iff.2 fun i _ => hQ i, ?_⟩
  intro s S hS
  have hX0 : q ^ (-s) ≠ 0 := fun h => hq ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have key : ∀ i, S i * (∏ j, (Q j).eval (q ^ (-s))) =
      q ^ (((-mlow : ℤ) : ℂ) * s) *
        ((q ^ (-s)) ^ (m i - mlow).toNat * (P i).eval (q ^ (-s)) * ∏ j ∈ univ.erase i, (Q j).eval (q ^ (-s))) := by
    intro i
    rw [← Finset.mul_prod_erase univ (fun j => (Q j).eval (q ^ (-s))) (mem_univ i), ← mul_assoc, hS i]
    have h1 : (q ^ (-s)) ^ (m i) = (q ^ (-s)) ^ mlow * (q ^ (-s)) ^ ((m i - mlow).toNat : ℕ) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith [hle i] : 0 ≤ m i - mlow), ← zpow_add₀ hX0]
      congr 1
      ring
    have h2 : (q ^ (-s)) ^ mlow = q ^ (((-mlow : ℤ) : ℂ) * s) := by
      rw [← Complex.cpow_int_mul]
      congr 1
      push_cast
      ring
    rw [h1, h2]
    ring
  calc (κ * ∑ i, S i) * (∏ i, Q i).eval (q ^ (-s))
      = κ * ∑ i, S i * ∏ j, (Q j).eval (q ^ (-s)) := by
        rw [Polynomial.eval_prod, mul_assoc, Finset.sum_mul]
    _ = κ * ∑ i, q ^ (((-mlow : ℤ) : ℂ) * s) *
          ((q ^ (-s)) ^ (m i - mlow).toNat * (P i).eval (q ^ (-s)) * ∏ j ∈ univ.erase i, (Q j).eval (q ^ (-s))) := by
        rw [Finset.sum_congr rfl fun i _ => key i]
    _ = κ * (q ^ (((-mlow : ℤ) : ℂ) * s) *
          ∑ i, (q ^ (-s)) ^ (m i - mlow).toNat * (P i).eval (q ^ (-s)) * ∏ j ∈ univ.erase i, (Q j).eval (q ^ (-s))) := by
        rw [← Finset.mul_sum]
    _ = q ^ (((-mlow : ℤ) : ℂ) * s) *
          (C κ * ∑ i, X ^ (m i - mlow).toNat * P i * ∏ j ∈ univ.erase i, Q j).eval (q ^ (-s)) := by
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_prod]
        ring

end RCm
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCg P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central.RCp"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hKb : IsOpen (Kb : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hKbK : Kb ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (hKbc : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      (∀ i j : Fin 2, Valued.v ((((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
        - 1) i j) ≤ WithZero.exp (-(b : ℤ))) → k ∈ Kb)
    (A B : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hA : ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), A (g * k) = A g)
    (hB : ∀ k ∈ Kb, ∀ g : GL (Fin 2) (v.adicCompletion ℚ), B (g * k) = B g)
    (hAB : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      A (unipotent x * g) * B (unipotent x * g) = A g * B g)

    (hAshell : ∃ (m₀ : ℤ) (t : ℕ) (CA : ℝ), ∀ (dn : ℤ × ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) → A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1 * k) = 0) ∧
      ‖A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ ≤
        CA * (Ideal.absNorm v.asIdeal : ℝ) ^ ((t : ℤ) * (dn.1 + dn.2)))

    (hArat : ∀ k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (c : ℕ),
      HasConductorExponentAt ℚ v η c → c ≤ b →
      letI := localBorel ℚ v
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
        let Arr : ℤ × ℤ → ℂ := fun n =>
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                  diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
          (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → Arr n = 0) ∧
          (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
            ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
              D₁.coeff i * D₂.coeff l * Arr (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))

    (ω : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hBcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      B (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * B g)

    (hBgr : ∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A' * m))

    (hBrec : ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        (∀ m : ℤ, m < N₁ → B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * B (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) :
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      ∃ (P Q : Polynomial ℂ) (m : ℤ) (σ₂ : ℝ), Q ≠ 0 ∧
        ∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (A g * B g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) ∧
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
              s A B * Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  intro μ₂ _ μN₂ _
  classical

  haveI : BorelSpace (v.adicCompletion ℚ)ˣ := RCu.borelSpace_locUnits v
  haveI := RCu.isAddHaarMeasure_selfDualHaarAt v
  haveI hνH : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) :
      Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure := RCu.isHaarMeasure_locMul v

  have hA' := hA
  obtain ⟨U, hU, hAU⟩ := hA'
  have hAc : Continuous A := RCp.continuous_of_rightInvariant hU hAU
  have hBc : Continuous B := RCp.continuous_of_rightInvariant hKb hB
  have hBcenR : ∀ (t : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      B (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω t : ℂˣ) : ℂ) * B g := by
    intro t g; rw [← RCg.scalar_mul_comm, hBcen]

  obtain ⟨n, k₀, η, cη, c, N₁', D', M', C', A'', hk₀, hη, hD'0, hcrec, hcgr, hSI⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_torusShell_eq_sum_mul_torusShellArray_of_shellRecurrence_of_central
      ℚ v hπ hϖ b Kb hKb hKbK hKbc A B hA hB ω hBcen hBgr hBrec μ₂
      (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))

  obtain ⟨m₀, t, CA, hsh0⟩ := hAshell
  have hsh : ∀ (dn : ℤ × ℤ), ∀ k ∈ RCg.kzero v,
      (¬ (min m₀ 0 ≤ dn.1 ∧ min m₀ 0 ≤ dn.2) → A ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) * k) = 0) ∧
      ‖A ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) * k)‖ ≤ CA * RCg.qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
    intro dn k hk
    obtain ⟨h1, h2⟩ := hsh0 dn k hk
    refine ⟨fun hmn => h1 fun hmn' => hmn ⟨(min_le_left _ _).trans hmn'.1, (min_le_left _ _).trans hmn'.2⟩, ?_⟩
    rw [RCg.qR_eq_natCast]; exact h2
  have hm₁ : min m₀ 0 ≤ 0 := min_le_right _ _
  obtain ⟨Cβ, A', hCβ, hA', hβ⟩ := RCg.exists_partner_shell_bound hπ hBc hBgr (min m₀ 0) hm₁

  have hωp : (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hρ : 0 < ‖((ω (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hρ' : ‖(((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)‖ = ‖((ω (RCg.piUnit hπ) : ℂˣ) : ℂ)‖ := rfl
  obtain ⟨σa, hσa⟩ := RCg.exists_abscissa (v := v) t hA' hρ
  obtain ⟨σb, hσb⟩ := RCg.exists_abscissa (v := v) t (le_max_right A'' 0) hρ

  have hJ : ∀ i : Fin n, ∃ (P Q : Polynomial ℂ) (mm : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun nn : ℤ × ℤ =>
          (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i nn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ nn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ nn.2 *
          X ^ ((1 : ℤ) * nn.1 + (2 : ℤ) * nn.2)) →
        (∑' nn : ℤ × ℤ,
          (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i nn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ nn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ nn.2 *
          X ^ ((1 : ℤ) * nn.1 + (2 : ℤ) * nn.2)) * Q.eval X = X ^ mm * P.eval X := by
    intro i
    obtain ⟨N₁, D₁, D₂, M, hrat⟩ := hArat (k₀ i) (hk₀ i) (η i) (cη i) (hη i).1 (hη i).2 μ₂
    have h := Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
      (fun nn : ℤ × ℤ => (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))))
      (c i) ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ))
      (RCm.cpow_ne_zero' (RCp.qC_ne_zero ℚ v) _) (mul_ne_zero (RCp.qC_ne_zero ℚ v) hωp)
      1 2 one_pos two_pos ⟨N₁, D₁, D₂, M, hrat⟩ ⟨N₁', D', M', hD'0, hcrec i⟩
    simpa only [Nat.cast_one, Nat.cast_ofNat] using h
  choose Pf Qf mf hQf hJf using hJ

  set V : ℝ := ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
      {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}).toReal with hV
  set W₀ : ℝ := ((μN₂ ((fun y : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range =>
      ((y : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹'
        {z : v.adicCompletion ℚ | Valued.v z ≤ 1}))⁻¹).toReal with hW₀
  obtain ⟨Ptot, Qtot, mtot, hQtot, hfin⟩ :=
    RCm.rational_of_pieces (RCp.qC ℚ v) (RCp.qC_ne_zero ℚ v) (((W₀ / V : ℝ) : ℂ)) Pf Qf mf hQf
  refine ⟨Ptot, Qtot, mtot, max σa σb, hQtot, fun s hs => ?_⟩
  obtain ⟨hr₁, hr₂⟩ := hσa s.re ((le_max_left _ _).trans_lt hs)
  obtain ⟨hr₁', hr₂'⟩ := hσb s.re ((le_max_right _ _).trans_lt hs)

  have hint : Integrable (RCp.fS ℚ v A B s)
      (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) :=
    RCm.integrable_fS v hϖ hπ hAc hBc hAB hsh ω hBcenR hCβ hβ hρ μ₂ μN₂ s hr₁ hr₂
  refine ⟨hint, ?_⟩

  obtain ⟨-, -, hHS⟩ :=
    AutomorphicForm.hasSum_integral_torusShells_of_integrable_withDensity_density_localGL2 ℚ v ϖ hπ hϖ μ₂ μN₂
      (RCp.fS ℚ v A B s) (RCp.measurable_fS ℚ v hAc hBc s) (RCp.fS_unip ℚ v hAB s) hint

  have hV0 : V ≠ 0 := by
    have h := RCp.measure_sph_ne ℚ v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
    rw [hV, ENNReal.toReal_ne_zero]
    exact ⟨h.1, h.2⟩
  have hVC : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV0

  have hηc : ∀ i, Continuous fun u : (v.adicCompletion ℚ)ˣ => ((η i u : ℂˣ) : ℂ) :=
    fun i => RCp.continuous_char ℚ v b (hη i).1 (hη i).2
  have hcgr' : ∀ i (m : ℤ), ‖c i m‖ ≤ C' * RCg.qR v ^ (A'' * ((max m 0 : ℤ) : ℝ)) := by
    intro i m; rw [RCg.qR_eq_natCast]; exact hcgr i m
  have hr₂'' : RCg.rTwo v t ‖(((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)‖ s.re < 1 := hr₂'
  have hsum : ∀ i : Fin n, Summable (fun nn : ℤ × ℤ =>
      (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i nn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ nn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ nn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * nn.1 + (2 : ℤ) * nn.2)) :=
    fun i => RCm.summable_piece v hϖ hπ hsh hm₁ Kb hKb hKbK μ₂ _ (hk₀ i) (η i) (hηc i) (c i) (hcgr' i)
      (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) hωp s hr₁' hr₂''
  have hS : ∀ i : Fin n, (∑' nn : ℤ × ℤ,
      (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i nn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ nn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ nn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * nn.1 + (2 : ℤ) * nn.2)) * (Qf i).eval ((RCp.qC ℚ v) ^ (-s)) =
      ((RCp.qC ℚ v) ^ (-s)) ^ (mf i) * (Pf i).eval ((RCp.qC ℚ v) ^ (-s)) :=
    fun i => hJf i _ (RCm.cpow_ne_zero' (RCp.qC_ne_zero ℚ v) _) (hsum i)

  have hterm : ∀ dn : ℤ × ℤ,
      (((μN₂ {x : ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range |
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ * (x : GL (Fin 2) (v.adicCompletion ℚ)) * (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤})⁻¹).toReal : ℂ) *
        ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))), RCp.fS ℚ v A B s ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) * k) ∂μ₂ =
      ((W₀ / V : ℝ) : ℂ) * ∑ i : Fin n, (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i dn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ dn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2) := by
    intro dn
    rw [RCm.weight_toReal v hϖ hπ μN₂ dn, RCm.setIntegral_fS_shell v hϖ hπ A B μ₂ s dn]
    have hSsh : ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))), A ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) * k) * B ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ dn.1) * k) ∂μ₂ =
        (V : ℂ)⁻¹ * ∑ i : Fin n, (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 * (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) := by
      rw [eq_inv_mul_iff_mul_eq₀ hVC]
      exact hSI dn
    rw [hSsh]
    have hq1 : ((RCg.qR v ^ dn.1 * W₀ : ℝ) : ℂ) = (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (W₀ : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_zpow, ← RCm.qC_eq_qR, Complex.cpow_intCast]
    rw [hq1, Complex.ofReal_div]
    have hw := RCm.weight_identity v (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) s dn
    have hpt : ∀ i : Fin n,
        (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (W₀ : ℂ) *
          ((RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
            ((V : ℂ)⁻¹ * ((((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 * (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))))) =
        ((W₀ : ℂ) / (V : ℂ)) * ((∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i dn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ dn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2)) := by
      intro i
      calc (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (W₀ : ℂ) *
            ((RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
              ((V : ℂ)⁻¹ * ((((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 * (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))))))
          = ((W₀ : ℂ) / (V : ℂ)) * ((∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) * c i dn.1) *
              ((RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
                (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2) := by
            rw [div_eq_mul_inv]; ring
        _ = _ := by rw [hw]; ring
    calc (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (W₀ : ℂ) *
          ((RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
            ((V : ℂ)⁻¹ * ∑ i : Fin n, (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 * (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))))
        = ∑ i : Fin n, (RCp.qC ℚ v) ^ ((dn.1 : ℤ) : ℂ) * (W₀ : ℂ) *
          ((RCp.qC ℚ v) ^ ((((-(dn.1 + 2 * dn.2)) : ℤ) : ℂ) * (s - 1 / 2)) *
            ((V : ℂ)⁻¹ * ((((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ) ^ dn.2 * c i dn.1 * (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ i : Fin n, ((W₀ : ℂ) / (V : ℂ)) * ((∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i dn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ dn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2)) := Finset.sum_congr rfl fun i _ => hpt i
      _ = _ := by rw [← Finset.mul_sum]

  have hΨ : (∫ g, RCp.fS ℚ v A B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂))) =
      ((W₀ / V : ℝ) : ℂ) * ∑ i : Fin n, ∑' nn : ℤ × ℤ,
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ nn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i nn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ nn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ nn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * nn.1 + (2 : ℤ) * nn.2) := by
    calc (∫ g, RCp.fS ℚ v A B s g
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)))
        = ∑' dn : ℤ × ℤ, ((W₀ / V : ℝ) : ℂ) * ∑ i : Fin n, (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i dn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ dn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2) := by
          rw [← hHS.tsum_eq]; exact tsum_congr hterm
      _ = ((W₀ / V : ℝ) : ℂ) * ∑' dn : ℤ × ℤ, ∑ i : Fin n, (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
              (∫ k in ((Kb : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                  A (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ dn.1 * u) *
                    (k₀ i * k)) ∂μ₂) * ((η i u : ℂˣ) : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) *
          c i dn.1 * ((RCp.qC ℚ v) ^ ((3 : ℂ) / 2)) ^ dn.1 * ((RCp.qC ℚ v) * (((ω (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ)) : ℂˣ) : ℂ)) ^ dn.2 *
          ((RCp.qC ℚ v) ^ (-s)) ^ ((1 : ℤ) * dn.1 + (2 : ℤ) * dn.2) := tsum_mul_left
      _ = _ := by rw [Summable.tsum_finsetSum (fun i _ => hsum i)]
  have hΨ' : RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂
      (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
        (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
      s A B =
      ∫ g, RCp.fS ℚ v A B s g
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) := rfl
  rw [hΨ', hΨ]
  exact hfin s _ hS

end S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_rational_rsLocalIntegral_of_shellGauge_of_rationalTorusShell_of_shellRecurrence_of_central (solution)
