-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_integrable_rsLocalIntegrand_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/85f9e33c-d035-5c60-93ee-528367b49c66

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_HaarQuotient
import Theorems.Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
import Theorems.Thm_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal

noncomputable section

namespace RSLocGauge

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

theorem continuous_of_rightInvariant {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    {α : Type*} [TopologicalSpace α]
    {f : H → α} {U : Subgroup H} (hU : IsOpen (U : Set H)) (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) :
    Continuous f := by
  refine (IsLocallyConstant.iff_exists_open f).mpr (fun x => ?_) |>.continuous
  refine ⟨(fun h => x⁻¹ * h) ⁻¹' (U : Set H), hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have := hf (x⁻¹ * y) hy x
    rwa [mul_inv_cancel_left] at this

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

end RSLocGauge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge.RSLocGauge"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge.RSLocGauge"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction RSLocGauge

open scoped nonZeroDivisors ENNReal

open scoped Classical in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) → W₂ (g * k) = W₂ g)
    (ω₂ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hW₂Z : ∀ (t : (v.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ((ω₂ t : ℂˣ) : ℂ) * W₂ g)
    (hW₂gr : ∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
      ‖W₂ (UnramifiedWhittaker.diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
        C * (Ideal.absNorm v.asIdeal : ℝ) ^ (A * m)) :
    ∀ g₃ : LocalGL3 v,
      letI := localGLBorel ℚ v
      haveI := borelSpace_localGLBorel ℚ v
      ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
        (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
      ∃ σ₂ : ℝ,
          ∀ s : ℂ, σ₂ < s.re →
            Integrable
              (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
                (W (iotaGL g * g₃) * W₂ g) *
                  ((LanglandsTunnell.TateLocal.modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                      v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
    := by
  intro g₃ μ₂ _ μN _
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  haveI := locallyCompactSpace_localGL ℚ v
  haveI := secondCountableTopology_localGL v
  haveI : SFinite μN := sFinite_unipHaar v μN
  have hϖ' : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v)
      (HeightOneSpectrum.adicCompletion ℚ v) ϖ) = WithZero.exp (-1 : ℤ) := hϖ

  have hW'mem : gl3AmbientRightTranslate (R := ℂ) g₃ W ∈ gl3CyclicSubspace W := Submodule.subset_span ⟨g₃, rfl⟩
  obtain ⟨⟨B, t, C, hg⟩, -⟩ :=
    forall_mem_gl3CyclicSubspace_exists_gauge_and_exists_gauge_dualWhittakerFn3 W hWgauge _ hW'mem
  have hWW' : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W (iotaGL g * g₃) = gl3AmbientRightTranslate (R := ℂ) g₃ W (iotaGL g) := fun g => rfl
  obtain ⟨m₀, hm₀le, hm₀⟩ := exists_cutoff v B

  have hKb : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
      Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero b v.ne_bot)).2
  have hW₂c : Continuous W₂ := continuous_of_rightInvariant hKb fun k hk g => hW₂K k g hk
  obtain ⟨Cβ, A', hCβ, hA', hβ⟩ := exists_partner_shell_bound hπ hW₂c hW₂gr m₀ hm₀le

  have hρ : 0 < ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  obtain ⟨σ₂, hσ₂⟩ := exists_abscissa (v := v) t hA' hρ
  refine ⟨σ₂, fun s hs => ?_⟩
  obtain ⟨hr₁, hr₂⟩ := hσ₂ s.re hs

  change Integrable (rsIntegrand W g₃ W₂ s) _
  have hΦm : Measurable (rsIntegrand W g₃ W₂ s) := measurable_rsIntegrand hsm g₃ hKb hW₂K s
  refine integrable_withDensity_of_lintegral_lt_top μ₂ (unip v) μN _ hΦm ?_

  have hΨN : ∀ x ∈ unip v, ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      (fun g => ‖rsIntegrand W g₃ W₂ s g‖ₑ) (x * g) = (fun g => ‖rsIntegrand W g₃ W₂ s g‖ₑ) g := by
    intro x hx g
    change ‖rsIntegrand W g₃ W₂ s (((⟨x, hx⟩ : ↥(unip v)) : GL (Fin 2) (v.adicCompletion ℚ)) * g)‖ₑ = _
    rw [rsIntegrand_unipotent_mul hψinv hW g₃ hW₂ψ s ⟨x, hx⟩ g]
  obtain ⟨hsl, hsum⟩ := AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2 ℚ v ϖ hπ hϖ μ₂ μN
    (fun g => ‖rsIntegrand W g₃ W₂ s g‖ₑ) hΦm.enorm hΨN
  rw [hsum]

  have hE₁0 : μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) ≠ 0 := by
    have := (hsl 0).1
    rwa [shellSlice_zero_eq hπ] at this
  have hc₀ : (μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hE₁0
  have hK₀ : μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))) < ∞ :=
    (isCompact_kzero v).measure_lt_top
  have hKr : 0 ≤ |C| * Cβ * qR v ^ (-A' * (m₀ : ℝ)) :=
    mul_nonneg (mul_nonneg (abs_nonneg C) hCβ) (Real.rpow_nonneg (qR_pos v).le _)
  have hg_nn := shellMajorant_nonneg (v := v) t A' s.re hρ m₀
  have hg_sum := summable_shellMajorant (v := v) t A' s.re hρ m₀ hr₁ hr₂

  have hterm : ∀ dn : ℤ × ℤ,
      (μN {x : ↥(unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          kzero v})⁻¹ *
        ∫⁻ k in ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖rsIntegrand W g₃ W₂ s
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ₑ ∂μ₂ ≤
      ((μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
        μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
        ENNReal.ofReal ((|C| * Cβ * qR v ^ (-A' * (m₀ : ℝ))) *
          shellMajorant v t A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
    intro dn

    have hslice : μN {x : ↥(unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          kzero v} =
        ENNReal.ofReal (qR v ^ (-dn.1)) *
          μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) := by
      rw [shellSlice_eq hπ dn, LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq v μN (piUnit hπ ^ dn.1),
        ← ENNReal.ofReal_coe_nnreal, coe_modulus_eq_norm, coe_piUnit_zpow, norm_uniformizer_zpow hϖ']
    have hqd : 0 < qR v ^ (-dn.1) := zpow_pos (qR_pos v) _
    have hinv : (μN {x : ↥(unip v) |
          (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (v.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈
          kzero v})⁻¹ =
        ENNReal.ofReal (qR v ^ dn.1) *
          (μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ := by
      rw [hslice, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hqd).ne') (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_inv_of_pos hqd, ← zpow_neg, neg_neg]
    have hmeasK : MeasurableSet ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))) := (isOpen_kzero v).measurableSet
    by_cases hmn : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2
    ·
      have hpt : ∀ k ∈ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖rsIntegrand W g₃ W₂ s
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 *
                k)‖ₑ ≤
            ENNReal.ofReal (shellPointwise v t C Cβ A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
        intro k hk
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal
          (norm_rsIntegrand_shell_le hϖ' hπ hWW' hg hm₀ ω₂ hW₂Z hβ s dn hmn.1 hk)
      have hRnn := shellPointwise_nonneg (v := v) t C hCβ A' s.re hρ m₀ dn
      calc _ ≤ (μN {x : ↥(unip v) |
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1)⁻¹ *
                (x : GL (Fin 2) (v.adicCompletion ℚ)) *
                (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 *
                  diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1) ∈ kzero v})⁻¹ *
            ∫⁻ k in ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
              ENNReal.ofReal (shellPointwise v t C Cβ A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) ∂μ₂ :=
            mul_le_mul' le_rfl (setLIntegral_mono' hmeasK hpt)
        _ = (ENNReal.ofReal (qR v ^ dn.1) *
              (μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹) *
              (ENNReal.ofReal (shellPointwise v t C Cβ A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) *
                μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) := by
            rw [hinv, setLIntegral_const]
        _ = ((μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
              μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
              (ENNReal.ofReal (qR v ^ dn.1) *
                ENNReal.ofReal (shellPointwise v t C Cβ A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn)) := by ring
        _ = _ := by
            rw [← ENNReal.ofReal_mul (zpow_nonneg (qR_pos v).le _), qR_zpow_mul_shellPointwise t C Cβ A' s.re _ hmn]
    ·
      have hzero : ∀ k ∈ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖rsIntegrand W g₃ W₂ s
              (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 *
                k)‖ₑ ≤ 0 := by
        intro k hk
        rw [rsIntegrand_shell_eq_zero hϖ' hπ hWW' hg hm₀ W₂ s dn hmn hk, enorm_zero]
      have hint : ∫⁻ k in ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
          ‖rsIntegrand W g₃ W₂ s
            (scalarPi (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion ℚ) ϖ) hπ dn.1 * k)‖ₑ
            ∂μ₂ = 0 :=
        le_antisymm ((setLIntegral_mono' hmeasK hzero).trans (by rw [setLIntegral_const, zero_mul])) bot_le
      rw [hint, mul_zero]
      exact bot_le

  calc _ ≤ ∑' dn : ℤ × ℤ,
        ((μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
          ENNReal.ofReal ((|C| * Cβ * qR v ^ (-A' * (m₀ : ℝ))) *
            shellMajorant v t A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := ENNReal.tsum_le_tsum hterm
    _ = ((μN ((fun y : ↥(unip v) => ((y : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((kzero v : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) *
          ENNReal.ofReal (∑' dn : ℤ × ℤ, (|C| * Cβ * qR v ^ (-A' * (m₀ : ℝ))) *
            shellMajorant v t A' s.re ‖((ω₂ (piUnit hπ) : ℂˣ) : ℂ)‖ m₀ dn) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun dn => mul_nonneg hKr (hg_nn dn)) (hg_sum.mul_left _)]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hc₀.lt_top hK₀) ENNReal.ofReal_lt_top

end S_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_integrable_rsLocalIntegrand_of_gauge (solution)
