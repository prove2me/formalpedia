-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4569d889-ed73-5746-88ae-4e57e29ec7ff

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_HaarQuotient
import Theorems.Thm_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_LanglandsTunnell_CubicInduction_absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
open scoped ENNReal NNReal

noncomputable section

namespace RSUnfoldConv

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

section Fold

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

def phi (W : LocalGL3 v → ℂ) (f : G → ℂ) (w₀ : G) (s : ℂ) (g : G) : ℂ :=
  (W (iotaGL g) * f (w₀ * g)) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) ^ (s - 1 / 2)

theorem measurable_phi {W : LocalGL3 v → ℂ}
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    {f : G → ℂ} (hlc : IsLocallyConstant f) (w₀ : G) (s : ℂ) :
    Measurable[localGLBorel ℚ v] (phi v W f w₀ s) := by
  letI : MeasurableSpace G := localGLBorel ℚ v
  haveI : BorelSpace G := borelSpace_localGLBorel ℚ v
  obtain ⟨Uv, hUv, hWU⟩ := hsm
  have hWc : Continuous W := continuous_of_rightInvariant hUv hWU
  have h1 : Continuous fun g : G => W (iotaGL g) := hWc.comp (continuous_iotaGL v)
  have h2 : Continuous fun g : G => f (w₀ * g) := hlc.continuous.comp (continuous_const.mul continuous_id)
  have h3 : Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
        HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ) := by
    have : (fun g : G => ((modulus
        ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
          HeightOneSpectrum.adicCompletion ℚ v) : ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
      funext g
      rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))
  exact ((h1.mul h2).measurable).mul (h3.measurable.pow_const _)

theorem unip_eq_unipotentGL2 (n : unip v) : (n : G) = unipotentGL2 (((n : G) : Mat) 0 1) := by
  obtain ⟨z, hz⟩ := n.2
  rw [← hz]
  change (unipotentGL2 z.toAdd : G) = unipotentGL2 (((unipotentGL2 z.toAdd : G) : Mat) 0 1)
  have h01 : (((unipotentGL2 z.toAdd : G) : Mat) 0 1) = z.toAdd := by simp [unipotentGL2_coe]
  rw [h01]

theorem unip_comm (m n : unip v) : m * n = n * m := by
  refine Subtype.ext ?_
  change (m : G) * (n : G) = (n : G) * (m : G)
  rw [unip_eq_unipotentGL2 v m, unip_eq_unipotentGL2 v n, ← unipotentGL2_add, ← unipotentGL2_add, add_comm]

theorem continuous_unipotentGL2 : Continuous fun y : F => (unipotentGL2 y : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun y : F => (unipotentGL2 y : G)) = fun y => !![1, y; 0, 1] := funext fun y => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)) = fun y => !![1, -y; 0, 1] :=
      funext fun y => rfl
    show Continuous fun y : F => (((unipotentGL2 y : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

def unipHomeo : F ≃ₜ (unip v) where
  toFun y := ⟨unipotentGL2 y, ⟨Multiplicative.ofAdd y, rfl⟩⟩
  invFun n := ((n : G) : Mat) 0 1
  left_inv y := by simp [unipotentGL2_coe]
  right_inv n := Subtype.ext (unip_eq_unipotentGL2 v n).symm
  continuous_toFun := (continuous_unipotentGL2 v).subtype_mk _
  continuous_invFun := ((Units.continuous_val).matrix_elem 0 1).comp continuous_subtype_val

theorem unipHomeo_apply_coe (y : F) : ((unipHomeo v y : unip v) : G) = unipotentGL2 y := rfl

theorem unipHomeo_add (y y' : F) : unipHomeo v (y + y') = unipHomeo v y * unipHomeo v y' :=
  Subtype.ext (by simp [unipHomeo_apply_coe, unipotentGL2_add])

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ v

scoped instance secondCountable_localGL' : SecondCountableTopology G := secondCountableTopology_localGL v

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip v) := (isClosed_unip v).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip v) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip v : Subgroup G) : Set G)

theorem isMulRightInvariant_unip (μN : Measure (unip v)) [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  refine ⟨fun n₀ => ?_⟩
  have h : (fun n : unip v => n * n₀) = fun n => n₀ * n := funext fun n => unip_comm v n n₀
  rw [h]
  exact map_mul_left_eq_self μN n₀

def unipMeasure (ν : Measure F) : Measure (unip v) := Measure.map (unipHomeo v) ν

theorem measurable_unipHomeo : Measurable (unipHomeo v) := (unipHomeo v).continuous.measurable

scoped instance isHaarMeasure_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] : (unipMeasure v ν).IsHaarMeasure where
  map_mul_left_eq_self n₀ := by
    obtain ⟨y₀, rfl⟩ : ∃ y₀, unipHomeo v y₀ = n₀ := ⟨(unipHomeo v).symm n₀, (unipHomeo v).apply_symm_apply n₀⟩
    unfold unipMeasure
    rw [Measure.map_map (measurable_const_mul _) (measurable_unipHomeo v)]
    have hcomp : ((fun n : unip v => unipHomeo v y₀ * n) ∘ (unipHomeo v)) = (unipHomeo v) ∘ fun y : F => y₀ + y := by
      funext y
      simp [Function.comp_apply, unipHomeo_add]
    rw [hcomp, ← Measure.map_map (measurable_unipHomeo v) (measurable_const_add _), map_add_left_eq_self]
  lt_top_of_isCompact K hK := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo v) hK.measurableSet]
    have : (unipHomeo v) ⁻¹' K = (unipHomeo v).symm '' K := by
      rw [← Homeomorph.image_symm]
    rw [this]
    exact (hK.image (unipHomeo v).symm.continuous).measure_lt_top
  open_pos U hU hne := by
    unfold unipMeasure
    rw [Measure.map_apply (measurable_unipHomeo v) hU.measurableSet]
    exact (hU.preimage (unipHomeo v).continuous).measure_ne_zero ν (hne.preimage (unipHomeo v).surjective)

scoped instance sFinite_unipMeasure (ν : Measure F) [ν.IsAddHaarMeasure] : SFinite (unipMeasure v ν) :=
  sFinite_unipHaar v _

theorem lintegral_unip_eq (ν : Measure F) (h : unip v → ℝ≥0∞) :
    ∫⁻ n, h n ∂(unipMeasure v ν) = ∫⁻ y, h (unipHomeo v y) ∂ν :=
  lintegral_map_equiv h (unipHomeo v).toMeasurableEquiv

end Fold

section FoldGeneric

theorem lintegral_eq_lintegral_lintegral_mul_density
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] [SFinite μH]
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ g, Φ g ∂μ = ∫⁻ g, (∫⁻ x : H, Φ ((x : G) * g) ∂μH) * HaarQuotient.density H μH g ∂μ := by
  rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH Φ hΦ]
  set Ξ : MulAction.orbitRel.Quotient H G → ℝ≥0∞ := fun q => ∫⁻ x : H, Φ ((x : G) * q.out) ∂μH with hΞ
  have hΞm : Measurable Ξ := HaarQuotient.measurable_lintegral_mul_out H hH μH Φ hΦ
  have hmk : Measurable (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) := measurable_quotient_mk''
  change ∫⁻ q, Ξ q ∂(Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
    (μ.withDensity (HaarQuotient.density H μH))) = _
  rw [lintegral_map hΞm hmk,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density H μH) (g := fun a => Ξ (Quotient.mk'' a))
      (hΞm.comp hmk)]
  refine lintegral_congr fun g => ?_
  rw [Pi.mul_apply, mul_comm]
  congr 1

  have hrel : @Setoid.r _ (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
    Quotient.mk_out' g
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨n, hn⟩ := hrel
  change ∫⁻ x : H, Φ ((x : G) * (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) ∂μH = _
  rw [← hn, Subgroup.smul_def, smul_eq_mul]
  have := lintegral_mul_right_eq_self (μ := μH) (fun x : H => Φ ((x : G) * g)) n
  simpa only [Subgroup.coe_mul, mul_assoc] using this

end FoldGeneric

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

section UnipShell

open LanglandsTunnell.CubicInduction

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem unipotentGL2_mul_apply_one (y : F) (g : G) (j : Fin 2) :
    ((unipotentGL2 y * g : G) : Mat) 1 j = (g : Mat) 1 j := by
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem det_unipotentGL2_mul (y : F) (g : G) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 y * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, det_unipotentGL2, one_mul]

theorem minorSup_iotaGL_unip_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (y : F) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    minorSup (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) =
      qR v ^ (-dn.2) := by
  rw [minorSup_iotaGL, unipotentGL2_mul_apply_one, unipotentGL2_mul_apply_one, ← minorSup_iotaGL,
    minorSup_iotaGL_shell hϖ hπ dn hk]

theorem detSize_iotaGL_unip_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (y : F) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    detSize (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) =
      qR v ^ (-(dn.2 + dn.1)) * qR v ^ (-dn.2) := by
  rw [detSize_iotaGL, ← Matrix.GeneralLinearGroup.val_det_apply, det_unipotentGL2_mul,
    Matrix.GeneralLinearGroup.val_det_apply, ← detSize_iotaGL, detSize_iotaGL_shell hϖ hπ dn hk]

theorem gauge_unip_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W' : LocalGL3 v → ℂ} {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W' h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W' h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d) (y : F) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    (¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) →
        W' (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) = 0) ∧
      ‖W' (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)))‖ ≤
        |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
  have hq := qR_ne_zero v
  obtain ⟨hvan, hbd⟩ := hg (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
    diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)))
  have hr1 : detSize (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
      diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) *
        lastRowSup (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
          diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) /
        minorSup (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
          diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) ^ 2 = qR v ^ (-dn.1) := by
    rw [detSize_iotaGL_unip_shell hϖ hπ y dn hk, lastRowSup_iotaGL, minorSup_iotaGL_unip_shell hϖ hπ y dn hk, mul_one]
    rw [div_eq_iff (pow_ne_zero _ (zpow_ne_zero _ hq)), ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq, ← zpow_add₀ hq]
    congr 1
    push_cast
    ring
  have hr2 : minorSup (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
      diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) /
        lastRowSup (iotaGL (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
          diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))) ^ 2 = qR v ^ (-dn.2) := by
    rw [minorSup_iotaGL_unip_shell hϖ hπ y dn hk, lastRowSup_iotaGL, one_pow, div_one]
  rw [hr1, hr2] at hvan hbd
  have hpow : qR v ^ (-dn.1) * qR v ^ (-dn.2) = qR v ^ (-(dn.1 + dn.2)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  refine ⟨fun hmn => hvan fun hB => hmn ⟨hm₀ _ hB.1, hm₀ _ hB.2⟩, ?_⟩
  have hnn : 0 ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := mul_nonneg (abs_nonneg C) (zpow_nonneg (qR_pos v).le _)
  by_cases hB : qR v ^ (-dn.1) ≤ B ∧ qR v ^ (-dn.2) ≤ B
  · calc _ ≤ C / (qR v ^ (-dn.1) * qR v ^ (-dn.2)) ^ t := hbd hB
      _ = C * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := by
          rw [hpow, ← zpow_natCast, ← zpow_mul, div_eq_mul_inv, ← zpow_neg]
          congr 2; ring
      _ ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (zpow_nonneg (qR_pos v).le _)
  · rw [hvan hB, norm_zero]
    exact hnn

theorem norm_cpow_unip_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (s : ℂ) (y : F) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    ‖((LanglandsTunnell.TateLocal.modulus
        ((Matrix.GeneralLinearGroup.det
            (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) :
              (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)‖ =
      qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)) := by
  rw [det_unipotentGL2_mul, coe_modulus_det_shell hϖ hπ dn hk, Complex.norm_cpow_eq_rpow_re_of_pos (zpow_pos (qR_pos v) _),
    ← Real.rpow_intCast, ← Real.rpow_mul (qR_pos v).le]
  congr 1
  have hre : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by simp [Complex.sub_re]
  rw [hre]
  push_cast
  ring

theorem shellRep_eq_diagonal2 (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 =
      diagonal2 v ![piUnit hπ ^ (dn.2 + dn.1), piUnit hπ ^ dn.2] := by
  rw [shellRep_eq_diagU hπ]
  refine Units.ext ?_
  rw [coe_diagU, diagonal2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end UnipShell

section ShellAlgebra

variable {v : HeightOneSpectrum (𝓞 ℚ)}

def rOne (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (ρ₁ σ : ℝ) : ℝ := ρ₁ * qR v ^ ((t : ℝ) + 1 - σ)

def rTwo (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (ρ₀ ρ₁ σ : ℝ) : ℝ := ρ₀ * ρ₁ * qR v ^ ((t : ℝ) + 1 - 2 * σ)

theorem rOne_pos (t : ℕ) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (σ : ℝ) : 0 < rOne v t ρ₁ σ :=
  mul_pos hρ₁ (Real.rpow_pos_of_pos (qR_pos v) _)

theorem rTwo_pos (t : ℕ) {ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (σ : ℝ) : 0 < rTwo v t ρ₀ ρ₁ σ :=
  mul_pos (mul_pos hρ₀ hρ₁) (Real.rpow_pos_of_pos (qR_pos v) _)

def shellMajorant (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (ρ₀ ρ₁ σ : ℝ) (m₀ : ℤ) (dn : ℤ × ℤ) : ℝ :=
  (if m₀ ≤ dn.1 then rOne v t ρ₁ σ ^ dn.1 else 0) * (if m₀ ≤ dn.2 then rTwo v t ρ₀ ρ₁ σ ^ dn.2 else 0)

theorem shellMajorant_nonneg (t : ℕ) {ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (σ : ℝ) (m₀ : ℤ) (dn : ℤ × ℤ) :
    0 ≤ shellMajorant v t ρ₀ ρ₁ σ m₀ dn :=
  mul_nonneg (indicator_zpow_nonneg (rOne_pos t hρ₁ σ) _ _) (indicator_zpow_nonneg (rTwo_pos t hρ₀ hρ₁ σ) _ _)

theorem summable_shellMajorant (t : ℕ) {ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (σ : ℝ) (m₀ : ℤ)
    (h₁ : rOne v t ρ₁ σ < 1) (h₂ : rTwo v t ρ₀ ρ₁ σ < 1) : Summable (shellMajorant v t ρ₀ ρ₁ σ m₀) :=
  (summable_indicator_zpow (rOne_pos t hρ₁ σ) h₁ m₀).mul_of_nonneg (summable_indicator_zpow (rTwo_pos t hρ₀ hρ₁ σ) h₂ m₀)
    (fun _ => indicator_zpow_nonneg (rOne_pos t hρ₁ σ) _ _) (fun _ => indicator_zpow_nonneg (rTwo_pos t hρ₀ hρ₁ σ) _ _)

theorem shellMajorant_of_le (t : ℕ) (ρ₀ ρ₁ σ : ℝ) {m₀ : ℤ} {dn : ℤ × ℤ} (h : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2) :
    shellMajorant v t ρ₀ ρ₁ σ m₀ dn = rOne v t ρ₁ σ ^ dn.1 * rTwo v t ρ₀ ρ₁ σ ^ dn.2 := by
  rw [shellMajorant, if_pos h.1, if_pos h.2]

def shellPointwise (v : HeightOneSpectrum (𝓞 ℚ)) (t : ℕ) (C CJ ρ₀ ρ₁ σ : ℝ) (dn : ℤ × ℤ) : ℝ :=
  |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)) *
    (ρ₀ ^ dn.2 * ρ₁ ^ (dn.2 + dn.1) * qR v ^ (-(dn.1 : ℝ) / 2) * CJ)

theorem shellPointwise_nonneg (t : ℕ) (C : ℝ) {CJ ρ₀ ρ₁ : ℝ} (hCJ : 0 ≤ CJ) (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (σ : ℝ)
    (dn : ℤ × ℤ) : 0 ≤ shellPointwise v t C CJ ρ₀ ρ₁ σ dn := by
  have hq := (qR_pos v).le
  unfold shellPointwise
  exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg C) (zpow_nonneg hq _)) (Real.rpow_nonneg hq _))
    (mul_nonneg (mul_nonneg (mul_nonneg (zpow_nonneg hρ₀.le _) (zpow_nonneg hρ₁.le _)) (Real.rpow_nonneg hq _)) hCJ)

theorem qR_zpow_mul_shellPointwise (t : ℕ) (C CJ : ℝ) {ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) (σ : ℝ)
    (dn : ℤ × ℤ) :
    qR v ^ dn.1 * shellPointwise v t C CJ ρ₀ ρ₁ σ dn = (|C| * CJ) * (rOne v t ρ₁ σ ^ dn.1 * rTwo v t ρ₀ ρ₁ σ ^ dn.2) := by
  have hq := qR_pos v
  unfold shellPointwise rOne rTwo
  rw [mul_zpow, mul_zpow, ← Real.rpow_intCast (qR v) dn.1, ← Real.rpow_intCast (qR v) ((t : ℤ) * (dn.1 + dn.2)),
    ← Real.rpow_intCast (qR v ^ ((t : ℝ) + 1 - σ)) dn.1, ← Real.rpow_intCast (qR v ^ ((t : ℝ) + 1 - 2 * σ)) dn.2,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, zpow_add₀ hρ₁.ne']
  have key : ∀ x y : ℝ, qR v ^ x * qR v ^ y = qR v ^ (x + y) := fun x y => (Real.rpow_add hq x y).symm
  calc qR v ^ ((dn.1 : ℤ) : ℝ) * (|C| * qR v ^ (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) *
        qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)) *
          (ρ₀ ^ dn.2 * (ρ₁ ^ dn.2 * ρ₁ ^ dn.1) * qR v ^ (-(dn.1 : ℝ) / 2) * CJ))
      = |C| * CJ * (ρ₁ ^ dn.1 * (ρ₀ ^ dn.2 * ρ₁ ^ dn.2)) * (qR v ^ ((dn.1 : ℤ) : ℝ) *
          qR v ^ (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2)) *
            qR v ^ (-(dn.1 : ℝ) / 2)) := by ring
    _ = |C| * CJ * (ρ₁ ^ dn.1 * (ρ₀ ^ dn.2 * ρ₁ ^ dn.2)) * qR v ^ (((dn.1 : ℤ) : ℝ) + (((t : ℤ) * (dn.1 + dn.2) : ℤ) : ℝ) +
          (-(2 * (dn.2 : ℝ) + dn.1)) * (σ - 1 / 2) + -(dn.1 : ℝ) / 2) := by rw [key, key, key]
    _ = |C| * CJ * (ρ₁ ^ dn.1 * (ρ₀ ^ dn.2 * ρ₁ ^ dn.2)) *
          qR v ^ (((t : ℝ) + 1 - σ) * ((dn.1 : ℤ) : ℝ) + ((t : ℝ) + 1 - 2 * σ) * ((dn.2 : ℤ) : ℝ)) := by
        congr 2
        push_cast
        ring
    _ = |C| * CJ * (ρ₁ ^ dn.1 * qR v ^ (((t : ℝ) + 1 - σ) * ((dn.1 : ℤ) : ℝ)) *
          ((ρ₀ * ρ₁) ^ dn.2 * qR v ^ (((t : ℝ) + 1 - 2 * σ) * ((dn.2 : ℤ) : ℝ)))) := by
        rw [← key, mul_zpow]; ring

theorem exists_abscissa (t : ℕ) {ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₁ : 0 < ρ₁) :
    ∃ σ₂ : ℝ, ∀ σ : ℝ, σ₂ < σ → rOne v t ρ₁ σ < 1 ∧ rTwo v t ρ₀ ρ₁ σ < 1 := by
  have hq := one_lt_qR v
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (max ρ₁ (ρ₀ * ρ₁)) hq
  have hj1 : ρ₁ < qR v ^ (j : ℝ) := by rw [Real.rpow_natCast]; exact (le_max_left _ _).trans_lt hj
  have hj2 : ρ₀ * ρ₁ < qR v ^ (j : ℝ) := by rw [Real.rpow_natCast]; exact (le_max_right _ _).trans_lt hj
  have h3 : qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 1) = qR v ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add (qR_pos v)]; congr 1; ring
  have h4 : qR v ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  refine ⟨(t : ℝ) + j + 2, fun σ hσ => ⟨?_, ?_⟩⟩
  · have h1 : qR v ^ ((t : ℝ) + 1 - σ) < qR v ^ (-(j : ℝ) - 1) := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
    calc rOne v t ρ₁ σ < ρ₁ * qR v ^ (-(j : ℝ) - 1) := mul_lt_mul_of_pos_left h1 hρ₁
      _ ≤ qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 1) := mul_le_mul_of_nonneg_right hj1.le (Real.rpow_nonneg (qR_pos v).le _)
      _ = qR v ^ (-(1 : ℝ)) := h3
      _ < 1 := h4
  · have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have h1 : qR v ^ ((t : ℝ) + 1 - 2 * σ) < qR v ^ (-(j : ℝ) - 1) := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
    calc rTwo v t ρ₀ ρ₁ σ < ρ₀ * ρ₁ * qR v ^ (-(j : ℝ) - 1) := mul_lt_mul_of_pos_left h1 (mul_pos hρ₀ hρ₁)
      _ ≤ qR v ^ (j : ℝ) * qR v ^ (-(j : ℝ) - 1) := mul_le_mul_of_nonneg_right hj2.le (Real.rpow_nonneg (qR_pos v).le _)
      _ = qR v ^ (-(1 : ℝ)) := h3
      _ < 1 := h4

end ShellAlgebra

section Folded

open LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

variable {ϖ : HeightOneSpectrum.adicCompletionIntegers ℚ v}

theorem norm_char_zpow (η : (HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ) (u : (HeightOneSpectrum.adicCompletion ℚ v)ˣ)
    (n : ℤ) : ‖((η (u ^ n) : ℂˣ) : ℂ)‖ = ‖((η u : ℂˣ) : ℂ)‖ ^ n := by
  rw [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow]

theorem sqrt_norm_shell
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) (dn : ℤ × ℤ) :
    Real.sqrt (‖((piUnit hπ ^ (dn.2 + dn.1) : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)‖ /
        ‖((piUnit hπ ^ dn.2 : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) : F)‖) = qR v ^ (-(dn.1 : ℝ) / 2) := by
  have hq := qR_pos v
  rw [coe_piUnit_zpow, coe_piUnit_zpow, norm_uniformizer_zpow hϖ, norm_uniformizer_zpow hϖ, ← zpow_sub₀ hq.ne',
    Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

theorem lintegral_phi_unip_shell_le
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W : LocalGL3 v → ℂ} {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d)
    (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ v)ˣ →* ℂˣ)) {f : G → ℂ} (w₀ : G) (ν : Measure F)
    (hJdiag : ∀ (t₁ t₂ : (HeightOneSpectrum.adicCompletion ℚ v)ˣ) (g : G),
      ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (diagonal2 v ![t₁, t₂] * g))‖ₑ ∂ν =
        ENNReal.ofReal (‖((χ 0 t₂ : ℂˣ) : ℂ)‖ * ‖((χ 1 t₁ : ℂˣ) : ℂ)‖ * Real.sqrt (‖(t₁ : F)‖ / ‖(t₂ : F)‖)) *
          ∫⁻ y, ‖f (w₀ * unipotentGL2 y * g)‖ₑ ∂ν)
    {CJ : ℝ≥0} (hJbd : ∀ k ∈ kzero v, ∫⁻ y, ‖f (w₀ * unipotentGL2 y * k)‖ₑ ∂ν ≤ CJ)
    (s : ℂ) (dn : ℤ × ℤ) {k : G} (hk : k ∈ kzero v) :
    ∫⁻ y, ‖phi v W f w₀ s (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k))‖ₑ ∂ν ≤
      ENNReal.ofReal (shellPointwise v t C CJ ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re dn) := by
  have hq := (qR_pos v).le
  set a : G := scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 with ha
  set K₁ : ℝ := |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) * qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)) with hK₁
  have hK₁nn : 0 ≤ K₁ := mul_nonneg (mul_nonneg (abs_nonneg C) (zpow_nonneg hq _)) (Real.rpow_nonneg hq _)

  have hpt : ∀ y : F, ‖phi v W f w₀ s (unipotentGL2 y * (a * k))‖ₑ ≤
      ENNReal.ofReal K₁ * ‖f (w₀ * unipotentGL2 y * (a * k))‖ₑ := by
    intro y
    have hW := (gauge_unip_shell hϖ hπ hg hm₀ y dn hk).2
    have hdet := norm_cpow_unip_shell hϖ hπ s y dn hk
    rw [← ha] at hW hdet
    have hCq : 0 ≤ |C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2)) := mul_nonneg (abs_nonneg C) (zpow_nonneg hq _)
    unfold phi
    rw [enorm_mul, enorm_mul, ← ofReal_norm (W _), ← ofReal_norm (_ ^ _), hdet]
    calc ENNReal.ofReal ‖W (iotaGL (unipotentGL2 y * (a * k)))‖ * ‖f (w₀ * (unipotentGL2 y * (a * k)))‖ₑ *
          ENNReal.ofReal (qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2)))
        ≤ ENNReal.ofReal (|C| * qR v ^ ((t : ℤ) * (dn.1 + dn.2))) * ‖f (w₀ * (unipotentGL2 y * (a * k)))‖ₑ *
          ENNReal.ofReal (qR v ^ ((-(2 * (dn.2 : ℝ) + dn.1)) * (s.re - 1 / 2))) := by
          gcongr
      _ = ENNReal.ofReal K₁ * ‖f (w₀ * unipotentGL2 y * (a * k))‖ₑ := by
          rw [hK₁, mul_right_comm, ← ENNReal.ofReal_mul hCq, ← mul_assoc w₀]
  calc ∫⁻ y, ‖phi v W f w₀ s (unipotentGL2 y * (a * k))‖ₑ ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal K₁ * ‖f (w₀ * unipotentGL2 y * (a * k))‖ₑ ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal K₁ * ∫⁻ y, ‖f (w₀ * unipotentGL2 y * (a * k))‖ₑ ∂ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal K₁ * (ENNReal.ofReal (‖((χ 0 (piUnit hπ ^ dn.2) : ℂˣ) : ℂ)‖ *
          ‖((χ 1 (piUnit hπ ^ (dn.2 + dn.1)) : ℂˣ) : ℂ)‖ * qR v ^ (-(dn.1 : ℝ) / 2)) *
            ∫⁻ y, ‖f (w₀ * unipotentGL2 y * k)‖ₑ ∂ν) := by
        rw [ha, shellRep_eq_diagonal2 hπ dn, hJdiag, sqrt_norm_shell hϖ hπ dn]
    _ ≤ ENNReal.ofReal K₁ * (ENNReal.ofReal (‖((χ 0 (piUnit hπ ^ dn.2) : ℂˣ) : ℂ)‖ *
          ‖((χ 1 (piUnit hπ ^ (dn.2 + dn.1)) : ℂˣ) : ℂ)‖ * qR v ^ (-(dn.1 : ℝ) / 2)) * (CJ : ℝ≥0∞)) := by
        gcongr
        exact hJbd k hk
    _ = _ := by
        rw [norm_char_zpow, norm_char_zpow, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hK₁nn]
        rw [hK₁, shellPointwise]

theorem phi_unip_shell_eq_zero
    (hϖ : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ v) (HeightOneSpectrum.adicCompletion ℚ v) ϖ) =
      WithZero.exp (-1 : ℤ))
    (hπ : algebraMap (O) (F) ϖ ≠ 0) {W : LocalGL3 v → ℂ} {B : ℝ} {t : ℕ} {C : ℝ}
    (hg : ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    {m₀ : ℤ} (hm₀ : ∀ d : ℤ, qR v ^ (-d) ≤ B → m₀ ≤ d) (f : G → ℂ) (w₀ : G) (s : ℂ) (dn : ℤ × ℤ)
    (hmn : ¬ (m₀ ≤ dn.1 ∧ m₀ ≤ dn.2)) (y : F) {k : G} (hk : k ∈ kzero v) :
    phi v W f w₀ s (unipotentGL2 y * (scalarPi (algebraMap (O) (F) ϖ) hπ ^ dn.2 * diagZ (algebraMap (O) (F) ϖ) hπ dn.1 * k)) = 0 := by
  unfold phi
  rw [(gauge_unip_shell hϖ hπ hg hm₀ y dn hk).1 hmn, zero_mul, zero_mul]

end Folded

end RSUnfoldConv
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge.RSUnfoldConv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge.RSUnfoldConv"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker LanglandsTunnell.CubicInduction RSUnfoldConv

open scoped ENNReal NNReal

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 p → ℂ)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (hWgauge : ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (ϖ : (p.adicCompletion ℚ)ˣ) (hϖ : Valued.v (ϖ : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (hdom : ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ < ‖((χ 1 ϖ : ℂˣ) : ℂ)‖)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (hfsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (W (iotaGL g) * f (w₀ * g)) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                (s - 1 / 2)) μ₂ := by
  intro μ₂ _
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p

  set ϖO : p.adicCompletionIntegers ℚ := ⟨(ϖ : p.adicCompletion ℚ),
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by rw [hϖ]; exact le_of_lt (WithZero.exp_lt_exp.mpr (by norm_num)))⟩ with hϖO
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖO ≠ 0 := by
    change (ϖ : p.adicCompletion ℚ) ≠ 0; exact ϖ.ne_zero
  have hϖ' : Valued.v (algebraMap (HeightOneSpectrum.adicCompletionIntegers ℚ p)
      (HeightOneSpectrum.adicCompletion ℚ p) ϖO) = WithZero.exp (-1 : ℤ) := hϖ
  have hpiUnit : piUnit hπ = ϖ := Units.ext rfl

  set ν : Measure (p.adicCompletion ℚ) := Measure.addHaar with hν
  set μN : Measure ↥(unip p) := unipMeasure p ν with hμN
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_unip p μN

  obtain ⟨-, -, hJdiag, ⟨CJ, hJbd⟩⟩ :=
    LanglandsTunnell.CubicInduction.absoluteJacquetIntegral_lt_top_and_unipotent_and_diagonal2_and_bounded_of_mem_principalSeries2
      p χ cχ hcχ ϖ hϖ hdom f hf hfsm w₀ hw₀ ν

  obtain ⟨B, t, C, hg⟩ := hWgauge
  obtain ⟨m₀, -, hm₀⟩ := exists_cutoff p B
  have hρ₀ : 0 < ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hρ₁ : 0 < ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  obtain ⟨σ₂, hσ₂⟩ := exists_abscissa (v := p) t hρ₀ hρ₁
  refine ⟨σ₂, fun s hs => ?_⟩
  obtain ⟨hr₁, hr₂⟩ := hσ₂ s.re hs

  obtain ⟨hlc, -, -⟩ := mem_principalSeries2_iff.mp hf
  change Integrable (phi p W f w₀ s) μ₂
  have hΦm : Measurable (phi p W f w₀ s) := measurable_phi p hWsm hlc w₀ s
  refine ⟨hΦm.aestronglyMeasurable, ?_⟩
  change ∫⁻ g, ‖phi p W f w₀ s g‖ₑ ∂μ₂ < ∞

  rw [lintegral_eq_lintegral_lintegral_mul_density μ₂ (unip p) (isClosed_unip p) μN (fun g => ‖phi p W f w₀ s g‖ₑ)
    hΦm.enorm]
  set φ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞ := fun g => ∫⁻ x : ↥(unip p), ‖phi p W f w₀ s ((x : GL (Fin 2) _) * g)‖ₑ ∂μN
    with hφdef
  have hφN : ∀ x ∈ unip p, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ (x * g) = φ g := by
    intro x hx g
    simp only [hφdef]
    have := lintegral_mul_right_eq_self (μ := μN)
      (fun n : ↥(unip p) => ‖phi p W f w₀ s ((n : GL (Fin 2) _) * g)‖ₑ) ⟨x, hx⟩
    simpa only [Subgroup.coe_mul, mul_assoc] using this
  have hφm : Measurable φ := by
    have hΞ := HaarQuotient.measurable_lintegral_mul_out (unip p) (isClosed_unip p) μN _ hΦm.enorm
    have hmk := measurable_quotient_mk'' (s := MulAction.orbitRel (↥(unip p)) (GL (Fin 2) (p.adicCompletion ℚ)))
    have hfib : ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        (fun q : MulAction.orbitRel.Quotient (↥(unip p)) (GL (Fin 2) (p.adicCompletion ℚ)) =>
          ∫⁻ x : ↥(unip p), ‖phi p W f w₀ s ((x : GL (Fin 2) _) * q.out)‖ₑ ∂μN) (Quotient.mk'' g) = φ g := by
      intro g
      simp only [hφdef]
      have hrel : @Setoid.r _ (MulAction.orbitRel (↥(unip p)) (GL (Fin 2) (p.adicCompletion ℚ)))
          ((Quotient.mk'' g : MulAction.orbitRel.Quotient (↥(unip p)) (GL (Fin 2) (p.adicCompletion ℚ))).out) g :=
        Quotient.mk_out' g
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨n, hn⟩ := hrel
      rw [← hn, Subgroup.smul_def, smul_eq_mul]
      have := lintegral_mul_right_eq_self (μ := μN)
        (fun x : ↥(unip p) => ‖phi p W f w₀ s ((x : GL (Fin 2) _) * g)‖ₑ) n
      simpa only [Subgroup.coe_mul, mul_assoc] using this
    have hφeq : φ = (fun q : MulAction.orbitRel.Quotient (↥(unip p)) (GL (Fin 2) (p.adicCompletion ℚ)) =>
          ∫⁻ x : ↥(unip p), ‖phi p W f w₀ s ((x : GL (Fin 2) _) * q.out)‖ₑ ∂μN) ∘ Quotient.mk'' :=
      funext fun g => (hfib g).symm
    rw [hφeq]
    exact hΞ.comp hmk
  change ∫⁻ g, φ g * HaarQuotient.density (unip p) μN g ∂μ₂ < ∞

  obtain ⟨hsl, hsum⟩ := AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2 ℚ p ϖO hπ hϖ' μ₂ μN φ hφm hφN
  rw [hsum]

  have hE₁0 : μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) ≠ 0 := by
    have := (hsl 0).1
    rwa [shellSlice_zero_eq hπ] at this
  have hc₀ : (μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hE₁0
  have hK₀ : μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) < ∞ :=
    (isCompact_kzero p).measure_lt_top
  have hKr : 0 ≤ |C| * (CJ : ℝ) := mul_nonneg (abs_nonneg C) CJ.2
  have hg_nn := shellMajorant_nonneg (v := p) t hρ₀ hρ₁ s.re m₀
  have hg_sum := summable_shellMajorant (v := p) t hρ₀ hρ₁ s.re m₀ hr₁ hr₂
  have hmeasK : MeasurableSet ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) := (isOpen_kzero p).measurableSet

  have hφshell : ∀ (dn : ℤ × ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)), k ∈ kzero p →
      φ (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k) =
        ∫⁻ y, ‖phi p W f w₀ s (unipotentGL2 y * (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 *
          diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k))‖ₑ ∂ν := by
    intro dn k _
    simp only [hφdef, hμN]
    rw [lintegral_unip_eq]
    rfl

  have hterm : ∀ dn : ℤ × ℤ,
      (μN {x : ↥(unip p) |
          (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (p.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1) ∈
          kzero p})⁻¹ *
        ∫⁻ k in ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          φ (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k)
            ∂μ₂ ≤
      ((μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
        μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) *
        ENNReal.ofReal ((|C| * (CJ : ℝ)) *
          shellMajorant p t ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re m₀ dn) := by
    intro dn

    have hslice : μN {x : ↥(unip p) |
          (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (p.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1) ∈
          kzero p} =
        ENNReal.ofReal (qR p ^ (-dn.1)) *
          μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}) := by
      rw [shellSlice_eq hπ dn, LanglandsTunnell.CubicInduction.measure_unipotentEntry_preimage_mul_eq p μN (piUnit hπ ^ dn.1),
        ← ENNReal.ofReal_coe_nnreal, coe_modulus_eq_norm, coe_piUnit_zpow, norm_uniformizer_zpow hϖ']
    have hqd : 0 < qR p ^ (-dn.1) := zpow_pos (qR_pos p) _
    have hinv : (μN {x : ↥(unip p) |
          (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1)⁻¹ *
            (x : GL (Fin 2) (p.adicCompletion ℚ)) *
            (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1) ∈
          kzero p})⁻¹ =
        ENNReal.ofReal (qR p ^ dn.1) *
          (μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ := by
      rw [hslice, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hqd).ne') (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_inv_of_pos hqd, ← zpow_neg, neg_neg]
    by_cases hmn : m₀ ≤ dn.1 ∧ m₀ ≤ dn.2
    ·
      have hpt : ∀ k ∈ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          φ (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k)
            ≤ ENNReal.ofReal (shellPointwise p t C CJ ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re dn) := by
        intro k hk
        rw [hφshell dn k hk]
        exact lintegral_phi_unip_shell_le hϖ' hπ hg hm₀ χ w₀ ν hJdiag hJbd s dn hk
      calc _ ≤ (μN {x : ↥(unip p) |
              (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1)⁻¹ *
                (x : GL (Fin 2) (p.adicCompletion ℚ)) *
                (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 *
                  diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1) ∈ kzero p})⁻¹ *
            ∫⁻ k in ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
              ENNReal.ofReal (shellPointwise p t C CJ ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re dn)
                ∂μ₂ :=
            mul_le_mul' le_rfl (setLIntegral_mono' hmeasK hpt)
        _ = (ENNReal.ofReal (qR p ^ dn.1) *
              (μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹) *
              (ENNReal.ofReal (shellPointwise p t C CJ ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re dn) *
                μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) := by
            rw [hinv, setLIntegral_const]
        _ = ((μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
                Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
              μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) *
              (ENNReal.ofReal (qR p ^ dn.1) *
                ENNReal.ofReal (shellPointwise p t C CJ ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re dn)) := by
            ring
        _ = _ := by
            rw [← ENNReal.ofReal_mul (zpow_nonneg (qR_pos p).le _),
              qR_zpow_mul_shellPointwise t C CJ hρ₀ hρ₁ s.re dn, shellMajorant_of_le t _ _ s.re hmn]
    ·
      have hzero : ∀ k ∈ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          φ (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k)
            ≤ 0 := by
        intro k hk
        rw [hφshell dn k hk]
        refine le_of_eq ?_
        rw [lintegral_congr (fun y => by rw [phi_unip_shell_eq_zero hϖ' hπ hg hm₀ f w₀ s dn hmn y hk, enorm_zero]),
          lintegral_zero]
      have hint : ∫⁻ k in ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          φ (scalarPi (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ ^ dn.2 * diagZ (algebraMap _ (p.adicCompletion ℚ) ϖO) hπ dn.1 * k)
            ∂μ₂ = 0 :=
        le_antisymm ((setLIntegral_mono' hmeasK hzero).trans (by rw [setLIntegral_const, zero_mul])) bot_le
      rw [hint, mul_zero]
      exact bot_le

  calc _ ≤ ∑' dn : ℤ × ℤ,
        ((μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) *
          ENNReal.ofReal ((|C| * (CJ : ℝ)) *
            shellMajorant p t ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re m₀ dn) :=
          ENNReal.tsum_le_tsum hterm
    _ = ((μN ((fun y : ↥(unip p) => ((y : GL (Fin 2) (p.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1) ⁻¹' {z | Valued.v z ≤ 1}))⁻¹ *
          μ₂ ((kzero p : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) *
          ENNReal.ofReal (∑' dn : ℤ × ℤ, (|C| * (CJ : ℝ)) *
            shellMajorant p t ‖((χ 0 (piUnit hπ) : ℂˣ) : ℂ)‖ ‖((χ 1 (piUnit hπ) : ℂˣ) : ℂ)‖ s.re m₀ dn) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun dn => mul_nonneg hKr (hg_nn dn)) (hg_sum.mul_left _)]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hc₀.lt_top hK₀) ENNReal.ofReal_lt_top

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_whittaker_iotaGL_mul_principalSeries2_antidiagonal_of_gauge (solution)
