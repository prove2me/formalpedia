-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2d1edd15-360a-520e-91f5-ada35c3f8cf1

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

namespace L2Box46

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "νa" => (selfDualHaarAt ℚ p)
local notation "νx" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
local notation "ψp" => (NumberField.StandardAddChar.psiLocal ℚ p)

theorem one_lt_qN : (1 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) :=
  NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p

theorem norm_le_norm_iff_v_le_v (x y : F) : ‖x‖ ≤ ‖y‖ ↔ Valued.v x ≤ Valued.v y := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, NNReal.coe_le_coe,
    (WithZeroMulInt.toNNReal_strictMono (one_lt_qN p)).le_iff_le]

theorem norm_eq_norm_iff_v_eq_v (x y : F) : ‖x‖ = ‖y‖ ↔ Valued.v x = Valued.v y := by
  constructor
  · intro h; exact le_antisymm ((norm_le_norm_iff_v_le_v p x y).1 h.le) ((norm_le_norm_iff_v_le_v p y x).1 h.ge)
  · intro h; exact le_antisymm ((norm_le_norm_iff_v_le_v p x y).2 h.le) ((norm_le_norm_iff_v_le_v p y x).2 h.ge)

theorem norm_eq_one_of_v_eq_one {x : F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [← norm_one (α := F)]; exact (norm_eq_norm_iff_v_eq_v p x 1).2 (by rw [h, Valuation.map_one])

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]; rfl

theorem v_eq_one_of_v_sub_one_le {a : F} {M : ℤ} (hM : 1 ≤ M) (h : Valued.v (a - 1) ≤ WithZero.exp (-M)) : Valued.v a = 1 := by
  have hlt : Valued.v (a - 1) < 1 := by
    refine lt_of_le_of_lt h ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have := Valuation.map_one_add_of_lt (Valued.v : Valuation F _) hlt
  rwa [add_sub_cancel] at this

theorem exp_neg_le_one {M : ℤ} (hM : 0 ≤ M) : WithZero.exp (-M) ≤ (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem mem_integers_of_v_le {x : F} {M : ℤ} (hM : 0 ≤ M) (h : Valued.v x ≤ WithZero.exp (-M)) : x ∈ (O) :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_trans h (exp_neg_le_one hM))

theorem unipotentGL2_eq_unipotent (x : F) : (unipotentGL2 x : G) = unipotent x := Units.ext rfl

theorem coe_chart (x : F) (a₁ a₂ : Fˣ) (y : F) :
    ((unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) : M2) =
      !![(a₁ : F) + x * (a₂ : F) * y, x * (a₂ : F); (a₂ : F) * y, (a₂ : F)] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_diagUnits2]
  show !![(1 : F), x; 0, 1] * !![(a₁ : F), 0; 0, (a₂ : F)] * !![(1 : F), 0; y, 1] = _
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_chart (x : F) (a₁ a₂ : Fˣ) (y : F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) = a₁ * a₂ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_chart, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem diagOne_coe (a : Fˣ) : ((diagOne a : G) : M2) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem chart_eq (x : F) (a₁ a₂ : Fˣ) (y : F) :
    (unipotentGL2 x * diagUnits2 a₁ a₂ * lowerUnipotentGL2 y : G) = unipotent x * (diagOne a₁ * (diagUnits2 1 a₂ * lowerUnipotentGL2 y)) := by
  have hd : (diagUnits2 a₁ a₂ : G) = diagOne a₁ * diagUnits2 1 a₂ := by
    apply Units.ext
    rw [Units.val_mul, coe_diagUnits2, coe_diagUnits2, diagOne_coe, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [unipotentGL2_eq_unipotent, hd]; simp only [mul_assoc]

theorem coe_unipotent (x : F) : ((unipotent x : G) : M2) = !![(1 : F), x; 0, 1] := rfl

theorem coe_scalar (a : Fˣ) : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) : M2) = !![(a : F), 0; 0, (a : F)] := by
  rw [show ((Matrix.GeneralLinearGroup.scalar (Fin 2) a : G) : M2) = Matrix.scalar (Fin 2) (a : F) from rfl,
    Matrix.scalar_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem det_wJ (wJ : G) (hwJ : (wJ : M2) = !![0, 1; -1, 0]) : Matrix.GeneralLinearGroup.det wJ = 1 :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hwJ, Matrix.det_fin_two_of, Units.val_one]; ring)

theorem coe_wJ_chart (wJ : G) (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (x : F) (β α : Fˣ) (y : F) :
    ((wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) : M2) =
      !![(β : F) * y, (β : F); -((α : F) + x * (β : F) * y), -(x * (β : F))] := by
  rw [Matrix.GeneralLinearGroup.coe_mul, hwJ, coe_chart]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_wJ_chart (wJ : G) (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (x : F) (β α : Fˣ) (y : F) :
    Matrix.GeneralLinearGroup.det (wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) = α * β := by
  rw [map_mul, det_wJ p wJ hwJ, det_chart, one_mul]

theorem transposeInvN_eq_of (X Y : G) (h : Matrix.transpose (Y : M2) * (X : M2) = 1) :
    transposeInvN (Fin 2) X = Y :=
  Units.ext (by rw [coe_transposeInvN, Matrix.coe_units_inv, Matrix.inv_eq_left_inv h, Matrix.transpose_transpose])

theorem transposeInvN_wJ_chart (wJ : G) (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (x : F) (β α : Fˣ) (y : F) :
    transposeInvN (Fin 2) (wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) =
      unipotent x * (Matrix.GeneralLinearGroup.scalar (Fin 2) α⁻¹ * (diagOne (α * β⁻¹) * (wJ * unipotent (-y)))) := by
  apply transposeInvN_eq_of
  rw [coe_wJ_chart p wJ hwJ, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_unipotent, coe_scalar,
    diagOne_coe, hwJ, coe_unipotent]
  have hα : (α : F) ≠ 0 := α.ne_zero
  have hβ : (β : F) ≠ 0 := β.ne_zero
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] <;> field_simp <;> ring

theorem diagOne_mul_wJ_eq (wJ : G) (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (α β : Fˣ) :
    (diagOne (α * β⁻¹) * wJ : G) = Matrix.GeneralLinearGroup.scalar (Fin 2) β⁻¹ * (diagOne α * wJ * diagOne β) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, diagOne_coe, diagOne_coe, diagOne_coe, coe_scalar, hwJ]
  have hβ : (β : F) ≠ 0 := β.ne_zero
  simp only [Units.val_inv_eq_inv_val, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

section Setup

scoped instance : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_GL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem measurable_unitsVal : Measurable (Units.val : Fˣ → F) := comap_measurable Units.val

scoped instance borelSpace_units : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := HeightOneSpectrum.adicCompletion ℚ p)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

scoped instance : (selfDualHaarAt ℚ p).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p

scoped instance isHaarMeasure_units : (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p _

theorem exists_uniformizer : ∃ ϖ : F, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer ℚ p
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation ℚ p)).symm π : F),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem v_uniformizer_zpow {ϖ : F} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem isOpen_vball (m : ℤ) : IsOpen {x : F | Valued.v x ≤ WithZero.exp m} := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer p
  have hset : {x : F | Valued.v x ≤ WithZero.exp m} =
      (fun x => ϖ ^ m * x) ⁻¹' (HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, v_uniformizer_zpow p hϖ, WithZero.exp_neg]
    constructor
    · intro h
      calc (WithZero.exp m)⁻¹ * Valued.v x ≤ (WithZero.exp m)⁻¹ * WithZero.exp m := mul_le_mul_right h _
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · intro h
      calc Valued.v x = WithZero.exp m * ((WithZero.exp m)⁻¹ * Valued.v x) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.exp_ne_zero, one_mul]
        _ ≤ WithZero.exp m * 1 := mul_le_mul_right h _
        _ = WithZero.exp m := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul _)

theorem isClosed_vball (γ : WithZero (Multiplicative ℤ)) : IsClosed {x : F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
  have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
  filter_upwards [Valued.locally_const hx0] with y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]; exact hx

theorem measurableSet_vball (γ : WithZero (Multiplicative ℤ)) : MeasurableSet {x : F | Valued.v x ≤ γ} :=
  (isClosed_vball p γ).measurableSet

theorem isCompact_integers : IsCompact ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) := by
  rw [← LanglandsTunnell.TateLocal.coe_integersPositiveCompacts]
  exact (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ p).isCompact

theorem vball_lt_top {M : ℤ} (hM : 0 ≤ M) : (selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-M)} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_integers p).measure_lt_top
  intro x hx; exact mem_integers_of_v_le p hM hx

theorem vball_pos (M : ℤ) : 0 < (selfDualHaarAt ℚ p) {x : F | Valued.v x ≤ WithZero.exp (-M)} :=
  (isOpen_vball p _).measure_pos _ ⟨0, by simp⟩

theorem isOpen_prinUnits (M : ℤ) : IsOpen {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_vball p _).preimage (Units.continuous_val.sub continuous_const)

theorem measurableSet_prinUnits (M : ℤ) : MeasurableSet {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_prinUnits p M).measurableSet

theorem isCompact_units_sphere : IsCompact {u : Fˣ | Valued.v (u : F) = 1} := by
  have hS : IsCompact {x : F | Valued.v x = 1} := by
    refine (isCompact_integers p).of_isClosed_subset ?_ (fun x hx => by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact le_of_eq hx)
    have : {x : F | Valued.v x = 1} = {x : F | Valued.v x ≤ 1} ∩ {x : F | Valued.v x ≤ WithZero.exp (-1 : ℤ)}ᶜ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
      constructor
      · intro h; rw [h]; refine ⟨le_rfl, ?_⟩
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
      · rintro ⟨h1, h2⟩
        by_cases hx : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
        · rw [hx] at h2; exact absurd h2 (not_lt.2 zero_le')
        · rw [← WithZero.exp_log hx] at h1 h2 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
          rw [WithZero.exp_lt_exp] at h2
          rw [← WithZero.exp_zero]; congr 1; omega
    rw [this]
    exact (isClosed_vball p 1).inter (isOpen_vball p _).isClosed_compl
  have himage : Units.val '' {u : Fˣ | Valued.v (u : F) = 1} = {x : F | Valued.v x = 1} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hx' : Valued.v x = 1 := hx
      have hx0 : x ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hx'; exact zero_ne_one hx'
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [(Units.isEmbedding_val₀ (G₀ := HeightOneSpectrum.adicCompletion ℚ p)).isCompact_iff, himage]
  exact hS

theorem prinUnits_lt_top {M : ℤ} (hM : 1 ≤ M) :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (isCompact_units_sphere p).measure_lt_top
  intro a ha; exact v_eq_one_of_v_sub_one_le p hM ha

theorem prinUnits_pos (M : ℤ) :
    0 < (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) : Measure Fˣ) {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)} :=
  (isOpen_prinUnits p M).measure_pos _ ⟨1, by simp⟩

end Setup

section Factors

theorem continuous_of_open_stabilizer (f : G → ℂ) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hU : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) : Continuous f := by
  refine continuous_def.2 fun s _ => ?_
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun k => g * k) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    show f (g * k) ∈ s
    rw [hU k hk g]; exact hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hUo

theorem continuous_modulusR_det : Continuous fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ)) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ))) = fun g : G => ‖((g : G) : M2).det‖ := by
    funext g; rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact continuous_norm.comp Units.continuous_val.matrix_det

theorem measurable_dens : Measurable fun q : F × Fˣ × Fˣ × F => modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F) := by
  have : (fun q : F × Fˣ × Fˣ × F => modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)) =
      fun q : F × Fˣ × Fˣ × F => ‖(((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)‖₊ := by
    funext q; rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
  rw [this]
  refine (continuous_nnnorm.comp (Units.continuous_val.comp ?_)).measurable
  exact (continuous_fst.comp continuous_snd).mul ((continuous_fst.comp (continuous_snd.comp continuous_snd)).inv)

theorem continuous_coe_char_of_trivial (θ : Fˣ →* ℂˣ) (M : ℤ)
    (hθ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-M) → θ a = 1) :
    Continuous fun a : Fˣ => ((θ a : ℂˣ) : ℂ) := by

  refine (IsLocallyConstant.continuous ?_)
  rw [IsLocallyConstant.iff_exists_open]
  intro a₀
  refine ⟨(fun a : Fˣ => a₀⁻¹ * a) ⁻¹' {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-M)},
    (isOpen_prinUnits p M).preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · show Valued.v (((a₀⁻¹ * a₀ : Fˣ) : F) - 1) ≤ WithZero.exp (-M)
    rw [inv_mul_cancel, Units.val_one, sub_self, Valuation.map_zero]; exact zero_le'
  · intro a ha
    have h1 : θ (a₀⁻¹ * a) = 1 := hθ _ ha
    have : θ a = θ a₀ := by
      calc θ a = θ (a₀ * (a₀⁻¹ * a)) := by rw [mul_inv_cancel_left]
        _ = θ a₀ * θ (a₀⁻¹ * a) := map_mul _ _ _
        _ = θ a₀ := by rw [h1, mul_one]
    rw [this]

theorem continuous_diagOne : Continuous fun a : Fˣ => (diagOne a : G) := by

  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (fun a : Fˣ => ((diagOne a : G) : M2)) = fun a : Fˣ => (!![(a : F), 0; 0, 1] : M2) :=
      funext fun a => diagOne_coe p a
    rw [show (Units.val ∘ fun a : Fˣ => (diagOne a : G)) = fun a : Fˣ => ((diagOne a : G) : M2) from rfl, this]
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun a : Fˣ => (((diagOne a : G)⁻¹ : G) : M2)) = fun a : Fˣ => (!![((a⁻¹ : Fˣ) : F), 0; 0, 1] : M2) :=
      funext fun a => by rw [← map_inv]; exact diagOne_coe p a⁻¹
    rw [this]
    refine continuous_matrix ?_
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using (Units.continuous_coe_inv : Continuous fun a : Fˣ => ((a⁻¹ : Fˣ) : F))
    all_goals (simp; exact continuous_const)

theorem continuous_transposeInvN : Continuous (fun g : G => transposeInvN (Fin 2) g) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun g : G => transposeInvN (Fin 2) g) = fun g : G => Matrix.transpose (((g⁻¹ : G) : M2)) :=
      funext fun g => coe_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_coe_inv.matrix_transpose
  · have : (fun g : G => (((transposeInvN (Fin 2) g)⁻¹ : G) : M2)) = fun g : G => Matrix.transpose (((g : G) : M2)) :=
      funext fun g => coe_inv_transposeInvN (Fin 2) g
    rw [this]
    exact Units.continuous_val.matrix_transpose

end Factors

section Chart

theorem continuous_unipotentGL2' : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : F => (!![(1 : F), x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : F => (!![(1 : F), -x; 0, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_lowerUnipotentGL2' : Continuous (fun y : F => (lowerUnipotentGL2 y : G)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun y : F => (!![(1 : F), 0; y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun y : F => (!![(1 : F), 0; -y, 1] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_diagUnits2' : Continuous (fun ab : Fˣ × Fˣ => (diagUnits2 ab.1 ab.2 : G)) := by
  have h1 : Continuous fun ab : Fˣ × Fˣ => ((ab.1 : Fˣ) : F) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun ab : Fˣ × Fˣ => ((ab.2 : Fˣ) : F) := Units.continuous_val.comp continuous_snd
  have h1' : Continuous fun ab : Fˣ × Fˣ => (((ab.1)⁻¹ : Fˣ) : F) := Units.continuous_coe_inv.comp continuous_fst
  have h2' : Continuous fun ab : Fˣ × Fˣ => (((ab.2)⁻¹ : Fˣ) : F) := Units.continuous_coe_inv.comp continuous_snd
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun ab : Fˣ × Fˣ => (!![((ab.1 : Fˣ) : F), 0; 0, ((ab.2 : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using continuous_const (y := (0 : F))
    · simpa using continuous_const (y := (0 : F))
    · simpa using h2
  · show Continuous fun ab : Fˣ × Fˣ => (!![(((ab.1)⁻¹ : Fˣ) : F), 0; 0, (((ab.2)⁻¹ : Fˣ) : F)] : M2)
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j
    · simpa using h1'
    · simpa using continuous_const (y := (0 : F))
    · simpa using continuous_const (y := (0 : F))
    · simpa using h2'

theorem continuous_chart :
    Continuous (fun q : F × Fˣ × Fˣ × F => (unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2 : G)) := by
  refine ((continuous_unipotentGL2' p |>.comp continuous_fst).mul ?_).mul
    ((continuous_lowerUnipotentGL2' p).comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  exact (continuous_diagUnits2' p).comp
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd))

end Chart

section BlockP4

theorem bp4_setCol22_self0 (X : M2) (j : Fin 2) (u : F × F) : setCol22 p X j u 0 j = u.1 := by
  simp [setCol22_apply]
theorem bp4_setCol22_self1 (X : M2) (j : Fin 2) (u : F × F) : setCol22 p X j u 1 j = u.2 := by
  simp [setCol22_apply]
theorem bp4_setCol22_other (X : M2) (j k : Fin 2) (hk : k ≠ j) (u : F × F) (i : Fin 2) : setCol22 p X j u i k = X i k := by
  rw [setCol22_apply, if_neg hk]

theorem bp4_col_step (j : Fin 2) (f g : F → ℂ) (h : M2 → ℂ) (hh : ∀ (X : M2) (u : F × F), h (setCol22 p X j u) = h X)
    (X : M2) :
    colFourier22 p ψp j (fun X : M2 => f (X 0 j) * g (X 1 j) * h X) X =
      tateFourier ψp νa f (X 0 j) * tateFourier ψp νa g (X 1 j) * h X := by
  haveI : SFinite (selfDualHaarAt ℚ p) := by unfold selfDualHaarAt; infer_instance
  rw [colFourier22_apply]
  have hpt : ∀ u : F × F,
      f (setCol22 p X j u 0 j) * g (setCol22 p X j u 1 j) * h (setCol22 p X j u) * ψp (u.1 * X 0 j + u.2 * X 1 j) =
        (f u.1 * ψp (u.1 * X 0 j)) * (g u.2 * ψp (u.2 * X 1 j)) * h X := by
    intro u
    rw [bp4_setCol22_self0, bp4_setCol22_self1, hh, AddChar.map_add_eq_mul]
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_prod_mul (μ := νa) (ν := νa) (fun x : F => f x * ψp (x * X 0 j)) (fun y : F => g y * ψp (y * X 1 j))]
  rfl

theorem matFourier22_prod_eq_prod_tateFourier (φ : Fin 2 → Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p) → ℂ)) (Y : M2) :
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) (fun X : M2 => ∏ i, ∏ j, φ i j (X i j)) Y =
      ∏ i, ∏ j, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p) (selfDualHaarAt ℚ p) (φ i j) (Y i j) := by

  have h1 : (fun X : M2 => ∏ i, ∏ j, φ i j (X i j)) =
      fun X : M2 => φ 0 1 (X 0 1) * φ 1 1 (X 1 1) * (φ 0 0 (X 0 0) * φ 1 0 (X 1 0)) := by
    funext X; simp only [Fin.prod_univ_two]; ring
  have hcol1 : colFourier22 p ψp 1 (fun X : M2 => ∏ i, ∏ j, φ i j (X i j)) =
      fun X : M2 => φ 0 0 (X 0 0) * φ 1 0 (X 1 0) *
        (tateFourier ψp νa (φ 0 1) (X 0 1) * tateFourier ψp νa (φ 1 1) (X 1 1)) := by
    funext X
    rw [h1, bp4_col_step p 1 (φ 0 1) (φ 1 1) (fun X : M2 => φ 0 0 (X 0 0) * φ 1 0 (X 1 0))
      (fun X u => by simp only [bp4_setCol22_other p X 1 0 (by decide)]) X]
    ring
  rw [matFourier22_eq, hcol1,
    bp4_col_step p 0 (φ 0 0) (φ 1 0) (fun X : M2 => tateFourier ψp νa (φ 0 1) (X 0 1) * tateFourier ψp νa (φ 1 1) (X 1 1))
      (fun X u => by simp only [bp4_setCol22_other p X 0 1 (by decide)]) Y]
  simp only [Fin.prod_univ_two]
  ring

end BlockP4

section Box

def indBall (m : ℤ) (x : F) : ℂ := Set.indicator {x : F | Valued.v x ≤ WithZero.exp m} (fun _ => (1 : ℂ)) x

def indBall1 (m : ℤ) (x : F) : ℂ := Set.indicator {x : F | Valued.v (x - 1) ≤ WithZero.exp m} (fun _ => (1 : ℂ)) x

def Va (m : ℤ) : ℝ := (selfDualHaarAt ℚ p).real {x : F | Valued.v x ≤ WithZero.exp m}

def boxSet (L Mb Mc Md : ℤ) : Set M2 :=
  {X : M2 | Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
      Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)}

def Φb (L Mb Mc Md : ℤ) : M2 → ℂ := fun X => Set.indicator (boxSet p L Mb Mc Md) (fun _ => (1 : ℂ)) X

theorem Φb_eq_prod (L Mb Mc Md : ℤ) :
    Φb p L Mb Mc Md = fun X : M2 => indBall p L (X 0 0) * indBall p (-Mb) (X 0 1) * indBall p (-Mc) (X 1 0) * indBall1 p (-Md) (X 1 1) := by
  funext X
  simp only [Φb, boxSet, indBall, indBall1, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases h1 : Valued.v (X 0 0) ≤ WithZero.exp L <;> by_cases h2 : Valued.v (X 0 1) ≤ WithZero.exp (-Mb) <;>
    by_cases h3 : Valued.v (X 1 0) ≤ WithZero.exp (-Mc) <;> by_cases h4 : Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md) <;>
    simp only [h1, h2, h3, h4, ite_true, ite_false, and_true, and_self, true_and, and_false, false_and,
      mul_one, mul_zero, one_mul, zero_mul, not_true, not_false_eq_true, if_true, if_false]

def Φhat (L Mb Mc Md : ℤ) (X : M2) : ℂ :=
  ((Va p L * Va p (-Mb) * Va p (-Mc) * Va p (-Md) : ℝ) : ℂ) *
    (indBall p (-L) (X 0 0) * indBall p Mb (X 0 1) * indBall p Mc (X 1 0) * (ψp (X 1 1) * indBall p Md (X 1 1)))

theorem c4a_isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem psi_level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψp x = 1) ∧ (∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψp x ≠ 1) := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → ψp x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← WithZero.exp_zero]; exact hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψp hk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h
  exact h

theorem psi_eq_one_of_v_le_one {x : F} (hx : Valued.v x ≤ 1) : ψp x = 1 :=
  LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx)

theorem tateFourier_indBall (m : ℤ) (y : F) :
    tateFourier ψp νa (indBall p m) y = ((Va p m : ℝ) : ℂ) * indBall p (-m) y := by
  haveI := c4a_isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h1, h2⟩ := psi_level_zero p
  have h := LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le ℚ p νa ψp 0 h1 h2 0 (-m) y
  simp only [sub_zero, neg_neg, zero_mul, AddChar.map_zero_eq_one, one_mul, zero_add] at h
  unfold indBall Va
  exact h

theorem tateFourier_indBall1 (M : ℤ) (y : F) :
    tateFourier ψp νa (indBall1 p (-M)) y = ψp y * ((Va p (-M) : ℝ) : ℂ) * indBall p M y := by
  haveI := c4a_isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h1, h2⟩ := psi_level_zero p
  have h := LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le ℚ p νa ψp 0 h1 h2 1 M y
  simp only [one_mul, zero_add] at h
  unfold indBall indBall1 Va
  exact h

theorem matFourier22_Φb (L Mb Mc Md : ℤ) : matFourier22 p ψp (Φb p L Mb Mc Md) = Φhat p L Mb Mc Md := by
  have hφ : Φb p L Mb Mc Md = fun X : M2 => ∏ i : Fin 2, ∏ j : Fin 2,
      (![![indBall p L, indBall p (-Mb)], ![indBall p (-Mc), indBall1 p (-Md)]] : Fin 2 → Fin 2 → (F → ℂ)) i j (X i j) := by
    rw [Φb_eq_prod]
    funext X
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  funext Y
  rw [hφ, matFourier22_prod_eq_prod_tateFourier]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    tateFourier_indBall, tateFourier_indBall1, neg_neg]
  unfold Φhat
  push_cast
  ring

theorem c4a_Va_zero : Va p 0 = 1 := by
  have h := LanglandsTunnell.TateLocal.selfDualHaarAt_real_integers_mul_real_setOf_valued_le_exp_addCharLevel ℚ p
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h
  have hO : ((HeightOneSpectrum.adicCompletionIntegers ℚ p : Set F)) = {x : F | Valued.v x ≤ WithZero.exp (0 : ℤ)} := by
    ext x; rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Set.mem_setOf_eq, WithZero.exp_zero]
  rw [hO] at h

  have hV : 0 ≤ Va p 0 := by unfold Va; exact MeasureTheory.measureReal_nonneg
  unfold Va at hV ⊢
  nlinarith [h, hV]

theorem Va_eq (m : ℤ) : Va p m = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  haveI := c4a_isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨h1, -⟩ := LanglandsTunnell.TateLocal.addHaar_ball_eq_and_setIntegral_psiLocal_inv_mul_rat p νa
  obtain ⟨-, -, h⟩ := h1 m
  have h0 := c4a_Va_zero p
  unfold Va at h0 ⊢
  rw [Measure.real, h]
  have : {y : F | Valued.v y ≤ 1} = {x : F | Valued.v x ≤ WithZero.exp (0 : ℤ)} := by rw [WithZero.exp_zero]
  rw [this, ← Measure.real, h0, mul_one]

theorem Va_pos (m : ℤ) : 0 < Va p m := by
  rw [Va_eq]
  exact zpow_pos (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)) m

theorem Va_mul_Va_neg (m : ℤ) : Va p m * Va p (-m) = 1 := by
  rw [Va_eq, Va_eq, zpow_neg]
  exact mul_inv_cancel₀ (zpow_ne_zero m (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot)))

end Box

section BlockX

theorem bx_level_zero :
    (∀ x : F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψp x = 1) ∧
      ∃ x : F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψp x ≠ 1 := by
  have hk : ∃ k : ℤ, ∀ x : F, Valued.v x ≤ WithZero.exp k → ψp x = 1 := by
    refine ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa using hx
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ p ψp hk
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p)
  rwa [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p] at h

theorem bx_isAddHaarMeasure : (νa).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem bx_ball_add_iff (z x₀ : F) (r : WithZero (Multiplicative ℤ)) (h₀ : Valued.v x₀ ≤ r) :
    Valued.v (z + x₀) ≤ r ↔ Valued.v z ≤ r := by
  constructor
  · intro h
    have : z = (z + x₀) + (-x₀) := by ring
    rw [this]
    exact le_trans (Valuation.map_add _ _ _) (max_le h (by rwa [Valuation.map_neg]))
  · intro h
    exact le_trans (Valuation.map_add _ _ _) (max_le h h₀)

theorem bx_exp_succ_le_of_lt {y : F} {k : ℤ} (h : WithZero.exp k < Valued.v y) :
    WithZero.exp (k + 1) ≤ Valued.v y := by
  have hy : Valued.v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨WithZero.log (Valued.v y), (WithZero.exp_log hy).symm⟩
  rw [hm] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem x_integral {L Mc Md : ℤ} (hL : Md ≤ L) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (a e : HeightOneSpectrum.adicCompletion ℚ p)
    (he : Valued.v e ≤ WithZero.exp (-L)) :
    ∫ x : HeightOneSpectrum.adicCompletion ℚ p, NumberField.StandardAddChar.psiLocal ℚ p x *
        NumberField.StandardAddChar.psiLocal ℚ p (-(x * (b : HeightOneSpectrum.adicCompletion ℚ p))) *
        Set.indicator {x : HeightOneSpectrum.adicCompletion ℚ p |
            Valued.v (x * (b : HeightOneSpectrum.adicCompletion ℚ p)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x *
        Set.indicator {x : HeightOneSpectrum.adicCompletion ℚ p | Valued.v (a + x * e) ≤ WithZero.exp Mc}
          (fun _ => (1 : ℂ)) x ∂(selfDualHaarAt ℚ p) =
      if Valued.v ((b : HeightOneSpectrum.adicCompletion ℚ p) - 1) ≤ WithZero.exp (-Md) ∧ Valued.v a ≤ WithZero.exp Mc
        then (((selfDualHaarAt ℚ p).real {x : HeightOneSpectrum.adicCompletion ℚ p | Valued.v x ≤ WithZero.exp Md} : ℝ) : ℂ)
        else 0 := by
  obtain ⟨h0, t₀, ht₀v, ht₀⟩ := bx_level_zero p
  haveI := bx_isAddHaarMeasure p
  have hb0 : (b : F) ≠ 0 := b.ne_zero

  have hphase : ∀ x : F, ψp x * ψp (-(x * (b : F))) = ψp (x * (1 - (b : F))) := by
    intro x; rw [← AddChar.map_add_eq_mul]; congr 1; ring

  have hball_meas : MeasurableSet {x : F | Valued.v x ≤ WithZero.exp Md} := by
    have hcl : IsClosed {x : F | Valued.v x ≤ WithZero.exp Md} := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
      filter_upwards [Valued.locally_const hx0] with y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]; exact hx
    exact hcl.measurableSet
  by_cases hb : Valued.v ((b : F) - 1) ≤ WithZero.exp (-Md)
  ·
    have hb1 : Valued.v (b : F) = 1 := by
      have hlt : Valued.v ((b : F) - 1) < Valued.v (1 : F) := by
        rw [Valuation.map_one]
        refine lt_of_le_of_lt hb ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
      have : (b : F) = 1 + ((b : F) - 1) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ hlt, Valuation.map_one]
    have hset : {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} = {x : F | Valued.v x ≤ WithZero.exp Md} := by
      ext x; simp [Valuation.map_mul, hb1]

    have hpt : ∀ x : F,
        ψp x * ψp (-(x * (b : F))) *
            Set.indicator {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x *
            Set.indicator {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) x =
          Set.indicator {x : F | Valued.v x ≤ WithZero.exp Md}
            (fun _ => if Valued.v a ≤ WithZero.exp Mc then (1 : ℂ) else 0) x := by
      intro x
      rw [hset]
      by_cases hx : Valued.v x ≤ WithZero.exp Md
      · have hxmem : x ∈ {x : F | Valued.v x ≤ WithZero.exp Md} := hx
        rw [Set.indicator_of_mem hxmem, Set.indicator_of_mem hxmem, hphase]

        have hph : ψp (x * (1 - (b : F))) = 1 := by
          apply h0
          rw [Valuation.map_mul, show (1 - (b : F)) = -((b : F) - 1) by ring, Valuation.map_neg]
          calc Valued.v x * Valued.v ((b : F) - 1) ≤ WithZero.exp Md * WithZero.exp (-Md) :=
                mul_le_mul' hx hb
            _ = WithZero.exp 0 := by rw [← WithZero.exp_add]; simp
        rw [hph]
        simp only [one_mul, mul_one]

        have hxe : Valued.v (x * e) ≤ WithZero.exp 0 := by
          rw [Valuation.map_mul]
          calc Valued.v x * Valued.v e ≤ WithZero.exp Md * WithZero.exp (-L) := mul_le_mul' hx he
            _ = WithZero.exp (Md - L) := by rw [← WithZero.exp_add]; ring_nf
            _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
        have hxe' : Valued.v (x * e) ≤ WithZero.exp Mc :=
          le_trans hxe (by rw [WithZero.exp_le_exp]; exact hMc)
        by_cases ha : Valued.v a ≤ WithZero.exp Mc
        · rw [if_pos ha, Set.indicator_of_mem]
          show Valued.v (a + x * e) ≤ WithZero.exp Mc
          exact le_trans (Valuation.map_add _ _ _) (max_le ha hxe')
        · rw [if_neg ha, Set.indicator_of_notMem]
          show ¬ Valued.v (a + x * e) ≤ WithZero.exp Mc
          have hlt : Valued.v (x * e) < Valued.v a := lt_of_le_of_lt hxe' (lt_of_not_ge ha)
          rw [Valuation.map_add_eq_of_lt_left _ hlt]
          exact ha
      · have hxnot : x ∉ {x : F | Valued.v x ≤ WithZero.exp Md} := hx
        rw [Set.indicator_of_notMem hxnot, Set.indicator_of_notMem hxnot, mul_zero, zero_mul]
    simp_rw [hpt]
    rw [integral_indicator_const _ hball_meas]
    by_cases ha : Valued.v a ≤ WithZero.exp Mc
    · rw [if_pos ha, if_pos ⟨hb, ha⟩, Complex.real_smul, mul_one]
    · rw [if_neg ha, if_neg (fun h => ha h.2), smul_zero]
  ·
    rw [if_neg (fun h => hb h.1)]
    have hξ : (1 - (b : F)) ≠ 0 := by
      intro h0'
      have : (b : F) - 1 = 0 := by linear_combination -h0'
      rw [this, Valuation.map_zero] at hb
      exact hb zero_le'
    have hvξ : Valued.v ((b : F) - 1) = Valued.v (1 - (b : F)) := by
      rw [show (1 - (b : F)) = -((b : F) - 1) by ring, Valuation.map_neg]

    have hgt : WithZero.exp (-Md) < Valued.v (1 - (b : F)) := by rw [← hvξ]; exact lt_of_not_ge hb
    have hK2 : WithZero.exp (1 - Md) ≤ Valued.v (1 - (b : F)) := by
      rcases lt_trichotomy (Valued.v (b : F)) 1 with hlt | heq | hgt'
      ·
        have : Valued.v (1 - (b : F)) = 1 := by
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, Valuation.map_one]; exact hlt),
            Valuation.map_one]
        rw [this, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
      ·
        have := bx_exp_succ_le_of_lt p hgt
        rwa [show (-Md + 1 : ℤ) = 1 - Md by ring] at this
      ·
        have : Valued.v (1 - (b : F)) = Valued.v (b : F) := by
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg, Valuation.map_one]; exact hgt'),
            Valuation.map_neg]
        rw [this]
        refine le_trans ?_ hgt'.le
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hK1 : Valued.v (b : F) ≤ Valued.v (1 - (b : F)) * WithZero.exp (Md - 1) := by
      rcases lt_trichotomy (Valued.v (b : F)) 1 with hlt | heq | hgt'
      · have : Valued.v (1 - (b : F)) = 1 := by
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, Valuation.map_one]; exact hlt),
            Valuation.map_one]
        rw [this, one_mul]
        refine le_trans hlt.le ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
      · rw [heq]
        calc (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (1 - Md) * WithZero.exp (Md - 1) := by
              rw [← WithZero.exp_add]; ring_nf; exact WithZero.exp_zero.symm
          _ ≤ Valued.v (1 - (b : F)) * WithZero.exp (Md - 1) := mul_le_mul_left hK2 _
      · have : Valued.v (1 - (b : F)) = Valued.v (b : F) := by
          rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg, Valuation.map_one]; exact hgt'),
            Valuation.map_neg]
        rw [this]
        calc Valued.v (b : F) = Valued.v (b : F) * WithZero.exp 0 := by rw [WithZero.exp_zero, mul_one]
          _ ≤ Valued.v (b : F) * WithZero.exp (Md - 1) :=
              mul_le_mul_right (by rw [WithZero.exp_le_exp]; omega) _

    set x₀ : F := t₀ * (1 - (b : F))⁻¹ with hx₀
    have hvξ0 : Valued.v (1 - (b : F)) ≠ 0 := (Valuation.ne_zero_iff _).2 hξ
    have hx₀b : Valued.v (x₀ * (b : F)) ≤ WithZero.exp Md := by
      rw [hx₀, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv]
      calc Valued.v t₀ * (Valued.v (1 - (b : F)))⁻¹ * Valued.v (b : F)
            ≤ WithZero.exp (0 + 1) * ((Valued.v (1 - (b : F)))⁻¹ * (Valued.v (1 - (b : F)) * WithZero.exp (Md - 1))) := by
              rw [mul_assoc]; exact mul_le_mul' ht₀v (mul_le_mul_right hK1 _)
        _ = WithZero.exp Md := by
              rw [← mul_assoc ((Valued.v (1 - (b : F)))⁻¹), inv_mul_cancel₀ hvξ0, one_mul, ← WithZero.exp_add]; ring_nf
    have hx₀e : Valued.v (x₀ * e) ≤ WithZero.exp Mc := by
      rw [hx₀, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv]
      have hinv : (Valued.v (1 - (b : F)))⁻¹ ≤ WithZero.exp (Md - 1) := by
        have := WithZero.exp_neg (1 - Md)
        rw [show (-(1 - Md) : ℤ) = Md - 1 by ring] at this
        rw [this]
        exact inv_anti₀ (lt_of_le_of_ne zero_le' (WithZero.exp_ne_zero).symm) hK2
      calc Valued.v t₀ * (Valued.v (1 - (b : F)))⁻¹ * Valued.v e
            ≤ WithZero.exp (0 + 1) * WithZero.exp (Md - 1) * WithZero.exp (-L) :=
              mul_le_mul' (mul_le_mul' ht₀v hinv) he
        _ = WithZero.exp (Md - L) := by rw [← WithZero.exp_add, ← WithZero.exp_add]; ring_nf
        _ ≤ WithZero.exp Mc := by rw [WithZero.exp_le_exp]; omega
    have hx₀ξ : x₀ * (1 - (b : F)) = t₀ := by rw [hx₀, mul_assoc, inv_mul_cancel₀ hξ, mul_one]

    set f : F → ℂ := fun x => ψp x * ψp (-(x * (b : F))) *
        Set.indicator {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x *
        Set.indicator {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) x with hf
    have hshift : ∀ x : F, f (x + x₀) = ψp t₀ * f x := by
      intro x
      have hind1 : Set.indicator {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) (x + x₀) =
          Set.indicator {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x := by
        have hiff : (x + x₀) ∈ {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} ↔
            x ∈ {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md} := by
          simp only [Set.mem_setOf_eq, add_mul]
          exact bx_ball_add_iff p _ _ _ hx₀b
        by_cases hx : x ∈ {x : F | Valued.v (x * (b : F)) ≤ WithZero.exp Md}
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.1 h))]
      have hind2 : Set.indicator {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) (x + x₀) =
          Set.indicator {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) x := by
        have hiff : (x + x₀) ∈ {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} ↔
            x ∈ {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc} := by
          simp only [Set.mem_setOf_eq, add_mul, ← add_assoc]
          exact bx_ball_add_iff p _ _ _ hx₀e
        by_cases hx : x ∈ {x : F | Valued.v (a + x * e) ≤ WithZero.exp Mc}
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.2 hx)]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.1 h))]
      simp only [hf, hind1, hind2]
      rw [hphase, hphase, add_mul, AddChar.map_add_eq_mul, hx₀ξ]
      ring
    have hI : (∫ x, f x ∂νa) = ψp t₀ * ∫ x, f x ∂νa := by
      conv_lhs => rw [← integral_add_right_eq_self f x₀]
      simp_rw [hshift]
      exact integral_const_mul _ _
    have hone : (1 - ψp t₀) * ∫ x, f x ∂νa = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
    have := (mul_eq_zero.1 hone).resolve_left (sub_ne_zero.2 (Ne.symm ht₀))
    simpa only [hf] using this

end BlockX

section Whittaker

theorem w_transposeInvN_wJ_chart (w : G → ℂ) (θ₀ : Fˣ →* ℂˣ) (wJ : G)
    (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = ψp x * w g)
    (hcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (x : F) (β α : Fˣ) (y : F) :
    w (transposeInvN (Fin 2) (wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G)) =
      ψp x * (((θ₀ α : ℂˣ) : ℂ))⁻¹ * w (diagOne (α * β⁻¹) * (wJ * unipotent (-y))) := by

  rw [transposeInvN_wJ_chart p wJ hwJ x β α y, hwlaw, hcentral, map_inv, Units.val_inv_eq_inv_val, mul_assoc]

theorem w_reduce (w : G → ℂ) (θ₀ : Fˣ →* ℂˣ) (U : Subgroup G) (wJ : G) {L Md : ℤ}
    (hcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (hwJ : (wJ : M2) = !![0, 1; -1, 0])
    (hstabN : ∀ x : F, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U)
    (hstabD : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U)
    (hθ₀ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (β α : Fˣ) (y : F) (hβ : Valued.v ((β : F) - 1) ≤ WithZero.exp (-Md)) (hy : Valued.v y ≤ WithZero.exp (-L)) :
    w (diagOne (α * β⁻¹) * (wJ * unipotent (-y))) = w (diagOne α * wJ) := by

  have hny : unipotent (-y) ∈ U := hstabN (-y) (by rwa [Valuation.map_neg])
  rw [← mul_assoc, hU _ hny, diagOne_mul_wJ_eq p wJ hwJ α β, hcentral, hU _ (hstabD β hβ), map_inv, hθ₀ β hβ,
    inv_one, Units.val_one, one_mul]

end Whittaker

section Chart2

def FG (w : G → ℂ) (χ : Fˣ →* ℂˣ) (L Mb Mc Md : ℤ) (s : ℂ) (g : G) : ℂ :=
  w (transposeInvN (Fin 2) g) * matFourier22 p ψp (Φb p L Mb Mc Md) ((g : G) : M2) *
    ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + 3 / 2)

def Ch (q : F × Fˣ × Fˣ × F) : G := unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2

def dens (q : F × Fˣ × Fˣ × F) : NNReal := modulus (((q.2.1 * (q.2.2.1)⁻¹ : Fˣ)) : F)

def J (w : G → ℂ) (χ : Fˣ →* ℂˣ) (wJ : G) (L Mb Mc Md : ℤ) (s : ℂ) (q : F × Fˣ × Fˣ × F) : ℂ :=
  (dens p q) • FG p w χ L Mb Mc Md s (wJ * Ch p q)

def Tor (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (wJ : G) (s : ℂ) (a : Fˣ) : ℂ :=
  w (diagOne a * wJ) * (((χ a : ℂˣ) : ℂ))⁻¹ * (((θ₀ a : ℂˣ) : ℂ))⁻¹ * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 + s)

def f2 (Md : ℤ) (a : Fˣ) : ℂ := Set.indicator {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) a

def R (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (wJ : G) (L Mb : ℤ) (s : ℂ) (β α : Fˣ) (y : F) : ℂ :=
  ((modulus (((β * α⁻¹ : Fˣ)) : F) : ℝ) : ℂ) * (((θ₀ α : ℂˣ) : ℂ))⁻¹ * w (diagOne (α * β⁻¹) * (wJ * unipotent (-y))) *
    indBall p (-L) ((β : F) * y) * indBall p Mb (β : F) * (((χ (α * β) : ℂˣ) : ℂ))⁻¹ *
    ((modulus (((α * β : Fˣ)) : F) : ℝ) : ℂ) ^ (s + 3 / 2)

def P (Mc Md : ℤ) (β : Fˣ) (α : Fˣ) (y : F) (x : F) : ℂ :=
  ψp x * ψp (-(x * (β : F))) *
    Set.indicator {x : F | Valued.v (x * (β : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x *
    Set.indicator {x : F | Valued.v ((α : F) + x * ((β : F) * y)) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) x

theorem J_eq (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (wJ : G) {L Mb Mc Md : ℤ} (s : ℂ)
    (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = ψp x * w g)
    (hcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (hwJ : (wJ : M2) = !![0, 1; -1, 0]) (x : F) (β α : Fˣ) (y : F) :
    J p w χ wJ L Mb Mc Md s (x, β, α, y) =
      ((Va p L * Va p (-Mb) * Va p (-Mc) * Va p (-Md) : ℝ) : ℂ) * (R p w θ₀ χ wJ L Mb s β α y * P p Mc Md β α y x) := by

  have h00 : ((wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) : M2) 0 0 = (β : F) * y := by
    rw [coe_wJ_chart p wJ hwJ]; simp
  have h01 : ((wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) : M2) 0 1 = (β : F) := by
    rw [coe_wJ_chart p wJ hwJ]; simp
  have h10 : ((wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) : M2) 1 0 = -((α : F) + x * (β : F) * y) := by
    rw [coe_wJ_chart p wJ hwJ]; simp
  have h11 : ((wJ * (unipotentGL2 x * diagUnits2 α β * lowerUnipotentGL2 y) : G) : M2) 1 1 = -(x * (β : F)) := by
    rw [coe_wJ_chart p wJ hwJ]; simp
  have hi1 : indBall p Md (-(x * (β : F))) =
      Set.indicator {x : F | Valued.v (x * (β : F)) ≤ WithZero.exp Md} (fun _ => (1 : ℂ)) x := by
    simp only [indBall, Set.indicator_apply, Set.mem_setOf_eq, Valuation.map_neg]
  have hi2 : indBall p Mc (-((α : F) + x * (β : F) * y)) =
      Set.indicator {x : F | Valued.v ((α : F) + x * ((β : F) * y)) ≤ WithZero.exp Mc} (fun _ => (1 : ℂ)) x := by
    simp only [indBall, Set.indicator_apply, Set.mem_setOf_eq, Valuation.map_neg, mul_assoc]
  simp only [J, dens, FG, Ch]
  rw [w_transposeInvN_wJ_chart p w θ₀ wJ hwlaw hcentral hwJ x β α y, matFourier22_Φb, det_wJ_chart p wJ hwJ,
    NNReal.smul_def, Complex.real_smul]
  simp only [Φhat, h00, h01, h10, h11, hi1, hi2, R, P, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  push_cast
  ring

theorem integral_x_J (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (U : Subgroup G) (wJ : G) {L Mb Mc Md : ℤ} (s : ℂ)
    (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = ψp x * w g)
    (hcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (hwJ : (wJ : M2) = !![0, 1; -1, 0])
    (hL : Md ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsuppJ : ∀ y : Fˣ, WithZero.exp Mc < Valued.v (y : F) → w (diagOne y * wJ) = 0)
    (hstabN : ∀ x : F, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U)
    (hstabD : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U)
    (hθ₀ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (hχ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (β α : Fˣ) (y : F) :
    ∫ x, J p w χ wJ L Mb Mc Md s (x, β, α, y) ∂νa =
      ((Va p L * Va p (-Mb) * Va p (-Mc) * Va p (-Md) * Va p Md : ℝ) : ℂ) *
        (f2 p Md β * (Tor p w θ₀ χ wJ s α * indBall p (-L) y)) := by
  have hJx : ∀ x : F, J p w χ wJ L Mb Mc Md s (x, β, α, y) =
      ((Va p L * Va p (-Mb) * Va p (-Mc) * Va p (-Md) : ℝ) : ℂ) * (R p w θ₀ χ wJ L Mb s β α y * P p Mc Md β α y x) :=
    fun x => J_eq p w θ₀ χ wJ s hwlaw hcentral hwJ x β α y
  simp_rw [hJx]
  rw [integral_const_mul, integral_const_mul]

  have hRzero : ¬ Valued.v ((β : F) * y) ≤ WithZero.exp (-L) → R p w θ₀ χ wJ L Mb s β α y = 0 := by
    intro hLy
    have h0 : indBall p (-L) ((β : F) * y) = 0 := by
      have h' : (β : F) * y ∉ {x : F | Valued.v x ≤ WithZero.exp (-L)} := hLy
      simp only [indBall]; exact Set.indicator_of_notMem h' _
    simp only [R, h0, mul_zero, zero_mul]
  have hPint : Valued.v ((β : F) * y) ≤ WithZero.exp (-L) → ∫ x, P p Mc Md β α y x ∂νa =
      if Valued.v ((β : F) - 1) ≤ WithZero.exp (-Md) ∧ Valued.v (α : F) ≤ WithZero.exp Mc then ((Va p Md : ℝ) : ℂ) else 0 := by
    intro hLy
    have hX := x_integral p hL hMc hMd β (α : F) ((β : F) * y) hLy
    simpa only [P, Va] using hX
  by_cases hβ : Valued.v ((β : F) - 1) ≤ WithZero.exp (-Md)
  · have hvβ : Valued.v (β : F) = 1 := v_eq_one_of_v_sub_one_le p hMd hβ
    have hf2 : f2 p Md β = 1 := by
      have h' : β ∈ {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} := hβ
      simp only [f2]; exact Set.indicator_of_mem h' _
    by_cases hy : Valued.v y ≤ WithZero.exp (-L)
    · have hLy : Valued.v ((β : F) * y) ≤ WithZero.exp (-L) := by rw [map_mul, hvβ, one_mul]; exact hy
      rw [hPint hLy]
      have hind : indBall p (-L) y = 1 := by
        have h' : y ∈ {x : F | Valued.v x ≤ WithZero.exp (-L)} := hy
        simp only [indBall]; exact Set.indicator_of_mem h' _
      by_cases hα : Valued.v (α : F) ≤ WithZero.exp Mc
      · rw [if_pos ⟨hβ, hα⟩, hf2, hind, one_mul, mul_one]

        have hmβ : modulus ((β : F)) = 1 := by
          apply NNReal.coe_injective
          rw [coe_modulus_eq_norm, NNReal.coe_one]; exact norm_eq_one_of_v_eq_one p hvβ
        have hmαinv : modulus (((α⁻¹ : Fˣ)) : F) = (modulus (α : F))⁻¹ := by
          rw [modulus_coe_units, modulus_coe_units, map_inv]
        have hm1 : modulus ((((β * α⁻¹ : Fˣ)) : F)) = (modulus (α : F))⁻¹ := by
          rw [Units.val_mul, modulus_mul, hmβ, one_mul, hmαinv]
        have hm2 : modulus ((((α * β : Fˣ)) : F)) = modulus (α : F) := by
          rw [Units.val_mul, modulus_mul, hmβ, mul_one]
        have hw : w (diagOne (α * β⁻¹) * (wJ * unipotent (-y))) = w (diagOne α * wJ) :=
          w_reduce p w θ₀ U wJ hcentral hU hwJ hstabN hstabD hθ₀ β α y hβ hy
        have hiL : indBall p (-L) ((β : F) * y) = 1 := by
          have h' : (β : F) * y ∈ {x : F | Valued.v x ≤ WithZero.exp (-L)} := hLy
          simp only [indBall]; exact Set.indicator_of_mem h' _
        have hiMb : indBall p Mb (β : F) = 1 := by
          simp only [indBall]
          refine Set.indicator_of_mem (show (β : F) ∈ {x : F | Valued.v x ≤ WithZero.exp Mb} from ?_) _
          show Valued.v (β : F) ≤ WithZero.exp Mb
          rw [hvβ, ← WithZero.exp_zero, WithZero.exp_le_exp]; exact hMb
        have hχ' : (((χ (α * β) : ℂˣ) : ℂ)) = ((χ α : ℂˣ) : ℂ) := by rw [map_mul, hχ β hβ, mul_one]
        have hmα0 : ((modulus (α : F) : ℝ) : ℂ) ≠ 0 := by
          have : (0 : ℝ) < (modulus (α : F) : ℝ) := by rw [coe_modulus_eq_norm]; exact norm_pos_iff.2 α.ne_zero
          exact_mod_cast this.ne'
        simp only [R, Tor, hm1, hm2, hw, hiL, hiMb, hχ', NNReal.coe_inv, Complex.ofReal_inv, mul_one]
        rw [show s + 3 / 2 = (1 / 2 + s) + 1 by ring, Complex.cpow_add _ _ hmα0, Complex.cpow_one]
        push_cast
        field_simp
      · rw [if_neg (fun h => hα h.2)]
        have hw0 : w (diagOne α * wJ) = 0 := hsuppJ α (lt_of_not_ge hα)
        simp only [Tor, hw0, zero_mul, mul_zero]
    · have hLy : ¬ Valued.v ((β : F) * y) ≤ WithZero.exp (-L) := by rwa [map_mul, hvβ, one_mul]
      have hind : indBall p (-L) y = 0 := by
        have h' : y ∉ {x : F | Valued.v x ≤ WithZero.exp (-L)} := hy
        simp only [indBall]; exact Set.indicator_of_notMem h' _
      rw [hRzero hLy, hind, zero_mul, mul_zero, mul_zero, mul_zero, mul_zero]
  · have hf2 : f2 p Md β = 0 := by
      have h' : β ∉ {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} := hβ
      simp only [f2]; exact Set.indicator_of_notMem h' _
    rw [hf2, zero_mul, mul_zero]
    by_cases hLy : Valued.v ((β : F) * y) ≤ WithZero.exp (-L)
    · rw [hPint hLy, if_neg (fun h => hβ h.1), mul_zero, mul_zero]
    · rw [hRzero hLy, zero_mul, mul_zero]

end Chart2

section Transport

local instance l2_secondCountableGL : SecondCountableTopology (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  (AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p).1

theorem transport (w : G → ℂ) (χ : Fˣ →* ℂˣ) (wJ : G) (L Mb Mc Md : ℤ) (s : ℂ) (μ₂ : Measure G) [μ₂.IsHaarMeasure] (c : ENNReal) (hc0 : c ≠ 0) (hcT : c ≠ ⊤)
    (hchart : μ₂ = c • Measure.map (Ch p) (((νa).prod ((νx).prod ((νx).prod (νa)))).withDensity fun q => (dens p q : ENNReal)))
    (hint : Integrable (FG p w χ L Mb Mc Md s) μ₂) :
    Integrable (J p w χ wJ L Mb Mc Md s) ((νa).prod ((νx).prod ((νx).prod (νa)))) ∧
      ∫ g, FG p w χ L Mb Mc Md s g ∂μ₂ = ((c.toReal : ℝ) : ℂ) * ∫ q, J p w χ wJ L Mb Mc Md s q ∂((νa).prod ((νx).prod ((νx).prod (νa)))) := by

  have hCh : Measurable (Ch p) := (continuous_chart p).measurable
  have hdens : Measurable (dens p) := measurable_dens p

  have hintw : Integrable (fun g : G => FG p w χ L Mb Mc Md s (wJ * g)) μ₂ := hint.comp_mul_left wJ
  have hintegral : ∫ g, FG p w χ L Mb Mc Md s g ∂μ₂ = ∫ g, FG p w χ L Mb Mc Md s (wJ * g) ∂μ₂ :=
    (integral_mul_left_eq_self (FG p w χ L Mb Mc Md s) wJ).symm

  have h1 : Integrable (fun g : G => FG p w χ L Mb Mc Md s (wJ * g))
      (c • Measure.map (Ch p) (((νa).prod ((νx).prod ((νx).prod (νa)))).withDensity fun q => (dens p q : ENNReal))) := by
    rw [← hchart]; exact hintw
  have h2 := (integrable_smul_measure hc0 hcT).1 h1
  have hsm : AEStronglyMeasurable (fun g : G => FG p w χ L Mb Mc Md s (wJ * g))
      (Measure.map (Ch p) (((νa).prod ((νx).prod ((νx).prod (νa)))).withDensity fun q => (dens p q : ENNReal))) :=
    h2.aestronglyMeasurable
  have h3 := (integrable_map_measure hsm hCh.aemeasurable).1 h2
  have h4 := (integrable_withDensity_iff_integrable_smul hdens).1 h3
  have hJeq : (fun q : F × Fˣ × Fˣ × F => dens p q • ((fun g : G => FG p w χ L Mb Mc Md s (wJ * g)) ∘ Ch p) q) =
      J p w χ wJ L Mb Mc Md s := by
    funext q; rfl
  refine ⟨?_, ?_⟩
  · rw [← hJeq]; exact h4
  · rw [hintegral]
    conv_lhs => rw [hchart]
    rw [integral_smul_measure, integral_map hCh.aemeasurable hsm, integral_withDensity_eq_integral_smul hdens,
      Complex.real_smul]
    rfl

end Transport

section Iterate

theorem continuous_Tor (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (U : Subgroup G) (wJ : G) {Md : ℤ} (s : ℂ)
    (hUo : IsOpen (U : Set G)) (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g) (hχc : IsLocallyConstant χ)
    (hθ₀ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1) :
    Continuous (Tor p w θ₀ χ wJ s) := by

  have hw : Continuous w := continuous_of_open_stabilizer p w U hUo hU
  have h1 : Continuous fun a : Fˣ => w (diagOne a * wJ) :=
    hw.comp ((continuous_diagOne p).mul continuous_const)
  have h2 : Continuous fun a : Fˣ => (((χ a : ℂˣ) : ℂ))⁻¹ :=
    (Units.continuous_val.comp (hχc.continuous)).inv₀ fun a => Units.ne_zero _
  have h3 : Continuous fun a : Fˣ => (((θ₀ a : ℂˣ) : ℂ))⁻¹ :=
    (continuous_coe_char_of_trivial p θ₀ Md hθ₀).inv₀ fun a => Units.ne_zero _
  have h4 : Continuous fun a : Fˣ => ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 + s) := by
    have hm : Continuous fun a : Fˣ => ((modulus (a : F) : ℝ) : ℂ) := by
      have : (fun a : Fˣ => ((modulus (a : F) : ℝ) : ℂ)) = fun a : Fˣ => ((‖(a : F)‖ : ℝ) : ℂ) :=
        funext fun a => by rw [coe_modulus_eq_norm]
      rw [this]
      exact Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)
    refine continuous_iff_continuousAt.2 fun a => ?_
    exact ContinuousAt.cpow hm.continuousAt continuousAt_const
      (Or.inl (by
        show 0 < (((modulus (a : F) : ℝ) : ℂ)).re
        rw [Complex.ofReal_re]; exact_mod_cast modulus_pos (Units.ne_zero a)))
  unfold Tor
  exact ((h1.mul h2).mul h3).mul h4

theorem integrable_Tor_of_integrable_triple (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (U : Subgroup G) (wJ : G) {L Md : ℤ} (s : ℂ)
    (hUo : IsOpen (U : Set G)) (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g) (hχc : IsLocallyConstant χ)
    (hθ₀ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (hL : 0 ≤ L) (hMd : 1 ≤ Md)
    (hH : Integrable (fun r : Fˣ × Fˣ × F => f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2)) ((νx).prod ((νx).prod (νa)))) :
    Integrable (Tor p w θ₀ χ wJ s) νx := by

  haveI : SigmaCompactSpace (HeightOneSpectrum.adicCompletion ℚ p) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hTm : Measurable (Tor p w θ₀ χ wJ s) := (continuous_Tor p w θ₀ χ U wJ s hUo hU hχc hθ₀).measurable
  refine ⟨hTm.aestronglyMeasurable, ?_⟩
  have hf2m : Measurable (f2 p Md) := by
    unfold f2; exact measurable_const.indicator (measurableSet_prinUnits p Md)
  have hfLm : Measurable (indBall p (-L)) := by
    unfold indBall; exact measurable_const.indicator (measurableSet_vball p _)
  have hgm : Measurable (fun z : Fˣ × F => ‖Tor p w θ₀ χ wJ s z.1‖ₑ * ‖indBall p (-L) z.2‖ₑ) :=
    (hTm.comp measurable_fst).enorm.mul (hfLm.comp measurable_snd).enorm

  have hA : ∫⁻ a, ‖f2 p Md a‖ₑ ∂νx = (νx) {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} := by
    have : (fun a : Fˣ => ‖f2 p Md a‖ₑ) =
        Set.indicator {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ENNReal)) := by
      funext a; unfold f2; rw [enorm_indicator_eq_indicator_enorm]; simp only [enorm_one]
    rw [this, lintegral_indicator_const (measurableSet_prinUnits p Md), one_mul]
  have hB : ∫⁻ x, ‖indBall p (-L) x‖ₑ ∂νa = (νa) {x : F | Valued.v x ≤ WithZero.exp (-L)} := by
    have : (fun x : F => ‖indBall p (-L) x‖ₑ) =
        Set.indicator {x : F | Valued.v x ≤ WithZero.exp (-L)} (fun _ => (1 : ENNReal)) := by
      funext x; unfold indBall; rw [enorm_indicator_eq_indicator_enorm]; simp only [enorm_one]
    rw [this, lintegral_indicator_const (measurableSet_vball p _), one_mul]
  have hA0 : ∫⁻ a, ‖f2 p Md a‖ₑ ∂νx ≠ 0 := by rw [hA]; exact (prinUnits_pos p Md).ne'
  have hB0 : ∫⁻ x, ‖indBall p (-L) x‖ₑ ∂νa ≠ 0 := by rw [hB]; exact (vball_pos p L).ne'

  have hprod : ∫⁻ r, ‖f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2)‖ₑ ∂((νx).prod ((νx).prod (νa))) =
      (∫⁻ a, ‖f2 p Md a‖ₑ ∂νx) * ((∫⁻ a, ‖Tor p w θ₀ χ wJ s a‖ₑ ∂νx) * ∫⁻ x, ‖indBall p (-L) x‖ₑ ∂νa) := by
    have h1 : ∀ r : Fˣ × Fˣ × F, ‖f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2)‖ₑ =
        ‖f2 p Md r.1‖ₑ * (‖Tor p w θ₀ χ wJ s r.2.1‖ₑ * ‖indBall p (-L) r.2.2‖ₑ) := fun r => by rw [enorm_mul, enorm_mul]
    simp_rw [h1]
    rw [lintegral_prod_mul hf2m.enorm.aemeasurable hgm.aemeasurable, lintegral_prod_mul hTm.enorm.aemeasurable hfLm.enorm.aemeasurable]
  have hfin : ∫⁻ r, ‖f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2)‖ₑ ∂((νx).prod ((νx).prod (νa))) < ⊤ :=
    hH.hasFiniteIntegral
  rw [hprod] at hfin
  show ∫⁻ a, ‖Tor p w θ₀ χ wJ s a‖ₑ ∂νx < ⊤
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.top_mul hB0, ENNReal.mul_top hA0] at hfin
  exact lt_irrefl _ hfin

theorem integrable_Tor_and_integral_J (w : G → ℂ) (θ₀ χ : Fˣ →* ℂˣ) (U : Subgroup G) (wJ : G) {L Mb Mc Md : ℤ} (s : ℂ)
    (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = ψp x * w g)
    (hcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (hχc : IsLocallyConstant χ) (hUo : IsOpen (U : Set G)) (hU : ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (hwJ : (wJ : M2) = !![0, 1; -1, 0])
    (hL : Md ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsuppJ : ∀ y : Fˣ, WithZero.exp Mc < Valued.v (y : F) → w (diagOne y * wJ) = 0)
    (hstabN : ∀ x : F, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U)
    (hstabD : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U)
    (hθ₀ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (hχ : ∀ a : Fˣ, Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (hJ : Integrable (J p w χ wJ L Mb Mc Md s) ((νa).prod ((νx).prod ((νx).prod (νa))))) :
    Integrable (Tor p w θ₀ χ wJ s) νx ∧
      ∫ q, J p w χ wJ L Mb Mc Md s q ∂((νa).prod ((νx).prod ((νx).prod (νa)))) =
        ((Va p (-Mb) * (νx).real {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} * Va p (-Mc) : ℝ) : ℂ) *
          ∫ a, Tor p w θ₀ χ wJ s a ∂νx := by

  haveI : SFinite (selfDualHaarAt ℚ p) := by unfold selfDualHaarAt; infer_instance
  set K : ℂ := ((Va p L * Va p (-Mb) * Va p (-Mc) * Va p (-Md) * Va p Md : ℝ) : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]; exact_mod_cast (mul_pos (mul_pos (mul_pos (mul_pos (Va_pos p L) (Va_pos p (-Mb))) (Va_pos p (-Mc)))
      (Va_pos p (-Md))) (Va_pos p Md)).ne'

  have hx : ∀ r : Fˣ × Fˣ × F, ∫ x, J p w χ wJ L Mb Mc Md s (x, r) ∂νa =
      K * (f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2)) := by
    rintro ⟨β, α, y⟩
    exact integral_x_J p w θ₀ χ U wJ s hwlaw hcentral hU hwJ hL hMb hMc hMd hsuppJ hstabN hstabD hθ₀ hχ β α y

  have hG : Integrable (fun r : Fˣ × Fˣ × F => ∫ x, J p w χ wJ L Mb Mc Md s (x, r) ∂νa) ((νx).prod ((νx).prod (νa))) :=
    hJ.integral_prod_right
  have hswap : ∫ q, J p w χ wJ L Mb Mc Md s q ∂((νa).prod ((νx).prod ((νx).prod (νa)))) =
      ∫ r, ∫ x, J p w χ wJ L Mb Mc Md s (x, r) ∂νa ∂((νx).prod ((νx).prod (νa))) :=
    integral_prod_symm _ hJ
  simp_rw [hx] at hG hswap

  have hH : Integrable (fun r : Fˣ × Fˣ × F => f2 p Md r.1 * (Tor p w θ₀ χ wJ s r.2.1 * indBall p (-L) r.2.2))
      ((νx).prod ((νx).prod (νa))) := by
    have := hG.const_mul K⁻¹
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  have hTor : Integrable (Tor p w θ₀ χ wJ s) νx :=
    integrable_Tor_of_integrable_triple p w θ₀ χ U wJ s hUo hU hχc hθ₀ (by omega) hMd hH
  refine ⟨hTor, ?_⟩

  rw [hswap, integral_const_mul,
    integral_prod_mul (f2 p Md) (fun r : Fˣ × F => Tor p w θ₀ χ wJ s r.1 * indBall p (-L) r.2),
    integral_prod_mul (Tor p w θ₀ χ wJ s) (indBall p (-L))]
  have hf2 : ∫ a, f2 p Md a ∂νx = (((νx).real {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} : ℝ) : ℂ) := by
    unfold f2
    rw [integral_indicator_const _ (measurableSet_prinUnits p Md), Complex.real_smul, mul_one]
  have hball : ∫ y, indBall p (-L) y ∂νa = ((Va p (-L) : ℝ) : ℂ) := by
    unfold indBall Va
    rw [integral_indicator_const _ (measurableSet_vball p _), Complex.real_smul, mul_one]
  rw [hf2, hball, hK]
  have h1 : ((Va p L : ℝ) : ℂ) * ((Va p (-L) : ℝ) : ℂ) = 1 := by exact_mod_cast Va_mul_Va_neg p L
  have h2 : ((Va p Md : ℝ) : ℂ) * ((Va p (-Md) : ℝ) : ℂ) = 1 := by exact_mod_cast Va_mul_Va_neg p Md
  push_cast
  linear_combination (((Va p (-Mb) : ℝ) : ℂ) * ((Va p (-Mc) : ℝ) : ℂ) *
      (((νx).real {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} : ℝ) : ℂ) *
      (∫ a, Tor p w θ₀ χ wJ s a ∂νx) * ((Va p (-Md) : ℝ) : ℂ) * ((Va p Md : ℝ) : ℂ)) * h1 +
    (((Va p (-Mb) : ℝ) : ℂ) * ((Va p (-Mc) : ℝ) : ℂ) *
      (((νx).real {a : Fˣ | Valued.v ((a : F) - 1) ≤ WithZero.exp (-Md)} : ℝ) : ℂ) *
      (∫ a, Tor p w θ₀ χ wJ s a ∂νx)) * h2

end Iterate

end

end L2Box46
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart.L2Box46"

open L2Box46 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχc : IsLocallyConstant χ)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hUo : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])
    (L Mb Mc Md : ℤ) (hL : Md ≤ L) (hMb : 0 ≤ Mb) (hMc : 0 ≤ Mc) (hMd : 1 ≤ Md)
    (hsuppJ : ∀ y : (p.adicCompletion ℚ)ˣ, WithZero.exp Mc < Valued.v (y : p.adicCompletion ℚ) → w (diagOne y * wJ) = 0)
    (hstabN : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (-L) → unipotent x ∈ U)
    (hstabD : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → diagOne a ∈ U)
    (hθ₀ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → θ₀ a = 1)
    (hχ : ∀ a : (p.adicCompletion ℚ)ˣ, Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md) → χ a = 1)
    (Φ₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hΦ₀ : Φ₀ = fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) =>
        Set.indicator {X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) |
            Valued.v (X 0 0) ≤ WithZero.exp L ∧ Valued.v (X 0 1) ≤ WithZero.exp (-Mb) ∧
            Valued.v (X 1 0) ≤ WithZero.exp (-Mc) ∧ Valued.v (X 1 1 - 1) ≤ WithZero.exp (-Md)} (fun _ => (1 : ℂ)) X) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ →
      μ₂ = c • Measure.map
          (fun q : (p.adicCompletion ℚ) × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ) =>
            unipotentGL2 q.1 * diagUnits2 q.2.2.1 q.2.1 * lowerUnipotentGL2 q.2.2.2)
          ((((selfDualHaarAt ℚ p).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod ((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))).prod (selfDualHaarAt ℚ p))))).withDensity fun q =>
            (modulus (((q.2.1 * (q.2.2.1)⁻¹ : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) : ENNReal)) →
      ∀ s : ℂ,
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w (transposeInvN (Fin 2) g) *
            matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀ (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            ((χ⁻¹ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + 3 / 2)) μ₂ →
        Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
          w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
            ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 + s)) (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) ∧
        godementZeta2 p μ₂ (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (transposeInvN (Fin 2) g))
            (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ₀) χ⁻¹ (s + 3 / 2) =
          (((c.toReal : ℝ) : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mb)}).toReal : ℂ) *
            (((Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) {a : (p.adicCompletion ℚ)ˣ | Valued.v ((a : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-Md)}).toReal : ℂ) *
            (((selfDualHaarAt ℚ p) {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-Mc)}).toReal : ℂ)) *
            ∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 + s) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  intro μ₂ _ c hc0 hcT hchart s hint
  subst hΦ₀
  have hint' : Integrable (L2Box46.FG p w χ L Mb Mc Md s) μ₂ := hint
  obtain ⟨hJ, hI⟩ := L2Box46.transport p w χ wJ L Mb Mc Md s μ₂ c hc0 hcT hchart hint'
  obtain ⟨hTor, hval⟩ := L2Box46.integrable_Tor_and_integral_J p w θ₀ χ U wJ s hwlaw hcentral hχc hUo hU hwJ hL hMb hMc hMd
    hsuppJ hstabN hstabD hθ₀ hχ hJ
  refine ⟨hTor, ?_⟩
  change ∫ g, L2Box46.FG p w χ L Mb Mc Md s g ∂μ₂ = _
  rw [hI, hval]
  simp only [L2Box46.Va, measureReal_def]
  simp only [L2Box46.Tor]
  push_cast
  ring

end S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_godementZeta2_transposeInv_matFourier22_boxIndicator_eq_mul_torusZeta_dual_of_integrable_of_chart (solution)
