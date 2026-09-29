-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/716a6a2e-13f2-5ef2-81a5-8cf6aad23c55

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory Filter Topology
open scoped NNReal ENNReal Matrix Pointwise

noncomputable section

namespace LTUnipotentFEPt

open LanglandsTunnell.CubicInduction

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, _root_.mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  rw [transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]

theorem transposeInv3_inv (g : GL (Fin 3) A) : transposeInv3 g⁻¹ = (transposeInv3 g)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← transposeInv3_mul, inv_mul_cancel, transposeInv3_one]

theorem transposeInv3_iotaGL_diagUnitGL2 (a : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) = iotaGL (diagUnitGL2 a⁻¹) := by
  refine Units.ext ?_
  rw [transposeInv3_coe, ← map_inv, coe_iotaGL, coe_iotaGL]
  have : (diagUnitGL2 a)⁻¹ = diagUnitGL2 a⁻¹ := by
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    rw [Units.val_mul, coe_diagUnitGL2, coe_diagUnitGL2, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

theorem dualWhittakerFn3_apply_translate {R : Type*} (W : GL (Fin 3) A → R) (h X : GL (Fin 3) A) :
    dualWhittakerFn3 (fun x => W (x * h)) X = dualWhittakerFn3 W (X * transposeInv3 h) := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_transposeInv3, mul_assoc]

theorem iotaGL_mul_lowerUnipotent21_mul_upperUnipotent3 (a : Aˣ) (x y : A) :
    (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) * lowerUnipotent21 x * upperUnipotent3 0 0 y =
      upperUnipotent3 0 (x * y) ((a : A) * y) * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem weylPrime3_mul_upperUnipotent3_left_mul_weylPrime3 (x : A) :
    (weylPrime3 : GL (Fin 3) A) * upperUnipotent3 x 0 0 * weylPrime3 = upperUnipotent3 0 0 x := by
  refine Units.ext ?_
  simp only [Units.val_mul, weylPrime3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_dual_lowerUnipotent21 (r : Aˣ) (x x' : A) :
    (longWeyl3 : GL (Fin 3) A) * iotaGL (diagUnitGL2 r) * upperUnipotent3 (-x') 0 0 * weylPrime3 *
        lowerUnipotent21 x =
      upperUnipotent3 (x' * x) 0 (((r⁻¹ : Aˣ) : A) * x) *
        (longWeyl3 * iotaGL (diagUnitGL2 r) * upperUnipotent3 (-x') 0 0 * weylPrime3) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, lowerUnipotent21_coe, upperUnipotent3_coe,
    weylPrime3_coe, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]
  · rw [mul_right_comm, Units.inv_mul, one_mul]
  · rw [mul_mul_mul_comm, Units.inv_mul, one_mul, mul_comm x x', add_neg_cancel]

theorem upperUnipotent3_left_mul_neg (x : A) :
    (upperUnipotent3 x 0 0 : GL (Fin 3) A) * upperUnipotent3 (-x) 0 0 = 1 := by
  refine Units.ext ?_
  simp only [Units.val_mul, upperUnipotent3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem upperUnipotent3_zero : (upperUnipotent3 0 0 0 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  simp only [upperUnipotent3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lowerUnipotent21_zero : (lowerUnipotent21 0 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  simp only [lowerUnipotent21_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lowerUnipotent21_add (x y : A) :
    (lowerUnipotent21 (x + y) : GL (Fin 3) A) = lowerUnipotent21 x * lowerUnipotent21 y := by
  refine Units.ext ?_
  simp only [lowerUnipotent21_coe, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Algebra

section Topology

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_upperUnipotent3_right : Continuous fun z : F => upperUnipotent3 (0 : F) 0 z := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun z : F => ((upperUnipotent3 (0 : F) 0 z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_id']
  · refine continuous_matrix fun i j => ?_
    show Continuous fun z : F =>
      (((upperUnipotent3 (0 : F) 0 z : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, continuous_const, continuous_neg]

theorem continuous_lowerUnipotent21 : Continuous fun x : F => lowerUnipotent21 x := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun x : F => ((lowerUnipotent21 x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [continuous_const, continuous_id']
  · refine continuous_matrix fun i j => ?_
    show Continuous fun x : F =>
      (((lowerUnipotent21 x : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21, continuous_const, continuous_neg]

end Topology

section Balls

variable {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]

theorem exists_forall_valued_le_exp_neg_mem {s : Set F} (hs : s ∈ 𝓝 (0 : F)) :
    ∃ L : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs
  let vv : Valuation F (WithZero (Multiplicative ℤ)) := Valued.v
  let g : (WithZero (Multiplicative ℤ))ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass vv)).toMonoidHom γ
  refine ⟨(WithZero.log (g : WithZero (Multiplicative ℤ))).natAbs + 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  show Valued.v x < (g : WithZero (Multiplicative ℤ))
  calc Valued.v x ≤ WithZero.exp (-(((WithZero.log (g : WithZero (Multiplicative ℤ))).natAbs + 1 : ℕ) : ℤ)) := hx
    _ < WithZero.exp (WithZero.log (g : WithZero (Multiplicative ℤ))) := WithZero.exp_lt_exp.mpr (by omega)
    _ = g := WithZero.exp_log g.ne_zero

theorem exists_forall_valued_le_exp_neg_mem_subgroup {G : Type*} [Group G] [TopologicalSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) {φ : F → G} (hφ : Continuous φ) (h0 : φ 0 = 1) :
    ∃ L : ℕ, ∀ x : F, Valued.v x ≤ WithZero.exp (-(L : ℤ)) → φ x ∈ U := by
  have hs : φ ⁻¹' (U : Set G) ∈ 𝓝 (0 : F) :=
    hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [h0]; exact U.one_mem))
  exact exists_forall_valued_le_exp_neg_mem hs

theorem exists_valued_eq_exp {x : F} (hx : x ≠ 0) : ∃ k : ℤ, Valued.v x = WithZero.exp k :=
  ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)).symm⟩

end Balls

section Support

variable {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]

theorem exists_forall_apply_lowerUnipotent21_eq_zero {θ : AddChar F ℂ} (hθ : ∃ x₀ : F, θ x₀ ≠ 1)
    {W : GL (Fin 3) F → ℂ} (hW : IsGL3PsiWhittakerFn θ W)
    (U : Subgroup (GL (Fin 3) F)) (hU : IsOpen (U : Set (GL (Fin 3) F)))
    (hWU : ∀ k ∈ U, ∀ g : GL (Fin 3) F, W (g * k) = W g) (h : GL (Fin 3) F) :
    ∃ m : ℤ, ∀ (a : Fˣ) (x : F), WithZero.exp m < Valued.v x →
      W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0 := by
  obtain ⟨x₀, hx₀⟩ := hθ
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one θ)
  obtain ⟨k₀, hk₀⟩ := exists_valued_eq_exp hx₀0

  obtain ⟨L, hL⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    (φ := fun y : F => h⁻¹ * upperUnipotent3 (0 : F) 0 y * h)
    ((continuous_const.mul (continuous_upperUnipotent3_right (F := F))).mul continuous_const)
    (by simp only [upperUnipotent3_zero, mul_one, inv_mul_cancel])
  refine ⟨k₀ + L, fun a x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact not_lt_of_ge zero_le' hx

  set y : F := x₀ * x⁻¹ with hy
  have hyv : Valued.v y ≤ WithZero.exp (-(L : ℤ)) := by
    obtain ⟨kx, hkx⟩ := exists_valued_eq_exp hx0
    rw [hy, map_mul, map_inv₀, hk₀, hkx, ← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp]
    rw [hkx] at hx
    have := WithZero.exp_lt_exp.mp hx
    omega
  have hmem := hL y hyv
  have hxy : x * y = x₀ := by
    rw [hy, mul_comm x₀, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

  have h1 : W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) =
      W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h * (h⁻¹ * upperUnipotent3 (0 : F) 0 y * h)) :=
    (hWU _ hmem _).symm
  have h2 : iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h * (h⁻¹ * upperUnipotent3 (0 : F) 0 y * h) =
      upperUnipotent3 0 (x * y) ((a : F) * y) * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) := by
    rw [show iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h * (h⁻¹ * upperUnipotent3 (0 : F) 0 y * h) =
        (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * upperUnipotent3 0 0 y) * h by group,
      iotaGL_mul_lowerUnipotent21_mul_upperUnipotent3, mul_assoc]
  rw [h2, hW, zero_add, hxy] at h1
  have h3 : (1 - θ x₀) * W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4).symm hx₀
  · exact h4

end Support

section AdicBalls

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def ball (m : ℤ) : Set (v.adicCompletion K) := {x | Valued.v x ≤ WithZero.exp m}

variable {K v}

theorem mem_ball {m : ℤ} {x : v.adicCompletion K} : x ∈ ball K v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem zero_mem_ball (m : ℤ) : (0 : v.adicCompletion K) ∈ ball K v m := by
  rw [mem_ball, map_zero]; exact zero_le'

theorem ball_mono {m m' : ℤ} (h : m ≤ m') : ball K v m ⊆ ball K v m' :=
  fun x hx => le_trans hx (WithZero.exp_le_exp.mpr h)

theorem neg_mem_ball {m : ℤ} {x : v.adicCompletion K} (hx : x ∈ ball K v m) : -x ∈ ball K v m := by
  rw [mem_ball, Valuation.map_neg]; exact hx

theorem add_mem_ball {m : ℤ} {x y : v.adicCompletion K} (hx : x ∈ ball K v m) (hy : y ∈ ball K v m) :
    x + y ∈ ball K v m := by
  show Valued.v (x + y) ≤ _
  exact le_trans (Valuation.map_add _ x y) (max_le hx hy)

variable (K v)

theorem exists_uniformizer : ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  exact ⟨((WithVal.equiv (HeightOneSpectrum.valuation K v)).symm π : WithVal (HeightOneSpectrum.valuation K v)),
    by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ⟩

theorem exists_valued_eq_exp_int (m : ℤ) : ∃ a : v.adicCompletion K, Valued.v a = WithZero.exp m := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer K v
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero.symm hϖ
  refine ⟨ϖ ^ (-m), ?_⟩
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  congr 1
  simp

variable {K v}

theorem ball_eq_closedBall {m : ℤ} {a : v.adicCompletion K} (ha : Valued.v a = WithZero.exp m) :
    ball K v m = Metric.closedBall (0 : v.adicCompletion K) ‖a‖ := by
  ext x
  rw [mem_ball, Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_iff, ha]

theorem norm_pos_of_valued_eq_exp {m : ℤ} {a : v.adicCompletion K} (ha : Valued.v a = WithZero.exp m) : 0 < ‖a‖ := by
  refine norm_pos_iff.mpr ?_
  intro h; rw [h, map_zero] at ha; exact WithZero.exp_ne_zero.symm ha

variable (K v)

theorem isCompact_ball (m : ℤ) : IsCompact (ball K v m) := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v m
  rw [ball_eq_closedBall ha]
  exact isCompact_closedBall _ _

theorem isOpen_ball (m : ℤ) : IsOpen (ball K v m) := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v m
  rw [ball_eq_closedBall ha]
  exact IsUltrametricDist.isOpen_closedBall _ (norm_pos_of_valued_eq_exp ha).ne'

theorem isClosed_ball (m : ℤ) : IsClosed (ball K v m) :=
  (isCompact_ball K v m).isClosed

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem measurableSet_ball (m : ℤ) : MeasurableSet (ball K v m) :=
  (isClosed_ball K v m).measurableSet

theorem measure_ball_lt_top (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν (ball K v m) < ⊤ :=
  (isCompact_ball K v m).measure_lt_top

theorem measure_ball_pos (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] (m : ℤ) :
    0 < ν (ball K v m) :=
  (isOpen_ball K v m).measure_pos ν ⟨0, zero_mem_ball m⟩

theorem measureReal_ball_pos (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] (m : ℤ) :
    0 < ν.real (ball K v m) :=
  ENNReal.toReal_pos (measure_ball_pos K v ν m).ne' (measure_ball_lt_top K v ν m).ne

theorem norm_eq_of_valued_eq_exp {m : ℤ} {a : v.adicCompletion K} (ha : Valued.v a = WithZero.exp m) :
    ‖a‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, ha, WithZero.exp,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.coe_ne_zero), WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow]
  rfl

theorem measureReal_ball (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] (m : ℤ) :
    ν.real (ball K v m) = (Ideal.absNorm v.asIdeal : ℝ) ^ m * ν.real (ball K v 0) := by
  obtain ⟨a, ha⟩ := exists_valued_eq_exp_int K v m
  have ha0 : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact WithZero.exp_ne_zero.symm ha
  set u : (v.adicCompletion K)ˣ := Units.mk0 a ha0 with hu
  have hset : ball K v m = u • ball K v 0 := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_ball, mem_ball, Units.smul_def, smul_eq_mul, map_mul,
      Units.val_inv_eq_inv_val, map_inv₀, hu, Units.val_mk0, ha, ← WithZero.exp_neg, WithZero.exp_zero]
    constructor
    · intro hx
      calc WithZero.exp (-m) * Valued.v x ≤ WithZero.exp (-m) * WithZero.exp m :=
            mul_le_mul_right hx _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · intro hx
      have := mul_le_mul_right hx (WithZero.exp m)
      rwa [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul, mul_one] at this
  have hmeas : ν (ball K v m) = (distribHaarChar (v.adicCompletion K) u : ℝ≥0∞) * ν (ball K v 0) := by
    rw [hset, distribHaarChar_mul]
  have hchar : (distribHaarChar (v.adicCompletion K) u : ℝ≥0) = ‖a‖₊ := by
    rw [← modulus_coe_units, hu, Units.val_mk0, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
  rw [measureReal_def, measureReal_def, hmeas, ENNReal.toReal_mul, hchar]
  simp only [ENNReal.coe_toReal, coe_nnnorm]
  rw [norm_eq_of_valued_eq_exp K v ha]

theorem measureReal_ball_mul_measureReal_ball (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure] (m n : ℤ) :
    ν.real (ball K v m) * ν.real (ball K v (n - m)) = (Ideal.absNorm v.asIdeal : ℝ) ^ n * ν.real (ball K v 0) ^ 2 := by
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    have := HeightOneSpectrum.one_lt_absNorm v
    positivity
  rw [measureReal_ball K v ν m, measureReal_ball K v ν (n - m), zpow_sub₀ hq]
  field_simp

end AdicBalls

section Smooth

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

def IsSmooth3 (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g : GL (Fin 3) F, W (g * k) = W g

theorem isSmooth3_zero : IsSmooth3 (0 : GL (Fin 3) F → ℂ) :=
  ⟨⊤, by simp, fun _ _ _ => rfl⟩

theorem IsSmooth3.add {W₁ W₂ : GL (Fin 3) F → ℂ} (h₁ : IsSmooth3 W₁) (h₂ : IsSmooth3 W₂) :
    IsSmooth3 (W₁ + W₂) := by
  obtain ⟨U₁, hU₁, hW₁⟩ := h₁
  obtain ⟨U₂, hU₂, hW₂⟩ := h₂
  refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
  · rw [Subgroup.coe_inf]; exact hU₁.inter hU₂
  · simp only [Pi.add_apply, hW₁ k (Subgroup.mem_inf.mp hk).1 g, hW₂ k (Subgroup.mem_inf.mp hk).2 g]

theorem IsSmooth3.smul (c : ℂ) {W : GL (Fin 3) F → ℂ} (h : IsSmooth3 W) : IsSmooth3 (c • W) := by
  obtain ⟨U, hU, hW⟩ := h
  exact ⟨U, hU, fun k hk g => by simp only [Pi.smul_apply, hW k hk g]⟩

theorem IsSmooth3.translate {W : GL (Fin 3) F → ℂ} (h : IsSmooth3 W) (h₀ : GL (Fin 3) F) :
    IsSmooth3 (fun x => W (x * h₀)) := by
  obtain ⟨U, hU, hW⟩ := h
  refine ⟨U.comap (MulAut.conj h₀⁻¹).toMonoidHom, ?_, fun k hk g => ?_⟩
  · rw [Subgroup.coe_comap]
    refine hU.preimage ?_
    show Continuous fun k : GL (Fin 3) F => h₀⁻¹ * k * h₀⁻¹⁻¹
    exact (continuous_const.mul continuous_id).mul continuous_const
  · have hk' : h₀⁻¹ * k * h₀ ∈ U := by
      have := Subgroup.mem_comap.mp hk
      simpa using this
    show W (g * k * h₀) = W (g * h₀)
    rw [show g * k * h₀ = g * h₀ * (h₀⁻¹ * k * h₀) by group]
    exact hW _ hk' _

theorem isSmooth3_of_mem_gl3CyclicSubspace {W : GL (Fin 3) F → ℂ} (hW : IsSmooth3 W)
    {W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) : IsSmooth3 W' := by
  refine Submodule.span_induction (p := fun f _ => IsSmooth3 f) ?_ ?_ ?_ ?_ hW'
  · rintro _ ⟨h₀, rfl⟩
    exact hW.translate h₀
  · exact isSmooth3_zero
  · intro f₁ f₂ _ _ h₁ h₂; exact h₁.add h₂
  · intro c f _ h; exact h.smul c

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem isGL3PsiWhittakerFn_of_mem_gl3CyclicSubspace {θ : AddChar F ℂ} {W : GL (Fin 3) F → ℂ}
    (hW : IsGL3PsiWhittakerFn θ W) {W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) :
    IsGL3PsiWhittakerFn θ W' := by
  have hle : gl3CyclicSubspace W ≤ gl3PsiWhittakerFnSpace F ℂ θ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h₀, rfl⟩
    exact rightTranslate_mem_gl3PsiWhittakerFnSpace θ h₀ ((mem_gl3PsiWhittakerFnSpace_iff θ W).mpr hW)
  exact (mem_gl3PsiWhittakerFnSpace_iff θ W').mp (hle hW')

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem gl3CyclicSubspace_le_of_mem {W W' : GL (Fin 3) F → ℂ} (hW' : W' ∈ gl3CyclicSubspace W) :
    gl3CyclicSubspace W' ≤ gl3CyclicSubspace W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h₀, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace W h₀ hW'

end Smooth

section Average

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

def transl (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K)) (x : v.adicCompletion K) :
    GL (Fin 3) (v.adicCompletion K) → ℂ :=
  fun g => W (g * (h⁻¹ * lowerUnipotent21 x * h))

def avg (ν : Measure (v.adicCompletion K)) (W : GL (Fin 3) (v.adicCompletion K) → ℂ)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) : GL (Fin 3) (v.adicCompletion K) → ℂ :=
  fun g => ∫ x, (ball K v m).indicator (fun _ => (1 : ℂ)) x * W (g * (h⁻¹ * lowerUnipotent21 x * h)) ∂ν

variable {K v}

theorem transl_apply (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K))
    (x : v.adicCompletion K) (g : GL (Fin 3) (v.adicCompletion K)) :
    transl K v W h x g = W (g * (h⁻¹ * lowerUnipotent21 x * h)) := rfl

theorem transl_mem_gl3CyclicSubspace (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K))
    (x : v.adicCompletion K) : transl K v W h x ∈ gl3CyclicSubspace W :=
  Submodule.subset_span ⟨h⁻¹ * lowerUnipotent21 x * h, rfl⟩

theorem exists_forall_transl_add_eq {W : GL (Fin 3) (v.adicCompletion K) → ℂ}
    (U : Subgroup (GL (Fin 3) (v.adicCompletion K))) (hU : IsOpen (U : Set (GL (Fin 3) (v.adicCompletion K))))
    (hWU : ∀ k ∈ U, ∀ g : GL (Fin 3) (v.adicCompletion K), W (g * k) = W g) (h : GL (Fin 3) (v.adicCompletion K)) :
    ∃ L : ℕ, ∀ x y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (-(L : ℤ)) →
      transl K v W h (x + y) = transl K v W h x := by
  obtain ⟨L, hL⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    (φ := fun y : v.adicCompletion K => h⁻¹ * lowerUnipotent21 y * h)
    ((continuous_const.mul (continuous_lowerUnipotent21 (F := v.adicCompletion K))).mul continuous_const)
    (by simp only [lowerUnipotent21_zero, mul_one, inv_mul_cancel])
  refine ⟨L, fun x y hy => ?_⟩
  funext g
  rw [transl_apply, transl_apply, lowerUnipotent21_add,
    show g * (h⁻¹ * (lowerUnipotent21 x * lowerUnipotent21 y) * h) =
      g * (h⁻¹ * lowerUnipotent21 x * h) * (h⁻¹ * lowerUnipotent21 y * h) by group]
  exact hWU _ (hL y hy) _

theorem isLocallyConstant_transl {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) : IsLocallyConstant (transl K v W h) := by
  obtain ⟨U, hU, hWU⟩ := hW
  obtain ⟨L, hL⟩ := exists_forall_transl_add_eq U hU hWU h
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have hmem : {y : v.adicCompletion K | y - x ∈ ball K v (-(L : ℤ))} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_ball K v (-(L : ℤ))).preimage (continuous_id.sub continuous_const)
    · show x - x ∈ ball K v (-(L : ℤ))
      rw [sub_self]; exact zero_mem_ball _
  filter_upwards [hmem] with y hy
  have := hL x (y - x) hy
  rwa [add_sub_cancel] at this

theorem finite_image_transl {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) : (transl K v W h '' ball K v m).Finite := by
  haveI : CompactSpace (ball K v m) := isCompact_iff_compactSpace.mp (isCompact_ball K v m)
  have hlc : IsLocallyConstant (transl K v W h ∘ ((↑) : ball K v m → v.adicCompletion K)) :=
    (isLocallyConstant_transl hW h).comp_continuous continuous_subtype_val
  have := hlc.range_finite
  rwa [Set.range_comp, Subtype.range_coe] at this

def piece (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ)
    (f : GL (Fin 3) (v.adicCompletion K) → ℂ) : Set (v.adicCompletion K) :=
  ball K v m ∩ transl K v W h ⁻¹' {f}

theorem measurableSet_piece {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) (f : GL (Fin 3) (v.adicCompletion K) → ℂ) :
    MeasurableSet (piece W h m f) :=
  (measurableSet_ball K v m).inter ((isLocallyConstant_transl hW h).isOpen_fiber f).measurableSet

theorem piece_subset (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ)
    (f : GL (Fin 3) (v.adicCompletion K) → ℂ) : piece W h m f ⊆ ball K v m :=
  Set.inter_subset_left

theorem measure_piece_lt_top (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ)
    (f : GL (Fin 3) (v.adicCompletion K) → ℂ) : ν (piece W h m f) < ⊤ :=
  lt_of_le_of_lt (measure_mono (piece_subset W h m f)) (measure_ball_lt_top K v ν m)

theorem pairwiseDisjoint_piece (W : GL (Fin 3) (v.adicCompletion K) → ℂ) (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ)
    (T : Set (GL (Fin 3) (v.adicCompletion K) → ℂ)) : T.Pairwise (Function.onFun Disjoint (piece W h m)) := by
  intro f _ f' _ hff'
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨_, hx⟩ ⟨_, hx'⟩
  exact hff' (hx.symm.trans hx')

theorem ball_eq_biUnion_piece {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) :
    ball K v m = ⋃ f ∈ (finite_image_transl hW h m).toFinset, piece W h m f := by
  ext x
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
  constructor
  · intro hx
    exact ⟨transl K v W h x, ⟨x, hx, rfl⟩, hx, rfl⟩
  · rintro ⟨f, _, hx, _⟩
    exact hx

theorem avg_apply_eq_sum (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) (g : GL (Fin 3) (v.adicCompletion K)) :
    avg K v ν W h m g =
      ∑ f ∈ (finite_image_transl hW h m).toFinset, (ν.real (piece W h m f) : ℂ) * f g := by
  unfold avg
  have h1 : (fun x => (ball K v m).indicator (fun _ => (1 : ℂ)) x * W (g * (h⁻¹ * lowerUnipotent21 x * h))) =
      (ball K v m).indicator (fun x => transl K v W h x g) := by
    funext x
    by_cases hx : x ∈ ball K v m
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul, transl_apply]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [h1, integral_indicator (measurableSet_ball K v m)]
  conv_lhs => rw [ball_eq_biUnion_piece hW h m]
  rw [integral_biUnion_finset _ (fun f _ => measurableSet_piece hW h m f) (pairwiseDisjoint_piece W h m _)]
  · refine Finset.sum_congr rfl fun f hf => ?_
    have hcongr : Set.EqOn (fun x => transl K v W h x g) (fun _ => f g) (piece W h m f) := by
      rintro x ⟨_, hx⟩
      show transl K v W h x g = f g
      rw [show transl K v W h x = f from hx]
    rw [setIntegral_congr_fun (measurableSet_piece hW h m f) hcongr, setIntegral_const, measureReal_def]
    simp [Complex.real_smul]
  · intro f hf
    have hcongr : Set.EqOn (fun _ => f g) (fun x => transl K v W h x g) (piece W h m f) := by
      rintro x ⟨_, hx⟩
      show f g = transl K v W h x g
      rw [show transl K v W h x = f from hx]
    exact (integrableOn_const (measure_piece_lt_top ν W h m f).ne).congr_fun hcongr (measurableSet_piece hW h m f)

theorem avg_eq_sum (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) :
    avg K v ν W h m = ∑ f ∈ (finite_image_transl hW h m).toFinset, (ν.real (piece W h m f) : ℂ) • f := by
  funext g
  rw [avg_apply_eq_sum ν hW h m g, Finset.sum_apply]
  rfl

theorem avg_mem_gl3CyclicSubspace (ν : Measure (v.adicCompletion K)) [ν.IsAddHaarMeasure]
    {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) : avg K v ν W h m ∈ gl3CyclicSubspace W := by
  rw [avg_eq_sum ν hW h m]
  refine Submodule.sum_smul_mem _ _ fun f hf => ?_
  obtain ⟨x, _, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
  exact transl_mem_gl3CyclicSubspace W h x

theorem sum_indicator_piece_mul_eq {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) (G : (GL (Fin 3) (v.adicCompletion K) → ℂ) → ℂ)
    {x : v.adicCompletion K} (hx : x ∈ ball K v m) :
    ∑ f ∈ (finite_image_transl hW h m).toFinset, (piece W h m f).indicator (fun _ => (1 : ℂ)) x * G f =
      G (transl K v W h x) := by
  rw [Finset.sum_eq_single_of_mem (transl K v W h x)]
  · rw [Set.indicator_of_mem (show x ∈ piece W h m (transl K v W h x) from ⟨hx, rfl⟩), one_mul]
  · exact (Set.Finite.mem_toFinset _).mpr ⟨x, hx, rfl⟩
  · intro f _ hf
    rw [Set.indicator_of_notMem, zero_mul]
    rintro ⟨_, hxf⟩
    exact hf hxf.symm

theorem sum_indicator_piece_mul_eq_zero {W : GL (Fin 3) (v.adicCompletion K) → ℂ} (hW : IsSmooth3 W)
    (h : GL (Fin 3) (v.adicCompletion K)) (m : ℤ) (G : (GL (Fin 3) (v.adicCompletion K) → ℂ) → ℂ)
    {x : v.adicCompletion K} (hx : x ∉ ball K v m) :
    ∑ f ∈ (finite_image_transl hW h m).toFinset, (piece W h m f).indicator (fun _ => (1 : ℂ)) x * G f = 0 := by
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [Set.indicator_of_notMem, zero_mul]
  rintro ⟨hx', _⟩
  exact hx hx'

end Average

section Transfer

variable {v : HeightOneSpectrum (𝓞 ℚ)}

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

structure GoodRadius (ψ : AddChar (v.adicCompletion ℚ) ℂ) (n : ℤ) (W : LocalGL3 v → ℂ) (h : LocalGL3 v) (m : ℤ) :
    Prop where
  support : ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), x ∉ ball ℚ v m →
    W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0
  smooth : ∀ y : v.adicCompletion ℚ, y ∈ ball ℚ v (n - m) → ∀ g : LocalGL3 v,
    W (g * (h⁻¹ * upperUnipotent3 0 0 y * h)) = W g

theorem exists_goodRadius {ψ : AddChar (v.adicCompletion ℚ) ℂ} {n : ℤ}
    (hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    {W : LocalGL3 v → ℂ} (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) (hWs : IsSmooth3 W) (h : LocalGL3 v) :
    ∃ m : ℤ, GoodRadius ψ n W h m := by
  obtain ⟨U, hU, hWU⟩ := hWs
  have hθ : ∃ x₀ : v.adicCompletion ℚ, ψ⁻¹ x₀ ≠ 1 := by
    obtain ⟨x, _, hx⟩ := hψn'
    exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩
  obtain ⟨m₀, hm₀⟩ := exists_forall_apply_lowerUnipotent21_eq_zero hθ hW U hU hWU h
  obtain ⟨L, hL⟩ := exists_forall_valued_le_exp_neg_mem_subgroup U hU
    (φ := fun y : v.adicCompletion ℚ => h⁻¹ * upperUnipotent3 (0 : v.adicCompletion ℚ) 0 y * h)
    ((continuous_const.mul (continuous_upperUnipotent3_right (F := v.adicCompletion ℚ))).mul continuous_const)
    (by simp only [upperUnipotent3_zero, mul_one, inv_mul_cancel])
  refine ⟨max m₀ (n + L), ⟨fun a x hx => hm₀ a x ?_, fun y hy g => hWU _ (hL y ?_) g⟩⟩
  · have hx' : ¬ Valued.v x ≤ WithZero.exp (max m₀ (n + L)) := hx
    exact lt_of_le_of_lt (WithZero.exp_le_exp.mpr (le_max_left _ _)) (not_le.mp hx')
  · exact le_trans hy (WithZero.exp_le_exp.mpr (by omega))

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {n : ℤ} {W : LocalGL3 v → ℂ} {h : LocalGL3 v} {m : ℤ}

theorem inner_primal (hR : GoodRadius ψ n W h m) (ν : Measure (v.adicCompletion ℚ)) (a : (v.adicCompletion ℚ)ˣ) :
    (∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ∂ν) =
      avg ℚ v ν W h m (iotaGL (diagUnitGL2 a) * h) := by
  unfold avg
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hg : iotaGL (diagUnitGL2 a) * h * (h⁻¹ * lowerUnipotent21 x * h) =
      iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h := by group
  show W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) =
    (ball ℚ v m).indicator (fun _ => (1 : ℂ)) x * W (iotaGL (diagUnitGL2 a) * h * (h⁻¹ * lowerUnipotent21 x * h))
  rw [hg]
  by_cases hx : x ∈ ball ℚ v m
  · rw [Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, zero_mul, hR.support a x hx]

theorem localZeta31_eq_localZeta30_avg (hR : GoodRadius ψ n W h m)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    localZeta31 v μ ν W χ s h = localZeta30 v μ (avg ℚ v ν W h m) χ s h := by
  unfold localZeta31 localZeta30
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  show (∫ x, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) ∂ν) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
    avg ℚ v ν W h m (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
  rw [inner_primal hR ν a]

theorem isLocalZeta31ConvergentAbove_of_transl (hR : GoodRadius ψ n W h m) (hWs : IsSmooth3 W)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℝ)
    (hconv : ∀ x : v.adicCompletion ℚ, IsLocalZeta30ConvergentAbove v μ (transl ℚ v W h x) χ h σ) :
    IsLocalZeta31ConvergentAbove v μ ν W χ h σ := by
  intro s hs
  set T := (finite_image_transl hWs h m).toFinset with hT
  set G : (LocalGL3 v → ℂ) → (v.adicCompletion ℚ)ˣ → ℂ := fun f a =>
    f (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) with hG
  have heq : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((χ p.1 : ℂˣ) : ℂ) *
        ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun p => ∑ f ∈ T, G f p.1 * (piece W h m f).indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp_rw [mul_comm (G _ p.1)]
    by_cases hx : p.2 ∈ ball ℚ v m
    · rw [sum_indicator_piece_mul_eq hWs h m (fun f => G f p.1) hx, hG]
      simp only [transl_apply]
      rw [show iotaGL (diagUnitGL2 p.1) * h * (h⁻¹ * lowerUnipotent21 p.2 * h) =
        iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h by group]
    · rw [sum_indicator_piece_mul_eq_zero hWs h m (fun f => G f p.1) hx, hR.support p.1 p.2 hx, zero_mul,
        zero_mul]
  rw [heq]
  refine integrable_finsetSum _ fun f hf => ?_
  obtain ⟨x, _, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
  refine Integrable.mul_prod (hconv x s hs) ?_
  exact (integrableOn_const (measure_piece_lt_top ν W h m _).ne).integrable_indicator
    (measurableSet_piece hWs h m _)

theorem transposeInv3_point (t : (v.adicCompletion ℚ)ˣ) (x' : v.adicCompletion ℚ) (h : LocalGL3 v) :
    transposeInv3 (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) =
      iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h := by
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2,
    transposeInv3_lowerUnipotent21, transposeInv3_weylPrime3, transposeInv3_transposeInv3]
  simp only [mul_assoc]

theorem dualWhittakerFn3_avg_apply (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) (ν : Measure (v.adicCompletion ℚ))
    (t : (v.adicCompletion ℚ)ˣ) (x' : v.adicCompletion ℚ) :
    dualWhittakerFn3 (avg ℚ v ν W h m) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) =
      tateFourier ψ ν ((ball ℚ v m).indicator fun _ => (1 : ℂ)) (-x') *
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, tateFourier]
  unfold avg
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ball ℚ v m).indicator (fun _ => (1 : ℂ)) x *
      W (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) *
        (h⁻¹ * lowerUnipotent21 x * h)) =
    (ball ℚ v m).indicator (fun _ => (1 : ℂ)) x * ψ (x * -x') *
      W (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)))
  rw [transposeInv3_point]
  have hmat : longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h) *
      (h⁻¹ * lowerUnipotent21 x * h) =
      upperUnipotent3 (x' * x) 0 (((t⁻¹⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) * x) *
        (longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h)) := by
    rw [show longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h) *
        (h⁻¹ * lowerUnipotent21 x * h) =
        (longWeyl3 * iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * lowerUnipotent21 x) * h
        by group, longWeyl3_dual_lowerUnipotent21]
    group
  rw [hmat, hW, add_zero, AddChar.inv_apply, show -(x' * x) = x * -x' by ring]
  ring

theorem tateFourier_ball (hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (y : v.adicCompletion ℚ) :
    tateFourier ψ ν ((ball ℚ v m).indicator fun _ => (1 : ℂ)) (-y) =
      (ν.real (ball ℚ v m) : ℂ) * (ball ℚ v (n - m)).indicator (fun _ => (1 : ℂ)) y := by
  have h := LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le ℚ v ν ψ n hψn hψn' 0 (-m) (-y)
  have hset : {x : v.adicCompletion ℚ | Valued.v (x - 0) ≤ WithZero.exp (-(-m))} = ball ℚ v m := by
    ext x; rw [Set.mem_setOf_eq, sub_zero, neg_neg]; rfl
  have hset' : {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(-m))} = ball ℚ v m := by
    ext x; rw [Set.mem_setOf_eq, neg_neg]; rfl
  have hset'' : {y' : v.adicCompletion ℚ | Valued.v y' ≤ WithZero.exp (n + -m)} = ball ℚ v (n - m) := by
    ext x; rw [Set.mem_setOf_eq, ← sub_eq_add_neg]; rfl
  rw [hset, hset', hset'', zero_mul, AddChar.map_zero_eq_one, one_mul] at h
  rw [h]
  congr 1
  by_cases hy : y ∈ ball ℚ v (n - m)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (neg_mem_ball hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
    intro hy'
    exact hy (by simpa using neg_mem_ball hy')

theorem dualWhittakerFn3_apply_lowerUnipotent21_eq (hR : GoodRadius ψ n W h m) (t : (v.adicCompletion ℚ)ˣ)
    {x' : v.adicCompletion ℚ} (hx' : x' ∈ ball ℚ v (n - m)) :
    dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) =
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_point]
  have h1 : transposeInv3 (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) =
      iotaGL (diagUnitGL2 t⁻¹) * weylPrime3 * h := by
    rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2, transposeInv3_weylPrime3,
      transposeInv3_transposeInv3, mul_assoc]
  rw [h1]
  have h2 : longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h) =
      longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * weylPrime3 * h) *
        (h⁻¹ * (weylPrime3 * upperUnipotent3 (-x') 0 0 * weylPrime3) * h) := by
    have hw : (weylPrime3 : LocalGL3 v) * weylPrime3 = 1 := weylPrime3_mul_self
    calc longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * upperUnipotent3 (-x') 0 0 * weylPrime3 * h)
        = longWeyl3 * (iotaGL (diagUnitGL2 t⁻¹) * (weylPrime3 * weylPrime3) * upperUnipotent3 (-x') 0 0 *
            weylPrime3 * h) := by rw [hw, mul_one]
      _ = _ := by group
  rw [h2, weylPrime3_mul_upperUnipotent3_left_mul_weylPrime3, hR.smooth (-x') (neg_mem_ball hx')]

theorem inner_dual (hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) (hR : GoodRadius ψ n W h m)
    (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure] (t : (v.adicCompletion ℚ)ˣ) :
    (∫ x', dualWhittakerFn3 (avg ℚ v ν W h m)
        (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) ∂ν) =
      ((ν.real (ball ℚ v m) * ν.real (ball ℚ v (n - m)) : ℝ) : ℂ) *
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) := by
  simp_rw [dualWhittakerFn3_avg_apply hW, tateFourier_ball hψn hψn' ν]
  have hind : (fun x' => (ν.real (ball ℚ v m) : ℂ) * (ball ℚ v (n - m)).indicator (fun _ => (1 : ℂ)) x' *
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h))) =
      fun x' => (ν.real (ball ℚ v m) : ℂ) * (ball ℚ v (n - m)).indicator (fun x' =>
        dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h))) x' := by
    funext x'
    by_cases hx : x' ∈ ball ℚ v (n - m)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, zero_mul]
  rw [hind, integral_const_mul, integral_indicator (measurableSet_ball ℚ v _),
    setIntegral_congr_fun (measurableSet_ball ℚ v _)
      (fun x' hx' => dualWhittakerFn3_apply_lowerUnipotent21_eq hR t hx'),
    setIntegral_const, Complex.real_smul, ← mul_assoc, Complex.ofReal_mul]

theorem localZetaDual31_avg_eq (hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) (hR : GoodRadius ψ n W h m)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) :
    localZetaDual31 v μ ν (avg ℚ v ν W h m) χ s h =
      ((ν.real (ball ℚ v m) * ν.real (ball ℚ v (n - m)) : ℝ) : ℂ) *
        localZeta30 v μ (dualWhittakerFn3 W) χ⁻¹ s (weylPrime3 * transposeInv3 h) := by
  unfold localZetaDual31 localZeta31 localZeta30
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (∫ x', dualWhittakerFn3 (avg ℚ v ν W h m)
        (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) ∂ν) *
      ((χ⁻¹ t : ℂˣ) : ℂ) * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
    ((ν.real (ball ℚ v m) * ν.real (ball ℚ v (n - m)) : ℝ) : ℂ) *
      (dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) *
        ((χ⁻¹ t : ℂˣ) : ℂ) * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
  rw [inner_dual hψn hψn' hW hR ν t]
  ring

theorem isLocalZeta30ConvergentAbove_dual_of_avg
    (hψn : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) (hR : GoodRadius ψ n W h m)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℝ)
    (hconv : IsLocalZeta31ConvergentAbove v μ ν (dualWhittakerFn3 (avg ℚ v ν W h m)) χ⁻¹
      (weylPrime3 * transposeInv3 h) σ) :
    IsLocalZeta30ConvergentAbove v μ (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 h) σ := by
  intro s hs
  have h1 := (hconv s hs).integral_prod_left
  set C : ℝ := ν.real (ball ℚ v m) * ν.real (ball ℚ v (n - m)) with hC
  have hC0 : (C : ℂ) ≠ 0 := by
    rw [hC]
    exact_mod_cast (mul_pos (measureReal_ball_pos ℚ v ν m) (measureReal_ball_pos ℚ v ν (n - m))).ne'
  have key : ∀ t : (v.adicCompletion ℚ)ˣ,
      (∫ x' : v.adicCompletion ℚ, dualWhittakerFn3 (avg ℚ v ν W h m)
          (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x' * (weylPrime3 * transposeInv3 h)) *
        ((χ⁻¹ t : ℂˣ) : ℂ) * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) ∂ν) =
      (C : ℂ) * (dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) *
        ((χ⁻¹ t : ℂˣ) : ℂ) * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro t
    rw [integral_mul_const, integral_mul_const, inner_dual hψn hψn' hW hR ν t, hC]
    ring
  have h2 : Integrable (fun t : (v.adicCompletion ℚ)ˣ =>
      (C : ℂ) * (dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * (weylPrime3 * transposeInv3 h)) *
        ((χ⁻¹ t : ℂˣ) : ℂ) * ((modulus (t : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))) μ :=
    h1.congr (Filter.Eventually.of_forall fun t => key t)
  refine (h2.const_mul ((C : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun t => ?_)
  show (C : ℂ)⁻¹ * ((C : ℂ) * _) = _
  rw [← mul_assoc, inv_mul_cancel₀ hC0, one_mul]

end Transfer

section AssemblyPt

variable {v : HeightOneSpectrum (𝓞 ℚ)}

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isLocalZeta30ConvergentAbove_mono {μ : Measure (v.adicCompletion ℚ)ˣ} {W : LocalGL3 v → ℂ}
    {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ σ' : ℝ}
    (h : IsLocalZeta30ConvergentAbove v μ W χ g σ) (hle : σ ≤ σ') :
    IsLocalZeta30ConvergentAbove v μ W χ g σ' :=
  fun s hs => h s (lt_of_le_of_lt hle hs)

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {n : ℤ} {W : LocalGL3 v → ℂ} {h : LocalGL3 v} {m : ℤ}

theorem isLocalZeta31ConvergentAbove_of_transl_ball (hR : GoodRadius ψ n W h m) (hWs : IsSmooth3 W)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (σ : ℝ)
    (hconv : ∀ x ∈ ball ℚ v m, IsLocalZeta30ConvergentAbove v μ (transl ℚ v W h x) χ h σ) :
    IsLocalZeta31ConvergentAbove v μ ν W χ h σ := by
  intro s hs
  set T := (finite_image_transl hWs h m).toFinset with hT
  set G : (LocalGL3 v → ℂ) → (v.adicCompletion ℚ)ˣ → ℂ := fun f a =>
    f (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
      ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) with hG
  have heq : (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h) * ((χ p.1 : ℂˣ) : ℂ) *
        ((modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun p => ∑ f ∈ T, G f p.1 * (piece W h m f).indicator (fun _ => (1 : ℂ)) p.2 := by
    funext p
    simp_rw [mul_comm (G _ p.1)]
    by_cases hx : p.2 ∈ ball ℚ v m
    · rw [sum_indicator_piece_mul_eq hWs h m (fun f => G f p.1) hx, hG]
      simp only [transl_apply]
      rw [show iotaGL (diagUnitGL2 p.1) * h * (h⁻¹ * lowerUnipotent21 p.2 * h) =
        iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * h by group]
    · rw [sum_indicator_piece_mul_eq_zero hWs h m (fun f => G f p.1) hx, hR.support p.1 p.2 hx, zero_mul,
        zero_mul]
  rw [heq]
  refine integrable_finsetSum _ fun f hf => ?_
  obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
  refine Integrable.mul_prod (hconv x hx s hs) ?_
  exact (integrableOn_const (measure_piece_lt_top ν W h m _).ne).integrable_indicator
    (measurableSet_piece hWs h m _)

end AssemblyPt

end LTUnipotentFEPt

open LanglandsTunnell.CubicInduction LTUnipotentFEPt

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (n : ℤ)
    (hψn : ∀ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : p.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn ψ⁻¹ W)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (γ : ℂ → ℂ) (g : LocalGL3 p) :
    letI := localBorel ℚ p
    ∀ (μ : Measure (p.adicCompletion ℚ)ˣ) (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      (∀ W' ∈ gl3CyclicSubspace W, ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta30ConvergentAbove p μ W' χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta30 p μ W' χ s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
          IsLocalZeta31ConvergentAbove p μ ν (dualWhittakerFn3 W') χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            localZetaDual31 p μ ν W' χ (1 - s) g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
                γ s)) →
      ∃ (Q₁ Q₂ : Polynomial ℂ) (k : ℤ) (σ₀ σ₁ : ℝ), Q₂ ≠ 0 ∧
          IsLocalZeta31ConvergentAbove p μ ν W χ g σ₀ ∧
          (∀ s : ℂ, σ₀ < s.re →
            localZeta31 p μ ν W χ s g * Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s)) ∧
          IsLocalZeta30ConvergentAbove p μ (dualWhittakerFn3 W) χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
          (∀ s : ℂ, σ₁ < (1 - s).re →
            (Ideal.absNorm p.asIdeal : ℂ) ^ n *
                  ((ν.real {x : p.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 *
                localZeta30 p μ (dualWhittakerFn3 W) χ⁻¹ (1 - s) (weylPrime3 * transposeInv3 g) *
              Q₂.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
              Q₁.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((k : ℂ) * s) *
                γ s) := by
  intro μ ν _ hyp
  have hWs : IsSmooth3 W := hWsm
  obtain ⟨m, hR⟩ := exists_goodRadius hψn' hW hWs g
  have havg : avg ℚ p ν W g m ∈ gl3CyclicSubspace W := avg_mem_gl3CyclicSubspace ν hWs g m
  obtain ⟨Q₁, Q₂, k, σ₀'', σ₁, hQ₂, hc0, he0, hc1, he1⟩ := hyp _ havg

  have hex : ∀ f : LocalGL3 p → ℂ, f ∈ gl3CyclicSubspace W →
      ∃ σ : ℝ, IsLocalZeta30ConvergentAbove p μ f χ g σ := by
    intro f hf
    obtain ⟨-, -, -, σ, -, -, hc, -, -, -⟩ := hyp f hf
    exact ⟨σ, hc⟩
  choose! σg hσg using hex
  set T := (finite_image_transl hWs g m).toFinset with hT
  set σ₀ : ℝ := max σ₀'' (∑ f ∈ T, |σg f|) with hσ₀
  have hσ₀_transl : ∀ x ∈ ball ℚ p m, IsLocalZeta30ConvergentAbove p μ (transl ℚ p W g x) χ g σ₀ := by
    intro x hx
    have hmemT : transl ℚ p W g x ∈ T := (Set.Finite.mem_toFinset _).mpr ⟨x, hx, rfl⟩
    have hmem : transl ℚ p W g x ∈ gl3CyclicSubspace W := transl_mem_gl3CyclicSubspace W g x
    refine isLocalZeta30ConvergentAbove_mono (hσg _ hmem) ?_
    calc σg (transl ℚ p W g x) ≤ |σg (transl ℚ p W g x)| := le_abs_self _
      _ ≤ ∑ f ∈ T, |σg f| := Finset.single_le_sum (fun f _ => abs_nonneg (σg f)) hmemT
      _ ≤ σ₀ := le_max_right _ _
  refine ⟨Q₁, Q₂, k, σ₀, σ₁, hQ₂, ?_, ?_, ?_, ?_⟩
  · exact isLocalZeta31ConvergentAbove_of_transl_ball hR hWs μ ν χ σ₀ hσ₀_transl
  · intro s hs
    rw [localZeta31_eq_localZeta30_avg hR μ ν χ s]
    exact he0 s (lt_of_le_of_lt (le_max_left _ _) hs)
  · exact isLocalZeta30ConvergentAbove_dual_of_avg hψn hψn' hW hR μ ν χ σ₁ hc1
  · intro s hs
    have h1 := he1 s hs
    rw [localZetaDual31_avg_eq hψn hψn' hW hR μ ν χ (1 - s), measureReal_ball_mul_measureReal_ball] at h1
    have hball : ball ℚ p 0 = {x : p.adicCompletion ℚ | Valued.v x ≤ 1} := by
      ext x; rw [mem_ball, WithZero.exp_zero]; rfl
    have hcast : ((((Ideal.absNorm p.asIdeal : ℝ) ^ n * ν.real (ball ℚ p 0) ^ 2 : ℝ)) : ℂ) =
        (Ideal.absNorm p.asIdeal : ℂ) ^ n *
          ((ν.real {x : p.adicCompletion ℚ | Valued.v x ≤ 1} : ℝ) : ℂ) ^ 2 := by
      rw [hball]; push_cast; ring
    rw [hcast] at h1
    exact h1

end
end S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_localZeta31_fe_of_forall_mem_gl3CyclicSubspace_exists_localZeta30_localZetaDual31_fe (solution)
