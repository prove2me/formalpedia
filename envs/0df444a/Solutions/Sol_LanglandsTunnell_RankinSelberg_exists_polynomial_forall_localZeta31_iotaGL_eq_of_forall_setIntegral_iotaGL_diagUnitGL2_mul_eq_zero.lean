-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f695ad1b-3cd0-5cf3-a3db-8accd1d1dd34

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory Filter Topology
open scoped NNReal ENNReal Matrix Pointwise

noncomputable section

namespace KcR3Sharp

open LanglandsTunnell.CubicInduction

section Algebra

variable {A : Type*} [CommRing A]

theorem iotaGL_mul_lowerUnipotent21_mul_upperUnipotent3 (a : Aˣ) (x y : A) :
    (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) * lowerUnipotent21 x * upperUnipotent3 0 0 y =
      upperUnipotent3 0 (x * y) ((a : A) * y) * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, lowerUnipotent21_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

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

def lowerTwo (x : A) : GL (Fin 2) A where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem iotaGL_lowerTwo (x : A) : (iotaGL (lowerTwo x) : GL (Fin 3) A) = lowerUnipotent21 x := by
  refine Units.ext ?_
  rw [coe_iotaGL, lowerUnipotent21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerTwo]

theorem iotaGL_diag_mul_conj (a : Aˣ) (x : A) (h : GL (Fin 2) A) :
    (iotaGL (diagUnitGL2 a) : GL (Fin 3) A) * iotaGL h * ((iotaGL h)⁻¹ * lowerUnipotent21 x * iotaGL h) =
      iotaGL (diagUnitGL2 a * (lowerTwo x * h)) := by
  rw [map_mul, map_mul, iotaGL_lowerTwo]
  group

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
  let g : (WithZero (Multiplicative ℤ))ˣ := Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass vv)) γ
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

end AdicBalls

section Smooth

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

def IsSmooth3 (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ U : Subgroup (GL (Fin 3) F), IsOpen (U : Set (GL (Fin 3) F)) ∧ ∀ k ∈ U, ∀ g : GL (Fin 3) F, W (g * k) = W g

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

variable {W : LocalGL3 v → ℂ} {h : LocalGL3 v} {m : ℤ}

def SupportRadius (W : LocalGL3 v → ℂ) (h : LocalGL3 v) (m : ℤ) : Prop :=
  ∀ (a : (v.adicCompletion ℚ)ˣ) (x : v.adicCompletion ℚ), x ∉ ball ℚ v m →
    W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = 0

theorem inner_primal (hR : SupportRadius W h m) (ν : Measure (v.adicCompletion ℚ)) (a : (v.adicCompletion ℚ)ˣ) :
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
  · rw [Set.indicator_of_notMem hx, zero_mul, hR a x hx]

theorem localZeta31_eq_localZeta30_avg (hR : SupportRadius W h m)
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

theorem localZeta30_avg_eq_sum (hWs : IsSmooth3 W)
    (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ)
    (hint : ∀ f ∈ (finite_image_transl hWs h m).toFinset,
      Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
        f (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ) :
    localZeta30 v μ (avg ℚ v ν W h m) χ s h =
      ∑ f ∈ (finite_image_transl hWs h m).toFinset,
        (ν.real (piece W h m f) : ℂ) * localZeta30 v μ f χ s h := by
  unfold localZeta30
  have heq : (fun a : (v.adicCompletion ℚ)ˣ =>
      avg ℚ v ν W h m (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a => ∑ f ∈ (finite_image_transl hWs h m).toFinset,
        (ν.real (piece W h m f) : ℂ) * (f (iotaGL (diagUnitGL2 a) * h) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    funext a
    rw [avg_apply_eq_sum ν hWs h m, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  rw [heq, integral_finsetSum _ (fun f hf => (hint f hf).const_mul _)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_const_mul]

theorem isLocalZeta31ConvergentAbove_of_transl_ball (hR : SupportRadius W h m) (hWs : IsSmooth3 W)
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
    · rw [sum_indicator_piece_mul_eq_zero hWs h m (fun f => G f p.1) hx, hR p.1 p.2 hx, zero_mul,
        zero_mul]
  rw [heq]
  refine integrable_finsetSum _ fun f hf => ?_
  obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
  refine Integrable.mul_prod (hconv x hx s hs) ?_
  exact (integrableOn_const (measure_piece_lt_top ν W h m _).ne).integrable_indicator
    (measurableSet_piece hWs h m _)

theorem isLocalZeta30ConvergentAbove_mono {μ : Measure (v.adicCompletion ℚ)ˣ} {W : LocalGL3 v → ℂ}
    {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {g : LocalGL3 v} {σ σ' : ℝ}
    (h : IsLocalZeta30ConvergentAbove v μ W χ g σ) (hle : σ ≤ σ') :
    IsLocalZeta30ConvergentAbove v μ W χ g σ' :=
  fun s hs => h s (lt_of_le_of_lt hle hs)

end Transfer

section Laurent

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev qC : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

theorem qC_ne_zero : qC v ≠ 0 := by
  exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)

theorem laurent_sum_pack {ι : Type*} (T : Finset ι) (c : ι → ℂ) (mf : ι → ℤ) (Pf : ι → Polynomial ℂ) :
    ∃ (P : Polynomial ℂ) (M : ℤ), ∀ s : ℂ,
      ∑ i ∈ T, c i * (qC v ^ ((mf i : ℂ) * s) * (Pf i).eval (qC v ^ (-s))) =
        qC v ^ ((M : ℂ) * s) * P.eval (qC v ^ (-s)) := by
  classical
  set M : ℤ := ∑ i ∈ T, |mf i| with hM
  have hnm : ∀ i ∈ T, 0 ≤ M - mf i := by
    intro i hi
    have h1 : |mf i| ≤ M := by
      rw [hM]; exact Finset.single_le_sum (fun j _ => abs_nonneg (mf j)) hi
    have h2 : mf i ≤ |mf i| := le_abs_self _
    omega
  refine ⟨∑ i ∈ T, Polynomial.C (c i) * Polynomial.X ^ (M - mf i).toNat * Pf i, M, fun s => ?_⟩
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← Complex.cpow_nat_mul,
    show (((M - mf i).toNat : ℕ) : ℂ) = ((M - mf i : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hnm i hi)]]
  have hq := qC_ne_zero v
  rw [show qC v ^ ((M : ℂ) * s) * (c i * qC v ^ (((M - mf i : ℤ) : ℂ) * -s) * (Pf i).eval (qC v ^ (-s))) =
      c i * ((qC v ^ ((M : ℂ) * s) * qC v ^ (((M - mf i : ℤ) : ℂ) * -s)) * (Pf i).eval (qC v ^ (-s))) by ring,
    ← Complex.cpow_add _ _ hq]
  congr 3
  push_cast
  ring

end Laurent

end KcR3Sharp

end

open LanglandsTunnell.CubicInduction KcR3Sharp

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (θ : AddChar (p.adicCompletion ℚ) ℂ) (hθ : ∃ x : p.adicCompletion ℚ, θ x ≠ 1)
    (W : LocalGL3 p → ℂ) (hW : IsGL3PsiWhittakerFn θ W)
    (hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (h : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ∀ (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],

      (∀ h' : GL (Fin 2) (p.adicCompletion ℚ), ∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
          W (iotaGL (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
            ^ n * u) * h')) * ((χ u : ℂˣ) : ℂ) ∂τ = 0) →

      (∀ W' ∈ gl3CyclicSubspace W, ∃ σ₀ : ℝ, IsLocalZeta30ConvergentAbove p τ W' χ (iotaGL h) σ₀) →
      ∃ (P : Polynomial ℂ) (m : ℤ) (σ₁ : ℝ),
        IsLocalZeta31ConvergentAbove p τ ν W χ (iotaGL h) σ₁ ∧
        ∀ s : ℂ, σ₁ < s.re →
          localZeta31 p τ ν W χ s (iotaGL h) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
  intro τ _ ν _ hTF hconv
  classical
  have hWs : IsSmooth3 W := hWsm
  obtain ⟨U, hU, hWU⟩ := id hWsm
  set g : LocalGL3 p := iotaGL h with hg

  obtain ⟨m, hm⟩ := exists_forall_apply_lowerUnipotent21_eq_zero hθ hW U hU hWU g
  have hR : SupportRadius W g m := fun a x hx => hm a x (not_le.mp hx)

  choose! σg hσg using hconv
  set T := (finite_image_transl hWs g m).toFinset with hT
  set σ₁ : ℝ := ∑ f ∈ T, |σg f| with hσ₁
  have hσ₁T : ∀ f ∈ T, IsLocalZeta30ConvergentAbove p τ f χ g σ₁ := by
    intro f hf
    obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
    refine isLocalZeta30ConvergentAbove_mono (hσg _ (transl_mem_gl3CyclicSubspace W g x)) ?_
    calc σg (transl ℚ p W g x) ≤ |σg (transl ℚ p W g x)| := le_abs_self _
      _ ≤ σ₁ := Finset.single_le_sum (fun f _ => abs_nonneg (σg f)) hf
  have hσ₁ball : ∀ x ∈ ball ℚ p m, IsLocalZeta30ConvergentAbove p τ (transl ℚ p W g x) χ g σ₁ :=
    fun x hx => hσ₁T _ ((Set.Finite.mem_toFinset _).mpr ⟨x, hx, rfl⟩)

  have hLaur : ∀ f ∈ T, ∃ (P : Polynomial ℂ) (mf : ℤ), ∀ s : ℂ, σ₁ < s.re →
      localZeta30 p τ f χ s g =
        (Ideal.absNorm p.asIdeal : ℂ) ^ ((mf : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) := by
    intro f hf
    have hconvf := hσ₁T f hf
    obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).mp hf
    have hpt : ∀ (a : (p.adicCompletion ℚ)ˣ) (s : ℂ),
        transl ℚ p W g x (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
            ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
          (fun k : GL (Fin 2) (p.adicCompletion ℚ) => W (iotaGL k)) (diagUnitGL2 a * (lowerTwo x * h)) *
            ((χ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) := by
      intro a s
      rw [transl_apply, hg, iotaGL_diag_mul_conj]
    have hint : ∀ s : ℂ, σ₁ < s.re →
        Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
          (fun k : GL (Fin 2) (p.adicCompletion ℚ) => W (iotaGL k)) (diagUnitGL2 a * (lowerTwo x * h)) *
            ((χ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) τ := by
      intro s hs
      exact (hconvf s hs).congr (Filter.Eventually.of_forall fun a => hpt a s)
    obtain ⟨P, mf, hP⟩ :=
      LanglandsTunnell.RankinSelberg.exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
        ℚ p hπ hϖ (fun k : GL (Fin 2) (p.adicCompletion ℚ) => W (iotaGL k)) χ (lowerTwo x * h) τ
        (hTF (lowerTwo x * h)) σ₁ hint
    refine ⟨P, mf, fun s hs => ?_⟩
    rw [← hP s hs]
    unfold localZeta30
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => hpt a s)
  choose! Pf mf hPf using hLaur
  obtain ⟨P, M, hPM⟩ := laurent_sum_pack p T (fun f => (ν.real (piece W g m f) : ℂ)) mf Pf
  refine ⟨P, M, σ₁, isLocalZeta31ConvergentAbove_of_transl_ball hR hWs τ ν χ σ₁ hσ₁ball, fun s hs => ?_⟩
  rw [localZeta31_eq_localZeta30_avg hR τ ν χ s,
    localZeta30_avg_eq_sum hWs τ ν χ s (fun f hf => hσ₁T f hf s hs), ← hPM s]
  exact Finset.sum_congr rfl fun f hf => by rw [hPf f hf s hs]

end S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_localZeta31_iotaGL_eq_of_forall_setIntegral_iotaGL_diagUnitGL2_mul_eq_zero (solution)
