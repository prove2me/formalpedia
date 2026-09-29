-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1d0a0fbe-223e-5ac0-afa3-c777cc51d874

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Theorems.Thm_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace KcBruhatInt

section LocalField

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem modulus_units_ne_zero (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (modulus (u : F) : ℝ≥0) ≠ 0 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]
  exact nnnorm_ne_zero_iff.mpr u.ne_zero

theorem norm_units_pos (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : 0 < ‖(u : F)‖ :=
  norm_pos_iff.mpr u.ne_zero

scoped instance secondCountable_units : SecondCountableTopology (HeightOneSpectrum.adicCompletion ℚ p)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

theorem borelSpace_units {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
    [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ := by
  refine ⟨?_⟩
  have hind : (inferInstance : TopologicalSpace G₀ˣ) = TopologicalSpace.induced Units.val inferInstance :=
    (Units.isEmbedding_val₀ (G₀ := G₀)).eq_induced
  show MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace G₀) = borel G₀ˣ
  rw [BorelSpace.measurable_eq (α := G₀), ← borel_comap, ← hind]

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

variable [MeasurableSpace (HeightOneSpectrum.adicCompletion ℚ p)] [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)]

theorem map_mul_left_eq_smul (ν : Measure F) [ν.IsAddHaarMeasure] (u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ν.map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) • s := by
    rw [smul_set_eq_preimage (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) • s : Set F) =
      ((u⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

omit [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)] in

theorem measurable_inv_modulus [BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ] :
    Measurable fun u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((modulus (u : F) : ℝ≥0))⁻¹ := by
  have h : (fun u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => ((modulus (u : F) : ℝ≥0))⁻¹) =
      fun u : (HeightOneSpectrum.adicCompletion ℚ p)ˣ => (‖(u : F)‖₊)⁻¹ := by
    funext u
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]
  rw [h]
  refine ((continuous_nnnorm.comp Units.continuous_val).inv₀ fun u => ?_).measurable
  exact nnnorm_ne_zero_iff.mpr u.ne_zero

end LocalField

section MatrixAlgebra

variable {A : Type*} [CommRing A]

theorem iotaGL_lowerUnipotentGL2 (x : A) : iotaGL (lowerUnipotentGL2 x) = lowerUnipotent21 x := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerUnipotentGL2_coe]

theorem lower_torus (x : A) (d a : Aˣ) :
    lowerUnipotent21 x * iotaGL (diagUnits2 d a) =
      iotaGL (diagUnits2 d a) * lowerUnipotent21 (x * d * ((a⁻¹ : Aˣ) : A)) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, embedMat2]
  all_goals (rw [mul_comm ((a : Aˣ) : A), mul_assoc, Units.inv_mul, mul_one])

theorem torus_lower (x : A) (d a : Aˣ) :
    iotaGL (diagUnits2 d a) * lowerUnipotent21 x =
      iotaGL (diagUnitGL2 d) * lowerUnipotent21 ((a : A) * x) * iotaGL (diagUnits2 1 a) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, embedMat2]

theorem cell_iota (x y : A) (d a : Aˣ) :
    lowerUnipotent21 x * iotaGL (diagUnits2 d a) * iotaGL (unipotentGL2 y) =
      iotaGL (diagUnitGL2 d) * lowerUnipotent21 ((d : A) * x) * iotaGL (diagUnits2 1 a * unipotentGL2 y) := by
  rw [lower_torus, torus_lower, map_mul]
  have hx : (a : A) * (x * d * ((a⁻¹ : Aˣ) : A)) = (d : A) * x := by
    calc (a : A) * (x * d * ((a⁻¹ : Aˣ) : A)) = ((a : A) * ((a⁻¹ : Aˣ) : A)) * ((d : A) * x) := by ring
      _ = (d : A) * x := by rw [Units.mul_inv, one_mul]
  rw [hx]
  simp only [mul_assoc]

theorem det_cell (x y : A) (d a : Aˣ) :
    Matrix.GeneralLinearGroup.det (lowerUnipotentGL2 x * diagUnits2 d a * unipotentGL2 y) = d * a := by
  refine Units.ext ?_
  simp [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, lowerUnipotentGL2_coe, unipotentGL2_coe,
    Matrix.det_fin_two_of]

end MatrixAlgebra

section MatrixAlgebraLocal

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem upperUnipotent2_eq (x : F) : upperUnipotent2 p x = (unipotentGL2 x : G) :=
  Units.ext rfl

theorem diagonal2_eq (a d : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : diagonal2 p ![a, d] = (diagUnits2 a d : G) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal2, coe_diagUnits2]

theorem weyl_cell (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (x y : F) (d a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    w₀ * (lowerUnipotentGL2 x * diagUnits2 d a * unipotentGL2 y) =
      upperUnipotent2 p x * (diagonal2 p ![a, d] * (w₀ * unipotentGL2 y)) := by
  rw [upperUnipotent2_eq, diagonal2_eq]
  refine Units.ext ?_
  simp only [Units.val_mul, hw₀, lowerUnipotentGL2_coe, unipotentGL2_coe, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem torusChar2_pair (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    (a d : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    torusChar2 p χ ![a, d] = ((χ 0 a : ℂˣ) : ℂ) * ((χ 1 d : ℂˣ) : ℂ) := by
  simp [torusChar2, Fin.prod_univ_two]

theorem halfModulus2_pair (a d : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    halfModulus2 p ![a, d] = ((Real.sqrt (‖(a : F)‖ / ‖(d : F)‖) : ℝ) : ℂ) := by
  simp [halfModulus2]

end MatrixAlgebraLocal

section Scalars

theorem scalar_identity (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (s : ℂ) :
    ((Real.sqrt (r / t) : ℝ) : ℂ) * ((t * r : ℝ) : ℂ) ^ (s - 1 / 2) * ((r : ℝ) : ℂ)⁻¹ =
      ((r : ℝ) : ℂ) ^ (s - 1) * ((t : ℝ) : ℂ) ^ (s - 1) := by
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have htr0 : ((t * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos ht hr).ne'
  have e1 : ((Real.sqrt (r / t) : ℝ) : ℂ) = Complex.exp ((((Real.log r - Real.log t) / 2 : ℝ)) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hr ht), Real.log_div hr.ne' ht.ne', Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have e2 : ((t * r : ℝ) : ℂ) ^ (s - 1 / 2) = Complex.exp (((Real.log t + Real.log r : ℝ) : ℂ) * (s - 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero htr0, ← Complex.ofReal_log (mul_pos ht hr).le, Real.log_mul ht.ne' hr.ne']
  have e3 : ((r : ℝ) : ℂ)⁻¹ = Complex.exp (((-Real.log r : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_inv, show r⁻¹ = Real.exp (-Real.log r) by rw [Real.exp_neg, Real.exp_log hr],
      Complex.ofReal_exp]
  have e4 : ((r : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero hr0, ← Complex.ofReal_log hr.le]
  have e5 : ((t : ℝ) : ℂ) ^ (s - 1) = Complex.exp (((Real.log t : ℝ) : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
  rw [e1, e2, e3, e4, e5, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Scalars

section Cell

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace (HeightOneSpectrum.adicCompletion ℚ p)ˣ := borelSpace_units

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

theorem continuous_lowerUnipotentGL2 : Continuous fun x : F => (lowerUnipotentGL2 x : G) := by
  rw [Units.continuous_iff]
  constructor
  · have h : (Units.val ∘ fun x : F => (lowerUnipotentGL2 x : G)) = fun x => !![1, 0; x, 1] := funext fun x => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_id
  · have h : (fun x : F => (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat)) = fun x => !![1, 0; -x, 1] :=
      funext fun x => rfl
    show Continuous fun x : F => (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact continuous_neg

theorem continuous_diagUnits2 :
    Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      (diagUnits2 da.1 da.2 : G) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((da.1 : F)) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((da.2 : F)) := Units.continuous_val.comp continuous_snd
  have h1' : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((da.1 : F))⁻¹ := by
    have := (Units.continuous_coe_inv (M := F)).comp
      (continuous_fst : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ ×
        (HeightOneSpectrum.adicCompletion ℚ p)ˣ => da.1)
    refine this.congr fun da => ?_
    simp [Function.comp_apply, Units.val_inv_eq_inv_val]
  have h2' : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
      ((da.2 : F))⁻¹ := by
    have := (Units.continuous_coe_inv (M := F)).comp
      (continuous_snd : Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ ×
        (HeightOneSpectrum.adicCompletion ℚ p)ˣ => da.2)
    refine this.congr fun da => ?_
    simp [Function.comp_apply, Units.val_inv_eq_inv_val]
  constructor
  · have h : (Units.val ∘ fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (diagUnits2 da.1 da.2 : G)) = fun da => !![(da.1 : F), 0; 0, (da.2 : F)] := funext fun da => rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h1 | exact h2
  · have h : (fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (((diagUnits2 da.1 da.2 : G)⁻¹ : G) : Mat)) =
        fun da => !![((da.1 : F))⁻¹, 0; 0, ((da.2 : F))⁻¹] := by
      funext da
      change !![(((da.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F), 0;
          0, (((da.2)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)] = _
      simp [Units.val_inv_eq_inv_val]
    show Continuous fun da : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ =>
        (((diagUnits2 da.1 da.2 : G)⁻¹ : G) : Mat)
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact h1' | exact h2'

def cellMap (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) : G :=
  lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1

theorem continuous_cellMap : Continuous (cellMap p) := by
  have hx : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      q.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hd : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      q.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have ha : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      q.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      q.1 := continuous_fst
  have hL : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      (lowerUnipotentGL2 q.2.2.2 : G) := (continuous_lowerUnipotentGL2 p).comp hx
  have hD : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      (diagUnits2 q.2.2.1 q.2.1 : G) := (continuous_diagUnits2 p).comp (hd.prodMk ha)
  have hU : Continuous fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      (unipotentGL2 q.1 : G) := (continuous_unipotentGL2 p).comp hy
  exact (hL.mul hD).mul hU

def cellWeight (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) : ℝ≥0 :=
  modulus (((q.2.2.1 * (q.2.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F)

theorem measurable_cellWeight : Measurable (cellWeight p) := by
  have h : cellWeight p = fun q => ‖(((q.2.2.1 * (q.2.1)⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F)‖₊ := by
    funext q
    exact LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p _
  rw [h]
  refine (continuous_nnnorm.comp (Units.continuous_val.comp ?_)).measurable
  exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).mul (continuous_fst.comp continuous_snd).inv

def invWeight (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) : ℝ≥0 :=
  ((modulus ((q.2.2.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹

theorem measurable_invWeight : Measurable (invWeight p) :=
  (measurable_inv_modulus (p := p)).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))

def scaleHomeo : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F ≃ₜ (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F where
  toFun q := (q.1, (q.1 : F) * q.2)
  invFun q := (q.1, ((q.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * q.2)
  left_inv q := by
    show (q.1, ((q.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * ((q.1 : F) * q.2)) = q
    rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv q := by
    show (q.1, (q.1 : F) * (((q.1⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * q.2)) = q
    rw [← mul_assoc, Units.mul_inv, one_mul]
  continuous_toFun := continuous_fst.prodMk ((Units.continuous_val.comp continuous_fst).mul continuous_snd)
  continuous_invFun := by
    refine continuous_fst.prodMk (Continuous.mul ?_ continuous_snd)
    exact Units.continuous_val.comp (continuous_inv.comp continuous_fst)

theorem scaleHomeo_apply (q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :
    scaleHomeo p q = (q.1, (q.1 : F) * q.2) := rfl

theorem map_scale (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [SFinite τ] (ν : Measure F) [ν.IsAddHaarMeasure] :
    Measure.map (scaleHomeo p) (τ.prod ν) =
      (τ.prod ν).withDensity
        (fun q => ((((modulus ((q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞)) := by
  have hmeas : Measurable (scaleHomeo p) := (scaleHomeo p).continuous.measurable
  have hδ : Measurable fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      ((((modulus ((q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ((measurable_inv_modulus (p := p)).comp measurable_fst).coe_nnreal_ennreal
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hmeas hA, Measure.prod_apply (hmeas hA), withDensity_apply _ hA, ← lintegral_indicator hA,
    lintegral_prod _ (hδ.indicator hA).aemeasurable]
  refine lintegral_congr fun d => ?_
  have hAd : MeasurableSet (Prod.mk d ⁻¹' A) := measurable_prodMk_left hA
  have h1 : Prod.mk d ⁻¹' ((scaleHomeo p) ⁻¹' A) = (fun x : F => (d : F) * x) ⁻¹' (Prod.mk d ⁻¹' A) := rfl
  rw [h1, ← Measure.map_apply (measurable_const_mul _) hAd, map_mul_left_eq_smul ν d, Measure.smul_apply,
    smul_eq_mul]
  have h2 : (fun x : F => A.indicator (fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      ((((modulus ((q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞)) (d, x)) =
      (Prod.mk d ⁻¹' A).indicator (fun _ => ((((modulus (d : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞)) := by
    funext x
    by_cases hx : (d, x) ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ Prod.mk d ⁻¹' A from hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ Prod.mk d ⁻¹' A from hx)]
  rw [h2, lintegral_indicator_const hAd, ENNReal.coe_inv (modulus_units_ne_zero d)]

def liftEquiv : (F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) ≃ᵐ
    (F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl F)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (HeightOneSpectrum.adicCompletion ℚ p)ˣ)
      (scaleHomeo p).toMeasurableEquiv)

theorem liftEquiv_apply (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :
    liftEquiv p q = (q.1, q.2.1, q.2.2.1, ((q.2.2.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * q.2.2.2) := rfl

theorem coe_liftEquiv :
    (liftEquiv p : (F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) →
        (F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F)) =
      Prod.map id (Prod.map id (scaleHomeo p)) := rfl

theorem map_liftEquiv (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [SFinite τ] (ν : Measure F) [ν.IsAddHaarMeasure] :
    Measure.map (liftEquiv p) (ν.prod (τ.prod (τ.prod ν))) =
      (ν.prod (τ.prod (τ.prod ν))).withDensity fun q => (invWeight p q : ℝ≥0∞) := by
  have hsc : Measurable (scaleHomeo p) := (scaleHomeo p).continuous.measurable
  have hδ₂ : Measurable fun q : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      ((((modulus ((q.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    ((measurable_inv_modulus (p := p)).comp measurable_fst).coe_nnreal_ennreal
  rw [coe_liftEquiv, ← Measure.map_prod_map ν (τ.prod (τ.prod ν)) measurable_id (measurable_id.prodMap hsc),
    Measure.map_id, ← Measure.map_prod_map τ (τ.prod ν) measurable_id hsc, Measure.map_id, map_scale p τ ν,
    prod_withDensity_right hδ₂]
  have hδ₃ : Measurable fun z : (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
      ((((modulus ((z.2.1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    hδ₂.comp measurable_snd
  rw [prod_withDensity_right hδ₃]
  rfl

end Cell

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def phiFn (V : G₃ → ℂ) (f : G → ℂ) (w₀ : G) (s : ℂ) (g : G) : ℂ :=
  (V (iotaGL g) * f (w₀ * g)) *
    ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) ^ (s - 1 / 2)

def cellScalar (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (f : G → ℂ) (w₀ : G) (s : ℂ)
    (y : F) (t a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : ℂ :=
  ((((modulus (((a * t⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) : ℝ≥0) : ℝ)) : ℂ) *
    (((χ 0 t : ℂˣ) : ℂ) * ((χ 1 a : ℂˣ) : ℂ) * ((Real.sqrt (‖(t : F)‖ / ‖(a : F)‖) : ℝ) : ℂ) *
      f (w₀ * unipotentGL2 y)) *
    ((modulus (((a * t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) : ℝ) : ℂ) ^ (s - 1 / 2)

def postFn (V : G₃ → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (f : G → ℂ) (w₀ : G) (s : ℂ)
    (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) : ℂ :=
  cellScalar p χ f w₀ s q.1 q.2.1 q.2.2.1 *
    V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1))

theorem cellWeight_smul_phiFn (V : G₃ → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    (f : G → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (s : ℂ)
    (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :
    cellWeight p q • phiFn p V f w₀ s (cellMap p q) = postFn p V χ f w₀ s (liftEquiv p q) := by
  obtain ⟨-, hfN, hfT⟩ := mem_principalSeries2_iff.mp hf
  obtain ⟨y, t, a, x⟩ := q
  rw [NNReal.smul_def, Complex.real_smul, liftEquiv_apply]
  simp only [phiFn, postFn, cellScalar, cellMap, cellWeight]
  rw [weyl_cell w₀ hw₀, hfN, hfT, torusChar2_pair, halfModulus2_pair, det_cell, map_mul, map_mul,
    iotaGL_lowerUnipotentGL2, cell_iota]
  ring

theorem invWeight_smul_postFn (V : G₃ → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    (f : G → ℂ) (w₀ : G) (s : ℂ)
    (q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :
    invWeight p q • postFn p V χ f w₀ s q =
      f (w₀ * unipotentGL2 q.1) *
        (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : F) : ℝ) : ℂ) ^ (s - 1)) *
        (V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
          ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : F) : ℝ) : ℂ) ^ (s - 1)) := by
  obtain ⟨y, t, a, x⟩ := q
  rw [NNReal.smul_def, Complex.real_smul]
  simp only [postFn, cellScalar, invWeight]
  have hma : ((modulus (a : F) : ℝ≥0) : ℝ) = ‖(a : F)‖ := coe_modulus_eq_norm _
  have hmt : ((modulus (t : F) : ℝ≥0) : ℝ) = ‖(t : F)‖ := coe_modulus_eq_norm _
  have hmat : ((modulus (((a * t : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) : ℝ≥0) : ℝ) =
      ‖(a : F)‖ * ‖(t : F)‖ := by
    rw [coe_modulus_eq_norm, Units.val_mul, norm_mul]
  have hmat' : ((modulus (((a * t⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) : ℝ≥0) : ℝ) =
      ‖(a : F)‖ * ‖(t : F)‖⁻¹ := by
    rw [coe_modulus_eq_norm, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv]
  have hinv : (((((modulus (a : F) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) : ℂ) = ((‖(a : F)‖ : ℝ) : ℂ)⁻¹ := by
    rw [NNReal.coe_inv, hma, Complex.ofReal_inv]
  rw [hinv, hma, hmt, hmat, hmat']
  have ha0 : ((‖(a : F)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_units_pos a).ne'
  have ht0 : ((‖(t : F)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_units_pos t).ne'
  have key := scalar_identity ‖(t : F)‖ ‖(a : F)‖ (norm_units_pos t) (norm_units_pos a) s
  have hu1 : ((‖(a : F)‖ : ℝ) : ℂ)⁻¹ * ((‖(a : F)‖ * ‖(t : F)‖⁻¹ : ℝ) : ℂ) = ((‖(t : F)‖ : ℝ) : ℂ)⁻¹ := by
    push_cast
    field_simp
  set Vv := V (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * iotaGL (diagUnits2 1 t * unipotentGL2 y))
  set fy := f (w₀ * unipotentGL2 y)
  calc ((‖(a : F)‖ : ℝ) : ℂ)⁻¹ *
        ((((‖(a : F)‖ * ‖(t : F)‖⁻¹ : ℝ) : ℂ)) *
            (((χ 0 t : ℂˣ) : ℂ) * ((χ 1 a : ℂˣ) : ℂ) * ((Real.sqrt (‖(t : F)‖ / ‖(a : F)‖) : ℝ) : ℂ) * fy) *
            (((‖(a : F)‖ * ‖(t : F)‖ : ℝ)) : ℂ) ^ (s - 1 / 2) * Vv)
        = (((χ 0 t : ℂˣ) : ℂ) * ((χ 1 a : ℂˣ) : ℂ) * fy * Vv) *
            ((((‖(a : F)‖ : ℝ) : ℂ)⁻¹ * ((‖(a : F)‖ * ‖(t : F)‖⁻¹ : ℝ) : ℂ)) *
              (((Real.sqrt (‖(t : F)‖ / ‖(a : F)‖) : ℝ) : ℂ) * (((‖(a : F)‖ * ‖(t : F)‖ : ℝ)) : ℂ) ^ (s - 1 / 2))) := by
          ring
    _ = (((χ 0 t : ℂˣ) : ℂ) * ((χ 1 a : ℂˣ) : ℂ) * fy * Vv) *
            (((Real.sqrt (‖(t : F)‖ / ‖(a : F)‖) : ℝ) : ℂ) * (((‖(a : F)‖ * ‖(t : F)‖ : ℝ)) : ℂ) ^ (s - 1 / 2) *
              ((‖(t : F)‖ : ℝ) : ℂ)⁻¹) := by
          rw [hu1]; ring
    _ = (((χ 0 t : ℂˣ) : ℂ) * ((χ 1 a : ℂˣ) : ℂ) * fy * Vv) *
            (((‖(t : F)‖ : ℝ) : ℂ) ^ (s - 1) * ((‖(a : F)‖ : ℝ) : ℂ) ^ (s - 1)) := by rw [key]
    _ = _ := by ring

theorem main (V : G₃ → ℂ) (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    (f : G → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : G) (hw₀ : (w₀ : Mat) = !![0, 1; 1, 0]) (s : ℂ)
    (μ₂ : Measure G) [μ₂.IsHaarMeasure]
    (τ : Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ) [τ.IsHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure]
    (hΦ : Integrable (phiFn p V f w₀ s) μ₂) :
    Integrable (fun q : F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F =>
        f (w₀ * unipotentGL2 q.1) *
          (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : F) : ℝ) : ℂ) ^ (s - 1)) *
          (V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 * iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
            ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : F) : ℝ) : ℂ) ^ (s - 1)))
      (ν.prod (τ.prod (τ.prod ν))) := by

  obtain ⟨c, hc0, hctop, hμ₂⟩ :=
    AutomorphicForm.exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2 ℚ p μ₂ τ ν
  set ρ : Measure (F × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × (HeightOneSpectrum.adicCompletion ℚ p)ˣ × F) :=
    ν.prod (τ.prod (τ.prod ν)) with hρ
  have hΘm : Measurable (cellMap p) := (continuous_cellMap p).measurable
  have hJm : Measurable (cellWeight p) := measurable_cellWeight p
  have hμ₂' : μ₂ = c • Measure.map (cellMap p) (ρ.withDensity fun q => (cellWeight p q : ℝ≥0∞)) := hμ₂
  have h1 : Integrable (phiFn p V f w₀ s) (c • Measure.map (cellMap p) (ρ.withDensity fun q => (cellWeight p q : ℝ≥0∞))) := by
    rw [← hμ₂']
    exact hΦ
  have h2 := (integrable_smul_measure hc0 hctop).mp h1
  have h3 : Integrable (phiFn p V f w₀ s ∘ cellMap p) (ρ.withDensity fun q => (cellWeight p q : ℝ≥0∞)) :=
    h2.comp_measurable hΘm
  have h4 : Integrable (fun q => cellWeight p q • phiFn p V f w₀ s (cellMap p q)) ρ :=
    (integrable_withDensity_iff_integrable_smul hJm).mp h3

  have h5 : Integrable (postFn p V χ f w₀ s ∘ liftEquiv p) ρ := by
    refine h4.congr (Filter.Eventually.of_forall fun q => ?_)
    exact cellWeight_smul_phiFn p V χ f hf w₀ hw₀ s q

  have h6 : Integrable (postFn p V χ f w₀ s) (Measure.map (liftEquiv p) ρ) :=
    (integrable_map_equiv (liftEquiv p) _).mpr h5
  rw [hρ, map_liftEquiv p τ ν] at h6
  have h7 : Integrable (fun q => invWeight p q • postFn p V χ f w₀ s q) (ν.prod (τ.prod (τ.prod ν))) :=
    (integrable_withDensity_iff_integrable_smul (measurable_invWeight p)).mp h6
  refine h7.congr (Filter.Eventually.of_forall fun q => ?_)
  exact invWeight_smul_postFn p V χ f w₀ s q

end Main

end KcBruhatInt
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2.KcBruhatInt"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2.KcBruhatInt"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : LocalGL3 p → ℂ)
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (s : ℂ) :
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (τ : Measure (p.adicCompletion ℚ)ˣ) [τ.IsHaarMeasure]
      (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (V (iotaGL g) * f (w₀p * g)) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
              (s - 1 / 2)) μ₂ →
      Integrable (fun q : p.adicCompletion ℚ × (p.adicCompletion ℚ)ˣ × (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
          f (w₀p * unipotentGL2 q.1) *
            (((χ 0 q.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) *
            (V (iotaGL (diagUnitGL2 q.2.2.1) * lowerUnipotent21 q.2.2.2 *
                  iotaGL (diagUnits2 1 q.2.1 * unipotentGL2 q.1)) *
              ((χ 1 q.2.2.1 : ℂˣ) : ℂ) * ((modulus (q.2.2.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)))
        (ν.prod (τ.prod (τ.prod ν))) := by
  intro μ₂ _ τ _ ν _ hΦ
  exact KcBruhatInt.main p V χ f hf w₀p hw₀p s μ₂ τ ν hΦ

end S_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integrable_principalSeries2_mul_whittaker_iotaGL_diagUnitGL2_mul_lowerUnipotent21_of_integrable_whittaker_iotaGL_mul_principalSeries2 (solution)
