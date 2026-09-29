-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fbc74aca-0543-5f12-bd42-42a6b75dad35

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
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B1aS1

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

def hz (h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 3) F :=
  Matrix.of fun i k => Fin.lastCases (0 : F) (fun k' : Fin 2 => (h : Matrix (Fin 2) (Fin 2) F) i k') k

def hcol (h : GL (Fin 2) F) (u : F × F) : Matrix (Fin 2) (Fin 3) F :=
  Matrix.of fun i k => Fin.lastCases (if i = 0 then u.1 else u.2) (fun k' : Fin 2 => (h : Matrix (Fin 2) (Fin 2) F) i k') k

def hmul (h : GL (Fin 2) F) (u : F × F) : F × F :=
  ((h : Matrix (Fin 2) (Fin 2) F) 0 0 * u.1 + (h : Matrix (Fin 2) (Fin 2) F) 0 1 * u.2,
   (h : Matrix (Fin 2) (Fin 2) F) 1 0 * u.1 + (h : Matrix (Fin 2) (Fin 2) F) 1 1 * u.2)

theorem hz_apply_castSucc (h : GL (Fin 2) F) (i k : Fin 2) :
    hz p h i (Fin.castSucc k) = (h : Matrix (Fin 2) (Fin 2) F) i k := by
  simp only [hz, Matrix.of_apply, Fin.lastCases_castSucc]

theorem hz_apply_last (h : GL (Fin 2) F) (i : Fin 2) : hz p h i (Fin.last 2) = 0 := by
  simp only [hz, Matrix.of_apply, Fin.lastCases_last]

theorem hz_apply_zero (h : GL (Fin 2) F) (i : Fin 2) : hz p h i 0 = (h : Matrix (Fin 2) (Fin 2) F) i 0 :=
  hz_apply_castSucc p h i 0

theorem hz_apply_one (h : GL (Fin 2) F) (i : Fin 2) : hz p h i 1 = (h : Matrix (Fin 2) (Fin 2) F) i 1 :=
  hz_apply_castSucc p h i 1

theorem hz_apply_two (h : GL (Fin 2) F) (i : Fin 2) : hz p h i 2 = 0 :=
  hz_apply_last p h i

theorem hcol_apply_castSucc (h : GL (Fin 2) F) (u : F × F) (i k : Fin 2) :
    hcol p h u i (Fin.castSucc k) = (h : Matrix (Fin 2) (Fin 2) F) i k := by
  simp only [hcol, Matrix.of_apply, Fin.lastCases_castSucc]

theorem hcol_apply_last (h : GL (Fin 2) F) (u : F × F) (i : Fin 2) :
    hcol p h u i (Fin.last 2) = if i = 0 then u.1 else u.2 := by
  simp only [hcol, Matrix.of_apply, Fin.lastCases_last]

theorem hcol_apply_zero (h : GL (Fin 2) F) (u : F × F) (i : Fin 2) : hcol p h u i 0 = (h : Matrix (Fin 2) (Fin 2) F) i 0 :=
  hcol_apply_castSucc p h u i 0

theorem hcol_apply_one (h : GL (Fin 2) F) (u : F × F) (i : Fin 2) : hcol p h u i 1 = (h : Matrix (Fin 2) (Fin 2) F) i 1 :=
  hcol_apply_castSucc p h u i 1

theorem hcol_apply_two (h : GL (Fin 2) F) (u : F × F) (i : Fin 2) : hcol p h u i 2 = if i = 0 then u.1 else u.2 :=
  hcol_apply_last p h u i

theorem godementArg_apply_zero (h : GL (Fin 2) F) (i : Fin 2) :
    godementArg p h i 0 = (h : Matrix (Fin 2) (Fin 2) F) i 0 :=
  godementArg_apply_castSucc p h i 0

theorem godementArg_apply_one (h : GL (Fin 2) F) (i : Fin 2) :
    godementArg p h i 1 = (h : Matrix (Fin 2) (Fin 2) F) i 1 :=
  godementArg_apply_castSucc p h i 1

theorem godementArg_apply_two (h : GL (Fin 2) F) (i : Fin 2) :
    godementArg p h i 2 = (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) F) i 1 :=
  godementArg_apply_last p h i

theorem coe_mul_upperUnipotent2 (h : GL (Fin 2) F) (x : F) (i : Fin 2) :
    (((h * upperUnipotent2 p x : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) i 0 = (h : Matrix (Fin 2) (Fin 2) F) i 0 ∧
    (((h * upperUnipotent2 p x : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) i 1 =
      (h : Matrix (Fin 2) (Fin 2) F) i 0 * x + (h : Matrix (Fin 2) (Fin 2) F) i 1 := by
  constructor <;> simp [Units.val_mul, upperUnipotent2_coe, Matrix.mul_apply, Fin.sum_univ_two]

theorem hz_mul_upperUnipotent3 (h : GL (Fin 2) F) (x y z : F) :
    hz p h * ((upperUnipotent3 x y z : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) =
      hcol p (h * upperUnipotent2 p x) (hmul p h (z, y)) := by
  ext i k
  rw [Matrix.mul_apply, Fin.sum_univ_three, hz_apply_zero, hz_apply_one, hz_apply_two, upperUnipotent3_coe]
  fin_cases k
  · simp [hcol_apply_zero, (coe_mul_upperUnipotent2 p h x i).1]
  · simp [hcol_apply_one, (coe_mul_upperUnipotent2 p h x i).2]
  · fin_cases i <;> simp [hcol_apply_two, hmul]

theorem hcol_eq_setCol23_godementArg (h : GL (Fin 2) F) (u : F × F) :
    hcol p h u = setCol23 p (godementArg p h) 2 u := by
  ext i k
  fin_cases k
  · simp [hcol_apply_zero, setCol23_apply, godementArg_apply_zero]
  · simp [hcol_apply_one, setCol23_apply, godementArg_apply_one]
  · simp [hcol_apply_two, setCol23_apply]

theorem hz_def (h : GL (Fin 2) F) :
    hz p h = (Matrix.of fun i k => Fin.lastCases (0 : F)
      (fun k' : Fin 2 => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i k') k : Matrix (Fin 2) (Fin 3) F) := rfl

theorem coe_inv_apply (h : GL (Fin 2) F) (i j : Fin 2) :
    ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = (transposeInvN (Fin 2) h : Matrix (Fin 2) (Fin 2) F) j i := by
  rw [coe_transposeInvN, Matrix.transpose_apply]

theorem hmul_inv_snd (h : GL (Fin 2) F) (u : F × F) :
    (hmul p h⁻¹ u).2 = u.1 * godementArg p h 0 2 + u.2 * godementArg p h 1 2 := by
  simp only [hmul, godementArg_apply_two, coe_inv_apply]
  ring

theorem det_upperUnipotent2 (x : F) : Matrix.GeneralLinearGroup.det (upperUnipotent2 p x) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent2_coe]
  simp [Matrix.det_fin_two_of]

theorem upperUnipotent2_neg_mul (x : F) : upperUnipotent2 p (-x) * upperUnipotent2 p x = 1 := by
  rw [upperUnipotent2_mul]
  simp [upperUnipotent2_zero]

theorem hmul_mul_upperUnipotent2_neg (h : GL (Fin 2) F) (x y z : F) :
    hmul p (h * upperUnipotent2 p (-x)) (z, y) = hmul p h (z - x * y, y) := by
  simp only [hmul, (coe_mul_upperUnipotent2 p h (-x) 0).1, (coe_mul_upperUnipotent2 p h (-x) 0).2,
    (coe_mul_upperUnipotent2 p h (-x) 1).1, (coe_mul_upperUnipotent2 p h (-x) 1).2]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

theorem inv_mul_entries (h : GL (Fin 2) F) (i j : Fin 2) :
    ∑ l : Fin 2, (h : Matrix (Fin 2) (Fin 2) F) i l * ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) l j =
      (1 : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem hmul_hmul_inv (h : GL (Fin 2) F) (u : F × F) : hmul p h (hmul p h⁻¹ u) = u := by
  have h00 := inv_mul_entries p h 0 0
  have h01 := inv_mul_entries p h 0 1
  have h10 := inv_mul_entries p h 1 0
  have h11 := inv_mul_entries p h 1 1
  simp only [Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h00 h01 h10 h11
  simp only [hmul]
  refine Prod.ext ?_ ?_
  · simp only []
    linear_combination u.1 * h00 + u.2 * h01
  · simp only []
    linear_combination u.1 * h10 + u.2 * h11

theorem hz_mul_upperUnipotent3_zero (h : GL (Fin 2) F) (c : F × F) :
    hz p h * ((upperUnipotent3 0 c.2 c.1 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) = hcol p h (hmul p h c) := by
  rw [hz_mul_upperUnipotent3]
  congr 1
  rw [upperUnipotent2_zero, mul_one]

end B1aS1

namespace B1ajf

open B1aS1

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel
attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ENNReal) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

theorem secondCountableTopology_GL2 : SecondCountableTopology (GL (Fin 2) F) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → F))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) F)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isMulRightInvariant_GL2 (μ₂ : Measure (GL (Fin 2) F)) [μ₂.IsHaarMeasure] : μ₂.IsMulRightInvariant := by
  haveI := secondCountableTopology_GL2 p
  haveI := locallyCompactSpace_localGL ℚ p
  exact (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μ₂).1

theorem continuous_upperUnipotent2 : Continuous (fun x : F => (upperUnipotent2 p x : GL (Fin 2) F)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent2_coe] <;> fun_prop
  · have : (fun x : F => (((upperUnipotent2 p x : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
        fun x : F => !![(1 : F), -x; 0, 1] := by
      funext x; rfl
    rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

def hmulEquiv (h : GL (Fin 2) F) : (F × F) ≃ᵐ (F × F) where
  toFun := hmul p h
  invFun := hmul p h⁻¹
  left_inv u := by
    have := hmul_hmul_inv p h⁻¹ u
    rwa [inv_inv] at this
  right_inv u := hmul_hmul_inv p h u
  measurable_toFun := by
    show Measurable (hmul p h)
    unfold hmul; fun_prop
  measurable_invFun := by
    show Measurable (hmul p h⁻¹)
    unfold hmul; fun_prop

theorem hmul_eq_comp (h : GL (Fin 2) F) :
    hmul p h = (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ F × F) ∘
      (fun f : Fin 2 → F => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec f) ∘
        (MeasurableEquiv.finTwoArrow : (Fin 2 → F) ≃ᵐ F × F).symm := by
  funext u
  simp [hmul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem map_hmul (h : GL (Fin 2) F) :
    Measure.map (hmul p h) ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) =
      ENNReal.ofReal ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ •
        ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  set μ : Measure F := selfDualHaarAt ℚ p with hμ
  set e : (Fin 2 → F) ≃ᵐ F × F := MeasurableEquiv.finTwoArrow with he
  have hpres : MeasurePreserving e (Measure.pi fun _ : Fin 2 => μ) (μ.prod μ) :=
    MeasureTheory.measurePreserving_finTwoArrow μ
  have hdet : ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det h).ne_zero
  have hmv : Measurable fun f : Fin 2 → F => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec f :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hpi := NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi ℚ p μ
    ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) hdet
  calc Measure.map (hmul p h) (μ.prod μ)
      = Measure.map (hmul p h) (Measure.map e (Measure.pi fun _ : Fin 2 => μ)) := by rw [hpres.map_eq]
    _ = Measure.map (hmul p h ∘ e) (Measure.pi fun _ : Fin 2 => μ) :=
        Measure.map_map (hmulEquiv p h).measurable e.measurable
    _ = Measure.map (e ∘ fun f : Fin 2 → F => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec f)
          (Measure.pi fun _ : Fin 2 => μ) := by
        congr 1
        rw [hmul_eq_comp]
        funext f
        simp only [Function.comp_apply, ← he, MeasurableEquiv.symm_apply_apply]
    _ = Measure.map e (Measure.map (fun f : Fin 2 → F => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec f)
          (Measure.pi fun _ : Fin 2 => μ)) := (Measure.map_map e.measurable hmv).symm
    _ = Measure.map e (ENNReal.ofReal ‖((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖⁻¹ • Measure.pi fun _ : Fin 2 => μ) := by
        rw [hpi]
    _ = ENNReal.ofReal ‖((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖⁻¹ • Measure.map e (Measure.pi fun _ : Fin 2 => μ) :=
        Measure.map_smul _ _ _
    _ = _ := by rw [hpres.map_eq, ← Matrix.GeneralLinearGroup.val_det_apply]

def shear : F × F × F ≃ᵐ F × F × F where
  toFun t := (t.1, t.2.1, t.2.2 + t.1 * t.2.1)
  invFun t := (t.1, t.2.1, t.2.2 - t.1 * t.2.1)
  left_inv t := by simp
  right_inv t := by simp
  measurable_toFun := by
    refine (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk ?_)).measurable
    exact (continuous_snd.comp continuous_snd).add (continuous_fst.mul (continuous_fst.comp continuous_snd))
  measurable_invFun := by
    refine (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk ?_)).measurable
    exact (continuous_snd.comp continuous_snd).sub (continuous_fst.mul (continuous_fst.comp continuous_snd))

theorem measurePreserving_shear :
    MeasurePreserving (shear p) ((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))
      ((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  set μ : Measure F := selfDualHaarAt ℚ p with hμ
  refine (MeasurePreserving.id μ).skew_product (g := fun (x : F) (q : F × F) => (q.1, q.2 + x * q.1)) ?_ ?_
  · exact ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).add (continuous_fst.mul (continuous_fst.comp continuous_snd)))).measurable
  · refine Filter.Eventually.of_forall fun x => ?_
    exact ((MeasurePreserving.id μ).skew_product (g := fun (y : F) (z : F) => z + x * y)
      ((continuous_snd.add (continuous_const.mul continuous_fst))).measurable
      (Filter.Eventually.of_forall fun y => map_add_right_eq_self μ (x * y))).map_eq

def bigS : (F × F × F) × GL (Fin 2) F ≃ᵐ (F × F × F) × GL (Fin 2) F where
  toFun r := (shear p r.1, r.2 * upperUnipotent2 p (-r.1.1))
  invFun r := ((shear p).symm r.1, r.2 * upperUnipotent2 p r.1.1)
  left_inv r := by
    obtain ⟨q, h⟩ := r
    simp only [MeasurableEquiv.symm_apply_apply, Prod.mk.injEq, true_and]
    show h * upperUnipotent2 p (-q.1) * upperUnipotent2 p ((shear p q).1) = h
    rw [show (shear p q).1 = q.1 from rfl, mul_assoc, upperUnipotent2_neg_mul, mul_one]
  right_inv r := by
    obtain ⟨q, h⟩ := r
    simp only [MeasurableEquiv.apply_symm_apply, Prod.mk.injEq, true_and]
    show h * upperUnipotent2 p q.1 * upperUnipotent2 p (-((shear p).symm q).1) = h
    rw [show ((shear p).symm q).1 = q.1 from rfl, mul_assoc]
    have := upperUnipotent2_neg_mul p (-q.1)
    rw [neg_neg] at this
    rw [this, mul_one]
  measurable_toFun := by
    refine ((shear p).measurable.comp measurable_fst).prodMk ?_
    exact (continuous_snd.mul ((continuous_upperUnipotent2 p).comp
      ((continuous_fst.comp continuous_fst).neg))).measurable
  measurable_invFun := by
    refine ((shear p).symm.measurable.comp measurable_fst).prodMk ?_
    exact (continuous_snd.mul ((continuous_upperUnipotent2 p).comp (continuous_fst.comp continuous_fst))).measurable

theorem measurePreserving_bigS (μ₂ : Measure (GL (Fin 2) F)) [μ₂.IsHaarMeasure] :
    MeasurePreserving (bigS p) (((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))).prod μ₂)
      (((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))).prod μ₂) := by
  haveI := secondCountableTopology_GL2 p
  haveI := locallyCompactSpace_localGL ℚ p
  haveI := isMulRightInvariant_GL2 p μ₂
  haveI := isAddHaarMeasure_selfDualHaarAt p
  set μ3 := (selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) with hμ3

  have hS2 : MeasurePreserving (fun r : (F × F × F) × GL (Fin 2) F => (shear p r.1, r.2)) (μ3.prod μ₂) (μ3.prod μ₂) :=
    (measurePreserving_shear p).prod (MeasurePreserving.id μ₂)
  have hS1 : MeasurePreserving (fun r : (F × F × F) × GL (Fin 2) F => (r.1, r.2 * upperUnipotent2 p (-r.1.1)))
      (μ3.prod μ₂) (μ3.prod μ₂) := by
    refine (MeasurePreserving.id μ3).skew_product (g := fun (q : F × F × F) (h : GL (Fin 2) F) => h * upperUnipotent2 p (-q.1)) ?_ ?_
    · exact (continuous_snd.mul ((continuous_upperUnipotent2 p).comp ((continuous_fst.comp continuous_fst).neg))).measurable
    · exact Filter.Eventually.of_forall fun q => map_mul_right_eq_self μ₂ _
  have hcomp : (bigS p : (F × F × F) × GL (Fin 2) F → (F × F × F) × GL (Fin 2) F) =
      (fun r : (F × F × F) × GL (Fin 2) F => (r.1, r.2 * upperUnipotent2 p (-r.1.1))) ∘
        (fun r : (F × F × F) × GL (Fin 2) F => (shear p r.1, r.2)) := by
    funext r; rfl
  rw [hcomp]
  exact hS1.comp hS2

theorem continuous_addChar_inv (η : AddChar F ℂ) (hη : Continuous η) : Continuous (η⁻¹ : AddChar F ℂ) := by
  have : ((η⁻¹ : AddChar F ℂ) : F → ℂ) = fun x => η (-x) := by
    funext x; exact AddChar.inv_apply η x
  rw [this]
  exact hη.comp continuous_neg

theorem norm_addChar_le_one (η : AddChar F ℂ) (hη : Continuous η) (y : F) : ‖η y‖ ≤ 1 := by

  set S : Set F := (fun t : F => y * t) '' (p.adicCompletionIntegers ℚ : Set F) with hS
  have hSc : IsCompact S := by
    rw [hS]
    exact (isCompact_iff_compactSpace.mpr (show CompactSpace (p.adicCompletionIntegers ℚ) from inferInstance)).image
      (continuous_const.mul continuous_id)
  obtain ⟨M, hM⟩ := hSc.bddAbove_image (f := fun t => ‖η t‖) (hη.norm.continuousOn)
  have hmem : ∀ n : ℕ, (n : F) * y ∈ S := by
    intro n
    refine ⟨(n : F), ?_, by ring⟩
    exact natCast_mem (p.adicCompletionIntegers ℚ).toSubring n
  have hpow : ∀ n : ℕ, ‖η y‖ ^ n ≤ M := by
    intro n
    have h1 : η ((n : F) * y) = (η y) ^ n := by
      rw [show (n : F) * y = n • y from (nsmul_eq_mul n y).symm, AddChar.map_nsmul_eq_pow]
    have := hM ⟨(n : F) * y, hmem n, rfl⟩
    simpa [h1, norm_pow] using this
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_addChar_inv_le_one (η : AddChar F ℂ) (hη : Continuous η) (y : F) : ‖(η⁻¹ : AddChar F ℂ) y‖ ≤ 1 := by
  rw [AddChar.inv_apply]; exact norm_addChar_le_one p η hη (-y)

section Kernels

variable (η : AddChar (HeightOneSpectrum.adicCompletion ℚ p) ℂ) (lam0 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)
  (D : Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p) → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (g : LocalGL3 p)

def bet (h : GL (Fin 2) F) : ℂ :=
  ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
    ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (3 / 2 : ℂ)

def DW (X : Matrix (Fin 2) (Fin 3) F) (k : GL (Fin 2) F) : ℂ :=
  ∫ x : F, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)

def Gp (r : (F × F × F) × GL (Fin 2) F) : ℂ :=
  η⁻¹ (r.1.1 + r.1.2.1) *
    (D (hcol p r.2 (hmul p r.2 (r.1.2.2, r.1.2.1)) * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (upperUnipotent2 p r.1.1 * r.2⁻¹) * bet p lam0 r.2)

def RF (h : GL (Fin 2) F) : ℂ :=
  rowFourier23 p η⁻¹ (fun X => DW p η D (X * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h⁻¹) (godementArg p h)

theorem bet_ne_zero (h : GL (Fin 2) F) : bet p lam0 h ≠ 0 := by
  unfold bet
  refine mul_ne_zero (Units.ne_zero _) ?_
  have hm : ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (modulus_ne_zero (Matrix.GeneralLinearGroup.det h).ne_zero)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hm)

theorem bet_mul_norm_inv (h : GL (Fin 2) F) :
    bet p lam0 h * ((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ : ℝ) : ℂ) =
      ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  unfold bet
  have hmod : ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℝ) = ‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖ := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p]; rfl
  set m : ℂ := ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm]; exact_mod_cast (modulus_ne_zero (Matrix.GeneralLinearGroup.det h).ne_zero)
  have hinv : ((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ : ℝ) : ℂ) = m⁻¹ := by
    rw [hm, ← hmod, Complex.ofReal_inv]
  rw [hinv, show (3 / 2 : ℂ) = (1 / 2 : ℂ) + 1 by norm_num, Complex.cpow_add _ _ hm0, Complex.cpow_one]
  field_simp

end Kernels

section Inner

variable (η : AddChar (HeightOneSpectrum.adicCompletion ℚ p) ℂ) (lam0 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)
  (D : Matrix (Fin 2) (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p) → GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (g : LocalGL3 p)

theorem inner_eq (h : GL (Fin 2) F)
    (hint : Integrable (fun q : F × F × F => Gp p η lam0 D g (q, h))
      ((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)))) :
    ∫ q : F × F × F, Gp p η lam0 D g (q, h) ∂((selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
      RF p η D g h * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  haveI := isAddHaarMeasure_selfDualHaarAt p
  set μ : Measure F := selfDualHaarAt ℚ p with hμ
  set gM := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hgM
  set β := bet p lam0 h with hβ
  have hβ0 : β ≠ 0 := bet_ne_zero p lam0 h

  set K : F × F × F → ℂ := fun q => D (hcol p h (hmul p h (q.2.2, q.2.1)) * gM) (upperUnipotent2 p q.1 * h⁻¹) with hK
  set L : F × F × F → ℂ := fun q => η⁻¹ q.1 * (η⁻¹ q.2.1 * K q) with hL
  have hGL : ∀ q, Gp p η lam0 D g (q, h) = L q * β := by
    intro q
    simp only [Gp, hL, hK, hβ, hgM, AddChar.map_add_eq_mul]
    ring
  have hLint : Integrable L (μ.prod (μ.prod μ)) := by
    have : L = fun q => Gp p η lam0 D g (q, h) * β⁻¹ := by
      funext q; rw [hGL, mul_assoc, mul_inv_cancel₀ hβ0, mul_one]
    rw [this]; exact hint.mul_const _

  have hA : ∫ q, L q ∂(μ.prod (μ.prod μ)) = ∫ w : F × F, η⁻¹ w.1 * DW p η D (hcol p h (hmul p h (w.2, w.1)) * gM) h⁻¹ ∂(μ.prod μ) := by
    rw [integral_prod L hLint, integral_integral_swap hLint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hL, DW, hK]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring

  have hB : (∫ w : F × F, η⁻¹ w.1 * DW p η D (hcol p h (hmul p h (w.2, w.1)) * gM) h⁻¹ ∂(μ.prod μ)) =
      ∫ c : F × F, η⁻¹ c.2 * DW p η D (hcol p h (hmul p h c) * gM) h⁻¹ ∂(μ.prod μ) := by
    rw [← integral_prod_swap]
    rfl

  set fW : F × F → ℂ := fun u => η⁻¹ (hmul p h⁻¹ u).2 * DW p η D (hcol p h u * gM) h⁻¹ with hfW
  have hC : (∫ c : F × F, η⁻¹ c.2 * DW p η D (hcol p h (hmul p h c) * gM) h⁻¹ ∂(μ.prod μ)) =
      ∫ c : F × F, fW (hmulEquiv p h c) ∂(μ.prod μ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hfW]
    show _ = η⁻¹ (hmul p h⁻¹ (hmul p h c)).2 * DW p η D (hcol p h (hmul p h c) * gM) h⁻¹
    have := hmul_hmul_inv p h⁻¹ c
    rw [inv_inv] at this
    rw [this]
  have hD' : (∫ c : F × F, fW (hmulEquiv p h c) ∂(μ.prod μ)) =
      ((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ : ℝ) : ℂ) * ∫ u, fW u ∂(μ.prod μ) := by
    rw [← integral_map_equiv (hmulEquiv p h) fW, show (⇑(hmulEquiv p h) : F × F → F × F) = hmul p h from rfl,
      hμ, map_hmul p h, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))]
    rw [Complex.real_smul]

  have hE : (∫ u, fW u ∂(μ.prod μ)) = RF p η D g h := by
    simp only [RF, rowFourier23_eq, colFourier23_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hfW, hmul_inv_snd p h u, hcol_eq_setCol23_godementArg p h u, hgM]
    ring

  calc ∫ q : F × F × F, Gp p η lam0 D g (q, h) ∂(μ.prod (μ.prod μ))
      = ∫ q, L q * β ∂(μ.prod (μ.prod μ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => hGL q)
    _ = (∫ q, L q ∂(μ.prod (μ.prod μ))) * β := integral_mul_const _ _
    _ = ((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ : ℝ) : ℂ) * RF p η D g h * β := by rw [hA, hB, hC, hD', hE]
    _ = RF p η D g h * (β * ((‖((Matrix.GeneralLinearGroup.det h : Fˣ) : F)‖⁻¹ : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hβ, bet_mul_norm_inv p lam0 h]; ring

end Inner

theorem det_upperUnipotent3 (x y z : F) : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 p) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one]
  simp [Matrix.det_fin_three]

end B1ajf

open B1aS1 B1ajf in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (η : AddChar (p.adicCompletion ℚ) ℂ) (hη : Continuous η)
    (lam0 : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (D : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (Fsec : LocalGL3 p → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],

      (∀ Y : LocalGL3 p, Fsec Y = ((lam0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
          ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
            D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
              ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) ∂μ₂) →

      Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) => D P.1 P.2) →
      ∀ g : LocalGL3 p,

      Integrable (fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((r.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
                ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) r.2⁻¹ *
            ((lam0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ))
        ((jacquetHaar3 p).prod μ₂) →
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          rowFourier23 p η⁻¹
              (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
                  ∫ x : p.adicCompletion ℚ, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
                (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
              (godementArg p h) *
            ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) μ₂ ∧
      ∫ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
          η⁻¹ (q.1 + q.2.1) * Fsec (upperUnipotent3 q.1 q.2.1 q.2.2 * g) ∂(jacquetHaar3 p) =
        godementWhittaker3 p η μ₂ lam0
          (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
            ∫ x : p.adicCompletion ℚ, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
  intro μ₂ _ hF hD g hH1
  haveI := B1ajf.isAddHaarMeasure_selfDualHaarAt p
  haveI := B1ajf.secondCountableTopology_GL2 p
  haveI := locallyCompactSpace_localGL ℚ p
  set μ : Measure (p.adicCompletion ℚ) := selfDualHaarAt ℚ p with hμ
  have hμ3 : jacquetHaar3 p = μ.prod (μ.prod μ) := rfl
  haveI : SFinite (jacquetHaar3 p) := by rw [hμ3]; infer_instance
  haveI : SigmaFinite (jacquetHaar3 p) := by rw [hμ3]; infer_instance
  set gM := ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) with hgM

  set Φ₃ : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun r => D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
                (fun k' : Fin 2 => ((r.2 : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
              : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
                ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) r.2⁻¹ *
            ((lam0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)
    with hΦ₃
  have hH1' : Integrable Φ₃ ((jacquetHaar3 p).prod μ₂) := hH1
  set G : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) → ℂ :=
    fun r => η⁻¹ (r.1.1 + r.1.2.1) * Φ₃ r with hG

  have hηc : Continuous (η⁻¹ : AddChar (p.adicCompletion ℚ) ℂ) := B1ajf.continuous_addChar_inv p η hη
  have hGint : Integrable G ((jacquetHaar3 p).prod μ₂) := by
    refine hH1'.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun r => B1ajf.norm_addChar_inv_le_one p η hη _)
    exact (hηc.comp ((continuous_fst.comp continuous_fst).add
      ((continuous_fst.comp (continuous_snd.comp continuous_fst))))).aestronglyMeasurable

  have hGS : ∀ r, G (B1ajf.bigS p r) = B1ajf.Gp p η lam0 D g r := by
    rintro ⟨⟨x, y, z⟩, h⟩
    simp only [hG, hΦ₃, B1ajf.Gp, B1ajf.bet]
    show η⁻¹ (x + y) * (D ((Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
          (fun k' : Fin 2 => (((h * upperUnipotent2 p (-x)) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
            : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
          ((upperUnipotent3 x y (z + x * y) * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) (h * upperUnipotent2 p (-x))⁻¹ *
        ((lam0 (Matrix.GeneralLinearGroup.det (h * upperUnipotent2 p (-x))) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det (h * upperUnipotent2 p (-x)) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)) =
      η⁻¹ (x + y) * (D (hcol p h (hmul p h (z, y)) * gM) (upperUnipotent2 p x * h⁻¹) *
        (((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)))
    have e1 : (Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
          (fun k' : Fin 2 => (((h * upperUnipotent2 p (-x)) : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k
            : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) *
          ((upperUnipotent3 x y (z + x * y) * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
        hcol p h (hmul p h (z, y)) * gM := by
      rw [← hz_def, Units.val_mul, ← Matrix.mul_assoc, hz_mul_upperUnipotent3, mul_assoc, upperUnipotent2_neg_mul, mul_one,
        hmul_mul_upperUnipotent2_neg]
      congr 2
      ring
    have e2 : (h * upperUnipotent2 p (-x))⁻¹ = upperUnipotent2 p x * h⁻¹ := by
      rw [mul_inv_rev]
      congr 1
      rw [inv_eq_iff_mul_eq_one]
      exact upperUnipotent2_neg_mul p x
    have e3 : Matrix.GeneralLinearGroup.det (h * upperUnipotent2 p (-x)) = Matrix.GeneralLinearGroup.det h := by
      rw [map_mul, det_upperUnipotent2, mul_one]
    rw [e1, e2, e3]
    ring
  have hS : MeasurePreserving (B1ajf.bigS p) ((jacquetHaar3 p).prod μ₂) ((jacquetHaar3 p).prod μ₂) :=
    B1ajf.measurePreserving_bigS p μ₂
  have hGpint : Integrable (B1ajf.Gp p η lam0 D g) ((jacquetHaar3 p).prod μ₂) := by
    have h1 : Integrable (G ∘ B1ajf.bigS p) ((jacquetHaar3 p).prod μ₂) :=
      (hS.integrable_comp_emb (B1ajf.bigS p).measurableEmbedding).mpr hGint
    exact h1.congr (Filter.Eventually.of_forall fun r => hGS r)
  have hae : ∀ᵐ h ∂μ₂, Integrable (fun q => B1ajf.Gp p η lam0 D g (q, h)) (jacquetHaar3 p) :=
    hGpint.swap.prod_right_ae
  have hinner : ∀ᵐ h ∂μ₂, ∫ q, B1ajf.Gp p η lam0 D g (q, h) ∂(jacquetHaar3 p) =
      B1ajf.RF p η D g h * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    filter_upwards [hae] with h hh
    exact B1ajf.inner_eq p η lam0 D g h hh
  have hRF : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), B1ajf.RF p η D g h =
      rowFourier23 p η⁻¹
        (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
            ∫ x : p.adicCompletion ℚ, η⁻¹ x * D X (upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
          (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
        (godementArg p h) := fun h => rfl
  refine ⟨?_, ?_⟩
  ·
    have hI : Integrable (fun h => ∫ q, B1ajf.Gp p η lam0 D g (q, h) ∂(jacquetHaar3 p)) μ₂ :=
      hGpint.swap.integral_prod_left
    refine hI.congr ?_
    filter_upwards [hinner] with h hh
    rw [hh, hRF]
  ·
    have hdet : ∀ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
        Matrix.GeneralLinearGroup.det (upperUnipotent3 q.1 q.2.1 q.2.2 * g : LocalGL3 p) = Matrix.GeneralLinearGroup.det g := by
      intro q; rw [map_mul, B1ajf.det_upperUnipotent3, one_mul]
    set cg : ℂ := ((lam0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) with hcg
    have hL1 : ∀ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
        η⁻¹ (q.1 + q.2.1) * Fsec (upperUnipotent3 q.1 q.2.1 q.2.2 * g) = cg * ∫ h, G (q, h) ∂μ₂ := by
      intro q
      rw [hF, hdet, ← integral_const_mul]
      simp only [hG, hΦ₃, hcg]
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      ring
    calc ∫ q, η⁻¹ (q.1 + q.2.1) * Fsec (upperUnipotent3 q.1 q.2.1 q.2.2 * g) ∂(jacquetHaar3 p)
        = ∫ q, cg * ∫ h, G (q, h) ∂μ₂ ∂(jacquetHaar3 p) := integral_congr_ae (Filter.Eventually.of_forall hL1)
      _ = cg * ∫ r, G r ∂((jacquetHaar3 p).prod μ₂) := by rw [integral_const_mul, integral_prod G hGint]
      _ = cg * ∫ r, B1ajf.Gp p η lam0 D g r ∂((jacquetHaar3 p).prod μ₂) := by
          rw [← hS.integral_comp (B1ajf.bigS p).measurableEmbedding]
          simp_rw [hGS]
      _ = cg * ∫ h, ∫ q, B1ajf.Gp p η lam0 D g (q, h) ∂(jacquetHaar3 p) ∂μ₂ := by rw [integral_prod_symm _ hGpint]
      _ = cg * ∫ h, B1ajf.RF p η D g h * ((lam0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) ∂μ₂ := by
          rw [integral_congr_ae hinner]
      _ = _ := by
          rw [godementWhittaker3_apply]
          simp_rw [hRF]
          simp only [hcg]
          ring

end

end S_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous (solution)
