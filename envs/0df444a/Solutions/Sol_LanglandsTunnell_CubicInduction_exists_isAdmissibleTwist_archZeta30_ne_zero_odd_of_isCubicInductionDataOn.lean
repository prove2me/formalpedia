-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/305c402d-ae33-5ef3-8279-9c9fea94e94a

import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Theorems.Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_of_infPart_eq_of_isArchCompAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn

set_option autoImplicit false

p2m_open "Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda"

noncomputable section

section
open MeasureTheory Set

namespace AbsInvDensity

noncomputable def nnDensity (y : ℝ) : NNReal := Real.toNNReal |y|⁻¹

theorem measurable_nnDensity : Measurable nnDensity :=
  (measurable_abs.inv).real_toNNReal

theorem coe_nnDensity (y : ℝ) : (nnDensity y : ℝ) = |y|⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg y))

theorem pos_of_map_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) : 0 < κ := by
  by_contra hle
  have h0 : ENNReal.ofReal κ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
  have hmap : Measure.map T μ = 0 := by rw [hκ, h0, zero_smul]
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← Set.preimage_univ (f := T), ← Measure.map_apply hT MeasurableSet.univ, hmap]
  rfl

theorem map_eq_smul_withDensity {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => (nnDensity y : ENNReal) := hκ

theorem map_absolutelyContinuous {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ ≪ (volume : Measure ℝ) := by
  rw [hκ]
  exact (withDensity_absolutelyContinuous _ _).smul_left (ENNReal.ofReal κ)

theorem nnDensity_smul_eq (f : ℝ → ℂ) (y : ℝ) : nnDensity y • f y = f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  change ((nnDensity y : ℝ)) • f y = f y * ((|y| : ℝ) : ℂ)⁻¹
  rw [Complex.real_smul, coe_nnDensity, Complex.ofReal_inv, mul_comm]

theorem integral_comp_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T)
    (κ : ℝ) (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    0 < κ ∧ ∫ x, f (T x) ∂μ = (κ : ℂ) * ∫ y : ℝ, f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  have hpos : 0 < κ := pos_of_map_eq μ T hT κ hκ hμ
  refine ⟨hpos, ?_⟩
  have hf' : AEStronglyMeasurable f (Measure.map T μ) := hf.mono_ac (map_absolutelyContinuous μ T κ hκ)
  rw [← integral_map hT.aemeasurable hf', map_eq_smul_withDensity μ T κ hκ, integral_smul_measure,
    integral_withDensity_eq_integral_smul measurable_nnDensity, ENNReal.toReal_ofReal hpos.le]
  refine Complex.real_smul.trans ?_
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => nnDensity_smul_eq f y)

end AbsInvDensity

theorem norm_component_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x Rat.infinitePlace‖ = |StandardKernel.realCoord x| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (Rat.isReal_infinitePlace)).norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  rw [← h, Real.norm_eq_abs]
  rfl

theorem norm_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x‖ = |StandardKernel.realCoord x| := by
  rw [InfiniteAdeleRing.norm_def, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  have hm : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  rw [hd, hm, pow_one]
  exact norm_component_eq_abs_realCoord x

theorem measurable_realCoord_units [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] :
    Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  have hc : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  exact (hc.comp Units.continuous_val).measurable

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.HasConductorExponentAt signEpsilon HeckeTate.heckeDatum Converse.exists_isArchCompAt_zero_of_isOfFinOrder CubicInduction.apply_of_infPart_eq_of_isArchCompAt"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "CubicInductionData IsCubicInductionDataOn IsGL3PsiWhittakerFn gl3CyclicSubspace transposeInv3 psiLoc AdelicGL upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL archComponent3 LocalGL3 IsRamifiedIn IsBadPlace inducedLevelAt diagUnitGL2 coe_diagUnitGL2 dualWhittakerFn3 weylPrime3 archRoot₁ archRoot₂ archRootSum IsGaugeMajorised3 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove apply_of_infPart_eq_of_isArchCompAt"
namespace ArchNonvanishing
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory Set AutomorphicForm.StandardKernel

theorem ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (r * s) =
    ofReal r v * ofReal s v
  rw [map_mul]
  rfl

private theorem _root_.LanglandsTunnell.CubicInduction.ArchNonvanishing.ofReal_one : ofReal 1 = 1 := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 1 = 1
  rw [map_one]

p2m_export "LanglandsTunnell.CubicInduction.ArchNonvanishing" "ofReal_one"
theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r := by
  rw [realCoord_apply]
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).apply_symm_apply r

def unitOfReal (y : ℝ) (hy : y ≠ 0) : (InfiniteAdeleRing ℚ)ˣ where
  val := ofReal y
  inv := ofReal y⁻¹
  val_inv := by rw [← ofReal_mul, mul_inv_cancel₀ hy, ofReal_one]
  inv_val := by rw [← ofReal_mul, inv_mul_cancel₀ hy, ofReal_one]

theorem unitOfReal_realCoord (z : (InfiniteAdeleRing ℚ)ˣ) :
    unitOfReal (realCoord (z : InfiniteAdeleRing ℚ)) ((z.isUnit.map realCoord).ne_zero) = z :=
  Units.ext (ofReal_realCoord _)

end LanglandsTunnell.CubicInduction.ArchNonvanishing

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.addCharLevel TateLocal.HasConductorExponentAt signEpsilon HeckeTate.heckeDatum Converse.exists_isArchCompAt_zero_of_isOfFinOrder CubicInduction.apply_of_infPart_eq_of_isArchCompAt"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "CubicInductionData IsCubicInductionDataOn IsGL3PsiWhittakerFn gl3CyclicSubspace transposeInv3 psiLoc AdelicGL upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL archComponent3 LocalGL3 IsRamifiedIn IsBadPlace inducedLevelAt diagUnitGL2 coe_diagUnitGL2 dualWhittakerFn3 weylPrime3 archRoot₁ archRoot₂ archRootSum IsGaugeMajorised3 archZeta30 archZetaDual31 IsArchZeta30ConvergentAbove IsArchZeta31ConvergentAbove apply_of_infPart_eq_of_isArchCompAt"
namespace ArchNonvanishing
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory Set AutomorphicForm.StandardKernel

section LineFn

def unitOfReal' (y : ℝ) : (InfiniteAdeleRing ℚ)ˣ :=
  if hy : y = 0 then 1 else unitOfReal y hy

theorem unitOfReal'_of_ne {y : ℝ} (hy : y ≠ 0) : unitOfReal' y = unitOfReal y hy := by
  simp [unitOfReal', hy]

theorem coe_unitOfReal'_of_ne {y : ℝ} (hy : y ≠ 0) :
    ((unitOfReal' y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = ofReal y := by
  rw [unitOfReal'_of_ne hy]; rfl

theorem unitOfReal'_realCoord (z : (InfiniteAdeleRing ℚ)ˣ) :
    unitOfReal' (realCoord (z : InfiniteAdeleRing ℚ)) = z := by
  rw [unitOfReal'_of_ne ((z.isUnit.map realCoord).ne_zero)]
  exact Units.ext (ofReal_realCoord _)

theorem unitOfReal'_one : unitOfReal' 1 = 1 := by
  rw [unitOfReal'_of_ne one_ne_zero]
  exact Units.ext ofReal_one

private theorem _root_.LanglandsTunnell.CubicInduction.ArchNonvanishing.ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (-r) = -ofReal r v
  rw [map_neg]
  rfl

p2m_export "LanglandsTunnell.CubicInduction.ArchNonvanishing" "ofReal_neg"
theorem coe_unitOfReal'_neg_one : ((unitOfReal' (-1) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = -1 := by
  rw [coe_unitOfReal'_of_ne (by norm_num), ofReal_neg, ofReal_one]

theorem continuousOn_unitOfReal' : ContinuousOn unitOfReal' ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (({0}ᶜ : Set ℝ).domRestrict unitOfReal') = fun y : ({0}ᶜ : Set ℝ) => unitOfReal (y : ℝ) y.2 := by
    funext y
    exact unitOfReal'_of_ne y.2
  rw [heq, Units.continuous_iff]
  constructor
  · show Continuous fun y : ({0}ᶜ : Set ℝ) => ofReal (y : ℝ)
    exact continuous_ofReal.comp continuous_subtype_val
  · show Continuous fun y : ({0}ᶜ : Set ℝ) => ofReal ((y : ℝ)⁻¹)
    exact continuous_ofReal.comp (continuous_subtype_val.inv₀ fun y => y.2)

variable (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))

def lineFn (y : ℝ) : ℂ := W (iotaGL (diagUnitGL2 (unitOfReal' y)) * g)

theorem lineFn_realCoord (z : (InfiniteAdeleRing ℚ)ˣ) :
    lineFn W g (realCoord (z : InfiniteAdeleRing ℚ)) = W (iotaGL (diagUnitGL2 z) * g) := by
  rw [lineFn, unitOfReal'_realCoord]

theorem continuous_iotaGL_diagUnitGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun x : Aˣ => (iotaGL (diagUnitGL2 x) : GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [embedMat2] <;> first | exact Units.continuous_val | exact continuous_const
  · show Continuous fun x : Aˣ => (((iotaGL (diagUnitGL2 x))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
    have h : ∀ x : Aˣ, (((iotaGL (diagUnitGL2 x))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
        embedMat2 ((diagUnitGL2 x)⁻¹ : GL (Fin 2) A) := fun x => by rw [← map_inv]; rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [embedMat2, diagUnitGL2] <;> first | exact Units.continuous_coe_inv | exact continuous_const

theorem continuousOn_lineFn (hW : Continuous W) : ContinuousOn (lineFn W g) ({0}ᶜ : Set ℝ) :=
  (hW.comp ((continuous_iotaGL_diagUnitGL2.mul continuous_const))).continuousOn.comp
    continuousOn_unitOfReal' (mapsTo_univ _ _)

theorem continuousAt_lineFn (hW : Continuous W) {y : ℝ} (hy : y ≠ 0) : ContinuousAt (lineFn W g) y :=
  (continuousOn_lineFn W g hW).continuousAt (isOpen_compl_singleton.mem_nhds hy)

def evenFn (t : ℝ) : ℂ := lineFn W g t + lineFn W g (-t)

theorem continuousAt_evenFn (hW : Continuous W) {t : ℝ} (ht : 0 < t) : ContinuousAt (evenFn W g) t :=
  (continuousAt_lineFn W g hW ht.ne').add
    ((continuousAt_lineFn W g hW (neg_ne_zero.mpr ht.ne')).comp (continuous_neg.continuousAt))

def sgnC (y : ℝ) : ℂ := ((y : ℝ) : ℂ) / ((|y| : ℝ) : ℂ)

theorem sgnC_one : sgnC 1 = 1 := by simp [sgnC]

theorem sgnC_neg_one : sgnC (-1) = -1 := by simp [sgnC]

theorem sgnC_of_pos {t : ℝ} (ht : 0 < t) : sgnC t = 1 := by
  rw [sgnC, abs_of_pos ht, div_self (Complex.ofReal_ne_zero.mpr ht.ne')]

theorem sgnC_neg_of_pos {t : ℝ} (ht : 0 < t) : sgnC (-t) = -1 := by
  rw [sgnC, abs_neg, abs_of_pos ht, Complex.ofReal_neg, neg_div, div_self (Complex.ofReal_ne_zero.mpr ht.ne')]

theorem continuousOn_sgnC : ContinuousOn sgnC ({0}ᶜ : Set ℝ) := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  refine ContinuousAt.continuousWithinAt ?_
  unfold sgnC
  exact (Complex.continuous_ofReal.continuousAt).div
    ((Complex.continuous_ofReal.comp continuous_abs).continuousAt)
    (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hy0))

def olineFn (y : ℝ) : ℂ := sgnC y * lineFn W g y

theorem continuousOn_olineFn (hW : Continuous W) : ContinuousOn (olineFn W g) ({0}ᶜ : Set ℝ) :=
  continuousOn_sgnC.mul (continuousOn_lineFn W g hW)

theorem continuousAt_olineFn (hW : Continuous W) {y : ℝ} (hy : y ≠ 0) : ContinuousAt (olineFn W g) y :=
  (continuousOn_olineFn W g hW).continuousAt (isOpen_compl_singleton.mem_nhds hy)

def ooddFn (t : ℝ) : ℂ := olineFn W g t + olineFn W g (-t)

theorem continuousAt_ooddFn (hW : Continuous W) {t : ℝ} (ht : 0 < t) : ContinuousAt (ooddFn W g) t :=
  (continuousAt_olineFn W g hW ht.ne').add
    ((continuousAt_olineFn W g hW (neg_ne_zero.mpr ht.ne')).comp (continuous_neg.continuousAt))

end LineFn

section Transport

variable [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
  (ν_mul : Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
  (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))

theorem integrand_eq (τ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (hτ : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ((τ z : ℂˣ) : ℂ) = sgnC (realCoord (z : InfiniteAdeleRing ℚ))) (s : ℂ) (z : (InfiniteAdeleRing ℚ)ˣ) :
    W (iotaGL (diagUnitGL2 z) * g) * ((τ z : ℂˣ) : ℂ) *
        ((‖(z : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1) =
      (fun y : ℝ => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1)) (realCoord (z : InfiniteAdeleRing ℚ)) := by
  show _ = sgnC (realCoord (z : InfiniteAdeleRing ℚ)) * lineFn W g (realCoord (z : InfiniteAdeleRing ℚ)) *
    (((|realCoord (z : InfiniteAdeleRing ℚ)| : ℝ) : ℂ)) ^ (s - 1)
  rw [hτ z, lineFn_realCoord, norm_eq_abs_realCoord]
  ring

theorem aestronglyMeasurable_line (hW : Continuous W) (s : ℂ) :
    AEStronglyMeasurable (fun y : ℝ => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1)) volume := by
  have h0 : (volume : Measure ℝ).restrict ({0}ᶜ : Set ℝ) = volume :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff, show {a : ℝ | ¬a ∈ ({0}ᶜ : Set ℝ)} = {0} by ext; simp]
      exact Real.volume_singleton)
  rw [← h0]
  refine ContinuousOn.aestronglyMeasurable ?_ isOpen_compl_singleton.measurableSet
  refine (continuousOn_olineFn W g hW).mul ?_
  intro y hy
  refine ((Complex.continuous_ofReal.comp continuous_abs).continuousAt.cpow continuousAt_const ?_).continuousWithinAt
  exact Or.inl (by simpa [Complex.ofReal_re] using abs_pos.mpr (show y ≠ 0 from hy))

theorem archZeta30_one_eq (τ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (hτ : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ((τ z : ℂˣ) : ℂ) = sgnC (realCoord (z : InfiniteAdeleRing ℚ))) (hW : Continuous W) (κ : ℝ)
    (hκ : Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) (s : ℂ) :
    archZeta30 ν_mul W τ s g =
      (κ : ℂ) * ∫ y : ℝ, olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ := by
  unfold archZeta30
  have hne : ν_mul ≠ 0 := fun h =>
    (Measure.IsOpenPosMeasure.open_pos (μ := ν_mul) _ isOpen_univ univ_nonempty) (by rw [h]; rfl)
  rw [show (fun a : (InfiniteAdeleRing ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) *
        ((τ a : ℂˣ) : ℂ) * ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) =
      fun a : (InfiniteAdeleRing ℚ)ˣ => (fun y : ℝ => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1)) (realCoord (a : InfiniteAdeleRing ℚ)) from
      funext fun a => integrand_eq W g τ hτ s a]
  exact (AbsInvDensity.integral_comp_eq ν_mul _ measurable_realCoord_units κ hκ hne _
    (aestronglyMeasurable_line W g hW s)).2

theorem integrable_line (τ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ)
    (hτ : ∀ z : (InfiniteAdeleRing ℚ)ˣ, ((τ z : ℂˣ) : ℂ) = sgnC (realCoord (z : InfiniteAdeleRing ℚ))) (hW : Continuous W) (κ : ℝ) (hκpos : 0 < κ)
    (hκ : Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) (s : ℂ)
    (hint : Integrable (fun a : (InfiniteAdeleRing ℚ)ˣ => W (iotaGL (diagUnitGL2 a) * g) *
        ((τ a : ℂˣ) : ℂ) * ((‖(a : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) ν_mul) :
    Integrable (fun y : ℝ => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹) volume := by
  set f : ℝ → ℂ := fun y => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) with hf
  have hcomp : Integrable (f ∘ fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul := by
    refine hint.congr (Filter.Eventually.of_forall fun a => ?_)
    exact integrand_eq W g τ hτ s a
  have hfm : AEStronglyMeasurable f (Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul) :=
    (aestronglyMeasurable_line W g hW s).mono_ac (AbsInvDensity.map_absolutelyContinuous ν_mul _ κ hκ)
  have h1 : Integrable f (Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ)) ν_mul) :=
    (integrable_map_measure hfm measurable_realCoord_units.aemeasurable).mpr hcomp
  rw [AbsInvDensity.map_eq_smul_withDensity ν_mul _ κ hκ] at h1
  have h2 : Integrable f ((volume : Measure ℝ).withDensity fun y => (AbsInvDensity.nnDensity y : ENNReal)) :=
    (integrable_smul_measure (by simpa using hκpos) ENNReal.ofReal_ne_top).mp h1
  rw [integrable_withDensity_iff_integrable_smul' ] at h2
  · refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    show ((AbsInvDensity.nnDensity y : ENNReal).toReal) • f y = f y * ((|y| : ℝ) : ℂ)⁻¹
    rw [ENNReal.coe_toReal, AbsInvDensity.coe_nnDensity, Complex.real_smul, Complex.ofReal_inv, mul_comm]
  · exact AbsInvDensity.measurable_nnDensity.coe_nnreal_ennreal
  · exact Filter.Eventually.of_forall fun y => ENNReal.coe_lt_top

theorem integral_line_eq_mellin (s : ℂ)
    (hint : Integrable (fun y : ℝ => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹) volume) :
    ∫ y : ℝ, olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ = mellin (ooddFn W g) (s - 1) ∧
      MellinConvergent (ooddFn W g) (s - 1) := by
  set h : ℝ → ℂ := fun y => olineFn W g y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ with hh

  have hray : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) • ooddFn W g t = h t + h (-t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have habs : |t| = t := abs_of_pos ht0
    have habs' : |-t| = t := by rw [abs_neg, habs]
    simp only [hh, ooddFn, olineFn, sgnC_of_pos ht0, sgnC_neg_of_pos ht0, habs, habs', smul_eq_mul]
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [Complex.cpow_sub _ _ htc, Complex.cpow_one, div_eq_mul_inv]
    ring
  have hIoi : IntegrableOn h (Ioi 0) volume := hint.integrableOn
  have hIoi' : IntegrableOn (fun t => h (-t)) (Ioi 0) volume := by
    have := (hint.integrableOn (s := Iio 0)).comp_neg
    simpa using this
  have hconv : MellinConvergent (ooddFn W g) (s - 1) := by
    refine (hIoi.add hIoi').congr_fun (fun t ht => (hray t ht).symm) measurableSet_Ioi
  refine ⟨?_, hconv⟩

  have hsplit : ∫ y : ℝ, h y = (∫ y in Ioi 0, h y) + ∫ y in Iic 0, h y := by
    rw [← setIntegral_univ, show (univ : Set ℝ) = Ioi 0 ∪ Iic 0 by rw [Ioi_union_Iic], ]
    exact setIntegral_union (Iic_disjoint_Ioi le_rfl).symm measurableSet_Iic hIoi hint.integrableOn
  have hneg : ∫ y in Iic (0 : ℝ), h y = ∫ y in Ioi (0 : ℝ), h (-y) := by
    rw [integral_comp_neg_Ioi 0 h, neg_zero]
  rw [hsplit, hneg, ← integral_add hIoi hIoi', mellin]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => (hray t ht).symm

end Transport

section Algebra

variable {A : Type*} [CommRing A]

theorem iotaGL_diagUnitGL2_mul_upperUnipotent3 (u : Aˣ) (x : A) :
    iotaGL (diagUnitGL2 u) * upperUnipotent3 x 0 0 = upperUnipotent3 ((u : A) * x) 0 0 * iotaGL (diagUnitGL2 u) := by
  apply Units.ext
  simp only [Units.val_mul, coe_iotaGL, coe_diagUnitGL2, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

end Algebra

end LanglandsTunnell.CubicInduction.ArchNonvanishing

end

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn.LanglandsTunnell LanglandsTunnell.CubicInduction.ArchNonvanishing AutomorphicForm.StandardKernel in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (hlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ w ↔ w ∈ S)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ
      (S : Set (HeightOneSpectrum (𝓞 ℚ))) X)
    (hcont : Continuous X.form) (hcontW : Continuous X.whittaker) (hcontW' : Continuous X.dualWhittaker)
    (hW : IsGaugeMajorised3 ℚ X.whittaker) (hW' : IsGaugeMajorised3 ℚ X.dualWhittaker)
    (hne : X.whittakerArch ≠ 0)
    (hatS : ∀ w ∈ S, X.whittakerLoc w 1 = 1 ∧
      (∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w), F ≠ 0 → X.whittakerLoc w ∈ gl3CyclicSubspace F) ∧
      (∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧
        ∀ k ∈ Uw, ∀ g : LocalGL3 w, X.whittakerLoc w (g * k) = X.whittakerLoc w g) ∧
      ∀ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) →
        ∃ B : Finset (LocalGL3 w → ℂ), ∀ F ∈ gl3CyclicSubspace (X.whittakerLoc w),
          (∀ k ∈ Uw, ∀ g : LocalGL3 w, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 w → ℂ)))
    (hcent : ∀ w ∈ S,
      (∀ z : (w.adicCompletion ℚ)ˣ, ‖((localChar X.centralChar w z : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (t : (w.adicCompletion ℚ)ˣ) (h : LocalGL3 w),
        X.whittakerLoc w (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
          ((localChar X.centralChar w t : ℂˣ) : ℂ) * X.whittakerLoc w h)
    (hωcond : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v → ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar X.centralChar v) a)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (hψinf : ψ.compAddMonoidHom
        (AddMonoidHom.inl (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)) = psiInf)
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (hArch :
      (Continuous X.whittakerArch ∧ ∃ t : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g)‖ ≤
        C / ((∏ w : InfinitePlace ℚ, archRoot₁ ℚ w g * archRoot₂ ℚ w g) ^ t * (1 + archRootSum ℚ g) ^ N)) ∧
      IsGL3PsiWhittakerFn psiInf X.whittakerArch ∧
      (∀ (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
        X.whittakerArch (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((X.centralChar (E z) : ℂˣ) : ℂ) * X.whittakerArch g) ∧
      (∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
        ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
        ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
          (∃ σ₀ : ℝ, IsArchZeta30ConvergentAbove ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) 1 σ₀ ∧
            ∀ s : ℂ, σ₀ < s.re →
              archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 =
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s) ∧
          (∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ‖P s‖ ≤ C * Real.exp (A * |s.im|)) ∧
          (∀ (σ₁ σ₂ : ℝ) (N : ℕ), ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
            |s.im| ^ N *
              ‖P s *
                (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                  (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactor s‖ ≤ C) ∧
          (∃ σ₁ : ℝ, IsArchZeta31ConvergentAbove ν_mul ν_add (dualWhittakerFn3 (fun h => X.whittakerArch (h * gInf)))
              (σ.comp E)⁻¹ (weylPrime3 * transposeInv3 1) σ₁ ∧
            ∀ s : ℂ, σ₁ < (1 - s).re →
              archZetaDual31 ν_mul ν_add (fun h => X.whittakerArch (h * gInf)) (σ.comp E) (1 - s) 1 =
                (((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).prod
                    fun w => signEpsilon (aR w.1 w.2 + (e : ZMod 2))) *
                  ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).prod
                      fun w => Complex.I ^ (kC w.1 w.2).natAbs) *
                  ∏ w : InfinitePlace K, lambdaArch K w) *
                (((X.centralChar (E aInf) : ℂˣ) : ℂ) * ((σ (E aInf) : ℂˣ) : ℂ) ^ 3) *
                (((|a| : ℝ) : ℂ) ^ (3 * (s - 1 / 2))) *
                P s *
                  (LanglandsTunnell.HeckeTate.heckeDatum K μ (fun w hw => uR w hw + t)
                    (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC).archFactorDual (1 - s))) ∧
      ∃ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ ∧
        ∃ s : ℂ, archZeta30 ν_mul X.whittakerArch (σ.comp E) s 1 ≠ 0)

 :
    ∃ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ), IsAdmissibleTwist ℚ σ ∧
      (∃ (t : ℂ) (e : ℤ), (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w t e) ∧ (-1 : ℂ) ^ e = -1) ∧
      ∀ σ₀ : ℝ, ∃ s : ℂ, σ₀ < s.re ∧ archZeta30 ν_mul (fun h => X.whittakerArch (h * gInf)) (σ.comp E) s 1 ≠ 0 := by
  classical
  obtain ⟨hcontA, _hdecay⟩ := hArch.1
  have hlaw := hArch.2.1
  have hzeta := hArch.2.2.2.1

  let χ4 : DirichletCharacter ℂ 4 := MulChar.ringHomComp ZMod.χ₄ (Int.castRingHom ℂ)
  have hχ4 : χ4 (-1) = -1 := by
    show ((ZMod.χ₄ (-1 : ZMod 4) : ℤ) : ℂ) = -1
    have h : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    rw [h]
    push_cast
    rfl
  set σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := χ4.dirichletIdeleChar with hσdef
  have hfo := DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar χ4
  have hσadm : IsAdmissibleTwist ℚ σ :=
    ⟨hfo.isIdeleClassChar, hfo.continuous, fun x => DirichletCharacter.norm_coe_dirichletIdeleChar_apply χ4 x⟩

  have hσarch : ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ σ w 0 1 := by
    intro w hw
    obtain ⟨b, hb⟩ := (LanglandsTunnell.Converse.exists_isArchCompAt_zero_of_isOfFinOrder ℚ σ hfo.continuous
      hfo.isOfFinOrder w).1 hw
    have hw0 : w = Rat.infinitePlace := Subsingleton.elim _ _
    have hval : ((archLocalChar σ w (-1) : ℂˣ) : ℂ) = -1 := by
      rw [NumberField.TateGlobal.archLocalChar_apply, ← hχ4]
      apply DirichletCharacter.coe_dirichletIdeleChar_of_snd_eq_one_of_neg χ4
      · intro p
        rw [NumberField.AdelicVolume.archCentralUnit_snd]
        rfl
      · subst hw0
        have hc : RatIdele.archCoord (NumberField.AdelicVolume.archCentralUnit ℚ Rat.infinitePlace (-1)) = -1 := by
          unfold RatIdele.archCoord
          rw [NumberField.AdelicVolume.archCentralUnit_fst_self, Units.val_neg, Units.val_one, map_neg, map_one]
        rw [hc]
        norm_num
    by_cases hb0 : b = 0
    · exfalso
      subst hb0
      have h1 := hb (-1)
      simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, Complex.cpow_zero, zpow_zero, mul_one] at h1
      rw [hval] at h1
      norm_num at h1
    · have hb1 : b = 1 := by
        fin_cases b
        · exact absurd rfl hb0
        · rfl
      subst hb1
      first
        | simpa using hb
        | (convert hb using 2 <;> first | rfl | decide)

  have hσE : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      ((((σ.comp E) z) : ℂˣ) : ℂ) = sgnC (realCoord (z : InfiniteAdeleRing ℚ)) := by
    intro z
    rw [MonoidHom.comp_apply, LanglandsTunnell.CubicInduction.apply_of_infPart_eq_of_isArchCompAt σ E hE 0 1 hσarch z
      Rat.infinitePlace Rat.isReal_infinitePlace]
    simp only [mul_zero, Complex.cpow_zero, one_mul, zpow_one]
    rw [sgnC, realCoord_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply, norm_component_eq_abs_realCoord,
      realCoord_apply]

  obtain ⟨κ, hκpos, hκ⟩ := AutomorphicForm.StandardKernel.exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv ν_mul
  by_contra hcon
  push Not at hcon

  have hzero : ∀ gInf : GL (Fin 3) (InfiniteAdeleRing ℚ),
      X.whittakerArch gInf - X.whittakerArch (iotaGL (diagUnitGL2 (unitOfReal' (-1))) * gInf) = 0 := by
    intro gInf
    obtain ⟨σ₀, hσ₀⟩ := hcon gInf σ hσadm ⟨0, 1, hσarch, by norm_num⟩
    obtain ⟨P, -, ⟨σ₁, hconv, -⟩, -⟩ := hzeta σ hσadm 0 1 hσarch gInf
    set V : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ := fun h => X.whittakerArch (h * gInf) with hV
    have hVc : Continuous V := hcontA.comp (continuous_id.mul continuous_const)
    set c : ℝ := max σ₀ σ₁ + 1 with hc

    have hkey : ∀ y : ℝ, mellin (ooddFn V 1) (((c - 1 : ℝ) : ℂ) + y * Complex.I) = 0 ∧
        MellinConvergent (ooddFn V 1) (((c - 1 : ℝ) : ℂ) + y * Complex.I) := by
      intro y
      set s : ℂ := (c : ℂ) + y * Complex.I with hs
      have hsre : s.re = c := by simp [hs]
      have hs1 : s - 1 = ((c - 1 : ℝ) : ℂ) + y * Complex.I := by
        rw [hs, Complex.ofReal_sub, Complex.ofReal_one]; ring
      have hconv_s := hconv s (by rw [hsre, hc]; linarith [le_max_right σ₀ σ₁])
      have hint := integrable_line ν_mul V 1 (σ.comp E) hσE hVc κ hκpos hκ s hconv_s
      obtain ⟨heq, hmc⟩ := integral_line_eq_mellin V 1 s hint
      have hz : archZeta30 ν_mul V (σ.comp E) s 1 = 0 :=
        hσ₀ s (by rw [hsre, hc]; linarith [le_max_left σ₀ σ₁])
      rw [archZeta30_one_eq ν_mul V 1 (σ.comp E) hσE hVc κ hκ s, heq] at hz
      rw [← hs1]
      exact ⟨(mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hκpos.ne'), hmc⟩

    have hG : ∀ t : ℝ, 0 < t → ooddFn V 1 t = 0 := by
      intro t ht
      have hmc := (hkey 0).2
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at hmc
      have hvert : Complex.VerticalIntegrable (mellin (ooddFn V 1)) (c - 1) volume := by
        have : (fun y : ℝ => mellin (ooddFn V 1) (((c - 1 : ℝ) : ℂ) + y * Complex.I)) = 0 :=
          funext fun y => (hkey y).1
        unfold Complex.VerticalIntegrable
        rw [this]
        exact integrable_zero _ _ _
      have hinv := mellinInv_mellin_eq (c - 1) (ooddFn V 1) ht hmc hvert (continuousAt_ooddFn V 1 hVc ht)
      rw [← hinv]
      unfold mellinInv
      have : (fun y : ℝ => ((t : ℂ) ^ (-(((c - 1 : ℝ) : ℂ) + y * Complex.I))) • mellin (ooddFn V 1) (((c - 1 : ℝ) : ℂ) + y * Complex.I)) = 0 :=
        funext fun y => by rw [(hkey y).1, smul_zero]; rfl
      rw [this, integral_zero', smul_zero]
    have h := hG 1 one_pos
    have h11 : (iotaGL (diagUnitGL2 (1 : (InfiniteAdeleRing ℚ)ˣ)) : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1 := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [embedMat2]
    simp only [ooddFn, olineFn, lineFn, hV, sgnC_one, sgnC_neg_one, unitOfReal'_one, h11, one_mul, mul_one,
      neg_one_mul] at h
    rw [← sub_eq_add_neg] at h
    exact h

  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hne
  set m : GL (Fin 3) (InfiniteAdeleRing ℚ) := iotaGL (diagUnitGL2 (unitOfReal' (-1))) with hm
  have hinv : ∀ gInf, X.whittakerArch (m * gInf) = X.whittakerArch gInf := fun gInf =>
    (sub_eq_zero.mp (hzero gInf)).symm
  have hψ : ∀ x : InfiniteAdeleRing ℚ, psiInf x = psiInf (-x) := by
    intro x
    have h1 := hinv (upperUnipotent3 x 0 0 * g₀)
    rw [← mul_assoc, hm, iotaGL_diagUnitGL2_mul_upperUnipotent3, mul_assoc, hlaw, coe_unitOfReal'_neg_one,
      ← hm, hinv g₀, hlaw, add_zero, add_zero, neg_one_mul] at h1

    have h2 : (psiInf (-x) - psiInf x) * X.whittakerArch g₀ = 0 := by linear_combination h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hg₀)).symm
  have htriv : ∀ x : InfiniteAdeleRing ℚ, psiInf x = 1 := by
    intro x
    have h2 := hψ ((2 : ℚ)⁻¹ • x)
    have hx : x = (2 : ℚ)⁻¹ • x + (2 : ℚ)⁻¹ • x := by
      rw [← add_smul]; norm_num
    have := AddChar.map_add_eq_mul psiInf ((2 : ℚ)⁻¹ • x) ((2 : ℚ)⁻¹ • x)
    rw [← hx] at this
    rw [this]
    nth_rewrite 2 [h2]
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

  have hhalf := htriv (algebraMap ℚ (InfiniteAdeleRing ℚ) (a⁻¹ * 2⁻¹))
  rw [hpsiInf, ← map_mul, show a * (a⁻¹ * 2⁻¹) = (2⁻¹ : ℚ) by field_simp,
    NumberField.StandardAddChar.psiArch_algebraMap] at hhalf
  have : Complex.exp ((2 * Real.pi * Complex.I) * ((2⁻¹ : ℚ) : ℂ)) = -1 := by
    rw [show (2 * Real.pi * Complex.I) * ((2⁻¹ : ℚ) : ℂ) = Real.pi * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [this] at hhalf
  norm_num at hhalf

end S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_archZeta30_ne_zero_odd_of_isCubicInductionDataOn (solution)
