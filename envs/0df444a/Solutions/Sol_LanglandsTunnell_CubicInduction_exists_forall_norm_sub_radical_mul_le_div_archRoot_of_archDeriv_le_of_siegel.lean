-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/70c5d9b5-502a-502a-9427-2d50ad168a8d

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le
import Theorems.Thm_LanglandsTunnell_CubicInduction_conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 radicalP21 radicalP12 radicalP21_zero radicalP12_zero localMaximalCompact3 componentAt3 archComponent3 matrixFin_ext matrixAdele_ext LocalGL3 archPlaceComponent3 archRoot₁ archRoot₂ conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel"
namespace RaySupplyK1
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev M3 : Type := Matrix (Fin 3) (Fin 3) ℝ

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

def liftR : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Units.map (ofRealHom.mapMatrix (m := Fin 3)).toMonoidHom

theorem liftR_apply (g : GL (Fin 3) ℝ) (i j : Fin 3) :
    ((liftR g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      ofReal ((g : M3) i j) := rfl

theorem realGL_liftR (g : GL (Fin 3) ℝ) : realGL (liftR g) = g := by
  refine Units.ext ?_
  ext i j
  change realCoord (ofReal ((g : M3) i j)) = (g : M3) i j
  exact realCoord_ofReal _

theorem liftR_realGL (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) : liftR (realGL x) = x := by
  refine Units.ext ?_
  ext i j
  rw [liftR_apply]
  exact ofReal_realCoord _

def E : GL (Fin 3) ℝ →* G3 := (archInclN (Fin 3) ℚ).comp liftR

theorem E_apply (g : GL (Fin 3) ℝ) (i j : Fin 3) :
    ((E g : G3) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      ((ofReal ((g : M3) i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
          InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem archComponent3_E (g : GL (Fin 3) ℝ) : archComponent3 (𝓞 ℚ) ℚ (E g) = liftR g :=
  archComponentN_archInclN (Fin 3) ℚ (liftR g)

def toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h

@[scoped simp] theorem coe_toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : (toGL e h : M3) = Matrix.of e := rfl

theorem archRealLift3_eq_E (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    archRealLift3 e = E (toGL e h) := by
  have hmat : archRealMat3 e = ((E (toGL e h) : G3) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := rfl
  have hu : IsUnit (archRealMat3 e) := by rw [hmat]; exact Units.isUnit _
  unfold archRealLift3
  rw [dif_pos hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hmat])

theorem archRealLift3_one' : archRealLift3 (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = 1 := by
  have h : (Matrix.of fun i j : Fin 3 => if i = j then (1 : ℝ) else 0).det ≠ 0 := by
    rw [show (Matrix.of fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = 1 from by
      ext i j; simp [Matrix.one_apply]]
    simp
  rw [archRealLift3_eq_E _ h, ← map_one E]
  congr 1
  refine Units.ext ?_
  ext i j
  simp [toGL, Matrix.one_apply]

theorem archRealLift3_mul (e e' : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) (h' : (Matrix.of e').det ≠ 0) :
    archRealLift3 e * archRealLift3 e' = archRealLift3 (fun i j => (Matrix.of e * Matrix.of e') i j) := by
  have hh : (Matrix.of fun i j => (Matrix.of e * Matrix.of e') i j).det ≠ 0 := by
    rw [show (Matrix.of fun i j => (Matrix.of e * Matrix.of e') i j) = Matrix.of e * Matrix.of e' from rfl,
      Matrix.det_mul]
    exact mul_ne_zero h h'
  rw [archRealLift3_eq_E e h, archRealLift3_eq_E e' h', archRealLift3_eq_E _ hh, ← map_mul]
  congr 1
  exact Units.ext rfl

abbrev AM3 : Type := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)

theorem archInclN_coe_apply (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) (i j : Fin 3) :
    ((archInclN (Fin 3) ℚ x : G3) : AM3) i j =
      (((x : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
          InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem archInclN_mul_comm_of_archComponent3_eq_one (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) (h : G3)
    (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) : archInclN (Fin 3) ℚ x * h = h * archInclN (Fin 3) ℚ x := by
  set X : AM3 := ((archInclN (Fin 3) ℚ x : G3) : AM3) with hX
  set Hm : AM3 := ((h : G3) : AM3) with hHm
  have hXa : X.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = (x : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := by
    ext i j; rfl
  have hXf : X.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
    ext i j; rfl
  have hHa : Hm.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = 1 := by
    have := congrArg (fun k : GL (Fin 3) (InfiniteAdeleRing ℚ) => (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) hh
    exact this
  refine Units.ext ?_
  change X * Hm = Hm * X
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((X * Hm) i j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((Hm * X) i j)
    rw [← Matrix.map_apply (f := AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (M := X * Hm),
      ← Matrix.map_apply (f := AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (M := Hm * X), Matrix.map_mul, Matrix.map_mul,
      hXa, hHa, Matrix.mul_one, Matrix.one_mul]
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((X * Hm) i j) = AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((Hm * X) i j)
    rw [← Matrix.map_apply (f := AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (M := X * Hm),
      ← Matrix.map_apply (f := AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (M := Hm * X), Matrix.map_mul, Matrix.map_mul,
      hXf, Matrix.mul_one, Matrix.one_mul]

theorem E_mul_comm_of_archComponent3_eq_one (g : GL (Fin 3) ℝ) (h : G3) (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    E g * h = h * E g :=
  archInclN_mul_comm_of_archComponent3_eq_one (liftR g) h hh

abbrev Arr : Type := Fin 3 → Fin 3 → ℝ

def idA : Arr := fun a b => if a = b then (1 : ℝ) else 0

def El (i j : Fin 3) : Arr := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

def sgl (i j : Fin 3) (s : ℝ) : Arr := fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def mulA (e e' : Arr) : Arr := fun a b => (Matrix.of e * Matrix.of e') a b

theorem of_mulA (e e' : Arr) : Matrix.of (mulA e e') = Matrix.of e * Matrix.of e' := rfl

theorem of_idA : Matrix.of idA = (1 : M3) := by
  ext a b; simp [idA, Matrix.one_apply]

theorem det_idA : (Matrix.of idA).det ≠ 0 := by rw [of_idA, Matrix.det_one]; exact one_ne_zero

theorem sgl_eq (i j : Fin 3) (s : ℝ) : sgl i j s = idA + s • El i j := by
  funext a b
  simp only [sgl, idA, El, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem sgl_zero (i j : Fin 3) : sgl i j 0 = idA := by
  rw [sgl_eq, zero_smul, add_zero]

theorem mulA_idA (e : Arr) : mulA e idA = e := by
  have : Matrix.of (mulA e idA) = Matrix.of e := by rw [of_mulA, of_idA, Matrix.mul_one]
  exact this

theorem idA_mulA (e : Arr) : mulA idA e = e := by
  have : Matrix.of (mulA idA e) = Matrix.of e := by rw [of_mulA, of_idA, Matrix.one_mul]
  exact this

theorem mulA_add (e x y : Arr) : mulA e (x + y) = mulA e x + mulA e y := by
  have : Matrix.of (mulA e (x + y)) = Matrix.of (mulA e x) + Matrix.of (mulA e y) := by
    rw [of_mulA, of_mulA, of_mulA, show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add]
  exact this

theorem mulA_smul (e : Arr) (s : ℝ) (x : Arr) : mulA e (s • x) = s • mulA e x := by
  have : Matrix.of (mulA e (s • x)) = s • Matrix.of (mulA e x) := by
    rw [of_mulA, of_mulA, show Matrix.of (s • x) = s • Matrix.of x from rfl, Matrix.mul_smul]
  exact this

theorem add_mulA (x y e : Arr) : mulA (x + y) e = mulA x e + mulA y e := by
  have : Matrix.of (mulA (x + y) e) = Matrix.of (mulA x e) + Matrix.of (mulA y e) := by
    rw [of_mulA, of_mulA, of_mulA, show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.add_mul]
  exact this

theorem smul_mulA (s : ℝ) (x e : Arr) : mulA (s • x) e = s • mulA x e := by
  have : Matrix.of (mulA (s • x) e) = s • Matrix.of (mulA x e) := by
    rw [of_mulA, of_mulA, show Matrix.of (s • x) = s • Matrix.of x from rfl, Matrix.smul_mul]
  exact this

def mulRightL (K : Arr) : Arr →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => mulA e K
      map_add' := fun x y => add_mulA x y K
      map_smul' := fun s x => smul_mulA s x K }

@[scoped simp] theorem mulRightL_apply (K e : Arr) : mulRightL K e = mulA e K := rfl

def mulLeftL (K : Arr) : Arr →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => mulA K e
      map_add' := fun x y => mulA_add K x y
      map_smul' := fun s x => mulA_smul K s x }

@[scoped simp] theorem mulLeftL_apply (K e : Arr) : mulLeftL K e = mulA K e := rfl

theorem mulA_El (i j k l : Fin 3) : mulA (El i j) (El k l) = if j = k then El i l else 0 := by
  funext a b
  simp only [mulA, Matrix.mul_apply, Matrix.of_apply, El]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.sum_eq_single j]
    · by_cases ha : a = i <;> by_cases hb : b = l <;> simp [ha, hb, El]
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hjk]
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : a = i ∧ c = j
    · rw [if_pos h1, one_mul, if_neg]
      rintro ⟨hc, -⟩; exact hjk (h1.2.symm.trans hc)
    · rw [if_neg h1, zero_mul]

def U3 : Set Arr := {e | (Matrix.of e).det ≠ 0}

theorem continuous_det_of : Continuous fun e : Arr => (Matrix.of e).det := by
  have : Continuous fun e : Arr => Matrix.of e := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply j).comp (continuous_apply i)
  exact this.matrix_det

theorem isOpen_U3 : IsOpen U3 :=
  isOpen_ne_fun continuous_det_of continuous_const

theorem idA_mem_U3 : idA ∈ U3 := det_idA

theorem mulA_mem_U3 {e e' : Arr} (h : e ∈ U3) (h' : e' ∈ U3) : mulA e e' ∈ U3 := by
  change (Matrix.of (mulA e e')).det ≠ 0
  rw [of_mulA, Matrix.det_mul]; exact mul_ne_zero h h'

theorem det_sgl (i j : Fin 3) (s : ℝ) : (Matrix.of (sgl i j s)).det = if i = j then 1 + s else 1 := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, sgl]

theorem sgl_mem_U3 (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : sgl i j s ∈ U3 := by
  change (Matrix.of (sgl i j s)).det ≠ 0
  rw [det_sgl]
  split_ifs
  · have := abs_lt.mp hs
    intro h; linarith [this.1]
  · exact one_ne_zero

theorem eventually_sgl_mem_U3 (i j : Fin 3) : ∀ᶠ s in nhds (0 : ℝ), sgl i j s ∈ U3 := by
  have : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [this] with s hs
  exact sgl_mem_U3 i j (abs_lt.mpr hs)

def Φ (φ : G3 → ℂ) (g : G3) : Arr → ℂ := fun e => φ (g * archRealLift3 e)

theorem archRealLift3_idA : archRealLift3 idA = 1 := archRealLift3_one'

theorem Φ_idA (φ : G3 → ℂ) (g : G3) : Φ φ g idA = φ g := by
  simp only [Φ, archRealLift3_idA, mul_one]

theorem archDeriv_def (i j : Fin 3) (φ : G3 → ℂ) (g : G3) :
    archDeriv i j φ g = deriv (fun s : ℝ => φ (g * archRealLift3 (sgl i j s))) 0 := rfl

theorem contDiffAt_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Φ φ g) e :=
  (hφ g).contDiffAt (isOpen_U3.mem_nhds he)

theorem differentiableAt_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3) :
    DifferentiableAt ℝ (Φ φ g) e :=
  (contDiffAt_Φ hφ g he).differentiableAt (by simp)

theorem line_eventuallyEq (φ : G3 → ℂ) (g : G3) {e : Arr} (he : e ∈ U3) (i j : Fin 3) :
    (fun s : ℝ => φ (g * archRealLift3 e * archRealLift3 (sgl i j s))) =ᶠ[nhds 0]
      fun s => Φ φ g (e + s • mulA e (El i j)) := by
  filter_upwards [eventually_sgl_mem_U3 i j] with s hs
  have harr : (fun a b => (Matrix.of e * Matrix.of (sgl i j s)) a b) = e + s • mulA e (El i j) := by
    change mulA e (sgl i j s) = e + s • mulA e (El i j)
    rw [sgl_eq, mulA_add, mulA_smul, mulA_idA]
  change φ _ = φ _
  rw [mul_assoc, archRealLift3_mul e _ he hs, harr]

theorem hasDerivAt_line {φ : G3 → ℂ} {g : G3} {e : Arr} (he : e ∈ U3) (hd : DifferentiableAt ℝ (Φ φ g) e)
    (i j : Fin 3) :
    HasDerivAt (fun s : ℝ => φ (g * archRealLift3 e * archRealLift3 (sgl i j s)))
      (fderiv ℝ (Φ φ g) e (mulA e (El i j))) 0 := by
  refine HasDerivAt.congr_of_eventuallyEq ?_ (line_eventuallyEq φ g he i j)
  have hline : HasDerivAt (fun s : ℝ => e + s • mulA e (El i j)) (mulA e (El i j)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (mulA e (El i j))).const_add e
    simpa using this
  have h0 : e = (fun s : ℝ => e + s • mulA e (El i j)) 0 := by simp
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hd.hasFDerivAt hline h0
  exact hcomp

theorem archDeriv_apply_mul_lift {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3)
    (i j : Fin 3) :
    archDeriv i j φ (g * archRealLift3 e) = fderiv ℝ (Φ φ g) e (mulA e (El i j)) :=
  (hasDerivAt_line he (differentiableAt_Φ hφ g he) i j).deriv

theorem archDeriv_eq_fderiv {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) (i j : Fin 3) :
    archDeriv i j φ g = fderiv ℝ (Φ φ g) idA (El i j) := by
  have := archDeriv_apply_mul_lift hφ g idA_mem_U3 i j
  rwa [archRealLift3_idA, mul_one, idA_mulA] at this

theorem top_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact le_of_eq (by norm_cast)

theorem contDiffOn_fderiv_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => fderiv ℝ (Φ φ g) e) U3 :=
  (hφ g).fderiv_of_isOpen isOpen_U3 top_add_one_le

end LanglandsTunnell.CubicInduction.RaySupplyK1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 radicalP21 radicalP12 radicalP21_zero radicalP12_zero localMaximalCompact3 componentAt3 archComponent3 matrixFin_ext matrixAdele_ext LocalGL3 archPlaceComponent3 archRoot₁ archRoot₂ conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel"
namespace GammaAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix LanglandsTunnell.CubicInduction.RaySupplyK1

theorem adelicGL3_ext {g h : AdelicGL 3 (𝓞 ℚ) ℚ} (ha : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hf : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v g = componentAt3 (𝓞 ℚ) ℚ v h) : g = h := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ (matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun v => ?_)
  · ext i j
    have := congrArg (fun k : GL (Fin 3) (InfiniteAdeleRing ℚ) => (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j) ha
    exact this
  · ext i j
    have := congrArg (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) (hf v)
    exact this

theorem eq_archRealLift3_of_forall_componentAt3_eq_one (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ v : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ v g = 1) :
    g = archRealLift3 (fun i j => realCoord (((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)) := by
  set A := archComponent3 (𝓞 ℚ) ℚ g with hA
  set eA : Fin 3 → Fin 3 → ℝ := fun i j => realCoord ((A : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j) with heA
  have hofeA : Matrix.of eA = ((realGL A : GL (Fin 3) ℝ) : M3) := by
    ext i j; rfl
  have hdet : (Matrix.of eA).det ≠ 0 := by
    rw [hofeA]; exact (realGL A).isUnit.map Matrix.detMonoidHom |>.ne_zero
  have hlift : liftR (toGL eA hdet) = A := by
    refine Units.ext ?_
    ext i j
    rw [liftR_apply, coe_toGL, Matrix.of_apply]
    exact ofReal_realCoord _
  rw [archRealLift3_eq_E _ hdet]
  refine adelicGL3_ext ?_ (fun v => ?_)
  · rw [archComponent3_E, hlift]
  · rw [hg v]
    exact (componentAtN_archInclN (Fin 3) ℚ v (liftR (toGL eA hdet))).symm

end LanglandsTunnell.CubicInduction.GammaAux
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 radicalP21 radicalP12 radicalP21_zero radicalP12_zero localMaximalCompact3 componentAt3 archComponent3 matrixFin_ext matrixAdele_ext LocalGL3 archPlaceComponent3 archRoot₁ archRoot₂ conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel"
namespace GammaAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix LanglandsTunnell.CubicInduction.RaySupplyK1

section Generic
variable {A' B' : Type*} [CommRing A'] [CommRing B']

theorem map_upperUnipotent3 (f : A' →+* B') (x y z : A') :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3]

theorem map_radicalP21 (f : A' →+* B') (v : Fin 2 → A') :
    Matrix.GeneralLinearGroup.map f (radicalP21 v) = radicalP21 fun i => f (v i) := by
  simp [radicalP21, map_upperUnipotent3]

theorem map_radicalP12 (f : A' →+* B') (v : Fin 2 → A') :
    Matrix.GeneralLinearGroup.map f (radicalP12 v) = radicalP12 fun i => f (v i) := by
  simp [radicalP12, map_upperUnipotent3]
end Generic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"

theorem componentAt3_radical_archOnly (x y : AdeleRing (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p (radicalP21 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) = 1 ∧
    componentAt3 (𝓞 ℚ) ℚ p (radicalP12 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  have h21 := map_radicalP21 ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
    (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
  have h12 := map_radicalP12 ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
    (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ)
  have hz : (fun i : Fin 2 => ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      ((![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) i)) = 0 := by
    funext i
    fin_cases i <;> simp [AdelicLevel.adeleFin]  <;> rfl
  constructor
  · change Matrix.GeneralLinearGroup.map _ _ = 1
    rw [h21, hz, radicalP21_zero]
  · change Matrix.GeneralLinearGroup.map _ _ = 1
    rw [h12, hz, radicalP12_zero]

theorem det_one_add_smul_ne_zero {Y : Matrix (Fin 3) (Fin 3) ℝ} (hY : Y * Y = 0) (s : ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) + s • Y).det ≠ 0 := by
  intro h0
  have h2 : (s • Y) * (s • Y) = 0 := by rw [smul_mul_assoc, mul_smul_comm, hY, smul_zero, smul_zero]
  have hmul : ((1 : Matrix (Fin 3) (Fin 3) ℝ) + s • Y) * (1 - s • Y) = 1 := by
    rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, h2, sub_zero]
    abel
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem sum_abs_mul_mul_le (P Y Q : Matrix (Fin 3) (Fin 3) ℝ) (m : ℝ) (hm : ∀ k l, |Y k l| ≤ m) :
    ∑ i : Fin 3, ∑ j : Fin 3, |(P * Y * Q) i j| ≤
      m * ((∑ i : Fin 3, ∑ k : Fin 3, |P i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |Q l j|)) := by
  have hPY : ∀ i l, |(P * Y) i l| ≤ m * ∑ k : Fin 3, |P i k| := by
    intro i l
    rw [Matrix.mul_apply]
    calc |∑ k, P i k * Y k l| ≤ ∑ k, |P i k * Y k l| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |P i k| * |Y k l| := by simp_rw [abs_mul]
      _ ≤ ∑ k, |P i k| * m := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hm k l) (abs_nonneg _)
      _ = m * ∑ k, |P i k| := by rw [← Finset.sum_mul, mul_comm]
  have h1 : ∀ i j, |(P * Y * Q) i j| ≤ (m * ∑ k : Fin 3, |P i k|) * (∑ l : Fin 3, |Q l j|) := by
    intro i j
    rw [Matrix.mul_apply]
    calc |∑ l, (P * Y) i l * Q l j| ≤ ∑ l, |(P * Y) i l * Q l j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |(P * Y) i l| * |Q l j| := by simp_rw [abs_mul]
      _ ≤ ∑ l, (m * ∑ k, |P i k|) * |Q l j| :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hPY i l) (abs_nonneg _)
      _ = (m * ∑ k, |P i k|) * (∑ l, |Q l j|) := (Finset.mul_sum _ _ _).symm
  have hQ : (∑ l : Fin 3, ∑ j : Fin 3, |Q l j|) = ∑ j : Fin 3, ∑ l : Fin 3, |Q l j| := Finset.sum_comm
  rw [hQ]
  calc ∑ i : Fin 3, ∑ j : Fin 3, |(P * Y * Q) i j|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, (m * ∑ k : Fin 3, |P i k|) * (∑ l : Fin 3, |Q l j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ i : Fin 3, (m * ∑ k : Fin 3, |P i k|) * (∑ j : Fin 3, ∑ l : Fin 3, |Q l j|) :=
        Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = m * ((∑ i : Fin 3, ∑ k : Fin 3, |P i k|) * (∑ j : Fin 3, ∑ l : Fin 3, |Q l j|)) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]

end LanglandsTunnell.CubicInduction.GammaAux
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "WhittakerBlock.archDeriv AdelicGL upperUnipotent3 radicalP21 radicalP12 radicalP21_zero radicalP12_zero localMaximalCompact3 componentAt3 archComponent3 matrixFin_ext matrixAdele_ext LocalGL3 archPlaceComponent3 archRoot₁ archRoot₂ conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel"
namespace GammaAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix LanglandsTunnell.CubicInduction.RaySupplyK1

theorem norm_eq_abs_ext (a : (Rat.infinitePlace).Completion) :
    ‖a‖ = |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace a| := by
  rw [← Real.norm_eq_abs,
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
      (map_zero _)]

theorem continuous_of' : Continuous fun e : Arr => Matrix.of e :=
  continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i)

theorem continuousAt_inv_of {e : Arr} (he : (Matrix.of e).det ≠ 0) :
    ContinuousAt (fun e : Arr => (Matrix.of e)⁻¹) e := by
  have hdet : ContinuousAt Ring.inverse (Matrix.of e).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ he
  exact ContinuousAt.comp (f := fun e : Arr => Matrix.of e) (x := e)
    (continuousAt_matrix_inv (Matrix.of e) hdet) continuous_of'.continuousAt

theorem displacement_step (F : G3 → ℂ) (hF : IsArchSmooth3 F) (g u : G3)
    (hu : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p u = 1)
    (e : Arr) (he : (Matrix.of e).det ≠ 0) (m : ℝ)
    (hX2 : ((archPlaceComponent3 ℚ Rat.infinitePlace (g⁻¹ * u * g) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
        ((archPlaceComponent3 ℚ Rat.infinitePlace (g⁻¹ * u * g) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0)
    (hXb : ∀ i j : Fin 3, ‖((archPlaceComponent3 ℚ Rat.infinitePlace (g⁻¹ * u * g) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤ m)
    (B : ℝ) (T : Set Arr)
    (hT : ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : Matrix (Fin 3) (Fin 3) ℝ, Y * Y = 0 → (∀ i j, |Y i j| ≤ m) →
      (fun a b => ((1 + s • Y) * Matrix.of e) a b) ∈ T)
    (hB : ∀ e' ∈ T, ∀ i j : Fin 3, ‖archDeriv i j F (g * archRealLift3 e')‖ ≤ B) :
    ‖F (g * archRealLift3 e) - F (u * g * archRealLift3 e)‖ ≤
      m * ((∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|)) * B := by
  classical
  set q : G3 := g⁻¹ * u * g with hq
  have hqfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p q = 1 := by
    intro p; rw [hq, map_mul, map_mul, map_inv, hu p, mul_one, inv_mul_cancel]
  set Aq := archComponent3 (𝓞 ℚ) ℚ q with hAq
  set eQ : Arr := fun i j => realCoord (((Aq : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j) with heQ
  have hqL : q = archRealLift3 eQ := eq_archRealLift3_of_forall_componentAt3_eq_one q hqfin

  set ρ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace with hρ
  set X : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion :=
    (archPlaceComponent3 ℚ Rat.infinitePlace q : Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1 with hXdef
  set Y : Matrix (Fin 3) (Fin 3) ℝ := ρ.mapMatrix X with hYdef
  have hofeQ : Matrix.of eQ = 1 + Y := by
    have h1 : Matrix.of eQ = ρ.mapMatrix (archPlaceComponent3 ℚ Rat.infinitePlace q :
        Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) := by
      ext i j; rfl
    rw [h1, hYdef, hXdef, map_sub, map_one]; abel
  have hY2 : Y * Y = 0 := by rw [hYdef, ← map_mul, hX2, map_zero]
  have hYb : ∀ i j, |Y i j| ≤ m := by
    intro i j
    rw [hYdef, RingHom.mapMatrix_apply, Matrix.map_apply, ← norm_eq_abs_ext]
    exact hXb i j
  have hdeteQ : (Matrix.of eQ).det ≠ 0 := by
    rw [hofeQ, ← one_smul ℝ Y]; exact det_one_add_smul_ne_zero hY2 1

  have hprod : u * g * archRealLift3 e = g * archRealLift3 (fun a b => ((1 + Y) * Matrix.of e) a b) := by
    have h1 : u * g = g * q := by rw [hq]; group
    rw [h1, mul_assoc, hqL, archRealLift3_mul eQ e hdeteQ he, hofeQ]
  rw [hprod]

  have hmvt := norm_sub_le_sum_abs_mul_of_mul_self_eq_zero_of_archDeriv_le F hF g e he Y hY2 B
    (fun s hs i j => hB _ (hT s hs Y hY2 hYb) i j)
  refine hmvt.trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (hT 0 ⟨le_refl _, zero_le_one⟩ Y hY2 hYb) 0 0)
  exact mul_le_mul_of_nonneg_right (sum_abs_mul_mul_le _ Y _ m hYb) hB0

end LanglandsTunnell.CubicInduction.GammaAux
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction.RaySupplyK1"

open Matrix

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.RaySupplyK1 LanglandsTunnell.CubicInduction.GammaAux _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm.StandardKernel in

theorem solution
    (c C M' : ℝ) (hc0 : 0 < c) (hM' : 0 ≤ M')
    (Dc : Set (Fin 3 → Fin 3 → ℝ)) (hDc : IsCompact Dc) (hDcU : Dc ⊆ {e | (Matrix.of e).det ≠ 0}) :
    ∃ Dc' : Set (Fin 3 → Fin 3 → ℝ), IsCompact Dc' ∧ Dc' ⊆ {e | (Matrix.of e).det ≠ 0} ∧ Dc ⊆ Dc' ∧
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 F →
      ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        ∀ B : ℝ, (∀ e' ∈ Dc', ∀ i j : Fin 3,
            ‖WhittakerBlock.archDeriv i j F (n * t * k * WhittakerBlock.archRealLift3 e')‖ ≤ B) →
        ∀ e ∈ Dc, ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
          (∀ w : InfinitePlace ℚ, ‖x.1 w‖ ≤ M') → (∀ w : InfinitePlace ℚ, ‖y.1 w‖ ≤ M') →
          ∀ w : InfinitePlace ℚ,
            ‖F (n * t * k * WhittakerBlock.archRealLift3 e) -
                F (radicalP21 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * (n * t * k) *
                  WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / archRoot₂ ℚ w t ∧
            ‖F (n * t * k * WhittakerBlock.archRealLift3 e) -
                F (radicalP12 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * (n * t * k) *
                  WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / archRoot₁ ℚ w t := by
  classical

  set RY : ℝ := |2 * (1 + C) * max 1 c⁻¹ * M'| / c with hRY
  have hRY0 : 0 ≤ RY := div_nonneg (abs_nonneg _) hc0.le
  set Ybox : Set (Fin 3 → Fin 3 → ℝ) :=
    {yb | ∀ i j, |yb i j| ≤ RY} ∩ {yb | Matrix.of yb * Matrix.of yb = 0} with hYbox
  have hYc : IsCompact Ybox := by
    have hbox : {yb : Fin 3 → Fin 3 → ℝ | ∀ i j, |yb i j| ≤ RY} =
        Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (-RY) RY)) := by
      ext yb; simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
    have h1 : IsCompact {yb : Fin 3 → Fin 3 → ℝ | ∀ i j, |yb i j| ≤ RY} := by
      rw [hbox]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    refine h1.inter_right ?_
    exact isClosed_eq (continuous_of'.mul continuous_of') continuous_const

  set Φm : ℝ × ((Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)) → (Fin 3 → Fin 3 → ℝ) :=
    fun p => fun a b => ((1 + p.1 • Matrix.of p.2.1) * Matrix.of p.2.2) a b with hΦm
  have hΦc : Continuous Φm := by
    have : Continuous fun p : ℝ × ((Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)) =>
        (1 + p.1 • Matrix.of p.2.1) * Matrix.of p.2.2 :=
      ((continuous_const.add (continuous_fst.smul (continuous_of'.comp (continuous_fst.comp continuous_snd)))).mul
        (continuous_of'.comp (continuous_snd.comp continuous_snd)))
    exact this
  set Dc' : Set (Fin 3 → Fin 3 → ℝ) := Φm '' (Set.Icc (0 : ℝ) 1 ×ˢ (Ybox ×ˢ Dc)) with hDc'
  have hDc'c : IsCompact Dc' := (isCompact_Icc.prod (hYc.prod hDc)).image hΦc
  have hDc'U : Dc' ⊆ {e | (Matrix.of e).det ≠ 0} := by
    rintro _ ⟨⟨s, yb, e⟩, ⟨hs, hyb, he⟩, rfl⟩
    show (Matrix.of (fun a b => ((1 + s • Matrix.of yb) * Matrix.of e) a b)).det ≠ 0
    change ((1 + s • Matrix.of yb) * Matrix.of e).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (det_one_add_smul_ne_zero hyb.2 s) (hDcU he)
  have hzero : (fun _ _ => (0 : ℝ) : Fin 3 → Fin 3 → ℝ) ∈ Ybox := by
    refine ⟨fun i j => by simp [hRY0], ?_⟩
    show Matrix.of (fun _ _ => (0 : ℝ)) * Matrix.of (fun _ _ => (0 : ℝ)) = 0
    ext i j; simp [Matrix.mul_apply]
  have hDcDc' : Dc ⊆ Dc' := by
    intro e he
    refine ⟨(0, ((fun _ _ => (0 : ℝ)), e)), ⟨⟨le_refl _, zero_le_one⟩, hzero, he⟩, ?_⟩
    funext a b
    simp [hΦm]

  set S : (Fin 3 → Fin 3 → ℝ) → ℝ := fun e =>
    (∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|) with hS
  have hScont : ContinuousOn S Dc := by
    intro e he
    have hinv := continuousAt_inv_of (hDcU he)
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ ?_
    · refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun k _ => ?_
      exact ((continuous_apply k).continuousAt.comp ((continuous_apply i).continuousAt.comp hinv)).abs
    · refine tendsto_finset_sum _ fun l _ => tendsto_finset_sum _ fun j _ => ?_
      exact (((continuous_apply j).comp ((continuous_apply l).comp continuous_of')).continuousAt).abs
  obtain ⟨Kb, hKb⟩ := hDc.exists_bound_of_continuousOn hScont
  set K : ℝ := max Kb 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hSK : ∀ e ∈ Dc, S e ≤ K := fun e he =>
    ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hKb e he))).trans (le_max_left _ _)
  have hS0 : ∀ e, 0 ≤ S e := fun e => mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨Dc', hDc'c, hDc'U, hDcDc', |2 * (1 + C) * max 1 c⁻¹ * M'| * K, mul_nonneg (abs_nonneg _) hK0, ?_⟩
  intro F hF n t k hn ht hk harch B hB e he x y hx hy w
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  obtain ⟨hnw, htw, hr₁, hr₂, hKo⟩ := harch Rat.infinitePlace
  have hr₁0 : 0 < archRoot₁ ℚ Rat.infinitePlace t := hc0.trans_le hr₁
  have hr₂0 : 0 < archRoot₂ ℚ Rat.infinitePlace t := hc0.trans_le hr₂
  have hvb : ∀ i : Fin 2, ‖AdelicLevel.archEval ℚ Rat.infinitePlace (AdelicLevel.adeleArch (𝓞 ℚ) ℚ
      ((![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) i))‖ ≤ M' := by
    intro i
    fin_cases i
    · exact hx Rat.infinitePlace
    · exact hy Rat.infinitePlace
  obtain ⟨⟨hX2, hXb⟩, ⟨hX2', hXb'⟩⟩ :=
    conj_radical_sub_one_mul_self_eq_zero_and_norm_le_div_archRoot_of_siegel hc0 hnw htw hr₁ hr₂ hKo
      (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) hvb
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB e (hDcDc' he) 0 0)

  have hT : ∀ (root : ℝ), c ≤ root → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : Matrix (Fin 3) (Fin 3) ℝ,
      Y * Y = 0 → (∀ i j, |Y i j| ≤ 2 * (1 + C) * max 1 c⁻¹ * M' / root) →
      (fun a b => ((1 + s • Y) * Matrix.of e) a b) ∈ Dc' := by
    intro root hroot s hs Y hY2 hYb
    have hroot0 : 0 < root := hc0.trans_le hroot
    refine ⟨(s, ((fun a b => Y a b), e)), ⟨hs, ⟨fun i j => ?_, ?_⟩, he⟩, rfl⟩
    · calc |Y i j| ≤ 2 * (1 + C) * max 1 c⁻¹ * M' / root := hYb i j
        _ ≤ |2 * (1 + C) * max 1 c⁻¹ * M'| / root := div_le_div_of_nonneg_right (le_abs_self _) hroot0.le
        _ ≤ |2 * (1 + C) * max 1 c⁻¹ * M'| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc0 hroot
    · show Matrix.of (fun a b => Y a b) * Matrix.of (fun a b => Y a b) = 0
      exact hY2

  have hfin := fun p => componentAt3_radical_archOnly x y p

  have hstep := fun (u : AdelicGL 3 (𝓞 ℚ) ℚ) (hu : ∀ p, componentAt3 (𝓞 ℚ) ℚ p u = 1) (root : ℝ) (hroot : c ≤ root)
      (h2 : ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * u * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) *
        ((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * u * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) = 0)
      (hb : ∀ i j : Fin 3, ‖((archPlaceComponent3 ℚ Rat.infinitePlace ((n * t * k)⁻¹ * u * (n * t * k)) :
          Matrix (Fin 3) (Fin 3) Rat.infinitePlace.Completion) - 1) i j‖ ≤ 2 * (1 + C) * max 1 c⁻¹ * M' / root) =>
    displacement_step F hF (n * t * k) u hu e (hDcU he) (2 * (1 + C) * max 1 c⁻¹ * M' / root) h2 hb B Dc'
      (hT root hroot) hB
  have hfinal : ∀ root : ℝ, c ≤ root →
      2 * (1 + C) * max 1 c⁻¹ * M' / root *
          ((∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|)) * B ≤
        |2 * (1 + C) * max 1 c⁻¹ * M'| * K * B / root := by
    intro root hroot
    have hroot0 : 0 < root := hc0.trans_le hroot
    have h1 : 2 * (1 + C) * max 1 c⁻¹ * M' *
        ((∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|)) ≤
        |2 * (1 + C) * max 1 c⁻¹ * M'| * K :=
      mul_le_mul (le_abs_self _) (hSK e he) (hS0 e) (abs_nonneg _)
    have h2 : 2 * (1 + C) * max 1 c⁻¹ * M' / root *
        ((∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|)) * B =
        2 * (1 + C) * max 1 c⁻¹ * M' *
        ((∑ i : Fin 3, ∑ k : Fin 3, |(Matrix.of e)⁻¹ i k|) * (∑ l : Fin 3, ∑ j : Fin 3, |(Matrix.of e) l j|)) * B / root := by
      ring
    rw [h2]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hB0) hroot0.le
  constructor
  · exact (hstep _ (fun p => (hfin p).1) _ hr₂ hX2 hXb).trans (hfinal _ hr₂)
  · exact (hstep _ (fun p => (hfin p).2) _ hr₁ hX2' hXb').trans (hfinal _ hr₁)

end S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel (solution)
