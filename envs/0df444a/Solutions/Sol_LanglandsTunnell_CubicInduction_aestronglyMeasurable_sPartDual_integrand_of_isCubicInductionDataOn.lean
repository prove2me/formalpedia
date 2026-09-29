-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dbb64970-e0d1-55ed-bd15-a5ceff4e4070

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

import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

noncomputable section

namespace MeasSP31

open Topology

scoped instance instSecondCountableUnitsAdicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) :
    SecondCountableTopology (v.adicCompletion ℚ)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance instSecondCountableCompletion (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  show SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X] [SecondCountableTopology X] :
    SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance instSecondCountableUnitsInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing ℚ)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

theorem borelSpace_units_adicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    BorelSpace (v.adicCompletion ℚ)ˣ := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  have hb : LanglandsTunnell.TateLocal.localBorel ℚ v = borel (v.adicCompletion ℚ) :=
    (LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v).measurable_eq
  refine ⟨?_⟩
  show MeasurableSpace.comap Units.val (LanglandsTunnell.TateLocal.localBorel ℚ v) = borel (v.adicCompletion ℚ)ˣ
  rw [hb]
  conv_rhs => rw [(Units.isEmbedding_val₀ (G₀ := v.adicCompletion ℚ)).eq_induced]
  exact borel_comap.symm

theorem stronglyMeasurable_integral_of_continuous
    {G Y : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [SFinite ν] (F : G → Y → ℂ) (hF : Continuous fun p : G × Y => F p.1 p.2) :
    StronglyMeasurable fun g => ∫ y, F g y ∂ν := by
  have h : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable
  exact h.integral_prod_right'

section MatrixMaps

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_matrix_of_entries {X : Type*} [TopologicalSpace X] {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n A) (h : ∀ i j, Continuous fun x => f x i j) : Continuous f :=
  continuous_pi fun i => continuous_pi fun j => h i j

theorem continuous_lowerUnipotent21 : Continuous (lowerUnipotent21 : A → GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix_of_entries _ fun i j => ?_
    show Continuous fun x : A => (!![(1 : A), 0, 0; x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A) i j
    fin_cases i <;> fin_cases j <;> (simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
      <;> fun_prop)
  · refine continuous_matrix_of_entries _ fun i j => ?_
    show Continuous fun x : A => (!![(1 : A), 0, 0; -x, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) A) i j
    fin_cases i <;> fin_cases j <;> (simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
      <;> fun_prop)

theorem continuous_iotaGL_diagUnitGL2 : Continuous fun u : Aˣ => iotaGL (diagUnitGL2 u) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix_of_entries _ fun i j => ?_
    show Continuous fun u : Aˣ => embedMat2 (!![(u : A), 0; 0, 1] : Matrix (Fin 2) (Fin 2) A) i j
    fin_cases i <;> fin_cases j <;> (simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
      <;> first | exact Units.continuous_val | fun_prop)
  · refine continuous_matrix_of_entries _ fun i j => ?_
    show Continuous fun u : Aˣ => embedMat2 (!![((u⁻¹ : Aˣ) : A), 0; 0, 1] : Matrix (Fin 2) (Fin 2) A) i j
    fin_cases i <;> fin_cases j <;> (simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
      <;> first | exact Units.continuous_coe_inv | fun_prop)

theorem continuous_transposeInv3 : Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem continuous_dual_torus_unipotent {W : GL (Fin 3) A → ℂ} (hW : Continuous W) (g : GL (Fin 3) A) :
    Continuous fun p : Aˣ × A => dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) := by
  simp only [dualWhittakerFn3_apply]
  refine hW.comp (continuous_const.mul (continuous_transposeInv3.comp ?_))
  exact ((continuous_iotaGL_diagUnitGL2.comp continuous_fst).mul
    (continuous_lowerUnipotent21.comp continuous_snd)).mul continuous_const

end MatrixMaps

theorem continuous_of_open_stabiliser {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {W : G → ℂ} (hU : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g) :
    Continuous W := by
  obtain ⟨U, hUo, hUW⟩ := hU
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hev : ∀ᶠ h in nhds g, W h = W g := by
    have ho : IsOpen {h : G | g⁻¹ * h ∈ (U : Set G)} := hUo.preimage (continuous_const.mul continuous_id)
    have hg : g ∈ {h : G | g⁻¹ * h ∈ (U : Set G)} := by
      show g⁻¹ * g ∈ (U : Set G)
      rw [inv_mul_cancel]; exact U.one_mem
    filter_upwards [ho.mem_nhds hg] with h hh
    have := hUW (g⁻¹ * h) hh g
    rwa [mul_inv_cancel_left] at this
  exact (continuousAt_const.congr (hev.mono fun h hh => hh.symm) : ContinuousAt W g)

section Local

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem sFinite_selfDualHaarAt :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ w
    SFinite (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ w
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ w
  unfold LanglandsTunnell.TateLocal.selfDualHaarAt
  infer_instance

theorem continuous_modulus_units :
    Continuous fun t : (w.adicCompletion ℚ)ˣ => (LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) := by
  have : (fun t : (w.adicCompletion ℚ)ˣ => (LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ)) =
      fun t : (w.adicCompletion ℚ)ˣ => ‖((t : (w.adicCompletion ℚ)ˣ) : w.adicCompletion ℚ)‖ := by
    funext t
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ w, coe_nnnorm]
  rw [this]
  exact continuous_norm.comp Units.continuous_val

theorem stronglyMeasurable_localFactor (W : LocalGL3 w → ℂ)
    (hU : ∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧ ∀ k ∈ Uw, ∀ g : LocalGL3 w, W (g * k) = W g)
    (gw : LocalGL3 w) (s : ℂ) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ w
    StronglyMeasurable (fun t : (w.adicCompletion ℚ)ˣ =>
        (∫ x : w.adicCompletion ℚ,
            dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw)
              ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)) *
          ((LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ w
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ w
  haveI := borelSpace_units_adicCompletion w
  haveI := sFinite_selfDualHaarAt w
  have hW : Continuous W := continuous_of_open_stabiliser hU
  have h1 : StronglyMeasurable fun t : (w.adicCompletion ℚ)ˣ => ∫ x : w.adicCompletion ℚ,
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w) :=
    stronglyMeasurable_integral_of_continuous _ (fun t x => dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw))
      (continuous_dual_torus_unipotent hW gw)
  have h2 : Measurable fun t : (w.adicCompletion ℚ)ˣ =>
      ((LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) :=
    (Complex.continuous_ofReal.comp (continuous_modulus_units w)).measurable.pow_const _
  exact h1.mul h2.stronglyMeasurable

theorem stronglyMeasurable_localIntegral (W : LocalGL3 w → ℂ)
    (hU : ∃ Uw : Subgroup (LocalGL3 w), IsOpen (Uw : Set (LocalGL3 w)) ∧ ∀ k ∈ Uw, ∀ g : LocalGL3 w, W (g * k) = W g)
    (gw : LocalGL3 w) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ w
    StronglyMeasurable (fun t : (w.adicCompletion ℚ)ˣ =>
        ∫ x : w.adicCompletion ℚ,
            dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw)
              ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ w
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ w
  haveI := borelSpace_units_adicCompletion w
  haveI := sFinite_selfDualHaarAt w
  exact stronglyMeasurable_integral_of_continuous _
    (fun t x => dualWhittakerFn3 W (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * gw))
    (continuous_dual_torus_unipotent (continuous_of_open_stabiliser hU) gw)

end Local

section ArchFactor

open NumberField.InfiniteAdeleRing NumberField.mixedEmbedding
open scoped Classical

theorem continuous_transposeInv3_h1 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (transposeInv3 : GL (Fin 3) A → GL (Fin 3) A) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun g : GL (Fin 3) A => (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : GL (Fin 3) A => ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
    exact Units.continuous_val.matrix_transpose

theorem continuous_dualWhittakerFn3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (W : GL (Fin 3) A → ℂ) (hW : Continuous W) : Continuous (dualWhittakerFn3 W) := by
  show Continuous fun g : GL (Fin 3) A => W (longWeyl3 * transposeInv3 g)
  exact hW.comp ((continuous_const.mul continuous_transposeInv3_h1))

theorem ringEquiv_mixedSpace_symm_apply_of_isReal (K : Type*) [Field K] [NumberField K]
    (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsReal) :
    (ringEquiv_mixedSpace K).symm y v =
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
  classical
  have h : InfinitePlace.Completion.ringEquivRealOfIsReal hv ((ringEquiv_mixedSpace K).symm y v) =
      y.1 ⟨v, hv⟩ :=
    congrArg (fun z : mixedSpace K => z.1 ⟨v, hv⟩) ((ringEquiv_mixedSpace K).apply_symm_apply y)
  rw [← h, RingEquiv.symm_apply_apply]

theorem ringEquiv_mixedSpace_symm_apply_of_isComplex (K : Type*) [Field K] [NumberField K]
    (y : mixedSpace K) (v : InfinitePlace K) (hv : v.IsComplex) :
    (ringEquiv_mixedSpace K).symm y v =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (y.2 ⟨v, hv⟩) := by
  classical
  have h : InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
      ((ringEquiv_mixedSpace K).symm y v) = y.2 ⟨v, hv⟩ :=
    congrArg (fun z : mixedSpace K => z.2 ⟨v, hv⟩) ((ringEquiv_mixedSpace K).apply_symm_apply y)
  rw [← h, RingEquiv.symm_apply_apply]

theorem continuous_ringEquiv_mixedSpace_symm (K : Type*) [Field K] [NumberField K] :
    Continuous ((ringEquiv_mixedSpace K).symm : mixedSpace K → InfiniteAdeleRing K) := by
  classical
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · have : (fun y : mixedSpace K => (ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) :=
      funext fun y => ringEquiv_mixedSpace_symm_apply_of_isReal K y v hv
    rw [this]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have : (fun y : mixedSpace K => (ringEquiv_mixedSpace K).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) :=
      funext fun y => ringEquiv_mixedSpace_symm_apply_of_isComplex K y v hv'
    rw [this]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem stronglyMeasurable_archFactor [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (hW : Continuous W) (gA : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    StronglyMeasurable (fun u : (InfiniteAdeleRing ℚ)ˣ => ∫ y : mixedEmbedding.mixedSpace ℚ,
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 u) *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * gA)) := by
  classical
  refine stronglyMeasurable_integral_of_continuous (volume : Measure (mixedEmbedding.mixedSpace ℚ))
    (fun (u : (InfiniteAdeleRing ℚ)ˣ) (y : mixedEmbedding.mixedSpace ℚ) =>
      dualWhittakerFn3 W (iotaGL (diagUnitGL2 u) *
        lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * gA)) ?_
  refine (continuous_dualWhittakerFn3 W hW).comp ?_
  refine ((continuous_iotaGL_diagUnitGL2.comp continuous_fst).mul ?_).mul continuous_const
  exact continuous_lowerUnipotent21.comp ((continuous_ringEquiv_mixedSpace_symm ℚ).comp continuous_snd)

end ArchFactor

theorem archComponent3_iota (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.infPart a)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (embedMat2 (!![((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ), 0; 0, 1]) i j) =
    embedMat2 (!![((M4aHerbrand.infPart a : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0; 0, 1]) i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> rfl

theorem componentAt3_iota (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) = iotaGL (diagUnitGL2 (M4aHerbrand.finPart v a)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ))
      (embedMat2 (!![((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ), 0; 0, 1]) i j) =
    embedMat2 (!![((M4aHerbrand.finPart v a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, 1]) i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> rfl

theorem continuous_infPart : Continuous (M4aHerbrand.infPart : (AdeleRing (𝓞 ℚ) ℚ)ˣ → (InfiniteAdeleRing ℚ)ˣ) :=
  Continuous.units_map _ continuous_fst

theorem continuous_finPart (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous (M4aHerbrand.finPart v : (AdeleRing (𝓞 ℚ) ℚ)ˣ → (v.adicCompletion ℚ)ˣ) :=
  Continuous.units_map _ ((RestrictedProduct.continuous_eval v).comp continuous_snd)

end MeasSP31
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn.MeasSP31"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn.MeasSP31"

open MeasSP31 LanglandsTunnell in
attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
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
    ∀ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ → ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℂ),
      AEStronglyMeasurable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            (∏ v ∈ S,
              (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
               ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
                 (v.adicCompletion ℚ)) : ℂ)⁻¹ *
                 ∫ x : v.adicCompletion ℚ,
                   dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
                     lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
                     ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) *
            ((τ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        (NumberField.Idele.productMeasureData ℚ S).νS ∧
      AEStronglyMeasurable (fun u : (InfiniteAdeleRing ℚ)ˣ =>
          (∫ y : mixedEmbedding.mixedSpace ℚ,
              dualWhittakerFn3 X.whittakerArch (iotaGL (diagUnitGL2 u) *
                lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) *
            ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) ν_mul ∧
      ∀ w ∈ S,
        letI := LanglandsTunnell.TateLocal.localBorel ℚ w
        AEStronglyMeasurable (fun t : (w.adicCompletion ℚ)ˣ =>
            (∫ x : w.adicCompletion ℚ,
                dualWhittakerFn3 (X.whittakerLoc w) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x *
                  componentAt3 (𝓞 ℚ) ℚ w g) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w)) *
              ((LanglandsTunnell.TateLocal.modulus (t : w.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
          (Measure.comap Units.val (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ w))) := by
  intro τ hτ g s

  haveI hBI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := NumberField.Idele.borelSpace_ideleBorel ℚ
  refine ⟨?_, ?_, fun w hw => ?_⟩
  ·
    have hA : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        ∫ y : mixedEmbedding.mixedSpace ℚ,
          dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
            lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g) := by
      have e : (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          ∫ y : mixedEmbedding.mixedSpace ℚ,
            dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ (iotaGL (diagUnitGL2 a)) *
              lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) =
          (fun u : (InfiniteAdeleRing ℚ)ˣ => ∫ y : mixedEmbedding.mixedSpace ℚ,
            dualWhittakerFn3 X.whittakerArch (iotaGL (diagUnitGL2 u) *
              lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) * archComponent3 (𝓞 ℚ) ℚ g)) ∘
            M4aHerbrand.infPart := by
        funext a
        simp only [Function.comp_apply, archComponent3_iota]
      rw [e]
      exact (stronglyMeasurable_archFactor X.whittakerArch hArch.1.1 _).measurable.comp continuous_infPart.measurable
    have hL : ∀ v ∈ S, Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        (letI := LanglandsTunnell.TateLocal.localBorel ℚ v
         ((LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).real (v.adicCompletionIntegers ℚ : Set
           (v.adicCompletion ℚ)) : ℂ)⁻¹ *
           ∫ x : v.adicCompletion ℚ,
             dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
               lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
               ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) := by
      intro v hv
      letI := LanglandsTunnell.TateLocal.localBorel ℚ v
      haveI := borelSpace_units_adicCompletion v
      refine measurable_const.mul ?_
      have e : (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ∫ x : v.adicCompletion ℚ,
             dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v (iotaGL (diagUnitGL2 a)) *
               lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
               ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) =
          (fun t : (v.adicCompletion ℚ)ˣ => ∫ x : v.adicCompletion ℚ,
             dualWhittakerFn3 (X.whittakerLoc v) (iotaGL (diagUnitGL2 t) * lowerUnipotent21 x * componentAt3 (𝓞 ℚ) ℚ v g)
               ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) ∘ M4aHerbrand.finPart v := by
        funext a
        simp only [Function.comp_apply, componentAt3_iota]
      rw [e]
      exact (stronglyMeasurable_localIntegral v (X.whittakerLoc v) (hatS v hv).2.2.1 _).measurable.comp
        (continuous_finPart v).measurable
    have hP := Finset.measurable_prod S hL
    have hτm : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((τ a : ℂˣ) : ℂ) :=
      (Units.continuous_val.comp hτ.2.1).measurable
    have hN : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1) :=
      (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm ℚ)).measurable.pow_const _
    exact (((hA.mul hP).mul hτm).mul hN).aestronglyMeasurable
  ·
    have h1 := stronglyMeasurable_archFactor X.whittakerArch hArch.1.1 (archComponent3 (𝓞 ℚ) ℚ g)
    have h2' : Continuous fun u : (InfiniteAdeleRing ℚ)ˣ => ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) := by
      show Continuous fun u : (InfiniteAdeleRing ℚ)ˣ =>
        (((∏ v : InfinitePlace ℚ, ‖(u : InfiniteAdeleRing ℚ) v‖ ^ v.mult) : ℝ) : ℂ)
      refine Complex.continuous_ofReal.comp (continuous_finset_prod _ fun v _ => ?_)
      exact ((continuous_norm.comp ((continuous_apply v).comp Units.continuous_val)).pow _)
    have h2 : Measurable fun u : (InfiniteAdeleRing ℚ)ˣ => ((‖(u : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1) :=
      h2'.measurable.pow_const _
    exact (h1.mul h2.stronglyMeasurable).aestronglyMeasurable
  ·
    exact (stronglyMeasurable_localFactor w (X.whittakerLoc w) (hatS w hw).2.2.1 (componentAt3 (𝓞 ℚ) ℚ w g) s).aestronglyMeasurable

end S_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_aestronglyMeasurable_sPartDual_integrand_of_isCubicInductionDataOn (solution)
