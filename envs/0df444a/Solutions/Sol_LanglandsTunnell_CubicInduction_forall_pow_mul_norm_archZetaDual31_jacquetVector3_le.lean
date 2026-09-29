-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/121bb137-c78c-505c-9dee-7adba02b3178

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_dualWhittakerFn3_jacquetVector3_prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Classical

namespace DualStripDecay

private theorem isReal_place (v : InfinitePlace ℚ) : IsReal v := IsTotallyReal.isReal v

private def rc : InfiniteAdeleRing ℚ →+* ℝ :=
  (Completion.extensionEmbeddingOfIsReal (isReal_place (default : InfinitePlace ℚ))).comp
    (Pi.evalRingHom (fun v : InfinitePlace ℚ => v.Completion) default)

private theorem rc_apply (x : InfiniteAdeleRing ℚ) :
    rc x = Completion.extensionEmbeddingOfIsReal (isReal_place (default : InfinitePlace ℚ)) (x default) := rfl

private theorem norm_eq_abs_rc (x : InfiniteAdeleRing ℚ) : ‖x‖ = |rc x| := by
  have hiso := Completion.isometry_extensionEmbeddingOfIsReal (isReal_place (default : InfinitePlace ℚ))
  have hmap := hiso.norm_map_of_map_zero
    (map_zero (Completion.extensionEmbeddingOfIsReal (isReal_place (default : InfinitePlace ℚ)))) (x default)
  have h1 : mult (default : InfinitePlace ℚ) = 1 := mult_isReal ⟨default, isReal_place default⟩
  rw [InfiniteAdeleRing.norm_def, Fintype.prod_unique, h1, pow_one, rc_apply, ← Real.norm_eq_abs, hmap]

private theorem rc_unit_ne_zero (α : (InfiniteAdeleRing ℚ)ˣ) : rc (α : InfiniteAdeleRing ℚ) ≠ 0 := by
  intro h
  have h1 := congrArg rc α.mul_inv
  rw [map_mul, map_one, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem rc_coe_inv (α : (InfiniteAdeleRing ℚ)ˣ) :
    rc ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (rc (α : InfiniteAdeleRing ℚ))⁻¹ := by
  have h1 := congrArg rc α.inv_mul
  rw [map_mul, map_one] at h1
  exact eq_inv_of_mul_eq_one_left h1

private theorem norm_unit_ne_zero (α : (InfiniteAdeleRing ℚ)ˣ) : ‖(α : InfiniteAdeleRing ℚ)‖ ≠ 0 := by
  rw [norm_eq_abs_rc]
  exact abs_ne_zero.mpr (rc_unit_ne_zero α)

private theorem mixed_mul_eq_smul (y : mixedEmbedding.mixedSpace ℚ) (u : InfiniteAdeleRing ℚ) :
    y * InfiniteAdeleRing.ringEquiv_mixedSpace ℚ u = rc u • y := by
  refine Prod.ext ?_ ?_
  · funext v
    have hv : v = ⟨default, isReal_place default⟩ := Subsingleton.elim _ _
    subst hv
    simp only [Prod.fst_mul, Pi.mul_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.smul_fst,
      Pi.smul_apply, smul_eq_mul, rc_apply]
    ring
  · funext v
    exact absurd (isReal_place v.1) (not_isReal_iff_isComplex.mpr v.2)

private theorem mul_ringEquiv_eq_smul (u : InfiniteAdeleRing ℚ) :
    (fun y : mixedEmbedding.mixedSpace ℚ => y * InfiniteAdeleRing.ringEquiv_mixedSpace ℚ u) =
      fun y => rc u • y := by
  funext y
  exact mixed_mul_eq_smul y u

private theorem finrank_mixedSpace_rat : Module.finrank ℝ (mixedEmbedding.mixedSpace ℚ) = 1 := by
  rw [mixedEmbedding.finrank, Module.finrank_self]

private theorem map_mul_volume (α : (InfiniteAdeleRing ℚ)ˣ) :
    Measure.map (fun y : mixedEmbedding.mixedSpace ℚ =>
        y * InfiniteAdeleRing.ringEquiv_mixedSpace ℚ (α : InfiniteAdeleRing ℚ)) volume =
      ENNReal.ofReal |(rc (α : InfiniteAdeleRing ℚ))⁻¹| • volume := by
  rw [mul_ringEquiv_eq_smul]
  have h := Measure.map_addHaar_smul (volume : Measure (mixedEmbedding.mixedSpace ℚ)) (rc_unit_ne_zero α)
  rw [finrank_mixedSpace_rat, pow_one] at h
  convert h using 2

private theorem comp_symm_eq (u : InfiniteAdeleRing ℚ) :
    (fun x : InfiniteAdeleRing ℚ => x * u) ∘ (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm =
      (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm ∘
        (fun y : mixedEmbedding.mixedSpace ℚ => y * InfiniteAdeleRing.ringEquiv_mixedSpace ℚ u) := by
  funext y
  simp only [Function.comp_apply, map_mul, RingEquiv.symm_apply_apply]

section Pinned

variable [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]

private def nuPinned (c : ENNReal) : Measure (InfiniteAdeleRing ℚ) :=
  c • MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume

private scoped instance instSFiniteNuPinned (c : ENNReal) : SFinite (nuPinned c) := by
  unfold nuPinned
  infer_instance

private theorem map_mul_unit_nuPinned (c : ENNReal) (α : (InfiniteAdeleRing ℚ)ˣ) :
    Measure.map (fun x : InfiniteAdeleRing ℚ => x * (α : InfiniteAdeleRing ℚ)) (nuPinned c) =
      ENNReal.ofReal |(rc (α : InfiniteAdeleRing ℚ))⁻¹| • nuPinned c := by
  unfold nuPinned
  rw [Measure.map_smul, smul_comm]
  congr 1
  by_cases hmeas : AEMeasurable (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm
      (volume : Measure (mixedEmbedding.mixedSpace ℚ))
  · rw [AEMeasurable.map_map_of_aemeasurable (measurable_mul_const _).aemeasurable hmeas, comp_symm_eq,
      ← AEMeasurable.map_map_of_aemeasurable _ (measurable_mul_const _).aemeasurable, map_mul_volume,
      Measure.map_smul]
    rw [map_mul_volume]
    exact hmeas.smul_measure _
  · rw [Measure.map_of_not_aemeasurable hmeas, Measure.map_zero, smul_zero]

private def mulUnit (α : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ ≃ᵐ InfiniteAdeleRing ℚ where
  toEquiv := Units.mulRight α
  measurable_toFun := measurable_mul_const _
  measurable_invFun := measurable_mul_const _

private theorem integral_mul_inv_unit_nuPinned (c : ENNReal) (α : (InfiniteAdeleRing ℚ)ˣ)
    (F : InfiniteAdeleRing ℚ → ℂ) :
    ∫ x, F (x * ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)) ∂(nuPinned c) =
      ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) * ∫ x, F x ∂(nuPinned c) := by
  have h1 : ∫ x, F (x * ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)) ∂(nuPinned c) =
      ∫ y, F y ∂(Measure.map (mulUnit α⁻¹) (nuPinned c)) := by
    rw [(mulUnit α⁻¹).measurableEmbedding.integral_map]
    rfl
  have h2 : Measure.map (mulUnit α⁻¹) (nuPinned c) = ENNReal.ofReal |rc (α : InfiniteAdeleRing ℚ)| • nuPinned c := by
    have h3 := map_mul_unit_nuPinned c α⁻¹
    rw [rc_coe_inv, inv_inv] at h3
    exact h3
  rw [h1, h2, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), norm_eq_abs_rc]
  exact Complex.real_smul

end Pinned

section Shear

variable [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
  [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] mT [BorelSpace (InfiniteAdeleRing ℚ)ˣ] in
private theorem secondCountable_completion (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion :=
  (Completion.isometryEquivRealOfIsReal (isReal_place v)).toHomeomorph.secondCountableTopology

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] mT [BorelSpace (InfiniteAdeleRing ℚ)ˣ] in
private scoped instance secondCountable_ring : SecondCountableTopology (InfiniteAdeleRing ℚ) := by
  haveI : ∀ v : InfinitePlace ℚ, SecondCountableTopology v.Completion := secondCountable_completion
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] mT [BorelSpace (InfiniteAdeleRing ℚ)ˣ] in
private theorem continuous_rc : Continuous rc :=
  (Completion.isometry_extensionEmbeddingOfIsReal (isReal_place (default : InfinitePlace ℚ))).continuous.comp
    (continuous_apply (default : InfinitePlace ℚ))

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] mT [BorelSpace (InfiniteAdeleRing ℚ)ˣ] in
private theorem continuous_norm_ring : Continuous (fun x : InfiniteAdeleRing ℚ => ‖x‖) := by
  have h : (fun x : InfiniteAdeleRing ℚ => ‖x‖) = fun x => |rc x| := funext norm_eq_abs_rc
  rw [h]
  exact continuous_abs.comp continuous_rc

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] in
private theorem measurable_normUnit :
    Measurable (fun α : (InfiniteAdeleRing ℚ)ˣ => ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp (continuous_norm_ring.comp Units.continuous_val).measurable

omit mA [BorelSpace (InfiniteAdeleRing ℚ)] in
private theorem measurable_ofReal_normUnit :
    Measurable (fun α : (InfiniteAdeleRing ℚ)ˣ => ENNReal.ofReal ‖(α : InfiniteAdeleRing ℚ)‖) :=
  ENNReal.measurable_ofReal.comp (continuous_norm_ring.comp Units.continuous_val).measurable

private def shear (p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ) : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ :=
  (p.1, p.2 * (p.1 : InfiniteAdeleRing ℚ))

private theorem measurable_shear : Measurable shear :=
  measurable_fst.prodMk (measurable_snd.mul (Units.continuous_val.measurable.comp measurable_fst))

omit mT [BorelSpace (InfiniteAdeleRing ℚ)ˣ] in
private theorem map_mulUnit_nuPinned (c : ENNReal) (α : (InfiniteAdeleRing ℚ)ˣ) :
    Measure.map (mulUnit α) (nuPinned c) = ENNReal.ofReal |(rc (α : InfiniteAdeleRing ℚ))⁻¹| • nuPinned c :=
  map_mul_unit_nuPinned c α

private theorem quasiMeasurePreserving_shear (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (c : ENNReal) :
    Measure.QuasiMeasurePreserving shear (μ.prod (nuPinned c)) (μ.prod (nuPinned c)) := by
  refine ⟨measurable_shear, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply measurable_shear hs, Measure.prod_apply (measurable_shear hs)]
  rw [Measure.measure_prod_null hs] at hs0
  have key : (fun α : (InfiniteAdeleRing ℚ)ˣ => nuPinned c (Prod.mk α ⁻¹' (shear ⁻¹' s))) =ᵐ[μ] 0 := by
    filter_upwards [hs0] with α hα
    have hα' : nuPinned c (Prod.mk α ⁻¹' s) = 0 := hα
    change nuPinned c ((fun x : InfiniteAdeleRing ℚ => x * (α : InfiniteAdeleRing ℚ)) ⁻¹' (Prod.mk α ⁻¹' s)) = 0
    rw [← Measure.map_apply (measurable_mul_const _) (measurable_prodMk_left hs), map_mul_unit_nuPinned,
      Measure.smul_apply, hα', smul_zero]
  rw [lintegral_congr_ae key]
  simp

private theorem integrable_comp_shear_mul_norm (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (c : ENNReal)
    {K : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ → ℂ} (hK : Integrable K (μ.prod (nuPinned c))) :
    Integrable (fun p => K (shear p) * ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ)) (μ.prod (nuPinned c)) := by
  have hqmp := quasiMeasurePreserving_shear μ c
  have hKs : AEStronglyMeasurable (fun p => K (shear p)) (μ.prod (nuPinned c)) :=
    hK.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  refine ⟨hKs.mul (measurable_normUnit.comp measurable_fst).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpt : ∀ p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ,
      ‖K (shear p) * ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ)‖ₑ =
        ‖K (shear p)‖ₑ * ENNReal.ofReal ‖(p.1 : InfiniteAdeleRing ℚ)‖ := by
    intro p
    have h0 : (0 : ℝ) ≤ ‖(p.1 : InfiniteAdeleRing ℚ)‖ := by
      rw [norm_eq_abs_rc]
      exact abs_nonneg _
    rw [enorm_mul, ← ofReal_norm ((‖(p.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ), Complex.norm_real,
      Real.norm_of_nonneg h0]
  simp_rw [hpt]
  have hmeas : AEMeasurable (fun p : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
      ‖K (shear p)‖ₑ * ENNReal.ofReal ‖(p.1 : InfiniteAdeleRing ℚ)‖) (μ.prod (nuPinned c)) :=
    hKs.enorm.mul (measurable_ofReal_normUnit.comp measurable_fst).aemeasurable
  rw [lintegral_prod _ hmeas]
  dsimp only
  have inner : ∀ α : (InfiniteAdeleRing ℚ)ˣ,
      (∫⁻ x, ‖K (shear (α, x))‖ₑ * ENNReal.ofReal ‖(α : InfiniteAdeleRing ℚ)‖ ∂(nuPinned c)) =
        ∫⁻ y, ‖K (α, y)‖ₑ ∂(nuPinned c) := by
    intro α
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    have h1 : (∫⁻ x, ‖K (shear (α, x))‖ₑ ∂(nuPinned c)) =
        ∫⁻ y, ‖K (α, y)‖ₑ ∂(Measure.map (mulUnit α) (nuPinned c)) := by
      rw [lintegral_map_equiv]
      rfl
    have hc : ENNReal.ofReal |(rc (α : InfiniteAdeleRing ℚ))⁻¹| * ENNReal.ofReal ‖(α : InfiniteAdeleRing ℚ)‖ = 1 := by
      rw [norm_eq_abs_rc, ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv,
        inv_mul_cancel₀ (abs_ne_zero.mpr (rc_unit_ne_zero α)), ENNReal.ofReal_one]
    rw [h1, map_mulUnit_nuPinned, lintegral_smul_measure, smul_eq_mul, mul_assoc,
      mul_comm (∫⁻ y, ‖K (α, y)‖ₑ ∂(nuPinned c)), ← mul_assoc, hc, one_mul]
  simp_rw [inner]
  have htot : (∫⁻ z, ‖K z‖ₑ ∂(μ.prod (nuPinned c))) = ∫⁻ α, ∫⁻ y, ‖K (α, y)‖ₑ ∂(nuPinned c) ∂μ :=
    lintegral_prod _ hK.aestronglyMeasurable.enorm
  rw [← htot]
  exact hasFiniteIntegral_iff_enorm.mp hK.hasFiniteIntegral

end Shear

section GLAlgebra

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction"

variable {A : Type*} [CommRing A]

private theorem iotaGL_diagUnitGL2_mul_lowerUnipotent21 (α : Aˣ) (x : A) :
    iotaGL (diagUnitGL2 α) * lowerUnipotent21 x =
      lowerUnipotent21 (x * ((α⁻¹ : Aˣ) : A)) * iotaGL (diagUnitGL2 α) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

private theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change Matrix.transpose (((g * h)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
    Matrix.transpose ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) *
      Matrix.transpose ((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem coe_diagUnitGL2_inv (α : Aˣ) :
    (((diagUnitGL2 α)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((α⁻¹ : Aˣ) : A), 0; 0, 1] := rfl

private theorem transposeInv3_iotaGL_diagUnitGL2 (α : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 α)) = iotaGL (diagUnitGL2 α⁻¹) := by
  refine Units.ext ?_
  change Matrix.transpose (((iotaGL (diagUnitGL2 α))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, coe_diagUnitGL2_inv, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

private theorem dualWhittakerFn3_comp_mul_lowerUnipotent21_mul_iotaGL_diagUnitGL2_mul {R : Type*}
    (W : GL (Fin 3) A → R) (g₀ : GL (Fin 3) A) (x : A) (α : Aˣ) :
    dualWhittakerFn3 (fun h => W (h * g₀)) (lowerUnipotent21 x * iotaGL (diagUnitGL2 α) * weylPrime3) =
      W ((longWeyl3 * transposeInv3 (lowerUnipotent21 x) * (weylPrime3 * g₀)) *
        ((weylPrime3 * g₀)⁻¹ * iotaGL (diagUnitGL2 α⁻¹) * (weylPrime3 * g₀))) := by
  unfold dualWhittakerFn3
  beta_reduce
  rw [transposeInv3_mul, transposeInv3_mul, transposeInv3_weylPrime3, transposeInv3_iotaGL_diagUnitGL2]
  congr 1
  group

end GLAlgebra

section Unfolding

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction"

private theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1 := by
  refine Units.ext ?_
  change Matrix.transpose (((1 : GL (Fin 3) (InfiniteAdeleRing ℚ))⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = _
  rw [inv_one, Units.val_one, Matrix.transpose_one]

variable [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]

private theorem integral_torus_mul_unipotent (a : ℚ) (ν_add : Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (α : (InfiniteAdeleRing ℚ)ˣ) :
    ∫ x, W (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * g) ∂ν_add =
      ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) * ∫ x, W (lowerUnipotent21 x * iotaGL (diagUnitGL2 α) * g) ∂ν_add := by
  subst hν_add
  have h1 : ∀ x : InfiniteAdeleRing ℚ, W (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * g) =
      W (lowerUnipotent21 (x * ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)) * iotaGL (diagUnitGL2 α) *
        g) := by
    intro x
    rw [iotaGL_diagUnitGL2_mul_lowerUnipotent21]
  simp_rw [h1]
  exact integral_mul_inv_unit_nuPinned (ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2))) α
    (fun y => W (lowerUnipotent21 y * iotaGL (diagUnitGL2 α) * g))

variable [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]

omit [BorelSpace (InfiniteAdeleRing ℚ)] in
private theorem archZeta31_eq (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (ν : Measure (InfiniteAdeleRing ℚ))
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archZeta31 μ ν W σ s g =
      ∫ α : (InfiniteAdeleRing ℚ)ˣ,
        (∫ x : InfiniteAdeleRing ℚ, W (iotaGL (diagUnitGL2 α) * lowerUnipotent21 x * g) ∂ν) *
          ((σ α : ℂˣ) : ℂ) * ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1) ∂μ :=
  rfl

private theorem archZetaDual31_one_eq (μ : Measure (InfiniteAdeleRing ℚ)ˣ) (a : ℚ)
    (ν_add : Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) :
    archZetaDual31 μ ν_add W σ s 1 =
      ∫ α : (InfiniteAdeleRing ℚ)ˣ,
        (∫ x : InfiniteAdeleRing ℚ,
            dualWhittakerFn3 W (lowerUnipotent21 x * iotaGL (diagUnitGL2 α) * weylPrime3) ∂ν_add) *
          ((σ⁻¹ α : ℂˣ) : ℂ) * ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ s ∂μ := by
  unfold archZetaDual31
  rw [transposeInv3_one, mul_one, archZeta31_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  dsimp only
  rw [integral_torus_mul_unipotent a ν_add hν_add (dualWhittakerFn3 W) weylPrime3 α]
  have hne : ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_unit_ne_zero α)
  rw [Complex.cpow_sub s 1 hne, Complex.cpow_one]
  have key : ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) *
      (((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ s / ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ)) =
        ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ s :=
    mul_div_cancel₀ _ hne
  have e1 : ∀ p q r u : ℂ, p * q * r * (u / p) = q * r * (p * (u / p)) := fun p q r u => by ring
  rw [e1, key]

end Unfolding

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

noncomputable section

open MeasureTheory NumberField AutomorphicForm LanglandsTunnell.Converse

namespace DualStripDecay

section QuasiChar

p2m_open "LanglandsTunnell.Converse.ArchR"

private theorem quasiChar_mul (u : ℂ) (a : ZMod 2) (x y : ℝ) :
    quasiChar u a (x * y) = quasiChar u a x * quasiChar u a y := by
  unfold quasiChar
  rw [abs_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg y)]
  split_ifs with ha
  · ring
  · rw [sign_mul, SignType.coe_mul, Complex.ofReal_mul]
    ring

private theorem signType_sign_inv_eq (y : ℝ) : SignType.sign y⁻¹ = SignType.sign y := by
  rcases lt_trichotomy y 0 with h | h | h
  · rw [sign_neg (inv_lt_zero.mpr h), sign_neg h]
  · rw [h, inv_zero]
  · rw [sign_pos (inv_pos.mpr h), sign_pos h]

private theorem quasiChar_inv (u : ℂ) (a : ZMod 2) (y : ℝ) : quasiChar u a y⁻¹ = quasiChar (-u) a y := by
  unfold quasiChar
  have h0 : ((|y| : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (abs_nonneg y)]
    exact Real.pi_ne_zero.symm
  rw [abs_inv, Complex.ofReal_inv, Complex.inv_cpow_eq_ite, if_neg h0, ← Complex.cpow_neg, signType_sign_inv_eq]

private theorem quasiChar_mul_quasiChar (u u' : ℂ) (a a' : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    quasiChar u a y * quasiChar u' a' y = quasiChar (u + u') (a + a') y := by
  unfold quasiChar
  have hpos : (0 : ℝ) < |y| := abs_pos.mpr hy
  have hne : ((|y| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [Complex.cpow_add _ _ hne]
  have hsign : ((SignType.sign y : ℝ) : ℂ) * ((SignType.sign y : ℝ) : ℂ) = 1 := by
    rcases lt_or_gt_of_ne hy with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]
  have h2 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 a' with rfl | rfl <;> simp [h11] <;>
    first
    | ring1
    | linear_combination ((|y| : ℝ) : ℂ) ^ u * ((|y| : ℝ) : ℂ) ^ u' * hsign

end QuasiChar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section RealMatrix

p2m_open "AutomorphicForm.StandardKernel LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction"

private theorem realCoord_coe_inv (α : (InfiniteAdeleRing ℚ)ˣ) :
    realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = (realCoord (α : InfiniteAdeleRing ℚ))⁻¹ := by
  have h1 : realCoord ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) * realCoord (α : InfiniteAdeleRing ℚ) =
      1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h1

private theorem realMat_iotaGL_diagUnitGL2 (α : (InfiniteAdeleRing ℚ)ˣ) :
    realMat (iotaGL (diagUnitGL2 α)) = Matrix.diagonal ![realCoord (α : InfiniteAdeleRing ℚ), 1, 1] := by
  rw [realMat_eq, coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private def E11 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]]

private theorem diagonal_eq_one_add_smul (t : ℝ) :
    (Matrix.diagonal ![t, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ) = 1 + (t - 1) • E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, Matrix.diagonal]

private theorem realMat_point (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) (α : (InfiniteAdeleRing ℚ)ˣ) :
    realMat ((L * G) * (G⁻¹ * iotaGL (diagUnitGL2 α⁻¹) * G)) =
      (realMat L * realMat G - realMat L * E11 * realMat G) +
        (realCoord (α : InfiniteAdeleRing ℚ))⁻¹ • (realMat L * E11 * realMat G) := by
  have h1 : (L * G) * (G⁻¹ * iotaGL (diagUnitGL2 α⁻¹) * G) = L * iotaGL (diagUnitGL2 α⁻¹) * G := by group
  rw [h1, realMat_mul, realMat_mul, realMat_iotaGL_diagUnitGL2, realCoord_coe_inv, diagonal_eq_one_add_smul]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, sub_smul, one_smul]
  abel

end RealMatrix
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

noncomputable section

p2m_open "NumberField AutomorphicForm.StandardKernel LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction Topology"

namespace DualStripDecay

section Curve

private theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem realCoord_injective : Function.Injective realCoord := by
  intro x y h
  rw [← ofReal_realCoord x, ← ofReal_realCoord y, h]

private theorem realCoord_unit_ne_zero (α : (InfiniteAdeleRing ℚ)ˣ) : realCoord (α : InfiniteAdeleRing ℚ) ≠ 0 := by
  intro h
  have h1 : realCoord ((α : InfiniteAdeleRing ℚ) * ((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)) = 1 := by
    rw [Units.mul_inv, map_one]
  rw [map_mul, h, zero_mul] at h1
  exact zero_ne_one h1

private theorem ofReal_mul_ofReal_inv {y : ℝ} (hy : y ≠ 0) : ofReal y * ofReal y⁻¹ = 1 := by
  apply realCoord_injective
  rw [map_mul, realCoord_ofReal, realCoord_ofReal, map_one, mul_inv_cancel₀ hy]

private def unitCurve (y : ℝ) : (InfiniteAdeleRing ℚ)ˣ :=
  if hy : y = 0 then 1 else
    { val := ofReal y
      inv := ofReal y⁻¹
      val_inv := ofReal_mul_ofReal_inv hy
      inv_val := by rw [mul_comm]; exact ofReal_mul_ofReal_inv hy }

private theorem unitCurve_val {y : ℝ} (hy : y ≠ 0) :
    ((unitCurve y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = ofReal y := by
  simp only [unitCurve, dif_neg hy]

private theorem unitCurve_inv_val {y : ℝ} (hy : y ≠ 0) :
    (((unitCurve y)⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = ofReal y⁻¹ := by
  simp only [unitCurve, dif_neg hy]
  rfl

private theorem realCoord_unitCurve {y : ℝ} (hy : y ≠ 0) :
    realCoord ((unitCurve y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = y := by
  rw [unitCurve_val hy, realCoord_ofReal]

private theorem unitCurve_realCoord (α : (InfiniteAdeleRing ℚ)ˣ) :
    unitCurve (realCoord (α : InfiniteAdeleRing ℚ)) = α := by
  apply Units.ext
  rw [unitCurve_val (realCoord_unit_ne_zero α), ofReal_realCoord]

private theorem continuousOn_unitCurve : ContinuousOn unitCurve ({0} : Set ℝ)ᶜ := by
  rw [continuousOn_iff_continuous_restrict]
  have hne : ∀ y : (({0} : Set ℝ)ᶜ : Set ℝ), (y : ℝ) ≠ 0 := fun y h0 => y.2 (Set.mem_singleton_iff.mpr h0)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun y : (({0} : Set ℝ)ᶜ : Set ℝ) =>
      ((unitCurve (y : ℝ) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)
    refine (continuous_ofReal.comp continuous_subtype_val).congr fun y => ?_
    exact (unitCurve_val (hne y)).symm
  · show Continuous fun y : (({0} : Set ℝ)ᶜ : Set ℝ) =>
      (((unitCurve (y : ℝ))⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ)
    refine (continuous_ofReal.comp (continuous_subtype_val.inv₀ hne)).congr fun y => ?_
    exact (unitCurve_inv_val (hne y)).symm

private theorem continuous_iotaGL_diagUnitGL2 :
    Continuous fun α : (InfiniteAdeleRing ℚ)ˣ => (iotaGL (diagUnitGL2 α) : GL (Fin 3) (InfiniteAdeleRing ℚ)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun α : (InfiniteAdeleRing ℚ)ˣ => embedMat2 !![(α : InfiniteAdeleRing ℚ), 0; 0, 1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons] <;>
      first | exact Units.continuous_val | exact continuous_const
  · show Continuous fun α : (InfiniteAdeleRing ℚ)ˣ =>
      embedMat2 !![((α⁻¹ : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ), 0; 0, 1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons] <;>
      first | exact Units.continuous_coe_inv | exact continuous_const

private theorem continuousOn_directCurve (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ContinuousOn (fun y : ℝ => (iotaGL (diagUnitGL2 (unitCurve y)) : GL (Fin 3) (InfiniteAdeleRing ℚ)) * g)
      ({0} : Set ℝ)ᶜ :=
  (continuous_iotaGL_diagUnitGL2.comp_continuousOn continuousOn_unitCurve).mul continuousOn_const

private theorem eventually_directCurve_mem (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) {y₀ : ℝ} (hy₀ : y₀ ≠ 0)
    {U : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))} (hU : U ∈ 𝓝 ((iotaGL (diagUnitGL2 (unitCurve y₀)) : _) * g)) :
    ∀ᶠ y in 𝓝 y₀, (iotaGL (diagUnitGL2 (unitCurve y)) : GL (Fin 3) (InfiniteAdeleRing ℚ)) * g ∈ U := by
  have hopen : ({0} : Set ℝ)ᶜ ∈ 𝓝 y₀ := isOpen_compl_singleton.mem_nhds (by simpa using hy₀)
  exact ((continuousOn_directCurve g).continuousAt hopen).preimage_mem_nhds hU

private theorem continuousOn_pointCurve (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ContinuousOn (fun y : ℝ => (L * G) * (G⁻¹ * iotaGL (diagUnitGL2 (unitCurve y)⁻¹) * G)) ({0} : Set ℝ)ᶜ := by
  have h1 : ContinuousOn (fun y : ℝ => (unitCurve y)⁻¹) ({0} : Set ℝ)ᶜ :=
    continuous_inv.comp_continuousOn continuousOn_unitCurve
  have h2 : ContinuousOn (fun y : ℝ => (iotaGL (diagUnitGL2 (unitCurve y)⁻¹) : GL (Fin 3) (InfiniteAdeleRing ℚ)))
      ({0} : Set ℝ)ᶜ :=
    continuous_iotaGL_diagUnitGL2.comp_continuousOn h1
  exact continuousOn_const.mul ((continuousOn_const.mul h2).mul continuousOn_const)

private theorem eventually_pointCurve_mem (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) {y₀ : ℝ} (hy₀ : y₀ ≠ 0)
    {U : Set (GL (Fin 3) (InfiniteAdeleRing ℚ))}
    (hU : U ∈ 𝓝 ((L * G) * (G⁻¹ * iotaGL (diagUnitGL2 (unitCurve y₀)⁻¹) * G))) :
    ∀ᶠ y in 𝓝 y₀, (L * G) * (G⁻¹ * iotaGL (diagUnitGL2 (unitCurve y)⁻¹) * G) ∈ U := by
  have hopen : ({0} : Set ℝ)ᶜ ∈ 𝓝 y₀ := isOpen_compl_singleton.mem_nhds (by simpa using hy₀)
  have hc := (continuousOn_pointCurve L G).continuousAt hopen
  exact hc.preimage_mem_nhds hU

end Curve
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

noncomputable section

p2m_open "LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR Filter Topology"

namespace DualStripDecay

private def sgnFactor (a : ZMod 2) (y : ℝ) : ℂ := if a = 0 then 1 else ((SignType.sign y : ℝ) : ℂ)

private theorem sgnFactor_congr (a : ZMod 2) {y z : ℝ} (h : SignType.sign z = SignType.sign y) :
    sgnFactor a z = sgnFactor a y := by
  simp only [sgnFactor, h]

private theorem norm_sgnFactor (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) : ‖sgnFactor a y‖ = 1 := by
  unfold sgnFactor
  split_ifs
  · simp
  · rcases lt_or_gt_of_ne hy with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

private theorem quasiChar_eventuallyEq {y : ℝ} (hy : y ≠ 0) (u : ℂ) (a : ZMod 2) :
    quasiChar u a =ᶠ[𝓝 y] fun z : ℝ => ((|z| : ℝ) : ℂ) ^ u * sgnFactor a y := by
  rcases lt_or_gt_of_ne hy with h | h
  · filter_upwards [Iio_mem_nhds h] with z hz
    have hs : SignType.sign z = SignType.sign y := by rw [sign_neg (Set.mem_Iio.mp hz), sign_neg h]
    show ((|z| : ℝ) : ℂ) ^ u * sgnFactor a z = ((|z| : ℝ) : ℂ) ^ u * sgnFactor a y
    rw [sgnFactor_congr a hs]
  · filter_upwards [Ioi_mem_nhds h] with z hz
    have hs : SignType.sign z = SignType.sign y := by rw [sign_pos (Set.mem_Ioi.mp hz), sign_pos h]
    show ((|z| : ℝ) : ℂ) ^ u * sgnFactor a z = ((|z| : ℝ) : ℂ) ^ u * sgnFactor a y
    rw [sgnFactor_congr a hs]

private theorem ofReal_abs_eq {y : ℝ} (hy : y ≠ 0) :
    ((|y| : ℝ) : ℂ) = ((SignType.sign y : ℝ) : ℂ) * (y : ℂ) := by
  rw [← Complex.ofReal_mul]
  congr 1
  rcases lt_or_gt_of_ne hy with h | h
  · simp [abs_of_neg h, sign_neg h]
  · simp [abs_of_pos h, sign_pos h]

private theorem hasDerivAt_quasiChar (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (quasiChar u a) (u * quasiChar u a y / y) y := by
  have hpos : (0 : ℝ) < |y| := abs_pos.mpr hy
  have hslit : ((|y| : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hpos
  have hin : HasDerivAt (fun t : ℝ => (t : ℂ) ^ u) (u * ((|y| : ℝ) : ℂ) ^ (u - 1)) |y| :=
    (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
  have hcomp : HasDerivAt (fun z : ℝ => ((|z| : ℝ) : ℂ) ^ u)
      ((SignType.sign y : ℝ) • (u * ((|y| : ℝ) : ℂ) ^ (u - 1))) y :=
    HasDerivAt.scomp (x := y) hin (hasDerivAt_abs hy)
  have h2 : HasDerivAt (quasiChar u a) ((SignType.sign y : ℝ) • (u * ((|y| : ℝ) : ℂ) ^ (u - 1)) * sgnFactor a y) y :=
    (hcomp.mul_const (sgnFactor a y)).congr_of_eventuallyEq (quasiChar_eventuallyEq hy u a)
  convert h2 using 1
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  have hne : ((|y| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hpow : ((|y| : ℝ) : ℂ) ^ u = ((|y| : ℝ) : ℂ) ^ (u - 1) * ((|y| : ℝ) : ℂ) := by
    conv_lhs => rw [← sub_add_cancel u 1]
    rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
  rw [Complex.real_smul]
  show u * (((|y| : ℝ) : ℂ) ^ u * sgnFactor a y) / y = _
  rw [hpow, div_eq_iff hyc, ofReal_abs_eq hy]
  ring

private theorem norm_quasiChar (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) : ‖quasiChar u a y‖ = |y| ^ u.re := by
  have hpos : (0 : ℝ) < |y| := abs_pos.mpr hy
  show ‖((|y| : ℝ) : ℂ) ^ u * sgnFactor a y‖ = _
  rw [norm_mul, norm_sgnFactor a hy, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hpos]

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

noncomputable section

section TransportAndHaarScalar
open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
open MeasureTheory Set Topology

namespace AbsInvDensity

private noncomputable def nnDensity (y : ℝ) : NNReal := Real.toNNReal |y|⁻¹

private theorem measurable_nnDensity : Measurable nnDensity :=
  (measurable_abs.inv).real_toNNReal

private theorem ofReal_abs_inv_eq (y : ℝ) : ENNReal.ofReal |y|⁻¹ = (nnDensity y : ENNReal) := rfl

private theorem coe_nnDensity (y : ℝ) : (nnDensity y : ℝ) = |y|⁻¹ :=
  Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg y))

private theorem pos_of_map_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) : 0 < κ := by
  by_contra hle
  have h0 : ENNReal.ofReal κ = 0 := ENNReal.ofReal_eq_zero.2 (le_of_not_gt hle)
  have hmap : Measure.map T μ = 0 := by rw [hκ, h0, zero_smul]
  apply hμ
  rw [← Measure.measure_univ_eq_zero, ← Set.preimage_univ (f := T), ← Measure.map_apply hT MeasurableSet.univ, hmap]
  rfl

private theorem map_eq_smul_withDensity {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => (nnDensity y : ENNReal) := hκ

private theorem map_absolutelyContinuous {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) :
    Measure.map T μ ≪ (volume : Measure ℝ) := by
  rw [hκ]
  exact (withDensity_absolutelyContinuous _ _).smul_left (ENNReal.ofReal κ)

private theorem nnDensity_smul_eq (f : ℝ → ℂ) (y : ℝ) : nnDensity y • f y = f y * ((|y| : ℝ) : ℂ)⁻¹ := by
  change ((nnDensity y : ℝ)) • f y = f y * ((|y| : ℝ) : ℂ)⁻¹
  rw [Complex.real_smul, coe_nnDensity, Complex.ofReal_inv, mul_comm]

private theorem integral_comp_eq
    {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
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

private theorem integrable_comp_iff
    {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T) (κ : ℝ)
    (hκ : Measure.map T μ = ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹)
    (hμ : μ ≠ 0) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    Integrable (fun x => f (T x)) μ ↔ Integrable (fun y => f y * ((|y| : ℝ) : ℂ)⁻¹) volume := by
  have hpos : 0 < κ := pos_of_map_eq μ T hT κ hκ hμ
  have hf' : AEStronglyMeasurable f (Measure.map T μ) := hf.mono_ac (map_absolutelyContinuous μ T κ hκ)
  have h1 : Integrable (fun x => f (T x)) μ ↔ Integrable f (Measure.map T μ) :=
    (integrable_map_measure hf' hT.aemeasurable).symm
  rw [h1, map_eq_smul_withDensity μ T κ hκ,
    integrable_smul_measure (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top,
    integrable_withDensity_iff_integrable_smul measurable_nnDensity]
  exact integrable_congr (Filter.Eventually.of_forall fun y => nnDensity_smul_eq f y)

end AbsInvDensity
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

private theorem norm_component_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x Rat.infinitePlace‖ = |StandardKernel.realCoord x| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (Rat.isReal_infinitePlace)).norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  rw [← h, Real.norm_eq_abs]
  rfl

private theorem ideleChar_section_eq_quasiChar_realCoord
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((σ (E z) : ℂˣ) : ℂ) = ArchR.quasiChar t (e : ZMod 2) (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := by
  have hvr : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace
  let zv : ((Rat.infinitePlace).Completion)ˣ :=
    Units.map (Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).toMonoidHom z
  have hzv : ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) =
      (z : InfiniteAdeleRing ℚ) Rat.infinitePlace := rfl
  obtain ⟨h1, h2⟩ := hE z
  have h1' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (z : InfiniteAdeleRing ℚ) := by
    have h := congrArg Units.val h1
    first | (simpa [M4aHerbrand.infPart] using h) | (have h__ := h; simp [M4aHerbrand.infPart] at h__; exact h__) | (exact h)
  have h2' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h := congrArg Units.val h2
    first | (simpa [RatIdele.finPart] using h) | (have h__ := h; simp [RatIdele.finPart] at h__; exact h__) | (exact h)
  have hEz : E z = NumberField.TateGlobal.archUnitHom Rat.infinitePlace zv := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    · rw [h1']
      funext w
      obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      simp [NumberField.TateGlobal.archUnitHom, NumberField.AdelicVolume.archCentralUnit, hzv]
    · exact h2'
  have hloc := hσ Rat.infinitePlace hvr zv
  have hσE : ((σ (E z) : ℂˣ) : ℂ) =
      ((NumberField.TateGlobal.archLocalChar σ Rat.infinitePlace zv : ℂˣ) : ℂ) := by
    rw [hEz]; rfl
  rw [hσE, hloc]
  set r : ℝ := StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) with hr
  have hnorm : ‖((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion)‖ = |r| := by
    rw [hzv, hr]; exact norm_component_eq_abs_realCoord _
  have hemb : InfinitePlace.Completion.extensionEmbedding Rat.infinitePlace
      ((zv : ((Rat.infinitePlace).Completion)ˣ) : (Rat.infinitePlace).Completion) = (r : ℂ) := by
    rw [hzv, hr, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hvr]
    rfl
  have hmult : ((Rat.infinitePlace).mult : ℂ) = 1 := by
    have h : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, hvr⟩
    rw [h]; norm_num
  have hr0 : r ≠ 0 := (z.isUnit.map StandardKernel.realCoord).ne_zero
  rw [hnorm, hemb, hmult, one_mul]
  unfold ArchR.quasiChar
  congr 1
  have hcast : ((e : ZMod 2) = 0) ↔ Even e := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    norm_cast
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have habs : |r| = -r := abs_of_neg hneg
    have hsign : SignType.sign r = -1 := sign_neg hneg
    rw [habs, hsign]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]
    by_cases he : Even e
    · rw [he.neg_one_zpow, if_pos (hcast.mpr he)]
    · rw [(Int.not_even_iff_odd.mp he).neg_one_zpow, if_neg (fun h => he (hcast.mp h))]
      simp
  · have habs : |r| = r := abs_of_pos hpos
    have hsign : SignType.sign r = 1 := sign_pos hpos
    rw [habs, hsign, div_self (by exact_mod_cast hr0), one_zpow]
    split_ifs <;> simp

private theorem norm_eq_abs_realCoord (x : InfiniteAdeleRing ℚ) :
    ‖x‖ = |StandardKernel.realCoord x| := by
  rw [InfiniteAdeleRing.norm_def, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  have hm : (Rat.infinitePlace).mult = 1 := InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  rw [hd, hm, pow_one]
  exact norm_component_eq_abs_realCoord x

private theorem measurable_realCoord_units [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [BorelSpace (InfiniteAdeleRing ℚ)ˣ] :
    Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  have hc : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
      (continuous_apply Rat.infinitePlace)
  exact (hc.comp Units.continuous_val).measurable

section HaarScalar

p2m_open "MeasureTheory Measure MeasureTheory.Measure Topology Set"
open scoped ENNReal

namespace ArchUnitsHaar

private noncomputable def lineHaar : Measure ℝ := (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹

private theorem measurable_density : Measurable fun y : ℝ => ENNReal.ofReal |y|⁻¹ :=
  ENNReal.measurable_ofReal.comp continuous_abs.measurable.inv

private theorem lineHaar_singleton_zero : lineHaar ({0} : Set ℝ) = 0 := by
  rw [lineHaar]
  exact withDensity_absolutelyContinuous _ _ Real.volume_singleton

private theorem map_mul_left_lineHaar {c : ℝ} (hc : c ≠ 0) : Measure.map (c * ·) lineHaar = lineHaar := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul c) hs, lineHaar, withDensity_apply _ (measurable_const_mul c hs),
    withDensity_apply _ hs]

  rw [← lintegral_indicator (measurable_const_mul c hs), ← lintegral_indicator hs]
  have key : ∀ y : ℝ, ((c * ·) ⁻¹' s).indicator (fun y : ℝ => ENNReal.ofReal |y|⁻¹) y =
      ENNReal.ofReal |c| * s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) := by
    intro y
    by_cases hy : c * y ∈ s
    · rw [indicator_of_mem (show y ∈ (c * ·) ⁻¹' s from hy), indicator_of_mem hy, ← ENNReal.ofReal_mul (abs_nonneg c),
        abs_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]
    · rw [indicator_of_notMem (show y ∉ (c * ·) ⁻¹' s from hy), indicator_of_notMem hy, mul_zero]
  simp_rw [key]
  have hmeas : Measurable (s.indicator fun z : ℝ => ENNReal.ofReal |z|⁻¹) := measurable_density.indicator hs
  have hmeas' : Measurable fun y : ℝ => s.indicator (fun z : ℝ => ENNReal.ofReal |z|⁻¹) (c * y) :=
    hmeas.comp (measurable_const_mul c)
  rw [lintegral_const_mul _ hmeas']

  have hsub := lintegral_map (μ := (volume : Measure ℝ)) hmeas (measurable_const_mul c)
  simp only [Real.map_volume_mul_left hc, lintegral_smul_measure, smul_eq_mul] at hsub
  rw [← hsub, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg c), abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hc),
    ENNReal.ofReal_one, one_mul]

section Group

variable {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] {e : G → ℝ}

private noncomputable def pullback (e : G → ℝ) : Measure G := Measure.comap e lineHaar

private theorem pullback_apply (he : IsOpenEmbedding e) (s : Set G) : pullback e s = lineHaar (e '' s) :=
  he.measurableEmbedding.comap_apply _ _

private theorem pullback_isFiniteMeasureOnCompacts (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsFiniteMeasureOnCompacts (pullback e) := by
  refine ⟨fun K hK => ?_⟩
  rw [pullback_apply he]
  have hK' : IsCompact (e '' K) := hK.image he.continuous

  rcases (e '' K).eq_empty_or_nonempty with h | h
  · rw [h, measure_empty]; exact ENNReal.zero_lt_top
  obtain ⟨y₀, hy₀K, hy₀⟩ := hK'.exists_isMinOn h continuous_abs.continuousOn
  obtain ⟨g₀, -, rfl⟩ := hy₀K
  have hpos : 0 < |e g₀| := abs_pos.mpr (hne g₀)
  calc lineHaar (e '' K) = ∫⁻ y in e '' K, ENNReal.ofReal |y|⁻¹ := withDensity_apply _ hK'.measurableSet
    _ ≤ ∫⁻ _ in e '' K, ENNReal.ofReal |e g₀|⁻¹ := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        exact ENNReal.ofReal_le_ofReal (inv_anti₀ hpos (hy₀ hy))
    _ = ENNReal.ofReal |e g₀|⁻¹ * volume (e '' K) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top

private theorem pullback_isOpenPosMeasure (he : IsOpenEmbedding e) (hne : ∀ g : G, e g ≠ 0) :
    IsOpenPosMeasure (pullback e) := by
  refine ⟨fun U hU hUne => ?_⟩
  rw [pullback_apply he, lineHaar, Ne, withDensity_apply_eq_zero measurable_density]
  have hopen : IsOpen (e '' U) := he.isOpenMap U hU
  have hsub : e '' U ⊆ {y : ℝ | ENNReal.ofReal |y|⁻¹ ≠ 0} := by
    rintro _ ⟨g, -, rfl⟩
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (abs_pos.mpr (hne g)))).ne'
  rw [inter_eq_self_of_subset_right hsub]
  exact hopen.measure_ne_zero volume (hUne.image e)

private theorem pullback_isMulLeftInvariant [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsMulLeftInvariant (pullback e) := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hg : Measurable (g * ·) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hg hs, pullback_apply he, pullback_apply he]
  have himage : e '' ((g * ·) ⁻¹' s) = (e g * ·) ⁻¹' (e '' s) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x, hx, hmul g x⟩
    · rintro ⟨z, hz, hzy⟩

      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · have h1 : e g * e (g⁻¹ * z) = e z := by rw [← hmul, mul_inv_cancel_left]
        have h2 : e g * e (g⁻¹ * z) = e g * y := by rw [h1, hzy]
        exact mul_left_cancel₀ (hne g) h2
  rw [himage, ← Measure.map_apply (measurable_const_mul (e g)) (he.measurableEmbedding.measurableSet_image' hs),
    map_mul_left_lineHaar (hne g)]

private theorem pullback_isHaarMeasure [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) : IsHaarMeasure (pullback e) := by
  haveI := pullback_isFiniteMeasureOnCompacts he hne
  haveI := pullback_isMulLeftInvariant he hmul hne
  haveI := pullback_isOpenPosMeasure he hne
  exact IsHaarMeasure.mk

private theorem map_pullback (he : IsOpenEmbedding e) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e) :
    Measure.map e (pullback e) = lineHaar := by
  rw [pullback, he.measurableEmbedding.map_comap]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  refine measure_mono_null ?_ lineHaar_singleton_zero
  intro y hy
  rw [mem_singleton_iff]
  by_contra h0
  exact hy (hrange y h0)

private theorem exists_map_eq_smul [Group G] [IsTopologicalGroup G] (he : IsOpenEmbedding e)
    (hmul : ∀ g h : G, e (g * h) = e g * e h) (hne : ∀ g : G, e g ≠ 0) (hrange : ∀ y : ℝ, y ≠ 0 → y ∈ range e)
    (ν : Measure G) [ν.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧ Measure.map e ν = ENNReal.ofReal κ • lineHaar := by
  haveI : LocallyCompactSpace G := he.locallyCompactSpace
  haveI : SecondCountableTopology G := he.isEmbedding.secondCountableTopology
  haveI : IsHaarMeasure (pullback e) := pullback_isHaarMeasure he hmul hne
  obtain ⟨r, hr, hν⟩ : ∃ r : NNReal, 0 < r ∧ ν = r • pullback e :=
    ⟨_, haarScalarFactor_pos_of_isHaarMeasure ν (pullback e), isMulLeftInvariant_eq_smul ν (pullback e)⟩
  refine ⟨(r : ℝ), NNReal.coe_pos.mpr hr, ?_⟩
  rw [ENNReal.ofReal_coe_nnreal, hν, Measure.map_smul, map_pullback he hrange]
  exact (Measure.coe_nnreal_smul r lineHaar).symm

end Group
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end ArchUnitsHaar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end HaarScalar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace DirectArchZetaBound

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem continuous_realCoord : Continuous (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private noncomputable def realCoordEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := StandardKernel.realCoord
  invFun := StandardKernel.ofReal
  left_inv := StandardKernel.ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul StandardKernel.realCoord
  map_add' := map_add StandardKernel.realCoord

private noncomputable def unitsHomeomorph : (InfiniteAdeleRing ℚ)ˣ ≃ₜ ℝˣ where
  toEquiv := (Units.mapEquiv realCoordEquiv.toMulEquiv).toEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨continuous_realCoord.comp Units.continuous_val, continuous_realCoord.comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨StandardKernel.continuous_ofReal.comp Units.continuous_val,
      StandardKernel.continuous_ofReal.comp Units.continuous_coe_inv⟩

private theorem unitsHomeomorph_apply_val (z : (InfiniteAdeleRing ℚ)ˣ) :
    ((unitsHomeomorph z : ℝˣ) : ℝ) = StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  rfl

private theorem isOpenEmbedding_realCoord_units :
    IsOpenEmbedding fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
  Units.isOpenEmbedding_val.comp unitsHomeomorph.isOpenEmbedding

private theorem realCoord_units_mul (z w : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord ((z * w : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) =
      StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) * StandardKernel.realCoord (w : InfiniteAdeleRing ℚ) := by
  rw [Units.val_mul, map_mul]

private theorem realCoord_units_ne_zero (z : (InfiniteAdeleRing ℚ)ˣ) :
    StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) ≠ 0 :=
  (z.isUnit.map StandardKernel.realCoord).ne_zero

private theorem realCoord_units_range (y : ℝ) (hy : y ≠ 0) :
    y ∈ Set.range fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) := by
  refine ⟨unitsHomeomorph.symm (Units.mk0 y hy), ?_⟩
  show ((unitsHomeomorph (unitsHomeomorph.symm (Units.mk0 y hy)) : ℝˣ) : ℝ) = y
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem exists_haarScalar [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      Measure.map (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
        ENNReal.ofReal κ • (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹ :=
  ArchUnitsHaar.exists_map_eq_smul isOpenEmbedding_realCoord_units realCoord_units_mul realCoord_units_ne_zero
    realCoord_units_range ν_mul

end DirectArchZetaBound
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end TransportAndHaarScalar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section MellinAndStrip
open MeasureTheory Set Filter Topology

namespace MellinByParts

private theorem smul_div_cast (g : ℝ → ℂ) (u : ℝ) (hu : 0 < u) :
    ((u ^ 2)⁻¹ : ℝ) • (g u⁻¹ / ((u⁻¹ : ℝ) : ℂ)) = g u⁻¹ / (u : ℂ) := by
  simp only [Complex.real_smul]
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  push_cast
  field_simp

private theorem tendsto_zero_atTop {g g' : ℝ → ℂ} (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Ioi 0)) (hg : IntegrableOn (fun y => g y / y) (Ioi 0)) :
    Tendsto g atTop (𝓝 0) := by
  have hL := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hderiv hg'
  set L := limUnder atTop g
  by_contra hne
  have hL0 : L ≠ 0 := by
    rintro h
    exact hne (h ▸ hL)
  have hpos : 0 < ‖L‖ / 2 := by
    have := norm_pos_iff.2 hL0
    linarith
  have hev : ∀ᶠ y in atTop, ‖L‖ / 2 ≤ ‖g y‖ := by
    have h1 : ∀ᶠ y in atTop, ‖g y - L‖ < ‖L‖ / 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hL).eventually (gt_mem_nhds hpos)
      exact this
    filter_upwards [h1] with y hy
    have := norm_sub_norm_le L (g y)
    rw [norm_sub_rev] at hy
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop (1 : ℝ)))
  have hT1 : 1 ≤ T := (hT T le_rfl).2
  have hint : IntegrableOn (fun y : ℝ => ‖L‖ / 2 * y⁻¹) (Ioi T) := by
    refine Integrable.mono' ((hg.mono_set (Ioi_subset_Ioi (by linarith))).norm) ?_ ?_
    · exact (measurable_const.mul measurable_inv).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun y hy => ?_
      have hTy : T ≤ y := le_of_lt hy
      have hy0 : 0 < y := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy0, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hT y hTy).1 hy0.le
  have hint' : IntegrableOn (fun y : ℝ => y⁻¹) (Ioi T) := by
    refine IntegrableOn.congr_fun (hint.const_mul (‖L‖ / 2)⁻¹) (fun y _ => ?_) measurableSet_Ioi
    show (‖L‖ / 2)⁻¹ * (‖L‖ / 2 * y⁻¹) = y⁻¹
    field_simp
  exact not_integrableOn_Ioi_inv hint'

private theorem tendsto_zero_nhdsGT {g g' : ℝ → ℂ} (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (g' x) x)
    (hg' : IntegrableOn g' (Ioi 0)) (hg : IntegrableOn (fun y => g y / y) (Ioi 0)) :
    Tendsto g (𝓝[>] 0) (𝓝 0) := by
  have hderiv' : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u : ℝ => g u⁻¹) ((-(u ^ 2)⁻¹) • g' u⁻¹) u :=
    fun u hu => (hderiv u⁻¹ (Set.mem_Ioi.2 (inv_pos.2 hu))).scomp u (hasDerivAt_inv (ne_of_gt hu))
  have A : IntegrableOn (fun u : ℝ => (-(u ^ 2)⁻¹) • g' u⁻¹) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_rpow_iff g' (p := (-1 : ℝ)) (by norm_num)).2 hg'
    refine h.neg.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := hu
    simp only [Pi.neg_apply, abs_neg, abs_one, one_mul, Real.rpow_neg_one]
    rw [(by norm_num : (-1 : ℝ) - 1 = -(2 : ℝ)), Real.rpow_neg hu0.le, Real.rpow_two]
    exact (neg_smul _ _).symm
  have B : IntegrableOn (fun u : ℝ => g u⁻¹ / u) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_rpow_iff (fun y => g y / y) (p := (-1 : ℝ)) (by norm_num)).2 hg
    refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := hu
    simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one]
    rw [(by norm_num : (-1 : ℝ) - 1 = -(2 : ℝ)), Real.rpow_neg hu0.le, Real.rpow_two]
    exact smul_div_cast g u hu0
  have hinf := tendsto_zero_atTop hderiv' A B
  have := hinf.comp tendsto_inv_nhdsGT_zero
  simpa [Function.comp_def, inv_inv] using this

private theorem half {f f₁ w : ℝ → ℂ} {c : ℂ}
    (hf : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt f (f₁ y / y) y) (hw : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt w (c * w y / y) y)
    (hfw : IntegrableOn (fun y => f y * w y) (Ioi 0)) (hf₁w : IntegrableOn (fun y => f₁ y * w y) (Ioi 0)) :
    (c + 1) * ∫ y in Ioi 0, f y * w y = -∫ y in Ioi 0, f₁ y * w y := by
  set G : ℝ → ℂ := fun y => f y * w y * y with hGdef
  set G' : ℝ → ℂ := fun y => f₁ y * w y + (c + 1) * (f y * w y) with hG'def
  have hG : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt G (G' y) y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hy)
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      first | (simpa using (Complex.ofRealCLM.hasDerivAt (x := y))) | (have h__ := (Complex.ofRealCLM.hasDerivAt (x := y)); simp at h__; exact h__) | (exact (Complex.ofRealCLM.hasDerivAt (x := y)))
    have h := ((hf y hy).mul (hw y hy)).mul hid
    refine h.congr_deriv ?_
    simp only [hG'def, Pi.mul_apply]
    field_simp
    ring
  have hG'int : IntegrableOn G' (Ioi 0) := hf₁w.add (hfw.const_mul (c + 1))
  have hGdiv : IntegrableOn (fun y => G y / y) (Ioi 0) := by
    refine hfw.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hy)
    simp only [hGdef]
    field_simp
  have hinf : Tendsto G atTop (𝓝 0) := tendsto_zero_atTop hG hG'int hGdiv
  have h0 : Tendsto G (𝓝[>] 0) (𝓝 0) := tendsto_zero_nhdsGT hG hG'int hGdiv
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hG0]
    exact h0
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hcont hG hG'int hinf
  rw [hG0, sub_zero] at key
  have hsplit : ∫ y in Ioi 0, G' y = (∫ y in Ioi 0, f₁ y * w y) + (c + 1) * ∫ y in Ioi 0, f y * w y := by
    simp only [hG'def]
    rw [integral_add hf₁w (hfw.const_mul (c + 1))]
    congr 1
    exact integral_const_mul (c + 1) _
  rw [hsplit] at key
  linear_combination key

private theorem whole {f f₁ w : ℝ → ℂ} {c : ℂ}
    (hf : ∀ y : ℝ, y ≠ 0 → HasDerivAt f (f₁ y / y) y) (hw : ∀ y : ℝ, y ≠ 0 → HasDerivAt w (c * w y / y) y)
    (hfw : Integrable (fun y => f y * w y)) (hf₁w : Integrable (fun y => f₁ y * w y)) :
    (c + 1) * ∫ y, f y * w y = -∫ y, f₁ y * w y := by
  have hp := half (fun y hy => hf y (ne_of_gt hy)) (fun y hy => hw y (ne_of_gt hy)) hfw.integrableOn
    hf₁w.integrableOn
  have hn := half (f := fun y => f (-y)) (f₁ := fun y => f₁ (-y)) (w := fun y => w (-y)) (c := c)
    (fun y hy => by
      have hy' : -y ≠ 0 := neg_ne_zero.2 (ne_of_gt hy)
      have h := (hf (-y) hy').scomp y (hasDerivAt_neg y)
      refine h.congr_deriv ?_
      have : ((-y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy'
      push_cast at this ⊢
      rw [neg_one_smul, div_neg, neg_neg])
    (fun y hy => by
      have hy' : -y ≠ 0 := neg_ne_zero.2 (ne_of_gt hy)
      have h := (hw (-y) hy').scomp y (hasDerivAt_neg y)
      refine h.congr_deriv ?_
      have : ((-y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy'
      push_cast at this ⊢
      rw [neg_one_smul, div_neg, neg_neg])
    (hfw.comp_neg.integrableOn) (hf₁w.comp_neg.integrableOn)
  have split : ∀ F : ℝ → ℂ, Integrable F → ∫ y, F y = (∫ y in Ioi 0, F y) + ∫ y in Ioi 0, F (-y) := by
    intro F hF
    rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn (b := 0), add_comm,
      integral_comp_neg_Ioi]
    simp [integral_Iic_eq_integral_Iio]
  rw [split _ hfw, split _ hf₁w, mul_add, hp, hn]
  ring

end MellinByParts
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace StripDecay

open MellinByParts

private theorem iterate {f : ℕ → ℝ → ℂ} {w : ℝ → ℂ} {c : ℂ} (N : ℕ)
    (hf : ∀ k < N, ∀ y : ℝ, y ≠ 0 → HasDerivAt (f k) (f (k + 1) y / y) y)
    (hw : ∀ y : ℝ, y ≠ 0 → HasDerivAt w (c * w y / y) y)
    (hint : ∀ k ≤ N, Integrable (fun y => f k y * w y)) :
    (c + 1) ^ N * ∫ y, f 0 y * w y = (-1) ^ N * ∫ y, f N y * w y := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk)) (fun k hk => hint k (Nat.le_succ_of_le hk))
    have step := whole (hf n (Nat.lt_succ_self n)) hw (hint n (Nat.le_succ n)) (hint (n + 1) le_rfl)
    rw [pow_succ, mul_comm ((c + 1) ^ n), mul_assoc, ih', ← mul_assoc, mul_comm (c + 1), mul_assoc, step]
    ring

private theorem rpow_le_rpow_add_rpow {x : ℝ} (hx : 0 < x) {a a₁ a₂ : ℝ} (h₁ : a₁ ≤ a) (h₂ : a ≤ a₂) :
    x ^ a ≤ x ^ a₁ + x ^ a₂ := by
  rcases le_total x 1 with hx1 | hx1
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_ge hx hx1 h₁) (Real.rpow_nonneg hx.le _)
  · exact le_add_of_nonneg_of_le (Real.rpow_nonneg hx.le _) (Real.rpow_le_rpow_of_exponent_le hx1 h₂)

private theorem decay {f : ℕ → ℝ → ℂ} {w : ℂ → ℝ → ℂ} {c : ℂ → ℂ} {d : ℂ} {r σ₁ σ₂ : ℝ} (N : ℕ)
    (hf : ∀ k < N, ∀ y : ℝ, y ≠ 0 → HasDerivAt (f k) (f (k + 1) y / y) y)
    (hw : ∀ s : ℂ, ∀ y : ℝ, y ≠ 0 → HasDerivAt (w s) (c s * w s y / y) y)
    (hc : ∀ s : ℂ, c s + 1 = s + d)
    (hwabs : ∀ s : ℂ, ∀ y : ℝ, y ≠ 0 → ‖w s y‖ = |y| ^ (s.re + r))
    (hint : ∀ k ≤ N, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → Integrable (fun y => f k y * w s y)) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      |s.im| ^ N * ‖∫ y, f 0 y * w s y‖ ≤ C := by
  by_cases hσ : σ₁ ≤ σ₂
  swap
  · exact ⟨0, 0, fun s h₁ h₂ _ => absurd (h₁.trans h₂) hσ⟩

  set I₁ : ℝ := ∫ y, ‖f N y * w (σ₁ : ℂ) y‖ with hI₁
  set I₂ : ℝ := ∫ y, ‖f N y * w (σ₂ : ℂ) y‖ with hI₂
  have hI : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖∫ y, f N y * w s y‖ ≤ I₁ + I₂ := by
    intro s h₁ h₂
    have hi₁ := (hint N le_rfl (σ₁ : ℂ) (by simp) (by simpa using hσ)).norm
    have hi₂ := (hint N le_rfl (σ₂ : ℂ) (by simpa using hσ) (by simp)).norm
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [hI₁, hI₂, ← integral_add hi₁ hi₂]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) (hi₁.add hi₂) ?_
    have hae : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
      simp [ae_iff]
    filter_upwards [hae] with y hy
    have hy' : 0 < |y| := abs_pos.2 hy
    simp only [norm_mul, hwabs s y hy, hwabs (σ₁ : ℂ) y hy, hwabs (σ₂ : ℂ) y hy, Complex.ofReal_re]
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow hy' (by linarith) (by linarith)) (norm_nonneg _)

  refine ⟨2 ^ N * (I₁ + I₂), 2 * |d.im| + 2, fun s h₁ h₂ hT => ?_⟩
  have hiter := iterate N hf (hw s) (fun k hk => hint k hk s h₁ h₂)
  rw [hc s] at hiter
  have hsd : |s.im| ≤ 2 * ‖s + d‖ := by
    have h1 : |(s + d).im| ≤ ‖s + d‖ := Complex.abs_im_le_norm _
    have h2 : |s.im| ≤ |(s + d).im| + |d.im| := by
      have : s.im = (s + d).im - d.im := by simp
      rw [this]
      exact abs_sub _ _
    have h3 : |d.im| ≤ |s.im| / 2 := by linarith [abs_nonneg d.im]
    linarith
  have hsd0 : s + d ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hsd
    linarith [abs_nonneg s.im, abs_nonneg d.im]

  have hZ : ∫ y, f 0 y * w s y = ((-1) ^ N * ∫ y, f N y * w s y) / (s + d) ^ N := by
    rw [eq_div_iff (pow_ne_zero N hsd0), mul_comm, hiter]
  rw [hZ, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  have hpos : 0 < ‖s + d‖ := norm_pos_iff.2 hsd0
  rw [mul_div_assoc', div_le_iff₀ (pow_pos hpos N)]
  have hI0 : 0 ≤ I₁ + I₂ := (norm_nonneg _).trans (hI s h₁ h₂)
  calc |s.im| ^ N * ‖∫ y, f N y * w s y‖ ≤ (2 * ‖s + d‖) ^ N * (I₁ + I₂) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hsd N) (hI s h₁ h₂) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * (I₁ + I₂) * ‖s + d‖ ^ N := by ring

private theorem iterate_identity {Z : ℕ → ℂ → ℂ} {c : ℂ → ℂ} {σ₁ σ₂ : ℝ} (N : ℕ)
    (hstep : ∀ k < N, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → (c s + 1) * Z k s = -Z (k + 1) s)
    (s : ℂ) (h₁ : σ₁ ≤ s.re) (h₂ : s.re ≤ σ₂) :
    (c s + 1) ^ N * Z 0 s = (-1) ^ N * Z N s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_comm ((c s + 1) ^ n), mul_assoc, ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk)),
      ← mul_assoc, mul_comm (c s + 1), mul_assoc, hstep n (Nat.lt_succ_self n) s h₁ h₂]
    ring

private theorem decay_of_identity {Z : ℕ → ℂ → ℂ} {c : ℂ → ℂ} {d : ℂ} {σ₁ σ₂ M : ℝ} (N : ℕ)
    (hiter : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → (c s + 1) ^ N * Z 0 s = (-1) ^ N * Z N s)
    (hM : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z N s‖ ≤ M)
    (hc : ∀ s : ℂ, c s + 1 = s + d) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| → |s.im| ^ N * ‖Z 0 s‖ ≤ C := by
  refine ⟨2 ^ N * M, 2 * |d.im| + 2, fun s h₁ h₂ hT => ?_⟩
  have hit := hiter s h₁ h₂
  rw [hc s] at hit
  have hsd : |s.im| ≤ 2 * ‖s + d‖ := by
    have h1 : |(s + d).im| ≤ ‖s + d‖ := Complex.abs_im_le_norm _
    have h2 : |s.im| ≤ |(s + d).im| + |d.im| := by
      have : s.im = (s + d).im - d.im := by simp
      rw [this]
      exact abs_sub _ _
    have h3 : |d.im| ≤ |s.im| / 2 := by linarith [abs_nonneg d.im]
    linarith
  have hsd0 : s + d ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hsd
    linarith [abs_nonneg s.im, abs_nonneg d.im]
  have hZ : Z 0 s = ((-1) ^ N * Z N s) / (s + d) ^ N := by
    rw [eq_div_iff (pow_ne_zero N hsd0), mul_comm, hit]
  rw [hZ, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  have hpos : 0 < ‖s + d‖ := norm_pos_iff.2 hsd0
  rw [mul_div_assoc', div_le_iff₀ (pow_pos hpos N)]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s h₁ h₂)
  calc |s.im| ^ N * ‖Z N s‖ ≤ (2 * ‖s + d‖) ^ N * M :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hsd N) (hM s h₁ h₂) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * M * ‖s + d‖ ^ N := by ring

private theorem norm_integral_le_of_strip {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : X → ℂ} {y : X → ℝ}
    {w : ℂ → ℝ → ℂ} {r σ₁ σ₂ : ℝ} (hy : ∀ᵐ p ∂μ, y p ≠ 0)
    (hwabs : ∀ s : ℂ, ∀ t : ℝ, t ≠ 0 → ‖w s t‖ = |t| ^ (s.re + r))
    (h₁ : Integrable (fun p => F p * w (σ₁ : ℂ) (y p)) μ) (h₂ : Integrable (fun p => F p * w (σ₂ : ℂ) (y p)) μ)
    (s : ℂ) (hs₁ : σ₁ ≤ s.re) (hs₂ : s.re ≤ σ₂) :
    ‖∫ p, F p * w s (y p) ∂μ‖ ≤
      (∫ p, ‖F p * w (σ₁ : ℂ) (y p)‖ ∂μ) + ∫ p, ‖F p * w (σ₂ : ℂ) (y p)‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add h₁.norm h₂.norm]
  refine integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _) (h₁.norm.add h₂.norm) ?_
  filter_upwards [hy] with p hp
  have hp' : 0 < |y p| := abs_pos.2 hp
  simp only [norm_mul, hwabs s (y p) hp, hwabs (σ₁ : ℂ) (y p) hp, hwabs (σ₂ : ℂ) (y p) hp, Complex.ofReal_re]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow_add_rpow hp' (by linarith) (by linarith)) (norm_nonneg _)

end StripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end MellinAndStrip
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section LineCalculus
open MvPolynomial Finset MeasureTheory Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam CubicInduction.integrable_dualWhittakerFn3_jacquetVector3_prod"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "archZeta31 archZetaDual31 lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 transposeInv3_weylPrime3 transposeInv3 embedMat2 iotaGL coe_iotaGL diagUnitGL2 coe_diagUnitGL2 gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod integrable_dualWhittakerFn3_jacquetVector3_prod"
namespace PolyGaussLine
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private abbrev Mat := Matrix (Fin 2) (Fin 3) ℝ

private def qf (M : Mat) : ℝ := ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2

private theorem qf_nonneg (M : Mat) : 0 ≤ qf M :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

private theorem sq_entry_le_qf (M : Mat) (i : Fin 2) (b : Fin 3) : M i b ^ 2 ≤ qf M := by
  refine (single_le_sum (f := fun b' => M i b' ^ 2) (fun _ _ => sq_nonneg _) (mem_univ b)).trans ?_
  exact single_le_sum (f := fun i' => ∑ b', M i' b' ^ 2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    (mem_univ i)

private theorem abs_entry_le (M : Mat) (i : Fin 2) (b : Fin 3) : |M i b| ≤ 1 + qf M := by
  have h := sq_entry_le_qf M i b
  nlinarith [abs_nonneg (M i b), sq_abs (M i b)]

private theorem norm_gaussian3 (M : Mat) : ‖gaussian3 M‖ = Real.exp (-(Real.pi * qf M)) := by
  rw [gaussian3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rfl

private def ent (M : Mat) : Fin 2 × Fin 3 → ℂ := fun v => ((M v.1 v.2 : ℝ) : ℂ)

private def pg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M : Mat) : ℂ := eval (ent M) p * gaussian3 M

private theorem hasDerivAt_eval_line {σ : Type*} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℂ) (Z V : σ → ℂ)
    (ε₀ : ℝ) :
    HasDerivAt (fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) p)
      (∑ v, eval (fun w => Z w + (ε₀ : ℂ) * V w) (pderiv v p) * V v) ε₀ := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_mul, sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add, add_mul, sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hγ : HasDerivAt (fun ε : ℝ => Z i + (ε : ℂ) * V i) (1 * V i) ε₀ :=
      ((hasDerivAt_id ε₀).ofReal_comp.mul_const (V i)).const_add (Z i)
    have h := hp.mul hγ
    have hfun : (fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) (p * X i)) =
        fun ε : ℝ => eval (fun v => Z v + (ε : ℂ) * V v) p * (Z i + (ε : ℂ) * V i) := by
      funext ε
      rw [map_mul, eval_X]
    rw [hfun]
    convert h using 1 <;> try rfl
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, add_mul, sum_add_distrib]
    congr 1
    · rw [sum_mul]
      exact sum_congr rfl fun v _ => by ring
    · rw [sum_eq_single i]
      · simp
      · intro v _ hv
        simp [hv]
      · intro hi
        exact absurd (mem_univ i) hi

private theorem hasDerivAt_gaussian3_line (A D : Mat) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => gaussian3 (A + t • D))
      (gaussian3 (A + t₀ • D) *
        (-(2 * Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, (A + t₀ • D) i b * D i b) : ℝ)) t₀ := by
  have key : ∀ (i : Fin 2) (b : Fin 3),
      HasDerivAt (fun t : ℝ => (A + t • D) i b ^ 2) (2 * ((A + t₀ • D) i b * D i b)) t₀ := by
    intro i b
    have h1 : HasDerivAt (fun t : ℝ => (A + t • D) i b) (D i b) t₀ := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simpa using ((hasDerivAt_id t₀).mul_const (D i b)).const_add (A i b)
    convert h1.mul h1 using 1 <;> try rfl
    · funext t
      simp only [Pi.mul_apply, pow_two]
    · ring
  have hq : HasDerivAt (fun t : ℝ => ∑ i : Fin 2, ∑ b : Fin 3, (A + t • D) i b ^ 2)
      (2 * ∑ i : Fin 2, ∑ b : Fin 3, (A + t₀ • D) i b * D i b) t₀ := by
    have hs := HasDerivAt.fun_sum (u := univ) fun i _ => HasDerivAt.fun_sum (u := univ) fun b _ => key i b
    refine hs.congr_deriv ?_
    simp only [mul_sum]
  unfold gaussian3
  have h := ((hq.const_mul Real.pi).neg.exp).ofReal_comp
  convert h using 1 <;> try rfl
  simp only [Pi.neg_apply]
  push_cast
  ring

private def rPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (w : Fin 2 × Fin 3) : MvPolynomial (Fin 2 × Fin 3) ℂ :=
  pderiv w p - C (2 * Real.pi : ℂ) * p * X w

private def pgDir (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M D : Mat) : ℂ :=
  (∑ w, ent D w * eval (ent M) (rPoly p w)) * gaussian3 M

private theorem hasDerivAt_pg_line (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (A D : Mat) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => pg p (A + t • D)) (pgDir p (A + t₀ • D) D) t₀ := by
  have hent : ∀ t : ℝ, ent (A + t • D) = fun w => ent A w + (t : ℂ) * ent D w := by
    intro t
    funext w
    simp only [ent, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  have hP := hasDerivAt_eval_line p (ent A) (ent D) t₀
  have hfun : (fun t : ℝ => eval (ent (A + t • D)) p) =
      fun t : ℝ => eval (fun v => ent A v + (t : ℂ) * ent D v) p := by
    funext t
    rw [hent t]
  rw [← hent t₀, ← hfun] at hP
  have h : HasDerivAt (fun t : ℝ => pg p (A + t • D)) _ t₀ := hP.mul (hasDerivAt_gaussian3_line A D t₀)
  refine h.congr_deriv ?_

  set M : Mat := A + t₀ • D with hM
  set G : ℂ := gaussian3 M
  set S₁ : ℂ := ∑ w, eval (ent M) (pderiv w p) * ent D w with hS₁
  set S₂ : ℂ := ∑ w, ent M w * ent D w with hS₂
  have e1 : ∑ w, ent D w * eval (ent M) (rPoly p w) = S₁ - 2 * Real.pi * eval (ent M) p * S₂ := by
    simp only [rPoly, map_sub, map_mul, eval_C, eval_X, mul_sub, Finset.sum_sub_distrib, hS₁, hS₂,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun w _ => by ring
    · exact Finset.sum_congr rfl fun w _ => by ring
  have e2 : (((∑ i : Fin 2, ∑ b : Fin 3, M i b * D i b : ℝ)) : ℂ) = S₂ := by
    rw [hS₂, Fintype.sum_prod_type]
    push_cast
    rfl
  rw [pgDir, e1, ← e2]
  push_cast
  ring

private theorem exists_eval_le (q : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ M : Mat, ‖eval (ent M) q‖ ≤ C * (1 + qf M) ^ d := by
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, norm_nonneg _, 0, fun M => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, hC₁, d₁, h₁⟩ := hp
    obtain ⟨C₂, hC₂, d₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, max d₁ d₂, fun M => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + qf M := le_add_of_nonneg_right (qf_nonneg M)
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have e₁ := pow_le_pow_right₀ h1 (le_max_left d₁ d₂)
    have e₂ := pow_le_pow_right₀ h1 (le_max_right d₁ d₂)
    nlinarith [h₁ M, h₂ M, mul_le_mul_of_nonneg_left e₁ hC₁, mul_le_mul_of_nonneg_left e₂ hC₂]
  | mul_X p w hp =>
    obtain ⟨C, hC, d, h⟩ := hp
    refine ⟨C, hC, d + 1, fun M => ?_⟩
    rw [map_mul, eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (h M) ?_ (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [qf_nonneg M]) _))
    simp only [ent, Complex.norm_real, Real.norm_eq_abs]
    exact abs_entry_le M w.1 w.2

private theorem exists_pow_mul_exp_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ d * Real.exp (-(c * x)) ≤ K := by
  refine ⟨d.factorial * c⁻¹ ^ d * Real.exp c, by positivity, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (c * (1 + x)) (by positivity) d
  have h1 : (c * (1 + x)) ^ d ≤ Real.exp (c * (1 + x)) * d.factorial := (div_le_iff₀ (by positivity)).1 h
  have h2 : (1 + x) ^ d = (c * (1 + x)) ^ d * c⁻¹ ^ d := by
    rw [mul_pow, mul_assoc, mul_comm ((1 + x) ^ d), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow,
      one_mul]
  calc (1 + x) ^ d * Real.exp (-(c * x))
      = (c * (1 + x)) ^ d * c⁻¹ ^ d * Real.exp (-(c * x)) := by rw [← h2]
    _ ≤ Real.exp (c * (1 + x)) * d.factorial * c⁻¹ ^ d * Real.exp (-(c * x)) := by gcongr
    _ = d.factorial * c⁻¹ ^ d * (Real.exp (c * (1 + x)) * Real.exp (-(c * x))) := by ring
    _ = d.factorial * c⁻¹ ^ d * Real.exp c := by rw [← Real.exp_add]; ring_nf

private theorem integrable_exp_neg_mul_norm_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun v : Fin 2 → ℝ => Real.exp (-(a * ‖v‖ ^ 2))) := by
  have hprod : Integrable (fun v : Fin 2 → ℝ => ∏ i, Real.exp (-(a / 2) * v i ^ 2)) :=
    Integrable.fintype_prod (f := fun (_ : Fin 2) (x : ℝ) => Real.exp (-(a / 2) * x ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by positivity)
  refine hprod.mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Fin.prod_univ_two, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h0 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
  have h1 : ‖v 1‖ ≤ ‖v‖ := norm_le_pi_norm v 1
  rw [Real.norm_eq_abs] at h0 h1
  have e0 : v 0 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : v 1 ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

private theorem continuous_ent : Continuous (ent : Mat → Fin 2 × Fin 3 → ℂ) :=
  continuous_pi fun w => Complex.continuous_ofReal.comp (continuous_id.matrix_elem w.1 w.2)

private theorem continuous_qf : Continuous qf := by
  unfold qf
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun b _ =>
    (continuous_id.matrix_elem i b).pow 2

private theorem continuous_gaussian3 : Continuous gaussian3 := by
  change Continuous fun M : Mat => ((Real.exp (-(Real.pi * qf M)) : ℝ) : ℂ)
  exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_qf).neg)

private theorem continuous_pg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) : Continuous (pg p) :=
  ((MvPolynomial.continuous_eval p).comp continuous_ent).mul continuous_gaussian3

private theorem continuous_pgDir (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    Continuous fun MD : Mat × Mat => pgDir p MD.1 MD.2 := by
  unfold pgDir
  refine Continuous.mul (continuous_finsetSum _ fun w _ => ?_) (continuous_gaussian3.comp continuous_fst)
  exact ((continuous_apply w).comp (continuous_ent.comp continuous_snd)).mul
    ((MvPolynomial.continuous_eval _).comp (continuous_ent.comp continuous_fst))

private theorem norm_pgDir_le (p : MvPolynomial (Fin 2 × Fin 3) ℂ) {Cr : ℝ} {dr : ℕ}
    (hrb : ∀ w M, ‖eval (ent M) (rPoly p w)‖ ≤ Cr * (1 + qf M) ^ dr) {B : ℝ} (M D : Mat)
    (hD : ∀ w, ‖ent D w‖ ≤ B) :
    ‖pgDir p M D‖ ≤ 6 * B * Cr * (1 + qf M) ^ dr * Real.exp (-(Real.pi * qf M)) := by
  rw [pgDir, norm_mul, norm_gaussian3]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have hB : 0 ≤ B := (norm_nonneg _).trans (hD ((0 : Fin 2), (0 : Fin 3)))
  calc ∑ w, ‖ent D w * eval (ent M) (rPoly p w)‖ ≤ ∑ _w : Fin 2 × Fin 3, B * (Cr * (1 + qf M) ^ dr) :=
        sum_le_sum fun w _ => by
          rw [norm_mul]
          exact mul_le_mul (hD w) (hrb w M) (norm_nonneg _) hB
    _ = 6 * B * Cr * (1 + qf M) ^ dr := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

private theorem hasDerivAt_integral_pg_line (p : MvPolynomial (Fin 2 × Fin 3) ℂ) {χ : (Fin 2 → ℝ) → ℂ}
    (hχ : Continuous χ) (hχ1 : ∀ v, ‖χ v‖ ≤ 1) {Z₀ Z₁ : (Fin 2 → ℝ) → Mat} (hZ₀ : Continuous Z₀)
    (hZ₁ : Continuous Z₁) {C₁ : ℝ} (hC₁ : ∀ v w, ‖ent (Z₁ v) w‖ ≤ C₁ * (1 + ‖v‖ ^ 2)) {t₀ δ c C : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hgrow : ∀ t ∈ Metric.ball t₀ δ, ∀ v, c * ‖v‖ ^ 2 - C ≤ qf (Z₀ v + t • Z₁ v)) :
    HasDerivAt (fun t : ℝ => ∫ v, pg p (Z₀ v + t • Z₁ v) * χ v)
      (∫ v, pgDir p (Z₀ v + t₀ • Z₁ v) (Z₁ v) * χ v) t₀ := by

  obtain ⟨Cp, hCp, dp, hpb⟩ := exists_eval_le p
  have hr : ∃ Cr : ℝ, 0 ≤ Cr ∧ ∃ dr : ℕ, ∀ w M, ‖eval (ent M) (rPoly p w)‖ ≤ Cr * (1 + qf M) ^ dr := by
    choose Cw hCw dw hw using fun w => exists_eval_le (rPoly p w)
    refine ⟨∑ w, Cw w, sum_nonneg fun w _ => hCw w, ∑ w, dw w, fun w M => (hw w M).trans ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + qf M := le_add_of_nonneg_right (qf_nonneg M)
    exact mul_le_mul (single_le_sum (fun w _ => hCw w) (mem_univ w))
      (pow_le_pow_right₀ h1 (single_le_sum (fun w _ => Nat.zero_le (dw w)) (mem_univ w)))
      (by positivity) (sum_nonneg fun w _ => hCw w)
  obtain ⟨Cr, hCr, dr, hrb⟩ := hr
  obtain ⟨Kp, hKp, hKpb⟩ := exists_pow_mul_exp_le dp (c := Real.pi / 2) (by positivity)
  obtain ⟨Kr, hKr, hKrb⟩ := exists_pow_mul_exp_le dr (c := Real.pi / 2) (by positivity)
  obtain ⟨Kv, hKv, hKvb⟩ := exists_pow_mul_exp_le 1 (c := Real.pi * c / 4) (by positivity)

  have core : ∀ {d : ℕ} {K : ℝ}, 0 ≤ K → (∀ x : ℝ, 0 ≤ x → (1 + x) ^ d * Real.exp (-(Real.pi / 2 * x)) ≤ K) →
      ∀ t ∈ Metric.ball t₀ δ, ∀ v,
        (1 + qf (Z₀ v + t • Z₁ v)) ^ d * Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v))) ≤
          K * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2))) := by
    intro d K hK0 hK t ht v
    set q := qf (Z₀ v + t • Z₁ v)
    have hq0 : 0 ≤ q := qf_nonneg _
    have hq : c * ‖v‖ ^ 2 - C ≤ q := hgrow t ht v
    have hsplit : Real.exp (-(Real.pi * q)) =
        Real.exp (-(Real.pi / 2 * q)) * Real.exp (-(Real.pi / 2 * q)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul (hK q hq0) ?_ (Real.exp_nonneg _) hK0
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hq (le_of_lt (half_pos Real.pi_pos))
    linarith
  have hv : ∀ v : Fin 2 → ℝ, (1 + ‖v‖ ^ 2) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) ≤
      Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) := by
    intro v
    have hsplit : Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) =
        Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    simpa using hKvb (‖v‖ ^ 2) (by positivity)

  set bound : (Fin 2 → ℝ) → ℝ := fun v =>
    6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) * Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2)) with hbound
  have hbound_int : Integrable bound := (integrable_exp_neg_mul_norm_sq (by positivity)).const_mul _

  have hFc : ∀ t : ℝ, Continuous fun v => pg p (Z₀ v + t • Z₁ v) * χ v := fun t =>
    ((continuous_pg p).comp (hZ₀.add (hZ₁.const_smul t))).mul hχ
  have hF'c : Continuous fun v => pgDir p (Z₀ v + t₀ • Z₁ v) (Z₁ v) * χ v :=
    ((continuous_pgDir p).comp ((hZ₀.add (hZ₁.const_smul t₀)).prodMk hZ₁)).mul hχ

  have ht₀ : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
  have hF_int : Integrable fun v => pg p (Z₀ v + t₀ • Z₁ v) * χ v := by
    refine Integrable.mono' ((integrable_exp_neg_mul_norm_sq (by positivity : (0 : ℝ) < Real.pi / 2 * c)).const_mul
      (Cp * Kp * Real.exp (Real.pi / 2 * C))) (hFc t₀).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    rw [norm_mul, pg, norm_mul, norm_gaussian3]
    have hq0 := qf_nonneg (Z₀ v + t₀ • Z₁ v)
    calc ‖eval (ent (Z₀ v + t₀ • Z₁ v)) p‖ * Real.exp (-(Real.pi * qf (Z₀ v + t₀ • Z₁ v))) * ‖χ v‖
        ≤ Cp * (1 + qf (Z₀ v + t₀ • Z₁ v)) ^ dp * Real.exp (-(Real.pi * qf (Z₀ v + t₀ • Z₁ v))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hpb _) (Real.exp_nonneg _)) (hχ1 v) (norm_nonneg _)
            (mul_nonneg (mul_nonneg hCp (pow_nonneg (by linarith) _)) (Real.exp_nonneg _))
      _ ≤ Cp * (Kp * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)))) := by
          rw [mul_one, mul_assoc]
          exact mul_le_mul_of_nonneg_left (core hKp hKpb t₀ ht₀ v) hCp
      _ = Cp * Kp * Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)) := by ring

  have h_bound : ∀ᵐ v ∂volume, ∀ t ∈ Metric.ball t₀ δ, ‖pgDir p (Z₀ v + t • Z₁ v) (Z₁ v) * χ v‖ ≤ bound v := by
    refine Eventually.of_forall fun v t ht => ?_
    rw [norm_mul]
    have h1 := norm_pgDir_le p hrb (Z₀ v + t • Z₁ v) (Z₁ v) (hC₁ v)
    have hC₁0 : 0 ≤ C₁ * (1 + ‖v‖ ^ 2) := (norm_nonneg _).trans (hC₁ v ((0 : Fin 2), (0 : Fin 3)))
    have hv0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    have hC₁' : 0 ≤ C₁ := nonneg_of_mul_nonneg_left hC₁0 (by positivity)
    have hq0 := qf_nonneg (Z₀ v + t • Z₁ v)
    have hA : (0 : ℝ) ≤ 6 * C₁ * Cr := by positivity
    have hB : (0 : ℝ) ≤ 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) := by positivity
    calc ‖pgDir p (Z₀ v + t • Z₁ v) (Z₁ v)‖ * ‖χ v‖
        ≤ 6 * (C₁ * (1 + ‖v‖ ^ 2)) * Cr * (1 + qf (Z₀ v + t • Z₁ v)) ^ dr *
            Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v))) * 1 :=
          mul_le_mul h1 (hχ1 v) (norm_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₁0) hCr)
              (pow_nonneg (by linarith) _)) (Real.exp_nonneg _))
      _ = 6 * C₁ * Cr * ((1 + qf (Z₀ v + t • Z₁ v)) ^ dr * Real.exp (-(Real.pi * qf (Z₀ v + t • Z₁ v)))) *
            (1 + ‖v‖ ^ 2) := by ring
      _ ≤ 6 * C₁ * Cr * (Kr * (Real.exp (Real.pi / 2 * C) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2)))) *
            (1 + ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (core hKr hKrb t ht v) hA) hv0
      _ = 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) *
            ((1 + ‖v‖ ^ 2) * Real.exp (-(Real.pi / 2 * c * ‖v‖ ^ 2))) := by ring
      _ ≤ 6 * C₁ * Cr * Kr * Real.exp (Real.pi / 2 * C) * (Kv * Real.exp (-(Real.pi * c / 4 * ‖v‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left (hv v) hB
      _ = bound v := by rw [hbound]; ring

  have h_diff : ∀ᵐ v ∂volume, ∀ t ∈ Metric.ball t₀ δ,
      HasDerivAt (fun t : ℝ => pg p (Z₀ v + t • Z₁ v) * χ v) (pgDir p (Z₀ v + t • Z₁ v) (Z₁ v) * χ v) t :=
    Eventually.of_forall fun v t _ => (hasDerivAt_pg_line p (Z₀ v) (Z₁ v) t).mul_const (χ v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hδ)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hF_int hF'c.aestronglyMeasurable h_bound
    hbound_int h_diff).2

private theorem pgDir_smul (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M D : Mat) (t : ℝ) :
    pgDir p M (t • D) = (t : ℂ) * pgDir p M D := by
  simp only [pgDir, ent, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  rw [← mul_sum, mul_assoc]

private def entryMulPoly (Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 × Fin 3) : MvPolynomial (Fin 2 × Fin 3) ℂ :=
  ∑ k : Fin 3, X (v.1, k) * C ((Y k v.2 : ℝ) : ℂ)

private theorem eval_entryMulPoly (M : Mat) (Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 × Fin 3) :
    eval (ent M) (entryMulPoly Y v) = ent (M * Y) v := by
  simp only [entryMulPoly, map_sum, map_mul, eval_X, eval_C, ent, Matrix.mul_apply, Complex.ofReal_sum,
    Complex.ofReal_mul]

private def derivedPoly (Y : Matrix (Fin 3) (Fin 3) ℝ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) :
    MvPolynomial (Fin 2 × Fin 3) ℂ :=
  ∑ w, rPoly p w * entryMulPoly Y w

private theorem pg_derivedPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ) (M : Mat) :
    pg (derivedPoly Y p) M = pgDir p M (M * Y) := by
  simp only [pg, pgDir, derivedPoly, map_sum, map_mul, eval_entryMulPoly]
  congr 1
  exact sum_congr rfl fun w _ => by ring

private theorem smul_pgDir_eq_pg_derivedPoly (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ)
    (Z₀ Z₁ : Mat) (t : ℝ) (h : t • Z₁ = (Z₀ + t • Z₁) * Y) :
    (t : ℂ) * pgDir p (Z₀ + t • Z₁) Z₁ = pg (derivedPoly Y p) (Z₀ + t • Z₁) := by
  rw [← pgDir_smul, pg_derivedPoly, ← h]

end LanglandsTunnell.CubicInduction.PolyGaussLine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end LineCalculus
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace DualStripDecay

open LanglandsTunnell.CubicInduction.PolyGaussLine Metric

private def rs (r : Fin 3 → ℝ) : ℝ := ∑ b : Fin 3, r b ^ 2

private def qf2 (h : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i : Fin 2, ∑ k : Fin 2, h i k ^ 2

private def slice0 (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) : Mat :=
  Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]

private def sliceMat (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) : Mat :=
  h * slice0 m v

private theorem slice0_apply (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) (b : Fin 3) :
    slice0 m v i b = m (Fin.castSucc i) b + v i * m 2 b := by
  fin_cases i <;> rfl

private theorem slice0_add_smul (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    slice0 (m₀ + t • m₁) v = slice0 m₀ v + t • slice0 m₁ v := by
  ext i b
  simp only [slice0_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem sliceMat_add_smul (h : Matrix (Fin 2) (Fin 2) ℝ) (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (v : Fin 2 → ℝ) : sliceMat h (m₀ + t • m₁) v = sliceMat h m₀ v + t • sliceMat h m₁ v := by
  simp only [sliceMat, slice0_add_smul, Matrix.mul_add, Matrix.mul_smul]

private theorem slice0_smul (M : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    slice0 (t • M) v = t • slice0 M v := by
  ext i b
  simp only [slice0_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem sliceMat_smul (h : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (v : Fin 2 → ℝ) :
    sliceMat h (t • M) v = t • sliceMat h M v := by
  simp only [sliceMat, slice0_smul, Matrix.mul_smul]

private theorem slice0_mul (m Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    slice0 (m * Y) v = slice0 m v * Y := by
  ext i b
  simp only [slice0_apply, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

private theorem sliceMat_mul (h : Matrix (Fin 2) (Fin 2) ℝ) (m Y : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    sliceMat h (m * Y) v = sliceMat h m v * Y := by
  rw [sliceMat, sliceMat, slice0_mul, Matrix.mul_assoc]

private theorem continuous_slice0 (m : Matrix (Fin 3) (Fin 3) ℝ) : Continuous fun v : Fin 2 → ℝ => slice0 m v := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [slice0_apply]
  fun_prop

private theorem continuous_sliceMat (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous fun v : Fin 2 → ℝ => sliceMat h m v :=
  continuous_const.matrix_mul (continuous_slice0 m)

private theorem abs_apply_le_norm (v : Fin 2 → ℝ) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rwa [Real.norm_eq_abs] at this

private theorem norm_le_one_add_sq (v : Fin 2 → ℝ) : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by
  nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]

private theorem exists_abs_sliceMat_le (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ C₁ : ℝ, ∀ (v : Fin 2 → ℝ) (i : Fin 2) (b : Fin 3), |sliceMat h m v i b| ≤ C₁ * (1 + ‖v‖ ^ 2) := by

  refine ⟨∑ i : Fin 2, ∑ b : Fin 3, ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|), ?_⟩
  intro v i b
  have hv1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hvn : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := norm_le_one_add_sq v
  have hentry : sliceMat h m v i b = ∑ k : Fin 2, h i k * (m (Fin.castSucc k) b + v k * m 2 b) := by
    simp only [sliceMat, Matrix.mul_apply, slice0_apply]
  rw [hentry]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k : Fin 2, |h i k * (m (Fin.castSucc k) b + v k * m 2 b)| ≤
      (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|) * (1 + ‖v‖ ^ 2) := by
    intro k
    rw [abs_mul]
    have hk : |v k| ≤ 1 + ‖v‖ ^ 2 := (abs_apply_le_norm v k).trans hvn
    have h1 : |m (Fin.castSucc k) b + v k * m 2 b| ≤
        |m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) + |m 2 b| * (1 + ‖v‖ ^ 2) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have hm0 : |m (Fin.castSucc k) b| ≤ |m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) :=
        le_mul_of_one_le_right (abs_nonneg _) hv1
      have hm2 : |v k| * |m 2 b| ≤ |m 2 b| * (1 + ‖v‖ ^ 2) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
      linarith
    calc |h i k| * |m (Fin.castSucc k) b + v k * m 2 b|
        ≤ |h i k| * (|m (Fin.castSucc k) b| * (1 + ‖v‖ ^ 2) + |m 2 b| * (1 + ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|) * (1 + ‖v‖ ^ 2) := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)

  have hib : (∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b| + |h i k| * |m 2 b|)) ≤
      ∑ b' : Fin 3, ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b'| + |h i k| * |m 2 b'|) :=
    Finset.single_le_sum (f := fun b' => ∑ k : Fin 2, (|h i k| * |m (Fin.castSucc k) b'| + |h i k| * |m 2 b'|))
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ b)
  refine hib.trans ?_
  exact Finset.single_le_sum
    (f := fun i' => ∑ b' : Fin 3, ∑ k : Fin 2, (|h i' k| * |m (Fin.castSucc k) b'| + |h i' k| * |m 2 b'|))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

private theorem qf_mul_le (A : Matrix (Fin 2) (Fin 2) ℝ) (X : Mat) : qf (A * X) ≤ qf2 A * qf X := by
  simp only [qf, qf2, Matrix.mul_apply]

  have hentry : ∀ (i : Fin 2) (b : Fin 3),
      (∑ k : Fin 2, A i k * X k b) ^ 2 ≤ (∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, X k b ^ 2 := fun i b =>
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => A i k) (fun k => X k b)
  calc ∑ i : Fin 2, ∑ b : Fin 3, (∑ k : Fin 2, A i k * X k b) ^ 2
      ≤ ∑ i : Fin 2, ∑ b : Fin 3, (∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, X k b ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hentry i b
    _ = (∑ i : Fin 2, ∑ k : Fin 2, A i k ^ 2) * ∑ k : Fin 2, ∑ b : Fin 3, X k b ^ 2 := by
        simp only [Fin.sum_univ_two, Fin.sum_univ_three]
        ring

private theorem qf_le_of_det_ne_zero (h : Matrix (Fin 2) (Fin 2) ℝ) (hdet : h.det ≠ 0) (X : Mat) :
    qf X ≤ (qf2 h⁻¹ + 1) * qf (h * X) := by
  have hX : X = h⁻¹ * (h * X) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul]
  have hq : 0 ≤ qf (h * X) := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc qf X = qf (h⁻¹ * (h * X)) := by rw [← hX]
    _ ≤ qf2 h⁻¹ * qf (h * X) := qf_mul_le _ _
    _ ≤ (qf2 h⁻¹ + 1) * qf (h * X) := by nlinarith

private theorem qf_slice0_ge (m : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 2 → ℝ) :
    rs (m 2) / 2 * (v 0 ^ 2 + v 1 ^ 2) - (rs (m 0) + rs (m 1)) ≤ qf (slice0 m v) := by
  simp only [qf, rs, slice0_apply, Fin.sum_univ_two, Fin.sum_univ_three, Fin.castSucc_zero, Fin.castSucc_one]
  nlinarith [sq_nonneg (2 * m 0 0 + v 0 * m 2 0), sq_nonneg (2 * m 0 1 + v 0 * m 2 1),
    sq_nonneg (2 * m 0 2 + v 0 * m 2 2), sq_nonneg (2 * m 1 0 + v 1 * m 2 0), sq_nonneg (2 * m 1 1 + v 1 * m 2 1),
    sq_nonneg (2 * m 1 2 + v 1 * m 2 2)]

private theorem rs_pos_of_ne_zero {r : Fin 3 → ℝ} (hr : r ≠ 0) : 0 < rs r := by
  rcases (Finset.sum_nonneg fun b _ => sq_nonneg (r b) : (0 : ℝ) ≤ rs r).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hr
    have h0 : ∑ b : Fin 3, r b ^ 2 = 0 := h.symm
    funext b
    have hb := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg (r b)).mp h0 b (Finset.mem_univ b)
    exact (pow_eq_zero_iff two_ne_zero).mp hb

private theorem sq_norm_le (v : Fin 2 → ℝ) : ‖v‖ ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
  have h0 : ‖v‖ ≤ Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    fin_cases i <;> (try simp) <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  calc ‖v‖ ^ 2 ≤ Real.sqrt (v 0 ^ 2 + v 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ = v 0 ^ 2 + v 1 ^ 2 := Real.sq_sqrt (by positivity)

private theorem continuous_rs_apply (m₀ m₁ : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    Continuous fun t : ℝ => rs ((m₀ + t • m₁) i) := by
  simp only [rs, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

private theorem exists_growth (h : Matrix (Fin 2) (Fin 2) ℝ) (hdet : h.det ≠ 0) (M₀ M₁ : Matrix (Fin 3) (Fin 3) ℝ)
    (t₀ δ : ℝ) (hδ : 0 < δ) (hrow : ∀ t ∈ closedBall t₀ δ, (M₀ + t • M₁) 2 ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ t ∈ ball t₀ δ, ∀ v : Fin 2 → ℝ,
      c * ‖v‖ ^ 2 - C ≤ qf (sliceMat h M₀ v + t • sliceMat h M₁ v) := by

  obtain ⟨tm, htm, hmin⟩ := (isCompact_closedBall t₀ δ).exists_isMinOn (nonempty_closedBall.mpr hδ.le)
    (continuous_rs_apply M₀ M₁ 2).continuousOn
  set ρ : ℝ := rs ((M₀ + tm • M₁) 2) with hρ
  have hρpos : 0 < ρ := rs_pos_of_ne_zero (hrow tm htm)

  obtain ⟨B, hB⟩ := (isCompact_closedBall t₀ δ).exists_bound_of_continuousOn
    ((continuous_rs_apply M₀ M₁ 0).add (continuous_rs_apply M₀ M₁ 1)).continuousOn
  set κ : ℝ := qf2 h⁻¹ + 1 with hκ
  have hκpos : 0 < κ := by
    have : 0 ≤ qf2 h⁻¹ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  refine ⟨ρ / 2 / κ, by positivity, B / κ, fun t ht v => ?_⟩
  have ht' : t ∈ closedBall t₀ δ := ball_subset_closedBall ht
  rw [← sliceMat_add_smul, sliceMat]
  have h1 := qf_le_of_det_ne_zero h hdet (slice0 (M₀ + t • M₁) v)
  have h2 := qf_slice0_ge (M₀ + t • M₁) v
  have h3 : ρ ≤ rs ((M₀ + t • M₁) 2) := hmin ht'
  have h4 : rs ((M₀ + t • M₁) 0) + rs ((M₀ + t • M₁) 1) ≤ B := by
    have hBt := hB t ht'
    rw [Real.norm_eq_abs] at hBt
    exact (abs_le.mp hBt).2
  have h5 := sq_norm_le v
  have hvv : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by positivity

  have h6 : ρ / 2 * ‖v‖ ^ 2 - B ≤ κ * qf (h * slice0 (M₀ + t • M₁) v) := by
    have h7 : ρ / 2 * ‖v‖ ^ 2 ≤ rs ((M₀ + t • M₁) 2) / 2 * (v 0 ^ 2 + v 1 ^ 2) := by
      have := mul_le_mul h3 h5 (sq_nonneg _) (by linarith)
      linarith
    linarith
  rw [div_mul_eq_mul_div, div_sub_div_same]
  exact (div_le_iff₀ hκpos).mpr (by linarith)

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace DualStripDecay

p2m_open "MeasureTheory Metric Filter Topology AutomorphicForm.StandardKernel LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse.ArchR P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction.PolyGaussLine"

section Bridge

private def wFactor {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) * D.W (diagOne a * (Matrix.of e)⁻¹)

private theorem jacquetIntegrand3_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (e : Fin 2 → Fin 2 → ℝ) :
    jacquetIntegrand3 D u₃ a₃ a ψ S g e = godementInner3 ψ S (Matrix.of e) (realMat g) * wFactor D u₃ a₃ a e := by
  simp only [jacquetIntegrand3, wFactor, mul_assoc]

private theorem godementInner3_pg_eq (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ (pg p) h m = ∫ v : Fin 2 → ℝ, pg p (sliceMat h m v) * ψ (ofReal (-(v 1))) :=
  rfl

end Bridge
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section Inner

variable (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)

private theorem hasDerivAt_inner (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1))))
    (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    {h : Matrix (Fin 2) (Fin 2) ℝ} (hdet : h.det ≠ 0) (M₀ M₁ : Matrix (Fin 3) (Fin 3) ℝ) {t₀ δ : ℝ} (hδ : 0 < δ)
    (hrow : ∀ t ∈ closedBall t₀ δ, (M₀ + t • M₁) 2 ≠ 0) :
    HasDerivAt (fun t : ℝ => godementInner3 ψ (pg p) h (M₀ + t • M₁))
      (∫ v : Fin 2 → ℝ, pgDir p (sliceMat h M₀ v + t₀ • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1))))
      t₀ := by
  obtain ⟨c, hc, C, hgrow⟩ := exists_growth h hdet M₀ M₁ t₀ δ hδ hrow
  obtain ⟨C₁, hC₁⟩ := exists_abs_sliceMat_le h M₁
  have hfun : (fun t : ℝ => godementInner3 ψ (pg p) h (M₀ + t • M₁)) =
      fun t : ℝ => ∫ v : Fin 2 → ℝ, pg p (sliceMat h M₀ v + t • sliceMat h M₁ v) * ψ (ofReal (-(v 1))) := by
    funext t
    rw [godementInner3_pg_eq]
    simp only [sliceMat_add_smul]
  rw [hfun]
  refine hasDerivAt_integral_pg_line p hχ hχ1 (continuous_sliceMat h M₀) (continuous_sliceMat h M₁) (C₁ := C₁)
    (fun v w => ?_) hδ hc hgrow
  simp only [ent, Complex.norm_real, Real.norm_eq_abs]
  exact hC₁ v w.1 w.2

private theorem mul_inner_deriv_eq (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (h : Matrix (Fin 2) (Fin 2) ℝ)
    (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (hY : (M₀ + t • M₁) * Y = t • M₁) :
    t * (∫ v : Fin 2 → ℝ, pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1)))) =
      godementInner3 ψ (pg (derivedPoly Y p)) h (M₀ + t • M₁) := by
  rw [godementInner3_pg_eq]
  refine (integral_const_mul (t : ℂ) _).symm.trans (integral_congr_ae (Eventually.of_forall fun v => ?_))
  have hv : t • sliceMat h M₁ v = (sliceMat h M₀ v + t • sliceMat h M₁ v) * Y := by
    rw [← sliceMat_add_smul, ← sliceMat_mul, hY, sliceMat_smul]
  show t * (pgDir p (sliceMat h M₀ v + t • sliceMat h M₁ v) (sliceMat h M₁ v) * ψ (ofReal (-(v 1)))) =
    pg (derivedPoly Y p) (sliceMat h (M₀ + t • M₁) v) * ψ (ofReal (-(v 1)))
  rw [← mul_assoc, smul_pgDir_eq_pg_derivedPoly p Y _ _ t hv, sliceMat_add_smul]

end Inner
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section Outer

private theorem hasDerivAt_integral_jacquetIntegrand3_line {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ)
    (a₃ : ZMod 2) (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1)))) (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1)
    (hnull : (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M₀ M₁ Y : Matrix (Fin 3) (Fin 3) ℝ)
    (hY : ∀ t : ℝ, (M₀ + t • M₁) * Y = t • M₁) (hrow : ∀ t : ℝ, t ≠ 0 → (M₀ + t • M₁) 2 ≠ 0)
    (γ : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ)) (hγ : ∀ t : ℝ, t ≠ 0 → realMat (γ t) = M₀ + t • M₁)
    (hγc : ContinuousOn γ ({0} : Set ℝ)ᶜ)
    (hmeas : ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg p) g) volume)
    (hmeas' : ∀ g : GL (Fin 3) (InfiniteAdeleRing ℚ),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g) volume)
    (hmaj : ∀ g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ,
      Integrable F volume ∧ ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg p) g e‖ ≤ F e)
    (hmaj' : ∀ g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ), ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ,
      Integrable F volume ∧
        ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e‖ ≤ F e)
    {t₀ : ℝ} (ht₀ : t₀ ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t) e)
      ((∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) (γ t₀) e) / t₀) t₀ := by
  obtain ⟨U, hU, Fm, hFm, hbound⟩ := hmaj' (γ t₀)
  obtain ⟨U₀, hU₀, Fm₀, hFm₀, hbound₀⟩ := hmaj (γ t₀)
  have ht₀pos : 0 < |t₀| := abs_pos.mpr ht₀
  have ht₀ne : |t₀| ≠ 0 := ht₀pos.ne'

  have hopen : ({0} : Set ℝ)ᶜ ∈ 𝓝 t₀ := isOpen_compl_singleton.mem_nhds (by simpa using ht₀)
  have hpre : γ ⁻¹' U ∈ 𝓝 t₀ := (hγc.continuousAt hopen).preimage_mem_nhds hU
  set s : Set ℝ := ball t₀ (|t₀| / 2) ∩ γ ⁻¹' U with hs_def
  have hs : s ∈ 𝓝 t₀ := inter_mem (ball_mem_nhds t₀ (by positivity)) hpre
  have hs_abs : ∀ t ∈ s, |t₀| / 2 ≤ |t| := by
    intro t ht
    have h1 : |t - t₀| < |t₀| / 2 := by simpa [Real.dist_eq] using ht.1
    have h2 := abs_sub_abs_le_abs_sub t₀ t
    rw [abs_sub_comm] at h2
    linarith
  have hs_ne : ∀ t ∈ s, t ≠ 0 := fun t ht h0 => by
    have := hs_abs t ht
    rw [h0, abs_zero] at this
    linarith

  set F' : ℝ → (Fin 2 → Fin 2 → ℝ) → ℂ :=
    fun t e => jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) (γ t) e / (t : ℂ) with hF'_def
  have hFm_nonneg : ∀ e, 0 ≤ Fm e := fun e => (norm_nonneg _).trans (hbound (γ t₀) (mem_of_mem_nhds hU) e)
  have h_bound : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, ∀ t ∈ s, ‖F' t e‖ ≤ 2 / |t₀| * Fm e := by
    refine Eventually.of_forall fun e t ht => ?_
    have htabs := hs_abs t ht
    have htpos : 0 < |t| := by linarith
    simp only [hF'_def, norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ htpos]
    calc ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) (γ t) e‖ ≤ Fm e := hbound (γ t) ht.2 e
      _ = 2 / |t₀| * Fm e * (|t₀| / 2) := by field_simp
      _ ≤ 2 / |t₀| * Fm e * |t| :=
          mul_le_mul_of_nonneg_left htabs (mul_nonneg (by positivity) (hFm_nonneg e))
  have hbound_int : Integrable (fun e => 2 / |t₀| * Fm e) volume := hFm.const_mul _
  have hF_int : Integrable (jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t₀)) volume :=
    hFm₀.mono' (hmeas (γ t₀)) (Eventually.of_forall fun e => hbound₀ (γ t₀) (mem_of_mem_nhds hU₀) e)
  have hF'_meas : AEStronglyMeasurable (F' t₀) volume := by
    simpa only [hF'_def, div_eq_mul_inv] using (hmeas' (γ t₀)).mul_const ((t₀ : ℂ)⁻¹)

  have hae : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e).det ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  have h_diff : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, ∀ t ∈ s,
      HasDerivAt (fun t' : ℝ => jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t') e) (F' t e) t := by
    refine hae.mono fun e hdet t ht => ?_
    have htne : t ≠ 0 := hs_ne t ht
    have htabs : 0 < |t| / 2 := by positivity
    have hrow' : ∀ t' ∈ closedBall t (|t| / 2), (M₀ + t' • M₁) 2 ≠ 0 := by
      intro t' ht'
      refine hrow t' fun h0 => ?_
      have h1 : |t' - t| ≤ |t| / 2 := by simpa [Real.dist_eq] using ht'
      rw [h0, zero_sub, abs_neg] at h1
      linarith [abs_pos.mpr htne]
    have hin := (hasDerivAt_inner ψ hχ hχ1 p hdet M₀ M₁ htabs hrow').mul_const (wFactor D u₃ a₃ a e)

    have hev : (fun t' : ℝ => jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (γ t') e) =ᶠ[𝓝 t]
        fun t' : ℝ => godementInner3 ψ (pg p) (Matrix.of e) (M₀ + t' • M₁) * wFactor D u₃ a₃ a e := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using htne : t ∈ ({0} : Set ℝ)ᶜ)] with t' ht'
      rw [jacquetIntegrand3_eq, hγ t' (by simpa using ht')]
    refine (hin.congr_of_eventuallyEq hev).congr_deriv ?_

    simp only [hF'_def]
    rw [jacquetIntegrand3_eq, hγ t htne, ← mul_inner_deriv_eq ψ p (Matrix.of e) M₀ M₁ Y t (hY t)]
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htne
    rw [eq_div_iff htc]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall fun t => hmeas (γ t)) hF_int
    hF'_meas h_bound hbound_int h_diff
  refine key.2.congr_deriv ?_
  simp only [hF'_def]
  exact integral_div _ _

end Outer
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace DualStripDecay

p2m_open "MeasureTheory Filter Topology AutomorphicForm.StandardKernel LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction.PolyGaussLine"

section Sign

private theorem pgDir_neg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (M D : Mat) : pgDir p M (-D) = -pgDir p M D := by
  have h := pgDir_smul p M D (-1)
  rw [neg_one_smul] at h
  rw [h, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]

private theorem pg_derivedPoly_neg (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ) (M : Mat) :
    pg (derivedPoly (-Y) p) M = -pg (derivedPoly Y p) M := by
  rw [pg_derivedPoly, pg_derivedPoly, Matrix.mul_neg, pgDir_neg]

private theorem godementInner3_pg_derivedPoly_neg (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (p : MvPolynomial (Fin 2 × Fin 3) ℂ) (Y : Matrix (Fin 3) (Fin 3) ℝ) (h : Matrix (Fin 2) (Fin 2) ℝ)
    (m : Matrix (Fin 3) (Fin 3) ℝ) :
    godementInner3 ψ (pg (derivedPoly (-Y) p)) h m = -godementInner3 ψ (pg (derivedPoly Y p)) h m := by
  rw [godementInner3_pg_eq, godementInner3_pg_eq]
  calc (∫ v : Fin 2 → ℝ, pg (derivedPoly (-Y) p) (sliceMat h m v) * ψ (ofReal (-(v 1))))
      = ∫ v : Fin 2 → ℝ, -(pg (derivedPoly Y p) (sliceMat h m v) * ψ (ofReal (-(v 1)))) :=
        integral_congr_ae (Eventually.of_forall fun v => by
          show pg (derivedPoly (-Y) p) (sliceMat h m v) * ψ (ofReal (-(v 1))) =
            -(pg (derivedPoly Y p) (sliceMat h m v) * ψ (ofReal (-(v 1))))
          rw [pg_derivedPoly_neg, neg_mul])
    _ = -∫ v : Fin 2 → ℝ, pg (derivedPoly Y p) (sliceMat h m v) * ψ (ofReal (-(v 1))) := integral_neg _

private theorem integral_jacquetIntegrand3_derivedPoly_neg {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ)
    (a₃ : ZMod 2) (a : ℝ) (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (Y : Matrix (Fin 3) (Fin 3) ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly (-Y) p)) g e =
      -∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e :=
  calc (∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly (-Y) p)) g e)
      = ∫ e : Fin 2 → Fin 2 → ℝ, -jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e :=
        integral_congr_ae (Eventually.of_forall fun e => by
          show jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly (-Y) p)) g e =
            -jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e
          rw [jacquetIntegrand3_eq, jacquetIntegrand3_eq, godementInner3_pg_derivedPoly_neg, neg_mul])
    _ = -∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly Y p)) g e := integral_neg _

end Sign
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section Reparam

private def pointAt (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) (y : ℝ) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  (L * G) * (G⁻¹ * iotaGL (diagUnitGL2 (unitCurve y)⁻¹) * G)

private def lineM₀ (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMat L * realMat G - realMat L * E11 * realMat G

private def lineM₁ (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMat L * E11 * realMat G

private def lineDir (G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  realMat G⁻¹ * E11 * realMat G

private def dualDir (G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) ℝ :=
  -lineDir G

private theorem realMat_one' : realMat (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) = 1 := by
  show ((realGL (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1
  rw [map_one, Units.val_one]

private theorem realMat_mul_realMat_inv (G : GL (Fin 3) (InfiniteAdeleRing ℚ)) : realMat G * realMat G⁻¹ = 1 := by
  rw [← realMat_mul, mul_inv_cancel, realMat_one']

private theorem E11_mul_E11 : E11 * E11 = E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem realMat_apply_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (i : Fin 3) : realMat g i ≠ 0 := by
  intro h0
  have hdet : (realMat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (realGL g).isUnit).ne_zero
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i fun j => congrFun h0 j)

private theorem line_mul_rowYc (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) (t : ℝ) :
    (lineM₀ L G + t • lineM₁ L G) * lineDir G = t • lineM₁ L G := by
  have hGG : ∀ Z : Matrix (Fin 3) (Fin 3) ℝ, realMat G * (realMat G⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, realMat_mul_realMat_inv, Matrix.one_mul]
  have hEE : ∀ Z : Matrix (Fin 3) (Fin 3) ℝ, E11 * (E11 * Z) = E11 * Z := fun Z => by
    rw [← Matrix.mul_assoc, E11_mul_E11]
  simp only [lineM₀, lineM₁, lineDir, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, hGG, hEE]
  abel

private theorem realMat_pointAt_inv (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) {t : ℝ} (ht : t ≠ 0) :
    realMat (pointAt L G t⁻¹) = lineM₀ L G + t • lineM₁ L G := by
  rw [pointAt, realMat_point, realCoord_unitCurve (inv_ne_zero ht), inv_inv]
  rfl

private theorem continuousOn_pointAt_inv (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ContinuousOn (fun t : ℝ => pointAt L G t⁻¹) ({0} : Set ℝ)ᶜ := by
  refine (continuousOn_pointCurve L G).comp continuousOn_inv₀ fun t ht => ?_
  have ht' : t ≠ 0 := by simpa using ht
  simpa using inv_ne_zero ht'

private theorem hasDerivAt_integral_pointAt {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (hχ : Continuous fun v : Fin 2 → ℝ => ψ (ofReal (-(v 1))))
    (hχ1 : ∀ v : Fin 2 → ℝ, ‖ψ (ofReal (-(v 1)))‖ ≤ 1)
    (hnull : (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0)
    (hmeas : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ a ψ (pg q) g) volume)
    (hmaj : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ a ψ (pg q) g e‖ ≤ F e)
    (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) (p : MvPolynomial (Fin 2 × Fin 3) ℂ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun y' : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (pointAt L G y') e)
      ((∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly (dualDir G) p)) (pointAt L G y) e) / y)
      y := by
  have hrow : ∀ t : ℝ, t ≠ 0 → (lineM₀ L G + t • lineM₁ L G) 2 ≠ 0 := by
    intro t ht
    rw [← realMat_pointAt_inv L G ht]
    exact realMat_apply_ne_zero _ 2
  have hcore := hasDerivAt_integral_jacquetIntegrand3_line D u₃ a₃ a ψ hχ hχ1 hnull p (lineM₀ L G) (lineM₁ L G)
    (lineDir G) (line_mul_rowYc L G) hrow (fun t : ℝ => pointAt L G t⁻¹) (fun t ht => realMat_pointAt_inv L G ht)
    (continuousOn_pointAt_inv L G) (hmeas p) (hmeas _) (hmaj p) (hmaj _) (inv_ne_zero hy)
  simp only [inv_inv] at hcore
  have hchain := HasDerivAt.scomp (x := y) hcore (hasDerivAt_inv hy)
  have hfun : ((fun t : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (pointAt L G t⁻¹) e) ∘
      fun y' : ℝ => y'⁻¹) =
        fun y' : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p) (pointAt L G y') e := by
    funext y'
    simp only [Function.comp_apply, inv_inv]
  rw [hfun] at hchain
  refine hchain.congr_deriv ?_
  rw [dualDir, integral_jacquetIntegrand3_derivedPoly_neg]
  set V : ℂ :=
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg (derivedPoly (lineDir G) p)) (pointAt L G y) e with hV
  show ((-(y ^ 2)⁻¹ : ℝ) : ℂ) * (V / ((y⁻¹ : ℝ) : ℂ)) = -V / (y : ℂ)
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  push_cast
  field_simp

end Reparam
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

section

open MeasureTheory Set

namespace SingularArrays

private theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

private theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

private theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingularArrays
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam CubicInduction.integrable_dualWhittakerFn3_jacquetVector3_prod"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "archZeta31 archZetaDual31 lowerUnipotent21 longWeyl3 dualWhittakerFn3 weylPrime3 transposeInv3_weylPrime3 transposeInv3 embedMat2 iotaGL coe_iotaGL diagUnitGL2 coe_diagUnitGL2 gaussian3 polyGauss3 godementInner3 jacquetIntegrand3 jacquetVector3 jacquetVector3_eq exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod integrable_dualWhittakerFn3_jacquetVector3_prod"
namespace DirectStripDecay
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Filter Topology NumberField AutomorphicForm AutomorphicForm.StandardKernel LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR LanglandsTunnell.CubicInduction.PolyGaussLine

private theorem norm_psi_le_one (s : ℝ) : ‖ArchR.psi s‖ ≤ 1 := by
  unfold ArchR.psi
  simp [Complex.norm_exp]

private theorem psiArch_eq_psi_realCoord (w : InfiniteAdeleRing ℚ) :
    NumberField.StandardAddChar.psiArch w = ArchR.psi (StandardKernel.realCoord w) := by
  have h1 : NumberField.StandardAddChar.psiArch w =
      NumberField.StandardAddChar.psiArchPlace Rat.infinitePlace (w Rat.infinitePlace) := by
    rw [NumberField.StandardAddChar.psiArch_apply]
    exact finprod_eq_single _ Rat.infinitePlace fun v hv => absurd (Subsingleton.elim v Rat.infinitePlace) hv
  rw [h1, NumberField.StandardAddChar.psiArchPlace_apply, ArchR.psi, StandardKernel.realCoord_apply]

private theorem realCoord_ratCast (a : ℚ) :
    StandardKernel.realCoord (algebraMap ℚ (InfiniteAdeleRing ℚ) a) = (a : ℝ) := by
  rw [← RingHom.comp_apply]
  exact eq_ratCast (StandardKernel.realCoord.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) a

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem psiInf_ofReal_neg (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x)) (t : ℝ) :
    psiInf (StandardKernel.ofReal (-t)) =
      Complex.exp (((-(2 * Real.pi * (a : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [hpsiInf, psiArch_eq_psi_realCoord, map_mul, realCoord_ratCast, realCoord_ofReal, ArchR.psi]
  congr 1
  push_cast
  ring

private theorem det_realMat_ne_zero (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (StandardKernel.realMat g).det ≠ 0 := by
  have hu : IsUnit (StandardKernel.realMat g) := (StandardKernel.realGL g).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

private theorem det_diagonal_mul (y : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (Matrix.diagonal ![y, 1, 1] * M).det = y * M.det := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  simp [Fin.prod_univ_three]

private theorem realMat_iotaGL_diagUnitGL2_mul (z : (InfiniteAdeleRing ℚ)ˣ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    StandardKernel.realMat (iotaGL (diagUnitGL2 z) * g) =
      Matrix.diagonal ![StandardKernel.realCoord (z : InfiniteAdeleRing ℚ), 1, 1] * StandardKernel.realMat g := by
  rw [StandardKernel.realMat_mul]
  congr 1
  rw [StandardKernel.realMat_eq, coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.diagonal]

private theorem quasiChar_ne_zero (u : ℂ) (b : ZMod 2) {x : ℝ} (hx : x ≠ 0) : quasiChar u b x ≠ 0 := by
  unfold quasiChar
  have hpos : (0 : ℝ) < |x| := abs_pos.mpr hx
  have h1 : ((|x| : ℝ) : ℂ) ^ u ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')]
    exact Complex.exp_ne_zero _
  refine mul_ne_zero h1 ?_
  split_ifs
  · exact one_ne_zero
  · rcases lt_or_gt_of_ne hx with h | h
    · simp [sign_neg h]
    · simp [sign_pos h]

end LanglandsTunnell.CubicInduction.DirectStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

noncomputable section

namespace DualStripDecay

p2m_open "MeasureTheory Set Filter Topology LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction LanglandsTunnell.Converse.ArchR AutomorphicForm.StandardKernel P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction.PolyGaussLine"

section Assembly

private theorem exists_rate_bound (P : RealArchParam) :
    ∃ c₀ : ℝ, ∀ b : ZMod 2,
      (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀) := by
  set m : Multiset ℂ := ∑ b : ZMod 2, ((P.twist 0 b).gammaR + (P.twist 0 b).gammaC) with hm
  obtain ⟨B, hB⟩ := (m.map fun μ : ℂ => -μ.re).toFinset.exists_le
  refine ⟨B + 1, fun b => ⟨fun μ hμ => ?_, fun ν hν => ?_⟩⟩
  · have h1 : μ ∈ m := by
      rw [hm, Multiset.mem_sum]
      exact ⟨b, Finset.mem_univ b, Multiset.mem_add.mpr (Or.inl hμ)⟩
    have h2 : -μ.re ∈ (m.map fun μ : ℂ => -μ.re).toFinset :=
      Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨μ, h1, rfl⟩)
    linarith [hB _ h2]
  · have h1 : ν ∈ m := by
      rw [hm, Multiset.mem_sum]
      exact ⟨b, Finset.mem_univ b, Multiset.mem_add.mpr (Or.inr hν)⟩
    have h2 : -ν.re ∈ (m.map fun μ : ℂ => -μ.re).toFinset :=
      Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨ν, h1, rfl⟩)
    linarith [hB _ h2]

private theorem quasiChar_zero_right (u : ℂ) (y : ℝ) : quasiChar u 0 y = ((|y| : ℝ) : ℂ) ^ u := by
  simp [quasiChar]

private theorem inv_quasiChar (u : ℂ) (b : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    (quasiChar u b y)⁻¹ = quasiChar (-u) b y := by
  have h := quasiChar_mul_quasiChar u (-u) b b hy
  rw [add_neg_cancel, CharTwo.add_self_eq_zero, quasiChar_zero_right, Complex.cpow_zero] at h
  exact inv_eq_of_mul_eq_one_right h

private theorem inv_ideleChar_eq (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (α : (InfiniteAdeleRing ℚ)ˣ) :
    ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) α : ℂˣ) : ℂ) =
      quasiChar (-t) (e : ZMod 2) (realCoord (α : InfiniteAdeleRing ℚ)) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, MonoidHom.comp_apply,
    ideleChar_section_eq_quasiChar_realCoord σ t e hte E hE α, inv_quasiChar _ _ (realCoord_unit_ne_zero α)]

private theorem det_realMat_pointAt (L G : GL (Fin 3) (InfiniteAdeleRing ℚ)) {y : ℝ} (hy : y ≠ 0) :
    (realMat (pointAt L G y)).det = (realMat L).det * (realMat G).det * y⁻¹ := by
  have h1 : (realMat G).det * (realMat G⁻¹).det = 1 := by
    rw [← Matrix.det_mul, realMat_mul_realMat_inv, Matrix.det_one]
  rw [pointAt]
  simp only [realMat_mul, Matrix.det_mul]
  rw [realMat_iotaGL_diagUnitGL2, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    realCoord_coe_inv, realCoord_unitCurve hy, mul_one]
  linear_combination ((realMat L).det * (realMat G).det * y⁻¹) * h1

private def movedIntegrand {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (σ' : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) (z : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ) : ℂ :=
  dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ a ψ S (h * gInf))
      (lowerUnipotent21 z.2 * iotaGL (diagUnitGL2 z.1) * weylPrime3) *
    ((σ' z.1 : ℂˣ) : ℂ) * ((‖(z.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ s

private theorem nativeIntegrand_shear {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ))
    (σ' : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ) (z : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ) :
    (fun q : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
        dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ a ψ S (h * gInf))
            (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * (weylPrime3 * transposeInv3 1)) *
          ((σ' q.1 : ℂˣ) : ℂ) * ((‖(q.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (shear z) *
        ((‖(z.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) =
      movedIntegrand D u₃ a₃ a ψ S gInf σ' s z := by
  obtain ⟨α, x⟩ := z
  simp only [shear, movedIntegrand]
  rw [iotaGL_diagUnitGL2_mul_lowerUnipotent21, Units.mul_inv_cancel_right, transposeInv3_one, mul_one]
  have hne : ((‖(α : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_unit_ne_zero α)
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one, mul_assoc, div_mul_cancel₀ _ hne]

private theorem movedIntegrand_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (p : MvPolynomial (Fin 2 × Fin 3) ℂ)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (s : ℂ) (α : (InfiniteAdeleRing ℚ)ˣ) (x : InfiniteAdeleRing ℚ) :
    movedIntegrand D u₃ a₃ a ψ (pg p) gInf (σ.comp E)⁻¹ s (α, x) =
      quasiChar (u₃ + 1) a₃
          ((realMat (longWeyl3 * transposeInv3 (lowerUnipotent21 x))).det * (realMat (weylPrime3 * gInf)).det) *
        ((∫ v : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p)
            (pointAt (longWeyl3 * transposeInv3 (lowerUnipotent21 x)) (weylPrime3 * gInf)
              (realCoord (α : InfiniteAdeleRing ℚ))) v) *
          quasiChar (s - (u₃ + t + 2)) (a₃ + (e : ZMod 2)) (realCoord (α : InfiniteAdeleRing ℚ))) *
        ((|realCoord (α : InfiniteAdeleRing ℚ)| : ℝ) : ℂ) := by
  have hy : realCoord (α : InfiniteAdeleRing ℚ) ≠ 0 := realCoord_unit_ne_zero α
  have hpt : pointAt (longWeyl3 * transposeInv3 (lowerUnipotent21 x)) (weylPrime3 * gInf)
      (realCoord (α : InfiniteAdeleRing ℚ)) =
        (longWeyl3 * transposeInv3 (lowerUnipotent21 x) * (weylPrime3 * gInf)) *
          ((weylPrime3 * gInf)⁻¹ * iotaGL (diagUnitGL2 α⁻¹) * (weylPrime3 * gInf)) := by
    rw [pointAt, unitCurve_realCoord]
  simp only [movedIntegrand]
  rw [inv_ideleChar_eq σ t e hte E hE α, norm_eq_abs_realCoord,
    dualWhittakerFn3_comp_mul_lowerUnipotent21_mul_iotaGL_diagUnitGL2_mul (jacquetVector3 D u₃ a₃ a ψ (pg p)) gInf x α,
    ← hpt, jacquetVector3_eq,
    det_realMat_pointAt _ _ hy, quasiChar_mul, quasiChar_inv]

  have he : -(u₃ + 1) + -t + s = s - (u₃ + t + 2) + 1 := by ring
  have hw : quasiChar (-(u₃ + 1)) a₃ (realCoord (α : InfiniteAdeleRing ℚ)) *
      quasiChar (-t) (e : ZMod 2) (realCoord (α : InfiniteAdeleRing ℚ)) *
        ((|realCoord (α : InfiniteAdeleRing ℚ)| : ℝ) : ℂ) ^ s =
      quasiChar (s - (u₃ + t + 2)) (a₃ + (e : ZMod 2)) (realCoord (α : InfiniteAdeleRing ℚ)) *
        ((|realCoord (α : InfiniteAdeleRing ℚ)| : ℝ) : ℂ) := by
    rw [← quasiChar_zero_right s, ← Complex.cpow_one ((|realCoord (α : InfiniteAdeleRing ℚ)| : ℝ) : ℂ),
      ← quasiChar_zero_right 1, quasiChar_mul_quasiChar (-(u₃ + 1)) (-t) a₃ (e : ZMod 2) hy,
      quasiChar_mul_quasiChar (-(u₃ + 1) + -t) s (a₃ + (e : ZMod 2)) 0 hy,
      quasiChar_mul_quasiChar (s - (u₃ + t + 2)) 1 (a₃ + (e : ZMod 2)) 0 hy, he]
  linear_combination
    (quasiChar (u₃ + 1) a₃
        ((realMat (longWeyl3 * transposeInv3 (lowerUnipotent21 x))).det * (realMat (weylPrime3 * gInf)).det) *
      ∫ v : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ (pg p)
        (pointAt (longWeyl3 * transposeInv3 (lowerUnipotent21 x)) (weylPrime3 * gInf)
          (realCoord (α : InfiniteAdeleRing ℚ))) v) * hw

private theorem aestronglyMeasurable_of_continuousOn_compl_zero {F : ℝ → ℂ}
    (hF : ContinuousOn F ({0} : Set ℝ)ᶜ) : AEStronglyMeasurable F (volume : Measure ℝ) := by
  have h := hF.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
  rwa [Measure.restrict_eq_self_of_ae_mem] at h
  rw [ae_iff]
  simp

private theorem ae_ne_zero_real : ∀ᵐ y : ℝ, y ≠ 0 := by
  rw [ae_iff]
  simp

open scoped Classical in

private theorem dual_main
    (P₂ : RealArchParam) (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm volume)
    (ν_mul : Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₁ : ℝ)
    (hc₁ : ∀ b : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 b).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 b).gammaC, -ν.re < c₁))
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ)
    (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₁ σ₂ : ℝ) (N : ℕ)
    (hσ₁ : max c₁ u₃.re + t.re < σ₁) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      |s.im| ^ N *
        ‖archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) s 1‖ ≤
          C := by

  by_cases hσ₁₂ : σ₁ ≤ σ₂
  swap
  · exact ⟨0, 0, fun s h₁ h₂ _ => absurd (h₁.trans h₂) hσ₁₂⟩
  obtain ⟨p₀, hp₀⟩ := hS
  subst hp₀

  have hν' : ν_add = nuPinned (ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2))) := hν_add
  haveI : SFinite ν_add := by rw [hν']; infer_instance
  haveI : LocallyCompactSpace (InfiniteAdeleRing ℚ)ˣ :=
    DirectArchZetaBound.isOpenEmbedding_realCoord_units.locallyCompactSpace
  haveI : SecondCountableTopology (InfiniteAdeleRing ℚ)ˣ :=
    DirectArchZetaBound.isOpenEmbedding_realCoord_units.isEmbedding.secondCountableTopology
  haveI : SFinite ν_mul := inferInstance

  let G₀ : GL (Fin 3) (InfiniteAdeleRing ℚ) := weylPrime3 * gInf
  let p : ℕ → MvPolynomial (Fin 2 × Fin 3) ℂ := fun k => Nat.rec p₀ (fun _ q => derivedPoly (dualDir G₀) q) k
  let Lx : InfiniteAdeleRing ℚ → GL (Fin 3) (InfiniteAdeleRing ℚ) := fun x =>
    longWeyl3 * transposeInv3 (lowerUnipotent21 x)
  let f : InfiniteAdeleRing ℚ → ℕ → ℝ → ℂ := fun x k y =>
    ∫ v : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg (p k)) (pointAt (Lx x) G₀ y) v
  let cc : ℂ → ℂ := fun s => s - (u₃ + t + 2)
  let cx : InfiniteAdeleRing ℚ → ℂ := fun x => quasiChar (u₃ + 1) a₃ ((realMat (Lx x)).det * (realMat G₀).det)
  let M : ℕ → ℂ → (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ → ℂ := fun k s =>
    movedIntegrand D u₃ a₃ (a : ℝ) psiInf (pg (p k)) gInf (σ.comp E)⁻¹ s
  let Z : ℕ → ℂ → ℂ := fun k s =>
    archZetaDual31 ν_mul ν_add (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (p k)) (h * gInf)) (σ.comp E) s 1
  have hmem : ∀ q : MvPolynomial (Fin 2 × Fin 3) ℂ, pg q ∈ polyGauss3 := fun q => ⟨q, rfl⟩

  obtain ⟨c₀, hc₀⟩ := exists_rate_bound P₂
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hmaj : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g₀ : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      ∃ U ∈ nhds g₀, ∃ F : (Fin 2 → Fin 2 → ℝ) → ℝ, Integrable F volume ∧
        ∀ g ∈ U, ∀ v : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) g v‖ ≤ F v := by
    intro q g₀
    obtain ⟨h1, -, -, -⟩ :=
      exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod u₃ a₃ a psiInf hpsiInf ha D (pg q)
        (hmem q) c₀ hc₀
    obtain ⟨U, hU, F, hF, hb⟩ := h1 g₀ (max c₀ (-u₃.re) + 1) (lt_add_one _)
    exact ⟨U, hU, fun v => |(a : ℝ)| ^ (1 - (max c₀ (-u₃.re) + 1)) * F v, hF.const_mul _,
      fun g hg v => hb g hg (a : ℝ) ha' v⟩
  have hmeas : ∀ (q : MvPolynomial (Fin 2 × Fin 3) ℂ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      AEStronglyMeasurable (jacquetIntegrand3 D u₃ a₃ (a : ℝ) psiInf (pg q) g) volume := fun q =>
    (exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod u₃ a₃ a psiInf hpsiInf ha D (pg q)
      (hmem q) c₀ hc₀).2.2.2

  have hχc : Continuous fun v : Fin 2 → ℝ => psiInf (StandardKernel.ofReal (-(v 1))) := by
    simp only [DirectStripDecay.psiInf_ofReal_neg a psiInf hpsiInf]
    fun_prop
  have hχ1 : ∀ v : Fin 2 → ℝ, ‖psiInf (StandardKernel.ofReal (-(v 1)))‖ ≤ 1 := fun v =>
    le_of_eq (by rw [DirectStripDecay.psiInf_ofReal_neg a psiInf hpsiInf, Complex.norm_exp_ofReal_mul_I])

  have hf : ∀ x : InfiniteAdeleRing ℚ, ∀ k : ℕ, ∀ y : ℝ, y ≠ 0 → HasDerivAt (f x k) (f x (k + 1) y / y) y :=
    fun x k y hy =>
      hasDerivAt_integral_pointAt D u₃ a₃ (a : ℝ) psiInf hχc hχ1 SingularArrays.volume_setOf_det_eq_zero hmeas hmaj
        (Lx x) G₀ (p k) hy
  have hfcont : ∀ x : InfiniteAdeleRing ℚ, ∀ k : ℕ, ContinuousOn (f x k) ({0} : Set ℝ)ᶜ := fun x k y hy =>
    (hf x k y (by simpa using hy)).continuousAt.continuousWithinAt

  have hw : ∀ s : ℂ, ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (quasiChar (cc s) (a₃ + (e : ZMod 2))) (cc s * quasiChar (cc s) (a₃ + (e : ZMod 2)) y / y) y :=
    fun s y hy => hasDerivAt_quasiChar (cc s) (a₃ + (e : ZMod 2)) hy
  have hwcont : ∀ s : ℂ, ContinuousOn (quasiChar (cc s) (a₃ + (e : ZMod 2))) ({0} : Set ℝ)ᶜ := fun s y hy =>
    (hw s y (by simpa using hy)).continuousAt.continuousWithinAt

  have hint : ∀ k : ℕ, ∀ s : ℂ, max c₁ u₃.re + t.re < s.re → Integrable (M k s) (ν_mul.prod ν_add) := by
    intro k s hs
    have h1 := LanglandsTunnell.CubicInduction.integrable_dualWhittakerFn3_jacquetVector3_prod P₂ D u₃ a₃ E hE a psiInf
      hpsiInf ν_add hν_add ν_mul ha (pg (p k)) (hmem (p k)) c₁ hc₁ σ hσ t e hte gInf s hs
    have h2 := integrable_comp_shear_mul_norm ν_mul (ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)))
      (K := fun q : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ =>
        dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (p k)) (h * gInf))
            (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * (weylPrime3 * transposeInv3 1)) *
          ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) q.1 : ℂˣ) : ℂ) *
            ((‖(q.1 : InfiniteAdeleRing ℚ)‖ : ℝ) : ℂ) ^ (s - 1)) (by rw [hν'] at h1; exact h1)
    rw [hν']
    refine h2.congr (Eventually.of_forall fun z => ?_)
    exact nativeIntegrand_shear D u₃ a₃ (a : ℝ) psiInf (pg (p k)) gInf (σ.comp E)⁻¹ s z

  have hZ : ∀ k : ℕ, ∀ s : ℂ, max c₁ u₃.re + t.re < s.re →
      Z k s = ∫ z, M k s z ∂(ν_mul.prod ν_add) := by
    intro k s hs
    rw [integral_prod _ (hint k s hs)]
    show archZetaDual31 ν_mul ν_add _ (σ.comp E) s 1 = _
    rw [archZetaDual31_one_eq ν_mul a ν_add hν_add]
    refine integral_congr_ae (Eventually.of_forall fun α => ?_)
    show (∫ x, _ ∂ν_add) * _ * _ =
      ∫ x, movedIntegrand D u₃ a₃ (a : ℝ) psiInf (pg (p k)) gInf (σ.comp E)⁻¹ s (α, x) ∂ν_add
    simp only [movedIntegrand, integral_mul_const]
  have hZ' : ∀ k : ℕ, ∀ s : ℂ, max c₁ u₃.re + t.re < s.re →
      Z k s = ∫ x, (∫ α, M k s (α, x) ∂ν_mul) ∂ν_add := fun k s hs =>
    (hZ k s hs).trans (integral_prod_symm _ (hint k s hs))

  obtain ⟨κ, -, hκ⟩ := DirectArchZetaBound.exists_haarScalar ν_mul
  have hν : ν_mul ≠ 0 := NeZero.ne ν_mul
  have hT : Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => realCoord (z : InfiniteAdeleRing ℚ) :=
    measurable_realCoord_units

  let Φ : InfiniteAdeleRing ℚ → ℕ → ℂ → ℝ → ℂ := fun x k s y =>
    cx x * (f x k y * quasiChar (cc s) (a₃ + (e : ZMod 2)) y) * ((|y| : ℝ) : ℂ)
  have hΦmeas : ∀ x k s, AEStronglyMeasurable (Φ x k s) volume := by
    intro x k s
    refine aestronglyMeasurable_of_continuousOn_compl_zero ?_
    exact (continuousOn_const.mul ((hfcont x k).mul (hwcont s))).mul
      (Complex.continuous_ofReal.comp_continuousOn continuous_abs.continuousOn)
  have hMΦ : ∀ x k s (α : (InfiniteAdeleRing ℚ)ˣ), M k s (α, x) = Φ x k s (realCoord (α : InfiniteAdeleRing ℚ)) :=
    fun x k s α => movedIntegrand_eq D u₃ a₃ (a : ℝ) psiInf (p k) gInf σ t e hte E hE s α x
  have hΦdiv : ∀ x k s, (fun y : ℝ => Φ x k s y * ((|y| : ℝ) : ℂ)⁻¹) =ᵐ[volume]
      fun y : ℝ => cx x * (f x k y * quasiChar (cc s) (a₃ + (e : ZMod 2)) y) := by
    intro x k s
    filter_upwards [ae_ne_zero_real] with y hy
    have : ((|y| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hy)
    exact mul_inv_cancel_right₀ this _
  have htrans : ∀ x k s, ∫ α, M k s (α, x) ∂ν_mul =
      (κ : ℂ) * (cx x * ∫ y : ℝ, f x k y * quasiChar (cc s) (a₃ + (e : ZMod 2)) y) := by
    intro x k s
    rw [show (∫ α, M k s (α, x) ∂ν_mul) = ∫ α, Φ x k s (realCoord (α : InfiniteAdeleRing ℚ)) ∂ν_mul from
        integral_congr_ae (Eventually.of_forall fun α => hMΦ x k s α),
      (AbsInvDensity.integral_comp_eq ν_mul _ hT κ hκ hν (Φ x k s) (hΦmeas x k s)).2,
      integral_congr_ae (hΦdiv x k s)]
    exact congrArg (fun r : ℂ => (κ : ℂ) * r) (integral_const_mul _ _)
  have hcx : ∀ x : InfiniteAdeleRing ℚ, cx x ≠ 0 := fun x =>
    DirectStripDecay.quasiChar_ne_zero _ _ (mul_ne_zero (DirectStripDecay.det_realMat_ne_zero _)
      (DirectStripDecay.det_realMat_ne_zero _))
  have hfib_int : ∀ x k s, Integrable (fun α => M k s (α, x)) ν_mul →
      Integrable (fun y : ℝ => f x k y * quasiChar (cc s) (a₃ + (e : ZMod 2)) y) volume := by
    intro x k s hx
    have h1 : Integrable (fun α : (InfiniteAdeleRing ℚ)ˣ => Φ x k s (realCoord (α : InfiniteAdeleRing ℚ))) ν_mul :=
      hx.congr (Eventually.of_forall fun α => hMΦ x k s α)
    have h2 := ((AbsInvDensity.integrable_comp_iff ν_mul _ hT κ hκ hν (Φ x k s) (hΦmeas x k s)).1 h1).congr
      (hΦdiv x k s)
    have h3 := h2.const_mul (cx x)⁻¹
    refine h3.congr (Eventually.of_forall fun y => ?_)
    exact inv_mul_cancel_left₀ (hcx x) _

  have hiter : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → (cc s + 1) ^ N * Z 0 s = (-1 : ℂ) ^ N * Z N s := by
    intro s hs₁ _
    have hs : max c₁ u₃.re + t.re < s.re := lt_of_lt_of_le hσ₁ hs₁

    have hae : ∀ᵐ x ∂ν_add, ∀ k, k ≤ N → Integrable (fun α => M k s (α, x)) ν_mul := by
      rw [ae_all_iff]
      intro k
      by_cases hk : k ≤ N
      · exact ((hint k s hs).swap.prod_right_ae).mono fun x hx _ => hx
      · exact Eventually.of_forall fun x hk' => absurd hk' hk
    rw [hZ' 0 s hs, hZ' N s hs]
    calc (cc s + 1) ^ N * ∫ x, (∫ α, M 0 s (α, x) ∂ν_mul) ∂ν_add
        = ∫ x, (cc s + 1) ^ N * ∫ α, M 0 s (α, x) ∂ν_mul ∂ν_add := (integral_const_mul _ _).symm
      _ = ∫ x, (-1 : ℂ) ^ N * ∫ α, M N s (α, x) ∂ν_mul ∂ν_add := by
          refine integral_congr_ae (hae.mono fun x hx => ?_)
          show (cc s + 1) ^ N * ∫ α, M 0 s (α, x) ∂ν_mul = (-1 : ℂ) ^ N * ∫ α, M N s (α, x) ∂ν_mul
          rw [htrans x 0 s, htrans x N s]
          have hstep := StripDecay.iterate (f := f x) (w := quasiChar (cc s) (a₃ + (e : ZMod 2))) (c := cc s) N
            (fun k _ y hy => hf x k y hy) (hw s) (fun k hk => hfib_int x k s (hx k hk))
          linear_combination ((κ : ℂ) * cx x) * hstep
      _ = (-1 : ℂ) ^ N * ∫ x, (∫ α, M N s (α, x) ∂ν_mul) ∂ν_add := integral_const_mul _ _

  have hbound : ∃ B : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z N s‖ ≤ B := by

    let F : (InfiniteAdeleRing ℚ)ˣ × InfiniteAdeleRing ℚ → ℂ := fun z =>
      dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (p N)) (h * gInf))
          (lowerUnipotent21 z.2 * iotaGL (diagUnitGL2 z.1) * weylPrime3) *
        ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) z.1 : ℂˣ) : ℂ)
    let w : ℂ → ℝ → ℂ := fun s y => ((|y| : ℝ) : ℂ) ^ s
    have hMF : ∀ s : ℂ, M N s = fun z => F z * w s (realCoord (z.1 : InfiniteAdeleRing ℚ)) := by
      intro s
      funext z
      show movedIntegrand D u₃ a₃ (a : ℝ) psiInf (pg (p N)) gInf (σ.comp E)⁻¹ s z =
        dualWhittakerFn3 (fun h => jacquetVector3 D u₃ a₃ (a : ℝ) psiInf (pg (p N)) (h * gInf))
            (lowerUnipotent21 z.2 * iotaGL (diagUnitGL2 z.1) * weylPrime3) *
          ((((σ.comp E)⁻¹ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) z.1 : ℂˣ) : ℂ) *
            ((|realCoord (z.1 : InfiniteAdeleRing ℚ)| : ℝ) : ℂ) ^ s
      rw [movedIntegrand, norm_eq_abs_realCoord]
    have hwabs : ∀ s : ℂ, ∀ y : ℝ, y ≠ 0 → ‖w s y‖ = |y| ^ (s.re + 0) := by
      intro s y hy
      show ‖((|y| : ℝ) : ℂ) ^ s‖ = |y| ^ (s.re + 0)
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy), add_zero]
    have hy : ∀ᵐ z ∂(ν_mul.prod ν_add), realCoord ((z.1 : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) ≠ 0 :=
      Eventually.of_forall fun z => realCoord_unit_ne_zero z.1
    have h₁ :
        Integrable (fun z => F z * w (σ₁ : ℂ) (realCoord (z.1 : InfiniteAdeleRing ℚ))) (ν_mul.prod ν_add) := by
      rw [← hMF]
      exact hint N (σ₁ : ℂ) (by rw [Complex.ofReal_re]; exact hσ₁)
    have h₂ :
        Integrable (fun z => F z * w (σ₂ : ℂ) (realCoord (z.1 : InfiniteAdeleRing ℚ))) (ν_mul.prod ν_add) := by
      rw [← hMF]
      exact hint N (σ₂ : ℂ) (by rw [Complex.ofReal_re]; exact lt_of_lt_of_le hσ₁ hσ₁₂)
    refine ⟨(∫ z, ‖F z * w (σ₁ : ℂ) (realCoord (z.1 : InfiniteAdeleRing ℚ))‖ ∂(ν_mul.prod ν_add)) +
      ∫ z, ‖F z * w (σ₂ : ℂ) (realCoord (z.1 : InfiniteAdeleRing ℚ))‖ ∂(ν_mul.prod ν_add), fun s hs₁ hs₂ => ?_⟩
    rw [hZ N s (lt_of_lt_of_le hσ₁ hs₁), hMF s]
    exact StripDecay.norm_integral_le_of_strip hy hwabs h₁ h₂ s hs₁ hs₂

  obtain ⟨B, hB⟩ := hbound
  exact StripDecay.decay_of_identity (Z := Z) (c := cc) (d := -(u₃ + t + 1)) N hiter hB fun s => by
    show s - (u₃ + t + 2) + 1 = s + -(u₃ + t + 1)
    ring

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end DualStripDecay
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.DualStripDecay"

open scoped Classical in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le.LanglandsTunnell.CubicInduction in

theorem solution
    (P₂ : RealArchParam) (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₁ : ℝ)
    (hc₁ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.dual.twist 0 a).gammaR, -μ.re < c₁) ∧ (∀ ν ∈ (P₂.dual.twist 0 a).gammaC, -ν.re < c₁))
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hσ : IsAdmissibleTwist ℚ σ)
    (t : ℂ) (e : ℤ) (hte : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ₁ σ₂ : ℝ) (N : ℕ)
    (hσ₁ : max c₁ u₃.re + t.re < σ₁) :
    ∃ C T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      |s.im| ^ N *
        ‖archZetaDual31 ν_mul ν_add (fun h => (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (h * gInf)) (σ.comp E) s 1‖ ≤
          C := by
  exact DualStripDecay.dual_main P₂ D u₃ a₃ E hE a psiInf hpsiInf ν_add hν_add ν_mul ha S hS c₁ hc₁ σ hσ t e hte gInf
    σ₁ σ₂ N hσ₁

end S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_pow_mul_norm_archZetaDual31_jacquetVector3_le (solution)
