-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archZeta30_jacquetVector3_eq_archFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/952d7e6f-a447-5648-bf7a-29ca29a9bac9

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_jacquetIntegrand3_dilate_mul_quasiChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

section
open MeasureTheory Set

namespace AbsInvDensity

private noncomputable def nnDensity (y : ℝ) : NNReal := Real.toNNReal |y|⁻¹

private theorem measurable_nnDensity : Measurable nnDensity :=
  (measurable_abs.inv).real_toNNReal

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

private theorem integral_comp_eq {G : Type*} [MeasurableSpace G] (μ : Measure G) (T : G → ℝ) (hT : Measurable T)
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

end

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
    simp [M4aHerbrand.infPart] at h
    exact h
  have h2' : ((E z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := by
    have h := congrArg Units.val h2
    simp [RatIdele.finPart] at h
    exact h
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

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam RealArchParam.discrete RealArchParam.principal"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "archZeta30 iotaGL diagUnitGL2 polyGauss3 godementInner3 jacquetVector3 jacquetVector3_iotaGL_diagUnitGL2_mul integrable_jacquetIntegrand3_dilate_mul_quasiChar"
namespace JacquetUnfold
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory Set

private theorem diagOne_mul_diagOne (x y : ℝ) : ArchR.diagOne x * ArchR.diagOne y = ArchR.diagOne (x * y) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unfold_core {G X : Type*} [MeasurableSpace G] [MeasurableSpace X] (μ : Measure G) (ν : Measure X)
    [SFinite ν] (T : G → ℝ) (κ : ℝ)
    (htrans : ∀ f : ℝ → ℂ, AEStronglyMeasurable f volume →
      ∫ z, f (T z) ∂μ = (κ : ℂ) * ∫ y : ℝ, f y * ((|y| : ℝ) : ℂ)⁻¹)
    (Φ : G → ℂ) (VEC : ℝ → ℂ) (a : ℝ) (h_torus : ∀ z, Φ z = VEC (a * T z))
    (χ : G → ℂ) (t : ℂ) (ē : ZMod 2) (hχ : ∀ z, χ z = ArchR.quasiChar t ē (T z))
    (nrm : G → ℝ) (hn : ∀ z, nrm z = |T z|)
    (q₁ : ℂ) (H : X → ℂ) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (inv : X → Matrix (Fin 2) (Fin 2) ℝ)
    (hVEC : ∀ b : ℝ, VEC b = q₁ * ∫ x, H x * W (ArchR.diagOne b * inv x) ∂ν)
    (s : ℂ)
    (hint : Integrable (fun p : ℝ × X =>
      H p.2 * W (ArchR.diagOne (a * p.1) * inv p.2) * ArchR.quasiChar t ē p.1 * ((|p.1| : ℝ) : ℂ) ^ (s - 1) *
        ((|p.1| : ℝ) : ℂ)⁻¹) (volume.prod ν))
    (AF : ℂ) (ZE : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hzeta : ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → ∫ y : ℝ, ArchR.zetaIntegrand W g t ē s y = AF * ZE g)
    (hdet : ∀ᵐ x ∂ν, (ArchR.diagOne a * inv x).det ≠ 0) :
    ∫ z, Φ z * χ z * ((nrm z : ℝ) : ℂ) ^ (s - 1) ∂μ =
      (κ : ℂ) * AF * (q₁ * ∫ x, H x * ZE (ArchR.diagOne a * inv x) ∂ν) := by

  set K : ℝ → X → ℂ := fun y x =>
    H x * W (ArchR.diagOne (a * y) * inv x) * ArchR.quasiChar t ē y * ((|y| : ℝ) : ℂ) ^ (s - 1) *
      ((|y| : ℝ) : ℂ)⁻¹ with hK
  have hKint : Integrable (Function.uncurry K) (volume.prod ν) := hint

  set f : ℝ → ℂ := fun y => VEC (a * y) * ArchR.quasiChar t ē y * ((|y| : ℝ) : ℂ) ^ (s - 1) with hf
  have h1 : (fun z => Φ z * χ z * ((nrm z : ℝ) : ℂ) ^ (s - 1)) = fun z => f (T z) := by
    funext z; simp only [hf, h_torus z, hχ z, hn z]

  have hmarg : ∀ y : ℝ, ∫ x, K y x ∂ν =
      (∫ x, H x * W (ArchR.diagOne (a * y) * inv x) ∂ν) * (ArchR.quasiChar t ē y * ((|y| : ℝ) : ℂ) ^ (s - 1) *
        ((|y| : ℝ) : ℂ)⁻¹) := by
    intro y
    have e : ∫ x, K y x ∂ν = ∫ x, (H x * W (ArchR.diagOne (a * y) * inv x)) * (ArchR.quasiChar t ē y *
        ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹) ∂ν := by
      congr 1; funext x; simp only [hK]; ring
    rw [e]
    exact integral_mul_const _ _

  have hfm : AEStronglyMeasurable f volume := by
    have hm1 : AEStronglyMeasurable (fun y => ∫ x, K y x ∂ν) volume := hKint.1.integral_prod_right'
    have hm2 : AEStronglyMeasurable (fun y : ℝ => q₁ * (∫ x, K y x ∂ν) * ((|y| : ℝ) : ℂ)) volume :=
      (aestronglyMeasurable_const.mul hm1).mul
        (Complex.continuous_ofReal.comp continuous_abs).aestronglyMeasurable
    refine hm2.congr ?_
    have hnull : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
      rw [ae_iff]; simp only [ne_eq, not_not, setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hnull] with y hy
    have hy' : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr hy)
    simp only [hf, hmarg y, hVEC (a * y)]
    field_simp

  rw [h1, htrans f hfm]

  have h3 : (fun y => f y * ((|y| : ℝ) : ℂ)⁻¹) = fun y => q₁ * ∫ x, K y x ∂ν := by
    funext y
    simp only [hf, hmarg y, hVEC (a * y)]
    ring
  have e4 : ∫ y : ℝ, q₁ * ∫ x, K y x ∂ν = q₁ * ∫ y : ℝ, ∫ x, K y x ∂ν := integral_const_mul _ _
  rw [h3, e4]

  rw [integral_integral_swap hKint]

  have h5 : ∀ x : X, ∫ y, K y x = H x * ∫ y, ArchR.zetaIntegrand W (ArchR.diagOne a * inv x) t ē s y := by
    intro x
    have e : ∫ y, K y x = ∫ y, H x * ArchR.zetaIntegrand W (ArchR.diagOne a * inv x) t ē s y := by
      congr 1; funext y
      simp only [hK, ArchR.zetaIntegrand, ← Matrix.mul_assoc, diagOne_mul_diagOne, mul_comm y a]
      ring
    rw [e]
    exact integral_const_mul _ _
  have h6 : (fun x : X => ∫ y, K y x) =ᵐ[ν] fun x => AF * (H x * ZE (ArchR.diagOne a * inv x)) := by
    filter_upwards [hdet] with x hx
    rw [h5 x, hzeta _ hx]
    ring
  have e7 : ∫ x, AF * (H x * ZE (ArchR.diagOne a * inv x)) ∂ν = AF * ∫ x, H x * ZE (ArchR.diagOne a * inv x) ∂ν :=
    integral_const_mul _ _
  rw [integral_congr_ae h6, e7]
  ring

end LanglandsTunnell.CubicInduction.JacquetUnfold

open scoped Classical in
open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul.LanglandsTunnell.CubicInduction in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)
    (c₀ : ℝ)
    (hc₀ : ∀ a : ZMod 2,
      (∀ μ ∈ (P₂.twist 0 a).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P₂.twist 0 a).gammaC, -ν.re < c₀))
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∀ (t : ℂ) (e : ℤ), (∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e) →
      ∀ (gInf : GL (Fin 3) (InfiniteAdeleRing ℚ)) (s : ℂ),
        max c₀ (-(uR w₀ h₀).re) - t.re < s.re → D.zeta_abscissa < s.re + t.re →
        archZeta30 ν_mul (fun h => (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (h * gInf))
            (σ.comp E) s 1 =
          (κ : ℂ) * (P₂.twist t (e : ZMod 2)).archFactor s *
            (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (StandardKernel.realMat gInf).det *
              ∫ x : Fin 2 → Fin 2 → ℝ,
                godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
                  ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of x).det *
                    (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                  D.zetaEntire (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹) t (e : ZMod 2) s) := by
  intro σ _ t e hσ gInf s hreg₁ hreg₂
  have hT : Measurable fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ) :=
    measurable_realCoord_units
  have hν : ν_mul ≠ 0 := NeZero.ne ν_mul
  have htrans : ∀ f : ℝ → ℂ, MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume →
      ∫ z, f (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ∂ν_mul =
        (κ : ℂ) * ∫ y : ℝ, f y * ((|y| : ℝ) : ℂ)⁻¹ :=
    fun f hf => (AbsInvDensity.integral_comp_eq ν_mul _ hT κ hκ hν f hf).2
  have ha' : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha
  have hdet : ∀ᵐ x : Fin 2 → Fin 2 → ℝ ∂MeasureTheory.volume, (ArchR.diagOne (a : ℝ) * (Matrix.of x)⁻¹).det ≠ 0 := by
    have h0 : ∀ᵐ x : Fin 2 → Fin 2 → ℝ ∂MeasureTheory.volume, (Matrix.of x).det ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa only [ne_eq, not_not] using SingularArrays.volume_setOf_det_eq_zero
    filter_upwards [h0] with x hx
    have hinv : ((Matrix.of x)⁻¹).det ≠ 0 :=
      (Matrix.isUnit_nonsing_inv_det_iff.mpr (isUnit_iff_ne_zero.mpr hx)).ne_zero
    have hdiag : (ArchR.diagOne (a : ℝ)).det = (a : ℝ) := by
      simp [ArchR.diagOne, Matrix.det_fin_two_of]
    rw [Matrix.det_mul, hdiag]
    exact mul_ne_zero ha' hinv
  unfold archZeta30
  exact LanglandsTunnell.CubicInduction.JacquetUnfold.unfold_core ν_mul MeasureTheory.volume
    (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) κ htrans
    (fun z => jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S (iotaGL (diagUnitGL2 z) * 1 * gInf))
    (fun b => jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) b psiInf S gInf) (a : ℝ)
    (fun z => by
      simp only [mul_one]
      exact jacquetVector3_iotaGL_diagUnitGL2_mul D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S z gInf)
    (fun z => (((σ.comp E) z : ℂˣ) : ℂ)) t (e : ZMod 2)
    (fun z => by
      simp only [MonoidHom.comp_apply]
      exact ideleChar_section_eq_quasiChar_realCoord σ t e hσ E hE z)
    (fun z => ‖(z : InfiniteAdeleRing ℚ)‖) (fun z => norm_eq_abs_realCoord (z : InfiniteAdeleRing ℚ))
    (ArchR.quasiChar (uR w₀ h₀ + 1) (aR w₀ h₀) (StandardKernel.realMat gInf).det)
    (fun x => godementInner3 psiInf S (Matrix.of x) (StandardKernel.realMat gInf) *
      ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of x).det * (((|(Matrix.of x).det| ^ 2)⁻¹ : ℝ) : ℂ))
    D.W (fun x => (Matrix.of x)⁻¹) (fun b => rfl) s
    (integrable_jacquetIntegrand3_dilate_mul_quasiChar K hdeg μ hμ uR aR uC kC huR huC ω hω E hE a aInf haInf
      psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D S hS c₀ hc₀ t e gInf s hreg₁)
    ((P₂.twist t (e : ZMod 2)).archFactor s) (fun g => D.zetaEntire g t (e : ZMod 2) s)
    (fun g hg => D.zeta_eq g t (e : ZMod 2) s hg hreg₂) hdet

end S_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_jacquetVector3_eq_archFactor_mul (solution)
