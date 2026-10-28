-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_no_monotone_revolution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:15:40.529835+00:00
-- url     : https://prove2.me/submissions/0ec92eda-bc72-4750-8ddf-3ab5f775a95f

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_TrueRadialTube_exists_revolution_CMC
import Theorems.Thm_OAI_CubicTorus_TrueRadialTube_revolution_area_le_perimeter
import Theorems.Thm_OAI_CubicTorus_delaunay_chamber_monotone_mean
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma liftSet_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    (fundamentalCube ∩ quotientMap ⁻¹' E : Set Cover) =ᵐ[volume]
      (fundamentalCube ∩ quotientMap ⁻¹' F : Set Cover) := by
  have hh := ae_of_ae_map measurable_quotientMap.aemeasurable hEF
  have h := (ae_restrict_iff' measurableSet_fundamentalCube).1 hh
  filter_upwards [h] with x hx
  change (x ∈ fundamentalCube ∧ quotientMap x ∈ E) =
    (x ∈ fundamentalCube ∧ quotientMap x ∈ F)
  by_cases hc : x ∈ fundamentalCube
  · have hh : (quotientMap x ∈ E) = (quotientMap x ∈ F) := hx hc
    simpa only [hc, true_and] using hh
  · simp only [hc, false_and]

theorem perimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    perimeter E = perimeter F := by
  unfold perimeter
  apply iSup_congr
  intro X
  apply iSup_congr
  intro _
  rw [setIntegral_congr_set (liftSet_congr_ae hEF)]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

end CubicTorus

namespace CubicTorus

lemma circle_measurePreserving_mk_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico 0 1)) volume := by
  rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
  simpa using AddCircle.measurePreserving_mk (1 : ℝ) 0

lemma torusVolume_eq_product :
    torusVolume = Measure.map (WithLp.toLp 2 : ProductTorus → Torus) volume := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have he := (PiLp.volume_preserving_toLp (Fin 3)).restrict_preimage measurableSet_fundamentalCube
  rw [cube_preimage] at he
  have hp := measurePreserving_pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1))
    (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ => circle_measurePreserving_mk_Ico)
  have hs : (volume : Measure (Fin 3 → ℝ)).restrict
      (univ.pi (fun _ : Fin 3 => Ico 0 1)) =
      Measure.pi (fun _ : Fin 3 => volume.restrict (Ico (0 : ℝ) 1)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hto : Measurable (WithLp.toLp 2 : ProductTorus → Torus) :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable
  unfold torusVolume
  rw [← he.map_eq, hs, Measure.map_map measurable_quotientMap (PiLp.volume_preserving_toLp (Fin 3)).measurable]
  rw [volume_pi, ← hp.map_eq, Measure.map_map hto hp.measurable]
  rfl

end CubicTorus

namespace CubicTorus

instance torusVolume_haar : torusVolume.IsAddHaarMeasure := by
  rw [torusVolume_eq_product]
  exact AddEquiv.isAddHaarMeasure_map volume (WithLp.addEquiv 2 ProductTorus).symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.continuous
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).continuous

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

lemma admissible_translate {F : Cover → Cover} (hF : AdmissibleField F) (a : Cover) :
    AdmissibleField (fun x => F (x + a)) := by
  refine ⟨hF.1.comp (contDiff_id.add contDiff_const), ?_, fun x => hF.2.2 _⟩
  intro n x
  change F ((x + latticeVector n) + a) = F (x + a)
  rw [add_right_comm, hF.2.1]

lemma setIntegral_lift {f : Cover → ℝ} (hf : Continuous f)
    (hp : ∀ n x, f (x + latticeVector n) = f x) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ z in E, f (representative z) ∂torusVolume) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, f x := by
  calc
    _ = ∫ x in quotientMap ⁻¹' E, f (representative (quotientMap x))
        ∂volume.restrict fundamentalCube :=
      setIntegral_map hE (hf.measurable.comp measurable_representative).aestronglyMeasurable
        measurable_quotientMap.aemeasurable
    _ = _ := by
      simp_rw [periodic_representative hp]
      rw [Measure.restrict_restrict (measurable_quotientMap hE), inter_comm]

lemma flux_translation {F : Cover → Cover} (hF : AdmissibleField F)
    (a : Cover) {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' ((fun z => z + quotientMap a) ⁻¹' E),
      divergence F x) =
    ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence (fun y => F (y - a)) x := by
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap a) ⁻¹' E) := by
    exact (by fun_prop : Measurable (fun z : Torus => z + quotientMap a)) hE
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) hpre]
  have hG := admissible_translate hF (-a)
  have hG' : AdmissibleField (fun y => F (y - a)) := by simpa [sub_eq_add_neg] using hG
  rw [← setIntegral_lift (continuous_divergence hG'.1) (divergence_periodic hG'.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (fun y => F (y - a)) (representative (z + quotientMap a))) := by
    funext z
    simp only [sub_eq_add_neg, divergence_translate]
    have hq : quotientMap (representative (z + quotientMap a) + -a) =
        quotientMap (representative z) := by
      rw [quotientMap_add, quotientMap_representative, quotientMap_representative,
        quotientMap_neg]
      abel
    obtain ⟨n, hn⟩ := same_quotient_lattice hq
    rw [hn, divergence_periodic hF.2.1]
  rw [he]
  exact (measurePreserving_add_right torusVolume (quotientMap a)).setIntegral_preimage_emb
    (Homeomorph.addRight (quotientMap a)).measurableEmbedding
      (fun z => divergence (fun y => F (y - a)) (representative z)) E

end CubicTorus

namespace CubicTorus

lemma perimeter_translation_le {E : Set Torus} (hE : MeasurableSet E) (a : Cover) :
    perimeter ((fun z => z + quotientMap a) ⁻¹' E) ≤ perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_translation hF a hE]
  have hG : AdmissibleField (fun y => F (y - a)) := by
    simpa [sub_eq_add_neg] using admissible_translate hF (-a)
  exact le_iSup_of_le (fun y => F (y - a)) (le_iSup_of_le hG le_rfl)

lemma perimeter_translation_measurable {E : Set Torus} (hE : MeasurableSet E) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  obtain ⟨b, rfl⟩ := quotientMap_surjective a
  refine le_antisymm (perimeter_translation_le hE b) ?_
  have hpre : MeasurableSet ((fun z : Torus => z + quotientMap b) ⁻¹' E) :=
    (continuous_add_const _).measurable hE
  have hh := perimeter_translation_le hpre (-b)
  have he : (fun z : Torus => z + quotientMap (-b)) ⁻¹'
      ((fun z : Torus => z + quotientMap b) ⁻¹' E) = E := by
    ext z
    simp [quotientMap_neg]
  rwa [he] at hh

theorem perimeter_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    perimeter ((fun z => z + a) ⁻¹' E) = perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (measurePreserving_add_right torusVolume a).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp, ← perimeter_congr_ae he]
  exact perimeter_translation_measurable (measurableSet_toMeasurable _ _) a

lemma volume_translation {E : Set Torus} (hE : NullMeasurableSet E torusVolume) (a : Torus) :
    torusVolume ((fun z => z + a) ⁻¹' E) = torusVolume E :=
  (measurePreserving_add_right torusVolume a).measure_preimage hE

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace

namespace CubicTorus

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

namespace CubicTorus

lemma realVolume_lift {E : Set Torus} (hE : MeasurableSet E) :
    torusVolume.real E = volume.real (fundamentalCube ∩ quotientMap ⁻¹' E) := by
  simp only [Measure.real_def, torusVolume,
    Measure.map_apply measurable_quotientMap hE,
    Measure.restrict_apply (measurable_quotientMap hE), inter_comm]

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

instance torusVolume_negInvariant : torusVolume.IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular torusVolume

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_UnitAngle
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

lemma unitAngle_norm (t : ℝ) : ‖unitAngle t‖=1 := by simp [unitAngle,Complex.norm_exp]

end CubicTorus

end
end

section

noncomputable section
open Set Complex
open scoped Topology Real
namespace CubicTorus

lemma complexSquareGauge_pos {z : ℂ} (hz : z≠0) : 0 < complexSquareGauge z := by
  by_contra hh
  have hl : max |z.re| |z.im|≤0 := le_of_not_gt hh
  have h1 : z.re=0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hl) (abs_nonneg _))
  have h2 : z.im=0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hl) (abs_nonneg _))
  exact hz (Complex.ext h1 h2)

lemma unitAngle_ne_zero (t : ℝ) : unitAngle t≠0 := by
  intro hz
  have hh := unitAngle_norm t
  simp [hz] at hh

lemma complexSquareGauge_smul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    complexSquareGauge (r • z)=r*complexSquareGauge z := by
  simp only [complexSquareGauge,Complex.smul_re,Complex.smul_im,smul_eq_mul,abs_mul,abs_of_nonneg hr]
  exact (mul_max_of_nonneg _ _ hr).symm

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
attribute [-instance] _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeProductCoordinates_measurePreserving : MeasurePreserving planeProductCoordinates :=
  Complex.volume_preserving_equiv_real_prod.comp Complex.orthonormalBasisOneI.repr.symm.measurePreserving

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

lemma fieldMove_hasFDerivAt {F : Cover → Cover} {x : Cover}
    (hf : DifferentiableAt ℝ F x) (t : ℝ) :
    HasFDerivAt (fieldMove F t) (fieldMoveDeriv F t x) x :=
  (hasFDerivAt_id x).add (hf.hasFDerivAt.const_smul t)

lemma fieldMoveDeriv_det (F : Cover → Cover) (t : ℝ) (x : Cover) :
    (fieldMoveDeriv F t x).det =
      1 + t * divergence F x + t ^ 2 * secondJacobian F x + t ^ 3 * thirdJacobian F x := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (fieldMoveDeriv F t x).toLinearMap =
      Matrix.of (fun j k ↦ (if j = k then 1 else 0) + t * derivativeEntry F x j k) := by
    ext j k
    rw [LinearMap.toMatrix_apply]
    change (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.repr
      (fieldMoveDeriv F t x ((EuclideanSpace.basisFun (Fin 3) ℝ) k)) j = _
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply]
    simp [fieldMoveDeriv, derivativeEntry]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, he]
  simp [Matrix.det_fin_three, divergence, secondJacobian, thirdJacobian,
    derivativeEntry, Fin.sum_univ_succ]
  ring

lemma fieldMove_injective {F : Cover → Cover} (hf : Differentiable ℝ F)
    {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M) {t : ℝ}
    (ht : |t| * M < 1) : Function.Injective (fieldMove F t) := by
  have hLip := lipschitzWith_of_nnnorm_fderiv_le hf hM
  intro x y hxy
  have he : x - y = (-t) • (F x - F y) := by
    calc
      x - y = fieldMove F t x - fieldMove F t y - t • (F x - F y) := by
        unfold fieldMove
        module
      _ = _ := by rw [hxy, sub_self, zero_sub, neg_smul]
  have hn : ‖x - y‖ = |t| * ‖F x - F y‖ := by
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg]
  have hh : ‖x - y‖ ≤ |t| * M * ‖x - y‖ := by
    calc
      ‖x - y‖ = |t| * ‖F x - F y‖ := hn
      _ ≤ |t| * ((M : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

lemma continuous_derivativeEntry {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (i j : Fin 3) : Continuous (fun x ↦ derivativeEntry F x i j) := by
  exact (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)

lemma continuous_secondJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (secondJacobian F) := by
  unfold secondJacobian
  exact (((((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 1 1)).add
    ((continuous_derivativeEntry hf 0 0).mul (continuous_derivativeEntry hf 2 2))).add
    ((continuous_derivativeEntry hf 1 1).mul (continuous_derivativeEntry hf 2 2))).sub
    ((continuous_derivativeEntry hf 0 1).mul (continuous_derivativeEntry hf 1 0))).sub
    ((continuous_derivativeEntry hf 0 2).mul (continuous_derivativeEntry hf 2 0)) |>.sub
    ((continuous_derivativeEntry hf 1 2).mul (continuous_derivativeEntry hf 2 1))

lemma continuous_thirdJacobian {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F) :
    Continuous (thirdJacobian F) := by
  exact (continuous_pi fun i ↦ continuous_pi fun j ↦
    continuous_derivativeEntry hf i j).matrix_det

lemma integral_det_fieldMove {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    {A : Set Cover} (hAc : IsCompact (closure A)) (t : ℝ) :
    (∫ x in A, (fieldMoveDeriv F t x).det) = volume.real A +
      t * (∫ x in A, divergence F x) + t ^ 2 * (∫ x in A, secondJacobian F x) +
      t ^ 3 * (∫ x in A, thirdJacobian F x) := by
  have h1 : IntegrableOn (divergence F) (closure A) volume :=
    (continuous_divergence hf).continuousOn.integrableOn_compact hAc
  have h2 : IntegrableOn (secondJacobian F) (closure A) volume :=
    (continuous_secondJacobian hf).continuousOn.integrableOn_compact hAc
  have h3 : IntegrableOn (thirdJacobian F) (closure A) volume :=
    (continuous_thirdJacobian hf).continuousOn.integrableOn_compact hAc
  have hμ : volume A < ⊤ := (measure_mono subset_closure).trans_lt hAc.measure_lt_top
  have hc : IntegrableOn (fun _ : Cover ↦ (1 : ℝ)) A :=
    integrableOn_const hμ.ne
  simp_rw [fieldMoveDeriv_det]
  rw [integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x + t^2 * secondJacobian F x)
      (g := fun x ↦ t^3 * thirdJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        ((hc.add ((h1.mono_set subset_closure).const_mul t)).add
          ((h2.mono_set subset_closure).const_mul (t^2))))
      ((h3.mono_set subset_closure).const_mul (t^3)),
    integral_add (μ := volume.restrict A) (f := fun x ↦ 1 + t * divergence F x)
      (g := fun x ↦ t^2 * secondJacobian F x)
      (by simpa only [IntegrableOn, Pi.add_def] using
        (hc.add ((h1.mono_set subset_closure).const_mul t)))
      ((h2.mono_set subset_closure).const_mul (t^2)),
    integral_add (μ := volume.restrict A) (f := fun _ : Cover ↦ (1 : ℝ)) (g := fun x ↦ t * divergence F x)
      hc ((h1.mono_set subset_closure).const_mul t)]
  simp only [integral_const_mul, setIntegral_const, smul_eq_mul, mul_one]

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma integral_det_fieldMove_le_volume {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) {M : NNReal} (hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ M)
    {t : ℝ} (ht : |t| * M < 1) {A : Set Cover} (hA : MeasurableSet A)
    (hAc : IsCompact (closure A)) :
    (∫ x in A, (fieldMoveDeriv F t x).det) ≤ volume.real (fieldMove F t '' A) := by
  have hdet : Continuous (fun x ↦ (fieldMoveDeriv F t x).det) :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add ((hf.continuous_fderiv (by simp)).const_smul t))
  have hi : IntegrableOn (fun x ↦ (fieldMoveDeriv F t x).det) A volume :=
    (hdet.continuousOn.integrableOn_compact hAc).mono_set subset_closure
  have hj := integral_image_eq_integral_abs_det_fderiv_smul volume hA
    (fun x (_ : x ∈ A) ↦
      (fieldMove_hasFDerivAt (hf.differentiable (by simp) x) t).hasFDerivWithinAt)
    (fieldMove_injective (hf.differentiable (by simp)) hM ht).injOn (fun _ ↦ (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hj
  rw [hj]
  exact integral_mono hi hi.abs (fun x ↦ le_abs_self _)

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma discProjection_norm_le (x : Cover) : ‖discProjection x‖ ≤ ‖x‖ := by
  have hh : ‖discProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [discProjection_apply, Fin.sum_univ_succ]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (discProjection x), norm_nonneg x]

lemma continuous_tubeSplit_symm : Continuous tubeSplit.symm := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).continuous_symm.comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × Plane ↦ tubeSplit.symm p i)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [tubeSplit_symm_zero] using (continuous_fst : Continuous (fun p : ℝ × Plane ↦ p.1))
  · simp_rw [tubeSplit_symm_succ]
    fun_prop

lemma tubeSplit_measurePreserving : MeasurePreserving tubeSplit := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin 3)))

lemma measurableSet_coverTube (r : ℝ) : MeasurableSet (coverTube r) :=
  (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).preimage tubeSplit.measurable

lemma isCompact_closure_coverTube (r : ℝ) : IsCompact (closure (coverTube r)) := by
  have hc : IsCompact (tubeSplit.symm '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall discCenter r)) :=
    (isCompact_Icc.prod (isCompact_closedBall discCenter r)).image continuous_tubeSplit_symm
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  refine ⟨tubeSplit x, ⟨⟨hx.1.1, hx.1.2.le⟩, Metric.ball_subset_closedBall hx.2⟩, ?_⟩
  exact tubeSplit.symm_apply_apply x

lemma volume_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume (coverTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [coverTube, tubeSplit_measurePreserving.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
      EuclideanSpace.volume_ball_fin_two]
    simp only [sub_zero, ENNReal.ofReal_one, one_mul]
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr]
    ring
  · exact (measurableSet_Ico.prod Metric.isOpen_ball.measurableSet).nullMeasurableSet

lemma volumeReal_coverTube {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coverTube r) = Real.pi * r^2 := by
  rw [Measure.real_def, volume_coverTube hr, ENNReal.toReal_ofReal (by positivity)]

lemma axialProjection_norm_le (x : Cover) : ‖axialProjection x‖ ≤ ‖x‖ := by
  have hh : ‖axialProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_succ, axialProjection_zero, axialProjection_succ, norm_zero,
      zero_pow (by omega : 2 ≠ 0), zero_add]
    nlinarith [sq_nonneg ‖x 0‖]
  nlinarith [norm_nonneg (axialProjection x), norm_nonneg x]

lemma fieldMove_coverTube_subset {F : Cover → Cover} (hF : ∀ x, ‖F x‖ ≤ 1)
    (hF0 : ∀ x, F x 0 = 0) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    fieldMove F t '' coverTube r ⊆ coverTube (r+t) := by
  rintro _ ⟨x, hx, rfl⟩
  change (fieldMove F t x) 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (fieldMove F t x) ∈ Metric.ball discCenter (r+t)
  constructor
  · simpa [fieldMove, hF0 x] using hx.1
  · have hb : ‖discProjection (F x)‖ ≤ 1 := (discProjection_norm_le _).trans (hF x)
    have hh : ‖t • discProjection (F x)‖ ≤ t := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, mul_one] using
        mul_le_mul_of_nonneg_left hb ht
    have hd : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      _ = ‖(discProjection x - discCenter) + t • discProjection (F x)‖ := by
        congr 1
        simp only [fieldMove, map_add, map_smul]
        abel
      _ ≤ ‖discProjection x - discCenter‖ + ‖t • discProjection (F x)‖ := norm_add_le _ _
      _ < r+t := add_lt_add_of_lt_of_le hd hh

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma tubeSplit_symm_line (u : ℝ) (y : Plane) :
    tubeSplit.symm (u,y) = tubeSplit.symm (0,y) + u • EuclideanSpace.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

lemma hasDerivAt_tubeLine (u : ℝ) (y : Plane) :
    HasDerivAt (fun t : ℝ ↦ tubeSplit.symm (t,y)) (EuclideanSpace.single 0 1) u := by
  have he : (fun t : ℝ ↦ tubeSplit.symm (t,y)) =
      (fun t : ℝ ↦ tubeSplit.symm (0,y) + t • EuclideanSpace.single 0 1) :=
    funext (fun t ↦ tubeSplit_symm_line t y)
  rw [he]
  simpa! only [Pi.add_def, zero_add, one_smul, id_eq] using
    (hasDerivAt_const u (tubeSplit.symm (0,y))).add
      ((hasDerivAt_id u).smul_const (EuclideanSpace.single 0 1))

lemma axial_integral_eq_zero {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (y : Plane) :
    (∫ u in Ico (0 : ℝ) 1, derivativeEntry F (tubeSplit.symm (u,y)) 0 0) = 0 := by
  have hd (u : ℝ) : HasDerivAt (fun u ↦ F (tubeSplit.symm (u,y)) 0)
      (derivativeEntry F (tubeSplit.symm (u,y)) 0 0) u := by
    exact (EuclideanSpace.proj 0).hasFDerivAt.comp_hasDerivAt u
      (((hf.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt u
        (hasDerivAt_tubeLine u y))
  have hc : Continuous (fun u ↦ derivativeEntry F (tubeSplit.symm (u,y)) 0 0) :=
    (continuous_derivativeEntry hf 0 0).comp (continuous_tubeSplit_symm.comp (by fun_prop))
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u) (hc.intervalIntegrable 0 1)]
  have he : tubeSplit.symm (1,y) = tubeSplit.symm (0,y) + latticeVector (Pi.single 0 1) := by
    rw [tubeSplit_symm_line 1 y]
    congr 1
    ext i
    simp [latticeVector, Pi.single_apply]
  rw [he, hp]
  simp

lemma integral_axial_coverTube {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, derivativeEntry F x 0 0) = 0 := by
  let g : ℝ × Plane → ℝ := fun p ↦ derivativeEntry F (tubeSplit.symm p) 0 0
  have hint : IntegrableOn (fun x ↦ derivativeEntry F x 0 0) (coverTube r) :=
    ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  have hi : IntegrableOn g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r) volume := by
    rw [← tubeSplit_measurePreserving.integrableOn_comp_preimage tubeSplit.measurableEmbedding]
    simpa only [g, Function.comp_def, tubeSplit.symm_apply_apply, coverTube] using hint
  have he := tubeSplit_measurePreserving.setIntegral_preimage_emb tubeSplit.measurableEmbedding
    g (Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r)
  simp only [g, tubeSplit.symm_apply_apply] at he
  change (∫ x in coverTube r, derivativeEntry F x 0 0) = _ at he
  rw [he]
  change (∫ p in Ico (0 : ℝ) 1 ×ˢ Metric.ball discCenter r, g p) = 0
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [integral_prod_symm g hi]
  simp only [g, axial_integral_eq_zero hf hp, integral_zero]

lemma divergence_axialProjection {x : Cover} {F : Cover → Cover} (hf : DifferentiableAt ℝ F x) :
    divergence (fun y ↦ axialProjection (F y)) x = divergence F x - derivativeEntry F x 0 0 := by
  have hc : HasFDerivAt (fun y ↦ axialProjection (F y))
      (axialProjection.comp (fderiv ℝ F x)) x :=
    axialProjection.hasFDerivAt.comp x hf.hasFDerivAt
  simp only [divergence, hc.fderiv, ContinuousLinearMap.comp_apply, Fin.sum_univ_succ,
    axialProjection_zero, axialProjection_succ, derivativeEntry]
  ring

lemma flux_axialProjection {F : Cover → Cover} (hf : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ n x, F (x + latticeVector n) = F x) (r : ℝ) :
    (∫ x in coverTube r, divergence (fun y ↦ axialProjection (F y)) x) =
      ∫ x in coverTube r, divergence F x := by
  simp_rw [divergence_axialProjection ((hf.differentiable (by simp)).differentiableAt)]
  rw [integral_sub]
  · rw [integral_axial_coverTube hf hp, sub_zero]
  · exact ((continuous_divergence hf).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure
  · exact ((continuous_derivativeEntry hf 0 0).continuousOn.integrableOn_compact
      (isCompact_closure_coverTube r)).mono_set subset_closure

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison
open Filter
open scoped Topology

lemma flux_coverTube_axial_le {F : Cover → Cover}
    (hf : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : ∀ x, F x 0 = 0) {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  obtain ⟨M, hM0, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  let MN : NNReal := ⟨M, hM0⟩
  have hM : ∀ x, ‖fderiv ℝ F x‖₊ ≤ MN := fun x ↦ by exact_mod_cast hbound x
  let P := ∫ x in coverTube r, divergence F x
  let Q := ∫ x in coverTube r, secondJacobian F x
  let R := ∫ x in coverTube r, thirdJacobian F x
  have hind : ∀ t : ℝ, 0 < t → t < 1 / (M+1) →
      P + t*Q + t^2*R ≤ 2 * Real.pi * r + Real.pi*t := by
    intro t ht0 ht1
    have htM : |t| * MN < 1 := by
      rw [abs_of_pos ht0]
      change t*M < 1
      have hh := (lt_div_iff₀ (by positivity : 0 < M+1)).1 ht1
      nlinarith
    have hv := integral_det_fieldMove_le_volume hf hM htM
      (measurableSet_coverTube r) (isCompact_closure_coverTube r)
    have hfin : volume (coverTube (r+t)) ≠ ⊤ := by
      rw [volume_coverTube (by linarith)]
      exact ENNReal.ofReal_ne_top
    have hv' : volume.real (fieldMove F t '' coverTube r) ≤ volume.real (coverTube (r+t)) :=
      ENNReal.toReal_mono hfin (measure_mono (fieldMove_coverTube_subset hF hF0 ht0.le r))
    rw [integral_det_fieldMove hf (isCompact_closure_coverTube r)] at hv
    rw [volumeReal_coverTube (by linarith : 0 ≤ r+t)] at hv'
    rw [volumeReal_coverTube hr.le] at hv
    change Real.pi*r^2 + t*P + t^2*Q + t^3*R ≤ _ at hv
    apply (mul_le_mul_iff_right₀ ht0).mp
    nlinarith [hv.trans hv']
  have htend₁ : Tendsto (fun t : ℝ ↦ P + t*Q + t^2*R) (𝓝[>] (0 : ℝ)) (𝓝 P) := by
    have hh : Continuous (fun t : ℝ ↦ P + t*Q + t^2*R) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have htend₂ : Tendsto (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t)
      (𝓝[>] (0 : ℝ)) (𝓝 (2*Real.pi*r)) := by
    have hh : Continuous (fun t : ℝ ↦ 2*Real.pi*r + Real.pi*t) := by fun_prop
    simpa using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto htend₁ htend₂
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1/(M+1))).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  exact hind t ht0 ht1

lemma flux_coverTube_le {F : Cover → Cover} (hF : AdmissibleField F)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in coverTube r, divergence F x) ≤ 2 * Real.pi * r := by
  rw [← flux_axialProjection hF.1 hF.2.1 r]
  apply flux_coverTube_axial_le (axialProjection.contDiff.comp hF.1)
  · intro n x
    change axialProjection (F (x + latticeVector n)) = axialProjection (F x)
    rw [hF.2.1]
  · intro x
    exact (axialProjection_norm_le _).trans (hF.2.2 x)
  · intro x
    exact axialProjection_zero (F x)
  · exact hr

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma representative_mem_cube (x : Torus) : representative x ∈ fundamentalCube := by
  intro i
  exact ⟨((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.1,
    by simpa! only [representative, PiLp.toLp_apply, zero_add] using
      ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property.2⟩

lemma coverTube_subset_cube {r : ℝ} (hr : r ≤ 1/2) : coverTube r ⊆ fundamentalCube := by
  intro x hx i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hx.1
  · have hnorm : ‖discProjection x - discCenter‖ < r := by
      simpa only [tubeSplit_apply, Metric.mem_ball, dist_eq_norm] using hx.2
    have hi := (PiLp.norm_apply_le (discProjection x - discCenter) j).trans_lt hnorm
    change |x j.succ - (1/2 : ℝ)| < r at hi
    rw [abs_lt] at hi
    constructor <;> linarith

lemma measurableSet_cubeTube (r : ℝ) : MeasurableSet (cubeTube r) :=
  (measurableSet_coverTube r).preimage measurable_representative

lemma cubeTube_lift {r : ℝ} (hr : r ≤ 1/2) :
    fundamentalCube ∩ quotientMap ⁻¹' cubeTube r = coverTube r := by
  ext x
  constructor
  · rintro ⟨hx, ht⟩
    change representative (quotientMap x) ∈ coverTube r at ht
    rwa [representative_quotientMap_of_mem hx] at ht
  · intro ht
    have hx := coverTube_subset_cube hr ht
    refine ⟨hx, ?_⟩
    change representative (quotientMap x) ∈ coverTube r
    rwa [representative_quotientMap_of_mem hx]

lemma volume_cubeTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (cubeTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_cubeTube r),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_cubeTube r)), inter_comm,
    cubeTube_lift hr1, volume_coverTube hr0]

lemma perimeter_cubeTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (cubeTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  unfold perimeter
  refine iSup_le fun F ↦ iSup_le fun hF ↦ ?_
  rw [cubeTube_lift hr1]
  exact ENNReal.ofReal_le_ofReal (flux_coverTube_le hF hr0)

lemma norm_representative_sub_half (x : Torus) (i : Fin 3) :
    ‖representative x i - (1/2 : ℝ)‖ = ‖x i - ((1/2 : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hi := representative_mem_cube x i
  have hb : |representative x i - (1/2 : ℝ)| ≤ |(1 : ℝ)|/2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hn : ‖((representative x i - (1/2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1/2 : ℝ)| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 hb
  have hxi : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i :=
    congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [map_sub, hxi, Real.norm_eq_abs] using hn.symm

lemma mem_cubeTube_iff {r : ℝ} (hr : 0 ≤ r) (x : Torus) :
    x ∈ cubeTube r ↔ x - quotientMap cubeCenter ∈ centeredTube r := by
  change (representative x 0 ∈ Ico (0 : ℝ) 1 ∧
    discProjection (representative x) ∈ Metric.ball discCenter r) ↔ _
  simp only [mem_Ico]
  rw [and_iff_right (representative_mem_cube x 0), Metric.mem_ball, dist_eq_norm,
    ← sq_lt_sq₀ (norm_nonneg _) hr, PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, discProjection_apply, discCenter,
    norm_representative_sub_half]
  rfl

lemma centeredTube_eq_cubeTube_preimage {r : ℝ} (hr : 0 ≤ r) :
    centeredTube r = (fun x ↦ x + quotientMap cubeCenter) ⁻¹' cubeTube r := by
  ext x
  simp only [mem_preimage, mem_cubeTube_iff hr, add_sub_cancel_right]

lemma measurableSet_centeredTube (r : ℝ) : MeasurableSet (centeredTube r) := by
  apply measurableSet_lt
  · fun_prop
  · fun_prop

lemma volume_centeredTube {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2) :
    torusVolume (centeredTube r) = ENNReal.ofReal (Real.pi * r^2) := by
  rw [centeredTube_eq_cubeTube_preimage hr0,
    volume_translation (measurableSet_cubeTube r).nullMeasurableSet,
    volume_cubeTube hr0 hr1]

lemma perimeter_centeredTube_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2) :
    perimeter (centeredTube r) ≤ ENNReal.ofReal (2 * Real.pi * r) := by
  rw [centeredTube_eq_cubeTube_preimage hr0.le,
    perimeter_translation (measurableSet_cubeTube r).nullMeasurableSet]
  exact perimeter_cubeTube_le hr0 hr1

end CubicTorus.UpperComparison

namespace CubicTorus.UpperComparison

lemma canonicalTube_radius_properties {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    0 < Real.sqrt (V/Real.pi) ∧ Real.sqrt (V/Real.pi) ≤ 1/2 ∧
    Real.pi * (Real.sqrt (V/Real.pi))^2 = V := by
  have hp := Real.pi_pos
  have hVpos := hV.1
  refine ⟨Real.sqrt_pos.2 (div_pos hV.1 hp), ?_, ?_⟩
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hp).2
    nlinarith [Real.pi_gt_three, hV.2]
  · rw [Real.sq_sqrt (by positivity)]
    field_simp

lemma tubeArea_formula {V : ℝ} (hV : 0 ≤ V) :
    2*Real.pi*Real.sqrt (V/Real.pi) = 2*Real.sqrt (Real.pi*V) := by
  have hp := Real.pi_pos
  have heq : Real.pi*Real.sqrt (V/Real.pi) = Real.sqrt (Real.pi*V) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
  calc
    _ = 2*(Real.pi*Real.sqrt (V/Real.pi)) := by ring
    _ = _ := by rw [heq]

lemma volume_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    torusVolume (canonicalTube V) = ENNReal.ofReal V := by
  obtain ⟨hr0, hr1, heq⟩ := canonicalTube_radius_properties hV
  change torusVolume (centeredTube _) = _
  rw [volume_centeredTube hr0.le hr1, heq]

lemma perimeter_canonicalTube_le {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    perimeter (canonicalTube V) ≤ ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) := by
  obtain ⟨hr0, hr1, _⟩ := canonicalTube_radius_properties hV
  exact (perimeter_centeredTube_le hr0 hr1).trans_eq
    (congrArg ENNReal.ofReal (tubeArea_formula hV.1.le))

lemma finitePerimeter_canonicalTube {V : ℝ} (hV : V ∈ Ioc 0 (1/2 : ℝ)) :
    FinitePerimeter (canonicalTube V) :=
  ⟨(measurableSet_centeredTube _).nullMeasurableSet,
    (perimeter_canonicalTube_le hV).trans_lt ENNReal.ofReal_lt_top⟩

end CubicTorus.UpperComparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainMass
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

@[simp] lemma simultaneousMass_zero (l : List Variation) {E : Set Torus} (hE : MeasurableSet E) :
    chainMass (simultaneousChain l 0) E=torusVolume.real E := by
  simp only [chainMass,simultaneousJacobian_zero,setIntegral_one_eq_measureReal]
  exact (realVolume_lift hE).symm

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSectionPoint_contDiff (c : Cover) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateSectionPoint c t) :=
  contDiff_const.add coordinatePlaneLift.contDiff

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_function_periodic (i : Fin 3) {f : ℝ → ℝ} (hp : Function.Periodic f 1) :
    ∀ (m : Fin 3 → ℤ) (x : Cover),f ((x+latticeVector m) i)=f (x i) := by
  intro m x
  simpa [latticeVector] using hp.int_mul (m i) (x i)

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSplit_measurePreserving (i : Fin 3) : MeasurePreserving (axialSplit i) :=
  UpperComparison.tubeSplit_measurePreserving.comp (coverCoordinatePermute (Equiv.swap 0 i)).measurePreserving

lemma measurableSet_transverseSquare : MeasurableSet transverseSquare := by
  change MeasurableSet {y : Plane | ∀ j,y j∈Ico (0 : ℝ) 1}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j =>
    measurableSet_Ico.preimage (EuclideanSpace.proj j : Plane →L[ℝ] ℝ).measurable)

lemma mem_axialSplit_cube (i : Fin 3) (x : Cover) :
    x∈fundamentalCube ↔ axialSplit i x∈Ico (0 : ℝ) 1 ×ˢ transverseSquare := by
  let y := coverCoordinatePermute (Equiv.swap 0 i) x
  have he : x∈fundamentalCube ↔ y∈fundamentalCube := by
    constructor
    · intro hx j
      exact hx ((Equiv.swap 0 i) j)
    · intro hy j
      have hh := hy ((Equiv.swap 0 i) j)
      simpa [y] using hh
  rw [he]
  change (∀ j,0≤y j ∧ y j<1) ↔ (0≤y 0 ∧ y 0<1) ∧ ∀ j : Fin 2,0≤y j.succ ∧ y j.succ<1
  constructor
  · intro hy
    exact ⟨hy 0,fun j => hy j.succ⟩
  · rintro ⟨h0,hs⟩ j
    exact Fin.cases h0 hs j

lemma axialSplit_preimage_cube (i : Fin 3) :
    axialSplit i ⁻¹' (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=fundamentalCube := by
  ext x
  exact (mem_axialSplit_cube i x).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma volume_axialSquare : volume transverseSquare=1 := by
  have he := (axialSplit_measurePreserving 0).measure_preimage
    ((measurableSet_Ico (a := (0 : ℝ)) (b := 1)).prod measurableSet_transverseSquare).nullMeasurableSet
  rw [axialSplit_preimage_cube,volume_fundamentalCube,Measure.volume_eq_prod,
    Measure.prod_prod,Real.volume_Ico] at he
  simpa using he.symm

lemma volume_axialRectangle : volume (Ico (0 : ℝ) 1 ×ˢ transverseSquare)=1 := by
  rw [Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ico,volume_axialSquare]
  norm_num

lemma axial_section_inner {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) (t c : ℝ) :
    (∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      axialSectionArea E i t*c := by
  let B : Set Plane := (fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E
  have hB : MeasurableSet B := hE.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he : (fun y => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      B.indicator (fun _ => c) := by
    funext y
    by_cases hy : y∈B
    · simp only [indicator_of_mem hy]
      change quotientMap ((axialSplit i).symm (t,y))∈E at hy
      simp only [characteristic,indicator_of_mem hy,one_mul]
    · simp only [indicator_of_notMem hy]
      change quotientMap ((axialSplit i).symm (t,y))∉E at hy
      simp only [characteristic,indicator_of_notMem hy,zero_mul]
  rw [he,setIntegral_indicator hB,integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  rfl

lemma integrable_axialIndicator {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    IntegrableOn (fun z : ℝ × Plane => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1)
      (Ico (0 : ℝ) 1 ×ˢ transverseSquare) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded
    (hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous) (axial_function_periodic i hp)
  apply IntegrableOn.of_bound (by rw [volume_axialRectangle]; simp)
    (((measurable_characteristic hE).comp (measurable_quotientMap.comp (axialSplit i).symm.measurable)).mul
      (hf.measurable.comp measurable_fst)).aestronglyMeasurable M
  apply Eventually.of_forall
  intro z
  have hb : ‖f z.1‖≤M := by
    have hh := hM ((axialSplit i).symm z)
    change ‖f ((axialSplit i).symm z i)‖≤M at hh
    simpa only [axialSplit_symm_axis] using hh
  change ‖characteristic E (quotientMap ((axialSplit i).symm z))*f z.1‖≤M
  by_cases hz : quotientMap ((axialSplit i).symm z)∈E
  · simpa only [characteristic,indicator_of_mem hz,one_mul] using hb
  · simp only [characteristic,indicator_of_notMem hz,zero_mul,norm_zero]
    exact hM0

theorem axial_section_fubini {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i))=
      ∫ t in Ico (0 : ℝ) 1,axialSectionArea E i t*f t := by
  let g : ℝ × Plane → ℝ := fun z => characteristic E (quotientMap ((axialSplit i).symm z))*f z.1
  have he := (axialSplit_measurePreserving i).setIntegral_preimage_emb
    (axialSplit i).measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ transverseSquare)
  rw [axialSplit_preimage_cube] at he
  have hleft : (fun x : Cover => g (axialSplit i x))=
      (quotientMap ⁻¹' E).indicator (fun x => f (x i)) := by
    funext x
    dsimp [g]
    rw [(axialSplit i).symm_apply_apply,axialSplit_fst]
    by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]
  rw [hleft,setIntegral_indicator (hE.preimage measurable_quotientMap)] at he
  rw [he]
  have hi := integrable_axialIndicator hE i hf hp
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact axial_section_inner hE i t (f t)

lemma integral_axialSectionArea {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionArea E i t)=torusVolume.real E := by
  have he := axial_section_fubini hE i (f := fun _ => 1) continuous_const (fun _ => rfl)
  rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one,← realVolume_lift hE] at he
  simpa only [mul_one] using he.symm

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlanarRadialArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

lemma measurableSet_planarRadialRegion {r : ℝ → ℝ} (hr : Measurable r) :
    MeasurableSet (planarRadialRegion r) :=
  measurableSet_lt measurable_norm (hr.comp (Complex.measurable_arg.div_const _))

lemma mem_planarRadialRegion_polar {r : ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p∈Complex.polarCoord.target) :
    Complex.polarCoord.symm p∈planarRadialRegion r ↔ p.1 < r (p.2/(2*Real.pi)) := by
  have he := congrArg Prod.snd (Complex.polarCoord.right_inv hp)
  rw [Complex.polarCoord_apply] at he
  change (Complex.polarCoord.symm p).arg=p.2 at he
  change ‖Complex.polarCoord.symm p‖ < r _ ↔ _
  rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1,he]

lemma lintegral_radial_coordinate {R : ℝ} (hR : 0≤R) :
    (∫⁻ x in Ioi (0 : ℝ),if x<R then ENNReal.ofReal x else 0)=ENNReal.ofReal (R^2/2) := by
  have he : (fun x : ℝ => if x<R then ENNReal.ofReal x else 0)=
      (Iio R).indicator ENNReal.ofReal := by rfl
  rw [he,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  rw [inter_comm,Ioi_inter_Iio,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hi : IntegrableOn (fun x : ℝ => x) (Ioc 0 R) :=
    (continuous_id.intervalIntegrable 0 R).1.mono_set (by rfl)
  have hn : 0≤ᵐ[volume.restrict (Ioc 0 R)] (fun x : ℝ => x) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← intervalIntegral.integral_of_le hR,integral_id]
  simp

theorem volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0 < r t) :
    volume (planarRadialRegion r)=
      ENNReal.ofReal (Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2)) := by
  let f : ℂ → ℝ≥0∞ := (planarRadialRegion r).indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator (measurableSet_planarRadialRegion hr.measurable)
  have hvol : (∫⁻ z,f z)=volume (planarRadialRegion r) := by
    simp [f,lintegral_indicator,measurableSet_planarRadialRegion hr.measurable]
  rw [← hvol,← Complex.lintegral_comp_polarCoord_symm]
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 < r (p.2/(2*Real.pi)) then ENNReal.ofReal p.1 else 0
  have hgm : Measurable g := by
    exact Measurable.ite (measurableSet_lt measurable_fst
      (hr.measurable.comp (measurable_snd.div_const _)))
      measurable_fst.ennreal_ofReal measurable_const
  have hg : (∫⁻ p in polarCoord.target,ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p))=
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,g p := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp'
    have hmem := mem_planarRadialRegion_polar (r := r) hp'
    by_cases hh : p.1 < r (p.2/(2*Real.pi))
    · simp only [f,g,indicator_of_mem (hmem.mpr hh),ite_eq_left hh,smul_eq_mul,mul_one]
    · simp only [f,g,indicator_of_notMem (not_imp_not.mpr hmem.mp hh),ite_eq_right hh,smul_eq_mul,mul_zero]
  rw [hg,Measure.volume_eq_prod,setLIntegral_prod _ hgm.aemeasurable]
  rw [lintegral_lintegral_swap hgm.aemeasurable]
  have hb : (∫⁻ t in Ioo (-Real.pi) Real.pi,∫⁻ x in Ioi (0 : ℝ),g (x,t))=
      ∫⁻ t in Ioo (-Real.pi) Real.pi,ENNReal.ofReal ((r (t/(2*Real.pi)))^2/2) := by
    apply lintegral_congr
    intro t
    exact lintegral_radial_coordinate (R := r (t/(2*Real.pi))) (hpos _).le
  rw [hb,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hrc : Continuous (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) :=
    ((hr.comp (continuous_id.div_const _)).pow 2).div_const _
  have hpi : -Real.pi≤Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) (Ioc (-Real.pi) Real.pi) := by
    exact (hrc.intervalIntegrable (-Real.pi) Real.pi).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity)),
    ← intervalIntegral.integral_of_le hpi]
  congr 1
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div (fun t => (r t)^2) (by positivity : 2*Real.pi≠0)]
  have hlo : -Real.pi/(2*Real.pi)= -(1/2 : ℝ) := by field_simp
  have hhi : Real.pi/(2*Real.pi)=(1/2 : ℝ) := by field_simp
  rw [hlo,hhi]
  have hper : Function.Periodic (fun t => (r t)^2) 1 := fun t => congrArg (fun a : ℝ => a^2) (hp t)
  have hs := hper.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  norm_num only [neg_add_cancel_left,zero_add] at hs
  have hs' : (∫ t in (-(1/2) : ℝ)..(1/2),(r t)^2)=∫ t in (0 : ℝ)..1,(r t)^2 := by
    exact hs
  rw [hs']
  simp only [smul_eq_mul]
  ring

lemma real_volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0 < r t) :
    volume.real (planarRadialRegion r)=Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2) := by
  rw [Measure.real,volume_planarRadialRegion hr hp hpos,ENNReal.toReal_ofReal]
  exact mul_nonneg Real.pi_pos.le
    (intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg (r t)))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_RadialSectionArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma norm_smul_unitAngle_arg (z : ℂ) : ‖z‖ • unitAngle (z.arg/(2*Real.pi))=z := by
  rw [unitAngle]
  have he : 2*Real.pi*(z.arg/(2*Real.pi))=z.arg := by field_simp
  rw [he,Complex.real_smul]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma radius_le_squareScale_of_gauge {z : ℂ} (hz : complexSquareGauge z≤1/2) :
    ‖z‖≤unitSquareScale (z.arg/(2*Real.pi)) := by
  let a := z.arg/(2*Real.pi)
  have hh : ‖z‖*complexSquareGauge (unitAngle a)≤1/2 := by
    rw [← complexSquareGauge_smul (norm_nonneg z),norm_smul_unitAngle_arg]
    exact hz
  rw [unitSquareScale,le_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))]
  nlinarith

lemma planarRadialRegion_eq_actual_section {E : Set Torus} {c : Cover} {t : ℝ} {r : ℝ → ℝ}
    (hr0 : ∀ a,0 < r a) (hrb : ∀ a,r a<unitSquareScale a)
    (hphase : ∀ a u,0≤u → u≤unitSquareScale a →
      (quotientMap (coordinateSectionPoint c t (u • unitAngle a))∈E ↔ u < r a)) :
    planarRadialRegion r=centeredPlaneSection E c t := by
  ext z
  let a := z.arg/(2*Real.pi)
  have hg : 0 < complexSquareGauge (unitAngle a) := complexSquareGauge_pos (unitAngle_ne_zero a)
  have hgs : unitSquareScale a*complexSquareGauge (unitAngle a)=1/2 := by
    dsimp [unitSquareScale]
    field_simp [hg.ne']
  change ‖z‖ < r a ↔ complexSquareGauge z<1/2 ∧ quotientMap (coordinateSectionPoint c t z)∈E
  constructor
  · intro hz
    have hb : ‖z‖≤unitSquareScale a := (hz.trans (hrb a)).le
    refine ⟨?_,?_⟩
    · rw [← norm_smul_unitAngle_arg z,complexSquareGauge_smul (norm_nonneg z)]
      exact (mul_lt_mul_of_pos_right (hz.trans (hrb a)) hg).trans_eq hgs
    · have he := (hphase a ‖z‖ (norm_nonneg z) hb).mpr hz
      rwa [norm_smul_unitAngle_arg] at he
  · rintro ⟨hz,hE⟩
    rcases (norm_nonneg z).eq_or_lt with hzero | hpos
    · rw [← hzero]
      exact hr0 a
    · apply (hphase a ‖z‖ hpos.le (radius_le_squareScale_of_gauge hz.le)).mp
      rwa [norm_smul_unitAngle_arg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_integral_unit_translate {f : ℝ → ℝ} (hp : Function.Periodic f 1) (a c : ℝ) :
    (∫ x in Ioo a (a+1),f (x+c))=∫ x in Ico (0 : ℝ) 1,f x := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : a≤a+1),
    intervalIntegral.integral_comp_add_right,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  convert hp.intervalIntegral_add_eq (a+c) 0 using 1 <;> congr 1 <;> ring

lemma bounded_integrable_rectangle {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) (a b c d : ℝ) :
    IntegrableOn f (Ioo a b ×ˢ Ioo c d) := by
  apply IntegrableOn.of_bound (by
    rw [Measure.volume_eq_prod]
    simp only [Measure.prod_prod,Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma bounded_integrable_unit_square {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) : IntegrableOn f (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (by rw [Measure.volume_eq_prod]; simp) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma periodic_plane_integral_translate {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M)
    (hx : ∀ y,Function.Periodic (fun x => f (x,y)) 1)
    (hy : ∀ x,Function.Periodic (fun y => f (x,y)) 1) (a b c d : ℝ) :
    (∫ z in Ioo a (a+1) ×ˢ Ioo b (b+1),f (z.1+c,z.2+d))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,f z := by
  have hmeas : Measurable (fun z : ℝ × ℝ => f (z.1+c,z.2+d)) :=
    hf.comp ((measurable_fst.add_const c).prodMk (measurable_snd.add_const d))
  have hi := bounded_integrable_rectangle hmeas (fun z => hb (z.1+c,z.2+d)) a (a+1) b (b+1)
  have hj := bounded_integrable_unit_square hf hb
  rw [Measure.volume_eq_prod] at hi hj ⊢
  rw [setIntegral_prod _ hi,setIntegral_prod _ hj]
  simp_rw [periodic_integral_unit_translate (hy _) b d]
  apply periodic_integral_unit_translate (f := fun x => ∫ y in Ico (0 : ℝ) 1,f (x,y))
  intro x
  apply setIntegral_congr_fun measurableSet_Ico
  intro y _
  exact hx y x

lemma axialSplit_zero_symm (t : ℝ) (y : Plane) :
    (axialSplit 0).symm (t,y)=UpperComparison.tubeSplit.symm (t,y) := by
  ext i
  simp [axialSplit,coverCoordinatePermute,LinearIsometryEquiv.piLpCongrLeft_apply]

lemma coordinateSectionPoint_coordinates (c : Cover) (t : ℝ) (z : ℂ) :
    coordinateSectionPoint c t z=(axialSplit 0).symm
      (t,planeProductCoordinates.symm (z.re+c 1,z.im+c 2)) := by
  rw [axialSplit_zero_symm]
  ext i
  fin_cases i <;> simp [planeProductCoordinates_symm_apply] <;> ring

lemma centered_complex_integral_periodic {f : Cover → ℝ} (hf : Measurable f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) {M : ℝ} (hb : ∀ x,‖f x‖≤M)
    (c : Cover) (t : ℝ) :
    (∫ z in {z : ℂ | complexSquareGauge z<1/2},f (coordinateSectionPoint c t z))=
      ∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)) := by
  let g : ℝ × ℝ → ℝ := fun z => f ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
  have hg : Measurable g := hf.comp ((axialSplit 0).symm.measurable.comp
    (measurable_const.prodMk planeProductCoordinates.symm.continuous.measurable))
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))=
      {z : ℂ | complexSquareGauge z<1/2} := by
    ext z
    simp [complexSquareGauge,abs_lt,max_lt_iff,Complex.measurableEquivRealProd]
  have hc := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ × ℝ => g (z.1+c 1,z.2+c 2))
    (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))
  rw [hpre] at hc
  have hfun : (fun z : ℂ => g ((Complex.measurableEquivRealProd z).1+c 1,
      (Complex.measurableEquivRealProd z).2+c 2))=(fun z => f (coordinateSectionPoint c t z)) := by
    funext z
    dsimp [g]
    rw [coordinateSectionPoint_coordinates]
  rw [hfun] at hc
  rw [hc]
  have hpp : planeProductCoordinates ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)=transverseSquare := by
    ext y
    simp only [mem_preimage,planeProductCoordinates_apply,mem_prod,mem_Ico,transverseSquare,mem_ofPred_eq]
    constructor
    · intro h j
      fin_cases j <;> tauto
    · intro h
      exact ⟨h 0,h 1⟩
  have he := planeProductCoordinates_measurePreserving.setIntegral_preimage_emb
    planeProductCoordinates.toHomeomorph.measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)
  rw [hpp] at he
  have he' : (∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,g z := by simpa only [g,ContinuousLinearEquiv.symm_apply_apply] using he
  rw [he']
  have hperiod (j : Fin 2) (z : ℝ × ℝ) :
      g (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2)=g z := by
    have hh := hp (Pi.single j.succ (1 : ℤ)) ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
    have hv : (axialSplit 0).symm (t,planeProductCoordinates.symm
        (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2))=
        (axialSplit 0).symm (t,planeProductCoordinates.symm z)+latticeVector (Pi.single j.succ (1 : ℤ)) := by
      rw [axialSplit_zero_symm,axialSplit_zero_symm]
      ext i
      fin_cases i <;> fin_cases j <;> simp [planeProductCoordinates_symm_apply,latticeVector,Pi.single_apply]
    dsimp only [g]
    rw [hv]
    exact hh
  have hx : ∀ y,Function.Periodic (fun x => g (x,y)) 1 := by
    intro y x
    simpa using hperiod 0 (x,y)
  have hy : ∀ x,Function.Periodic (fun y => g (x,y)) 1 := by
    intro x y
    simpa using hperiod 1 (x,y)
  convert periodic_plane_integral_translate hg (fun z => hb _) hx hy (-(1/2)) (-(1/2)) (c 1) (c 2) using 1; norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma centeredPlaneSection_integral {E : Set Torus} (hE : MeasurableSet E)
    {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x)
    (c : Cover) (t : ℝ) :
    (∫ z in centeredPlaneSection E c t,g (coordinateSectionPoint c t z))=
      axialSectionIntegral E 0 g t := by
  let f : Cover → ℝ := fun x => characteristic E (quotientMap x)*g x
  have hf : Measurable f := ((measurable_characteristic hE).comp measurable_quotientMap).mul hg.measurable
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp [f,quotientMap_add,quotientMap_latticeVector,hp]
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  have hb : ∀ x,‖f x‖≤M := by
    intro x
    change ‖characteristic E (quotientMap x)*g x‖≤M
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM x)
  have he := centered_complex_integral_periodic hf hfp hb c t
  have hfun : (fun z => f (coordinateSectionPoint c t z))=
      ((fun z => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E).indicator
        (fun z => g (coordinateSectionPoint c t z)) := by
    funext z
    by_cases hz : quotientMap (coordinateSectionPoint c t z)∈E <;> simp [f,characteristic,hz]
  have hms : MeasurableSet ((fun z : ℂ => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E) :=
    hE.preimage (measurable_quotientMap.comp (coordinateSectionPoint_contDiff c t).continuous.measurable)
  rw [hfun] at he
  rw [setIntegral_indicator hms] at he
  exact he

lemma axialSectionIntegral_one {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : ℝ) :
    axialSectionIntegral E i (fun _ => 1) t=axialSectionArea E i t := by
  have hfun : (fun y : Plane => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*(1 : ℝ))=
      ((fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : quotientMap ((axialSplit i).symm (t,y))∈E <;> simp [characteristic,hy]
  have hms : MeasurableSet ((fun y : Plane => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E) :=
    hE.preimage (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  rw [axialSectionIntegral,hfun,setIntegral_indicator hms]
  simp [axialSectionArea,axialSection,integral_const,Measure.real]

lemma centeredPlaneSection_real_volume {E : Set Torus} (hE : MeasurableSet E) (c : Cover) (t : ℝ) :
    volume.real (centeredPlaneSection E c t)=axialSectionArea E 0 t := by
  have he := centeredPlaneSection_integral hE (g := fun _ => 1) continuous_const (fun _ _ => rfl) c t
  rw [axialSectionIntegral_one hE] at he
  simpa [integral_const,Measure.real] using he

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_RevolutionTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
namespace CubicTorus

lemma hasDerivAt_delaunay_first_integral {r p q : ℝ → ℝ} {H t : ℝ}
    (hr : HasDerivAt r (p t) t) (hp : HasDerivAt p (q t) t)
    (hCMC : H=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3)
    (hr0 : 0 < r t) :
    HasDerivAt (fun s => r s/Real.sqrt (1+p s^2)-H/2*r s^2) 0 t := by
  have hs0 : 0<Real.sqrt (1+p t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
  have hd := ((hasDerivAt_const t (1 : ℝ)).add (hp.pow 2)).sqrt (by positivity : 1+p t^2≠0)
  have he := (hr.div hd hs0.ne').sub ((hr.pow 2).const_mul (H/2))
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,zero_add,Nat.cast_ofNat,pow_one]
  field_simp
  have hcmc : H*(r t*(Real.sqrt (1+p t^2))^3)=
      (Real.sqrt (1+p t^2))^2-r t*q t := by
    field_simp at hCMC ⊢
    nlinarith only [hCMC]
  linear_combination p t * hcmc

theorem delaunay_first_integral {r p q : ℝ → ℝ} {H : ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : ∀ t,HasDerivAt p (q t) t)
    (hpos : ∀ t,0 < r t)
    (hCMC : ∀ t,H=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3) :
    ∃ α : ℝ,∀ t,r t/Real.sqrt (1+p t^2)=α+H/2*r t^2 := by
  let f := fun t => r t/Real.sqrt (1+p t^2)-H/2*r t^2
  have hd (t) : HasDerivAt f 0 t := hasDerivAt_delaunay_first_integral (hr t) (hp t) (hCMC t) (hpos t)
  refine ⟨f 0,?_⟩
  intro t
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  change r t/Real.sqrt (1+p t^2)-H/2*r t^2=f 0 at he
  linarith only [he]

lemma delaunay_first_integral_endpoints {a b α β : ℝ} (ha : 0<a) (hab : a<b)
    (h₁ : a=α+β*a^2) (h₂ : b=α+β*b^2) :
    β=1/(a+b) ∧ α=a*b/(a+b) := by
  have hs : a+b≠0 := (show 0<a+b by linarith).ne'
  have he : (b-a)*(β*(a+b)-1)=0 := by nlinarith only [h₁,h₂]
  have hβ := (mul_eq_zero.mp he).resolve_left (sub_pos.mpr hab).ne'
  have hβ' : β=1/(a+b) := (eq_div_iff hs).2 (by linarith only [hβ])
  refine ⟨hβ',?_⟩
  rw [hβ'] at h₁
  apply (eq_div_iff hs).2
  field_simp at h₁
  nlinarith only [h₁]

lemma delaunay_slope_product {r p β k : ℝ} (hr : 0 < r) (hβ : 0<β) (hk : 0<k)
    (hf : r/Real.sqrt (1+p^2)=β*(r^2+k)) :
    p*(p/Real.sqrt (1+p^2))=r/(β*(r^2+k))-β*(r^2+k)/r := by
  have hs : 0<Real.sqrt (1+p^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p^2 by positivity)
  have hu : 0 < r^2+k := add_pos_of_nonneg_of_pos (sq_nonneg _) hk
  have he : r=β*(r^2+k)*Real.sqrt (1+p^2) := (div_eq_iff hs.ne').mp hf
  have he₁ : r/(β*(r^2+k))=Real.sqrt (1+p^2) := (div_eq_iff (mul_pos hβ hu).ne').2 (by linarith only [he])
  have he₂ : β*(r^2+k)/r=1/Real.sqrt (1+p^2) := by
    rw [eq_div_iff hs.ne',div_mul_eq_mul_div,div_eq_one_iff_eq hr.ne']
    exact he.symm
  rw [he₁,he₂]
  field_simp
  nlinarith only [hs2]

lemma hasDerivAt_delaunay_slope {r p q : ℝ → ℝ} {β k t : ℝ}
    (hp : HasDerivAt p (q t) t) (hr : 0 < r t)
    (hf : r t/Real.sqrt (1+p t^2)=β*(r t^2+k))
    (hCMC : 2*β=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3) :
    HasDerivAt (fun s => p s/Real.sqrt (1+p s^2)) (β*(k/r t^2-1)) t := by
  have hs0 : 0<Real.sqrt (1+p t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
  have hd := ((hasDerivAt_const t (1 : ℝ)).add (hp.pow 2)).sqrt (by positivity : 1+p t^2≠0)
  have he := hp.div hd hs0.ne'
  convert! he using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,zero_add,Nat.cast_ofNat,pow_one]
  have hsimp : (q t*Real.sqrt (1+p t^2)-p t*(2*p t*q t/(2*Real.sqrt (1+p t^2)))) /
      (Real.sqrt (1+p t^2))^2 = q t/(Real.sqrt (1+p t^2))^3 := by
    field_simp
    nlinarith only [congrArg (fun z : ℝ => q t*z) hs2]
  rw [hsimp]
  have hu : 1/(r t*Real.sqrt (1+p t^2))=β*(r t^2+k)/r t^2 := by
    rw [← hf]
    field_simp
  have ht : β*(k/r t^2-1)=1/(r t*Real.sqrt (1+p t^2))-2*β := by
    rw [hu]
    field_simp
    ring
  linarith only [ht,hCMC]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.revolution_section_volume {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) (t : ℝ) :
    volume.real (centeredPlaneSection (openRepresentative E) c t)=Real.pi*r (t,0)^2 := by
  have he := planarRadialRegion_eq_actual_section
    (fun a => (hr.2.2.2.1 (t,a)).1) (fun a => (hr.2.2.2.1 (t,a)).2)
    (fun a u hu hub => hr.2.2.2.2.2.1 (t,a) u hu hub)
  rw [← he,real_volume_planarRadialRegion
    (show Continuous (fun a => r (t,a)) from hr.1.continuous.comp (continuous_const.prodMk continuous_id)) (hr.2.2.1 t)
      (fun a => (hr.2.2.2.1 (t,a)).1)]
  simp only [hangle,intervalIntegral.integral_const,sub_zero,one_smul]

theorem TrueRadialTube.revolution_volume {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    V=Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)^2) := by
  have hU := (isOpen_openRepresentative E).measurableSet
  have hs (t) : axialSectionArea (openRepresentative E) 0 t=Real.pi*r (t,0)^2 := by
    rw [← centeredPlaneSection_real_volume hU c t]
    exact hr.revolution_section_volume hangle t
  have hInt := integral_axialSectionArea hU 0
  simp_rw [hs] at hInt
  rw [integral_const_mul] at hInt
  have hv : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr (isMinimizerAt_openRepresentative_ae hV hE hm),hm.2.1,
      ENNReal.toReal_ofReal hV.1.le]
  rw [hv] at hInt
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)] at hInt
  exact hInt.symm

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_DelaunayPeriodicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_deriv_real {r : ℝ → ℝ} (hr : Function.Periodic r 1) :
    Function.Periodic (deriv r) 1 := by
  intro t
  have he : (fun u => r (u+1))=r := funext hr
  rw [← deriv_comp_add_const,he]

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory
namespace CubicTorus

lemma delaunayRecurrence_continuous {r : ℝ → ℝ} (hr : Continuous r)
    (hpos : ∀ t,0 < r t) {β k : ℝ} (hk : 0<k) (j : ℤ) :
    Continuous (delaunayRecurrence r β k j) := by
  have hz (l : ℤ) : Continuous (fun t => r t^l) :=
    continuous_iff_continuousAt.mpr (fun t => (hr.continuousAt).zpow₀ l (Or.inl (hpos t).ne'))
  unfold delaunayRecurrence
  exact ((continuous_const.mul (hz j)).div ((hr.pow 2).add continuous_const)
    (fun t => (add_pos_of_nonneg_of_pos (sq_nonneg _) hk).ne')).sub
      (continuous_const.mul ((continuous_const.mul (hz j)).add
        (continuous_const.mul (hz (j-2)))))

lemma hasDerivAt_delaunay_moment {r p v : ℝ → ℝ} {β k : ℝ}
    (hβ : β≠0) (hk : 0<k) (hpos : ∀ t,0 < r t)
    (hr : ∀ t,HasDerivAt r (p t) t)
    (hv : ∀ t,HasDerivAt v (β*(k/r t^2-1)) t)
    (hpv : ∀ t,p t*v t=r t/(β*(r t^2+k))-β*(r t^2+k)/r t)
    (j : ℤ) (t : ℝ) :
    HasDerivAt (fun s => r s^j*v s) (delaunayRecurrence r β k j t) t := by
  have ht := (hpos t).ne'
  have hg := ((hasDerivAt_zpow j (r t) (Or.inl ht)).comp t (hr t)).mul (hv t)
  convert! hg using 1
  all_goals try with_reducible_and_instances rfl
  unfold delaunayRecurrence
  simp only [zpow_sub₀ ht,show (r t)^(1 : ℤ)=r t from zpow_one _,zpow_ofNat]
  have hden : r t^2+k≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hk).ne'
  calc
    (j : ℝ)/β*r t^j/(r t^2+k)-β*((j+1 : ℝ)*r t^j+(j-1 : ℝ)*k*(r t^j/r t^2)) =
        (j : ℝ)*(r t^j/r t)*(r t/(β*(r t^2+k))-β*(r t^2+k)/r t)+
          r t^j*(β*(k/r t^2-1)) := by field_simp; ring
    _ = (j : ℝ)*(r t^j/r t)*p t*v t+r t^j*(β*(k/r t^2-1)) := by
      rw [← hpv t]
      ring

theorem delaunay_periodic_moment_recurrence {r p v : ℝ → ℝ} {β k : ℝ}
    (hβ : β≠0) (hk : 0<k) (hpos : ∀ t,0 < r t)
    (hr : ∀ t,HasDerivAt r (p t) t)
    (hv : ∀ t,HasDerivAt v (β*(k/r t^2-1)) t)
    (hpv : ∀ t,p t*v t=r t/(β*(r t^2+k))-β*(r t^2+k)/r t)
    (hrp : Function.Periodic r 1) (hvp : Function.Periodic v 1) (j : ℤ) :
    (∫ t in (0 : ℝ)..1,delaunayRecurrence r β k j t)=0 := by
  have hc : Continuous r := continuous_iff_continuousAt.mpr (fun t => (hr t).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_delaunay_moment hβ hk hpos hr hv hpv j t)
    ((delaunayRecurrence_continuous hc hpos hk j).intervalIntegrable 0 1)]
  have hr01 : r 1=r 0 := by simpa only [zero_add] using hrp 0
  have hv01 : v 1=v 0 := by simpa only [zero_add] using hvp 0
  rw [hr01,hv01,sub_self]

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory Filter
namespace CubicTorus

lemma periodic_radius_extrema {r p : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hper : Function.Periodic r 1) :
    ∃ s t : ℝ,(∀ u,r s ≤ r u) ∧ (∀ u,r u ≤ r t) ∧ p s=0 ∧ p t=0 := by
  have hc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hco := hper.compact_of_continuous (by norm_num : (1 : ℝ)≠0) hc
  obtain ⟨a,⟨s,rfl⟩,ha⟩ := hco.exists_isMinOn (range_nonempty r) continuous_id.continuousOn
  obtain ⟨b,⟨t,rfl⟩,hb⟩ := hco.exists_isMaxOn (range_nonempty r) continuous_id.continuousOn
  have hmin (u : ℝ) : r s ≤ r u := ha (mem_range_self u)
  have hmax (u : ℝ) : r u ≤ r t := hb (mem_range_self u)
  exact ⟨s,t,hmin,hmax,
    (show IsLocalMin r s from Filter.Eventually.of_forall hmin).hasDerivAt_eq_zero (hr s),
    (show IsLocalMax r t from Filter.Eventually.of_forall hmax).hasDerivAt_eq_zero (hr t)⟩

theorem delaunay_nonconstant_parameters {r p q : ℝ → ℝ} {H : ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : ∀ t,HasDerivAt p (q t) t)
    (hpos : ∀ t,0 < r t) (hrp : Function.Periodic r 1) (hpp : Function.Periodic p 1)
    (hCMC : ∀ t,H=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3)
    (hn : ¬∀ t,r t=r 0) :
    ∃ a b : ℝ,0<a ∧ a<b ∧
      (∀ t,r t∈Icc a b) ∧ (∃ s t,r s=a ∧ r t=b ∧ p s=0 ∧ p t=0) ∧
      H=2/(a+b) ∧
      (∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b)) ∧
      ∀ j : ℤ,(∫ t in (0 : ℝ)..1,delaunayRecurrence r (1/(a+b)) (a*b) j t)=0 := by
  obtain ⟨s,t,hmin,hmax,hps,hpt⟩ := periodic_radius_extrema hr hrp
  have hab : r s < r t := by
    apply lt_of_le_of_ne (hmin t)
    intro he
    apply hn
    intro u
    have hu := le_antisymm (hmax u) (by rw [← he]; exact hmin u)
    have h0 := le_antisymm (hmax 0) (by rw [← he]; exact hmin 0)
    exact hu.trans h0.symm
  obtain ⟨α,hα⟩ := delaunay_first_integral hr hp hpos hCMC
  have hs : r s=α+(H/2)*r s^2 := by simpa only [hps,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_one,div_one] using hα s
  have ht : r t=α+(H/2)*r t^2 := by simpa only [hpt,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_one,div_one] using hα t
  obtain ⟨hβ,hα'⟩ := delaunay_first_integral_endpoints (hpos s) hab hs ht
  have hsum : 0 < r s+r t := add_pos (hpos s) (hpos t)
  have hf (u) : r u/Real.sqrt (1+p u^2)=(1/(r s+r t))*(r u^2+r s*r t) := by
    rw [hα u,hβ,hα']; ring
  have hH : H=2/(r s+r t) := by
    calc H=2*(H/2) := by ring
         _=2/(r s+r t) := by rw [hβ]; ring
  refine ⟨r s,r t,hpos s,hab,(fun u => ⟨hmin u,hmax u⟩),⟨s,t,rfl,rfl,hps,hpt⟩,hH,hf,?_⟩
  have hb : 0<1/(r s+r t) := one_div_pos.mpr hsum
  have hk : 0 < r s*r t := mul_pos (hpos s) (hpos t)
  have hv (u) : HasDerivAt (fun u => p u/Real.sqrt (1+p u^2))
      ((1/(r s+r t))*(r s*r t/r u^2-1)) u := by
    apply hasDerivAt_delaunay_slope (hp u) (hpos u) (hf u)
    rw [← hβ]
    convert hCMC u using 1 <;> first | rfl | ring
  have hprod (u) : p u*(p u/Real.sqrt (1+p u^2))=
      r u/((1/(r s+r t))*(r u^2+r s*r t))-(1/(r s+r t))*(r u^2+r s*r t)/r u :=
    delaunay_slope_product (hpos u) hb hk (hf u)
  have hvp : Function.Periodic (fun u => p u/Real.sqrt (1+p u^2)) 1 := by
    intro u; dsimp only; rw [hpp u]
  exact delaunay_periodic_moment_recurrence hb.ne' hk hpos hr hv hprod hrp hvp

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory
namespace CubicTorus

theorem delaunay_area_moment {r p : ℝ → ℝ} {β k : ℝ}
    (hr : Continuous r) (hp : Continuous p) (_hpos : ∀ t,0 < r t)
    (hk : 0<k) (hβ : β≠0)
    (hf : ∀ t,r t/Real.sqrt (1+p t^2)=β*(r t^2+k))
    (hrec : (∫ t in (0 : ℝ)..1,delaunayRecurrence r β k 2 t)=0) :
    (∫ t in (0 : ℝ)..1,r t*Real.sqrt (1+p t^2))=
      (β/2)*(3*(∫ t in (0 : ℝ)..1,r t^2)+k) := by
  have hi : IntervalIntegrable (fun t => r t*Real.sqrt (1+p t^2)) volume 0 1 :=
    (hr.mul (continuous_const.add (hp.pow 2)).sqrt).intervalIntegrable _ _
  have hi' : IntervalIntegrable (fun t => 3*r t^2+k) volume 0 1 :=
    ((continuous_const.mul (hr.pow 2)).add continuous_const).intervalIntegrable _ _
  have he (t : ℝ) : delaunayRecurrence r β k 2 t=
      2*(r t*Real.sqrt (1+p t^2))-β*(3*r t^2+k) := by
    have hs : Real.sqrt (1+p t^2)≠0 := (Real.sqrt_pos.mpr (by positivity : 0<1+p t^2)).ne'
    have hden : r t^2+k≠0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hk).ne'
    have hh := hf t
    rw [div_eq_iff hs] at hh
    simp only [delaunayRecurrence,Int.cast_ofNat,zpow_ofNat,show (2 : ℤ)-2=0 by norm_num]
    norm_num
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z * r t) hh]
  simp_rw [he] at hrec
  rw [intervalIntegral.integral_sub (hi.const_mul 2) (hi'.const_mul β),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hrec
  have hsi : (∫ t in (0 : ℝ)..1,3*r t^2+k)=3*(∫ t in (0 : ℝ)..1,r t^2)+k := by
    rw [intervalIntegral.integral_add (f := fun t => 3*r t^2)
      (g := fun _ => k) (((hr.pow 2).intervalIntegrable 0 1).const_mul 3) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp
  rw [hsi] at hrec
  linarith only [hrec]

lemma delaunay_area_scalar_gt {a b m : ℝ} (ha : 0<a) (hab : a<b)
    (hm : (a^2+b^2)/2 ≤ m) : Real.sqrt m<(3*m+a*b)/(2*(a+b)) := by
  have hb : 0<b := ha.trans hab
  have hk : 0<a*b := mul_pos ha hb
  have hm' : a*b < m := by nlinarith only [hm,sq_pos_of_ne_zero (sub_ne_zero.mpr hab.ne)]
  have hm0 : 0 < m := hk.trans hm'
  have hs : 0<a+b := add_pos ha hb
  have hd := Real.sq_sqrt hm0.le
  have ht : 0≤Real.sqrt m := Real.sqrt_nonneg m
  rw [lt_div_iff₀ (mul_pos (by norm_num) hs)]
  have hden : (a+b)^2≤2*(m+a*b) := by nlinarith only [hm]
  have hmul := mul_le_mul_of_nonneg_right hden hm0.le
  have hg : 8*(m+a*b)*m<(3*m+a*b)^2 := by
    nlinarith only [sq_pos_of_ne_zero (sub_ne_zero.mpr hm'.ne')]
  have hsq : (Real.sqrt m*(2*(a+b)))^2<(3*m+a*b)^2 := by
    nlinarith only [hmul,hg,hd]
  nlinarith only [hsq,hd,ht,hm0,hk,sq_nonneg (Real.sqrt m*(2*(a+b))-(3*m+a*b))]

theorem delaunay_area_gt_cylinder {r p : ℝ → ℝ} {a b : ℝ}
    (hr : Continuous r) (hp : Continuous p) (hpos : ∀ t,0 < r t)
    (ha : 0<a) (hab : a<b)
    (hf : ∀ t,r t/Real.sqrt (1+p t^2)=(1/(a+b))*(r t^2+a*b))
    (hrec : (∫ t in (0 : ℝ)..1,delaunayRecurrence r (1/(a+b)) (a*b) 2 t)=0)
    (hm : (a^2+b^2)/2≤∫ t in (0 : ℝ)..1,r t^2) :
    Real.sqrt (∫ t in (0 : ℝ)..1,r t^2)<∫ t in (0 : ℝ)..1,r t*Real.sqrt (1+p t^2) := by
  have hs := add_pos ha (ha.trans hab)
  rw [delaunay_area_moment hr hp hpos (mul_pos ha (ha.trans hab)) (one_div_ne_zero hs.ne') hf hrec]
  convert delaunay_area_scalar_gt ha hab hm using 1; field_simp

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_FourStarScalarGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_no_monotone_revolution_oai {V : ℝ} (hVhalf : V∈Ioc (0 : ℝ) (1/2))
    {G : Set Torus} (hG : MeasurableSet G) (hm : IsMinimizerAt V G)
    {b : Fin 3 → Bool} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube G (chamberCorner b) r)
    (hangle : ∀ t a,r (t,a)=r (t,0))
    (heven : ∀ t a,r (-t,a)=r (t,a))
    (hneg : ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
      deriv (fun s => r (s,0)) t<0) : False := by
  have hV : V∈Ioo (0 : ℝ) 1 := ⟨hVhalf.1,by linarith [hVhalf.2]⟩
  let R := fun t => r (t,0)
  let p := deriv R
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := hr.1.comp (contDiff_id.prodMk contDiff_const)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := (contDiff_infty_iff_deriv.mp hR).2
  have hRp : Function.Periodic R 1 := fun t => hr.2.1 t 0
  have hpp : Function.Periodic p 1 := periodic_deriv_real hRp
  have hd (t) : HasDerivAt R (p t) t := (hR.differentiable (by simp) t).hasDerivAt
  have hdp (t) : HasDerivAt p (deriv p t) t := (hp.differentiable (by simp) t).hasDerivAt
  have hpos (t) : 0<R t := (hr.2.2.2.1 (t,0)).1
  have hn : ¬∀ t,R t=R 0 := by
    intro he
    have hf : R=fun _ => R 0 := funext he
    have hz : deriv R (chamberCorner b 0+1/4)=0 := by rw [hf,deriv_const]
    have hh := hneg (chamberCorner b 0+1/4) ⟨by linarith,by linarith⟩
    change deriv R (chamberCorner b 0+1/4)<0 at hh
    linarith only [hz,hh]
  obtain ⟨μ,H,σ,N,hN,hNp,hμ,ha,hu,hstab,hσ,hsign,hCMC,hfirst⟩ :=
    hr.exists_revolution_CMC hV hG hm hangle
  change ∀ t,H/σ=1/(R t*Real.sqrt (1+(p t)^2))-deriv p t/(Real.sqrt (1+(p t)^2))^3 at hCMC
  obtain ⟨a,d,ha,hband,hrad,hext,hH,hf,hrec⟩ :=
    delaunay_nonconstant_parameters hd hdp hpos hRp hpp hCMC hn
  have hc : chamberCorner b 0=0 ∨ chamberCorner b 0=1/2 := by
    simp only [chamberCorner]
    cases b 0 <;> simp
  have hmean := delaunay_chamber_monotone_mean ha hband hc hd hRp
    (fun t => heven t 0) hneg hf
  have hstrict := delaunay_area_gt_cylinder hR.continuous hp.continuous hpos ha hband hf (hrec 2) hmean
  have harea := hr.revolution_area_le_perimeter hV hG hm hμ hangle
  have hvolume := hr.revolution_volume hV hG hm hangle
  have hmV : (∫ t in (0 : ℝ)..1,R t^2)=V/Real.pi := by
    apply (eq_div_iff Real.pi_ne_zero).mpr
    change V=Real.pi*(∫ t in (0 : ℝ)..1,R t^2) at hvolume
    linarith only [hvolume]
  have hupper : perimeter G≤ENNReal.ofReal (2*Real.sqrt (Real.pi*V)) :=
    (hm.2.2 _ (UpperComparison.finitePerimeter_canonicalTube hVhalf)
      (UpperComparison.volume_canonicalTube hVhalf)).trans
      (UpperComparison.perimeter_canonicalTube_le hVhalf)
  have hupper' : (perimeter G).toReal≤2*Real.sqrt (Real.pi*V) := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hgt := mul_lt_mul_of_pos_left hstrict (show 0<2*Real.pi by positivity)
  rw [hmV,UpperComparison.tubeArea_formula hV.1.le] at hgt
  exact (not_lt_of_ge hupper') (hgt.trans_le harea)

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_no_monotone_revolution_oai := @OAI.CubicTorus.isMinimizerAt_no_monotone_revolution_oai
