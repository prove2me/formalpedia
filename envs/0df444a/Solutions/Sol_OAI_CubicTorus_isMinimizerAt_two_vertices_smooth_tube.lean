-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:19:32.048436+00:00
-- url     : https://prove2.me/submissions/609819e6-610e-4dd3-a5f7-12805a7fe69d

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_actual_centered_graph_phase_patch
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_openRepresentative_ae
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_periodic_ae_eq_boundary
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_smooth_CMC
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_tubular_sections

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

lemma admissible_zero : AdmissibleField (fun _ => 0) := by
  exact ⟨contDiff_const, by simp, by simp⟩

lemma divergence_zero (x : Cover) : divergence (fun _ => 0) x = 0 := by
  simp [divergence]

lemma admissible_neg {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (fun x => -F x) := by
  refine ⟨hF.1.neg, ?_, ?_⟩
  · intro n x
    change -F (x + latticeVector n) = -F x
    rw [hF.2.1 n x]
  · intro x
    simpa using hF.2.2 x

lemma divergence_neg (F : Cover → Cover) (x : Cover) :
    divergence (fun x => -F x) x = -divergence F x := by
  unfold divergence
  change ∑ i : Fin 3, (fderiv ℝ (-F) x (EuclideanSpace.single i 1)) i = _
  rw [fderiv_neg]
  simp

lemma perimeter_empty : perimeter ∅ = 0 := by
  simp [perimeter]

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

theorem finitePerimeter_congr_ae {E F : Set Torus} (hEF : E =ᵐ[torusVolume] F) :
    FinitePerimeter E ↔ FinitePerimeter F := by
  rw [FinitePerimeter, FinitePerimeter, perimeter_congr_ae hEF]
  exact and_congr ⟨fun h => h.congr hEF, fun h => h.congr hEF.symm⟩ Iff.rfl

theorem isMinimizerAt_congr_ae {E F : Set Torus} {V : ℝ}
    (hEF : E =ᵐ[torusVolume] F) : IsMinimizerAt V E ↔ IsMinimizerAt V F := by
  unfold IsMinimizerAt
  rw [finitePerimeter_congr_ae hEF, measure_congr hEF, perimeter_congr_ae hEF]

lemma cube_preimage : (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹' fundamentalCube =
    univ.pi (fun _ : Fin 3 => Ico (0 : ℝ) 1) := by
  ext x
  simp [fundamentalCube]

lemma integrableOn_divergence {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    IntegrableOn (divergence F) fundamentalCube := by
  have hEmb := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toHomeomorph.measurableEmbedding
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrableOn_comp_preimage hEmb]
  rw [cube_preimage]
  have hc : Continuous (fun x : Fin 3 → ℝ => divergence F (WithLp.toLp 2 x)) :=
    (continuous_divergence hF).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous
  apply hc.integrableOn_Icc.mono_set
  intro x hx
  exact ⟨fun i => (hx i (mem_univ i)).1, fun i => le_of_lt (hx i (mem_univ i)).2⟩

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

theorem integral_divergence_fundamentalCube {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube, divergence F x) = 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) (1 : Fin 3 → ℝ) (by intro i; norm_num)
    g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : (∑ i : Fin 3,
      ((∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 1 x)) -
       ∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) ((1 : Fin 3 → ℝ) ∘ i.succAbove),
         g i (i.insertNth 0 x))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth 1 x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  have hi : (∫ x in Icc (0 : Fin 3 → ℝ) 1, divergence F (e.symm x)) = 0 := hth.trans hzero
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, cube_preimage]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  exact hi

lemma quotientMap_measurePreserving :
    MeasurePreserving quotientMap (volume.restrict fundamentalCube) torusVolume :=
  ⟨measurable_quotientMap, rfl⟩

lemma integral_divergence_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' Eᶜ, divergence F x) =
      -(∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) := by
  have hm := hE.preimage quotientMap_measurePreserving.quasiMeasurePreserving
  have hi := integral_add_compl₀ hm (integrableOn_divergence hF.1)
  rw [Measure.restrict_restrict₀ hm, Measure.restrict_restrict₀ hm.compl,
    integral_divergence_fundamentalCube hF] at hi
  simp only [inter_comm] at hi
  rw [preimage_compl]
  linarith

theorem perimeter_compl {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter Eᶜ = perimeter E := by
  have hle : ∀ E : Set Torus, NullMeasurableSet E torusVolume →
      perimeter Eᶜ ≤ perimeter E := by
    intro E hE
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply le_iSup_of_le (fun x => -F x)
    apply le_iSup_of_le (admissible_neg hF)
    rw [integral_divergence_compl hE hF]
    simp only [divergence_neg, integral_neg, le_refl]
  exact le_antisymm (hle E hE) (by simpa only [compl_compl] using hle Eᶜ hE.compl)

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

lemma product_to_torus_measurePreserving :
    MeasurePreserving (WithLp.toLp 2 : ProductTorus → Torus) volume torusVolume :=
  ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.measurable,
    torusVolume_eq_product.symm⟩

lemma torus_to_product_measurePreserving :
    MeasurePreserving (WithLp.ofLp : Torus → ProductTorus) torusVolume volume := by
  exact product_to_torus_measurePreserving.symm
    (PiLp.homeomorph 2 (fun _ : Fin 3 => AddCircle (1 : ℝ))).symm.toMeasurableEquiv

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

lemma finitePerimeter_translation {E : Set Torus} (hE : FinitePerimeter E) (a : Torus) :
    FinitePerimeter ((fun z => z + a) ⁻¹' E) := by
  refine ⟨hE.1.preimage (measurePreserving_add_right torusVolume a).quasiMeasurePreserving, ?_⟩
  rw [perimeter_translation hE.1]
  exact hE.2

theorem isMinimizerAt_translation {E : Set Torus} {V : ℝ} (hE : IsMinimizerAt V E) (a : Torus) :
    IsMinimizerAt V ((fun z => z + a) ⁻¹' E) := by
  refine ⟨finitePerimeter_translation hE.1 a, ?_, ?_⟩
  · rw [volume_translation hE.1.1, hE.2.1]
  · intro F hF hvF
    rw [perimeter_translation hE.1.1]
    exact hE.2.2 F hF hvF

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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
open Filter
open scoped Topology Convolution

lemma quotientMap_sub (x y : Cover) : quotientMap (x - y) = quotientMap x - quotientMap y := by
  simp only [sub_eq_add_neg, quotientMap_add, quotientMap_neg]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma divergence_smul_function {f : Cover → ℝ} {F : Cover → Cover} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (hF : DifferentiableAt ℝ F point) :
    divergence (fun y ↦ f y • F y) point = f point * divergence F point +
      ⟪gradient f point, F point⟫ := by
  have ha : (∑ i : Fin 3, F point i • EuclideanSpace.single i 1) = F point := by
    ext j
    simp [Pi.single_apply]
  rw [inner_gradient_left]
  conv_rhs => rw [← ha, map_sum]
  change (∑ i : Fin 3, (fderiv ℝ (f • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_smul hf hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    divergence, Finset.mul_sum, map_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
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

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

namespace CubicTorus
open scoped RealInnerProductSpace

lemma divergence_sub_fields {F G : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (hG : DifferentiableAt ℝ G point) :
    divergence (fun y ↦ F y - G y) point = divergence F point - divergence G point := by
  change (∑ i : Fin 3, (fderiv ℝ (F - G) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_sub hF hG]
  simp [divergence, Finset.sum_sub_distrib]

lemma linearForm_apply_basis (L : Cover →L[ℝ] ℝ) (v : Cover) :
    L v = ∑ j : Fin 3, v j * L (EuclideanSpace.single j 1) := by
  have hv : (∑ j : Fin 3, v j • EuclideanSpace.single j 1) = v := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [← hv, map_sum]
  simp

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_FiberPoint
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_WeightedPerimeter
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
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalTest_le_one {F : Cover → Cover} (hF : AdmissibleField F) (z : NormalBundle) :
    normalTest F hF.1.continuous z ≤ 1 := by
  calc
    _ ≤ ‖(z.2 : Cover)‖ * ‖F z.1‖ := real_inner_le_norm _ _
    _ ≤ 1 := by simpa only [z.2.property, one_mul] using hF.2.2 z.1

theorem normalMeasure_weighted_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (w : C(NormalBundle, ℝ))
    {A : ℝ} (hA : ∀ (F : Cover → Cover) (hF : AdmissibleField F),
      (∫ z, w z * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ A) :
    (∫ z, w z ∂(μ : Measure NormalBundle)) ≤ A := by
  let C : ℝ := ‖w‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hwC (z : NormalBundle) : w z ≤ C := by
    exact (le_abs_self _).trans ((w.norm_coe_le_norm z).trans (by dsimp [C]; linarith))
  let P : ℝ := (perimeter E).toReal
  let I : ℝ := ∫ z, w z ∂(μ : Measure NormalBundle)
  let B : ℝ := P + (A - I) / C
  have hiw : Integrable w (μ : Measure NormalBundle) := w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound (F : Cover → Cover) (hF : AdmissibleField F) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) ≤ B := by
    let T := normalTest F hF.1.continuous
    have hiT : Integrable T (μ : Measure NormalBundle) := T.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hiwT : Integrable (fun z ↦ w z * T z) (μ : Measure NormalBundle) :=
      (w.continuous.mul T.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hdef (z : NormalBundle) :
        w z - w z * T z ≤ C * (1 - T z) := by
      have hT : 0 ≤ 1 - T z := sub_nonneg.mpr (normalTest_le_one hF z)
      nlinarith [mul_le_mul_of_nonneg_right (hwC z) hT]
    have hh := integral_mono (hiw.sub hiwT)
      (((integrable_const (1 : ℝ)).sub hiT).const_mul C) hdef
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hiw hiwT, integral_const_mul,
      integral_sub (integrable_const (1 : ℝ)) hiT] at hh
    have hmass : (∫ _ : NormalBundle, (1 : ℝ) ∂(μ : Measure NormalBundle)) = P := by
      simpa only [integral_const, smul_eq_mul, mul_one, P,
        FiniteMeasure.mass, FiniteMeasure.coeFn_def, Measure.real, ENNReal.toReal] using hμ.1
    rw [hmass] at hh
    have hcap : (∫ z, w z * T z ∂(μ : Measure NormalBundle)) ≤ A := hA F hF
    have hflux : (∫ z, T z ∂(μ : Measure NormalBundle)) =
        ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := hμ.2 F hF
    rw [← hflux]
    dsimp only [B]
    apply (mul_le_mul_iff_left₀ hC).mp
    rw [add_mul, div_mul_cancel₀ _ hC.ne']
    dsimp only [I] at *
    nlinarith
  have hB : 0 ≤ B := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hP : perimeter E ≤ ENNReal.ofReal B := by
    unfold perimeter
    exact iSup_le fun F ↦ iSup_le fun hF ↦ ENNReal.ofReal_le_ofReal (hbound F hF)
  have hPB : P ≤ B := by
    simpa only [P, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
  have hneg : (A - I) / C ≥ 0 := by dsimp only [B] at hPB; linarith
  have hh := mul_nonneg hneg hC.le
  rw [div_mul_cancel₀ _ hC.ne'] at hh
  exact sub_nonneg.mp hh

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_weighted_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
        divergence (fun y ↦ w y • F y) x := by
  obtain ⟨M, hM, hb⟩ := periodic_bounded hw.continuous hp
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x • F x) := hw.smul hF.1
  have hGp : ∀ n x, w (x + latticeVector n) • F (x + latticeVector n) = w x • F x := by
    intro n x
    rw [hp, hF.2.1]
  have hGb (x : Cover) : ‖w x • F x‖ ≤ M + 1 := by
    rw [norm_smul]
    calc
      _ ≤ ‖w x‖ * 1 := mul_le_mul_of_nonneg_left (hF.2.2 x) (norm_nonneg _)
      _ ≤ M + 1 := by simpa only [mul_one] using (hb x).trans (by linarith)
  simpa only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right] using
    normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1) hGb

theorem normalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ z, w z.1 ∂(μ : Measure NormalBundle)) := by
  let W : C(NormalBundle, ℝ) := ⟨fun z ↦ w z.1,
    hw.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  have hiW : Integrable W (μ : Measure NormalBundle) :=
    W.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : weightedPerimeter E w ≤ ENNReal.ofReal (∫ z, W z ∂(μ : Measure NormalBundle)) := by
    apply iSup_le
    intro F
    apply iSup_le
    intro hF
    apply ENNReal.ofReal_le_ofReal
    rw [← normalMeasure_weighted_flux hμ hw hp hF]
    apply integral_mono ((W.continuous.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hiW
    intro z
    exact (mul_le_mul_of_nonneg_left (normalTest_le_one hF z) (hn z.1)).trans_eq (mul_one _)
  have htop : weightedPerimeter E w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm hle
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply normalMeasure_weighted_saturation hμ W
  intro F hF
  change (∫ z, w z.1 * normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ _
  rw [normalMeasure_weighted_flux hμ hw hp hF]
  apply (ENNReal.ofReal_le_iff_le_toReal htop).mp
  exact le_iSup_of_le F (le_iSup_of_le hF le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma admissible_convex_cutoff {w : Cover → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x)
    (hb : ∀ x, w x ∈ Icc 0 1)
    {F G : Cover → Cover} (hF : AdmissibleField F) (hG : AdmissibleField G) :
    AdmissibleField (fun x ↦ w x • F x + (1 - w x) • G x) := by
  refine ⟨(hw.smul hF.1).add ((contDiff_const.sub hw).smul hG.1), ?_, ?_⟩
  · intro n x
    dsimp only
    rw [hp, hF.2.1, hG.2.1]
  · intro x
    calc
      _ ≤ ‖w x • F x‖ + ‖(1 - w x) • G x‖ := norm_add_le _ _
      _ = w x * ‖F x‖ + (1 - w x) * ‖G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hb x).1, abs_of_nonneg (sub_nonneg.mpr (hb x).2)]
      _ ≤ w x * 1 + (1 - w x) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left (hF.2.2 x) (hb x).1)
        (mul_le_mul_of_nonneg_left (hG.2.2 x) (sub_nonneg.mpr (hb x).2))
      _ = 1 := by ring

end CubicTorus

namespace CubicTorus

lemma smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.zero_of_nonpos hx]
  exact Real.smoothTransition.nonneg y

lemma smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.smoothTransition.one_of_one_le hx]
  exact Real.smoothTransition.le_one y

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

lemma sublevelCutoff_periodic {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t ε : ℝ) :
    ∀ n x, sublevelCutoff q t ε (x + latticeVector n) = sublevelCutoff q t ε x := by
  intro n x
  simp only [sublevelCutoff, hp]

lemma sublevelCutoff_mem_Icc (q : Cover → ℝ) (t ε : ℝ) (x : Cover) :
    sublevelCutoff q t ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma fderiv_sublevelCutoff {q : Cover → ℝ} {x : Cover}
    (hq : DifferentiableAt ℝ q x) (t ε : ℝ) :
    fderiv ℝ (sublevelCutoff q t ε) x =
      (deriv Real.smoothTransition ((t - q x) / ε) / ε) • (-fderiv ℝ q x) := by
  have hd : DifferentiableAt ℝ Real.smoothTransition ((t - q x) / ε) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num) _
  have hi := (hq.hasFDerivAt.const_sub t).const_smul ε⁻¹
  have hi' : HasFDerivAt (fun y : Cover ↦ (t - q y) / ε)
      (ε⁻¹ • (-fderiv ℝ q x)) x := by
    convert! hi using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    simp [div_eq_inv_mul]
  have ho := hd.hasDerivAt.comp_hasFDerivAt x hi'
  calc
    _ = deriv Real.smoothTransition ((t - q x) / ε) • (ε⁻¹ • (-fderiv ℝ q x)) := by
      convert! ho.fderiv using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by simp only [div_eq_mul_inv, smul_smul]

lemma sublevelCutoff_gradient_zero {q : Cover → ℝ}
    (hq : Differentiable ℝ q) {ε : ℝ} (hε : 0 < ε) (t : ℝ) (x : Cover)
    (hx : q x ≤ t - ε ∨ t ≤ q x) :
    gradient (sublevelCutoff q t ε) x = 0 := by
  apply (InnerProductSpace.toDual ℝ Cover).injective
  simp only [gradient, LinearIsometryEquiv.apply_symm_apply, map_zero]
  rw [fderiv_sublevelCutoff (hq x)]
  have hd : deriv Real.smoothTransition ((t - q x) / ε) = 0 := by
    rcases hx with hx | hx
    · apply smoothTransition_deriv_zero_of_one_le
      apply (le_div_iff₀ hε).2
      linarith
    · exact smoothTransition_deriv_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)
  rw [hd, zero_div, zero_smul]

end CubicTorus

namespace CubicTorus

lemma measurableSet_sublevelRegion {q : Cover → ℝ} (hq : Measurable q) (t : ℝ) :
    MeasurableSet (sublevelRegion q t) :=
  measurableSet_lt (hq.comp measurable_representative) measurable_const

lemma mem_sublevelRegion_quotient {q : Cover → ℝ}
    (hp : ∀ n x, q (x + latticeVector n) = q x) (t : ℝ) (x : Cover) :
    quotientMap x ∈ sublevelRegion q t ↔ q x < t := by
  simp only [sublevelRegion, mem_ofPred_eq, periodic_representative hp]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
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

lemma radialCore_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCore := by
  exact radialBump.contDiff.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma radialCore_compactSupport : HasCompactSupport radialCore :=
  radialBump.hasCompactSupport.mul_right

lemma radialCore_tsupport : tsupport radialCore ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hs : x ∈ tsupport (radialBump : Cover → ℝ) := tsupport_mul_subset_left hx
  rw [radialBump.tsupport_eq] at hs
  have hnorm : ‖x - cubeCenter‖ ≤ 1 / 3 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, radialBump] using hs
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans hnorm
  change ‖x i - (1 / 2 : ℝ)‖ ≤ 1 / 3 at hb
  rw [Real.norm_eq_abs, abs_le] at hb
  constructor <;> linarith

lemma radialSquared_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialSquared :=
  contDiff_const.sub (latticePeriodize_contDiff radialCore_contDiff radialCore_compactSupport)

lemma radialSquared_periodic (n : Fin 3 → ℤ) (x : Cover) :
    radialSquared (x + latticeVector n) = radialSquared x := by
  simp only [radialSquared, latticePeriodize_periodic]

lemma radialSquared_eq_on_cube {x : Cover} (hx : x ∈ fundamentalCube) :
    radialSquared x = 1 - radialBump x * (1 - ‖x - cubeCenter‖ ^ 2) := by
  unfold radialSquared
  rw [(latticePeriodize_eventuallyEq radialCore_compactSupport radialCore_tsupport
    (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  rfl

lemma radialSquared_sublevel_iff {x : Cover} (hx : x ∈ fundamentalCube)
    {t : ℝ} (ht : t ≤ 1 / 16) :
    radialSquared x < t ↔ ‖x - cubeCenter‖ ^ 2 < t := by
  rw [radialSquared_eq_on_cube hx]
  have hn := norm_nonneg (x - cubeCenter)
  have hb0 : 0 ≤ radialBump x := radialBump.nonneg
  have hb1 : radialBump x ≤ 1 := radialBump.le_one
  have he (h : ‖x - cubeCenter‖ ^ 2 < 1 / 16) : radialBump x = 1 := by
    apply radialBump.one_of_mem_closedBall
    change dist x cubeCenter ≤ 1 / 4
    rw [dist_eq_norm]
    nlinarith
  constructor
  · intro hh
    by_cases h : ‖x - cubeCenter‖ ^ 2 < 1 / 16
    · rw [he h, one_mul, sub_sub_cancel] at hh
      exact hh
    · have hh' : 1 / 16 ≤ ‖x - cubeCenter‖ ^ 2 := le_of_not_gt h
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hh')]
  · intro hh
    rw [he (hh.trans_le ht), one_mul, sub_sub_cancel]
    exact hh

lemma representative_mem_fundamentalCube (z : Torus) : representative z ∈ fundamentalCube := by
  intro i
  simpa only [representative, zero_add, mem_Ico] using ((AddCircle.equivIco (1 : ℝ) 0) (z i)).property

lemma sublevelRegion_radialSquared {r : ℝ} (hr : 0 ≤ r) (hsmall : r ≤ 1 / 4) :
    sublevelRegion radialSquared (r ^ 2) = cubeBall r := by
  ext z
  change radialSquared (representative z) < r ^ 2 ↔
    dist (representative z) cubeCenter < r
  rw [radialSquared_sublevel_iff (representative_mem_fundamentalCube _) (by nlinarith), dist_eq_norm]
  exact sq_lt_sq₀ (norm_nonneg _) hr

end CubicTorus

namespace CubicTorus

lemma dist_representative_cubeCenter (x : Torus) :
    dist (representative x) cubeCenter = dist x (quotientMap cubeCenter) := by
  rw [dist_eq_norm, dist_eq_norm, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := ((AddCircle.equivIco (1 : ℝ) 0) (x i)).property
  have hxi : ‖((representative x i - (1 / 2 : ℝ)) : AddCircle (1 : ℝ))‖ =
      |representative x i - (1 / 2 : ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    change |((AddCircle.equivIco (1 : ℝ) 0) (x i) : ℝ) - (1 / 2 : ℝ)| ≤ |(1 : ℝ)| / 2
    norm_num only [abs_one] at *
    rw [abs_le]
    constructor <;> linarith [hi.1, hi.2]
  have hq : ((representative x i : ℝ) : AddCircle (1 : ℝ)) = x i := by
    exact congrArg (fun z : Torus ↦ z i) (quotientMap_representative x)
  simpa only [PiLp.sub_apply, cubeCenter, quotientMap, PiLp.toLp_apply,
    Real.norm_eq_abs, map_sub, hq] using hxi.symm

lemma cubeBall_eq_metricBall (r : ℝ) :
    cubeBall r = Metric.ball (quotientMap cubeCenter) r := by
  ext x
  change dist (representative x) cubeCenter < r ↔ dist x (quotientMap cubeCenter) < r
  rw [dist_representative_cubeCenter]

lemma localRadialSquared_contDiff (a : Torus) :
    ContDiff ℝ (⊤ : ℕ∞) (localRadialSquared a) :=
  radialSquared_contDiff.comp (contDiff_id.add contDiff_const)

lemma localRadialSquared_periodic (a : Torus) (n : Fin 3 → ℤ) (x : Cover) :
    localRadialSquared a (x + latticeVector n) = localRadialSquared a x := by
  unfold localRadialSquared
  rw [show x + latticeVector n + representative (quotientMap cubeCenter - a) =
    (x + representative (quotientMap cubeCenter - a)) + latticeVector n by abel]
  exact radialSquared_periodic n _

lemma sublevelRegion_localRadialSquared (a : Torus) {r : ℝ} (hr : 0 ≤ r) (hs : r ≤ 1 / 4) :
    sublevelRegion (localRadialSquared a) (r ^ 2) = Metric.ball a r := by
  ext z
  have hrep := periodic_representative radialSquared_periodic
    (representative z + representative (quotientMap cubeCenter - a))
  rw [quotientMap_add, quotientMap_representative, quotientMap_representative] at hrep
  change radialSquared (representative z + representative (quotientMap cubeCenter - a)) < r ^ 2 ↔ _
  rw [← hrep]
  change z + (quotientMap cubeCenter - a) ∈ sublevelRegion radialSquared (r ^ 2) ↔ _
  rw [sublevelRegion_radialSquared hr hs, cubeBall_eq_metricBall]
  simp only [Metric.mem_ball, dist_eq_norm]
  rw [show z + (quotientMap cubeCenter - a) - quotientMap cubeCenter = z - a by abel]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma mem_volumeSupport_iff (E : Set Torus) (a : Torus) :
    a ∈ volumeSupport E ↔ ∀ r : ℝ, 0 < r →
      0 < torusVolume.real (E ∩ Metric.ball a r) := by
  rw [volumeSupport, Metric.nhds_basis_ball.mem_measureSupport]
  simp only [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_comm]
  exact forall_congr' fun r ↦ imp_congr_right fun _ ↦
    (ENNReal.toReal_pos_iff.trans (and_iff_left (measure_lt_top _ _))).symm

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

lemma volumeSupport_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    volumeSupport E = volumeSupport F := by
  unfold volumeSupport
  rw [Measure.restrict_congr_set h]

lemma volumeSupport_eq_closure {E : Set Torus} (hE : IsOpen E) :
    volumeSupport E = closure E := by
  apply Subset.antisymm
  · exact Measure.support_restrict_subset.trans inter_subset_left
  · apply closure_minimal _ (isClosed_volumeSupport E)
    have hh := Measure.interior_inter_support (μ := torusVolume) (s := E)
    change E ⊆ (torusVolume.restrict E).support
    simpa only [hE.interior_eq, Measure.support_eq_univ, inter_univ] using hh

lemma isMinimizerAt_closure_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    closure (openRepresentative E) = volumeSupport E := by
  rw [← volumeSupport_eq_closure (isOpen_openRepresentative E)]
  exact volumeSupport_congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin)

lemma isMinimizerAt_frontier_openRepresentative {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    frontier (openRepresentative E) = volumeSupport E ∩ volumeSupport Eᶜ := by
  rw [frontier, (isOpen_openRepresentative E).interior_eq,
    isMinimizerAt_closure_openRepresentative hV hE hmin]
  simp only [openRepresentative, sdiff_eq, compl_compl]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma integral_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) {f : Torus → ℝ}
    (hf : Measurable f) :
    (∫ x, f x ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, f (normalProjection z) ∂(μ : Measure NormalBundle) := by
  change (∫ x, f x ∂Measure.map normalProjection (μ : Measure NormalBundle)) = _
  exact integral_map normalProjection_continuous.measurable.aemeasurable hf.aestronglyMeasurable

lemma integral_spatialNormalMeasure_periodic (μ : FiniteMeasure NormalBundle)
    {w : Cover → ℝ} (hw : Continuous w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) :
    (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z, w z.1 ∂(μ : Measure NormalBundle) := by
  rw [integral_spatialNormalMeasure μ (f := fun x ↦ w (representative x))
    (hw.measurable.comp measurable_representative)]
  congr 1
  ext z
  exact periodic_representative hp z.1

lemma spatialNormalMeasure_weightedPerimeter {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hn : ∀ x, 0 ≤ w x) :
    weightedPerimeter E w = ENNReal.ofReal
      (∫ x, w (representative x) ∂(spatialNormalMeasure μ : Measure Torus)) := by
  rw [integral_spatialNormalMeasure_periodic μ hw.continuous hp]
  exact normalMeasure_weightedPerimeter hμ hw hp hn

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

lemma sublevelCutoff_eq_one {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : q x ≤ t - ε) : sublevelCutoff q t ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).2 (by linarith)

lemma divergence_cutoff_zero {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    {t ε : ℝ} (hε : 0 < ε) {x : Cover} (hx : t ≤ q x) :
    divergence (fun y ↦ sublevelCutoff q t ε y • F y) x = 0 := by
  rw [divergence_smul_function ((sublevelCutoff_contDiff hq t ε).differentiable (by simp) x)
    (hF.differentiable (by simp) x), sublevelCutoff_eq_zero hε hx,
    sublevelCutoff_gradient_zero (hq.differentiable (by simp)) hε t x (Or.inr hx)]
  simp

lemma admissible_sublevelCutoff {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {F : Cover → Cover}
    (hF : AdmissibleField F) (t ε : ℝ) :
    AdmissibleField (fun x ↦ sublevelCutoff q t ε x • F x) := by
  have hh := admissible_convex_cutoff (sublevelCutoff_contDiff hq t ε)
    (sublevelCutoff_periodic hp t ε) (sublevelCutoff_mem_Icc q t ε) hF admissible_zero
  simpa only [smul_zero, add_zero] using hh

lemma weightedPerimeter_sublevelCutoff_le {E : Set Torus} (hE : MeasurableSet E)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {t ε : ℝ} (hε : 0 < ε) :
    weightedPerimeter E (sublevelCutoff q t ε) ≤ perimeter (E ∩ sublevelRegion q t) := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have he : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∩ sublevelRegion q t),
      divergence (fun y ↦ sublevelCutoff q t ε y • F y) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))
      (inter_subset_inter_right _ (preimage_mono inter_subset_left))
    intro x hx
    apply divergence_cutoff_zero hq hF.1 hε
    by_contra hn
    apply hx.2
    refine ⟨hx.1.1, hx.1.2, ?_⟩
    exact (mem_sublevelRegion_quotient hp t x).2 (lt_of_not_ge hn)
  rw [he]
  exact le_iSup₂_of_le (fun x ↦ sublevelCutoff q t ε x • F x)
    (admissible_sublevelCutoff hq hp hF t ε) le_rfl

lemma spatialNormalMeasure_sublevel_le {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x) {s t : ℝ} (hst : s < t)
    (hP : perimeter (E ∩ sublevelRegion q t) ≠ ⊤) :
    (spatialNormalMeasure μ : Measure Torus).real (sublevelRegion q s) ≤
      (perimeter (E ∩ sublevelRegion q t)).toReal := by
  let σ : Measure Torus := spatialNormalMeasure μ
  let w := sublevelCutoff q t (t - s)
  let B := sublevelRegion q s
  have hB : MeasurableSet B := measurableSet_sublevelRegion hq.continuous.measurable s
  have hwb (x : Cover) : w x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (t - s) x
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := sublevelCutoff_contDiff hq t (t - s)
  have hwp : ∀ n x, w (x + latticeVector n) = w x := sublevelCutoff_periodic hp t (t - s)
  have hi : Integrable (fun x ↦ w (representative x)) σ :=
    Integrable.of_bound (hw.continuous.measurable.comp measurable_representative).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (hwb _).1]
        exact (hwb _).2)
  have hminor (x : Torus) : B.indicator (fun _ ↦ (1 : ℝ)) x ≤ w (representative x) := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact le_of_eq (sublevelCutoff_eq_one (sub_pos.mpr hst) (by
        have hh : q (representative x) < s := hx
        linarith)).symm
    · rw [indicator_of_notMem hx]
      exact (hwb _).1
  have hm : σ.real B ≤ ∫ x, w (representative x) ∂σ := by
    have hh := integral_mono ((integrable_const (1 : ℝ)).indicator hB) hi hminor
    simpa only [integral_indicator hB, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] using hh
  have hpbound := weightedPerimeter_sublevelCutoff_le hE hq hp (t := t) (sub_pos.mpr hst)
  rw [spatialNormalMeasure_weightedPerimeter hμ hw hwp (fun x ↦ (hwb x).1)] at hpbound
  have hnonneg : 0 ≤ ∫ x, w (representative x) ∂σ := integral_nonneg fun x ↦ (hwb _).1
  have hh := ENNReal.toReal_mono hP hpbound
  rw [ENNReal.toReal_ofReal hnonneg] at hh
  exact hm.trans hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVLocalTranslation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isNormalMeasure_compl {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    IsNormalMeasure Eᶜ (μ.map reverseNormal) := by
  constructor
  · have hm : ((μ.map reverseNormal).mass : ℝ) = (μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal
        (Measure.map_apply continuous_reverseNormal.measurable MeasurableSet.univ
          (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ, FiniteMeasure.mass, FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map, Measure.real, ENNReal.toReal] using hh
    rw [hm, hμ.1, perimeter_compl hE.nullMeasurableSet]
  · intro F hF
    change (∫ z, normalTest F hF.1.continuous z
      ∂Measure.map reverseNormal (μ : Measure NormalBundle)) = _
    rw [integral_map continuous_reverseNormal.measurable.aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable]
    change (∫ z, ⟪-(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
    simp_rw [inner_neg_left, integral_neg]
    rw [integral_divergence_compl hE.nullMeasurableSet hF, ← hμ.2 F hF]
    rfl

lemma spatialNormalMeasure_reverse (μ : FiniteMeasure NormalBundle) :
    spatialNormalMeasure (μ.map reverseNormal) = spatialNormalMeasure μ := by
  apply Subtype.ext
  change Measure.map normalProjection (Measure.map reverseNormal (μ : Measure NormalBundle)) = _
  rw [Measure.map_map normalProjection_continuous.measurable continuous_reverseNormal.measurable]
  rfl

lemma perimeter_eq_zero_of_volume_eq_zero {E : Set Torus} (hE : torusVolume E = 0) :
    perimeter E = 0 := by
  rw [perimeter_congr_ae (ae_eq_empty.mpr hE), perimeter_empty]

lemma spatialNormalMeasure_support_subset_volumeSupport {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E := by
  intro a ha
  rw [mem_volumeSupport_iff]
  intro r hr
  by_contra! hv
  have hz : torusVolume (E ∩ Metric.ball a r) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hv ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  let s := min r (1 / 4 : ℝ)
  have hs : 0 < s := lt_min hr (by norm_num)
  have hs4 : s ≤ 1 / 4 := min_le_right _ _
  have hsr : s ≤ r := min_le_left _ _
  have hcut : perimeter (E ∩ sublevelRegion (localRadialSquared a) (s ^ 2)) = 0 := by
    rw [sublevelRegion_localRadialSquared a hs.le hs4]
    apply perimeter_eq_zero_of_volume_eq_zero
    apply measure_mono_null (inter_subset_inter_right E (Metric.ball_subset_ball hsr)) hz
  have hbound := spatialNormalMeasure_sublevel_le hE hμ (localRadialSquared_contDiff a)
    (localRadialSquared_periodic a) (s := (s / 2) ^ 2) (t := s ^ 2)
    (by nlinarith [sq_pos_of_pos hs]) (by rw [hcut]; exact ENNReal.zero_ne_top)
  rw [hcut, ENNReal.toReal_zero,
    sublevelRegion_localRadialSquared a (by positivity : 0 ≤ s / 2) (by linarith)] at hbound
  have hzero : (spatialNormalMeasure μ : Measure Torus) (Metric.ball a (s / 2)) = 0 := by
    exact (ENNReal.toReal_eq_zero_iff _).mp
      (le_antisymm hbound ENNReal.toReal_nonneg) |>.resolve_right (measure_ne_top _ _)
  have hp := (Metric.nhds_basis_ball.mem_measureSupport.mp ha) (s / 2) (by positivity)
  exact hp.ne' hzero

lemma spatialNormalMeasure_support_subset_boundary {E : Set Torus}
    (hE : MeasurableSet E) {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    (spatialNormalMeasure μ : Measure Torus).support ⊆ volumeSupport E ∩ volumeSupport Eᶜ := by
  intro a ha
  refine ⟨spatialNormalMeasure_support_subset_volumeSupport hE hμ ha, ?_⟩
  have hh := spatialNormalMeasure_support_subset_volumeSupport hE.compl (isNormalMeasure_compl hE hμ)
  rw [spatialNormalMeasure_reverse] at hh
  exact hh ha

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

lemma unitAngle_deriv (t : ℝ) :
    HasDerivAt unitAngle (((2*Real.pi : ℝ)*Complex.I)*unitAngle t) t := by
  have hd := ((((hasDerivAt_id t).const_mul (2*Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp [unitAngle,id_eq,mul_comm]

lemma unitAngle_continuous : Continuous unitAngle :=
  continuous_iff_continuousAt.mpr fun t => (unitAngle_deriv t).continuousAt

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

lemma unitSquareScale_pos (t : ℝ) : 0<unitSquareScale t :=
  one_div_pos.mpr (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero t)))

lemma complexSquareGauge_continuous : Continuous complexSquareGauge :=
  Complex.continuous_re.abs.max Complex.continuous_im.abs

lemma unitSquareScale_continuous : Continuous unitSquareScale :=
  continuous_const.div (continuous_const.mul (complexSquareGauge_continuous.comp unitAngle_continuous))
    (fun t => (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero t))).ne')

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma radialDensityWeight_contDiff (a : Cover) (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDensityWeight a r ε) :=
  sublevelCutoff_contDiff ((contDiff_id.sub contDiff_const).norm_sq ℝ) _ _

lemma radialDensityWeight_nonneg (a : Cover) (r ε : ℝ) (x : Cover) :
    0 ≤ radialDensityWeight a r ε x := Real.smoothTransition.nonneg _

lemma radialDensityWeight_zero {a x : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε)
    (hx : r ≤ ‖x - a‖) : radialDensityWeight a r ε x = 0 := by
  apply sublevelCutoff_eq_zero hε
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_halfspaceIndicator (n : Cover) : Measurable (halfspaceIndicator n) :=
  measurable_const.indicator (isOpen_lt (innerSL ℝ n).continuous continuous_const).measurableSet

lemma halfspaceIndicator_bound (n x : Cover) : |halfspaceIndicator n x| ≤ 1 := by
  classical
  by_cases hx : ⟪n, x⟫ < 0 <;> simp [halfspaceIndicator, hx]

lemma hyperplane_volume_zero {n : Cover} (hn : ‖n‖ = 1) :
    volume {x : Cover | ⟪n, x⟫ = 0} = 0 := by
  apply Measure.addHaar_submodule volume (LinearMap.ker (innerSL ℝ n).toLinearMap)
  intro htop
  have hm : n ∈ LinearMap.ker (innerSL ℝ n).toLinearMap := by rw [htop]; trivial
  change ⟪n, n⟫ = 0 at hm
  rw [real_inner_self_eq_norm_sq, hn] at hm
  norm_num at hm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma divergence_tsupport_subset (F : Cover → Cover) :
    tsupport (divergence F) ⊆ tsupport F := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (divergence_of_notMem_tsupport hh)

theorem normalMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle)) =
      ∫ x : Cover, characteristic E (quotientMap x) * divergence F x := by
  let G := latticePeriodize F
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := latticePeriodize_contDiff hF hc
  have hGp : ∀ n x, G (x + latticeVector n) = G x := latticePeriodize_periodic F
  obtain ⟨M, hM, hb⟩ := periodic_bounded hG.continuous hGp
  have hflux := normalMeasure_flux hμ hG hGp (by linarith : 0 < M + 1)
    (fun x ↦ (hb x).trans (by linarith : M ≤ M + 1))
  have he (z : NormalBundle) : G z.1 = F z.1 :=
    (latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)).eq_of_nhds
  change (∫ z, ⟪(z.2 : Cover), G z.1⟫ ∂(μ : Measure NormalBundle)) = _ at hflux
  simp_rw [he] at hflux
  have hdiv : (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence G x) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
      with x hx
    have hd := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx.1 i).1, (hx.1 i).2.le⟩)).fderiv_eq (𝕜 := ℝ)
    simp only [divergence, G, hd]
  rw [hdiv] at hflux
  rw [hflux, ← integral_indicator (measurableSet_fundamentalCube.inter (hE.preimage measurable_quotientMap))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · by_cases he : quotientMap x ∈ E <;> simp [characteristic, hx, he]
  · have hd : divergence F x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      apply hx
      exact fun i ↦ ⟨(hs hh i).1.le, (hs hh i).2⟩
    simp [hx, hd]

lemma IsNormalMeasure.congr_ae {E F : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (hEF : E =ᵐ[torusVolume] F) : IsNormalMeasure F μ := by
  refine ⟨?_, ?_⟩
  · rw [← perimeter_congr_ae hEF]
    exact hμ.1
  · intro G hG
    rw [hμ.2 G hG]
    apply setIntegral_congr_set
    exact liftSet_congr_ae hEF

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalProductChart_measurePreserving (n : Cover) :
    MeasurePreserving (normalProductChart n) := by
  exact (((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm _).trans
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm).trans
    (normalRotation n).measurePreserving

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma radialDensityWeight_le_one (a : Cover) (r ε : ℝ) (x : Cover) :
    radialDensityWeight a r ε x ≤ 1 := Real.smoothTransition.le_one _

lemma radialDensityWeight_tsupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    tsupport (radialDensityWeight a r ε) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (radialDensityWeight_zero hr hε (le_of_lt (by
    simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hh)))

lemma radialDensityWeight_hasCompactSupport {a : Cover} {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 < ε) :
    HasCompactSupport (radialDensityWeight a r ε) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (radialDensityWeight_tsupport hr hε)

lemma radialHeightCutoff_one {a x : Cover} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.closedBall a r) : radialHeightCutoff a r x = 1 := by
  have hnorm : ‖x - a‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (by positivity : 0 < 3 * r ^ 2)).mpr
  nlinarith [norm_nonneg (x - a)]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVLipschitzGraph
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalMeasure_frontier_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), quotientMap z.1 ∈ frontier E := by
  have hh : ∀ᵐ c ∂(spatialNormalMeasure μ : Measure Torus), c ∈ frontier E := by
    filter_upwards [Measure.support_mem_ae (μ := (spatialNormalMeasure μ : Measure Torus))] with c hc
    have hc' := spatialNormalMeasure_support_subset_boundary hE hμ hc
    rw [frontier_eq_closure_inter_closure]
    exact ⟨Measure.support_restrict_subset.trans inter_subset_left hc'.1,
      Measure.support_restrict_subset.trans inter_subset_left hc'.2⟩
  change ∀ᵐ c ∂Measure.map normalProjection (μ : Measure NormalBundle), c ∈ frontier E at hh
  exact (ae_map_iff normalProjection_continuous.measurable.aemeasurable
    (show MeasurableSet {c : Torus | c ∈ frontier E} from isClosed_frontier.measurableSet)).mp hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_inner {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪n, normalGraph n g y⟫ = g y := by
  simp [normalGraph, inner_add_right, normalPlaneEmbedding_inner hn,
    inner_smul_right, hn]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma integral_compact_fderiv_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (v : X) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hi : Integrable (fun x ↦ fderiv ℝ f x v) μ :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : X ↦ (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ ↦ differentiableAt_const 1) (fun _ _ ↦ hf.differentiable (by simp) |>.differentiableAt)
  simpa using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_lipschitz (n : Cover) :
    LipschitzWith 1 (normalPlaneCoordinates n) := by
  apply (normalPlaneCoordinates n).lipschitz.weaken
  change ‖(normalPlaneLinearIsometry n).toContinuousLinearMap.adjoint‖₊ ≤ 1
  simp

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma normalColumnChart_apply (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    normalColumnChart a n (t, y) = a + (normalPlaneEmbedding n y + t • n) := by
  change a + normalProductChart n (t, WithLp.ofLp y) = _
  rw [normalProductChart_decompose hn]
  congr 1
  exact add_comm _ _

lemma normalColumnChart_measurePreserving (a n : Cover) :
    MeasurePreserving (normalColumnChart a n) := by
  apply MeasurePreserving.trans _ (measurePreserving_add_left volume a)
  apply MeasurePreserving.trans _ (normalProductChart_measurePreserving n)
  change MeasurePreserving
    (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
  simpa only [Measure.volume_eq_prod] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

lemma integral_normalColumnChart (a n : Cover) {f : Cover → ℝ} (hf : Integrable f) :
    (∫ x : Cover, f x) = ∫ y : Plane, ∫ t : ℝ, f (normalColumnChart a n (t, y)) := by
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f]
  have hi := (normalColumnChart_measurePreserving a n).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf
  exact integral_prod_symm (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z))
    (by simpa only [Measure.volume_eq_prod, Function.comp_def] using hi)

lemma normalColumnChart_height (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) : ⟪n, normalColumnChart a n (t, y) - a⟫ = t := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, inner_add_right,
    normalPlaneEmbedding_inner hn, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, zero_add]

lemma normalColumnChart_projection (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (t : ℝ) (y : Plane) :
    normalPlaneCoordinates n (normalColumnChart a n (t, y) - a) = y := by
  rw [normalColumnChart_apply a hn, add_sub_cancel_left, map_add, map_smul,
    normalPlaneCoordinates_embedding, normalPlaneCoordinates_normal hn, smul_zero, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalColumnChart_line_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (y : Plane) :
    Isometry (fun t : ℝ ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + s • n) -
      (a + (normalPlaneEmbedding n y + t • n)) = (s - t) • n := by rw [sub_smul]; abel
  rw [he, norm_smul, Real.norm_eq_abs, hn, mul_one, Real.dist_eq]

lemma normalColumnChart_plane_isometry (a : Cover) {n : Cover} (hn : ‖n‖ = 1) (t : ℝ) :
    Isometry (fun y : Plane ↦ normalColumnChart a n (t, y)) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [dist_eq_norm, normalColumnChart_apply a hn, normalColumnChart_apply a hn]
  have he : a + (normalPlaneEmbedding n y + t • n) -
      (a + (normalPlaneEmbedding n z + t • n)) = normalPlaneEmbedding n (y - z) := by
    rw [show normalPlaneEmbedding n (y - z) = normalPlaneEmbedding n y - normalPlaneEmbedding n z from
      (normalPlaneLinearIsometry n).map_sub y z]; abel
  rw [he, normalPlaneEmbedding_norm, dist_eq_norm]

lemma halfspace_directional_integrable {ψ : Cover → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (a n v : Cover) :
    Integrable (fun x ↦ halfspaceIndicator n (x - a) * fderiv ℝ ψ x v) := by
  exact (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hs.fderiv_apply ℝ v)).bdd_mul
      ((measurable_halfspaceIndicator n).comp (measurable_id.sub_const a)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using halfspaceIndicator_bound n (x-a))

lemma integral_halfspace_normal_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) =
      ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  rw [integral_normalColumnChart a n (halfspace_directional_integrable hψ hs a n n)]
  apply integral_congr_ae
  filter_upwards [] with y
  let f : ℝ → ℝ := fun t ↦ ψ (normalColumnChart a n (t,y))
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ normalColumnChart a n (t,y)) := by
    simp_rw [normalColumnChart_apply a hn]
    fun_prop
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hψ.comp hc
  have hfs : HasCompactSupport f := hs.comp_isClosedEmbedding
    (normalColumnChart_line_isometry a hn y).isClosedEmbedding
  have hd (t : ℝ) : deriv f t = fderiv ℝ ψ (normalColumnChart a n (t,y)) n := by
    have hh : HasDerivAt (fun s : ℝ ↦ normalColumnChart a n (s,y)) n t := by
      simp_rw [normalColumnChart_apply a hn]
      simpa only [one_smul, add_zero, zero_add, id_eq, add_assoc] using
        ((hasDerivAt_id t).smul_const n).const_add (a + normalPlaneEmbedding n y)
    exact (((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hh).deriv
  have he (t : ℝ) : halfspaceIndicator n (normalColumnChart a n (t,y)-a) *
      fderiv ℝ ψ (normalColumnChart a n (t,y)) n = (Iio (0 : ℝ)).indicator (deriv f) t := by
    by_cases ht : t < 0 <;> simp [halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    hfs.integral_Iic_deriv_eq (hf.of_le (by simp)) 0]
  simp [f, normalColumnChart_apply a hn]

lemma integral_halfspace_tangent_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Plane) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)) = 0 := by
  let f : Cover → ℝ := fun x ↦ halfspaceIndicator n (x-a) * fderiv ℝ ψ x (normalPlaneEmbedding n v)
  have hi := halfspace_directional_integrable hψ hs a n (normalPlaneEmbedding n v)
  rw [← (normalColumnChart_measurePreserving a n).integral_comp' f, Measure.volume_eq_prod]
  have hic := (normalColumnChart_measurePreserving a n).integrable_comp hi.aestronglyMeasurable |>.mpr hi
  rw [integral_prod (f := fun z : ℝ × Plane ↦ f (normalColumnChart a n z)) (by
    simpa only [Measure.volume_eq_prod, Function.comp_def] using hic)]
  have he (t : ℝ) : (∫ y : Plane, f (normalColumnChart a n (t,y))) = 0 := by
    let g : Plane → ℝ := fun y ↦ ψ (normalColumnChart a n (t,y))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ normalColumnChart a n (t,y)) := by
      simp_rw [normalColumnChart_apply a hn]
      exact contDiff_const.add ((normalPlaneLinearIsometry n).contDiff.add contDiff_const)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.comp hc
    have hs' : HasCompactSupport g := hs.comp_isClosedEmbedding
      (normalColumnChart_plane_isometry a hn t).isClosedEmbedding
    have hd (y : Plane) : fderiv ℝ g y v =
        fderiv ℝ ψ (normalColumnChart a n (t,y)) (normalPlaneEmbedding n v) := by
      have hline := ((normalPlaneLinearIsometry n).toContinuousLinearMap.hasFDerivAt (x := y)).add_const (t • n) |>.const_add a
      have hh := ((hψ.differentiable (by simp) _).hasFDerivAt.comp y hline).fderiv
      have he : g = ψ ∘ (fun z : Plane ↦ a + ((normalPlaneLinearIsometry n).toContinuousLinearMap z + t • n)) := by
        funext z
        simp only [g, Function.comp_def, normalColumnChart_apply a hn]
        rfl
      rw [he, hh, normalColumnChart_apply a hn]
      rfl
    have hh : (fun y : Plane ↦ f (normalColumnChart a n (t,y))) =
        fun y ↦ (if t < 0 then (1 : ℝ) else 0) * fderiv ℝ g y v := by
      ext y
      by_cases ht : t < 0 <;> simp [f, halfspaceIndicator, normalColumnChart_height a hn, ht, hd]
    rw [hh, integral_const_mul, integral_compact_fderiv_zero hg hs', mul_zero]
  simp_rw [he]
  simp

lemma integral_halfspace_directional_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ) (v : Cover) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * fderiv ℝ ψ x v) =
      ⟪n,v⟫ * ∫ y : Plane, ψ (a + normalPlaneEmbedding n y) := by
  have he (x : Cover) : halfspaceIndicator n (x-a) * fderiv ℝ ψ x v =
      halfspaceIndicator n (x-a) * fderiv ℝ ψ x
        (normalPlaneEmbedding n (normalPlaneCoordinates n v)) +
      ⟪n,v⟫ * (halfspaceIndicator n (x-a) * fderiv ℝ ψ x n) := by
    conv_lhs => arg 2; arg 2; rw [← normalPlaneCoordinates_reconstruct hn v]
    rw [map_add, map_smul]
    ring
  simp_rw [he]
  rw [integral_add (halfspace_directional_integrable hψ hs a n _)
      ((halfspace_directional_integrable hψ hs a n n).const_mul ⟪n,v⟫),
    integral_const_mul, integral_halfspace_tangent_derivative a hn hψ hs,
    integral_halfspace_normal_derivative a hn hψ hs, zero_add]

theorem integral_halfspace_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, halfspaceIndicator n (x-a) * divergence F x) =
      ∫ y : Plane, ⟪n, F (a + normalPlaneEmbedding n y)⟫ := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ halfspace_directional_integrable (hp i) (hps i) a n _)]
  simp_rw [integral_halfspace_directional_derivative a hn (hp _) (hps _)]
  have hg (i : Fin 3) : Integrable (fun y : Plane ↦ ⟪n, EuclideanSpace.single i 1⟫ *
      ψ i (a + normalPlaneEmbedding n y)) := by
    have hc := (hp i).continuous.comp (normalColumnChart_plane_isometry a hn 0).continuous
    have hcc := (hps i).comp_isClosedEmbedding (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
    have hi := (hc.integrable_of_hasCompactSupport (μ := volume) hcc).const_mul ⟪n, EuclideanSpace.single i 1⟫
    simpa only [Function.comp_def, normalColumnChart_apply a hn, zero_smul, add_zero] using hi
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ hg i)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [EuclideanSpace.inner_single_right, ψ]
  simp [PiLp.inner_apply, mul_comm]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMove_hasFDerivAt (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (normalMove n f)
      (ContinuousLinearMap.id ℝ Cover + (fderiv ℝ f x).smulRight n) x := by
  exact (hasFDerivAt_id x).add (hf.hasFDerivAt.smul_const n)

lemma normalMove_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMove n f) := contDiff_id.add (hf.smul_const n)

lemma normalPullback_contDiff (n : Cover) {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (normalPullback n f F) := by
  have hd := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hG := hF.comp (normalMove_contDiff n hf)
  exact (contDiff_const.add (hd.clm_apply contDiff_const)).smul hG |>.sub
    ((hd.clm_apply hG).smul contDiff_const)

lemma divergence_comp_normalMove (n : Cover) {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) {F : Cover → Cover}
    (hF : DifferentiableAt ℝ F (normalMove n f x)) :
    divergence (fun y ↦ F (normalMove n f y)) x =
      divergence F (normalMove n f x) +
        fderiv ℝ f x (fderiv ℝ F (normalMove n f x) n) := by
  have hd := (hF.hasFDerivAt.comp x (normalMove_hasFDerivAt n hf)).fderiv
  change fderiv ℝ (fun y ↦ F (normalMove n f y)) x = _ at hd
  simp only [divergence, hd, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [linearForm_apply_basis]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalPullback_divergence (n : Cover) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (normalPullback n f F) x =
      normalJacobian n f x * divergence F (normalMove n f x) := by
  have hfd := (hf.differentiable (by simp)).differentiableAt (x := x)
  have hdf := ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp)).differentiableAt (x := x)
  have hm := normalMove_hasFDerivAt n hfd
  have hg := (hF.differentiable (by simp)).differentiableAt (x := normalMove n f x)
  have hu := hg.hasFDerivAt.comp x hm
  have hj := (hdf.hasFDerivAt.clm_apply (hasFDerivAt_const n x)).const_add 1
  have hb := hdf.hasFDerivAt.clm_apply hu
  have he := ((hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)) n (F (normalMove n f x))
  change divergence (fun y ↦ normalJacobian n f y • F (normalMove n f y) -
    fderiv ℝ f y (F (normalMove n f y)) • n) x = _
  have hjf := hj.fderiv
  change fderiv ℝ (normalJacobian n f) x = _ at hjf
  dsimp only [Function.comp_def] at hb
  have hJ : DifferentiableAt ℝ (normalJacobian n f) x := hj.differentiableAt
  have hU : DifferentiableAt ℝ (fun y ↦ F (normalMove n f y)) x := hu.differentiableAt
  have hB : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (F (normalMove n f y))) x := hb.differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y ↦ normalJacobian n f y • F (normalMove n f y)) x := hJ.smul hU
  have hC : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (F (normalMove n f y)) • n) x := hB.smul_const n
  rw [divergence_sub_fields hA hC,
    divergence_smul_function hJ hU, divergence_smul_const hB, inner_gradient_left,
    hjf, hb.fderiv, divergence_comp_normalMove n hfd hg]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    ContinuousLinearMap.flip_apply, zero_add,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, map_zero, smul_eq_mul]
  dsimp only [normalJacobian, Function.comp_def]
  rw [← he]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphShear_columnChart (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphShear a n g (normalColumnChart a n (t,y)) = normalColumnChart a n (t+g y,y) := by
  change normalColumnChart a n (t,y) +
    g (normalPlaneCoordinates n (normalColumnChart a n (t,y)-a)) • n = _
  rw [normalColumnChart_projection a hn, normalColumnChart_apply a hn,
    normalColumnChart_apply a hn, add_smul]
  abel

lemma columnShear_measurePreserving {g : Plane → ℝ} (hg : Measurable g) :
    MeasurePreserving (fun p : ℝ × Plane ↦ (p.1+g p.2, p.2)) := by
  have hs : MeasurePreserving (fun p : Plane × ℝ ↦ (p.1, p.2+g p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.add (hg.comp measurable_fst))
      (Eventually.of_forall fun y ↦ (measurePreserving_add_right volume (g y)).map_eq)
  have hh := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure ℝ))).comp (hs.comp (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure Plane))))
  simpa only [Function.comp_def, Prod.swap, Measure.volume_eq_prod] using hh

lemma graphShear_measurePreserving (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Measurable g) : MeasurePreserving (graphShear a n g) := by
  have hi : MeasurePreserving (normalColumnChart a n).symm :=
    MeasurePreserving.symm (normalColumnChart a n) (normalColumnChart_measurePreserving a n)
  have hh := (normalColumnChart_measurePreserving a n).comp
    ((columnShear_measurePreserving hg).comp hi)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  obtain ⟨⟨t,y⟩,rfl⟩ := (normalColumnChart a n).surjective x
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact graphShear_columnChart a hn g t y

lemma graphHeightExtension_fderiv (a n : Cover) {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (x : Cover) : fderiv ℝ (graphHeightExtension a n g) x =
      (fderiv ℝ g (normalPlaneCoordinates n (x-a))).comp (normalPlaneCoordinates n) := by
  unfold graphHeightExtension
  have hp := (normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, graphHeightExtension] using
    ((hg _).hasFDerivAt.comp x hp).fderiv

lemma graphHeightExtension_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    fderiv ℝ (graphHeightExtension a n g) x n = 0 := by
  rw [graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    normalPlaneCoordinates_normal hn, map_zero]

lemma graphShear_jacobian (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (x : Cover) :
    normalJacobian n (graphHeightExtension a n g) x = 1 := by
  rw [normalJacobian, graphHeightExtension_normal a hn hg, add_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphSublevelIndicator_shear (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (x : Cover) :
    graphSublevelIndicator a n g (graphShear a n g x) = halfspaceIndicator n (x-a) := by
  have hheight : ⟪n, graphShear a n g x - a⟫ = ⟪n,x-a⟫ + graphHeightExtension a n g x := by
    simp only [graphShear, normalMove, add_sub_right_comm, inner_add_right,
      inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hp : graphHeightExtension a n g (graphShear a n g x) = graphHeightExtension a n g x :=
    congrArg g (graphShear_projection a hn g x)
  simp only [graphSublevelIndicator, Set.indicator, Set.mem_ofPred_eq, hheight, hp,
    add_lt_iff_neg_right, halfspaceIndicator]

lemma normalPullback_graph_compactSupport (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {F : Cover → Cover} (hs : HasCompactSupport F) :
    HasCompactSupport (normalPullback n (graphHeightExtension a n g) F) := by
  have hc := hs.comp_homeomorph (graphShearHomeomorph a hn hg)
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx
  dsimp only [Function.comp_def, graphShearHomeomorph] at hx
  have hh : F (graphShear a n g x) = 0 := hx
  simp only [Function.mem_support, not_not]
  change normalPullback n (graphHeightExtension a n g) F x = 0
  change F (normalMove n (graphHeightExtension a n g) x) = 0 at hh
  simp only [normalPullback, hh, smul_zero, map_zero, zero_smul, sub_self]

lemma graphAreaVector_pullback (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Differentiable ℝ g) (F : Cover → Cover) (y : Plane) :
    ⟪n, normalPullback n (graphHeightExtension a n g) F (a+normalPlaneEmbedding n y)⟫ =
      ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hs : graphShear a n g (a+normalPlaneEmbedding n y) = a+normalGraph n g y := by
    simp only [graphShear, normalMove, graphHeightExtension, add_sub_cancel_left,
      normalPlaneCoordinates_embedding, normalGraph]
    abel
  rw [normalPullback, graphShear_jacobian a hn hg, one_smul, ← graphShear, hs,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hn, one_pow,
    mul_one, graphHeightExtension_fderiv a n hg, ContinuousLinearMap.comp_apply,
    add_sub_cancel_left, normalPlaneCoordinates_embedding]
  rw [graphAreaVector, inner_sub_left]
  congr 1
  rw [show normalPlaneEmbedding n (gradient g y) =
    (normalPlaneLinearIsometry n).toContinuousLinearMap (gradient g y) from rfl,
    ← ContinuousLinearMap.adjoint_inner_right, inner_gradient_left]
  rfl

theorem integral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hmp : MeasurePreserving (graphShearHomeomorph a hn hg.continuous).toMeasurableEquiv :=
    graphShear_measurePreserving a hn hg.continuous.measurable
  rw [← hmp.integral_comp' (fun x : Cover ↦ graphSublevelIndicator a n g x * divergence F x)]
  have he (x : Cover) : graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
      divergence F (graphShearHomeomorph a hn hg.continuous x) =
      halfspaceIndicator n (x-a) * divergence (normalPullback n (graphHeightExtension a n g) F) x := by
    change graphSublevelIndicator a n g (graphShear a n g x) * divergence F (graphShear a n g x) = _
    rw [graphSublevelIndicator_shear a hn, normalPullback_divergence n
      (graphHeightExtension_contDiff a n hg) hF,
      graphShear_jacobian a hn (hg.differentiable (by simp)), one_mul]
    rfl
  change (∫ x : Cover, graphSublevelIndicator a n g (graphShearHomeomorph a hn hg.continuous x) *
    divergence F (graphShearHomeomorph a hn hg.continuous x)) = _
  simp_rw [he]
  rw [integral_halfspace_divergence a hn
    (normalPullback_contDiff n (graphHeightExtension_contDiff a n hg) hF)
    (normalPullback_graph_compactSupport a hn hg.continuous hs)]
  apply integral_congr_ae
  exact Eventually.of_forall (graphAreaVector_pullback a hn (hg.differentiable (by simp)) F)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graph_trace_compactSupport {X : Type*} [Zero X]
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hs : HasCompactSupport F) :
    HasCompactSupport (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  have hc := (hs.comp_homeomorph (graphShearHomeomorph a hn hg)).comp_isClosedEmbedding
    (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
  have he (y : Plane) : graphShearHomeomorph a hn hg (normalColumnChart a n (0,y)) =
      a+normalGraph n g y := by
    change graphShear a n g (normalColumnChart a n (0,y)) = _
    rw [graphShear_columnChart a hn, zero_add, normalColumnChart_apply a hn]
    rfl
  simpa only [Function.comp_def, he] using hc

lemma graphAreaVector_continuous (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphAreaVector n g) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact continuous_const.sub ((normalPlaneLinearIsometry n).continuous.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp hd))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_norm_ge {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖y‖ ≤ ‖normalGraph n g y‖ := by
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (normalGraph n g y) 0
  simpa only [normalPlaneCoordinates_graph hn, map_zero, dist_zero_right,
    NNReal.coe_one, one_mul] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVPlanarLocalModels
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma blowup_test_inner_bound {F : Cover → Cover} (hn : ∀ x, ‖F x‖ ≤ 1)
    (z : BlowupNormalBundle) : |⟪(z.2 : Cover),F z.1⟫| ≤ 1 := by
  have hh : |⟪(z.2 : Cover),F z.1⟫| ≤ ‖F z.1‖ := by
    simpa only [Real.norm_eq_abs,z.2.property,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (z.2 : Cover) (F z.1)
  exact hh.trans (hn _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma setIntegral_divergence_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B))
    {F : Cover → Cover} (hs : tsupport F ⊆ O) :
    (∫ x in A, divergence F x) = ∫ x in B, divergence F x := by
  rw [← integral_indicator hA,← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [hAB] with x hx
  by_cases ho : x ∈ O
  · have hh := hx ho
    by_cases ha : x ∈ A
    · simp only [indicator_of_mem ha,indicator_of_mem (hh.mp ha)]
    · simp only [indicator_of_notMem ha,indicator_of_notMem (mt hh.mpr ha)]
  · have hz : divergence F x = 0 := divergence_of_notMem_tsupport (fun hh ↦ ho (hs hh))
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha,hb,hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
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

lemma graphMollifier_radius_tendsto :
    Tendsto (fun i ↦ (graphMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifier,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma graphSmooth_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    Tendsto (fun i ↦ graphSmooth (graphMollifier i) g y) atTop (𝓝 (g y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [mul_zero] using graphMollifier_radius_tendsto.const_mul (K:ℝ))
  exact graphSmooth_error _ hg y

theorem graphSmooth_fderiv_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ fderiv ℝ (graphSmooth (graphMollifier i) g) y)
      atTop (𝓝 (fderiv ℝ g y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi
  have ha := lipschitz_probability_average_hasFDerivAt (graphSmoothingMeasure_ac (graphMollifier i))
    hg (graphMollifier i).rOut_pos.le (graphSmoothingMeasure_radius (graphMollifier i)) y
  change dist (fderiv ℝ (fun z ↦ ∫ w, g (z-w) ∂graphSmoothingMeasure (graphMollifier i)) y) _ < ε
  rw [ha.2.fderiv,dist_eq_norm]
  have he : (∫ _w : Plane, fderiv ℝ g y ∂graphSmoothingMeasure (graphMollifier i)) = fderiv ℝ g y := by simp
  rw [← he,← integral_sub ha.1 (integrable_const _)]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have hb : (∫ w, ‖fderiv ℝ g (y-w)-fderiv ℝ g y‖ ∂graphSmoothingMeasure (graphMollifier i)) ≤ ε/2 := by
    calc
      _ ≤ ∫ _w : Plane, ε/2 ∂graphSmoothingMeasure (graphMollifier i) := by
        apply integral_mono_ae (ha.1.sub (integrable_const _)).norm (integrable_const _)
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with w hw
        have hh : dist (y-w) y < δ := by simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hw.trans_lt hi
        simpa only [dist_eq_norm,Pi.sub_apply] using (hclose hh).le
      _ = _ := by simp
  exact hb.trans_lt (by linarith)

lemma graphSmooth_gradient_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ gradient (graphSmooth (graphMollifier i) g) y) atTop (𝓝 (gradient g y)) := by
  exact ((InnerProductSpace.toDual ℝ Plane).symm.continuous.tendsto _).comp
    (graphSmooth_fderiv_tendsto hg hc)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_trace_volume_zero (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) :
    volume {x : Cover | ⟪n,x-a⟫ = graphHeightExtension a n g x} = 0 := by
  have hz : volume {x : Cover | ⟪n,x-a⟫ = 0} = 0 := by
    simpa only [Set.preimage_ofPred_eq,sub_eq_add_neg] using
      (measurePreserving_add_right volume (-a)).quasiMeasurePreserving.preimage_null
        (hyperplane_volume_zero hn)
  have hh := (graphShear_measurePreserving a hn hg.neg.measurable).quasiMeasurePreserving.preimage_null hz
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_preimage,graphShear,normalMove,graphHeightExtension,
    add_sub_right_comm,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hn,
    one_pow,mul_one,Pi.neg_apply]
  constructor <;> intro h <;> linarith

lemma measurable_graphSublevelIndicator (a n : Cover) {g : Plane → ℝ} (hg : Measurable g) :
    Measurable (graphSublevelIndicator a n g) := by
  exact measurable_const.indicator (measurableSet_lt (by fun_prop)
    (hg.comp ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const))))

lemma graphSublevelIndicator_bound (a n : Cover) (g : Plane → ℝ) (x : Cover) :
    |graphSublevelIndicator a n g x| ≤ 1 := by
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

lemma graphSublevelIndicator_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (a n : Cover) {x : Cover} (hx : ⟪n,x-a⟫ ≠ graphHeightExtension a n g x) :
    Tendsto (fun i ↦ graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphSublevelIndicator a n g x)) := by
  have ht := graphSmooth_tendsto hg (normalPlaneCoordinates n (x-a))
  have he : ∀ᶠ i in atTop,
      graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x = graphSublevelIndicator a n g x := by
    by_cases hl : ⟪n,x-a⟫ < graphHeightExtension a n g x
    · filter_upwards [ht.eventually (Ioi_mem_nhds hl)] with i hi
      change (if ⟪n,x-a⟫ < graphSmooth (graphMollifier i) g (normalPlaneCoordinates n (x-a)) then (1:ℝ) else 0) = _
      rw [ite_eq_left hi]
      exact (indicator_of_mem hl (fun _ ↦ (1:ℝ))).symm
    · have hh : graphHeightExtension a n g x < ⟪n,x-a⟫ := lt_of_le_of_ne (not_lt.mp hl) hx.symm
      filter_upwards [ht.eventually (Iio_mem_nhds hh)] with i hi
      have hi' : ¬ ⟪n,x-a⟫ < graphHeightExtension a n (graphSmooth (graphMollifier i) g) x := not_lt.mpr hi.le
      simp [graphSublevelIndicator,hl,hi']
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with i hi
  exact hi.symm

lemma graphSublevel_flux_mollification_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    Tendsto (fun i ↦ ∫ x : Cover, graphSublevelIndicator a n (graphSmooth (graphMollifier i) g) x * divergence F x)
      atTop (𝓝 (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x)) := by
  have hi : Integrable (divergence F) := (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖divergence F x‖)
    (fun i ↦ ((measurable_graphSublevelIndicator a n (graphSmooth_contDiff _ hg).continuous.measurable).mul
      (continuous_divergence hF).measurable).aestronglyMeasurable) hi.norm
  · intro i
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (graphSublevelIndicator_bound a n _ x)
  · have hae : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
      simpa only [ae_iff,not_not] using graph_trace_volume_zero a hn hg.continuous
    filter_upwards [hae] with x hx
    exact (graphSublevelIndicator_tendsto hg a n hx).mul_const _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_norm_linear {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    ‖graphAreaVector n g y‖ ≤ 1+(K:ℝ) := by
  calc
    _ ≤ ‖n‖+‖normalPlaneEmbedding n (gradient g y)‖ := norm_sub_le _ _
    _ = 1+‖fderiv ℝ g y‖ := by rw [hn,normalPlaneEmbedding_norm,plane_gradient_norm]
    _ ≤ _ := add_le_add le_rfl (norm_fderiv_le_of_lipschitz ℝ hg)

lemma graph_trace_zero_outside {X : Type*} [Zero X] {a n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → X} {R : ℝ} (hs : tsupport F ⊆ Metric.closedBall a R)
    (g : Plane → ℝ) {y : Plane} (hy : y ∉ Metric.closedBall (0 : Plane) R) :
    F (a+normalGraph n g y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] at hh
  exact hy (by simpa only [Metric.mem_closedBall,dist_zero_right] using
    (normalGraph_norm_ge hn g y).trans hh)

theorem integral_C1graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫ := by
  have hFs : HasCompactSupport F := (isCompact_closedBall a R).of_isClosed_subset isClosed_closure hs
  obtain ⟨M,hM⟩ := hF.continuous.norm.bddAbove_range_of_hasCompactSupport hFs.norm
  have hMb (x : Cover) : ‖F x‖ ≤ M := hM (mem_range_self x)
  have hM0 : 0 ≤ M := (norm_nonneg (F 0)).trans (hMb 0)
  let B : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator (fun _ ↦ (1+(K:ℝ))*M)
  have hBi : Integrable B := (integrableOn_const (isCompact_closedBall (0 : Plane) R).measure_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have ht : Tendsto (fun i ↦ ∫ y : Plane,
      ⟪graphAreaVector n (graphSmooth (graphMollifier i) g) y,
        F (a+normalGraph n (graphSmooth (graphMollifier i) g) y)⟫) atTop
      (𝓝 (∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun i ↦ ((graphAreaVector_continuous n (graphSmooth_contDiff _ hg)).inner
        (graph_trace_continuous a n (graphSmooth_contDiff _ hg).continuous hF.continuous)).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · rw [show B y = (1+(K:ℝ))*M from indicator_of_mem hy _]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (graphAreaVector_norm_linear hn (graphSmooth_lipschitz _ hg) y)
            (hMb _) (norm_nonneg _) (by positivity))
      · rw [graph_trace_zero_outside hn hs _ hy,inner_zero_right,norm_zero,
          show B y = 0 from indicator_of_notMem hy _]
    · filter_upwards [] with y
      by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
      · have hd := graphSmooth_gradient_tendsto hg (hc y hy)
        have hnG : Tendsto (fun i ↦ normalGraph n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (normalGraph n g y)) :=
          tendsto_const_nhds.add ((graphSmooth_tendsto hg y).smul_const n)
        have hnA : Tendsto (fun i ↦ graphAreaVector n (graphSmooth (graphMollifier i) g) y)
            atTop (𝓝 (graphAreaVector n g y)) :=
          tendsto_const_nhds.sub (((normalPlaneLinearIsometry n).continuous.tendsto _).comp hd)
        exact hnA.inner ((hF.continuous.tendsto _).comp (tendsto_const_nhds.add hnG))
      · simp only [graph_trace_zero_outside hn hs _ hy,inner_zero_right]
        exact tendsto_const_nhds
  apply tendsto_nhds_unique (graphSublevel_flux_mollification_tendsto a hn hg hF hFs)
  simpa only [integral_graphSublevel_divergence a hn (graphSmooth_contDiff _ hg) hF hFs] using ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphAreaVector_continuousAt (n : Cover) {g : Plane → ℝ} {y : Plane}
    (hc : ContinuousAt (fderiv ℝ g) y) : ContinuousAt (graphAreaVector n g) y := by
  exact continuousAt_const.sub ((normalPlaneLinearIsometry n).continuous.continuousAt.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.continuousAt.comp hc))

lemma graph_weighted_continuous (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Continuous (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
  · exact (graph_trace_continuous a n hg hφ).continuousAt.mul (hψ y hy)
  · have he : (fun z : Plane ↦ φ (a+normalGraph n g z)*ψ z) =ᶠ[𝓝 y] fun _ ↦ 0 := by
      filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      rw [graph_trace_zero_outside hn hs _ hz,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq he

lemma graph_weighted_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {R : ℝ}
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Metric.closedBall a R)
    {ψ : Plane → ℝ} (hψ : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt ψ y) :
    Integrable (fun y : Plane ↦ φ (a+normalGraph n g y)*ψ y) :=
  (graph_weighted_continuous a hn hg hφ hs hψ).integrable_of_hasCompactSupport
    (graph_trace_compactSupport a hn hg hsφ).mul_right

lemma setIntegral_graphSublevel_divergence (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall a R) :
    (∫ x in {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x}, divergence F x) =
      ∫ y : Plane, ⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  rw [← integral_C1graphSublevel_divergence a hn hg hc hF hs]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  rw [← integral_indicator hm]
  congr 1
  funext x
  classical
  by_cases hx : ⟪n,x-a⟫ < graphHeightExtension a n g x <;>
    simp [graphSublevelIndicator,hx]

theorem blowup_graph_patch_weighted_flux {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*⟪graphAreaVector n g y,F (a+normalGraph n g y)⟫ := by
  let H : Cover → Cover := fun x ↦ φ x • F x
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hφ.smul hF
  have hsH : HasCompactSupport H := hsφ.smul_right
  have hHO : tsupport H ⊆ O := (tsupport_smul_subset_left _ _).trans hφO
  have hnH (x) : ‖H x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hφb x).1]
    exact (mul_le_mul (hφb x).2 (hnF x) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have he : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, ⟪(z.2 : Cover),H z.1⟫
      ∂(ν : Measure BlowupNormalBundle)) = ∫ z, ⟪(z.2 : Cover),H z.1⟫ ∂(ν : Measure BlowupNormalBundle) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hh : H z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hHO h))
    simp only [hh,inner_zero_right]
  have hm : MeasurableSet {x : Cover | ⟪n,x-a⟫ < graphHeightExtension a n g x} :=
    measurableSet_lt (by fun_prop) (hg.continuous.measurable.comp
      ((normalPlaneCoordinates n).measurable.comp (measurable_id.sub measurable_const)))
  have hh := hflux H hH hsH hHO hnH
  rw [setIntegral_divergence_congr_local hA hm hgraph
      ((tsupport_smul_subset_left _ _).trans hφU),
    setIntegral_graphSublevel_divergence a hn hg hc hH
      ((tsupport_smul_subset_left _ _).trans hφR)] at hh
  rw [← he] at hh
  simpa only [H,inner_smul_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_contDiff (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (graphUnitNormalExtension a n g) := by
  have hd := hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient g) :=
    (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp hd
  exact (graphSlopeNormal_contDiff hn).comp (hgrad.comp
    ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma graphUnitNormalExtension_graph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g f : Plane → ℝ) (y : Plane) :
    graphUnitNormalExtension a n f (a+normalGraph n g y) = graphSlopeNormal n (gradient f y) := by
  unfold graphUnitNormalExtension
  rw [add_sub_cancel_left,normalGraph, map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]

lemma graphUnitNormalExtension_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {x : Cover}
    (hc : ContinuousAt (fderiv ℝ g) (normalPlaneCoordinates n (x-a))) :
    Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) x)
      atTop (𝓝 (graphUnitNormalExtension a n g x)) :=
  ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp (graphSmooth_gradient_tendsto hg hc)

lemma graphAreaVector_inner_unit {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ⟪graphAreaVector n g y,graphSlopeNormal n (gradient g y)⟫ = ‖graphAreaVector n g y‖ := by
  have hh : 0 < ‖graphAreaVector n g y‖ := lt_of_lt_of_le (by norm_num) (graphSlopeVector_norm_ge hn _)
  rw [graphSlopeNormal,inner_smul_right,show n-normalPlaneEmbedding n (gradient g y)=graphAreaVector n g y from rfl,
    real_inner_self_eq_norm_sq]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graph_area_trace_mollified_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφ : Continuous φ) (hsφ : HasCompactSupport φ)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφ0 : ∀ x, 0 ≤ φ x) :
    Tendsto (fun i ↦ ∫ y : Plane, φ (a+normalGraph n g y)*
      ⟪graphAreaVector n g y,graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g) (a+normalGraph n g y)⟫)
      atTop (𝓝 (∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
  have hi := graph_weighted_integrable a hn hg.continuous hφ hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  apply tendsto_integral_of_dominated_convergence
    (fun y ↦ φ (a+normalGraph n g y)*‖graphAreaVector n g y‖) ?_ hi
  · intro i
    filter_upwards [] with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    apply mul_le_mul_of_nonneg_left _ (hφ0 _)
    exact (norm_inner_le_norm _ _).trans_eq (by rw [graphUnitNormalExtension_unit a hn,mul_one])
  · filter_upwards [] with y
    by_cases hy : y ∈ Metric.closedBall (0 : Plane) R
    · have ht : Tendsto (fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
          (a+normalGraph n g y)) atTop (𝓝 (graphSlopeNormal n (gradient g y))) := by
        simp only [graphUnitNormalExtension_graph a hn]
        exact ((graphSlopeNormal_contDiff hn).continuous.tendsto _).comp
          (graphSmooth_gradient_tendsto hg (hc y hy))
      simpa only [graphAreaVector_inner_unit hn] using ((show Tendsto (fun _ : ℕ ↦ graphAreaVector n g y) atTop
        (𝓝 (graphAreaVector n g y)) from tendsto_const_nhds).inner ht).const_mul (φ (a+normalGraph n g y))
    · simp only [graph_trace_zero_outside hn hφR _ hy,zero_mul]
      exact tendsto_const_nhds
  · intro i
    exact (graph_weighted_continuous a hn hg.continuous hφ hφR (fun y hy ↦
      (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous
          (graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)).continuous).continuousAt)).aestronglyMeasurable

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_norm_le (n x : Cover) : ‖normalPlaneCoordinates n x‖ ≤ ‖x‖ := by
  simpa only [map_zero,dist_zero_right,NNReal.coe_one,one_mul] using
    (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0

lemma graph_weighted_normal_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    {φ : Cover → ℝ} (hφR : tsupport φ ⊆ Metric.closedBall a R) (z : BlowupNormalBundle) :
    Tendsto (fun i ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n
      (graphSmooth (graphMollifier i) g) z.1⟫) atTop
      (𝓝 (φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)) := by
  by_cases hz : z.1 ∈ tsupport φ
  · have hcoord : normalPlaneCoordinates n (z.1-a) ∈ Metric.closedBall (0 : Plane) R := by
      simp only [Metric.mem_closedBall,dist_zero_right]
      exact (normalPlaneCoordinates_norm_le n _).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hφR hz)
    exact ((show Tendsto (fun _ : ℕ ↦ (z.2 : Cover)) atTop (𝓝 (z.2 : Cover)) from
      tendsto_const_nhds).inner (graphUnitNormalExtension_tendsto a hn hg (hc _ hcoord))).const_mul _
  · simp only [image_eq_zero_of_notMem_tsupport hz,zero_mul]
    exact tendsto_const_nhds

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalCoverMap
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

lemma continuous_normalCoverMap : Continuous normalCoverMap := by
  exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

lemma normalCoverMeasure_integral {μ : FiniteMeasure NormalBundle} {f : BlowupNormalBundle → ℝ}
    (hf : Continuous f) :
    (∫ z, f z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, f (normalCoverMap z) ∂(μ : Measure NormalBundle) := by
  rw [normalCoverMeasure,FiniteMeasure.toMeasure_map,
    integral_map continuous_normalCoverMap.measurable.aemeasurable hf.aestronglyMeasurable]

lemma normalMeasure_cutoff_saturation {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) (O : Set Cover) : HasCutoffSaturation (normalCoverMeasure μ) O := by
  intro φ hφ hsφ hs hb C hC
  have hemass : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z, φ (z.1 : Cover) ∂(μ : Measure NormalBundle) := by
    have hz : ∀ z : BlowupNormalBundle, z ∉ {z : BlowupNormalBundle | z.1 ∈ O} → φ z.1=0 :=
      fun z hz ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact normalCoverMeasure_integral (hφ.continuous.comp continuous_fst)
  rw [hemass]
  apply normalMeasure_weighted_saturation hμ
    ⟨fun z ↦ φ (z.1 : Cover),hφ.continuous.comp (continuous_subtype_val.comp continuous_fst)⟩
  intro F hF
  have hFc : Continuous F := hF.1.continuous
  have heflux : (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1*⟪(z.2 : Cover),F z.1⟫
      ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun (z : BlowupNormalBundle) hz ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h)),zero_mul])]
    exact normalCoverMeasure_integral (by fun_prop)
  change (∫ z : NormalBundle, φ (z.1 : Cover)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle)) ≤ C
  rw [← heflux]
  exact hC F hF.1 hF.2.2

lemma normalCoverMeasure_local_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0<x i ∧ x i<1}) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(normalCoverMeasure μ : Measure BlowupNormalBundle)) =
      ∫ x in quotientMap ⁻¹' E, divergence F x := by
  rw [normalCoverMeasure_integral (by fun_prop)]
  change (∫ z : NormalBundle, ⟪(z.2 : Cover), F (z.1 : Cover)⟫ ∂(μ : Measure NormalBundle)) = _
  rw [normalMeasure_local_flux hE hμ hF hc hs,← integral_indicator (hE.preimage measurable_quotientMap)]
  congr 1
  funext x
  classical
  by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_weighted_mass {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ O}, φ z.1 ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb z.1).1]; exact (hφb z.1).2)
  have hiArea := graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
    (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).norm)
  have hiF (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      Integrable (fun z : BlowupNormalBundle ↦ φ z.1*⟪(z.2 : Cover),F z.1⟫) μ := by
    simpa only [mul_comm] using hiφ.bdd_mul
      (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),F z.1⟫) from by fun_prop).aestronglyMeasurable
      (ae_of_all μ fun z ↦ blowup_test_inner_bound hnF z)
  have hfield (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hnF : ∀ x, ‖F x‖ ≤ 1) :
      (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) ≤
        ∫ y : Plane, φ (a+normalGraph n g y)*‖graphAreaVector n g y‖ := by
    rw [show (∫ z, φ z.1*⟪(z.2 : Cover),F z.1⟫ ∂μ) = _ from
      blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (graph_weighted_integrable a hn hg.continuous hφ.continuous hsφ hφR
      (fun y hy ↦ (graphAreaVector_continuousAt n (hc y hy)).inner
        (graph_trace_continuous a n hg.continuous hF.continuous).continuousAt)) hiArea
    intro y
    apply mul_le_mul_of_nonneg_left _ (hφb _).1
    exact (real_inner_le_norm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hnF _))
  refine le_antisymm ?_ ?_
  · exact hsat φ hφ hsφ hφO hφb _ hfield
  · apply le_of_tendsto (graph_area_trace_mollified_normal_tendsto a hn hg hc
      hφ.continuous hsφ hφR (fun x ↦ (hφb x).1))
    apply Eventually.of_forall
    intro i
    let F := graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
    have hnF (x : Cover) : ‖F x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
    rw [← blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb hF hnF]
    apply integral_mono (hiF F hF hnF) hiφ
    intro z
    apply mul_le_of_le_one_right (hφb _).1
    exact (real_inner_le_norm (z.2 : Cover) (F z.1)).trans (by rw [z.2.property,one_mul]; exact hnF _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cutoff_graph_patch_normal_ae {A O U : Set Cover} (hA : MeasurableSet A)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {R : ℝ} (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hsat : HasCutoffSaturation ν O)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ O)
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O},
      0 < φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  let μ := (ν : Measure BlowupNormalBundle).restrict {z | z.1 ∈ O}
  let F : ℕ → Cover → Cover := fun i ↦ graphUnitNormalExtension a n (graphSmooth (graphMollifier i) g)
  let f : ℕ → BlowupNormalBundle → ℝ := fun i z ↦ φ z.1*⟪(z.2 : Cover),F i z.1⟫
  let f₀ : BlowupNormalBundle → ℝ := fun z ↦ φ z.1*⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫
  have hF (i) : ContDiff ℝ (⊤ : ℕ∞) (F i) := graphUnitNormalExtension_contDiff a hn (graphSmooth_contDiff _ hg)
  have hFn (i) (x) : ‖F i x‖ ≤ 1 := (graphUnitNormalExtension_unit a hn _ x).le
  have hf (i) : AEStronglyMeasurable (f i) μ :=
    (show Continuous (f i) from (hφ.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd |>.inner ((hF i).continuous.comp continuous_fst))).aestronglyMeasurable
  have ht : ∀ᵐ z ∂μ, Tendsto (fun i ↦ f i z) atTop (𝓝 (f₀ z)) :=
    ae_of_all μ (graph_weighted_normal_tendsto a hn hg hc hφR)
  have hb (i) (z : BlowupNormalBundle) : ‖f i z‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound (hFn i) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb₀ (z : BlowupNormalBundle) : ‖f₀ z‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφb _).1]
    exact (mul_le_mul (hφb _).2 (blowup_test_inner_bound
      (fun x ↦ (graphUnitNormalExtension_unit a hn _ x).le) z) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hi₀ : Integrable f₀ μ := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop hf ht) 1 (ae_of_all μ hb₀)
  have hilim : Tendsto (fun i ↦ ∫ z, f i z ∂μ) atTop (𝓝 (∫ z, f₀ z ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ (1:ℝ)) hf
      (integrable_const 1) (fun i ↦ ae_of_all μ (hb i)) ht
  have heint : (∫ z, f₀ z ∂μ) = ∫ z, φ z.1 ∂μ := by
    apply tendsto_nhds_unique hilim
    rw [show (∫ z, φ z.1 ∂μ) = _ from
      cutoff_graph_patch_weighted_mass hA a hn hg hc hgraph hsat hflux hφ hsφ hφU hφO hφR hφb]
    have hh := graph_area_trace_mollified_normal_tendsto a hn hg hc hφ.continuous hsφ hφR
      (fun x ↦ (hφb x).1)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact blowup_graph_patch_weighted_flux hA a hn hg hc hgraph hflux hφ hsφ hφU hφO hφR hφb (hF i) (hFn i)
  have hiφ : Integrable (fun z : BlowupNormalBundle ↦ φ z.1) μ :=
    Integrable.of_bound (hφ.continuous.comp continuous_fst).aestronglyMeasurable 1
      (ae_of_all μ fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (hφb _).1]; exact (hφb _).2)
  have hinon (z : BlowupNormalBundle) : 0 ≤ φ z.1-f₀ z := by
    have hh : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ ≤ 1 := by
      exact (real_inner_le_norm _ _).trans_eq (by rw [z.2.property,graphUnitNormalExtension_unit a hn,one_mul])
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hφb _).1 hh)
  have hezero : (∫ z, (φ z.1-f₀ z) ∂μ)=0 := by rw [integral_sub hiφ hi₀,heint,sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ hinon) (hiφ.sub hi₀)).mp hezero
  filter_upwards [hae] with z hz
  intro hzφ
  have hi : ⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫ = 1 := by
    have hh : φ z.1*(1-⟪(z.2 : Cover),graphUnitNormalExtension a n g z.1⟫)=0 := by
      simpa only [mul_sub,mul_one,f₀,Pi.zero_apply] using hz
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hzφ.ne')).symm
  exact (inner_eq_one_iff_of_norm_eq_one z.2.property (graphUnitNormalExtension_unit a hn g z.1)).mp hi

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ConeSlopeReciprocalArea
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

lemma graph_superlevel_compl_ae {A U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} (hg : Continuous g)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ A ↔ graphHeightExtension a n g x < ⟪n,x-a⟫)) :
    ∀ᵐ x : Cover ∂volume, x ∈ U → (x ∈ Aᶜ ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x) := by
  have hnz : ∀ᵐ x : Cover ∂volume, ⟪n,x-a⟫ ≠ graphHeightExtension a n g x := by
    rw [ae_iff]
    simpa only [not_not] using graph_trace_volume_zero a hn hg
  filter_upwards [hgraph,hnz] with x hx hne hU
  rw [mem_compl_iff,hx hU,not_lt]
  exact ⟨fun h ↦ lt_of_le_of_ne h hne,le_of_lt⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
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

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

lemma normalGraph_coordinates_eq_iff {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (x : Cover) :
    normalGraph n g (normalPlaneCoordinates n x)=x ↔ g (normalPlaneCoordinates n x)=⟪n,x⟫ := by
  constructor
  · intro hh
    simpa only [normalGraph_inner hn] using congrArg (fun v : Cover ↦ ⟪n,v⟫) hh
  · intro hh
    rw [normalGraph,hh,normalPlaneCoordinates_reconstruct hn x]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
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

lemma volumeSupport_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    volumeSupport ((fun z ↦ z+b) ⁻¹' E) = (fun z ↦ z+b) ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : ((fun z ↦ z+b) ⁻¹' E) ∩ Metric.ball a r =
      (fun z ↦ z+b) ⁻¹' (E ∩ Metric.ball (a+b) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,dist_add_right]
  rw [he,Measure.real_def,Measure.real_def,
    volume_translation (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    openRepresentative ((fun z ↦ z+b) ⁻¹' E) =
      (fun z ↦ z+b) ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_translation hE.compl]
  rfl

lemma frontier_openRepresentative_translation {E : Set Torus} (hE : MeasurableSet E) (b : Torus) :
    frontier (openRepresentative ((fun z ↦ z+b) ⁻¹' E)) =
      (fun z ↦ z+b) ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_translation hE b]
  exact (Homeomorph.addRight b).preimage_frontier _ |>.symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
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

lemma contDiff_local_vector_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {η : Plane → ℝ} {S : Set Plane} {n : WithTop ℕ∞}
    (hS : IsOpen S) (hf : ContDiffOn ℝ n f S) (hη : ContDiff ℝ n η)
    (hs : tsupport η⊆S) : ContDiff ℝ n (fun y ↦ η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.contDiffAt.smul ((hf y (hs hy)).contDiffAt (hS.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
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

theorem normalMeasure_graph_normal_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y∈Metric.closedBall (0 : Plane) R,ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume,x∈U →
      (quotientMap x∈E ↔ ⟪n,x-a⟫<graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ⊆U) (hφO : tsupport φ⊆{x | ∀ i,0<x i ∧ x i<1})
    (hφR : tsupport φ⊆Metric.closedBall a R) (hφb : ∀ x,φ x∈Icc 0 1) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
      (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1})
      (_hb : ∀ x,‖F x‖≤1) := normalCoverMeasure_local_flux hE hμ hF hs hO
  have h := cutoff_graph_patch_normal_ae (hE.preimage measurable_quotientMap) a hn hg hc
    hgraph (normalMeasure_cutoff_saturation hμ _) hflux hφ hsφ hφU hφO hφR hφb
  have hO : MeasurableSet {z : BlowupNormalBundle | ∀ i,0<z.1 i ∧ z.1 i<1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun z : BlowupNormalBundle ↦ z.1 i) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter
      (measurableSet_lt hm measurable_const)
  have h' : ∀ᵐ z ∂(normalCoverMeasure μ : Measure BlowupNormalBundle),
      0<φ z.1 → (z.2 : Cover)=graphUnitNormalExtension a n g z.1 := by
    have hh := (ae_restrict_iff' hO).mp h
    filter_upwards [hh] with z hz hpos
    exact hz (hφO (subset_tsupport _ (show φ z.1≠0 from hpos.ne'))) hpos
  have hm : (normalCoverMeasure μ : Measure BlowupNormalBundle)=
      Measure.map normalCoverMap (μ : Measure NormalBundle) := FiniteMeasure.toMeasure_map μ normalCoverMap
  rw [hm] at h'
  exact ae_of_ae_map continuous_normalCoverMap.measurable.aemeasurable h'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma translateNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (a : Cover) (z : NormalBundle) :
    F (translateNormal a z).1=F ((z.1 : Cover)-a) := by
  change F (representative (quotientMap z.1-quotientMap a))=F ((z.1 : Cover)-a)
  rw [← quotientMap_sub]
  exact periodic_representative hp _

theorem isNormalMeasure_translation {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (a : Cover) :
    IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) (μ.map (translateNormal a)) := by
  constructor
  · have hm : ((μ.map (translateNormal a)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_translateNormal a)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_translation_measurable hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (translateNormal a) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_translateNormal a).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_translation hF a hE]
    have hG : AdmissibleField (fun x ↦ F (x-a)) := by
      simpa only [sub_eq_add_neg] using admissible_translate hF (-a)
    rw [← hμ.2 _ hG]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      change ⟪(z.2 : Cover),F (translateNormal a z).1⟫=⟪(z.2 : Cover),F ((z.1 : Cover)-a)⟫
      rw [translateNormal_periodic_eval hF.2.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smooth_graph_extension {g : Plane → ℝ} {R : ℝ} (hR : 0<R)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball 0 R)) :
    ∃ f : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) f ∧ EqOn f g (Metric.ball 0 (R/2)) := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  refine ⟨fun y ↦ b y*g y,?_,?_⟩
  · exact contDiff_local_vector_cutoff Metric.isOpen_ball hg b.contDiff hs
  · intro y hy
    change b y*g y=g y
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
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

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

theorem actual_centered_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (cubeCenter+normalGraph n f y)=
        σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (cubeCenter+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  obtain ⟨n,g,r,H,hn,hr,hg,hg0,hgc,hi,hcover,_,_⟩ :=
    isMinimizerAt_smooth_CMC hV hE hmin (quotientMap cubeCenter) hcenter
  obtain ⟨f,hf,hfg⟩ := smooth_graph_extension hr hgc
  have hcover' (x : Cover) (hx : x∈Metric.ball (0 : Cover) (r/2)) :
      quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
        normalGraph n g (normalPlaneCoordinates n x)=x := by
    rw [quotientMap_add]
    exact hcover x ((Metric.ball_subset_ball (by linarith)) hx)
  obtain ⟨R,ρ,U,hRr,_,_,_,hR,hρ,hgC,hU,hρU,hUR,hUO,_,hphase⟩ :=
    actual_centered_graph_phase_patch hV hE hmin hcenter hn (by linarith : 0 < r/2)
      hg hg0 ((hgc.of_le (by simp)).mono (Metric.ball_subset_ball (by linarith))) hcover'
  let φ := radialHeightCutoff cubeCenter ρ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := radialDensityWeight_contDiff _ _ _
  have hsφ : HasCompactSupport φ := radialDensityWeight_hasCompactSupport (by positivity) (by positivity)
  have hφs : tsupport φ⊆Metric.closedBall cubeCenter (2*ρ) :=
    radialDensityWeight_tsupport (by positivity) (by positivity)
  have hφU := hφs.trans hρU
  have hφO := hφU.trans hUO
  have hφR := hφU.trans (hUR.trans Metric.ball_subset_closedBall)
  have hφb (x : Cover) : φ x∈Icc 0 1 :=
    ⟨radialDensityWeight_nonneg _ _ _ _,radialDensityWeight_le_one _ _ _ _⟩
  have hdc (y : Plane) (hy : y∈Metric.closedBall (0 : Plane) R) : ContinuousAt (fderiv ℝ g) y :=
    (hgC y hy).continuousAt_fderiv (by norm_num)
  have hNfg (x : Cover) (hx : x∈tsupport φ) :
      graphUnitNormalExtension cubeCenter n f x=graphUnitNormalExtension cubeCenter n g x := by
    have hpp : normalPlaneCoordinates n (x-cubeCenter)∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right]
      have hnorm : ‖x-cubeCenter‖<R := by
        simpa only [Metric.mem_ball,dist_eq_norm] using hUR (hφU hx)
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt (hnorm.trans hRr)
    have he : f=ᶠ[𝓝 (normalPlaneCoordinates n (x-cubeCenter))]g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hpp] with y hy
      exact hfg hy
    simp only [graphUnitNormalExtension,gradient,he.fderiv_eq]
  have hsign : ∃ σ : ℝ,(σ=1 ∨ σ= -1) ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
        σ • graphUnitNormalExtension cubeCenter n f z.1=(z.2 : Cover) := by
    rcases hphase with hphase|hphase
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (quotientMap x∈E ↔ ⟪n,x-cubeCenter⟫<graphHeightExtension cubeCenter n g x) := by
        simpa only [graphSignedHeight,sub_neg] using hphase
      refine ⟨1,Or.inl rfl,?_⟩
      filter_upwards [normalMeasure_graph_normal_ae hE hμ cubeCenter hn hg hdc hh
        hφ hsφ hφU hφO hφR hφb] with z hz hpos
      rw [one_smul,hNfg _ (subset_tsupport _ hpos.ne')]
      exact (hz hpos).symm
    · have hh : ∀ᵐ x : Cover ∂volume,x∈U →
          (x∈quotientMap ⁻¹' E ↔ graphHeightExtension cubeCenter n g x<⟪n,x-cubeCenter⟫) := by
        simpa only [graphSignedHeight,sub_pos,mem_preimage] using hphase
      have hh' := graph_superlevel_compl_ae cubeCenter hn hg.continuous hh
      have hh'' := normalMeasure_graph_normal_ae hE.compl (isNormalMeasure_compl hE hμ)
        cubeCenter hn hg hdc hh' hφ hsφ hφU hφO hφR hφb
      have hm : ∀ᵐ z ∂(μ : Measure NormalBundle),0<φ z.1 →
          -(z.2 : Cover)=graphUnitNormalExtension cubeCenter n g z.1 :=
        ae_of_ae_map continuous_reverseNormal.measurable.aemeasurable hh''
      refine ⟨-1,Or.inr rfl,?_⟩
      filter_upwards [hm] with z hz hpos
      rw [neg_one_smul,hNfg _ (subset_tsupport _ hpos.ne'),← hz hpos,neg_neg]
  obtain ⟨σ,hσ,hσae⟩ := hsign
  let F : Cover → Cover := fun x ↦ φ x • (σ • graphUnitNormalExtension cubeCenter n f x)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hφ.smul
    ((graphUnitNormalExtension_contDiff _ hn hf).const_smul σ)
  have hsF : HasCompactSupport F := hsφ.smul_right
  have hFO : tsupport F⊆{x | ∀ i,0<x i ∧ x i<1} :=
    (tsupport_smul_subset_left _ _).trans hφO
  have he := latticePeriodize_eventuallyEq hsF hFO
    (show ∀ i,0 ≤ cubeCenter i ∧ cubeCenter i≤1 by intro i; norm_num [cubeCenter])
  have heφ := latticePeriodize_eventuallyEq hsφ hφO
    (show ∀ coordinate,0 ≤ cubeCenter coordinate ∧ cubeCenter coordinate≤1 by
      intro coordinate
      norm_num [cubeCenter])
  have hz : ∀ᵐ z ∂(μ : Measure NormalBundle),
      latticePeriodize φ z.1 • N z.1=latticePeriodize F z.1 := by
    filter_upwards [hae,hσae] with z hz hloc
    rw [(latticePeriodize_eventuallyEq hsφ hφO (compactCell_coordinates z.1)).eq_of_nhds,
      (latticePeriodize_eventuallyEq hsF hFO (compactCell_coordinates z.1)).eq_of_nhds]
    change φ z.1 • N z.1=φ z.1 • (σ • graphUnitNormalExtension cubeCenter n f z.1)
    by_cases hpos : 0<φ z.1
    · rw [hz,hloc hpos]
    · have hzφ : φ z.1=0 := le_antisymm (le_of_not_gt hpos) (hφb z.1).1
      simp only [hzφ,zero_smul]
  have hb (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
      latticePeriodize φ x • N x=latticePeriodize F x :=
    isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      ((latticePeriodize_contDiff hφ hsφ).continuous.smul hN.continuous)
      (latticePeriodize_contDiff hF hsF).continuous
      (fun shift point ↦ congrArg₂ (· • ·)
        (latticePeriodize_periodic φ shift point) (hp shift point))
      (latticePeriodize_periodic F) hz x hx
  have hf0 : f 0=0 := (hfg (by simpa using (half_pos hr))).trans hg0
  have ht : Tendsto (fun y ↦ cubeCenter+normalGraph n f y) (𝓝 (0 : Plane)) (𝓝 cubeCenter) := by
    have hc : Continuous (fun y ↦ cubeCenter+normalGraph n f y) :=
      continuous_const.add ((normalPlaneLinearIsometry n).continuous.add
        (hf.continuous.smul continuous_const))
    have hz : cubeCenter+normalGraph n f 0=cubeCenter := by
      simp only [normalGraph,hf0,zero_smul,add_zero]
      change cubeCenter+(normalPlaneLinearIsometry n) 0=cubeCenter
      rw [map_zero,add_zero]
    simpa only [ContinuousAt,hz] using hc.continuousAt (x := 0)
  have hone : ∀ᶠ x in 𝓝 cubeCenter,φ x=1 := by
    filter_upwards [Metric.ball_mem_nhds cubeCenter hρ] with x hx
    exact radialHeightCutoff_one hρ (Metric.ball_subset_closedBall hx)
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  ·
    filter_upwards [ht.eventually he,ht.eventually heφ,ht.eventually hone,
      Metric.ball_mem_nhds (0 : Plane) (half_pos hr)] with y hey heφy hoy hy
    have hgraph : normalGraph n f y=normalGraph n g y := by simp only [normalGraph,hfg hy]
    have hby : quotientMap (cubeCenter+normalGraph n f y)∈frontier (openRepresentative E) := by
      rw [quotientMap_add,hgraph]
      exact hi y ((Metric.ball_subset_ball (by linarith)) hy)
    have hnormal := hb _ hby
    rw [heφy,hey] at hnormal
    change φ (cubeCenter+normalGraph n f y) • N (cubeCenter+normalGraph n f y)=
      φ (cubeCenter+normalGraph n f y) • (σ • graphUnitNormalExtension cubeCenter n f
        (cubeCenter+normalGraph n f y)) at hnormal
    simp only [hoy,one_smul,graphUnitNormalExtension_graph cubeCenter hn f f y] at hnormal
    exact ⟨hnormal,hby⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Cover) (half_pos hr)] with v hv
    have hpv : normalPlaneCoordinates n v∈Metric.ball (0 : Plane) (r/2) := by
      rw [Metric.mem_ball,dist_zero_right] at hv ⊢
      exact (normalPlaneCoordinates_norm_le _ _).trans_lt hv
    rw [hcover' v hv]
    simp only [normalGraph,hfg hpv]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_normal_graph_chart {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (f : Plane → ℝ) (σ : ℝ),‖n‖=1 ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ f 0=0 ∧ (σ=1 ∨ σ= -1) ∧
      (∀ᶠ y in 𝓝 (0 : Plane),N (x+normalGraph n f y)=σ • graphSlopeNormal n (gradient f y) ∧
        quotientMap (x+normalGraph n f y)∈frontier (openRepresentative E)) ∧
      ∀ᶠ v in 𝓝 (0 : Cover),quotientMap (x+v)∈frontier (openRepresentative E) ↔
        normalGraph n f (normalPlaneCoordinates n v)=v := by
  let a := x-cubeCenter
  let E' := (fun z : Torus ↦ z+quotientMap a) ⁻¹' E
  have hE' : MeasurableSet E' := (continuous_add_const _).measurable hE
  have hmin' : IsMinimizerAt V E' := isMinimizerAt_translation hmin _
  have hc : quotientMap cubeCenter∈frontier (openRepresentative E') := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap cubeCenter+quotientMap a∈frontier (openRepresentative E)
    rw [← quotientMap_add]
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [a]
    congr 1
    abel
  let N' : Cover → Cover := fun y ↦ N (y+a)
  have hN' : ContDiff ℝ (⊤ : ℕ∞) N' := hN.comp (contDiff_id.add contDiff_const)
  have hp' : ∀ m y,N' (y+latticeVector m)=N' y := by
    intro m y
    change N ((y+latticeVector m)+a)=N (y+a)
    rw [add_right_comm,hp]
  have hae' : ∀ᵐ z ∂((μ.map (translateNormal a)) : Measure NormalBundle),N' z.1=(z.2 : Cover) := by
    change ∀ᵐ z ∂Measure.map (translateNormal a) (μ : Measure NormalBundle),N' z.1=(z.2 : Cover)
    apply (ae_map_iff (measurable_translateNormal a).aemeasurable
      (isClosed_eq (hN'.continuous.comp normalEmbedding_continuous.fst) continuous_normalUnit).measurableSet).mpr
    filter_upwards [hae] with z hz
    change N' (translateNormal a z).1=(z.2 : Cover)
    rw [translateNormal_periodic_eval hp']
    change N (((z.1 : Cover)-a)+a)=(z.2 : Cover)
    simpa only [sub_add_cancel] using hz
  obtain ⟨n,f,σ,hn,hf,hf0,hσ,hm,hcov⟩ := actual_centered_normal_graph_chart hV hE' hmin' hc
    (isNormalMeasure_translation hE hμ a) hN' hp' hae'
  have ht (v : Cover) : (cubeCenter+v)+a=x+v := by dsimp [a]; abel
  have htrans (v : Cover) : quotientMap (cubeCenter+v)∈frontier (openRepresentative E') ↔
      quotientMap (x+v)∈frontier (openRepresentative E) := by
    rw [frontier_openRepresentative_translation hE]
    change quotientMap (cubeCenter+v)+quotientMap a∈frontier (openRepresentative E) ↔ _
    rw [← quotientMap_add,ht]
  refine ⟨n,f,σ,hn,hf,hf0,hσ,?_,?_⟩
  · filter_upwards [hm] with y hy
    refine ⟨?_,(htrans _).mp hy.2⟩
    have hh := hy.1
    change N ((cubeCenter+normalGraph n f y)+a)=_ at hh
    rwa [ht] at hh
  · filter_upwards [hcov] with v hv
    exact (htrans v).symm.trans hv

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GraphNormalExtensionDivergence
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

lemma localRadialSquared_lt_iff (a : Torus) (x : Cover) {r : ℝ}
    (hr : 0 ≤ r) (hs : r≤1/4) :
    localRadialSquared a x < r^2 ↔ quotientMap x∈Metric.ball a r := by
  have he := periodic_representative (localRadialSquared_periodic a) x
  rw [← he]
  change quotientMap x∈sublevelRegion (localRadialSquared a) (r^2) ↔ _
  rw [sublevelRegion_localRadialSquared a hr hs]

theorem exists_periodic_local_cutoff (a : Torus) {U : Set Torus}
    (hU : IsOpen U) (ha : a∈U) :
    ∃ φ : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ m x,φ (x+latticeVector m)=φ x) ∧ (∀ x,φ x∈Icc 0 1) ∧
      (∃ W : Set Torus,IsOpen W ∧ a∈W ∧
        ∀ x,quotientMap x∈W → ∀ᶠ y in 𝓝 x,φ y=1) ∧
      ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0 := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU a ha
  let r := min (ε/4) (1/8 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrsmall : 2*r≤1/4 := by dsimp [r]; linarith [min_le_right (ε/4) (1/8 : ℝ)]
  have hrε : 2*r<ε := by dsimp [r]; linarith [min_le_left (ε/4) (1/8 : ℝ)]
  let q := localRadialSquared a
  let φ : Cover → ℝ := fun x ↦ Real.smoothTransition ((r^2-q x)/(r^2/2))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := localRadialSquared_contDiff a
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const _)
  have hden : 0 < r^2/2 := by positivity
  refine ⟨φ,hφ,?_,?_,?_,?_⟩
  · intro m x
    simp only [φ,q,localRadialSquared_periodic]
  · intro x
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · refine ⟨Metric.ball a (r/2),Metric.isOpen_ball,Metric.mem_ball_self (by positivity),?_⟩
    intro x hx
    have hxq : q x<(r/2)^2 := (localRadialSquared_lt_iff a x (by positivity) (by linarith)).mpr hx
    have hn : ∀ᶠ y in 𝓝 x,q y < r^2/2 := hq.continuous.continuousAt.eventually_lt_const (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  · intro x hx
    have hnot : quotientMap x∉Metric.ball a (2*r) := fun hh ↦ hx (hεU (Metric.ball_subset_ball hrε.le hh))
    have hxq : (2*r)^2≤q x := le_of_not_gt (fun hh ↦ hnot ((localRadialSquared_lt_iff a x (by positivity) hrsmall).mp hh))
    have hn : ∀ᶠ y in 𝓝 x,r^2<q y := hq.continuous.continuousAt.eventually_const_lt (by nlinarith [sq_pos_of_pos hr])
    filter_upwards [hn] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_normal_base {F : Cover → ℝ} (hF : Continuous F)
    (μ : FiniteMeasure NormalBundle) :
    Integrable (fun z : NormalBundle ↦ F z.1) (μ : Measure NormalBundle) :=
  (hF.comp normalEmbedding_continuous.fst).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_TorusCoordinatePermute
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

lemma openRepresentative_congr_ae {E F : Set Torus} (h : E =ᵐ[torusVolume] F) :
    openRepresentative E=openRepresentative F := by
  unfold openRepresentative
  apply congrArg (fun A : Set Torus ↦ Aᶜ)
  apply volumeSupport_congr_ae
  filter_upwards [h] with z hz
  exact congrArg Not hz

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateReflection
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma coordinateReflection_continuous (i : Fin 3) : Continuous (coordinateReflection i) :=
  (coordinateReflection_isometry i).continuous

lemma coordinateReflection_measurePreserving (i : Fin 3) :
    MeasurePreserving (coordinateReflection i) torusVolume torusVolume := by
  have h (j : Fin 3) : MeasurePreserving
      (fun a : AddCircle (1 : ℝ) => if j=i then -a else a) volume volume := by
    by_cases hj : j=i
    · simpa only [ite_eq_left hj] using (Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ))))
    · simp only [ite_eq_right hj]
      constructor
      · exact measurable_id
      · exact Measure.map_id
  exact product_to_torus_measurePreserving.comp ((volume_preserving_pi h).comp torus_to_product_measurePreserving)

lemma quotientMap_coordinateReflection (i : Fin 3) (x : Cover) :
    quotientMap (coverCoordinateReflection i x)=coordinateReflection i (quotientMap x) := by
  ext j
  by_cases h : j=i <;> simp [quotientMap,h]

lemma coverCoordinateReflection_lattice (i : Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinateReflection i (latticeVector m)=latticeVector (fun j => if j=i then -m j else m j) := by
  ext j
  by_cases h : j=i <;> simp [latticeVector,h]

lemma coverCoordinateReflection_single (i j : Fin 3) :
    coverCoordinateReflection i (EuclideanSpace.single j 1)=
      (if j=i then (-1 : ℝ) else 1) • EuclideanSpace.single j 1 := by
  ext k
  by_cases h : j=i
  · subst j
    by_cases hk : k=i <;> simp [hk]
  · by_cases hk : k=j
    · subst k; simp [h]
    · by_cases hi : k=i <;> simp [h,hk,hi]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateReflectedField_contDiff (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinateReflectedField i F) :=
  (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinateReflection i).toContinuousLinearEquiv.contDiff)

lemma coordinateReflectedField_periodic (i : Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinateReflectedField i F (x+latticeVector n)=coordinateReflectedField i F x := by
  intro n x
  simp only [coordinateReflectedField,map_add,coverCoordinateReflection_lattice,hp]

lemma coordinateReflectedField_admissible (i : Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinateReflectedField i F) := by
  refine ⟨coordinateReflectedField_contDiff i hF.1,coordinateReflectedField_periodic i hF.2.1,?_⟩
  intro x
  simpa only [coordinateReflectedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinateReflection i x)

lemma coordinateReflectedField_divergence (i : Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinateReflectedField i F) x=divergence F (coverCoordinateReflection i x) := by
  have hd : HasFDerivAt (coordinateReflectedField i F)
      ((coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinateReflection i x)).comp
          (coverCoordinateReflection i).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinateReflection i).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinateReflection_single,map_smul,
    coverCoordinateReflection_apply,PiLp.smul_apply,smul_eq_mul]
  by_cases h : j=i <;> simp [h]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinateReflection (i : Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (coordinateReflection i ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinateReflectedField i F) x := by
  have hm := (coordinateReflection_continuous i).measurable
  have hr := coordinateReflectedField_admissible i hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinateReflectedField i F) (representative (coordinateReflection i z))) := by
    funext z
    rw [coordinateReflectedField_divergence i hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinateReflection i (representative (coordinateReflection i z))),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_involutive]
  rw [he]
  exact (coordinateReflection_measurePreserving i).setIntegral_preimage_emb
    (coordinateReflectionEquiv i).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinateReflectedField i F) (representative z)) E

lemma perimeter_coordinateReflection_le (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinateReflection i hF hE]
  exact le_iSup_of_le (coordinateReflectedField i F)
    (le_iSup_of_le (coordinateReflectedField_admissible i hF) le_rfl)

lemma perimeter_coordinateReflection_measurable (i : Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (coordinateReflection i ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinateReflection_le i hE)
  have hh := perimeter_coordinateReflection_le i ((coordinateReflection_continuous i).measurable hE)
  have he : coordinateReflection i ⁻¹' (coordinateReflection i ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinateSine_periodic (i : Fin 3) :
    ∀ n x,coordinateSine i (x+latticeVector n)=coordinateSine i x := by
  intro n x
  unfold coordinateSine
  simp only [PiLp.add_apply,latticeVector]
  rw [show 2*Real.pi*(x i+(n i : ℝ))=2*Real.pi*x i+(n i : ℝ)*(2*Real.pi) by ring,
    Real.sin_add_int_mul_two_pi]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceGraphBundleMeasure
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma mem_coordinateHalf_quotient (i : Fin 3) (a : ℝ) (x : Cover) :
    quotientMap x∈coordinateHalf i a ↔ Real.sin (2*Real.pi*(x i-a))<0 := by
  let q : Cover → ℝ := fun y => coordinateSine i (y-a • EuclideanSpace.single i 1)
  have hp : ∀ n y,q (y+latticeVector n)=q y := by
    intro n y
    dsimp [q]
    rw [show y+latticeVector n-a • EuclideanSpace.single i 1=
      (y-a • EuclideanSpace.single i 1)+latticeVector n by abel,coordinateSine_periodic]
  have he := periodic_representative hp x
  simp only [q,coordinateSine,PiLp.sub_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,
    smul_eq_mul,mul_one] at he
  change Real.sin (2*Real.pi*((representative (quotientMap x)) i-a))<0 ↔ _
  rw [he]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_CMCSecantSymbol
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

lemma normalGraph_zero {n : Cover} {f : Plane → ℝ} (hf0 : f 0=0) :
    normalGraph n f 0=0 := by
  change (normalPlaneLinearIsometry n) 0+f 0 • n=0
  simp [hf0]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_NormalMeasureCoordinateReflection
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma volumeSupport_local_mono {E F U : Set Torus} (hU : IsOpen U)
    (hEF : E∩U⊆F∩U) {a : Torus} (haU : a∈U) (haE : a∈volumeSupport E) :
    a∈volumeSupport F := by
  have hh := Measure.interior_inter_support (μ := torusVolume.restrict E) (s := U)
  rw [hU.interior_eq] at hh
  have hh' := hh ⟨haU,haE⟩
  have he : (torusVolume.restrict E).restrict U=torusVolume.restrict (E∩U) := by
    rw [Measure.restrict_restrict hU.measurableSet,inter_comm]
  rw [he] at hh'
  exact (Measure.support_mono (Measure.restrict_mono (hEF.trans inter_subset_left) le_rfl)) hh'

lemma volumeSupport_local_eq {E F U : Set Torus} (hU : IsOpen U) (hEF : E∩U=F∩U) :
    volumeSupport E∩U=volumeSupport F∩U := by
  ext a
  constructor
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.subset ha.2 ha.1,ha.2⟩
  · exact fun ha => ⟨volumeSupport_local_mono hU hEF.symm.subset ha.2 ha.1,ha.2⟩

lemma isMinimizerAt_frontier_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U) :
    frontier (openRepresentative E)∩U=frontier (openRepresentative F)∩U := by
  have hec : Eᶜ∩U=Fᶜ∩U := by
    ext a
    have hh := Set.ext_iff.mp he a
    simp only [mem_inter_iff,mem_compl_iff] at *
    tauto
  have hh := volumeSupport_local_eq hU he
  have hc := volumeSupport_local_eq hU hec
  rw [isMinimizerAt_frontier_openRepresentative hV hE hmE,
    isMinimizerAt_frontier_openRepresentative hW hF hmF]
  ext a
  have hh' := Set.ext_iff.mp hh a
  have hc' := Set.ext_iff.mp hc a
  simp only [mem_inter_iff] at *
  tauto

lemma local_region_flux_eq {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (he : E∩U=F∩U) {X : Cover → Cover}
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,X y=0) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence X x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,divergence X x := by
  classical
  rw [← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hE)),
    ← integral_indicator (measurableSet_fundamentalCube.inter (measurable_quotientMap hF))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hx : quotientMap x∈U
  · have hh := Set.ext_iff.mp he (quotientMap x)
    simp only [mem_inter_iff,hx,and_true] at hh
    simp only [Set.indicator_apply,mem_inter_iff,mem_preimage,hh]
  · have he0 : X=ᶠ[𝓝 x] (fun _ => 0) := hz x hx
    have hd : divergence X x=0 := by
      have hd0 : fderiv ℝ X x=0 := he0.fderiv_eq.trans (congrFun (fderiv_const (𝕜 := ℝ) (E := Cover) (c := (0 : Cover))) x)
      simp only [divergence,hd0,zero_apply,PiLp.zero_apply,Finset.sum_const_zero]
    simp only [Set.indicator_apply,hd,ite_self]

lemma local_region_weightedPerimeter_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {φ : Cover → ℝ} (hzero : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    weightedPerimeter E φ=weightedPerimeter F φ := by
  unfold weightedPerimeter
  congr 1
  funext X
  congr 1
  funext hX
  rw [local_region_flux_eq hE hF he (X := fun y => φ y • X y) (by
    intro x hx
    filter_upwards [hzero x hx] with y hy
    rw [hy,zero_smul])]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_region_weighted_mass_eq {E F U : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ m x,φ (x+latticeVector m)=φ x) (hn : ∀ x,0≤φ x)
    (hz : ∀ x,quotientMap x∉U → ∀ᶠ y in 𝓝 x,φ y=0) :
    (∫ z,φ z.1 ∂(μ : Measure NormalBundle))=∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
  have hh := local_region_weightedPerimeter_eq hE hF he hz
  rw [normalMeasure_weightedPerimeter hμ hφ hp hn,
    normalMeasure_weightedPerimeter hν hφ hp hn] at hh
  have hh' := congrArg ENNReal.toReal hh
  have hm0 : 0≤∫ z,φ z.1 ∂(μ : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  have hn0 : 0≤∫ z,φ z.1 ∂(ν : Measure NormalBundle) := integral_nonneg fun z => hn z.1
  simpa only [ENNReal.toReal_ofReal hm0,ENNReal.toReal_ofReal hn0] using hh'

theorem isMinimizerAt_normal_local_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : E∩U=F∩U)
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  obtain ⟨φ,hφ,hp,hb,⟨T,hT,hxT,hone⟩,hzero⟩ := exists_periodic_local_cutoff (quotientMap x) hU hx.2
  have hbound := isMinimizerAt_frontier_local_eq hV hW hE hF hmE hmF hU he
  have hxF : quotientMap x∈frontier (openRepresentative F) := (hbound ▸ hx).1
  have hunit (y : Cover) (hy : quotientMap y∈frontier (openRepresentative E)) : ‖N y‖=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.continuous.norm continuous_const
      (fun k y => by rw [hpN]) (fun _ _ => rfl) _ y hy
    filter_upwards [haN] with z hz
    rw [hz,z.2.property]
  have hmass := local_region_weighted_mass_eq hE hF he hμ hν hφ hp (fun y => (hb y).1) hzero
  have hX : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y • N y) := hφ.smul hN
  have hXp : ∀ k y,φ (y+latticeVector k) • N (y+latticeVector k)=φ y • N y :=
    fun k y => by rw [hp,hpN]
  have hflux : (∫ z,φ z.1*⟪(z.2 : Cover),N z.1⟫ ∂(ν : Measure NormalBundle))=
      ∫ z,φ z.1 ∂(ν : Measure NormalBundle) := by
    calc
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(ν : Measure NormalBundle) := by simp only [real_inner_smul_right]
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' F,divergence (fun y => φ y • N y) y := periodic_normal_flux hν hX hXp
      _ = ∫ y in fundamentalCube∩quotientMap ⁻¹' E,divergence (fun y => φ y • N y) y :=
        (local_region_flux_eq hE hF he (by intro y hy; filter_upwards [hzero y hy] with z hz; rw [hz,zero_smul])).symm
      _ = ∫ z,⟪(z.2 : Cover),φ z.1 • N z.1⟫ ∂(μ : Measure NormalBundle) := (periodic_normal_flux hμ hX hXp).symm
      _ = ∫ z,φ z.1 ∂(μ : Measure NormalBundle) := by
        apply integral_congr_ae
        filter_upwards [haN] with z hz
        rw [real_inner_smul_right,hz,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
      _ = _ := hmass
  have hbF := normalMeasure_frontier_ae (E := openRepresentative F) (isOpen_openRepresentative F).measurableSet
    (hν.congr_ae (isMinimizerAt_openRepresentative_ae hW hF hmF).symm)
  have hid : (fun z : NormalBundle => φ z.1*‖N z.1-M z.1‖^2) =ᵐ[(ν : Measure NormalBundle)]
      (fun z => 2*(φ z.1-φ z.1*⟪(z.2 : Cover),N z.1⟫)) := by
    filter_upwards [haM,hbF] with z hz hzF
    by_cases hp0 : φ z.1=0
    · simp only [hp0,zero_mul,sub_self,mul_zero]
    · have hzU : quotientMap z.1∈U := by
        by_contra hh
        exact hp0 (hzero z.1 hh).self_of_nhds
      have hzE : quotientMap z.1∈frontier (openRepresentative E) := (hbound.symm.subset ⟨hzF,hzU⟩).1
      rw [hz,norm_sub_sq_real,hunit z.1 hzE,z.2.property,real_inner_comm]
      ring
  have hiφ := integrable_normal_base hφ.continuous ν
  have hiX : Integrable (fun z : NormalBundle => φ z.1*⟪(z.2 : Cover),N z.1⟫) (ν : Measure NormalBundle) := by
    simpa only [normalTest,ContinuousMap.coe_mk,real_inner_smul_right] using
      (normalTest _ hX.continuous).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := integrable_normal_base
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) ν
  have hiz : (∫ z,φ z.1*‖N z.1-M z.1‖^2 ∂(ν : Measure NormalBundle))=0 := by
    rw [integral_congr_ae hid,integral_const_mul,integral_sub hiφ hiX,hflux,sub_self,mul_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun z : NormalBundle =>
    mul_nonneg (hb z.1).1 (sq_nonneg _)) hi).mp hiz
  have hxzero := isMinimizerAt_periodic_ae_eq_boundary hW hF hmF hν
    (hφ.continuous.mul ((hN.continuous.sub hM.continuous).norm.pow 2)) continuous_const
    (fun k y => by
      change φ (y+latticeVector k)*‖N (y+latticeVector k)-M (y+latticeVector k)‖^2=φ y*‖N y-M y‖^2
      rw [hp,hpN,hpM]) (fun _ _ => rfl) hae x hxF
  change φ x*‖N x-M x‖^2=0 at hxzero
  rw [(hone x hxT).self_of_nhds,one_mul] at hxzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hxzero))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_replace_ae {E F U : Set Torus} (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus)) :
    ((F\U)∪(E∩U) : Set Torus) =ᵐ[torusVolume] F := by
  filter_upwards [he] with a ha
  have hh : (a∈E ∧ a∈U) ↔ (a∈F ∧ a∈U) := Iff.of_eq ha
  change (a∈(F\U)∪(E∩U))=(a∈F)
  apply propext
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma local_replace_inter (E F U : Set Torus) : ((F\U)∪(E∩U))∩U=E∩U := by
  ext a
  simp only [mem_union,Set.mem_sdiff,mem_inter_iff]
  tauto

lemma isMinimizerAt_normal_local_ae_eq {V W : ℝ} (hV : V∈Ioo 0 1) (hW : W∈Ioo 0 1)
    {E F U : Set Torus} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hmE : IsMinimizerAt V E) (hmF : IsMinimizerAt W F)
    (hU : IsOpen U) (he : (E∩U : Set Torus) =ᵐ[torusVolume] (F∩U : Set Torus))
    {μ ν : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (hν : IsNormalMeasure F ν)
    {N M : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (hpN : ∀ k x,N (x+latticeVector k)=N x) (hpM : ∀ k x,M (x+latticeVector k)=M x)
    (haN : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (haM : ∀ᵐ z ∂(ν : Measure NormalBundle),M z.1=(z.2 : Cover))
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)∩U) : N x=M x := by
  let F' := (F\U)∪(E∩U)
  have hF' : MeasurableSet F' := (hF.diff hU.measurableSet).union (hE.inter hU.measurableSet)
  have hrep : F' =ᵐ[torusVolume] F := local_replace_ae he
  exact isMinimizerAt_normal_local_eq hV hW hE hF' hmE ((isMinimizerAt_congr_ae hrep).mpr hmF)
    hU (local_replace_inter E F U).symm hμ (hν.congr_ae hrep.symm) hN hM hpN hpM haN haM x hx

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_reflectNormal (i : Fin 3) : Measurable (reflectNormal i) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((coordinateReflection_continuous i).measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinateReflection i).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma reflectNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (i : Fin 3) (z : NormalBundle) :
    F (reflectNormal i z).1=F (coverCoordinateReflection i z.1) := by
  change F (representative (coordinateReflection i (quotientMap z.1)))=_
  rw [← quotientMap_coordinateReflection]
  exact periodic_representative hp _

lemma coverCoordinateReflection_inner (i : Fin 3) (x y : Cover) :
    ⟪coverCoordinateReflection i x,y⟫=⟪x,coverCoordinateReflection i y⟫ := by
  rw [← (coverCoordinateReflection i).inner_map_map x (coverCoordinateReflection i y),
    coverCoordinateReflection_involutive]

theorem isNormalMeasure_coordinateReflection {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3) :
    IsNormalMeasure (coordinateReflection i ⁻¹' E) (μ.map (reflectNormal i)) := by
  constructor
  · have hm : ((μ.map (reflectNormal i)).mass : ℝ)=(μ.mass : ℝ) := by
      have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_reflectNormal i)
        MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
      simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
        FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh
    rw [hm,hμ.1,perimeter_coordinateReflection_measurable i hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_reflectNormal i).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinateReflection i hF hE,← hμ.2 _ (coordinateReflectedField_admissible i hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinateReflection i z.2,F (reflectNormal i z).1⟫=
        ⟪(z.2 : Cover),coverCoordinateReflection i (F (coverCoordinateReflection i z.1))⟫
      rw [reflectNormal_periodic_eval hF.2.1,coverCoordinateReflection_inner]

lemma reflected_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    ∀ᵐ z ∂(μ.map (reflectNormal i) : Measure NormalBundle),
      coordinateReflectedField i N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (reflectNormal i) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_reflectNormal i).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinateReflection i).continuous.comp (hN.comp (coverCoordinateReflection i).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [hae] with z hz
  change coordinateReflectedField i N (reflectNormal i z).1=((reflectNormal i z).2 : Cover)
  rw [reflectNormal_periodic_eval (coordinateReflectedField_periodic i hp)]
  change coverCoordinateReflection i (N (coverCoordinateReflection i (coverCoordinateReflection i z.1)))=_
  rw [coverCoordinateReflection_involutive,hz]
  rfl

theorem isMinimizerAt_normal_reflection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (x : Cover) (hx : quotientMap x∈frontier (openRepresentative E)) :
    N x=coverCoordinateReflection i (N (coverCoordinateReflection i x)) := by
  have hmR := (isMinimizerAt_congr_ae hs).mpr hmE
  have hh : (E∩univ : Set Torus) =ᵐ[torusVolume] ((coordinateReflection i ⁻¹' E)∩univ : Set Torus) := by
    simpa only [inter_univ] using hs.symm
  exact isMinimizerAt_normal_local_ae_eq hV hV hE ((coordinateReflection_continuous i).measurable hE)
    hmE hmR isOpen_univ hh hμ (isNormalMeasure_coordinateReflection hE hμ i)
    hN (coordinateReflectedField_contDiff i hN) hp (coordinateReflectedField_periodic i hp)
    hae (reflected_normal_ae hN.continuous hp hae i) x ⟨hx,mem_univ _⟩

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_NodalBalanceValue
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma volumeSupport_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    volumeSupport (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (coordinateReflection i ⁻¹' E)∩Metric.ball a r=
      coordinateReflection i ⁻¹' (E∩Metric.ball (coordinateReflection i a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(coordinateReflection_isometry i).dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (coordinateReflection_measurePreserving i).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    openRepresentative (coordinateReflection i ⁻¹' E)=coordinateReflection i ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinateReflection hE.compl]
  rfl

lemma frontier_openRepresentative_coordinateReflection {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) :
    frontier (openRepresentative (coordinateReflection i ⁻¹' E))=
      coordinateReflection i ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinateReflection hE i]
  exact (coordinateReflectionEquiv i).toHomeomorph.preimage_frontier _ |>.symm

lemma frontier_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' frontier (openRepresentative E)=frontier (openRepresentative E) := by
  rw [← frontier_openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

lemma coordinateReflection_fixed_of_sine_zero (i : Fin 3) {a : Torus}
    (ha : coordinateSine i (representative a)=0) : coordinateReflection i a=a := by
  ext j
  by_cases hji : j=i
  · subst j
    simp only [coordinateReflection_apply,ite_true]
    change -a i=a i
    have hz : Real.sin (Real.pi*(2*representative a i))=0 := by
      simpa only [coordinateSine,mul_assoc,mul_left_comm,mul_comm] using ha
    obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hz
    have he : (2 : ℝ)*representative a i=(k : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      exact hk.symm.trans (mul_comm _ _)
    have hh : ((2*representative a i : ℝ) : AddCircle (1 : ℝ))=0 := by
      rw [he]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k,by simp⟩
    have haa : a i+a i=0 := by
      rw [← quotientMap_representative a]
      change ((representative a i : ℝ) : AddCircle (1 : ℝ))+((representative a i : ℝ) : AddCircle (1 : ℝ))=0
      rw [← AddCircle.coe_add,← two_mul]
      exact hh
    exact (neg_eq_iff_add_eq_zero).mpr haa
  · simp [hji]

theorem isMinimizerAt_normal_coordinate_seam_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) {a : Torus}
    (ha : a∈frontier (openRepresentative E)) (hz : coordinateSine i (representative a)=0) :
    N (representative a) i=0 := by
  have hh := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
    (representative a) (by rwa [quotientMap_representative]))
  simp only [coverCoordinateReflection_apply,ite_true] at hh
  have he : N (coverCoordinateReflection i (representative a))=N (representative a) := by
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative,coordinateReflection_fixed_of_sine_zero i hz]
  rw [he] at hh
  linarith

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_MinimizerAxialCenter
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma isMinimizerAt_normal_unit_boundary {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : Continuous N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    ∀ x : Cover,quotientMap x∈frontier (openRepresentative E) → ‖N x‖=1 := by
  apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmE hμ hN.norm continuous_const
    (fun m x => by rw [hp]) (fun _ _ => rfl)
  filter_upwards [hae] with z hz
  rw [hz,z.2.property]

theorem isMinimizerAt_reflection_vertex_excluded {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {a : Torus} (hv : ∀ i,coordinateSine i (representative a)=0) :
    a∉frontier (openRepresentative E) := by
  intro ha
  have hz : N (representative a)=0 := by
    ext i
    exact isMinimizerAt_normal_coordinate_seam_zero hV hE hmE hμ hN hp hae i (hs i) ha (hv i)
  have hu := isMinimizerAt_normal_unit_boundary hV hE hmE hμ hN.continuous hp hae
    (representative a) (by rwa [quotientMap_representative])
  rw [hz,norm_zero] at hu
  exact zero_ne_one hu

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_TorusCylinders
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma torusCoordinatePermute_measurePreserving (e : Fin 3 ≃ Fin 3) :
    MeasurePreserving (torusCoordinatePermute e) torusVolume torusVolume := by
  convert product_to_torus_measurePreserving.comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => AddCircle (1 : ℝ)) e.symm).comp
      torus_to_product_measurePreserving) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  ext i
  simp [Function.comp_def,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft]

lemma quotientMap_coordinatePermute (e : Fin 3 ≃ Fin 3) (x : Cover) :
    quotientMap (coverCoordinatePermute e x)=torusCoordinatePermute e (quotientMap x) := rfl

lemma coverCoordinatePermute_lattice (e : Fin 3 ≃ Fin 3) (m : Fin 3 → ℤ) :
    coverCoordinatePermute e (latticeVector m)=latticeVector (fun j => m (e j)) := rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinatePermutedField_contDiff (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (coordinatePermutedField e F) :=
  (coverCoordinatePermute e.symm).toContinuousLinearEquiv.contDiff.comp
    (hF.comp (coverCoordinatePermute e).toContinuousLinearEquiv.contDiff)

lemma coordinatePermutedField_periodic (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,coordinatePermutedField e F (x+latticeVector n)=coordinatePermutedField e F x := by
  intro n x
  simp only [coordinatePermutedField,map_add,coverCoordinatePermute_lattice,hp]

lemma coordinatePermutedField_admissible (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : AdmissibleField F) : AdmissibleField (coordinatePermutedField e F) := by
  refine ⟨coordinatePermutedField_contDiff e hF.1,coordinatePermutedField_periodic e hF.2.1,?_⟩
  intro x
  simpa only [coordinatePermutedField,LinearIsometryEquiv.norm_map] using hF.2.2 (coverCoordinatePermute e x)

lemma coordinatePermutedField_divergence (e : Fin 3 ≃ Fin 3) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (coordinatePermutedField e F) x=divergence F (coverCoordinatePermute e x) := by
  have hd : HasFDerivAt (coordinatePermutedField e F)
      ((coverCoordinatePermute e.symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((fderiv ℝ F (coverCoordinatePermute e x)).comp
          (coverCoordinatePermute e).toContinuousLinearEquiv.toContinuousLinearMap)) x :=
    (coverCoordinatePermute e.symm).toContinuousLinearEquiv.hasFDerivAt.comp x
      (((hF.differentiable (by simp)) _).hasFDerivAt.comp x
        (coverCoordinatePermute e).toContinuousLinearEquiv.hasFDerivAt)
  unfold divergence
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,coverCoordinatePermute_single,
    coverCoordinatePermute_apply]
  exact e.symm.sum_comp (fun j : Fin 3 => (fderiv ℝ F (coverCoordinatePermute e x) (EuclideanSpace.single j 1)) j)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flux_coordinatePermute (e : Fin 3 ≃ Fin 3) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' (torusCoordinatePermute e ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E,divergence (coordinatePermutedField e.symm F) x := by
  have hm := (torusCoordinatePermute e).continuous.measurable
  have hr := coordinatePermutedField_admissible e.symm hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1) (hm hE),
    ← setIntegral_lift (continuous_divergence hr.1) (divergence_periodic hr.2.1) hE]
  have he : (fun z : Torus => divergence F (representative z)) =
      (fun z => divergence (coordinatePermutedField e.symm F) (representative (torusCoordinatePermute e z))) := by
    funext z
    rw [coordinatePermutedField_divergence e.symm hF.1,← periodic_representative (divergence_periodic hF.2.1)
      (coverCoordinatePermute e.symm (representative (torusCoordinatePermute e z))),
      quotientMap_coordinatePermute,quotientMap_representative]
    have hh : torusCoordinatePermute e.symm (torusCoordinatePermute e z)=z := by
      simpa only [Equiv.symm_symm] using torusCoordinatePermute_inverse e.symm z
    rw [hh]
  rw [he]
  exact (torusCoordinatePermute_measurePreserving e).setIntegral_preimage_emb
    (torusCoordinatePermute e).toHomeomorph.measurableEmbedding
    (fun z => divergence (coordinatePermutedField e.symm F) (representative z)) E

lemma perimeter_coordinatePermute_le (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)≤perimeter E := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [flux_coordinatePermute e hF hE]
  exact le_iSup_of_le (coordinatePermutedField e.symm F)
    (le_iSup_of_le (coordinatePermutedField_admissible e.symm hF) le_rfl)

lemma perimeter_coordinatePermute_measurable (e : Fin 3 ≃ Fin 3) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  apply le_antisymm (perimeter_coordinatePermute_le e hE)
  have hh := perimeter_coordinatePermute_le e.symm ((torusCoordinatePermute e).continuous.measurable hE)
  have he : torusCoordinatePermute e.symm ⁻¹' (torusCoordinatePermute e ⁻¹' E)=E := by
    ext z; simp
  rwa [he] at hh

theorem perimeter_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    perimeter (torusCoordinatePermute e ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq he
  rw [← perimeter_congr_ae hp,← perimeter_congr_ae he]
  exact perimeter_coordinatePermute_measurable e (measurableSet_toMeasurable _ _)

lemma volume_coordinatePermute (e : Fin 3 ≃ Fin 3) {E : Set Torus}
    (hE : NullMeasurableSet E torusVolume) :
    torusVolume (torusCoordinatePermute e ⁻¹' E)=torusVolume E :=
  (torusCoordinatePermute_measurePreserving e).measure_preimage hE

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_CoordinateChamber
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma foldCoordinate_apply (i : Fin 3) (d : ℝ) (upper : Bool) (x : Cover) (j : Fin 3) :
    foldCoordinate i d upper x j=if j=i then
      (if upper then d-|x i-d| else d+|x i-d|) else x j := by
  by_cases hj : j=i
  · subst j; simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply]
  · simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply,hj]

lemma quotientMap_centered_reflection (i : Fin 3) {d : ℝ}
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (x+(2*d-2*x i) • EuclideanSpace.single i 1)=coordinateReflection i (quotientMap x) := by
  obtain ⟨k,hk⟩ := hd
  have he : x+(2*d-2*x i) • EuclideanSpace.single i 1=
      coverCoordinateReflection i x+latticeVector (Pi.single i k) := by
    ext j
    by_cases hj : j=i
    · subst j
      simp [PiLp.add_apply,PiLp.smul_apply,latticeVector]
      linarith
    · simp [PiLp.add_apply,PiLp.smul_apply,latticeVector,hj]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero,quotientMap_coordinateReflection]

lemma foldCoordinate_quotient_alternative (i : Fin 3) {d : ℝ} (upper : Bool)
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (foldCoordinate i d upper x)=quotientMap x ∨
    quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
  have hsame (h : (if upper then d-|x i-d| else d+|x i-d|)=x i) :
      quotientMap (foldCoordinate i d upper x)=quotientMap x := by
    simp only [foldCoordinate,h,sub_self,zero_smul,add_zero]
  have href (h : (if upper then d-|x i-d| else d+|x i-d|)-x i=2*d-2*x i) :
      quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
    simp only [foldCoordinate,h,quotientMap_centered_reflection i hd]
  cases upper
  · by_cases hx : 0≤x i-d
    · exact Or.inl (hsame (by simp only [Bool.false_eq_true,ite_false,abs_of_nonneg hx]; ring))
    · exact Or.inr (href (by simp only [Bool.false_eq_true,ite_false,abs_of_neg (lt_of_not_ge hx)]; ring))
  · by_cases hx : x i-d≤0
    · exact Or.inl (hsame (by simp only [ite_true,abs_of_nonpos hx]; ring))
    · exact Or.inr (href (by simp only [ite_true,abs_of_pos (lt_of_not_ge hx)]; ring))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma openRepresentative_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' openRepresentative E=openRepresentative E := by
  rw [← openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma reflection_invariant_closure {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' closure F=closure F := by
  intro i
  change (coordinateReflectionEquiv i).toHomeomorph ⁻¹' closure F=closure F
  rw [(coordinateReflectionEquiv i).toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage
    (coordinateReflection_continuous i)]
  change closure (coordinateReflection i ⁻¹' F)=closure F
  rw [hs i]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_ChamberGlobalFold
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

lemma chamberVertex_sine_zero (s b : Fin 3 → Bool) (i : Fin 3) :
    coordinateSine i (representative (quotientMap (chamberVertex s b)))=0 := by
  rw [periodic_representative (coordinateSine_periodic i)]
  cases hs : s i <;> cases hb : b i <;>
    simp [coordinateSine,chamberVertex,chamberCorner,hs,hb] <;> ring_nf <;> first | exact Real.sin_pi | exact Real.sin_two_pi | simpa [mul_comm] using Real.sin_two_pi

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_open_of_mem_closure_not_frontier {α : Type*} [TopologicalSpace α]
    {F : Set α} (hF : IsOpen F) {a : α} (hc : a∈closure F) (hn : a∉frontier F) : a∈F := by
  by_contra ha
  apply hn
  rw [frontier,hF.interior_eq]
  exact ⟨hc,ha⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma mem_coordinateHalf_of_chamber_interval (s : Fin 3 → Bool) (x : Cover) (i : Fin 3)
    (hx : chamberCorner s i<x i ∧ x i < chamberCorner s i+1/2) :
    quotientMap x∈coordinateHalf i (if s i then 0 else 1/2) := by
  rw [mem_coordinateHalf_quotient]
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hx
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hx.2]
    · nlinarith [Real.pi_pos,hx.1]
  · simp only [chamberCorner,hs,ite_true] at hx
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hx.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hx.1])
    simpa only [Real.sin_sub_two_pi] using hr

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_CoordinatePlaneRays
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
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

theorem isMinimizerAt_centered_normal_product {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x : Cover} (hx : quotientMap x∈frontier (openRepresentative E)) (i : Fin 3)
    (hxi : |x i-chamberCorner s i|<1/2) (hne : x i≠chamberCorner s i) :
    0<N x i*(x i-chamberCorner s i) := by
  obtain hn|hn := lt_or_gt_of_ne hne
  · let q := x+(2*chamberCorner s i-2*x i) • EuclideanSpace.single i 1
    have hqi : q i=2*chamberCorner s i-x i := by
      simp only [q,PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
      ring
    have hc : ∃ k : ℤ,2*chamberCorner s i=(k : ℝ) := by
      cases hi : s i
      · exact ⟨0,by simp [chamberCorner,hi]⟩
      · exact ⟨1,by simp [chamberCorner,hi]⟩
    have hqeq : quotientMap q=coordinateReflection i (quotientMap x) := quotientMap_centered_reflection i hc x
    have hinv := fun j => frontier_reflection_invariant hE j (hs j)
    have hqb : quotientMap q∈frontier (openRepresentative E) := by
      rw [hqeq]
      change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
      rwa [hinv i]
    have hqhalf : q i∈Ioo (chamberCorner s i) (chamberCorner s i+1/2) := by
      rw [hqi]
      obtain ⟨hl,hu⟩ := abs_lt.mp hxi
      constructor <;> linarith
    have hpos : 0<N q i := hsg q i ⟨hqb,mem_coordinateHalf_of_chamber_interval s q i hqhalf⟩
    have hNq : N q=N (coverCoordinateReflection i x) := by
      rw [← periodic_representative hp q,hqeq,← quotientMap_coordinateReflection,periodic_representative hp]
    have hcov := congrArg (fun z : Cover => z i) (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx)
    simp only [coverCoordinateReflection_apply,ite_true] at hcov
    rw [← hNq] at hcov
    exact mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr hn)
  · have hpos : 0<N x i := hsg x i ⟨hx,mem_coordinateHalf_of_chamber_interval s x i
      ⟨hn,by linarith [(abs_lt.mp hxi).2]⟩⟩
    exact mul_pos hpos (sub_pos.mpr hn)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_coordinate_plane_transverse {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {t : ℝ} {z : ℂ} (hz : z≠0) (hbox : complexSquareGauge z<1/2)
    (hb : quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈frontier (openRepresentative E)) :
    0<⟪N (coordinateSectionPoint (chamberCorner s) t z),coordinatePlaneLift z⟫ := by
  let x := coordinateSectionPoint (chamberCorner s) t z
  have hsign (i : Fin 3) (hi : i=1 ∨ i=2) (hn : x i≠chamberCorner s i) :
      0<N x i*(x i-chamberCorner s i) := by
    apply isMinimizerAt_centered_normal_product hV hE hm hμ hN hp ha hs hsg hb i _ hn
    rcases hi with rfl|rfl
    · simpa [x] using (le_max_left |z.re| |z.im|).trans_lt hbox
    · simpa [x] using (le_max_right |z.re| |z.im|).trans_lt hbox
  have h1 : z.re≠0 →0<N x 1*z.re := by
    intro hh
    simpa [x] using hsign 1 (Or.inl rfl) (by simpa [x] using hh)
  have h2 : z.im≠0 →0<N x 2*z.im := by
    intro hh
    simpa [x] using hsign 2 (Or.inr rfl) (by simpa [x] using hh)
  have hn1 : 0≤N x 1*z.re := by
    by_cases hh : z.re=0
    · simp [hh]
    · exact (h1 hh).le
  have hn2 : 0≤N x 2*z.im := by
    by_cases hh : z.im=0
    · simp [hh]
    · exact (h2 hh).le
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,Fin.sum_univ_three,coordinatePlaneLift_apply,
    Fin.reduceEq,ite_true,ite_false,zero_mul,zero_add]
  change 0<z.re*N x 1+z.im*N x 2
  by_cases hh : z.re=0
  · have hh' : z.im≠0 := by intro he; exact hz (Complex.ext hh he)
    nlinarith [h2 hh']
  · nlinarith [h1 hh]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

theorem continuous_path_exit {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    {F : Set X} (hF : IsOpen F) {γ : A → ℝ → X}
    (hγ : ∀ t,Continuous (fun a => γ a t)) {r : A → ℝ}
    (hr : ∀ a,r a∈Ioo (0 : ℝ) 1)
    (ho : ∀ a t,t∈Icc (0 : ℝ) 1 → (γ a t∈F ↔ t < r a))
    (hc : ∀ a t,t∈Icc (0 : ℝ) 1 → (γ a t∈closure F ↔ t ≤ r a)) :
    Continuous r := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_order.2
  constructor
  · intro q hq
    by_cases hq0 : q<0
    · exact Filter.Eventually.of_forall (fun b => hq0.trans (hr b).1)
    · have hqi : q∈Icc (0 : ℝ) 1 := ⟨le_of_not_gt hq0,hq.le.trans (hr a).2.le⟩
      have hh : γ a q∈F := (ho a q hqi).mpr hq
      filter_upwards [(hγ q).continuousAt.preimage_mem_nhds (hF.mem_nhds hh)] with b hb
      exact (ho b q hqi).mp hb
  · intro q hq
    by_cases hq1 : 1<q
    · exact Filter.Eventually.of_forall (fun b => (hr b).2.trans hq1)
    · have hqi : q∈Icc (0 : ℝ) 1 := ⟨(hr a).1.le.trans hq.le,le_of_not_gt hq1⟩
      have hh : γ a q∈(closure F)ᶜ := by
        intro hn
        exact (not_le.mpr hq) ((hc a q hqi).mp hn)
      filter_upwards [(hγ q).continuousAt.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hh)] with b hb
      exact lt_of_not_ge (fun hn => hb ((hc b q hqi).mpr hn))

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalMeasureCoordinatePermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

theorem contDiffAt_continuous_implicit_root {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {f : A × ℝ → ℝ} {r : A → ℝ} {a : A}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (a,r a)) (hr : ContinuousAt r a)
    (hz : ∀ᶠ b in 𝓝 a,f (b,r b)=f (a,r a))
    (hi : (fderiv ℝ f (a,r a) ∘L ContinuousLinearMap.inr ℝ A ℝ).IsInvertible) :
    ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  have hp : ((⊤ : ℕ∞) : WithTop ℕ∞)≠0 := by simp
  have ht : Tendsto (fun b => (b,r b)) (𝓝 a) (𝓝 (a,r a)) := continuousAt_id.prodMk hr
  have he := ht.eventually (hf.eventually_apply_eq_iff_implicitFunction hp hi)
  apply (hf.contDiffAt_implicitFunction hp hi).congr_of_eventuallyEq
  filter_upwards [he,hz] with b hb hbz
  exact ((hb.mp hbz)).symm

lemma real_clm_isInvertible {L : ℝ →L[ℝ] ℝ} (hL : L 1≠0) : L.IsInvertible := by
  have he (t : ℝ) : L t=t*L 1 := by
    simpa only [smul_eq_mul,mul_one] using L.map_smul t (1 : ℝ)
  have hinj : Function.Injective L := by
    intro t u h
    rw [he t,he u] at h
    exact mul_right_cancel₀ hL h
  have hbij : Function.Bijective L :=
    ⟨hinj,(LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv,rfl⟩

theorem contDiffAt_continuous_implicit_root_of_deriv {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {f : A × ℝ → ℝ} {r : A → ℝ} {a : A} {d : ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (a,r a)) (hr : ContinuousAt r a)
    (hz : ∀ᶠ b in 𝓝 a,f (b,r b)=f (a,r a))
    (hd : HasDerivAt (fun t => f (a,t)) d (r a)) (hdn : d≠0) :
    ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  apply contDiffAt_continuous_implicit_root hf hr hz
  apply real_clm_isInvertible
  have ht : HasDerivAt (fun t : ℝ => (a,t)) (0,1) (r a) :=
    (hasDerivAt_const (r a) a).prodMk (hasDerivAt_id (r a))
  have hh := (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (r a) ht
  have he := hd.unique hh
  change fderiv ℝ f (a,r a) (0,1)≠0
  rwa [← he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_boundary_exit {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {γ : A × ℝ → Cover} {r : A → ℝ} {a : A} {v : Cover}
    (hγ : ContDiffAt ℝ (⊤ : ℕ∞) γ (a,r a)) (hr : ContinuousAt r a)
    (hb : ∀ᶠ b in 𝓝 a,quotientMap (γ (b,r b))∈frontier (openRepresentative E))
    (hd : HasDerivAt (fun t => γ (a,t)) v (r a))
    (hv : ⟪N (γ (a,r a)),v⟫≠0) : ContDiffAt ℝ (⊤ : ℕ∞) r a := by
  let x := γ (a,r a)
  have hx : quotientMap x∈frontier (openRepresentative E) := hb.self_of_nhds
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hm hμ hN hp ha x hx
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  let δ : A × ℝ → Cover := fun p => γ p-x
  let F : A × ℝ → ℝ := fun p => g (normalPlaneCoordinates n (δ p))-⟪n,δ p⟫
  have hδ0 : δ (a,r a)=0 := sub_self _
  have hδ : ContDiffAt ℝ (⊤ : ℕ∞) δ (a,r a) := hγ.sub contDiffAt_const
  have hF : ContDiffAt ℝ (⊤ : ℕ∞) F (a,r a) :=
    (hg.contDiffAt.comp _ ((normalPlaneCoordinates n).contDiff.contDiffAt.comp _ hδ)).sub
      (contDiffAt_const.inner ℝ hδ)
  have hF0 : F (a,r a)=0 := by simp [F,hδ0,hg0]
  have ht : Tendsto (fun b => δ (b,r b)) (𝓝 a) (𝓝 (0 : Cover)) := by
    have he : Tendsto δ (𝓝 (a,r a)) (𝓝 (δ (a,r a))) := hδ.continuousAt
    rw [hδ0] at he
    have hi : Tendsto (fun b : A => (b,r b)) (𝓝 a) (𝓝 (a,r a)) := continuousAt_id.prodMk hr
    exact he.comp hi
  have hz : ∀ᶠ b in 𝓝 a,F (b,r b)=F (a,r a) := by
    filter_upwards [hb,ht.eventually hcover] with b hb' hcov
    have he : x+δ (b,r b)=γ (b,r b) := by dsimp [δ]; abel
    rw [he] at hcov
    have hgph := (normalGraph_coordinates_eq_iff hn _ _).mp (hcov.mp hb')
    change g (normalPlaneCoordinates n (δ (b,r b)))-⟪n,δ (b,r b)⟫=F (a,r a)
    rw [hgph,sub_self,hF0]
  let w := normalPlaneCoordinates n v
  have hδd : HasDerivAt (fun t => δ (a,t)) v (r a) := by
    simpa only [sub_zero] using hd.sub_const x
  have hcd := (normalPlaneCoordinates n).hasFDerivAt.comp_hasDerivAt (r a) hδd
  have hgd := (hg.differentiable (by simp) (0 : Plane)).hasFDerivAt.comp_hasDerivAt_of_eq
    (r a) hcd (by simp [hδ0])
  have hnd := (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt (r a) hδd
  have hFd : HasDerivAt (fun t => F (a,t)) (⟪gradient g 0,w⟫-⟪n,v⟫) (r a) := by
    rw [inner_gradient_left]
    exact hgd.sub hnd
  have hdn : ⟪gradient g 0,w⟫-⟪n,v⟫≠0 := by
    intro he
    apply hv
    change ⟪N x,v⟫=0
    rw [hc,graphSlopeNormal_weight hn,real_inner_smul_left,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
    change σ*((cmcWeight (gradient g 0))⁻¹*(⟪n,v⟫-⟪gradient g 0,w⟫))=0
    rw [sub_eq_zero.mp he]
    ring
  exact contDiffAt_continuous_implicit_root_of_deriv hF hr hz hFd hdn

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unitAngle_contDiff : ContDiff ℝ (⊤ : ℕ∞) unitAngle := by
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_permuteNormal (e : Fin 3 ≃ Fin 3) : Measurable (permuteNormal e) := by
  apply Measurable.prodMk
  · exact measurable_cubeRepresentative.comp ((torusCoordinatePermute e).continuous.measurable.comp
      (measurable_quotientMap.comp (measurable_subtype_coe.comp measurable_fst)))
  · exact ((coverCoordinatePermute e).continuous.measurable.comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk

lemma permuteNormal_periodic_eval {Y : Type*} {F : Cover → Y}
    (hp : ∀ m x,F (x+latticeVector m)=F x) (e : Fin 3 ≃ Fin 3) (z : NormalBundle) :
    F (permuteNormal e z).1=F (coverCoordinatePermute e z.1) := by
  change F (representative (torusCoordinatePermute e (quotientMap z.1)))=_
  rw [← quotientMap_coordinatePermute]
  exact periodic_representative hp _

lemma permuteNormal_mass (μ : FiniteMeasure NormalBundle) (e : Fin 3 ≃ Fin 3) :
    ((μ.map (permuteNormal e)).mass : ℝ)=(μ.mass : ℝ) := by
  have hh := congrArg ENNReal.toReal (Measure.map_apply (measurable_permuteNormal e)
    MeasurableSet.univ (μ := (μ : Measure NormalBundle)))
  simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
    FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh

lemma coverCoordinatePermute_inner (e : Fin 3 ≃ Fin 3) (x y : Cover) :
    ⟪coverCoordinatePermute e x,y⟫=⟪x,coverCoordinatePermute e.symm y⟫ := by
  rw [← (coverCoordinatePermute e).inner_map_map x (coverCoordinatePermute e.symm y),
    coverCoordinatePermute_inverse]

theorem isNormalMeasure_coordinatePermute {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (e : Fin 3 ≃ Fin 3) :
    IsNormalMeasure (torusCoordinatePermute e ⁻¹' E) (μ.map (permuteNormal e.symm)) := by
  constructor
  · rw [permuteNormal_mass,hμ.1,perimeter_coordinatePermute_measurable e hE]
  · intro F hF
    change (∫ z,normalTest F hF.1.continuous z
      ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle))=_
    rw [integral_map (measurable_permuteNormal e.symm).aemeasurable
      (normalTest F hF.1.continuous).continuous.aestronglyMeasurable,
      flux_coordinatePermute e hF hE,← hμ.2 _ (coordinatePermutedField_admissible e.symm hF)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change ⟪coverCoordinatePermute e.symm z.2,F (permuteNormal e.symm z).1⟫=
        ⟪(z.2 : Cover),coverCoordinatePermute e (F (coverCoordinatePermute e.symm z.1))⟫
      rw [permuteNormal_periodic_eval hF.2.1,coverCoordinatePermute_inner,Equiv.symm_symm]

lemma permuted_normal_ae {μ : FiniteMeasure NormalBundle} {N : Cover → Cover}
    (hN : Continuous N) (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (e : Fin 3 ≃ Fin 3) :
    ∀ᵐ z ∂(μ.map (permuteNormal e.symm) : Measure NormalBundle),
      coordinatePermutedField e N z.1=(z.2 : Cover) := by
  change ∀ᵐ z ∂Measure.map (permuteNormal e.symm) (μ : Measure NormalBundle),_
  apply (ae_map_iff (measurable_permuteNormal e.symm).aemeasurable
    (measurableSet_eq_fun
      (((coverCoordinatePermute e.symm).continuous.comp (hN.comp (coverCoordinatePermute e).continuous)).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))
      (measurable_subtype_coe.comp measurable_snd))).mpr
  filter_upwards [ha] with z hz
  change coordinatePermutedField e N (permuteNormal e.symm z).1=((permuteNormal e.symm z).2 : Cover)
  rw [permuteNormal_periodic_eval (coordinatePermutedField_periodic e hp)]
  change coverCoordinatePermute e.symm (N (coverCoordinatePermute e (coverCoordinatePermute e.symm z.1)))=_
  rw [coverCoordinatePermute_inverse,hz]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma finitePerimeter_coordinatePermute {E : Set Torus} (hE : FinitePerimeter E)
    (e : Fin 3 ≃ Fin 3) : FinitePerimeter (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨hE.1.preimage (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving,?_⟩
  rw [perimeter_coordinatePermute e hE.1]
  exact hE.2

theorem isMinimizerAt_coordinatePermute {E : Set Torus} {V : ℝ}
    (hE : IsMinimizerAt V E) (e : Fin 3 ≃ Fin 3) :
    IsMinimizerAt V (torusCoordinatePermute e ⁻¹' E) := by
  refine ⟨finitePerimeter_coordinatePermute hE.1 e,?_,?_⟩
  · rw [volume_coordinatePermute e hE.1.1,hE.2.1]
  · intro F hF hvF
    rw [perimeter_coordinatePermute e hE.1.1]
    exact hE.2.2 F hF hvF

lemma volumeSupport_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    volumeSupport (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' volumeSupport E := by
  ext a
  rw [mem_preimage,mem_volumeSupport_iff,mem_volumeSupport_iff]
  apply forall_congr'
  intro r
  apply imp_congr_right
  intro _
  have he : (torusCoordinatePermute e ⁻¹' E)∩Metric.ball a r=
      torusCoordinatePermute e ⁻¹' (E∩Metric.ball (torusCoordinatePermute e a) r) := by
    ext z
    simp only [mem_inter_iff,mem_preimage,Metric.mem_ball,(torusCoordinatePermute e).isometry.dist_eq]
  rw [he,Measure.real_def,Measure.real_def,
    (torusCoordinatePermute_measurePreserving e).measure_preimage
      (hE.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet]

lemma openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    openRepresentative (torusCoordinatePermute e ⁻¹' E)=torusCoordinatePermute e ⁻¹' openRepresentative E := by
  unfold openRepresentative
  rw [← preimage_compl,volumeSupport_coordinatePermute hE.compl]
  rfl

lemma frontier_openRepresentative_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) (e : Fin 3 ≃ Fin 3) :
    frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))=
      torusCoordinatePermute e ⁻¹' frontier (openRepresentative E) := by
  rw [openRepresentative_coordinatePermute hE e]
  exact (torusCoordinatePermute e).toHomeomorph.preimage_frontier _ |>.symm

lemma coordinateReflection_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (z : Torus) :
    torusCoordinatePermute e (coordinateReflection i z)=
      coordinateReflection (e.symm i) (torusCoordinatePermute e z) := by
  ext j
  simp only [torusCoordinatePermute_apply,coordinateReflection_apply]
  simp only [show (j=e.symm i)↔e j=i from Equiv.eq_symm_apply e]

lemma reflection_invariant_coordinatePermute {E : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) (e : Fin 3 ≃ Fin 3) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E) =ᵐ[torusVolume]
      (torusCoordinatePermute e ⁻¹' E) := by
  intro i
  have hh := (torusCoordinatePermute_measurePreserving e).quasiMeasurePreserving.preimage_ae_eq (hs (e.symm i))
  have he : coordinateReflection i ⁻¹' (torusCoordinatePermute e ⁻¹' E)=
      torusCoordinatePermute e ⁻¹' (coordinateReflection (e.symm i) ⁻¹' E) := by
    ext z
    simp only [mem_preimage,coordinateReflection_coordinatePermute]
  rwa [he]

lemma coordinateHalf_coordinatePermute (e : Fin 3 ≃ Fin 3) (i : Fin 3) (a : ℝ) (z : Torus) :
    torusCoordinatePermute e z∈coordinateHalf i a ↔ z∈coordinateHalf (e i) a := by
  rfl

lemma chamberVertex_coordinatePermute (e : Fin 3 ≃ Fin 3) (c b : Fin 3 → Bool) :
    coverCoordinatePermute e (chamberVertex (c ∘ e.symm) b)=chamberVertex c (b ∘ e) := by
  ext i
  simp [chamberVertex,chamberCorner]

lemma chamberSign_coordinatePermute {E : Set Torus} (hE : MeasurableSet E) {N : Cover → Cover}
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    (e : Fin 3 ≃ Fin 3) :
    ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative (torusCoordinatePermute e ⁻¹' E))∩
        coordinateHalf i (if (c ∘ e.symm) i then 0 else 1/2) →0 < coordinatePermutedField e N x i := by
  intro x i hx
  apply hsg (coverCoordinatePermute e x) (e.symm i)
  constructor
  · rw [quotientMap_coordinatePermute]
    change quotientMap x∈torusCoordinatePermute e ⁻¹' frontier (openRepresentative E)
    rw [← frontier_openRepresentative_coordinatePermute hE e]
    exact hx.1
  · rw [quotientMap_coordinatePermute,coordinateHalf_coordinatePermute,Equiv.apply_symm_apply]
    exact hx.2

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_MinimizerFirstTransitionTube
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

lemma coordinateSectionPoint_continuous_pair (c : Cover) :
    Continuous (fun p : ℝ × ℂ => coordinateSectionPoint c p.1 p.2) := by
  unfold coordinateSectionPoint
  fun_prop

theorem tubular_radius_uniform {c : ℝ}
    {r : (Icc c (c+1/2)) × ℝ → ℝ} (hrc : Continuous r)
    (hr : ∀ p,0 < r p ∧ r p<unitSquareScale p.2) :
    ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
      ε ≤ r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  let K := (Icc c (c+1/2)) × (Icc (0 : ℝ) 1)
  let g : K → ℝ := fun p => min (r (p.1,p.2.val))
    (unitSquareScale p.2.val-r (p.1,p.2.val))
  have hgc : Continuous g := by
    have hc : Continuous (fun p : K => r (p.1,p.2.val)) :=
      hrc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact hc.min ((unitSquareScale_continuous.comp (continuous_subtype_val.comp continuous_snd)).sub hc)
  have hgp (p : K) : 0<g p := lt_min (hr _).1 (sub_pos.mpr (hr _).2)
  have hn : (univ : Set K).Nonempty :=
    ⟨(⟨c,by constructor <;> linarith⟩,⟨0,by norm_num⟩),mem_univ _⟩
  obtain ⟨p,_,hmin⟩ := isCompact_univ.exists_isMinOn hn hgc.continuousOn
  refine ⟨g p,hgp p,?_⟩
  intro t a ha
  have hh := hmin (show (t,⟨a,ha⟩)∈(univ : Set K) from mem_univ _)
  change g p ≤ min (r (t,a)) (unitSquareScale a-r (t,a)) at hh
  obtain ⟨h1,h2⟩ := le_min_iff.mp hh
  exact ⟨h1,by linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_coordinateSectionPoint_int (c : Cover) (t : ℝ) (z : ℂ) (n : ℤ) :
    quotientMap (coordinateSectionPoint c (t+(n : ℝ)) z)=
      quotientMap (coordinateSectionPoint c t z) := by
  have he : coordinateSectionPoint c (t+(n : ℝ)) z=
      coordinateSectionPoint c t z+latticeVector (Pi.single 0 n) := by
    ext i
    fin_cases i <;> simp [latticeVector]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma coordinateSectionPoint_fold_axis (s : Fin 3 → Bool) (t : ℝ) :
    ∃ τ∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2),
      ∀ (F : Set Torus),coordinateReflection 0 ⁻¹' F=F → ∀ z : ℂ,
        (quotientMap (coordinateSectionPoint (chamberCorner s) τ z)∈F ↔
          quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈F) := by
  let n : ℤ := ⌊t-chamberCorner s 0+1/2⌋
  let w := t-(n : ℝ)
  let τ := chamberCorner s 0+|w-chamberCorner s 0|
  have hl := Int.floor_le (t-chamberCorner s 0+1/2)
  have hu := Int.lt_floor_add_one (t-chamberCorner s 0+1/2)
  have hw : |w-chamberCorner s 0|≤1/2 := by
    dsimp only [w,n]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  refine ⟨τ,⟨by dsimp [τ]; exact le_add_of_nonneg_right (abs_nonneg _),by dsimp [τ]; linarith⟩,?_⟩
  intro F hF z
  have hbase : ∃ k : ℤ,2*chamberCorner s 0=(k : ℝ) := by
    cases hh : s 0
    · exact ⟨0,by simp [chamberCorner,hh]⟩
    · exact ⟨1,by simp [chamberCorner,hh]⟩
  have he : coordinateSectionPoint (chamberCorner s) τ z=
      foldCoordinate 0 (chamberCorner s 0) false
        (coordinateSectionPoint (chamberCorner s) w z) := by
    ext i
    fin_cases i <;> simp [foldCoordinate_apply,τ]
  have hwq : quotientMap (coordinateSectionPoint (chamberCorner s) w z)=
      quotientMap (coordinateSectionPoint (chamberCorner s) t z) := by
    simpa only [w,Int.cast_neg,sub_eq_add_neg] using
      quotientMap_coordinateSectionPoint_int (chamberCorner s) t z (-n)
  rcases foldCoordinate_quotient_alternative 0 false hbase
    (coordinateSectionPoint (chamberCorner s) w z) with hh|hh
  · rw [he,hh,hwq]
  · rw [he,hh,hwq]
    change quotientMap (coordinateSectionPoint (chamberCorner s) t z)∈coordinateReflection 0 ⁻¹' F ↔ _
    rw [hF]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_radial_phase {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hrpos : ∀ p,0 < r p ∧ r p<unitSquareScale p.2)
    (hrop : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint c p.1 (u • unitAngle p.2))∈openRepresentative E ↔ u < r p))
    (hrcl : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint c p.1 (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r p)) :
    Continuous r := by
  let q : ℝ × ℝ → ℝ := fun p => r p/unitSquareScale p.2
  have hqc : Continuous q := by
    refine continuous_path_exit (isOpen_openRepresentative E)
      (γ := fun p u => quotientMap (coordinateSectionPoint c p.1
        ((u*unitSquareScale p.2) • unitAngle p.2))) ?_ ?_ ?_ ?_
    · intro u
      exact continuous_quotientMap.comp ((coordinateSectionPoint_continuous_pair c).comp
        (continuous_fst.prodMk
          ((continuous_const.mul (unitSquareScale_continuous.comp continuous_snd)).smul
            (unitAngle_contDiff.continuous.comp continuous_snd))))
    · intro p
      exact ⟨div_pos (hrpos p).1 (unitSquareScale_pos p.2),
        (div_lt_one (unitSquareScale_pos p.2)).mpr (hrpos p).2⟩
    · intro p u hu
      rw [hrop p (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (lt_div_iff₀ (unitSquareScale_pos p.2)).symm
    · intro p u hu
      rw [hrcl p (u*unitSquareScale p.2)
        (mul_nonneg hu.1 (unitSquareScale_pos p.2).le)
        (by nlinarith [unitSquareScale_pos p.2,hu.2])]
      exact (le_div_iff₀ (unitSquareScale_pos p.2)).symm
  have he : r=fun p => q p*unitSquareScale p.2 := by
    funext p
    dsimp only [q]
    rw [div_mul_cancel₀ _ (unitSquareScale_pos p.2).ne']
  rw [he]
  exact hqc.mul (unitSquareScale_continuous.comp continuous_snd)

theorem isMinimizerAt_contDiff_tube_radius {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r : ℝ × ℝ → ℝ} (hrc : Continuous r)
    (hrpos : ∀ p,0 < r p ∧ r p<unitSquareScale p.2)
    (hrbd : ∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
      (r p • unitAngle p.2))∈frontier (openRepresentative E)) :
    ContDiff ℝ (⊤ : ℕ∞) r := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let γ : (ℝ × ℝ) × ℝ → Cover := fun b =>
    coordinateSectionPoint (chamberCorner s) b.1.1 (b.2 • unitAngle b.1.2)
  have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := by
    dsimp only [γ,coordinateSectionPoint]
    exact (contDiff_const.add
      ((contDiff_fst.fst.sub contDiff_const).smul contDiff_const)).add
        (coordinatePlaneLift.contDiff.comp
          (contDiff_snd.smul (unitAngle_contDiff.comp contDiff_fst.snd)))
  have hd : HasDerivAt (fun u => γ (p,u)) (coordinatePlaneLift (unitAngle p.2)) (r p) := by
    have hh := coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt (r p)
      ((hasDerivAt_id (r p)).smul_const (unitAngle p.2))
    simpa only [γ,coordinateSectionPoint,Function.comp_def,one_smul,id_eq] using
      hh.const_add (chamberCorner s+(p.1-chamberCorner s 0) • EuclideanSpace.single 0 1)
  have hz : r p • unitAngle p.2≠0 := smul_ne_zero (hrpos p).1.ne' (unitAngle_ne_zero p.2)
  have hgauge : complexSquareGauge (r p • unitAngle p.2)<1/2 := by
    rw [complexSquareGauge_smul (hrpos p).1.le]
    have hscl : unitSquareScale p.2*complexSquareGauge (unitAngle p.2)=1/2 := by
      dsimp [unitSquareScale]
      field_simp [(complexSquareGauge_pos (unitAngle_ne_zero p.2)).ne']
    calc
      r p*complexSquareGauge (unitAngle p.2)<unitSquareScale p.2*complexSquareGauge (unitAngle p.2) :=
        mul_lt_mul_of_pos_right (hrpos p).2 (complexSquareGauge_pos (unitAngle_ne_zero p.2))
      _=1/2 := hscl
  have hpos := isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hz hgauge (hrbd p)
  have hne : ⟪N (γ (p,r p)),coordinatePlaneLift (unitAngle p.2)⟫≠0 := by
    intro he
    rw [map_smul,real_inner_smul_right] at hpos
    change 0 < r p*⟪N (γ (p,r p)),coordinatePlaneLift (unitAngle p.2)⟫ at hpos
    rw [he,mul_zero] at hpos
    exact lt_irrefl _ hpos
  exact isMinimizerAt_smooth_boundary_exit hV hE hm hμ hN hp ha hγ.contDiffAt
    hrc.continuousAt (Filter.Eventually.of_forall hrbd) hd hne

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tubular_radius_extension {E : Set Torus} (hE : MeasurableSet E)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    {r0 : (Icc (chamberCorner s 0) (chamberCorner s 0+1/2)) × ℝ → ℝ}
    (hr0c : Continuous r0)
    (hr0p : ∀ t,Function.Periodic (fun a => r0 (t,a)) 1)
    (hr0pos : ∀ p,0 < r0 p ∧ r0 p<unitSquareScale p.2)
    (hr0bd : ∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
      (r0 p • unitAngle p.2))∈frontier (openRepresentative E))
    (hr0op : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        (u • unitAngle p.2))∈openRepresentative E ↔ u < r0 p))
    (hr0cl : ∀ p u,0≤u → u≤unitSquareScale p.2 →
      (quotientMap (coordinateSectionPoint (chamberCorner s) p.1.val
        (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r0 p)) :
    ∃ r : ℝ × ℝ → ℝ,Continuous r ∧
      (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
      (∀ p,0 < r p ∧ r p<unitSquareScale p.2) ∧
      (∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
        (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈openRepresentative E ↔ u < r p)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r p)) ∧
      ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
        ε ≤ r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  choose τ hτ hfold using coordinateSectionPoint_fold_axis s
  let r : ℝ × ℝ → ℝ := fun p => r0 (⟨τ p.1,hτ p.1⟩,p.2)
  have hsO := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hsC := reflection_invariant_closure hsO
  have hsB := fun i => frontier_reflection_invariant hE i (hs i)
  have hrpos (p : ℝ × ℝ) : 0 < r p ∧ r p<unitSquareScale p.2 := hr0pos _
  have hrbd (p : ℝ × ℝ) : quotientMap (coordinateSectionPoint (chamberCorner s) p.1
      (r p • unitAngle p.2))∈frontier (openRepresentative E) :=
    (hfold p.1 _ (hsB 0) _).mp (hr0bd (⟨τ p.1,hτ p.1⟩,p.2))
  have hrop (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2) :
      quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈openRepresentative E ↔ u < r p := by
    rw [← hfold p.1 _ (hsO 0) _]
    exact hr0op (⟨τ p.1,hτ p.1⟩,p.2) u hu hu'
  have hrcl (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2) :
      quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r p := by
    rw [← hfold p.1 _ (hsC 0) _]
    exact hr0cl (⟨τ p.1,hτ p.1⟩,p.2) u hu hu'
  have huniq (p : ℝ × ℝ) (u : ℝ) (hu : 0≤u) (hu' : u≤unitSquareScale p.2)
      (hb : quotientMap (coordinateSectionPoint (chamberCorner s) p.1 (u • unitAngle p.2))∈frontier (openRepresentative E)) : u=r p := by
    rw [(isOpen_openRepresentative E).frontier_eq] at hb
    exact le_antisymm ((hrcl p u hu hu').mp hb.1)
      (le_of_not_gt (fun h => hb.2 ((hrop p u hu hu').mpr h)))
  have hrc : Continuous r := continuous_radial_phase hrpos hrop hrcl
  refine ⟨r,hrc,?_,fun t a => hr0p _ a,hrpos,hrbd,hrop,hrcl,?_⟩
  · intro t a
    apply huniq (t,a) (r (t+1,a)) (hrpos _).1.le (hrpos _).2.le
    have hh := hrbd (t+1,a)
    simpa only [show t+1=t+(1 : ℤ) from by norm_num,
      quotientMap_coordinateSectionPoint_int] using hh
  · obtain ⟨ε,hε,hεr⟩ := tubular_radius_uniform hr0c hr0pos
    exact ⟨ε,hε,fun t a ha => hεr _ a ha⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_tube_radius {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv0 : quotientMap (chamberVertex s (fun j => decide (j=0)))∈openRepresentative E)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E)) :
    ∃ r : ℝ × ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ t a,r (t+1,a)=r (t,a)) ∧ (∀ t a,r (t,a+1)=r (t,a)) ∧
      (∀ p,0 < r p ∧ r p<unitSquareScale p.2) ∧
      (∀ p,quotientMap (coordinateSectionPoint (chamberCorner s) p.1
        (r p • unitAngle p.2))∈frontier (openRepresentative E)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈openRepresentative E ↔ u < r p)) ∧
      (∀ p u,0≤u → u≤unitSquareScale p.2 →
        (quotientMap (coordinateSectionPoint (chamberCorner s) p.1
          (u • unitAngle p.2))∈closure (openRepresentative E) ↔ u ≤ r p)) ∧
      ∃ ε : ℝ,0<ε ∧ ∀ t (a : ℝ),a∈Icc (0 : ℝ) 1 →
        ε ≤ r (t,a) ∧ r (t,a)+ε≤unitSquareScale a := by
  obtain ⟨r0,hr0c,hr0s,hr0p,hr0pos,hr0bd,hr0op,hr0cl⟩ :=
    isMinimizerAt_tubular_sections hV hE hm hμ hN hp ha hs hsg hv0 hv1 hv2
  obtain ⟨r,hrc,hrp1,hrp2,hrpos,hrbd,hrop,hrcl,heps⟩ :=
    tubular_radius_extension hE hs hr0c hr0p hr0pos hr0bd hr0op hr0cl
  exact ⟨r,isMinimizerAt_contDiff_tube_radius hV hE hm hμ hN hp ha hs hsg hrc hrpos hrbd,
    hrp1,hrp2,hrpos,hrbd,hrop,hrcl,heps⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_two_vertices_smooth_tube_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ j : Fin 3,coordinateReflection j ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (j : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf j (if c j then 0 else 1/2) →0<N x j)
    (i : Fin 3)
    (hv : ∀ b : Fin 3 → Bool,quotientMap (chamberVertex c b)∈openRepresentative E ↔
      b=(fun _ => false) ∨ b=(fun j => decide (j=i))) :
    ∃ (e : Fin 3 ≃ Fin 3) (r : ℝ × ℝ → ℝ),
      TrueRadialTube (torusCoordinatePermute e ⁻¹' E) (chamberCorner (c ∘ e.symm)) r := by
  classical
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have he0 : e.symm 0=i := by simp [e]
  have hF := (torusCoordinatePermute e).continuous.measurable hE
  have hmF := isMinimizerAt_coordinatePermute hm e
  have hμF := isNormalMeasure_coordinatePermute hE hμ e
  have hNF := coordinatePermutedField_contDiff e hN
  have hpF := coordinatePermutedField_periodic e hp
  have haF := permuted_normal_ae hN.continuous hp ha e
  have hsF := reflection_invariant_coordinatePermute hs e
  have hsgF := chamberSign_coordinatePermute hE hsg e
  have hvF (b : Fin 3 → Bool) :
      quotientMap (chamberVertex (c ∘ e.symm) b)∈openRepresentative (torusCoordinatePermute e ⁻¹' E) ↔
      quotientMap (chamberVertex c (b ∘ e))∈openRepresentative E := by
    rw [openRepresentative_coordinatePermute hE e]
    change torusCoordinatePermute e (quotientMap (chamberVertex (c ∘ e.symm) b))∈openRepresentative E ↔ _
    rw [← quotientMap_coordinatePermute,chamberVertex_coordinatePermute]
  have hsingle (j : Fin 3) : ((fun k : Fin 3 => decide (k=j)) ∘ e)=
      (fun k => decide (k=e.symm j)) := by
    funext k
    simp only [Function.comp_apply,← Equiv.eq_symm_apply]
  have h0 : quotientMap (chamberVertex (c ∘ e.symm) (fun j => decide (j=0)))∈
      openRepresentative (torusCoordinatePermute e ⁻¹' E) := by
    rw [hvF,hsingle,he0,hv]
    exact Or.inr rfl
  have hnot (j : Fin 3) (hj : j≠0) :
      quotientMap (chamberVertex (c ∘ e.symm) (fun k => decide (k=j)))∉
        closure (openRepresentative (torusCoordinatePermute e ⁻¹' E)) := by
    intro hh
    have ho := mem_open_of_mem_closure_not_frontier
      (isOpen_openRepresentative (torusCoordinatePermute e ⁻¹' E)) hh
      (isMinimizerAt_reflection_vertex_excluded hV hF hmF hμF hNF hpF haF hsF
        (chamberVertex_sine_zero (c ∘ e.symm) _))
    rw [hvF,hsingle,hv] at ho
    have heji : e.symm j≠i := by rw [← he0]; exact e.symm.injective.ne hj
    rcases ho with h|h
    · have hh := congrFun h (e.symm j)
      simp at hh
    · have hh := congrFun h (e.symm j)
      simp [heji] at hh
  obtain ⟨r,hr⟩ := isMinimizerAt_smooth_tube_radius hV hF hmF hμF hNF hpF haF hsF hsgF h0
    (hnot 1 (by decide)) (hnot 2 (by decide))
  exact ⟨e,r,hr⟩

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube_oai := @OAI.CubicTorus.isMinimizerAt_two_vertices_smooth_tube_oai
