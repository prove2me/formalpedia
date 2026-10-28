-- Prove2me | solution 1 for OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:56:29.47492+00:00
-- url     : https://prove2.me/submissions/1579bf1c-98dc-471c-a774-338ee0a129b0

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

lemma quotientMap_neg (x : Cover) : quotientMap (-x) = -quotientMap x := by
  ext i
  simp [quotientMap]

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
open Filter
open scoped Topology Convolution RealInnerProductSpace

lemma characteristic_nonneg (E : Set Torus) (x : Torus) : 0 ≤ characteristic E x := by
  rcases characteristic_dichotomy E x with h | h <;> simp [h]

end CubicTorus

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

lemma representative_quotientMap_of_mem {x : Cover} (hx : x ∈ fundamentalCube) :
    representative (quotientMap x) = x := by
  ext i
  change ((AddCircle.equivIco (1 : ℝ) 0) (x i : AddCircle (1 : ℝ)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_of_mem (by simpa using hx i)]

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma continuous_coordinateNormalVelocity (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : NormalBundle ↦ coordinateNormalVelocity i f z.1 z.2) := by
  unfold coordinateNormalVelocity
  exact ((((hf.continuous_fderiv (by simp)).clm_apply continuous_const).comp
    (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).sub
    (((continuous_subtype_val.comp continuous_snd).inner (𝕜 := ℝ) continuous_const).smul
      ((gradient_contDiff hf).continuous.comp (continuous_subtype_val.comp continuous_fst)))

lemma continuous_normalUnit : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
  continuous_subtype_val.comp continuous_snd

end CubicTorus

namespace CubicTorus
open Filter
open scoped Topology RealInnerProductSpace

lemma integrableOn_directionalDeriv (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    IntegrableOn (fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)) fundamentalCube := by
  have hFc : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) :=
    hf.smul contDiff_const
  have hi := integrableOn_divergence hFc
  have he : divergence (fun x ↦ f x • (EuclideanSpace.single i 1 : Cover)) =
      fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact divergence_smul_const (hf.differentiable (by simp)).differentiableAt _
  rwa [he] at hi

lemma exists_wallVariation_of_function (i : Fin 3) {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ n x, f (x + latticeVector n) = f x)
    (hface : ∀ x, x i = 0 ∨ x i = 1 → f x = 0) :
    ∃ D : WallVariation, D.coordinate = i ∧ D.function = f := by
  obtain ⟨M, hM, hbound⟩ := periodic_bounded (hf.continuous_fderiv (by simp))
    (fderiv_periodic hp)
  refine ⟨⟨i, f, ⟨M, hM⟩, hf, hp, ?_, hface⟩, rfl, rfl⟩
  intro x
  exact_mod_cast hbound x

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

lemma fderiv_component {F : Cover → Cover} {x : Cover} (hF : DifferentiableAt ℝ F x)
    (i : Fin 3) (v : Cover) :
    fderiv ℝ (fun y ↦ F y i) x v = fderiv ℝ F x v i := by
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ F y i) x = _ at hh
  rw [hh]
  rfl

lemma flux_sum_components (E : Set Torus) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x) =
      ∑ i : Fin 3, directionalFlux E i (fun x ↦ F x i) := by
  unfold divergence directionalFlux
  simp_rw [← fderiv_component (hF.differentiable (by simp)).differentiableAt]
  exact integral_finsetSum _ (fun i _ ↦
    (integrableOn_directionalDeriv i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)).mono_set
      inter_subset_left)

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma inner_coordinateNormalVelocity (i : Fin 3) (f : Cover → ℝ) (x : Cover)
    {n : Cover} (hn : ‖n‖ = 1) :
    ⟪n, coordinateNormalVelocity i f x n⟫ =
      fderiv ℝ f x (EuclideanSpace.single i 1) - n i * fderiv ℝ f x n := by
  simp only [coordinateNormalVelocity, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hn, one_pow, mul_one, inner_gradient_right,
    conj_trivial]
  congr 1
  simp [PiLp.inner_apply, EuclideanSpace.single]

lemma tangentialDivergence_eq_sum {F : Cover → Cover} {x n : Cover}
    (hF : DifferentiableAt ℝ F x) (hn : ‖n‖ = 1) :
    tangentialDivergence F x n = ∑ i : Fin 3,
      ⟪n, coordinateNormalVelocity i (fun y ↦ F y i) x n⟫ := by
  simp_rw [inner_coordinateNormalVelocity _ _ _ hn, fderiv_component hF]
  simp only [Finset.sum_sub_distrib, tangentialDivergence, divergence]
  congr 1
  simp [PiLp.inner_apply, mul_comm]

lemma integral_tangentialDivergence_eq_sum {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (μ : FiniteMeasure NormalBundle) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      ∑ i : Fin 3, ∫ z, ⟪(z.2 : Cover),
        coordinateNormalVelocity i (fun y ↦ F y i) z.1 z.2⟫ ∂(μ : Measure NormalBundle) := by
  have he (z : NormalBundle) := tangentialDivergence_eq_sum (x := (z.1 : Cover))
    (hF.differentiable (by simp)).differentiableAt z.2.property
  simp_rw [he]
  apply integral_finsetSum
  intro i _
  exact (continuous_normalUnit.inner (𝕜 := ℝ)
    (continuous_coordinateNormalVelocity i
      ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x
    change (F (x + latticeVector m)) i = (F x) i
    rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_wallVariation_of_function i hc hpc (hw i)
  simpa only [normalFirstVariation, hi, hf] using hH D

theorem weakCMC_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x)
    (hw : ∀ i x, x i = 0 ∨ x i = 1 → F x i = 0) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [tangent_firstVariation_of_coordinate hH hF hp hw]
  obtain ⟨C, hC, hbound⟩ := periodic_bounded hF.continuous hp
  have h := normalMeasure_flux hμ hF hp (by linarith : 0 < C + 1)
    (fun x ↦ (hbound x).trans (by linarith : C ≤ C + 1))
  exact congrArg (fun r : ℝ ↦ H * r) h.symm

end CubicTorus

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

lemma latticePeriodize_wall {F : Cover → Cover}
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (i : Fin 3) (x : Cover)
    (hx : x i = 0 ∨ x i = 1) : latticePeriodize F x i = 0 := by
  have he : latticePeriodize F x = 0 := by
    unfold latticePeriodize
    suffices hz : ∀ n : Fin 3 → ℤ, F (x + latticeVector n) = 0 by
      simp only [hz, tsum_zero]
    intro n
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hi := hs h i
    simp only [PiLp.add_apply, latticeVector] at hi
    rcases hx with hx | hx
    · rw [hx, zero_add] at hi
      have hlo : (0 : ℤ) < n i := by exact_mod_cast hi.1
      have hhi : n i < (1 : ℤ) := by exact_mod_cast hi.2
      omega
    · rw [hx] at hi
      have hlo : (-1 : ℤ) < n i := by exact_mod_cast (by linarith : (-1 : ℝ) < (n i : ℝ))
      have hhi : n i < (0 : ℤ) := by exact_mod_cast (by linarith : (n i : ℝ) < 0)
      omega
  rw [he]
  rfl

theorem weakCMC_local_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  have h := weakCMC_identity hμ hH (latticePeriodize_contDiff hF hc)
    (latticePeriodize_periodic F) (latticePeriodize_wall hs)
  have he (z : NormalBundle) := latticePeriodize_eventuallyEq hc hs (compactCell_coordinates z.1)
  have hval (z : NormalBundle) : latticePeriodize F z.1 = F z.1 := (he z).eq_of_nhds
  have hder (z : NormalBundle) : fderiv ℝ (latticePeriodize F) z.1 = fderiv ℝ F z.1 :=
    (he z).fderiv_eq
  simpa only [tangentialDivergence, divergence, hder, hval] using h

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

lemma coverBall_subset_cube {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball cubeCenter r ⊆ fundamentalCube := by
  intro x hx i
  have hx' : ‖x - cubeCenter‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hb := (PiLp.norm_apply_le (x - cubeCenter) i).trans_lt hx'
  change ‖x i - (1 / 2 : ℝ)‖ < r at hb
  rw [Real.norm_eq_abs, abs_lt] at hb
  constructor <;> linarith

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
open scoped ENNReal Topology RealInnerProductSpace Convolution

namespace CubicTorus

lemma norm_quotientMap_le (x : Cover) : ‖quotientMap x‖ ≤ ‖x‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) QuotientAddGroup.norm_mk_le_norm 2

lemma quotientMap_shortestLift (x : Torus) : quotientMap (shortestLift x) = x := by
  simp only [shortestLift, quotientMap_sub, quotientMap_representative, add_sub_cancel_right]

lemma norm_shortestLift (x : Torus) : ‖shortestLift x‖ = ‖x‖ := by
  have hh := dist_representative_cubeCenter (x + quotientMap cubeCenter)
  simpa only [dist_eq_norm, add_sub_cancel_right, shortestLift] using hh

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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVTangentialBlowup
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

lemma shortestLift_quotientMap {x : Cover} (hx : ‖x‖ < 1 / 2) :
    shortestLift (quotientMap x) = x := by
  have hc : x + cubeCenter ∈ fundamentalCube := coverBall_subset_cube (by rfl)
    (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right] using hx)
  rw [shortestLift, ← quotientMap_add, representative_quotientMap_of_mem hc, add_sub_cancel_right]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRadialVariation
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

lemma quotientMap_injective_open_closed_cell {x y : Cover}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (he : quotientMap x = quotientMap y) : x = y := by
  obtain ⟨n, hn⟩ := same_quotient_lattice he
  have hz (i : Fin 3) : n i = 0 := by
    have he' := congrArg (fun z : Cover ↦ z i) hn
    change x i = y i + (n i : ℝ) at he'
    have hlt : (n i : ℝ) < 1 := by linarith [(hx i).2, (hy i).1]
    have hgt : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).1, (hy i).2]
    have hlt' : n i < (1 : ℤ) := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n i := by exact_mod_cast hgt
    omega
  rw [show n = 0 from funext hz, latticeVector_zero, add_zero] at hn
  exact hn

lemma quotientMap_image_ball (a : Cover) (r : ℝ) :
    quotientMap '' Metric.ball a r = Metric.ball (quotientMap a) r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change dist (quotientMap y) (quotientMap a) < r
    rw [dist_eq_norm, ← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
  · intro hx
    refine ⟨shortestLift (x - quotientMap a) + a, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_shortestLift] using hx
    · rw [quotientMap_add, quotientMap_shortestLift, sub_add_cancel]

lemma compactCell_mem_quotient_ball_iff (z : CompactCell) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    quotientMap z ∈ Metric.ball (quotientMap a) r ↔ (z : Cover) ∈ Metric.ball a r := by
  constructor
  · intro hz
    rw [← quotientMap_image_ball a r] at hz
    obtain ⟨y, hy, he⟩ := hz
    have he' := quotientMap_injective_open_closed_cell (compactCell_coordinates z) (hc hy) he.symm
    rwa [he']
  · intro hz
    rw [← quotientMap_image_ball a r]
    exact ⟨z, hz, rfl⟩

lemma cellBallMass_eq_spatialNormalMeasure (μ : FiniteMeasure NormalBundle) (a : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    cellBallMass μ a r = (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap a) r) := by
  unfold cellBallMass
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle) (Metric.ball (quotientMap a) r)).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable Metric.isOpen_ball.measurableSet]
  congr 1
  ext z
  exact (compactCell_mem_quotient_ball_iff z.1 a r hc).symm

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

lemma tangentialDivergence_smul_const {f : Cover → ℝ} {x : Cover}
    (hf : DifferentiableAt ℝ f x) (ν n : Cover) :
    tangentialDivergence (fun y ↦ f y • n) x ν = fderiv ℝ f x (tangentPart ν n) := by
  rw [tangentialDivergence, divergence_smul_const hf, fderiv_smul_const hf]
  simp only [ContinuousLinearMap.smulRight_apply, inner_smul_right, tangentPart,
    map_sub, map_smul, smul_eq_mul]
  ring

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

lemma unit_normal_sq_distance {ν n : Cover} (hν : ‖ν‖ = 1) (hn : ‖n‖ = 1) :
    ‖ν - n‖ ^ 2 = 2 * (1 - ⟪ν, n⟫) := by
  rw [norm_sub_sq_real, hν, hn]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_of_notMem_tsupport {ψ : Cover → ℝ} {x : Cover}
    (hx : x ∉ tsupport ψ) : gradient ψ x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

lemma gradient_tsupport_subset (ψ : Cover → ℝ) :
    tsupport (gradient ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hh
  exact hx (gradient_of_notMem_tsupport hh)

theorem normalMeasure_local_laplacian {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) =
      ∫ z, fderiv ℝ ψ z.1 (z.2 : Cover) ∂(μ : Measure NormalBundle) := by
  have hf := normalMeasure_local_flux hE hμ (gradient_contDiff hψ)
    (hc.of_isClosed_subset isClosed_closure (gradient_tsupport_subset ψ))
    ((gradient_tsupport_subset ψ).trans hs)
  simpa [inner_gradient_right] using hf.symm

theorem weakCMC_scalar_residual_identity {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) -
      (∫ z, fderiv ℝ ψ z.1 n ∂(μ : Measure NormalBundle)) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hν : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
    continuous_subtype_val.comp continuous_snd
  have hd := (hψ.continuous_fderiv (by simp)).comp hx
  have hB : Integrable (fun z : NormalBundle ↦ fderiv ℝ ψ z.1 (z.2 : Cover)) (μ : Measure NormalBundle) :=
    (hd.clm_apply hν).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hD : Integrable (fun z : NormalBundle ↦ fderiv ℝ ψ z.1 n) (μ : Measure NormalBundle) :=
    (hd.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover))
      (μ : Measure NormalBundle) :=
    ((hν.inner continuous_const).mul (hd.clm_apply hν)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hF := hψ.smul_const n
  have hFs := tsupport_smul_subset_left (f := ψ) (g := fun _ ↦ n)
  have hvar := weakCMC_local_identity hμ hH hF
    (hc.of_isClosed_subset isClosed_closure hFs) (hFs.trans hs)
  have he (z : NormalBundle) : tangentialDivergence (fun x ↦ ψ x • n) z.1 z.2 =
      fderiv ℝ ψ z.1 n - ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover) := by
    rw [tangentialDivergence_smul_const ((hψ.differentiable (by simp)) _)]
    simp only [tangentPart, map_sub, map_smul, smul_eq_mul]
  simp_rw [he, inner_smul_right] at hvar
  rw [integral_sub hD hA] at hvar
  have herr (z : NormalBundle) :
      ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover) =
      2 * (fderiv ℝ ψ z.1 (z.2 : Cover) -
        ⟪(z.2 : Cover), n⟫ * fderiv ℝ ψ z.1 (z.2 : Cover)) := by
    rw [unit_normal_sq_distance z.2.property hn]
    ring
  simp_rw [herr]
  rw [integral_const_mul, integral_sub hB hA, normalMeasure_local_laplacian hE hμ hψ hc hs]
  linarith

end CubicTorus

end
end

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

lemma trapped_frontier_height {E : Set Torus} (hE : IsOpen E)
    {a n x : Cover} {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    (hx : x ∈ Metric.ball a r) (hb : quotientMap x ∈ frontier E) :
    |⟪n, x - a⟫| ≤ ε * r := by
  have hl : shortestLift (quotientMap x - quotientMap a) = x - a := by
    rw [← quotientMap_sub]
    exact shortestLift_quotientMap ((show ‖x - a‖ < r by simpa only [Metric.mem_ball, dist_eq_norm] using hx).trans hrsmall)
  have hd : dist (quotientMap x) (quotientMap a) < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hl]
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  apply abs_le.mpr
  constructor
  · by_contra! hh
    have hmem := htrap.2 (show quotientMap x ∈ normalCap (quotientMap a) (-n) r (ε * r) from
      ⟨hd, by rw [hl, inner_neg_left]; linarith⟩)
    rw [frontier, hE.interior_eq] at hb
    exact hb.2 hmem
  · by_contra! hh
    have hnot := htrap.1 (show quotientMap x ∈ normalCap (quotientMap a) n r (ε * r) from
      ⟨hd, by simpa only [hl] using hh⟩)
    exact hnot (frontier_subset_closure hb)

theorem normalMeasure_trapped_test_derivative_zero {E : Set Torus} (hE : IsOpen E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {a n : Cover} {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hs : tsupport ψ ⊆ Metric.ball a r)
    (hstrip : ∀ x, |⟪n, x - a⟫| ≤ ε * r → fderiv ℝ ψ x n = 0) :
    ∀ᵐ z ∂(μ : Measure NormalBundle), fderiv ℝ ψ z.1 n = 0 := by
  filter_upwards [normalMeasure_frontier_ae hE.measurableSet hμ] with z hz
  by_cases hsupp : (z.1 : Cover) ∈ tsupport ψ
  · exact hstrip _ (trapped_frontier_height hE hrsmall htrap (hs hsupp) hz)
  · rw [fderiv_of_notMem_tsupport ℝ hsupp]
    rfl

theorem weakCMC_trapped_scalar_identity {E : Set Torus} (hE : IsOpen E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ} (hrsmall : r < 1 / 2)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure E)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ E)
    {ψ : Cover → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : tsupport ψ ⊆ Metric.ball a r)
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hstrip : ∀ x, |⟪n, x - a⟫| ≤ ε * r → fderiv ℝ ψ x n = 0) :
    (∫ x : Cover, characteristic E (quotientMap x) * divergence (gradient ψ) x) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  have hc : HasCompactSupport ψ := (isCompact_closedBall a r).of_isClosed_subset isClosed_closure
    (hs.trans Metric.ball_subset_closedBall)
  have hi := weakCMC_scalar_residual_identity hE.measurableSet hμ hH hn hψ hc
    (hs.trans (Metric.ball_subset_closedBall.trans hcell))
  have hz : (∫ z, fderiv ℝ ψ z.1 n ∂(μ : Measure NormalBundle)) = 0 :=
    integral_eq_zero_of_ae (normalMeasure_trapped_test_derivative_zero hE hμ hrsmall htrap hs hstrip)
  simpa only [hz, sub_zero] using hi

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
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
open Laplacian
namespace CubicTorus

lemma fderiv_gradient_inner {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : Cover) :
    ⟪fderiv ℝ (gradient f) x u, v⟫ = fderiv ℝ (fderiv ℝ f) x u v := by
  have hd := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hh := ((InnerProductSpace.toDual ℝ Cover).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp
    x (hd x).hasFDerivAt).fderiv
  change fderiv ℝ (gradient f) x = _ at hh
  rw [hh]
  change ⟪(InnerProductSpace.toDual ℝ Cover).symm (fderiv ℝ (fderiv ℝ f) x u), v⟫ = _
  exact InnerProductSpace.toDual_symm_apply

lemma divergence_gradient_eq_laplacian {f : Cover → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Cover) :
    divergence (gradient f) x = Δ f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.inner_single_right,
    RCLike.conj_to_real, mul_one, one_mul] using
    fderiv_gradient_inner hf x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

lemma iteratedFDeriv_two_line {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u : X) :
    iteratedFDeriv ℝ 2 f x ![u, u] =
      iteratedDeriv 2 (fun t : ℝ ↦ f (x + t • u)) 0 := by
  let L : ℝ →L[ℝ] X := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f (x + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hh := L.iteratedFDeriv_comp_right ht 0
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hh' := congrArg (fun A ↦ A (fun _ : Fin 2 ↦ (1 : ℝ))) hh
  have hv : (fun _ : Fin 2 ↦ u) = ![u, u] := by
    funext j
    fin_cases j <;> rfl
  simpa [iteratedDeriv, L, Function.comp_def, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hv] using hh'.symm

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

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_eq_sum_directional {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y ((stdOrthonormalBasis ℝ X) i)) x
      ((stdOrthonormalBasis ℝ X) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply hf]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma compact_laplacian_continuous {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (Δ f) := by
  have he : Δ f = fun x ↦ ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y
      ((stdOrthonormalBasis ℝ X) i)) x ((stdOrthonormalBasis ℝ X) i) :=
    funext (laplacian_eq_sum_directional hf)
  rw [he]
  apply continuous_finsetSum
  intro i _
  have ht := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply (contDiff_const
    (c := (stdOrthonormalBasis ℝ X) i))
  exact (ht.continuous_fderiv (by simp)).clm_apply continuous_const

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_tsupport_subset {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (Δ f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  apply hx
  rw [laplacian_eq_sum_directional hf]
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hn ((tsupport_fderiv_apply_subset ℝ _ ) hh))]
  rfl

lemma integral_compact_laplacian_zero {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    (∫ x, Δ f x ∂μ) = 0 := by
  have hd (i : Fin (Module.finrank ℝ X)) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ fderiv ℝ f x ((stdOrthonormalBasis ℝ X) i)) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  simp_rw [laplacian_eq_sum_directional hf]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_compact_fderiv_zero (hd i) (hs.fderiv_apply ℝ _) _
  · intro i _
    exact (((hd i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVColumnHeight
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

lemma measurable_normalColumnHeight {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) : Measurable (normalColumnHeight U a n r) := by
  have hc : Continuous (fun p : Plane × ℝ ↦
      a + quotientMap (normalPlaneEmbedding n p.1 + p.2 • n)) :=
    continuous_const.add (continuous_quotientMap.comp
      (((normalPlaneLinearIsometry n).continuous.comp continuous_fst).add
        (continuous_snd.smul continuous_const)))
  exact (((measurable_characteristic hU).comp hc.measurable).stronglyMeasurable.integral_prod_right').measurable.sub_const _

lemma normalColumn_integrable {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (y : Plane) :
    IntegrableOn (fun t ↦ characteristic U
      (a + quotientMap (normalPlaneEmbedding n y + t • n))) (Icc (-r / 4) (r / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact ((measurable_characteristic hU).comp
      (continuous_const.add (continuous_quotientMap.comp
        (continuous_const.add (continuous_id.smul continuous_const)))).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun t ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U _

lemma normalColumnHeight_bound {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) (y : Plane) :
    |normalColumnHeight U a n r y| ≤ r / 4 := by
  have hi := normalColumn_integrable hU a n r y
  have hlo : 0 ≤ ∫ t in Icc (-r / 4) (r / 4),
      characteristic U (a + quotientMap (normalPlaneEmbedding n y + t • n)) :=
    integral_nonneg (fun t ↦ characteristic_nonneg U _)
  have hhi := integral_mono hi (integrable_const (1 : ℝ)) (fun t ↦
    (le_abs_self _).trans (characteristic_bound U _))
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ r / 4 - -r / 4)] at hhi
  dsimp [normalColumnHeight]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma normalScalarTest_contDiff (a n : Cover) {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalScalarTest a n χ φ) := by
  exact (hχ.comp (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const))).mul
    (hφ.comp ((normalPlaneCoordinates n).contDiff.comp (contDiff_id.sub contDiff_const)))

lemma normalRotation_single_succ (n : Cover) (i : Fin 2) :
    normalRotation n (EuclideanSpace.single i.succ 1) =
      normalPlaneEmbedding n (EuclideanSpace.single i 1) := by
  rw [normalPlaneEmbedding, normalProductChart_apply]
  congr 1
  ext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp
  · simp [Pi.single_apply]

lemma normalScalarTest_normal_line (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) (t : ℝ) :
    normalScalarTest a n χ φ (x + t • n) =
      χ (⟪n, x - a⟫ + t) * φ (normalPlaneCoordinates n (x - a)) := by
  have he : x + t • n - a = (x - a) + t • n := by abel
  rw [normalScalarTest, he, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
    hn, one_pow, mul_one, map_add, map_smul, normalPlaneCoordinates_normal hn,
    smul_zero, add_zero]

lemma normalScalarTest_plane_line (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (χ : ℝ → ℝ) (φ : Plane → ℝ) (x : Cover) (u : Plane) (t : ℝ) :
    normalScalarTest a n χ φ (x + t • normalPlaneEmbedding n u) =
      χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a) + t • u) := by
  have he : x + t • normalPlaneEmbedding n u - a =
      (x - a) + t • normalPlaneEmbedding n u := by abel
  rw [normalScalarTest, he, inner_add_right, inner_smul_right,
    normalPlaneEmbedding_inner hn, mul_zero, add_zero, map_add, map_smul,
    normalPlaneCoordinates_embedding]

theorem laplacian_normalScalarTest (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) :
    Δ (normalScalarTest a n χ φ) x =
      iteratedDeriv 2 χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) +
      χ ⟪n, x - a⟫ * Δ φ (normalPlaneCoordinates n (x - a)) := by
  have htest := normalScalarTest_contDiff a n hχ hφ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map (normalRotation n))]
  simp only [OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply]
  rw [Fin.sum_univ_succ, normalRotation_axis hn]
  have hv : iteratedFDeriv ℝ 2 (normalScalarTest a n χ φ) x ![n, n] =
      iteratedDeriv 2 χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) := by
    rw [iteratedFDeriv_two_line htest]
    simp_rw [normalScalarTest_normal_line a hn]
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_comp_const_add]
    simp
  rw [hv]
  congr 1
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin 2) ℝ), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalRotation_single_succ, iteratedFDeriv_two_line htest]
  simp_rw [normalScalarTest_plane_line a hn]
  rw [iteratedDeriv_const_mul_field, EuclideanSpace.basisFun_apply,
    iteratedFDeriv_two_line hφ]

lemma fderiv_normalScalarTest_normal (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) :
    fderiv ℝ (normalScalarTest a n χ φ) x n =
      deriv χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) := by
  have htest := normalScalarTest_contDiff a n hχ hφ
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • n) n 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_add x
  have hh := (((htest.differentiable (by simp)) (x + (0 : ℝ) • n)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt (fun t : ℝ ↦ x + t • n) n 0 from hl))
  have hh' : deriv (fun t : ℝ ↦ normalScalarTest a n χ φ (x + t • n)) 0 =
      fderiv ℝ (normalScalarTest a n χ φ) x n := by
    simpa [Function.comp_def] using hh.deriv
  rw [← hh']
  have he := funext (normalScalarTest_normal_line a hn χ φ x)
  rw [he, deriv_mul_const, deriv_comp_const_add]
  · simp
  · exact (hχ.comp (contDiff_const.add contDiff_id)).differentiable (by simp) |>.differentiableAt

lemma normalScalarTest_tsupport (a n : Cover) (χ : ℝ → ℝ) (φ : Plane → ℝ) :
    tsupport (normalScalarTest a n χ φ) ⊆
      {x | ⟪n, x - a⟫ ∈ tsupport χ} ∩
        {x | normalPlaneCoordinates n (x - a) ∈ tsupport φ} := by
  apply closure_minimal _
    ((isClosed_closure.preimage (continuous_const.inner (continuous_id.sub continuous_const))).inter
      (isClosed_closure.preimage ((normalPlaneCoordinates n).continuous.comp
        (continuous_id.sub continuous_const))))
  intro x hx
  have hnz : χ ⟪n, x - a⟫ * φ (normalPlaneCoordinates n (x - a)) ≠ 0 := hx
  exact ⟨subset_tsupport _ (left_ne_zero_of_mul hnz),
    subset_tsupport _ (right_ne_zero_of_mul hnz)⟩

end CubicTorus

end
end

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

lemma normalColumnChart_characteristic (U : Set Torus) (a : Cover) {n : Cover}
    (hn : ‖n‖ = 1) (t : ℝ) (y : Plane) :
    characteristic U (quotientMap (normalColumnChart a n (t, y))) =
      characteristic U (quotientMap a + quotientMap (normalPlaneEmbedding n y + t • n)) := by
  rw [normalColumnChart_apply a hn, quotientMap_add]

lemma normalColumnChart_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {r t : ℝ} (hr : 0 < r) {y : Plane} (ht : |t| ≤ r / 2)
    (hy : ‖y‖ ≤ r / 3) : normalColumnChart a n (t, y) ∈ Metric.ball a r := by
  rw [Metric.mem_ball, dist_eq_norm, normalColumnChart_apply a hn, add_sub_cancel_left]
  have hh := norm_add_le (normalPlaneEmbedding n y) (t • n)
  rw [normalPlaneEmbedding_norm, norm_smul, Real.norm_eq_abs, hn, mul_one] at hh
  linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVAnnulusSelection
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma centered_scale_laplacian_pairing {f φ : Plane → ℝ} (hf : Continuous f)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : HasCompactSupport φ) (a m : ℝ) :
    (∫ x, (a * (f x - m)) * Δ φ x) = a * ∫ x, f x * Δ φ x := by
  have hl : Continuous (Δ φ) := compact_laplacian_continuous hφ
  have hls : HasCompactSupport (Δ φ) := hs.mono'
    ((subset_tsupport _).trans (laplacian_tsupport_subset hφ))
  have hi : Integrable (fun x ↦ f x * Δ φ x) :=
    (hf.mul hl).integrable_of_hasCompactSupport hls.mul_left
  have hli : Integrable (Δ φ) := hl.integrable_of_hasCompactSupport hls
  simp_rw [mul_assoc, sub_mul]
  rw [integral_const_mul, integral_sub hi (hli.const_mul m), integral_const_mul,
    integral_compact_laplacian_zero hφ hs, mul_zero, sub_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma normalColumnCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (normalColumnCutoff r hr) ⊆ Icc (-r / 2) (r / 2) := by
  rw [(normalColumnCutoff r hr).tsupport_eq]
  intro t ht
  have hh : |t| ≤ r / 2 := by simpa [normalColumnCutoff, Real.norm_eq_abs] using ht
  exact ⟨by linarith [(abs_le.mp hh).1], (abs_le.mp hh).2⟩

lemma normalColumnCutoff_eventually_one {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    (normalColumnCutoff r hr : ℝ → ℝ) =ᶠ[𝓝 t] (fun _ ↦ (1 : ℝ)) := by
  apply (normalColumnCutoff r hr).eventuallyEq_one_of_mem_ball
  change dist t 0 < r / 3
  rw [dist_zero_right, Real.norm_eq_abs]
  linarith

lemma normalColumnCutoff_one {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    normalColumnCutoff r hr t = 1 :=
  (normalColumnCutoff_eventually_one hr ht).eq_of_nhds

lemma normalColumnCutoff_deriv_zero {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    deriv (normalColumnCutoff r hr) t = 0 := by
  rw [(normalColumnCutoff_eventually_one hr ht).deriv_eq]
  simp

lemma normalColumnCutoff_second_zero {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    iteratedDeriv 2 (normalColumnCutoff r hr) t = 0 := by
  rw [((normalColumnCutoff_eventually_one hr ht).iteratedDeriv 2).eq_of_nhds]
  simp [iteratedDeriv_const]

lemma normalColumnTest_tsupport_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {r : ℝ} (hr : 0 < r) {φ : Plane → ℝ}
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    tsupport (normalScalarTest a n (normalColumnCutoff r hr) φ) ⊆ Metric.ball a r := by
  intro x hx
  have hh := normalScalarTest_tsupport a n (normalColumnCutoff r hr) φ hx
  have hv : |⟪n, x - a⟫| ≤ r / 2 := by
    have ht := normalColumnCutoff_tsupport hr hh.1
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hp : ‖normalPlaneCoordinates n (x - a)‖ ≤ r / 3 := by simpa using hφ hh.2
  have htri := norm_add_le (normalPlaneEmbedding n (normalPlaneCoordinates n (x - a)))
    (⟪n, x - a⟫ • n)
  rw [normalPlaneCoordinates_reconstruct hn, normalPlaneEmbedding_norm, norm_smul,
    Real.norm_eq_abs, hn, mul_one] at htri
  change dist x a < r
  rw [dist_eq_norm]
  linarith

lemma trapped_column_characteristic {U : Set Torus} {a n : Cover} (hn : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {y : Plane} (hy : ‖y‖ ≤ r / 3) {t : ℝ} (ht : |t| ≤ r / 2)
    (htout : r / 4 ≤ |t|) :
    characteristic U (quotientMap (normalColumnChart a n (t, y))) =
      (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t := by
  let x := normalColumnChart a n (t, y)
  have hx := normalColumnChart_ball a hn hr ht hy
  have hl : shortestLift (quotientMap x - quotientMap a) = x - a := by
    rw [← quotientMap_sub]
    exact shortestLift_quotientMap ((show ‖x - a‖ < r by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx).trans hrsmall)
  have hd : dist (quotientMap x) (quotientMap a) < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hl]
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hnxt : ⟪n, shortestLift (quotientMap x - quotientMap a)⟫ = t := by
    rw [hl]
    exact normalColumnChart_height a hn t y
  have her : ε * r < r / 4 := by nlinarith
  change characteristic U (quotientMap x) = _
  by_cases htneg : t < 0
  · have hU : quotientMap x ∈ U := by
      apply htrap.2
      refine ⟨hd, ?_⟩
      rw [inner_neg_left, hnxt]
      rw [abs_of_neg htneg] at htout
      linarith
    simp [characteristic, hU, htneg]
  · have hU : quotientMap x ∉ U := by
      apply fun h ↦ htrap.1 (show quotientMap x ∈ normalCap (quotientMap a) n r (ε * r) from
        ⟨hd, by rw [hnxt]; rw [abs_of_nonneg (le_of_not_gt htneg)] at htout; linarith⟩)
        (subset_closure h)
    simp [characteristic, hU, htneg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_column_negative_indicator {r : ℝ} (hr : 0 < r) :
    (∫ t in Icc (-r / 4) (r / 4), (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) = r / 4 := by
  rw [setIntegral_indicator measurableSet_Iio]
  have he : Icc (-r / 4) (r / 4) ∩ Iio (0 : ℝ) = Ico (-r / 4) 0 := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩
  rw [he, integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith : 0 ≤ 0 - -r / 4)]
  ring

lemma integrableOn_column_bounded {r : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t, ‖f t‖ ≤ 1) : IntegrableOn f (Icc (-r / 4) (r / 4)) := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ hb)

lemma integral_column_cutoff {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∀ t, ‖f t‖ ≤ 1)
    (hphase : ∀ t, |t| ≤ r / 2 → r / 4 ≤ |t| →
      f t = (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) :
    (∫ t : ℝ, f t * normalColumnCutoff r hr t) =
      (∫ t in Icc (-r / 4) (r / 4), f t) - r / 4 +
        ∫ t in Iio (0 : ℝ), normalColumnCutoff r hr t := by
  let χ := normalColumnCutoff r hr
  let h : ℝ → ℝ := (Iio (0 : ℝ)).indicator (fun _ ↦ 1)
  let I := Icc (-r / 4) (r / 4)
  have hm : Measurable h := measurable_const.indicator measurableSet_Iio
  have hb' (t : ℝ) : ‖h t‖ ≤ 1 := by
    by_cases ht : t < 0 <;> simp [h, ht]
  have hfi : IntegrableOn f I := integrableOn_column_bounded hf hb
  have hhi : IntegrableOn h I := integrableOn_column_bounded hm hb'
  have hχi : Integrable (fun t ↦ h t * χ t) :=
    (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).bdd_mul
      hm.aestronglyMeasurable (ae_of_all _ hb')
  have he (t : ℝ) : f t * χ t = I.indicator (fun s ↦ f s - h s) t + h t * χ t := by
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      have habs : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      rw [show χ t = 1 from normalColumnCutoff_one hr habs]
      ring
    · rw [indicator_of_notMem ht, zero_add]
      by_cases hs : t ∈ tsupport χ
      · have hs' := normalColumnCutoff_tsupport hr hs
        have hu : |t| ≤ r / 2 := abs_le.mpr ⟨by linarith [hs'.1], hs'.2⟩
        have hlo : r / 4 ≤ |t| := by
          by_contra! hn
          apply ht
          exact ⟨by linarith [(abs_lt.mp hn).1], (abs_lt.mp hn).2.le⟩
        rw [hphase t hu hlo]
      · rw [image_eq_zero_of_notMem_tsupport hs]
        simp
  change (∫ t : ℝ, f t * χ t) = _
  simp_rw [he]
  have hdiff : Integrable (I.indicator (fun s ↦ f s - h s)) := by
    exact hfi.integrable_indicator measurableSet_Icc |>.sub
      (hhi.integrable_indicator measurableSet_Icc) |>.congr (ae_of_all _ fun t ↦ by
        by_cases ht : t ∈ I <;> simp [ht])
  rw [integral_add hdiff hχi,
    integral_indicator measurableSet_Icc, integral_sub hfi hhi]
  change (∫ t in I, f t) - (∫ t in I, h t) + (∫ t, h t * χ t) = _
  rw [show (∫ t in I, h t) = r / 4 from integral_column_negative_indicator hr]
  congr 1
  simp only [h, ← indicator_mul_left, one_mul, integral_indicator measurableSet_Iio]
  rfl

lemma integral_column_cutoff_second {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hphase : ∀ t, |t| ≤ r / 2 → r / 4 ≤ |t| →
      f t = (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) :
    (∫ t : ℝ, f t * iteratedDeriv 2 (normalColumnCutoff r hr) t) = 0 := by
  let χ := normalColumnCutoff r hr
  have he (t : ℝ) : f t * iteratedDeriv 2 χ t =
      (Iio (0 : ℝ)).indicator (iteratedDeriv 2 χ) t := by
    by_cases ht : |t| ≤ r / 4
    · have hz : iteratedDeriv 2 χ t = 0 := normalColumnCutoff_second_zero hr ht
      by_cases hneg : t < 0 <;> simp [hneg, hz]
    · by_cases hs : t ∈ tsupport χ
      · have hs' := normalColumnCutoff_tsupport hr hs
        have hu : |t| ≤ r / 2 := abs_le.mpr ⟨by linarith [hs'.1], hs'.2⟩
        rw [hphase t hu (le_of_not_ge ht)]
        simp only [← indicator_mul_left, one_mul]
      · have hz : iteratedDeriv 2 χ t = 0 := by
          have h0 : (χ : ℝ → ℝ) =ᶠ[𝓝 t] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hs
          simpa [iteratedDeriv_const] using (h0.iteratedDeriv 2).eq_of_nhds
        by_cases hneg : t < 0 <;> simp [hneg, hz]
  change (∫ t : ℝ, f t * iteratedDeriv 2 χ t) = 0
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    show iteratedDeriv 2 (χ : ℝ → ℝ) = deriv (deriv χ) from by
      rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]]
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) := by
    simpa using (χ.contDiff : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ)).iterate_deriv 1
  rw [χ.hasCompactSupport.deriv.integral_Iic_deriv_eq (hd.of_le (by simp))]
  exact normalColumnCutoff_deriv_zero hr (by simp; positivity)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma columnCutoff_second_contDiff {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 (normalColumnCutoff r hr)) := by
  rw [iteratedDeriv_eq_iterate]
  exact (normalColumnCutoff r hr).contDiff.iterate_deriv 2

lemma columnCutoff_second_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (iteratedDeriv 2 (normalColumnCutoff r hr)) := by
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  exact (normalColumnCutoff r hr).hasCompactSupport.deriv.deriv

theorem integral_column_laplacian {U : Set Torus} (hU : MeasurableSet U)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    (∫ x : Cover, characteristic U (quotientMap x) *
      Δ (normalScalarTest a n (normalColumnCutoff r hr) φ) x) =
      ∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y := by
  let χ := normalColumnCutoff r hr
  let ψ := normalScalarTest a n χ φ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ) := χ.contDiff
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := normalScalarTest_contDiff a n hχ hφ
  have hψs : HasCompactSupport ψ := (isCompact_closedBall a r).of_isClosed_subset isClosed_closure
    ((normalColumnTest_tsupport_ball a hn hr hs).trans Metric.ball_subset_closedBall)
  have hψi : Integrable (Δ ψ) := (compact_laplacian_continuous hψ).integrable_of_hasCompactSupport
    (hψs.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hψ))
  have hbulk : Integrable (fun x : Cover ↦ characteristic U (quotientMap x) * Δ ψ x) :=
    hψi.bdd_mul ((measurable_characteristic hU).comp measurable_quotientMap).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U (quotientMap x))
  have hφs : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (r / 3)).of_isClosed_subset
    isClosed_closure hs
  have hφi : Integrable (Δ φ) := (compact_laplacian_continuous hφ).integrable_of_hasCompactSupport
    (hφs.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hφ))
  let C := ∫ t in Iio (0 : ℝ), χ t
  have he (y : Plane) :
      (∫ t : ℝ, characteristic U (quotientMap (normalColumnChart a n (t, y))) *
        Δ ψ (normalColumnChart a n (t, y))) =
        normalColumnHeight U (quotientMap a) n r y * Δ φ y + C * Δ φ y := by
    have hl (t : ℝ) : Δ ψ (normalColumnChart a n (t, y)) =
        iteratedDeriv 2 χ t * φ y + χ t * Δ φ y := by
      rw [laplacian_normalScalarTest a hn hχ hφ,
        normalColumnChart_height a hn, normalColumnChart_projection a hn]
    simp_rw [hl]
    by_cases hy : y ∈ tsupport φ
    · have hyn : ‖y‖ ≤ r / 3 := by simpa using hs hy
      let f : ℝ → ℝ := fun t ↦ characteristic U (quotientMap (normalColumnChart a n (t, y)))
      have hfm : Measurable f := (measurable_characteristic hU).comp
        (measurable_quotientMap.comp ((normalColumnChart a n).measurable.comp
          (measurable_id.prodMk measurable_const)))
      have hfb (t : ℝ) : ‖f t‖ ≤ 1 := by
        simpa only [f, Real.norm_eq_abs] using characteristic_bound U
          (quotientMap (normalColumnChart a n (t, y)))
      have hphase := fun t ht ho ↦ trapped_column_characteristic hn hr hrsmall hε htrap hyn
        (t := t) ht ho
      have hfχ : Integrable (fun t ↦ f t * χ t) :=
        (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).bdd_mul
          hfm.aestronglyMeasurable (ae_of_all _ hfb)
      have hfχ2 : Integrable (fun t ↦ f t * iteratedDeriv 2 χ t) :=
        ((columnCutoff_second_contDiff hr).continuous.integrable_of_hasCompactSupport
          (columnCutoff_second_hasCompactSupport hr)).bdd_mul
            hfm.aestronglyMeasurable (ae_of_all _ hfb)
      change (∫ t : ℝ, f t * (iteratedDeriv 2 χ t * φ y + χ t * Δ φ y)) = _
      simp_rw [mul_add, ← mul_assoc]
      rw [integral_add (hfχ2.mul_const _) (hfχ.mul_const _), integral_mul_const, integral_mul_const,
        integral_column_cutoff_second hr hphase, zero_mul, zero_add,
        integral_column_cutoff hr hfm hfb hphase]
      have hfcol : (∫ t in Icc (-r / 4) (r / 4), f t) - r / 4 =
          normalColumnHeight U (quotientMap a) n r y := by
        unfold normalColumnHeight
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        exact normalColumnChart_characteristic U a hn t y
      rw [hfcol]
      ring
    · have hzφ := image_eq_zero_of_notMem_tsupport hy
      have hzΔ := image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (laplacian_tsupport_subset hφ hh))
      simp [hzφ, hzΔ]
  have hheighti : Integrable (fun y : Plane ↦ normalColumnHeight U (quotientMap a) n r y * Δ φ y) :=
    hφi.bdd_mul (measurable_normalColumnHeight hU (quotientMap a) n r).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs] using
        normalColumnHeight_bound hU (quotientMap a) n hr.le y)
  change (∫ x : Cover, characteristic U (quotientMap x) * Δ ψ x) = _
  rw [integral_normalColumnChart a n hbulk]
  simp_rw [he]
  rw [integral_add hheighti (hφi.const_mul C), integral_const_mul,
    integral_compact_laplacian_zero hφ hφs, mul_zero, add_zero]

theorem weakCMC_column_height_identity {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    let ψ := normalScalarTest a n (normalColumnCutoff r hr) φ
    (∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  dsimp only
  let χ := normalColumnCutoff r hr
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ) := χ.contDiff
  have ht := weakCMC_trapped_scalar_identity hU hμ hH hn hrsmall htrap
    (normalScalarTest_contDiff a n hχ hφ) (normalColumnTest_tsupport_ball a hn hr hs) hcell
    (fun x hx ↦ by
      rw [fderiv_normalScalarTest_normal a hn hχ hφ,
        normalColumnCutoff_deriv_zero hr (hx.trans (by nlinarith : ε * r ≤ r / 4)), zero_mul])
  simp_rw [divergence_gradient_eq_laplacian (normalScalarTest_contDiff a n hχ hφ)] at ht
  rw [integral_column_laplacian hU.measurableSet hn hr hrsmall hε htrap hφ hs] at ht
  exact ht

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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
open Laplacian
namespace CubicTorus

theorem weakCMC_column_height_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {w : NormalBundle → ℝ} (hw : Integrable w (μ : Measure NormalBundle))
    (hb : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1‖ *
        ‖(z.2 : Cover) - n‖ ^ 2 ≤ w z) :
    |(∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
      H * (∫ z, normalScalarTest a n (normalColumnCutoff r hr) φ z.1 *
        ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle))| ≤
      (1 / 2 : ℝ) * ∫ z, w z ∂(μ : Measure NormalBundle) := by
  rw [weakCMC_column_height_identity hU hμ hH hn hr hrsmall hε htrap hφ hs hcell,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hw
  filter_upwards [hb] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hd : |fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1
      (z.2 : Cover)| ≤ ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1‖ := by
    simpa only [Real.norm_eq_abs, z.2.property, mul_one] using
      (fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) z.1).le_opNorm (z.2 : Cover)
  exact (mul_le_mul_of_nonneg_left hd (sq_nonneg _)).trans (by simpa only [mul_comm] using hz)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma normalColumnTest_fderiv_le {r : ℝ} (hr : 0 < r) (a n x : Cover)
    {φ : Plane → ℝ} (hφ : Differentiable ℝ φ) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ φ y‖ ≤ D) (hx : |⟪n, x - a⟫| ≤ r / 4) :
    ‖fderiv ℝ (normalScalarTest a n (normalColumnCutoff r hr) φ) x‖ ≤ D := by
  have ht : ContinuousAt (fun y : Cover ↦ ⟪n, y - a⟫) x :=
    (continuous_const.inner (continuous_id.sub continuous_const)).continuousAt
  have he := (normalColumnCutoff_eventually_one hr hx).comp_tendsto ht
  have heq : normalScalarTest a n (normalColumnCutoff r hr) φ =ᶠ[𝓝 x]
      (fun y ↦ φ (normalPlaneCoordinates n (y - a))) := by
    filter_upwards [he] with y hy
    simp only [Function.comp_def] at hy
    simp only [normalScalarTest, hy, one_mul]
  rw [heq.fderiv_eq]
  have hd := (hφ (normalPlaneCoordinates n (x - a))).hasFDerivAt.comp x
    ((normalPlaneCoordinates n).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a))
  simp only [Function.comp_def, id_eq] at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_id]
  exact ((fderiv ℝ φ (normalPlaneCoordinates n (x - a))).opNorm_comp_le _).trans
    ((mul_le_of_le_one_right (norm_nonneg _) (norm_normalPlaneCoordinates_le n)).trans (hD _))

theorem weakCMC_column_residual_bound {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {B D : ℝ} (_hB : 0 ≤ B) (_hD : 0 ≤ D)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D) :
    |∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y| ≤
      (D / 2) * (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) +
      |H| * B * (μ : Measure NormalBundle).real
        {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} := by
  let S : Set NormalBundle := {z | (z.1 : Cover) ∈ Metric.ball a r}
  let ψ := normalScalarTest a n (normalColumnCutoff r hr) φ
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  have hν : Continuous (fun z : NormalBundle ↦ (z.2 : Cover)) :=
    continuous_subtype_val.comp continuous_snd
  have hS : MeasurableSet S := measurableSet_ball.preimage hx.measurable
  have htest : tsupport ψ ⊆ Metric.ball a r := normalColumnTest_tsupport_ball a hn hr hs
  have htilt : Integrable (fun z : NormalBundle ↦ ‖(z.2 : Cover) - n‖ ^ 2)
      (μ : Measure NormalBundle) :=
    ((hν.sub continuous_const).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (S.indicator (fun z : NormalBundle ↦ D * ‖(z.2 : Cover) - n‖ ^ 2))
      (μ : Measure NormalBundle) := (htilt.const_mul D).indicator hS
  have hbound : ∀ᵐ z ∂(μ : Measure NormalBundle),
      ‖fderiv ℝ ψ z.1‖ * ‖(z.2 : Cover) - n‖ ^ 2 ≤
        S.indicator (fun z : NormalBundle ↦ D * ‖(z.2 : Cover) - n‖ ^ 2) z := by
    filter_upwards [normalMeasure_frontier_ae hU.measurableSet hμ] with z hz
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS]
      have hh := trapped_frontier_height hU hrsmall htrap hzS hz
      have hh' : |⟪n, (z.1 : Cover) - a⟫| ≤ r / 4 := hh.trans (by nlinarith)
      exact mul_le_mul_of_nonneg_right
        (normalColumnTest_fderiv_le hr a n z.1 (hφ.differentiable (by simp)) hd hh')
        (sq_nonneg _)
    · rw [indicator_of_notMem hzS, fderiv_of_notMem_tsupport ℝ
        (show (z.1 : Cover) ∉ tsupport ψ from fun hz ↦ hzS (htest hz))]
      simp
  have hres := weakCMC_column_height_residual hU hμ hH hn hr hrsmall hε htrap
    hφ hs hcell hw hbound
  rw [integral_indicator hS, integral_const_mul] at hres
  have hval : ∀ z : NormalBundle, |ψ z.1 * ⟪(z.2 : Cover), n⟫| ≤ S.indicator (fun _ ↦ B) z := by
    intro z
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS, abs_mul]
      have hh : |⟪(z.2 : Cover), n⟫| ≤ 1 := by
        simpa only [z.2.property, hn, one_mul] using abs_real_inner_le_norm (z.2 : Cover) n
      have hp : |ψ z.1| ≤ B := by
        dsimp [ψ, normalScalarTest]
        rw [abs_mul, abs_of_nonneg ((normalColumnCutoff r hr).nonneg)]
        exact (mul_le_of_le_one_left (abs_nonneg _)
          ((normalColumnCutoff r hr).le_one)).trans (hb _)
      exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans (by simpa only [mul_one] using hp)
    · rw [indicator_of_notMem hzS]
      have hp : ψ z.1 = 0 := image_eq_zero_of_notMem_tsupport
        (show (z.1 : Cover) ∉ tsupport ψ from fun hz ↦ hzS (htest hz))
      simp [hp]
  have hi : |∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)| ≤
      B * (μ : Measure NormalBundle).real S := by
    rw [← Real.norm_eq_abs]
    have hh : ‖∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)‖ ≤
        ∫ z : NormalBundle, S.indicator (fun _ ↦ B) z ∂(μ : Measure NormalBundle) :=
      norm_integral_le_of_norm_le ((integrable_const B).indicator hS)
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using hval z)
    simpa only [integral_indicator hS, integral_const, smul_eq_mul, mul_comm, measureReal_def, Measure.restrict_apply_univ] using hh
  have ht := abs_add_le ((∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
    H * (∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)))
    (-(H * (∫ z : NormalBundle, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle))))
  simp only [add_neg_cancel_right, abs_neg, abs_mul] at ht
  have hi' := mul_le_mul_of_nonneg_left hi (abs_nonneg H)
  dsimp only [ψ] at hi' ht
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma integral_pairing_local_error {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {f g q : X → ℝ} {S : Set X} (hS : MeasurableSet S)
    (hf : Integrable (fun x ↦ f x * q x) ν)
    (hg : Integrable (fun x ↦ g x * q x) ν)
    (he : IntegrableOn (fun x ↦ g x - f x) S ν)
    (hqzero : ∀ x ∉ S, q x = 0) {Q : ℝ}
    (hq : ∀ x, |q x| ≤ Q) :
    |(∫ x, g x * q x ∂ν) - ∫ x, f x * q x ∂ν| ≤
      Q * ∫ x in S, |g x - f x| ∂ν := by
  rw [← integral_sub hg hf, ← Real.norm_eq_abs]
  have he' : Integrable (S.indicator (fun x ↦ Q * |g x - f x|)) ν :=
    IntegrableOn.integrable_indicator (he.abs.const_mul Q) hS
  have hb : ∀ x, ‖g x * q x - f x * q x‖ ≤ S.indicator (fun x ↦ Q * |g x - f x|) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← sub_mul, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hq x) (abs_nonneg _)).trans_eq (mul_comm _ _)
    · rw [indicator_of_notMem hx, hqzero x hx]
      simp
  have hh := norm_integral_le_of_norm_le he' (Eventually.of_forall hb)
  simpa only [integral_indicator hS, integral_const_mul] using hh

theorem weakCMC_graph_residual_bound {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (r / 4))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) {g : Plane → ℝ} (hg : Continuous g) :
    |∫ y : Plane, g y * Δ φ y| ≤
      (D / 2) * (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) +
      |H| * B * (μ : Measure NormalBundle).real
        {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} +
      Q * (∫ y in Metric.ball (0 : Plane) (r / 4),
        |g y - normalColumnHeight U (quotientMap a) n r y|) := by
  let f := normalColumnHeight U (quotientMap a) n r
  have hs' : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3) :=
    hs.trans (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))
  have hres := weakCMC_column_residual_bound hU hμ hH hn hr hrsmall hε htrap
    hφ hs' hcell hB hD hb hd
  have hc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (r / 3)).of_isClosed_subset
    isClosed_closure hs'
  have hcs : HasCompactSupport (Δ φ) := hc.of_isClosed_subset isClosed_closure
    (laplacian_tsupport_subset hφ)
  have hdφ := compact_laplacian_continuous hφ
  have hφi : Integrable (Δ φ) := hdφ.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y ↦ f y * Δ φ y) :=
    hφi.bdd_mul (c := r / 4) (measurable_normalColumnHeight hU.measurableSet _ _ _).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [f, Real.norm_eq_abs] using
        normalColumnHeight_bound hU.measurableSet (quotientMap a) n hr.le y)
  have hgi : Integrable (fun y ↦ g y * Δ φ y) :=
    (hg.mul hdφ).integrable_of_hasCompactSupport hcs.mul_left
  have hfi : IntegrableOn f (Metric.ball (0 : Plane) (r / 4)) :=
    (integrableOn_const (C := r / 4) measure_ball_lt_top.ne).mono'
      (measurable_normalColumnHeight hU.measurableSet _ _ _).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [f, Real.norm_eq_abs] using
        normalColumnHeight_bound hU.measurableSet (quotientMap a) n hr.le y)
  have hgon : IntegrableOn g (Metric.ball (0 : Plane) (r / 4)) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) (r / 4))).mono_set
      Metric.ball_subset_closedBall
  have he := integral_pairing_local_error measurableSet_ball hf hgi (hgon.sub hfi)
    (fun y hy ↦ image_eq_zero_of_notMem_tsupport
      (fun hh ↦ hy (hs (laplacian_tsupport_subset hφ hh)))) hq
  have ht := abs_add_le ((∫ y : Plane, g y * Δ φ y) - ∫ y, f y * Δ φ y)
    (∫ y : Plane, f y * Δ φ y)
  simp only [sub_add_cancel] at ht
  dsimp only [f] at he ht
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma laplacian_comp_smul {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℝ) (x : X) :
    Δ (fun y ↦ f (r • y)) x = r ^ 2 * Δ f (r • x) := by
  let L : X →L[ℝ] X := r • ContinuousLinearMap.id ℝ X
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hh := L.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := congrArg (fun A ↦ A ![(stdOrthonormalBasis ℝ X) i,
    (stdOrthonormalBasis ℝ X) i]) hh
  have hm := (iteratedFDeriv ℝ 2 f (r • x)).map_smul_univ (fun _ ↦ r)
    (![(stdOrthonormalBasis ℝ X) i, (stdOrthonormalBasis ℝ X) i])
  simp only [Fin.prod_univ_two, smul_eq_mul] at hm
  simpa only [L, Function.comp_def, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ← sq] using he.trans hm

lemma planar_scaled_laplacian_pairing {f φ : Plane → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {r : ℝ} (hr : 0 < r) :
    (∫ y : Plane, f (r • y) * Δ φ y) =
      ∫ y : Plane, f y * Δ (fun z ↦ φ (r⁻¹ • z)) y := by
  have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
    (fun y ↦ f y * Δ (fun z ↦ φ (r⁻¹ • z)) y) r (hR := hr.le)
  have hd : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  simp only [laplacian_comp_smul hφ, inv_smul_smul₀ hr.ne', hd, smul_eq_mul,
    inv_pow] at hh
  have hfun : (fun y : Plane ↦ f (r • y) * ((r ^ 2)⁻¹ * Δ φ y)) =
      (fun y : Plane ↦ (r ^ 2)⁻¹ * (f (r • y) * Δ φ y)) := by
    funext y
    ring
  rw [hfun, integral_const_mul] at hh
  simp_rw [laplacian_comp_smul hφ, inv_pow]
  exact (mul_left_cancel₀ (by positivity : (r ^ 2)⁻¹ ≠ 0) hh)

lemma fderiv_comp_smul_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} {x : X} {r : ℝ} (hf : DifferentiableAt ℝ f (r • x)) :
    fderiv ℝ (fun y ↦ f (r • y)) x = r • fderiv ℝ f (r • x) := by
  have hh := hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  have he : (fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ X) =
      r • fderiv ℝ f (r • x) := by ext y; simp
  simpa only [Function.comp_def, id_eq, he] using hh.fderiv

lemma scaled_test_support {φ : Plane → ℝ} {r R : ℝ} (hr : 0 < r)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) R) :
    tsupport (fun y ↦ φ (r⁻¹ • y)) ⊆ Metric.ball 0 (r * R) := by
  have hh : tsupport (fun y ↦ φ (r⁻¹ • y)) ⊆ (fun y : Plane ↦ r⁻¹ • y) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ (by fun_prop)
  intro y hy
  have hn : ‖r⁻¹ • y‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hs (hh hy)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hn
  change dist y 0 < r * R
  rw [dist_zero_right]
  have hm := mul_lt_mul_of_pos_left hn hr
  simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using hm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVGraphNormalization
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
open Laplacian
namespace CubicTorus

theorem weakCMC_normalized_graph_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε e A C : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4) (he : 0 < e)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (htilt : (∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
      ‖(z.2 : Cover) - n‖ ^ 2 ∂(μ : Measure NormalBundle)) ≤ r ^ 2 * e ^ 2)
    (harea : (μ : Measure NormalBundle).real
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} ≤ A * r ^ 2)
    {g : Plane → ℝ} (hg : Continuous g)
    (hcol : (∫ y in Metric.ball (0 : Plane) (r / 4),
      |g y - normalColumnHeight U (quotientMap a) n r y|) ≤ C * r ^ 3 * e ^ 2)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (1 / 4))
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) (m : ℝ) :
    |∫ y : Plane, ((r * e)⁻¹ * (g (r • y) - m)) * Δ φ y| ≤
      (D / 2 + C * Q) * e + |H| * B * A * (r / e) := by
  let φr : Plane → ℝ := fun y ↦ φ (r⁻¹ • y)
  have hφr : ContDiff ℝ (⊤ : ℕ∞) φr := hφ.comp (by fun_prop)
  have hsr : tsupport φr ⊆ Metric.ball (0 : Plane) (r / 4) := by
    simpa only [mul_one_div] using scaled_test_support hr hs
  have hdr (y : Plane) : ‖fderiv ℝ φr y‖ ≤ D / r := by
    rw [fderiv_comp_smul_eq ((hφ.differentiable (by simp)) _), norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hd _) (inv_nonneg.mpr hr.le)).trans_eq (by ring)
  have hqr (y : Plane) : |Δ φr y| ≤ Q / r ^ 2 := by
    rw [laplacian_comp_smul hφ, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hq _) (sq_nonneg r⁻¹)).trans_eq (by rw [inv_pow]; ring)
  have hres := weakCMC_graph_residual_bound hU hμ hH hn hr hrsmall hε htrap
    hφr hsr hcell hB (by positivity) (fun y ↦ hb _) hdr hqr hg
  have hbnd : |∫ y : Plane, g y * Δ φr y| ≤
      (D / 2 + C * Q) * r * e ^ 2 + |H| * B * A * r ^ 2 := by
    calc
      _ ≤ (D / r / 2) * (r ^ 2 * e ^ 2) +
          |H| * B * (A * r ^ 2) + (Q / r ^ 2) * (C * r ^ 3 * e ^ 2) :=
        hres.trans (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left htilt (by positivity))
          (mul_le_mul_of_nonneg_left harea (by positivity)))
          (mul_le_mul_of_nonneg_left hcol (by positivity)))
      _ = _ := by field_simp; ring
  have hc : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (1 / 4)).of_isClosed_subset
    isClosed_closure (hs.trans Metric.ball_subset_closedBall)
  have hcont : Continuous (fun y : Plane ↦ g (r • y)) := by fun_prop
  rw [centered_scale_laplacian_pairing hcont hφ hc,
    planar_scaled_laplacian_pairing hφ hr, abs_mul,
    abs_of_pos (inv_pos.mpr (mul_pos hr he))]
  have hh := mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr (mul_nonneg hr.le he.le))
  apply hh.trans_eq
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma integral_polar_tilt_ball {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (a n : Cover) (r : ℝ)
    (hc : Metric.ball a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ x in Metric.ball (quotientMap a) r, ‖N x-n‖^2 ∂(spatialNormalMeasure μ : Measure Torus)) =
      ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r},
        ‖(z.2 : Cover)-n‖^2 ∂(μ : Measure NormalBundle) := by
  have hs : MeasurableSet {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (by fun_prop)
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    integral_spatialNormalMeasure μ (((hN.sub_const n).norm.pow_const 2).indicator
      Metric.isOpen_ball.measurableSet), ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [hp] with z hz
  have hm := compactCell_mem_quotient_ball_iff z.1 a r hc
  change (Metric.ball (quotientMap a) r).indicator (fun x ↦ ‖N x-n‖^2) (quotientMap z.1) = _
  by_cases hh : (z.1 : Cover) ∈ Metric.ball a r
  · rw [indicator_of_mem (hm.mpr hh),indicator_of_mem (show z ∈ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh),hz]
  · rw [indicator_of_notMem (mt hm.mp hh),indicator_of_notMem (show z ∉ {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball a r} from hh)]

lemma polar_tilt_integrable {μ : FiniteMeasure NormalBundle} {N : Torus → Cover}
    (hN : Measurable N) (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (n : Cover) : Integrable (fun x ↦ ‖N x-n‖^2) (spatialNormalMeasure μ : Measure Torus) := by
  apply Integrable.of_bound ((hN.sub_const n).norm.pow_const 2).aestronglyMeasurable ((1+‖n‖)^2)
  filter_upwards [hu] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [hx] using norm_sub_le (N x) n) 2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma smooth_compact_test_bounds {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ∃ B D Q : ℝ, 0 ≤ B ∧ 0 ≤ D ∧ 0 ≤ Q ∧
      (∀ y, |φ y| ≤ B) ∧ (∀ y, ‖fderiv ℝ φ y‖ ≤ D) ∧ (∀ y, |Δ φ y| ≤ Q) := by
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨D,hD⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hl : HasCompactSupport (Δ φ) := hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hφ)
  obtain ⟨Q,hQ⟩ := hl.exists_bound_of_continuous (compact_laplacian_continuous hφ)
  exact ⟨max B 0,max D 0,max Q 0,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    fun y ↦ (hB y).trans (le_max_left _ _),fun y ↦ (hD y).trans (le_max_left _ _),
    fun y ↦ (hQ y).trans (le_max_left _ _)⟩

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVInteriorMultiplier
attribute [-instance] _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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
namespace CubicTorus.MovingCenter

lemma coords (c : InteriorCenter) (i : Fin 3) :
    3/8 ≤ (c : Cover) i ∧ (c : Cover) i ≤ 5/8 := by
  have hh := (PiLp.norm_apply_le ((c : Cover)-cubeCenter) i).trans c.property
  change ‖(c : Cover) i-(1/2:ℝ)‖ ≤ 1/8 at hh
  rw [Real.norm_eq_abs, abs_le] at hh
  constructor <;> linarith

variable {c : InteriorCenter}

lemma closedBall_interior {r : ℝ} (hr : r < 3/8) :
    Metric.closedBall (c : Cover) r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := (PiLp.norm_apply_le (x-(c : Cover)) i).trans
    (show ‖x-(c : Cover)‖ ≤ r from hx)
  change ‖x i-(c : Cover) i‖ ≤ r at hh
  rw [Real.norm_eq_abs,abs_le] at hh
  have hc := coords c i
  constructor <;> linarith

end CubicTorus.MovingCenter

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVMovingOrientedReplacement
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem weakCMC_spatial_normalized_residual {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {n : Cover} (hn : ‖n‖ = 1) {r α e A C : ℝ}
    (hr : 0 < r) (hrs : r < 3/8) (hα : α < 1/4) (he : 0 < e)
    (htrap : normalCap (quotientMap (c : Cover)) n r (α*r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap (c : Cover)) (-n) r (α*r) ⊆ U)
    (htilt : (∫ x in Metric.closedBall (quotientMap (c : Cover)) (17*r), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2)
    (ha : (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c : Cover)) r) ≤ A*r^2)
    {g : Plane → ℝ} (hg : Continuous g)
    (hcol : (∫ y in Metric.ball (0 : Plane) (r/4),
      |g y-normalColumnHeight U (quotientMap (c : Cover)) n r y|) ≤ C*r^3*e^2)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.ball (0 : Plane) (1/4))
    {B D Q : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hb : ∀ y, |φ y| ≤ B) (hd : ∀ y, ‖fderiv ℝ φ y‖ ≤ D)
    (hq : ∀ y, |Δ φ y| ≤ Q) (m : ℝ) :
    |∫ y : Plane, graphNormalize r e m g y*Δ φ y| ≤
      (D/2+C*Q)*e+|H| * B*A*(r/e) := by
  have hc := closedBall_interior (c:=c) hrs
  have hcb := Metric.ball_subset_closedBall.trans hc
  apply weakCMC_normalized_graph_residual hU hμ hH hn hr (by linarith) hα he htrap hc
    (g := g) (m := r*m) ?_ ?_ hg hcol hφ hs hB hD hQ hb hd hq
  · rw [← integral_polar_tilt_ball hN hp (c : Cover) n r hcb]
    apply (setIntegral_mono_set (polar_tilt_integrable hN hu n).integrableOn
      (Eventually.of_forall fun x ↦ sq_nonneg _) ?_).trans htilt
    exact (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))).eventuallyLE
  · change cellBallMass μ (c : Cover) r ≤ A*r^2
    rwa [cellBallMass_eq_spatialNormalMeasure μ (c : Cover) r hcb]

end CubicTorus.MovingCenter

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
open Laplacian
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem weakCMC_normalized_sequence_harmonic_oai {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e m C : ℕ → ℝ) (g : ℕ → Plane → ℝ) (A : ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < 3/8)
    (hα : ∀ i, α i < 1/4) (he : ∀ i, 0 < e i)
    (htrap : ∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ U)
    (htilt : ∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2)
    (ha : ∀ i, (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c i : Cover)) (r i)) ≤ A*(r i)^2)
    (hg : ∀ i, Continuous (g i))
    (hcol : ∀ i, (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight U (quotientMap (c i : Cover)) (n i) (r i) y|) ≤ C i*(r i)^3*(e i)^2)
    (helim : Tendsto e atTop (𝓝 0)) (hClim : Tendsto C atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Plane) (1/4) →
      Tendsto (fun i ↦ ∫ y, graphNormalize (r i) (e i) (m i) (g i) y*Δ φ y) atTop (𝓝 0) := by
  intro φ hφ hc hs
  obtain ⟨B,D,Q,hB,hD,hQ,hb,hd,hq⟩ := smooth_compact_test_bounds hφ hc
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hrE : Tendsto (fun i ↦ r i/e i) atTop (𝓝 0) := by
    have hfun : (fun i ↦ (r i/(e i)^2)*e i) = (fun i ↦ r i/e i) := by
      funext i
      field_simp [(he i).ne']
    simpa only [hfun,mul_zero] using hrel.mul helim
  have hl : Tendsto (fun i ↦ (D/2+C i*Q)*e i+|H| * B*A*(r i/e i)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,add_zero] using
      ((tendsto_const_nhds.add (hClim.mul_const Q)).mul helim).add (hrE.const_mul (|H| * B*A))
  apply squeeze_zero' (Eventually.of_forall fun i ↦ abs_nonneg _) _ hl
  exact Eventually.of_forall fun i ↦ weakCMC_spatial_normalized_residual hU hμ hH hN hp hu
    (hn i) (hr i) (hrs i) (hα i) (he i) (htrap i) (htilt i) (ha i) (hg i) (hcol i)
      hφ hs hB hD hQ hb hd hq (m i)

end CubicTorus.MovingCenter

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic_oai := @OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic_oai
