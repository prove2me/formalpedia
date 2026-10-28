-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:47:39.914266+00:00
-- url     : https://prove2.me/submissions/0c748d5d-f77a-44c2-b94e-645ca27338d5

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Definitions.Def_OAIQ079A001
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_perimeter_upper_density
import Theorems.Thm_OAI_CubicTorus_moving_blowup_perimeter_eq_normal_ball

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

lemma sublevelCutoff_contDiff {q : Cover → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (t ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelCutoff q t ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub hq).div_const ε)

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma sublevelCutoff_eq_zero {q : Cover → ℝ} {t ε : ℝ} (hε : 0 < ε)
    {x : Cover} (hx : t ≤ q x) : sublevelCutoff q t ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le)

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

lemma radialDensityWeight_tendsto (a x : Cover) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ radialDensityWeight a r ε x) (𝓝[>] 0)
      (𝓝 ((Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Metric.ball a r
  · have hxr : ‖x - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hp : 0 < r ^ 2 - ‖x - a‖ ^ 2 := by nlinarith [norm_nonneg (x - a)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp)] with ε hε hεδ
    rw [indicator_of_mem hx]
    exact (Real.smoothTransition.one_of_one_le ((one_le_div hε).2 (by simpa using hεδ.le))).symm
  · have hxr : r ≤ ‖x - a‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [indicator_of_notMem hx]
    exact (radialDensityWeight_zero hr.le hε hxr).symm

end CubicTorus

end
end

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

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.plane_hausdorff_two_haar
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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma scaledTestField_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (a : Cover) (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledTestField a r F) :=
  (hF.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)).const_smul r

lemma fderiv_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    fderiv ℝ (scaledTestField a r F) x = fderiv ℝ F (r⁻¹ • (x - a)) := by
  have hψ : HasFDerivAt (fun y : Cover ↦ r⁻¹ • (y - a))
      (r⁻¹ • (ContinuousLinearMap.id ℝ Cover)) x :=
    ((hasFDerivAt_id x).sub_const a).const_smul r⁻¹
  have h := (((hF _).hasFDerivAt).comp x hψ).const_smul r
  change HasFDerivAt (scaledTestField a r F) _ x at h
  rw [h.fderiv]
  ext v
  simp [smul_smul, hr]

lemma divergence_scaledTestField {F : Cover → Cover} (hF : Differentiable ℝ F)
    (a x : Cover) {r : ℝ} (hr : r ≠ 0) :
    divergence (scaledTestField a r F) x = divergence F (r⁻¹ • (x - a)) := by
  simp only [divergence, fderiv_scaledTestField hF a x hr]

lemma scaledTestField_tsupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledTestField a r F) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hFx : F (r⁻¹ • (x - a)) ≠ 0 := by
    intro h
    exact hx (by simp [scaledTestField, h])
  have hb := hs (subset_closure hFx)
  have hb' : ‖x - a‖ / r ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul] using hb
  exact (div_le_iff₀ hr).mp hb' |>.trans_eq (one_mul r)

lemma scaledTestField_hasCompactSupport {F : Cover → Cover}
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledTestField a r F) :=
  (isCompact_closedBall a r).of_isClosed_subset isClosed_closure (scaledTestField_tsupport hs a hr)

lemma integral_cover_affine_scaling (g : Cover → ℝ) (a : Cover) {r : ℝ} (hr : 0 < r) :
    (∫ x, g x) = r ^ 3 * ∫ y : Cover, g (r • y + a) := by
  have h := Measure.integral_comp_smul (volume : Measure Cover) (fun x ↦ g (x + a)) r
  rw [integral_add_right_eq_self, show Module.finrank ℝ Cover = 3 by simp [Cover],
    smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le 3))] at h
  rw [h]
  field_simp

theorem normalMeasure_scaled_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (a : Cover) {r : ℝ} (hr : 0 < r)
    (hc : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 2 =
      ∫ x : Cover, characteristic E (quotientMap (r • x + a)) * divergence F x := by
  have hflux := normalMeasure_local_flux hE hμ (scaledTestField_contDiff hF a r)
    (scaledTestField_hasCompactSupport hs a hr) ((scaledTestField_tsupport hs a hr).trans hc)
  simp only [scaledTestField, inner_smul_right, integral_const_mul] at hflux
  have hscale := integral_cover_affine_scaling
    (fun x ↦ characteristic E (quotientMap x) * divergence (scaledTestField a r F) x) a hr
  have hdiv (x : Cover) : divergence (scaledTestField a r F) (r • x + a) = divergence F x := by
    rw [divergence_scaledTestField (hF.differentiable (by simp)) a _ hr.ne']
    simp [hr.ne']
  simp_rw [hdiv] at hscale
  rw [hscale] at hflux
  calc
    _ = (r * ∫ z, ⟪(z.2 : Cover), F (r⁻¹ • ((z.1 : Cover) - a))⟫ ∂(μ : Measure NormalBundle)) / r ^ 3 := by
      field_simp
    _ = _ := by rw [hflux]; field_simp

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

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_measurable (n : Cover) : Measurable (normalPlaneEmbedding n) :=
  (normalProductChart n).measurable.comp
    (measurable_const.prodMk (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable)

lemma plane_ball_real {s : ℝ} (hs : 0 ≤ s) :
    (volume : Measure Plane).real (Metric.ball 0 s) = Real.pi * s ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

lemma radialDensityWeight_plane_bound (n : Cover) {s ε : ℝ}
    (hs : 0 ≤ s) (hε : 0 < ε) (y : Plane) :
    ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y := by
  by_cases hy : y ∈ Metric.ball (0 : Plane) s
  · rw [indicator_of_mem hy, Real.norm_eq_abs,
      abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  · rw [indicator_of_notMem hy]
    have hnorm : s ≤ ‖normalPlaneEmbedding n y - 0‖ := by
      simpa only [sub_zero, normalPlaneEmbedding_norm, Metric.mem_ball, dist_zero_right,
        not_lt] using hy
    rw [radialDensityWeight_zero hs hε hnorm, norm_zero]

lemma integral_radialDensityWeight_plane_tendsto (n : Cover) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε : ℝ ↦ ∫ y : Plane, radialDensityWeight 0 s ε (normalPlaneEmbedding n y))
      (𝓝[>] 0) (𝓝 (Real.pi * s ^ 2)) := by
  have hi : Integrable ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator Metric.isOpen_ball.measurableSet
  have ht := tendsto_integral_filter_of_dominated_convergence
    ((Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)))
    (Eventually.of_forall fun ε : ℝ ↦
      ((radialDensityWeight_contDiff 0 s ε).continuous.measurable.comp
        (normalPlaneEmbedding_measurable n)).aestronglyMeasurable)
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ y : Plane, ‖radialDensityWeight 0 s ε (normalPlaneEmbedding n y)‖ ≤
      (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact Eventually.of_forall (radialDensityWeight_plane_bound n hs.le hε)) hi
    (Eventually.of_forall fun y : Plane ↦ radialDensityWeight_tendsto 0 (normalPlaneEmbedding n y) hs)
  have he : (fun y : Plane ↦ (Metric.ball (0 : Cover) s).indicator (fun _ ↦ (1 : ℝ))
      (normalPlaneEmbedding n y)) = (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) := by
    ext y
    have hy : normalPlaneEmbedding n y ∈ Metric.ball (0 : Cover) s ↔
        y ∈ Metric.ball (0 : Plane) s := by
      simp only [Metric.mem_ball, dist_zero_right, normalPlaneEmbedding_norm]
    by_cases h : y ∈ Metric.ball (0 : Plane) s
    · rw [indicator_of_mem h, indicator_of_mem (hy.mpr h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hy.mp h)]
  have hval : (∫ y : Plane, (Metric.ball (0 : Plane) s).indicator (fun _ ↦ (1 : ℝ)) y) =
      Real.pi * s ^ 2 := by
    calc _ = (volume : Measure Plane).real (Metric.ball 0 s) :=
          integral_indicator_one Metric.isOpen_ball.measurableSet
         _ = _ := plane_ball_real hs.le
  rw [he, hval] at ht
  exact ht

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
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
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVBlowupNormalMeasure
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_blowupNormalMap (c : Cover) (r : ℝ) :
    Continuous (blowupNormalMap c r) := by
  have hx : Continuous (fun z : NormalBundle ↦ (z.1 : Cover)) :=
    continuous_subtype_val.comp continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

lemma blowupNormalMeasure_mass (μ : FiniteMeasure NormalBundle) (c : Cover) (r R : ℝ) :
    ((blowupNormalMeasure μ c r R).mass : ℝ) = r⁻¹^2*cellBallMass μ c (r*R) := by
  change (((Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (blowupNormalMap c r)) univ) : ℝ) = _
  rw [FiniteMeasure.smul_apply,FiniteMeasure.map_apply _
    (continuous_blowupNormalMap c r).measurable MeasurableSet.univ]
  rw [Set.preimage_univ,FiniteMeasure.restrict_apply _ _ MeasurableSet.univ,univ_inter]
  change (Real.toNNReal (r⁻¹^2) : ℝ) *
    (((μ : Measure NormalBundle) {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma blowupNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : NormalBundle) :
    (blowupNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [blowupNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

lemma blowupNormalMeasure_supported (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    blowupNormalMeasure μ c r R ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 := by
  have hm : MeasurableSet ((Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere))ᶜ) :=
    (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ).compl
  have he : (blowupNormalMap c r ⁻¹' ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ)) ∩
      {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨Metric.ball_subset_closedBall ((blowupNormalMap_mem c hr R z).mpr hz.2),mem_univ _⟩
  unfold blowupNormalMeasure
  rw [FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (continuous_blowupNormalMap c r).measurable hm,
    FiniteMeasure.restrict_apply _ _ (hm.preimage (continuous_blowupNormalMap c r).measurable),he]
  simp [FiniteMeasure.coeFn_def]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma integral_blowupNormalMeasure (μ : FiniteMeasure NormalBundle) (c : Cover)
    (r R : ℝ) {g : BlowupNormalBundle → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z in {z : NormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)},
        g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [blowupNormalMeasure,FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure,
    FiniteMeasure.toMeasure_map,integral_map
      (continuous_blowupNormalMap c r).measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  change (Real.toNNReal (r⁻¹^2) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma integral_blowup_test (μ : FiniteMeasure NormalBundle) (c : Cover)
    {r R : ℝ} (hr : 0 < r) {g : BlowupNormalBundle → ℝ} (hg : Continuous g)
    (hzero : ∀ z, z.1 ∉ Metric.ball (0 : Cover) R → g z = 0) :
    (∫ z, g z ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z, g (blowupNormalMap c r z) ∂(μ : Measure NormalBundle) := by
  rw [integral_blowupNormalMeasure μ c r R hg]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero _ (by rwa [blowupNormalMap_mem c hr R z])

lemma tangentialDivergence_scaledTestField {F : Cover → Cover}
    (hF : Differentiable ℝ F) (c x n : Cover) {r : ℝ} (hr : r ≠ 0) :
    tangentialDivergence (scaledTestField c r F) x n =
      tangentialDivergence F (r⁻¹ • (x-c)) n := by
  simp only [tangentialDivergence,divergence_scaledTestField hF c x hr,
    fderiv_scaledTestField hF c x hr]

theorem weakCMC_blowup_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1)
    (c : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall c r ⊆ {x | ∀ j, 0 < x j ∧ x j < 1}) :
    (∫ z, tangentialDivergence F z.1 z.2
      ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      (r*H) * ∫ z, ⟪(z.2 : Cover),F z.1⟫
        ∂(blowupNormalMeasure μ c r R : Measure BlowupNormalBundle) := by
  have ht (z : BlowupNormalBundle) (hz : z.1 ∉ Metric.ball (0 : Cover) R) :
      z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
  rw [integral_blowup_test μ c hr (continuous_blowupTangentTest hF)
      (fun z hz ↦ tangentialDivergence_zero_of_notMem_tsupport (ht z hz) z.2),
    integral_blowup_test μ c hr (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport (ht z hz)])]
  have hid := weakCMC_local_identity hμ hH (scaledTestField_contDiff hF c r)
    (scaledTestField_hasCompactSupport hs c hr) ((scaledTestField_tsupport hs c hr).trans hc)
  simp only [tangentialDivergence_scaledTestField (hF.differentiable (by simp)) c _ _ hr.ne',
    scaledTestField,inner_smul_right,integral_const_mul] at hid
  change r⁻¹^2*(∫ z, tangentialDivergence F (r⁻¹ • ((z.1 : Cover)-c)) z.2
    ∂(μ : Measure NormalBundle)) = _
  rw [hid]
  simp only [blowupNormalMap]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma localL1_weighted_integral_tendsto {η : Measure Cover} [IsFiniteMeasure η]
    {l : Filter ℕ} (g : ℕ → Cover → ℝ) (hg : ∀ i, Measurable (g i))
    (hgb : ∀ i x, |g i x| ≤ 1) {f : Cover → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1)
    (hlim : Tendsto (fun i ↦ ∫ x, |g i x-f x| ∂η) l (𝓝 0))
    (k : Cover →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, g i x*k x ∂η) l (𝓝 (∫ x, f x*k x ∂η)) := by
  have hi (i) : Integrable (fun x ↦ g i x*k x) η :=
    Integrable.of_bound ((hg i).mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hgb i x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hfi : Integrable (fun x ↦ f x*k x) η :=
    Integrable.of_bound (hf.mul k.continuous.measurable).aestronglyMeasurable ‖k‖
      (ae_of_all _ (fun x ↦ by
        simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
          mul_le_mul (hfb x) (k.norm_coe_le_norm x) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
  have hdiff (i) : Integrable (fun x ↦ |g i x-f x|) η :=
    ((integrable_bounded_one (hg i) (hgb i)).sub (integrable_bounded_one hf hfb)).abs
  have hbound (i) : ‖(∫ x, g i x*k x ∂η)-(∫ x, f x*k x ∂η)‖ ≤
      ‖k‖ * ∫ x, |g i x-f x| ∂η := by
    rw [← integral_sub (hi i) hfi,← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono ((hi i).sub hfi).norm ((hdiff i).const_mul ‖k‖)
    intro x
    change ‖g i x*k x-f x*k x‖ ≤ ‖k‖*|g i x-f x|
    rw [← sub_mul,Real.norm_eq_abs,abs_mul]
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (abs_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun i ↦ norm_nonneg _) hbound (by simpa using hlim.const_mul ‖k‖)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverLocalPerimeter_mono (A : Set Cover) {O P : Set Cover} (hOP : O ⊆ P) :
    coverLocalPerimeter A O ≤ coverLocalPerimeter A P := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hs
  apply iSup_le
  intro hO
  apply iSup_le
  intro hb
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le (hO.trans hOP) (le_iSup_of_le hb le_rfl))))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVLocalScaling
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
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma moving_blowup_flux_tendsto {E : Set Torus} (hE : MeasurableSet E)
    (c : ℕ → Cover) (r : ℕ → ℝ) {A : Set Cover} (hA : MeasurableSet A)
    {R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) R) :
    Tendsto (fun i ↦ ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x)
      l (𝓝 (∫ x in A, divergence F x)) := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hd : HasCompactSupport (divergence F) := hFs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F)
  let k : Cover →ᵇ ℝ := ofCompactSupport _ (continuous_divergence hF) hd
  have ht := localL1_weighted_integral_tendsto
    (fun i ↦ blowupCharacteristic E (c i) (r i))
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv k
  have hz (x : Cover) (hx : x ∉ Metric.closedBall (0 : Cover) R) : divergence F x = 0 :=
    divergence_of_notMem_tsupport (fun hh ↦ hx (hs hh))
  have heg (i) : (∫ x in Metric.closedBall (0 : Cover) R, blowupCharacteristic E (c i) (r i) x*k x) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])
  have hef : (∫ x in Metric.closedBall (0 : Cover) R, A.indicator (fun _ ↦ (1 : ℝ)) x*k x) =
      ∫ x in A, divergence F x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by change _*divergence F x = 0; rw [hz x hx,mul_zero])]
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence F x) = _
    simp only [← indicator_mul_left,one_mul]
    exact integral_indicator hA
  simpa only [heg,hef] using ht

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVStationaryDensity
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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weakCMC_moving_blowup_limit_stationary {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupTangentTest hF hFs)
  have hf := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupFluxTest hF.continuous hFs)
  have hh := (hrlim.mul_const H).mul hf
  simp only [zero_mul] at hh
  have he (i) := weakCMC_blowup_identity hμ hH hF hs (c i) (hr i) hR (hc i)
  exact tendsto_nhds_unique ht (hh.congr (fun i ↦ (he i).symm))

theorem moving_blowup_normal_limit_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ x in A, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hf := moving_blowup_flux_tendsto hE c r hA hconv hF hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (blowupFluxTest hF.continuous hFs)
  have he (i) : (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(blowupNormalMeasure μ (c i) (r i) R : Measure BlowupNormalBundle)) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x := by
    rw [integral_blowup_test μ (c i) (hr i) (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by
        have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
        simp [image_eq_zero_of_notMem_tsupport hn])]
    change (r i)⁻¹^2*(∫ z, ⟪(z.2 : Cover),F ((r i)⁻¹ • ((z.1 : Cover)-c i))⟫ ∂(μ : Measure NormalBundle)) = _
    rw [show (r i)⁻¹^2 = ((r i)^2)⁻¹ by ring]
    rw [← div_eq_inv_mul,normalMeasure_scaled_flux hE hμ hF hs (c i) (hr i) (hc i)]
    simp only [blowupCharacteristic,add_comm (c i)]
  exact tendsto_nhds_unique (hweak.congr fun i ↦ he i) hf

theorem moving_blowup_normal_cluster {μ : FiniteMeasure NormalBundle}
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, cellBallMass μ (c i) (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) := by
  have hm (i) : (blowupNormalMeasure μ (c i) (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,blowupNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,blowupNormalMeasure_supported μ (c i) (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

theorem isMinimizerAt_moving_paired_normal_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0)) {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ (ν : FiniteMeasure BlowupNormalBundle) (k : ℕ) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ (c (i+k)) (r (i+k)) 2) U (𝓝 ν) ∧
      ν ((Metric.closedBall (0 : Cover) 2 ×ˢ univ)ᶜ) = 0 ∧
      ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x := by
  obtain ⟨S,B,hS,hB,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hsmall : 0 < min (3/16 : ℝ) (S/2) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let q : ℕ → ℝ := fun i ↦ r (i+k)
  let d : ℕ → Cover := fun i ↦ c (i+k)
  have hq (i) : 0 < q i := hr _
  have hqb (i) : q i < min (3/16 : ℝ) (S/2) := hk _ (by omega)
  have hchart (i) : Metric.closedBall (d i) (q i*2) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    MovingCenter.closedBall_interior (c := c (i+k)) (by
      have hh := (hqb i).trans_le (min_le_left _ _)
      linarith)
  have hmass (i) : cellBallMass μ (d i) (q i*2) ≤ (B*4)*(q i)^2 := by
    rw [cellBallMass_eq_spatialNormalMeasure μ (d i) _ (Metric.ball_subset_closedBall.trans (hchart i))]
    have hh := harea μ hμ (quotientMap (d i)) (q i*2) (mul_pos (hq i) (by norm_num)) (by
      have hh := (hqb i).trans_le (min_le_right _ _)
      linarith)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨ν,_,hsup,hcl⟩ := moving_blowup_normal_cluster d q hq (by positivity : 0 ≤ B*4) hmass
  obtain ⟨U,hU,hν⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hqlim : Tendsto q (U : Filter ℕ) (𝓝 0) :=
    (hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hc1 (i) : Metric.closedBall (d i) (q i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.closedBall_subset_closedBall (by have hh := hq i; linarith)).trans (hchart i)
  have hconv' : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (d i) (q i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        (U : Filter ℕ) (𝓝 0) := (hconv.comp (tendsto_add_atTop_nat k)).mono_left hU
  refine ⟨ν,k,U,hU,hν,hsup,?_⟩
  intro F hF hs
  exact ⟨weakCMC_moving_blowup_limit_stationary hμ hH d q hq (by norm_num) hc1 hqlim hν hF hs,
    moving_blowup_normal_limit_flux hE hμ d q hq (by norm_num) hc1 hν hA hconv' hF hs⟩

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

lemma coverLocalPerimeter_congr_local {A B O : Set Cover}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : ∀ᵐ x ∂(volume : Measure Cover), x ∈ O → (x ∈ A ↔ x ∈ B)) :
    coverLocalPerimeter A O = coverLocalPerimeter B O := by
  unfold coverLocalPerimeter
  apply iSup_congr; intro F
  apply iSup_congr; intro _
  apply iSup_congr; intro _
  apply iSup_congr; intro hs
  apply iSup_congr; intro _
  rw [setIntegral_divergence_congr_local hA hB hAB hs]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurableSet_coverHalfspace (n : Cover) : MeasurableSet (coverHalfspace n) :=
  measurableSet_lt (by fun_prop) measurable_const

lemma halfspace_indicator_eq (n : Cover) :
    (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) = halfspaceIndicator n := rfl

lemma setIntegral_coverHalfspace_divergence {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, ⟪n,F (normalPlaneEmbedding n y)⟫ := by
  have hh := integral_halfspace_divergence 0 hn hF hs
  simp only [sub_zero,zero_add] at hh
  rw [← hh,← halfspace_indicator_eq]
  simp only [← indicator_mul_left,one_mul,integral_indicator (measurableSet_coverHalfspace n)]

lemma coverHalfspace_flux_le {n : Cover} (hn : ‖n‖ = 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {b : ℝ} (hb : 0 ≤ b) (hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b)
    (hbound : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in coverHalfspace n, divergence F x) ≤ Real.pi*b^2 := by
  rw [setIntegral_coverHalfspace_divergence hn hF hs]
  have hc : Continuous (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hh := (normalColumnChart_plane_isometry 0 hn 0).continuous
    simp only [normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] at hh
    exact continuous_const.inner (hF.continuous.comp hh)
  have hsc : HasCompactSupport (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := by
    have hss := hs.comp_isClosedEmbedding (normalColumnChart_plane_isometry 0 hn 0).isClosedEmbedding
    have hh := hss.comp_left (show ⟪n,(0 : Cover)⟫ = 0 by simp)
    simpa only [Function.comp_def,normalColumnChart_apply 0 hn,zero_smul,add_zero,zero_add] using hh
  have hi : Integrable (fun y : Plane ↦ ⟪n,F (normalPlaneEmbedding n y)⟫) := hc.integrable_of_hasCompactSupport hsc
  have hbint : Integrable ((Metric.closedBall (0 : Plane) b).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hh := integral_mono hi hbint (fun y ↦ ?_)
  · have hv : (volume : Measure Plane).real (Metric.closedBall 0 b) = Real.pi*b^2 := by
      simp only [Measure.real,EuclideanSpace.volume_closedBall_fin_two,ENNReal.toReal_mul,
        ENNReal.toReal_pow,ENNReal.toReal_ofReal hb,ENNReal.toReal_ofReal Real.pi_pos.le]
      ring
    rw [integral_indicator Metric.isClosed_closedBall.measurableSet,integral_const,
      smul_eq_mul,mul_one,measureReal_restrict_apply_univ,hv] at hh
    exact hh
  · by_cases hy : y ∈ Metric.closedBall (0 : Plane) b
    · rw [indicator_of_mem hy]
      exact (real_inner_le_norm _ _).trans (by rw [hn,one_mul]; exact hbound _)
    · rw [indicator_of_notMem hy]
      have hz : F (normalPlaneEmbedding n y) = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (by
        simpa only [Metric.mem_closedBall,dist_zero_right,normalPlaneEmbedding_norm] using hFb hh))
      simp [hz]

lemma coverLocalPerimeter_halfspace_le {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 ≤ b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) ≤
      ENNReal.ofReal (Real.pi*b^2) := by
  apply iSup_le; intro F
  apply iSup_le; intro hF
  apply iSup_le; intro hs
  apply iSup_le; intro hbF
  apply iSup_le; intro hbound
  exact ENNReal.ofReal_le_ofReal (coverHalfspace_flux_le hn hF hs hb hbF hbound)

theorem coverLocalPerimeter_halfspace {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.closedBall (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm (coverLocalPerimeter_halfspace_le hn hb.le)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (integral_radialDensityWeight_plane_tendsto n hb)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
  have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
  have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
    (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
      (radialDensityWeight_tsupport hb.le hε)
  have hbound (x : Cover) : ‖F x‖ ≤ 1 := by
    change ‖radialDensityWeight 0 b ε x • n‖ ≤ 1
    rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact radialDensityWeight_le_one _ _ _ _
  have he : (∫ x in coverHalfspace n, divergence F x) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    rw [setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  dsimp only [Function.comp_apply]
  rw [← he]
  exact le_iSup_of_le F (le_iSup_of_le hF (le_iSup_of_le hs
    (le_iSup_of_le hFb (le_iSup_of_le hbound le_rfl))))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSecondaryPlanarData
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

lemma blowupNormal_inner_integrable (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) :
    Integrable (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) ν := by
  apply Integrable.of_bound (show AEStronglyMeasurable _ _ from
    (show Continuous (fun z : BlowupNormalBundle ↦ ⟪(z.2 : Cover),n⟫) from by fun_prop).aestronglyMeasurable) 1
  exact ae_of_all _ fun z ↦ by
    simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n

lemma radial_normal_flux_tendsto (ν : FiniteMeasure BlowupNormalBundle)
    {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ε : ℝ ↦ ∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫
      ∂(ν : Measure BlowupNormalBundle)) (𝓝[>] 0)
      (𝓝 (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
        ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle))) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : BlowupNormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall fun ε : ℝ ↦ (show Continuous (fun z : BlowupNormalBundle ↦
      radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫) from by
        exact ((radialDensityWeight_contDiff 0 b ε).continuous.comp continuous_fst).mul
          ((continuous_subtype_val.comp continuous_snd).inner continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun ε : ℝ ↦ ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦ by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
      exact (mul_le_mul (radialDensityWeight_le_one _ _ _ _)
        (show ‖⟪(z.2 : Cover),n⟫‖ ≤ 1 by
          simpa only [z.2.property,hn,one_mul] using norm_inner_le_norm (z.2 : Cover) n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (integrable_const 1)
    (ae_of_all (ν : Measure BlowupNormalBundle) fun z ↦
      (radialDensityWeight_tendsto 0 z.1 hb).mul_const ⟪(z.2 : Cover),n⟫)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [← integral_indicator (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from
    Metric.isOpen_ball.measurableSet.preimage measurable_fst)]
  apply integral_congr_ae
  exact ae_of_all _ fun z ↦ by
    dsimp only
    by_cases hz : z.1 ∈ Metric.ball (0 : Cover) b
    · rw [Set.indicator_of_mem (show z ∈ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_mem hz,one_mul]
    · rw [Set.indicator_of_notMem (show z ∉ {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b} from hz),
        Set.indicator_of_notMem hz,zero_mul]

lemma flat_set_limit_flux_on_ball {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ z in {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) b},
      ⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = Real.pi*b^2 := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ z, radialDensityWeight 0 b ε z.1*⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ y : Plane, radialDensityWeight 0 b ε (normalPlaneEmbedding n y) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let F : Cover → Cover := fun x ↦ radialDensityWeight 0 b ε x • n
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := (radialDensityWeight_contDiff 0 b ε).smul_const n
    have hs : HasCompactSupport F := (radialDensityWeight_hasCompactSupport hb.le hε).smul_right
    have hFb : tsupport F ⊆ Metric.closedBall (0 : Cover) b :=
      (tsupport_smul_subset_left (f := radialDensityWeight 0 b ε) (g := fun _ ↦ n)).trans
        (radialDensityWeight_tsupport hb.le hε)
    have hh := hflux F hF (hFb.trans (Metric.closedBall_subset_closedBall hb1.le))
    simp only [F,inner_smul_right] at hh
    rw [hh,setIntegral_divergence_congr_local hA (measurableSet_coverHalfspace n) hAn
      (hFb.trans (Metric.closedBall_subset_ball hb1)),setIntegral_coverHalfspace_divergence hn hF hs]
    simp only [F,inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,mul_one]
  exact tendsto_nhds_unique (radial_normal_flux_tendsto ν hn hb)
    ((integral_radialDensityWeight_plane_tendsto n hb).congr' (he.mono fun _ h ↦ h.symm))

theorem flat_set_limit_normal {A : Set Cover} (hA : MeasurableSet A)
    {n : Cover} (hn : ‖n‖ = 1)
    (hAn : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ A ↔ x ∈ coverHalfspace n))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hm : (ν : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2)
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x) :
    ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n := by
  let B : Set BlowupNormalBundle := {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)}
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet.preimage measurable_fst
  have hi := (blowupNormal_inner_integrable ν hn).integrableOn (s := B)
  have he := flat_set_limit_flux_on_ball hA hn hAn hflux
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hz : (∫ z in B, 1-⟪(z.2 : Cover),n⟫ ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    rw [integral_sub (integrable_const 1) hi,integral_const]
    simp only [smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
    change (ν : Measure BlowupNormalBundle).real B-_ = 0
    rw [hm,he,sub_self]
  have hnneg : ∀ z : BlowupNormalBundle, 0 ≤ 1-⟪(z.2 : Cover),n⟫ := by
    intro z
    have hh := real_inner_le_norm (z.2 : Cover) n
    rw [z.2.property,hn,one_mul] at hh
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hnneg)
    ((integrable_const 1).sub hi)).mp hz
  have hae' := (ae_restrict_iff' hB).mp hae
  filter_upwards [hae'] with z hz hzb
  have hh := hz hzb
  change 1-⟪(z.2 : Cover),n⟫ = 0 at hh
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hs : ‖(z.2 : Cover)-n‖^2 = 0 := by rw [norm_sub_sq_real,z.2.property,hn]; nlinarith
  exact sq_eq_zero_iff.mp hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coverLocalPerimeter_halfspace_ball {n : Cover} (hn : ‖n‖ = 1) {b : ℝ} (hb : 0 < b) :
    coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) b) =
      ENNReal.ofReal (Real.pi*b^2) := by
  apply le_antisymm
  · exact (coverLocalPerimeter_mono _ Metric.ball_subset_closedBall).trans
      (coverLocalPerimeter_halfspace_le hn hb.le)
  · have ht : Tendsto (fun a : ℝ ↦ ENNReal.ofReal (Real.pi*a^2)) (𝓝[<] b)
        (𝓝 (ENNReal.ofReal (Real.pi*b^2))) := by
      exact (ENNReal.continuous_ofReal.comp
        (show Continuous (fun a : ℝ ↦ Real.pi*a^2) by fun_prop)).continuousAt.tendsto.mono_left inf_le_left
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with a ha ha0
    rw [← coverLocalPerimeter_halfspace hn ha0]
    exact coverLocalPerimeter_mono _ (Metric.closedBall_subset_ball ha)

lemma halfspace_model_perimeter_ball {B : Set Cover} (hB : MeasurableSet B)
    {n : Cover} (hn : ‖n‖ = 1)
    (hhalf : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ B ↔ x ∈ coverHalfspace n))
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    coverLocalPerimeter B (Metric.ball (0 : Cover) a) = ENNReal.ofReal (Real.pi*a^2) := by
  have he : coverLocalPerimeter B (Metric.ball (0 : Cover) a) =
      coverLocalPerimeter (coverHalfspace n) (Metric.ball (0 : Cover) a) := by
    apply coverLocalPerimeter_congr_local hB (measurableSet_coverHalfspace n)
    filter_upwards [hhalf] with x hx hb
    exact hx (Metric.ball_subset_ball ha1.le hb)
  rw [he]
  exact coverLocalPerimeter_halfspace_ball hn ha

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVFlatBlowupRegular
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
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma continuous_blowupTilt (n : Cover) : Continuous (blowupTilt n) := by
  exact ((radialDensityWeight_contDiff 0 (2*(1/8)) (3*(1/8)^2)).continuous.comp
    continuous_fst).mul (((continuous_subtype_val.comp continuous_snd).sub continuous_const).norm.pow 2)

lemma blowupTilt_zero (n : Cover) (z : BlowupNormalBundle)
    (hz : z.1 ∉ Metric.ball (0 : Cover) (1/4)) : blowupTilt n z = 0 := by
  have hx : (1/4 : ℝ) ≤ ‖z.1‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hz
  have hh := radialDensityWeight_zero (a := (0 : Cover)) (r := (2*(1/8):ℝ))
    (ε := (3*(1/8)^2 : ℝ)) (x := z.1) (by norm_num) (by norm_num) (by norm_num; linarith)
  dsimp only [blowupTilt,radialHeightCutoff]
  rw [hh,zero_mul]

lemma blowupTilt_hasCompactSupport (n : Cover) : HasCompactSupport (blowupTilt n) := by
  apply ((isCompact_closedBall (0 : Cover) (1/4)).prod (isCompact_univ : IsCompact (univ : Set NormalSphere))).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
  intro z hz
  refine ⟨?_,mem_univ _⟩
  by_contra h
  exact hz (blowupTilt_zero n z (fun hh ↦ h (Metric.ball_subset_closedBall hh)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma flat_moving_normal_tilt_limit {μ : FiniteMeasure NormalBundle} (c : ℕ → Cover)
    (r : ℕ → ℝ) {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    {n : Cover}
    (hflat : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) (1/2) →
      (z.2 : Cover) = n) :
    Tendsto (fun i ↦ ∫ z, blowupTilt n z
      ∂(blowupNormalMeasure μ (c i) (r i) 2 : Measure BlowupNormalBundle)) l (𝓝 0) := by
  have hh := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
    (ofCompactSupport _ (continuous_blowupTilt n) (blowupTilt_hasCompactSupport n))
  have he : (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hflat] with z hz
    change blowupTilt n z = 0
    by_cases hb : z.1 ∈ Metric.ball (0 : Cover) (1/4)
    · have hn := hz (Metric.ball_subset_ball (by norm_num : (1/4 : ℝ) ≤ 1/2) hb)
      simp only [blowupTilt,hn,sub_self,norm_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero]
    · exact blowupTilt_zero n z hb
  change Tendsto (fun i ↦ ∫ z, blowupTilt n z ∂(blowupNormalMeasure μ (c i) (r i) 2 : Measure BlowupNormalBundle)) l
    (𝓝 (∫ z, blowupTilt n z ∂(ν : Measure BlowupNormalBundle))) at hh
  rwa [he] at hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
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

theorem isMinimizerAt_halfspace_L1_tilt_small_oai {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (c : MovingCenter.InteriorCenter) (r : ℝ),
      0 < r → r < η →
      (∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E c r x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
      (∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c r 2 : Measure BlowupNormalBundle)) < ε := by
  by_contra h
  push Not at h
  let d : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hb (i : ℕ) := h (d i) (hd i)
  choose c r hr hrd he ht using hb
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrlim : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i ↦ (hr i).le) (fun i ↦ (hrd i).le) hdlim
  have hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-
        (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) :=
    squeeze_zero (fun i ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
      (fun i ↦ (he i).le) hdlim
  obtain ⟨ν,k,U,hU,hν,_,hstat⟩ := isMinimizerAt_moving_paired_normal_limit
    hV hE hmin hμ hH c r hr hrlim (measurableSet_coverHalfspace n) hconv
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) := (hstat F hF hs).2
  have heq := moving_blowup_perimeter_eq_normal_ball hV hE hmin hμ
    (fun i ↦ c (i+k)) (fun i ↦ r (i+k)) (fun i ↦ hr _)
    ((hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU)
    (measurableSet_coverHalfspace n)
    ((hconv.comp (tendsto_add_atTop_nat k)).mono_left hU) hν hflux
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hmodel : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ coverHalfspace n ↔ x ∈ coverHalfspace n) := ae_of_all _ (by simp)
  have hmass : (ν : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2 := by
    rw [Measure.real_def,← heq,
      halfspace_model_perimeter_ball (measurableSet_coverHalfspace n) hn hmodel
        (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by positivity)]
  have hflat := flat_set_limit_normal (measurableSet_coverHalfspace n) hn hmodel hmass hflux
  have htilt := flat_moving_normal_tilt_limit
    (fun i ↦ (c (i+k) : Cover)) (fun i ↦ r (i+k)) hν hflat
  obtain ⟨i,hi⟩ := (htilt.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge (ht (i+k))) hi

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small_oai := @OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small_oai
