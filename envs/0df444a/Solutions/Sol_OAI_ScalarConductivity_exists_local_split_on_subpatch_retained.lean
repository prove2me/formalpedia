-- Prove2me | solution 1 for OAI.ScalarConductivity.exists_local_split_on_subpatch_retained
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:03:04.51599+00:00
-- url     : https://prove2.me/submissions/34373900-d132-4287-82c8-ee57889376ef

import Mathlib
import Definitions.Def_OAIQ059C007

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPiolaFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

lemma localPiolaFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) :
    Function.support (localPiolaFlux X F) ⊆ X '' (Function.support F ∩ X.source) := by
  intro y hy
  by_cases hyt : y ∈ X.target
  · refine ⟨X.symm y, ⟨?_, X.map_target hyt⟩, X.right_inv hyt⟩
    intro hz
    exact hy (by simp [localPiolaFlux, hyt, hz])
  · exact False.elim (hy (by simp [localPiolaFlux, hyt]))

lemma localPiolaFlux_hasCompactSupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (hF : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : HasCompactSupport (localPiolaFlux X F) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hF.image_of_continuousOn (X.continuousOn.mono hs))
  exact (localPiolaFlux_support X F).trans (image_mono (fun _ hx => subset_closure hx.1))

lemma localPiolaFlux_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) (hF : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : tsupport (localPiolaFlux X F) ⊆ X.target := by
  have hc : IsClosed (X '' tsupport F) :=
    (hF.image_of_continuousOn (X.continuousOn.mono hs)).isClosed
  exact (closure_minimal ((localPiolaFlux_support X F).trans
    (image_mono (fun _ hx => subset_closure hx.1))) hc).trans
      (by rintro y ⟨x, hx, rfl⟩; exact X.map_source (hs hx))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_ContDiffClmDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

lemma localPiolaFlux_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ X.source) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localPiolaFlux X F) := by
  apply contDiff_of_contDiffOn_tsupport X.open_target _ (localPiolaFlux_tsupport X F hc hs)
  apply X.open_target.contDiffOn_iff.mpr
  intro y hy
  have hxi := hXi.contDiffAt (X.open_target.mem_nhds hy)
  have hx := hX.contDiffAt (X.open_source.mem_nhds (X.map_target hy))
  have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun z => fderiv ℝ X (X.symm z)) y :=
    (hx.fderiv_right (by simp)).comp y hxi
  have hd0 : (fderiv ℝ X (X.symm y)).det ≠ 0 :=
    local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) (X.map_target hy)
  have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp y hd).abs hd0
  have hformula := (hdet.inv (abs_ne_zero.mpr hd0)).smul
    (hd.clm_apply (hF.contDiffAt.comp y hxi))
  apply hformula.congr_of_eventuallyEq
  filter_upwards [X.open_target.mem_nhds hy] with z hz
  simp [localPiolaFlux, hz]

lemma compactFlux_local_test
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    (μ : Measure E) {U : Set E} (hU : IsOpen U)
    (F : E → E) (hc : HasCompactSupport F) (hs : tsupport F ⊆ U)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (φ : E → ℝ) (hφ : ContDiffOn ℝ (↑(⊤ : ℕ∞)) φ U) :
    (∫ x, fderiv ℝ φ x (F x) ∂μ) = 0 := by
  obtain ⟨g, hg, hge⟩ := exists_smooth_extension_near_compact hU hc hs φ hφ
  rw [← hF g hg]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport F
  · rw [(hge x hx).fderiv_eq]
  · rw [image_eq_zero_of_notMem_tsupport hx, map_zero, map_zero]

lemma localPiolaFlux_zero_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (F : E → E) (hc : HasCompactSupport F) (hs : tsupport F ⊆ X.source)
    (hF : ∀ ψ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
      (∫ x, fderiv ℝ ψ x (F x) ∂μ) = 0)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) :
    (∫ y, fderiv ℝ ψ y (localPiolaFlux X F y) ∂μ) = 0 := by
  rw [localPiolaFlux_pairing μ X (hX.differentiableOn (by simp))
    (fun _ hx => local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) hx)
    F (subset_closure.trans hs) ψ (hψ.differentiable (by simp))]
  exact compactFlux_local_test μ X.open_source F hc hs hF _ (hψ.comp_contDiffOn hX)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_InverseChartPiolaOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma localPiolaFlux_inverse_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) {y : E} (hy : y ∈ X.source) :
    localPiolaFlux X.symm F y = inverseChartPiolaOperator X y (F (X y)) := by
  simp only [localPiolaFlux, X.symm_symm, show y ∈ X.symm.target from hy, ite_eq_left,
    inverseChartPiolaOperator, _root_.smul_apply]

lemma inverseChartPiolaOperator_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a : E} (ha : a ∈ X.source) : ContinuousAt (inverseChartPiolaOperator X) a := by
  have hca : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ X.symm) (X a) :=
    ((hXi _ (X.map_source ha)).contDiffAt
    (X.open_target.mem_nhds (X.map_source ha))).fderiv_right (by simp)
  have hda := ((hX a ha).contDiffAt (X.open_source.mem_nhds ha)).continuousAt
  have hd : ContinuousAt (fun y => fderiv ℝ X.symm (X y)) a := hca.continuousAt.comp hda
  have hdet0 := local_fderiv_det_ne_zero X.symm (hXi.differentiableOn (by simp))
    (hX.differentiableOn (by simp)) (X.map_source ha)
  have hc : ContinuousAt (fun y => (fderiv ℝ X.symm (X y)).det) a :=
    ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).continuous.continuousAt).comp hd
  exact (hc.abs.inv₀ (abs_ne_zero.mpr hdet0)).smul hd

lemma inverseChartPiolaOperator_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E) :
    inverseChartPiolaOperator X a = ContinuousLinearMap.id ℝ E := by
  have hdi := local_fderiv_symm_comp X hX hXi ha
  rw [hDa, ContinuousLinearMap.comp_id] at hdi
  simp only [inverseChartPiolaOperator, hdi, ContinuousLinearMap.det,
    ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one, inv_one, one_smul]

theorem inverseChartPiola_freezing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ X.source ∧
      ∀ (χ h : E → ℝ) (R : E) (y : E), y ∈ V →
        ‖localPiolaFlux X.symm (fun z => (χ (X.symm z) * h z) • R) y -
          (χ y * h (X y)) • R‖ ≤ ε * (|χ y * h (X y)| * ‖R‖) := by
  have heq := inverseChartPiolaOperator_eq_id X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) ha hDa
  have hc : ContinuousAt (fun y => inverseChartPiolaOperator X y -
      ContinuousLinearMap.id ℝ E) a :=
    (inverseChartPiolaOperator_continuousAt X hX hXi ha).sub continuousAt_const
  have hevent : ∀ᶠ y in 𝓝 a,
      ‖inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E‖ < ε := by
    have ht := hc.norm.eventually (gt_mem_nhds (show
      ‖inverseChartPiolaOperator X a - ContinuousLinearMap.id ℝ E‖ < ε by
      rw [heq, sub_self, norm_zero]; exact hε))
    exact ht
  obtain ⟨V, hVsub, hV, haV⟩ := mem_nhds_iff.mp (hevent.and (X.open_source.mem_nhds ha))
  refine ⟨V, hV, haV, fun y hy => (hVsub hy).2, ?_⟩
  intro χ h R y hy
  rw [localPiolaFlux_inverse_eq X _ (hVsub hy).2, X.left_inv (hVsub hy).2]
  rw [map_smul]
  have hid : (χ y * h (X y)) • (inverseChartPiolaOperator X y R) -
      (χ y * h (X y)) • R =
      (χ y * h (X y)) • ((inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E) R) := by
    simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs]
  calc
    |χ y * h (X y)| * ‖(inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E) R‖ ≤
        |χ y * h (X y)| * (ε * ‖R‖) :=
      mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hVsub hy).1.le (norm_nonneg _))) (abs_nonneg _)
    _ = ε * (|χ y * h (X y)| * ‖R‖) := by ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPiolaFluxPotentialPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
namespace ScalarConductivity

theorem localPiolaFlux_potential_pairing
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : OpenPartialHomeomorph E E) (hX : DifferentiableOn ℝ X X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    (D : E →L[ℝ] V) (u : E → V)
    (hu : ∀ y ∈ X.source, D (X y) = u y) (F : E → E)
    {y : E} (hy : y ∈ X.source) :
    fderiv ℝ u y (localPiolaFlux X.symm F y) =
      |(fderiv ℝ X.symm (X y)).det|⁻¹ • D (F (X y)) := by
  classical
  have hxy := X.map_source hy
  have he : u =ᶠ[𝓝 y] D ∘ X := by
    filter_upwards [X.open_source.mem_nhds hy] with z hz
    exact (hu z hz).symm
  have hd := (hX y hy).differentiableAt (X.open_source.mem_nhds hy)
  have hinv := local_fderiv_symm_comp X.symm hXi hX hxy
  simp only [OpenPartialHomeomorph.symm_symm, X.left_inv hy] at hinv
  rw [he.fderiv_eq, fderiv_comp y D.differentiableAt hd, D.fderiv]
  have hflux : localPiolaFlux X.symm F y =
      |(fderiv ℝ X.symm (X y)).det|⁻¹ • (fderiv ℝ X.symm (X y)) (F (X y)) := by
    simp [localPiolaFlux, hy]
  rw [ContinuousLinearMap.comp_apply, hflux, map_smul, map_smul]
  congr 1
  exact congrArg D (congrArg (fun T : E →L[ℝ] E => T (F (X y))) hinv)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Scalarization_SmoothScalarAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open scoped ContDiff

theorem smoothDirection_comm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (f : SmoothScalar E) :
    smoothDirection v (smoothDirection w f) =
      smoothDirection w (smoothDirection v f) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (fun y => fderiv ℝ f.val y w) x v =
    fderiv ℝ (fun y => fderiv ℝ f.val y v) x w
  have hd : DifferentiableAt ℝ (fderiv ℝ f.val) x :=
    ((smoothScalar_contDiff f).fderiv_right (m := ↑(⊤ : ℕ∞)) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa using ((smoothScalar_contDiff f).contDiffAt.isSymmSndFDerivAt (by simp) v w)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem airyFlux_divergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) :
    twoFluxDivergence v (airyFlux v φ) = 0 := by
  have h01 := smoothDirection_comm (v 0) (v 1)
  funext i
  fin_cases i <;> simp [twoFluxDivergence, airyFlux, h01]

theorem transverseFlux_divergence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (ψ η ω : SmoothScalar E) :
    twoFluxDivergence v (transverseFlux v ψ η ω) = 0 := by
  have h02 := smoothDirection_comm (v 0) (v 2)
  have h12 := smoothDirection_comm (v 1) (v 2)
  funext i
  fin_cases i <;> simp [twoFluxDivergence, transverseFlux, h02, h12]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_SmoothPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem smoothDirection_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (f g : SmoothScalar E) :
    smoothDirection v (f * g) = f * smoothDirection v g + g * smoothDirection v f := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (f.val * g.val) x v =
    f.val x * fderiv ℝ g.val x v + g.val x * fderiv ℝ f.val x v
  rw [fderiv_mul ((smoothScalar_contDiff f).differentiable (by simp) x)
    ((smoothScalar_contDiff g).differentiable (by simp) x)]
  rfl

theorem smoothDirection_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) :
    smoothDirection v (smoothPhase L H) = L v • smoothPhase L (smoothDirection 1 H) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (H.val ∘ L) x v = L v * fderiv ℝ H.val (L x) 1
  rw [fderiv_comp x ((smoothScalar_contDiff H).differentiable (by simp) (L x))
    L.differentiableAt, L.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  simpa only [smul_eq_mul, mul_one] using (fderiv ℝ H.val (L x)).map_smul (L v) 1

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AirySymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

theorem airy_transverse_span {ξ : Fin 3 → ℝ} (hξ : ξ ≠ 0)
    {F : Fin 5 → ℝ} (hF : divSymbolTwo ξ *ᵥ F = 0) :
    ∃ α p q r : ℝ, F = α • airySymbol ξ + transverseSymbol ξ p q r := by
  have h0 := congr_fun hF 0
  have h1 := congr_fun hF 1
  simp [divSymbolTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
  by_cases hz : ξ 2 = 0
  · by_cases hx : ξ 0 = 0
    · have hy : ξ 1 ≠ 0 := by
        intro hy
        apply hξ
        funext i
        fin_cases i <;> simp [hx, hy, hz]
      have hb : F 1 = 0 := by simpa [hx, hz, hy] using h0
      have hc : F 2 = 0 := by simpa [hx, hz, hy] using h1
      refine ⟨F 0 / ξ 1 ^ 2, 0, -F 3 / ξ 1, -F 4 / ξ 1, ?_⟩
      funext i
      fin_cases i <;> simp [airySymbol, transverseSymbol, hx, hz, hb, hc, hy] <;> field_simp
    · have hb : ξ 0 * F 1 = -(ξ 1 * F 2) := by
        simp only [hz, zero_mul, add_zero] at h1
        linarith
      have ha : ξ 0 ^ 2 * F 0 = ξ 1 ^ 2 * F 2 := by
        simp only [hz, zero_mul, add_zero] at h0
        nlinarith [congrArg (fun t => ξ 1 * t) hb, congrArg (fun t => ξ 0 * t) h0]
      refine ⟨F 2 / ξ 0 ^ 2, -F 3 / ξ 0 + ξ 1 * F 4 / ξ 0 ^ 2,
        -F 4 / ξ 0, 0, ?_⟩
      funext i
      fin_cases i <;> simp [airySymbol, transverseSymbol, hz] <;>
        field_simp [hx] <;> nlinarith [hb, ha]
  · refine ⟨0, F 0 / ξ 2, F 1 / ξ 2, F 2 / ξ 2, ?_⟩
    funext i
    fin_cases i <;> simp [airySymbol, transverseSymbol] <;>
      field_simp <;> nlinarith [h0, h1]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_LocalizedFirstPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem localizedFirstPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (localizedFirstPotential χ L H k) =
      L v • (χ * smoothPhase (k • L) (smoothDirection 1 H)) +
        k⁻¹ • (smoothPhase (k • L) H * smoothDirection v χ) := by
  simp only [localizedFirstPotential, map_smul, smoothDirection_mul,
    smoothDirection_phase]
  apply Subtype.ext
  funext x
  change k⁻¹ * (χ.val x * ((k * L v) *
    (smoothDirection 1 H).val (k * L x)) +
    H.val (k * L x) * (smoothDirection v χ).val x) =
    L v * (χ.val x * (smoothDirection 1 H).val (k * L x)) +
      k⁻¹ * (H.val (k * L x) * (smoothDirection v χ).val x)
  field_simp

theorem localizedSecondPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (smoothDirection w (localizedSecondPotential χ L H k)) =
      (L v * L w) •
        (χ * smoothPhase (k • L) (smoothDirection 1 (smoothDirection 1 H))) +
      k⁻¹ • ((L w • smoothDirection v χ + L v • smoothDirection w χ) *
        smoothPhase (k • L) (smoothDirection 1 H)) +
      (k ^ 2)⁻¹ • (smoothPhase (k • L) H *
        smoothDirection v (smoothDirection w χ)) := by
  simp only [localizedSecondPotential, map_smul, map_add, smoothDirection_mul,
    smoothDirection_phase]
  apply Subtype.ext
  funext x
  change (k ^ 2)⁻¹ *
    (χ.val x * ((k * L w) * ((k * L v) *
       (smoothDirection 1 (smoothDirection 1 H)).val (k * L x))) +
    ((k * L w) * (smoothDirection 1 H).val (k * L x)) *
      (smoothDirection v χ).val x +
    (H.val (k * L x) * (smoothDirection v (smoothDirection w χ)).val x +
      (smoothDirection w χ).val x * ((k * L v) *
        (smoothDirection 1 H).val (k * L x)))) =
    (L v * L w) * (χ.val x *
      (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)) +
    k⁻¹ * ((L w * (smoothDirection v χ).val x +
      L v * (smoothDirection w χ).val x) *
        (smoothDirection 1 H).val (k * L x)) +
    (k ^ 2)⁻¹ * (H.val (k * L x) *
      (smoothDirection v (smoothDirection w χ)).val x)
  field_simp
  ring

open Filter Topology

theorem uniform_zero_of_bound {X I : Type*} {l : Filter I}
    {f : I → X → ℝ} {b : I → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ x, |f i x| ≤ b i) :
    TendstoUniformly f (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hf, hb.eventually_lt_const hε] with i hi hib x
  simpa only [dist_zero_left, Real.norm_eq_abs] using (hi x).trans_lt hib

theorem localizedFirstPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (hχ : HasCompactSupport χ.val)
    (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => (smoothDirection v (localizedFirstPotential χ L H k)).val x -
        L v * (χ.val x * (smoothDirection 1 H).val (k * L x)))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff (smoothDirection v χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := hH
  have hBnonneg : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [localizedFirstPotential_derivative v χ L H (ne_of_gt hk)]
    change |L v * (χ.val x * (smoothDirection 1 H).val (k * L x)) +
      k⁻¹ * (H.val (k * L x) * (smoothDirection v χ).val x) -
        L v * (χ.val x * (smoothDirection 1 H).val (k * L x))| ≤ |k⁻¹| * B * A
    rw [add_sub_cancel_left, abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hA x)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBnonneg)

theorem localizedSecondPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v w : E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (hχ : HasCompactSupport χ.val)
    (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (hH' : ∃ C : ℝ, ∀ t, |(smoothDirection 1 H).val t| ≤ C) :
    TendstoUniformly
      (fun k x =>
        (smoothDirection v (smoothDirection w (localizedSecondPotential χ L H k))).val x -
        (L v * L w) *
          (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff (smoothDirection v χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := ((smoothScalar_contDiff (smoothDirection w χ)).continuous).bounded_above_of_compact_support (compactSupport_smoothDirection w hχ)
  obtain ⟨C, hC⟩ :=
    ((smoothScalar_contDiff (smoothDirection v (smoothDirection w χ))).continuous).bounded_above_of_compact_support
        (compactSupport_smoothDirection v (compactSupport_smoothDirection w hχ))
  obtain ⟨M, hM⟩ := hH
  obtain ⟨N, hN⟩ := hH'
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hTn : 0 ≤ |L w| * A + |L v| * B := by positivity
  apply uniform_zero_of_bound (b := fun k : ℝ =>
    |k⁻¹| * ((|L w| * A + |L v| * B) * N) + |(k ^ 2)⁻¹| * (M * C))
  · have hi : Tendsto (fun k : ℝ => |k⁻¹|) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).abs
    have hi2 : Tendsto (fun k : ℝ => |(k ^ 2)⁻¹|) atTop (𝓝 0) := by
      simpa [inv_pow, abs_pow] using hi.pow 2
    simpa using (hi.mul_const ((|L w| * A + |L v| * B) * N)).add
      (hi2.mul_const (M * C))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [localizedSecondPotential_derivative v w χ L H (ne_of_gt hk)]
    change |(L v * L w) *
      (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x)) +
      k⁻¹ * ((L w * (smoothDirection v χ).val x +
        L v * (smoothDirection w χ).val x) * (smoothDirection 1 H).val (k * L x)) +
      (k ^ 2)⁻¹ * (H.val (k * L x) *
        (smoothDirection v (smoothDirection w χ)).val x) -
      (L v * L w) *
        (χ.val x * (smoothDirection 1 (smoothDirection 1 H)).val (k * L x))| ≤ _
    rw [add_assoc, add_sub_cancel_left]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul _ (hN _) (abs_nonneg _) hTn
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hA x) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using hB x) (abs_nonneg _))
    · rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul (hM _) (by simpa only [Real.norm_eq_abs] using hC x)
        (abs_nonneg _) hMn

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_LocalizedTwoFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

theorem uniform_zero_const_mul {X I : Type*} {l : Filter I}
    {f : I → X → ℝ} (c : ℝ) (hf : TendstoUniformly f (fun _ => 0) l) :
    TendstoUniformly (fun i x => c * f i x) (fun _ => 0) l := by
  simpa [Function.comp_def] using
    (uniformContinuous_const_smul (X := ℝ) c).comp_tendstoUniformly hf

theorem uniform_zero_add {X I : Type*} {l : Filter I} {f g : I → X → ℝ}
    (hf : TendstoUniformly f (fun _ => 0) l)
    (hg : TendstoUniformly g (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x + g i x) (fun _ => 0) l := by
  have hh := hf.add hg
  change TendstoUniformly (fun i x => f i x + g i x) (fun _ => (0 : ℝ) + 0) l at hh
  simpa only [add_zero] using hh

theorem uniform_zero_sub {X I : Type*} {l : Filter I} {f g : I → X → ℝ}
    (hf : TendstoUniformly f (fun _ => 0) l)
    (hg : TendstoUniformly g (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x - g i x) (fun _ => 0) l := by
  have hh := hf.sub hg
  change TendstoUniformly (fun i x => f i x - g i x) (fun _ => (0 : ℝ) - 0) l at hh
  simpa only [sub_zero] using hh

theorem twoFluxDivergence_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (F G : Fin 5 → SmoothScalar E) :
    twoFluxDivergence v (F + G) = twoFluxDivergence v F + twoFluxDivergence v G := by
  funext i
  fin_cases i <;> simp [twoFluxDivergence] <;> abel

theorem twoFluxDivergence_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (c : ℝ) (F : Fin 5 → SmoothScalar E) :
    twoFluxDivergence v (c • F) = c • twoFluxDivergence v F := by
  funext i
  fin_cases i <;> simp [twoFluxDivergence, smul_add]

theorem localizedTwoFlux_divergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) :
    twoFluxDivergence v (localizedTwoFlux v χ L H₁ H₂ α p q r k) = 0 := by
  rw [localizedTwoFlux, twoFluxDivergence_add, twoFluxDivergence_smul,
    airyFlux_divergence, transverseFlux_divergence, smul_zero, zero_add]

theorem localizedTwoFlux_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (h H₁ H₂ : SmoothScalar ℝ) (α p q r : ℝ)
    (hχ : HasCompactSupport χ.val)
    (h₁ : smoothDirection 1 H₁ = h) (h₂ : smoothDirection 1 H₂ = H₁)
    (hB₁ : ∃ C : ℝ, ∀ t, |H₁.val t| ≤ C)
    (hB₂ : ∃ C : ℝ, ∀ t, |H₂.val t| ≤ C) (i : Fin 5) :
    TendstoUniformly
      (fun k x => (localizedTwoFlux v χ L H₁ H₂ α p q r k i).val x -
        (α • airySymbol (fun j => L (v j)) +
          transverseSymbol (fun j => L (v j)) p q r) i *
            (χ.val x * h.val (k * L x))) (fun _ => 0) atTop := by
  have hfirst (j : Fin 3) :=
    localizedFirstPotential_error_tendsto (v j) χ L H₁ hχ hB₁
  simp only [h₁] at hfirst
  have hsecond (j l : Fin 3) :=
    localizedSecondPotential_error_tendsto (v j) (v l) χ L H₂ hχ hB₂
      (by simpa only [h₂] using hB₁)
  simp only [h₂, h₁] at hsecond
  fin_cases i
  · convert uniform_zero_add (uniform_zero_const_mul α (hsecond 1 1))
      (uniform_zero_const_mul p (hfirst 2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_add (uniform_zero_const_mul (-α) (hsecond 0 1))
      (uniform_zero_const_mul q (hfirst 2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_add (uniform_zero_const_mul α (hsecond 0 0))
      (uniform_zero_const_mul r (hfirst 2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul, Subalgebra.coe_add]
    ring
  · convert uniform_zero_sub (uniform_zero_const_mul (-p) (hfirst 0))
      (uniform_zero_const_mul q (hfirst 1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul]
    ring
  · convert uniform_zero_sub (uniform_zero_const_mul (-q) (hfirst 0))
      (uniform_zero_const_mul r (hfirst 1)) using 1
    all_goals try with_reducible_and_instances rfl
    funext k x
    simp [localizedTwoFlux, airyFlux, transverseFlux, airySymbol, transverseSymbol,
      map_smul]
    ring

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem meanZeroPrimitive_mean (h : SmoothScalar ℝ) :
    ∫ t in (0 : ℝ)..1, (meanZeroPrimitive h).val t = 0 := by
  change (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t -
    ∫ s in (0 : ℝ)..1, (smoothPrimitive h).val s) = 0
  rw [intervalIntegral.integral_sub
    ((smoothScalar_contDiff (smoothPrimitive h)).continuous.intervalIntegrable _ _)
    (intervalIntegrable_const)]
  simp [intervalIntegral.integral_const]

theorem meanZeroPrimitive_periodic (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    Function.Periodic (meanZeroPrimitive h).val 1 := by
  intro x
  change (∫ t in (0 : ℝ)..x + 1, h.val t) -
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t) =
    (∫ t in (0 : ℝ)..x, h.val t) -
    (∫ t in (0 : ℝ)..1, (smoothPrimitive h).val t)
  rw [hp.intervalIntegral_add_eq_add 0 x
    (fun a b => (smoothScalar_contDiff h).continuous.intervalIntegrable a b)]
  simp only [zero_add, hm, add_zero]

theorem periodic_smoothScalar_bounded (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) : ∃ C : ℝ, ∀ t, |h.val t| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (hp.isBounded_of_continuous one_ne_zero (smoothScalar_contDiff h).continuous).exists_norm_le
  exact ⟨C, fun t => by simpa only [Real.norm_eq_abs] using hC _ ⟨t, rfl⟩⟩

theorem periodic_two_primitives (h : SmoothScalar ℝ)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    ∃ H₁ H₂ : SmoothScalar ℝ,
      smoothDirection 1 H₁ = h ∧ smoothDirection 1 H₂ = H₁ ∧
      Function.Periodic H₁.val 1 ∧ Function.Periodic H₂.val 1 ∧
      (∃ C : ℝ, ∀ t, |H₁.val t| ≤ C) ∧
      (∃ C : ℝ, ∀ t, |H₂.val t| ≤ C) := by
  let H₁ := meanZeroPrimitive h
  let H₂ := meanZeroPrimitive H₁
  have hp₁ : Function.Periodic H₁.val 1 := meanZeroPrimitive_periodic h hp hm
  have hp₂ : Function.Periodic H₂.val 1 :=
    meanZeroPrimitive_periodic H₁ hp₁ (meanZeroPrimitive_mean h)
  exact ⟨H₁, H₂, smoothDirection_meanZeroPrimitive h,
    smoothDirection_meanZeroPrimitive H₁, hp₁, hp₂,
    periodic_smoothScalar_bounded H₁ hp₁, periodic_smoothScalar_bounded H₂ hp₂⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothSupportedAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section

theorem smooth_supported_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f g : SmoothScalar E}
    (hf : tsupport f.val ⊆ K) (hg : tsupport g.val ⊆ K) :
    tsupport (f + g).val ⊆ K :=
  (tsupport_add f.val g.val).trans (Set.union_subset hf hg)

theorem smooth_supported_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (c : ℝ) {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) :
    tsupport (c • f).val ⊆ K :=
  (tsupport_smul_subset_right (fun _ => c) f.val).trans hf

theorem smooth_supported_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) :
    tsupport (-f).val ⊆ K := by
  change tsupport (-f.val) ⊆ K
  rwa [tsupport_neg]

theorem smooth_supported_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {f g : SmoothScalar E}
    (hf : tsupport f.val ⊆ K) (hg : tsupport g.val ⊆ K) :
    tsupport (f - g).val ⊆ K :=
  (tsupport_sub f.val g.val).trans (Set.union_subset hf hg)

theorem localizedFirstPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (localizedFirstPotential χ L H k).val ⊆ tsupport χ.val := by
  apply smooth_supported_smul
  exact tsupport_mul_subset_left

theorem localizedSecondPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (localizedSecondPotential χ L H k).val ⊆ tsupport χ.val := by
  apply smooth_supported_smul
  exact tsupport_mul_subset_left

theorem airyFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (φ : SmoothScalar E) (i : Fin 5) :
    tsupport (airyFlux v φ i).val ⊆ tsupport φ.val := by
  have hd (j l : Fin 3) :=
    (tsupport_smoothDirection_subset (v j) (smoothDirection (v l) φ)).trans
      (tsupport_smoothDirection_subset (v l) φ)
  fin_cases i
  · exact hd 1 1
  · exact smooth_supported_neg (hd 0 1)
  · exact hd 0 0
  · change tsupport (0 : E → ℝ) ⊆ _
    simp
  · change tsupport (0 : E → ℝ) ⊆ _
    simp

theorem transverseFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) {K : Set E} {ψ η ω : SmoothScalar E}
    (hψ : tsupport ψ.val ⊆ K) (hη : tsupport η.val ⊆ K)
    (hω : tsupport ω.val ⊆ K) (i : Fin 5) :
    tsupport (transverseFlux v ψ η ω i).val ⊆ K := by
  have hd {f : SmoothScalar E} (hf : tsupport f.val ⊆ K) (j : Fin 3) :=
    (tsupport_smoothDirection_subset (v j) f).trans hf
  fin_cases i
  · exact hd hψ 2
  · exact hd hη 2
  · exact hd hω 2
  · exact smooth_supported_sub (smooth_supported_neg (hd hψ 0)) (hd hη 1)
  · exact smooth_supported_sub (smooth_supported_neg (hd hη 0)) (hd hω 1)

theorem localizedTwoFlux_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (H₁ H₂ : SmoothScalar ℝ) (α p q r k : ℝ) (i : Fin 5) :
    tsupport (localizedTwoFlux v χ L H₁ H₂ α p q r k i).val ⊆ tsupport χ.val := by
  apply smooth_supported_add
  · exact smooth_supported_smul α
      ((airyFlux_support v (localizedSecondPotential χ L H₂ k) i).trans
        (localizedSecondPotential_support χ L H₂ k))
  · exact transverseFlux_support v
      (smooth_supported_smul p (localizedFirstPotential_support χ L H₁ k))
      (smooth_supported_smul q (localizedFirstPotential_support χ L H₁ k))
      (smooth_supported_smul r (localizedFirstPotential_support χ L H₁ k)) i

open Matrix

theorem exists_localized_two_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (χ : SmoothScalar E) (L : E →L[ℝ] ℝ)
    (h : SmoothScalar ℝ) (R : Fin 5 → ℝ)
    (hχ : HasCompactSupport χ.val) (hξ : (fun j => L (v j)) ≠ 0)
    (hR : divSymbolTwo (fun j => L (v j)) *ᵥ R = 0)
    (hp : Function.Periodic h.val 1) (hm : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    ∃ G : ℝ → Fin 5 → SmoothScalar E,
      (∀ k, twoFluxDivergence v (G k) = 0) ∧
      (∀ k i, tsupport (G k i).val ⊆ tsupport χ.val) ∧
      ∀ i, TendstoUniformly
        (fun k x => (G k i).val x - R i * (χ.val x * h.val (k * L x)))
        (fun _ => 0) Filter.atTop := by
  obtain ⟨α, p, q, r, hspan⟩ := airy_transverse_span hξ hR
  obtain ⟨H₁, H₂, h₁, h₂, _, _, hB₁, hB₂⟩ := periodic_two_primitives h hp hm
  refine ⟨localizedTwoFlux v χ L H₁ H₂ α p q r,
    localizedTwoFlux_divergence v χ L H₁ H₂ α p q r,
    localizedTwoFlux_support v χ L H₁ H₂ α p q r, ?_⟩
  intro i
  rw [hspan]
  exact localizedTwoFlux_error_tendsto v χ L h H₁ H₂ α p q r hχ h₁ h₂ hB₁ hB₂ i

end

theorem lineShift_bijective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) (f : E → ℝ) (hf : Differentiable ℝ f)
    (hpos : ∀ x, 0 < 1 + fderiv ℝ f x d)
    (hbound : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    Function.Bijective (lineShift d f) := by
  have hd (y : E) (t : ℝ) : HasDerivAt (fun s => s + f (y + s • d))
      (1 + fderiv ℝ f (y + t • d) d) t := by
    have hline : HasDerivAt (fun s : ℝ => y + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    exact (hasDerivAt_id t).add ((hf _).hasFDerivAt.comp_hasDerivAt t hline)
  have hm (y : E) : StrictMono (fun s : ℝ => s + f (y + s • d)) := by
    apply strictMono_of_deriv_pos
    intro t
    rw [(hd y t).deriv]
    exact hpos _
  constructor
  · intro x y hxy
    have hx : x = y + (f y - f x) • d := by
      dsimp [lineShift] at hxy
      calc
        x = (x + f x • d) - f x • d := by abel
        _ = (y + f y • d) - f x • d := congrArg (fun z => z - f x • d) hxy
        _ = y + (f y - f x) • d := by module
    have harg : (f y - f x) + f (y + (f y - f x) • d) =
        (0 : ℝ) + f (y + (0 : ℝ) • d) := by
      rw [← hx]
      simp
    have heq := (hm y).injective harg
    rw [heq] at hx
    simpa using hx
  · obtain ⟨B, hB⟩ := hbound
    have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
    intro y
    have hcont : Continuous (fun t : ℝ => t + f (y + t • d)) :=
      continuous_id.add (hf.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const)))
    have hlo : (-B - 1) + f (y + (-B - 1) • d) ≤ 0 := by
      have := (abs_le.mp (hB (y + (-B - 1) • d))).2
      linarith
    have hhi : 0 ≤ (B + 1) + f (y + (B + 1) • d) := by
      have := (abs_le.mp (hB (y + (B + 1) • d))).1
      linarith
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -B - 1 ≤ B + 1)
      hcont.continuousOn ⟨hlo, hhi⟩
    refine ⟨y + t • d, ?_⟩
    change t + f (y + t • d) = 0 at ht
    dsimp [lineShift]
    rw [add_assoc, ← add_smul, ht, zero_smul, add_zero]

theorem exists_smooth_lineShift_inverse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (f : SmoothScalar E)
    (hpos : ∀ x, 0 < 1 + fderiv ℝ f.val x d)
    (hbound : ∃ B : ℝ, ∀ x, |f.val x| ≤ B) :
    ∃ X : E ≃ E, (∀ x, X x = lineShift d f.val x) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm := by
  let X := Equiv.ofBijective (lineShift d f.val)
    (lineShift_bijective d f.val ((smoothScalar_contDiff f).differentiable (by simp)) hpos hbound)
  have hs : ContDiff ℝ (↑(⊤ : ℕ∞)) (lineShift d f.val) :=
    contDiff_id.add ((smoothScalar_contDiff f).smul contDiff_const)
  refine ⟨X, fun _ => rfl, hs, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  let x := X.symm y
  let T := rankOneEquiv d (fderiv ℝ f.val x) (ne_of_gt (hpos x))
  have hT : HasFDerivAt (lineShift d f.val) (T : E →L[ℝ] E) x := by
    exact (hasFDerivAt_id x).add
      (((smoothScalar_contDiff f).differentiable (by simp) x).hasFDerivAt.smul_const d)
  have hh := hs.contDiffAt.to_localInverse hT (by simp)
  have he := (hs.contDiffAt.hasStrictFDerivAt' hT (by simp)).localInverse_unique
    (g := X.symm) (Filter.Eventually.of_forall X.symm_apply_apply)
  have hxy : lineShift d f.val x = y := X.apply_symm_apply y
  rw [hxy] at hh he
  exact hh.congr_of_eventuallyEq he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TwoFluxColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem smooth_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (f g : SmoothScalar E) (hf : HasCompactSupport f.val) :
    (∫ x, f.val x * (smoothDirection v g).val x ∂μ) =
      -(∫ x, (smoothDirection v f).val x * g.val x ∂μ) := by
  have hc (a b : SmoothScalar E) (ha : HasCompactSupport a.val) :
      Integrable (fun x => a.val x * b.val x) μ :=
    ((smoothScalar_contDiff a).continuous.mul (smoothScalar_contDiff b).continuous).integrable_of_hasCompactSupport ha.mul_right
  exact integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (hc (smoothDirection v f) g (compactSupport_smoothDirection v hf))
    (hc f (smoothDirection v g) hf) (hc f g hf)
    (fun x _ => ((smoothScalar_contDiff f).differentiable (by simp) x).hasFDerivAt)
    (fun x _ => ((smoothScalar_contDiff g).differentiable (by simp) x).hasFDerivAt)

theorem smooth_divergence_zero_pairing
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : ι → E) (F : ι → SmoothScalar E)
    (hF : ∀ i, HasCompactSupport (F i).val)
    (hdiv : ∑ i, smoothDirection (v i) (F i) = 0) (ψ : SmoothScalar E) :
    (∫ x, ∑ i, (F i).val x * (smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  have hI (i : ι) : Integrable (fun x => (F i).val x *
      (smoothDirection (v i) ψ).val x) μ :=
    ((smoothScalar_contDiff (F i)).continuous.mul
      (smoothScalar_contDiff (smoothDirection (v i) ψ)).continuous).integrable_of_hasCompactSupport (hF i).mul_right
  have hI' (i : ι) : Integrable (fun x => (smoothDirection (v i) (F i)).val x *
      ψ.val x) μ :=
    ((smoothScalar_contDiff (smoothDirection (v i) (F i))).continuous.mul
      (smoothScalar_contDiff ψ).continuous).integrable_of_hasCompactSupport
        (compactSupport_smoothDirection (v i) (hF i)).mul_right
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [smooth_integration_by_parts μ _ _ _ (hF _)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hI' i)]
  have hz (x : E) : ∑ i, (smoothDirection (v i) (F i)).val x = 0 := by
    have hh := congrArg (fun f : SmoothScalar E => f.val x) hdiv
    simpa using hh
  simp_rw [← Finset.sum_mul, hz, zero_mul]
  simp

theorem twoFluxColumns_divergence {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (j : Fin 2) :
    ∑ i, smoothDirection (v i) (twoFluxColumns G j i) = twoFluxDivergence v G j := by
  fin_cases j <;> simp [twoFluxColumns, twoFluxDivergence, Fin.sum_univ_succ, add_assoc]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_AdaptedSpatialBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section

theorem exists_adapted_spatial_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 3)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D) :
    ∃ v : Module.Basis (Fin 3) ℝ E,
      D (v 0) = Pi.single 0 1 ∧ D (v 1) = Pi.single 1 1 ∧ D (v 2) = 0 := by
  classical
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hD
  have hk := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top,
    Module.finrank_pi, Fintype.card_fin, hdim] at hk
  have hkp : 0 < Module.finrank ℝ D.ker := by omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkp
  have hw0 : (w : E) ≠ 0 := fun h => hw (Subtype.ext h)
  have hDw : D (w : E) = 0 := w.property
  let v : Fin 3 → E := ![Q (Pi.single 0 1), Q (Pi.single 1 1), w]
  have hv : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hs : c 0 • Q (Pi.single 0 1) + c 1 • Q (Pi.single 1 1) + c 2 • (w : E) = 0 := by
      simpa [v, Fin.sum_univ_succ, add_assoc] using hc
    have hh := congrArg D hs
    simp only [map_add, map_smul, hQ (Pi.single 0 1), hQ (Pi.single 1 1), hDw,
      smul_zero, add_zero, map_zero] at hh
    have h0 : c 0 = 0 := by simpa using congr_fun hh 0
    have h1 : c 1 = 0 := by simpa using congr_fun hh 1
    have h2 : c 2 = 0 := by
      simp only [h0, h1, zero_smul, zero_add] at hs
      exact (smul_eq_zero.mp hs).resolve_right hw0
    intro i
    fin_cases i <;> assumption
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hdim.symm)
  have hb : (b : Fin 3 → E) = v := coe_basisOfLinearIndependentOfCardEqFinrank hv _
  refine ⟨b, ?_, ?_, ?_⟩
  · rw [hb]
    exact hQ _
  · rw [hb]
    exact hQ _
  · rw [hb]
    exact hDw

open Filter Topology

lemma rawTwoSpatial_symmetry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (r : Fin 5 → ℝ) :
    D (rawTwoSpatial v r 0) 1 = D (rawTwoSpatial v r 1) 0 := by
  simp [rawTwoSpatial, map_add, map_smul, h0, h1, h2]

lemma adapted_basis_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Module.Basis (Fin 3) ℝ E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (x : E) (i : Fin 2) :
    D x i = v.repr x i.castSucc := by
  have hx := congrArg D (v.sum_repr x)
  rw [Fin.sum_univ_three] at hx
  simp only [map_add, map_smul, h0, h1, h2, smul_zero, add_zero] at hx
  fin_cases i
  · simpa using (congr_fun hx 0).symm
  · simpa using (congr_fun hx 1).symm

lemma exists_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Module.Basis (Fin 3) ℝ E) (D : E →L[ℝ] (Fin 2 → ℝ))
    (h0 : D (v 0) = Pi.single 0 1) (h1 : D (v 1) = Pi.single 1 1)
    (h2 : D (v 2) = 0) (R : Fin 2 → E)
    (hR : D (R 0) 1 = D (R 1) 0) :
    ∃ r : Fin 5 → ℝ, rawTwoSpatial v r = R := by
  have hs : v.repr (R 0) 1 = v.repr (R 1) 0 := by
    simpa [adapted_basis_coordinate v D h0 h1 h2] using hR
  refine ⟨![v.repr (R 0) 0, v.repr (R 0) 1, v.repr (R 1) 1,
    v.repr (R 0) 2, v.repr (R 1) 2], ?_⟩
  funext i
  fin_cases i
  · change v.repr (R 0) 0 • v 0 + v.repr (R 0) 1 • v 1 + v.repr (R 0) 2 • v 2 = R 0
    simpa only [Fin.sum_univ_three] using v.sum_repr (R 0)
  · change v.repr (R 0) 1 • v 0 + v.repr (R 1) 1 • v 1 + v.repr (R 1) 2 • v 2 = R 1
    rw [hs]
    simpa only [Fin.sum_univ_three] using v.sum_repr (R 1)

lemma rawTwoSpatial_symbol
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (L : E →L[ℝ] ℝ) (r : Fin 5 → ℝ) :
    divSymbolTwo (fun i => L (v i)) *ᵥ r = fun j => L (rawTwoSpatial v r j) := by
  ext j
  fin_cases j <;> simp [rawTwoSpatial, divSymbolTwo, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, map_add, map_smul] <;> ring

lemma smooth_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => rawTwoSpatial v (fun i => (G i).val x) j) := by
  fin_cases j <;>
    exact (((smoothScalar_contDiff (G _)).smul contDiff_const).add
      ((smoothScalar_contDiff (G _)).smul contDiff_const)).add
        ((smoothScalar_contDiff (G _)).smul contDiff_const)

lemma support_rawTwoSpatial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) {K : Set E}
    (hK : IsClosed K) (hG : ∀ i, tsupport (G i).val ⊆ K) (j : Fin 2) :
    tsupport (fun x => rawTwoSpatial v (fun i => (G i).val x) j) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have hz (i : Fin 5) : (G i).val x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hn (hG i ht))
  apply hx
  fin_cases j <;> simp [rawTwoSpatial, hz]

lemma rawTwoSpatial_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (G : Fin 5 → SmoothScalar E) (ψ : SmoothScalar E)
    (j : Fin 2) (x : E) :
    fderiv ℝ ψ.val x (rawTwoSpatial v (fun i => (G i).val x) j) =
      ∑ i, (twoFluxColumns G j i).val x * (smoothDirection (v i) ψ).val x := by
  fin_cases j <;> simp [rawTwoSpatial, twoFluxColumns, smoothDirection,
    Fin.sum_univ_succ, map_add, map_smul, add_assoc]

end

open MeasureTheory Filter Topology

lemma uniform_zero_smul_vector {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter I} {f : I → X → ℝ} (v : E)
    (hf : TendstoUniformly f (fun _ => 0) l) :
    TendstoUniformly (fun i x => f i x • v) (fun _ => 0) l := by
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).uniformContinuous.comp_tendstoUniformly hf

lemma rawTwoSpatial_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Fin 3 → E) (g r : Fin 5 → ℝ) (z : ℝ) (j : Fin 2) :
    rawTwoSpatial v g j - z • rawTwoSpatial v r j =
      rawTwoSpatial v (fun i => g i - r i * z) j := by
  fin_cases j <;> simp [rawTwoSpatial, sub_smul, mul_smul, smul_add] <;> module

lemma rawTwoSpatial_error_tendsto
    {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter I} (v : Fin 3 → E) (G : I → X → Fin 5 → ℝ)
    (r : Fin 5 → ℝ) (z : I → X → ℝ)
    (hG : ∀ i, TendstoUniformly (fun k x => G k x i - r i * z k x)
      (fun _ => 0) l) (j : Fin 2) :
    TendstoUniformly (fun k x => rawTwoSpatial v (G k x) j - z k x • rawTwoSpatial v r j)
      (fun _ => 0) l := by
  simp_rw [rawTwoSpatial_error]
  have hc (i : Fin 5) (a : Fin 3) := uniform_zero_smul_vector (v a) (hG i)
  fin_cases j
  · convert ((hc 0 0).add (hc 1 1)).add (hc 3 2) using 1 <;> ext <;> simp [rawTwoSpatial]
  · convert ((hc 1 0).add (hc 2 1)).add (hc 4 2) using 1 <;> ext <;> simp [rawTwoSpatial]

theorem exists_physical_two_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (χ : SmoothScalar E) (hχ : HasCompactSupport χ.val)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (h : SmoothScalar ℝ) (hp : Function.Periodic h.val 1)
    (hm : ∫ t in (0 : ℝ)..1, h.val t = 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0)
    (hRn : ∀ j, L (R j) = 0) :
    ∃ F : ℝ → Fin 2 → E → E,
      (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
      (∀ k j, tsupport (F k j) ⊆ tsupport χ.val) ∧
      (∀ k x, D (F k 0 x) 1 = D (F k 1 x) 0) ∧
      (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ x, fderiv ℝ ψ x (F k j x) ∂μ) = 0) ∧
      ∀ j, TendstoUniformly
        (fun k x => F k j x - (χ.val x * h.val (k * L x)) • R j)
        (fun _ => 0) atTop := by
  obtain ⟨v, h0, h1, h2⟩ := exists_adapted_spatial_basis hdim D hD
  obtain ⟨r, hr⟩ := exists_rawTwoSpatial v D h0 h1 h2 R hRs
  have hξ : (fun i => L (v i)) ≠ 0 := by
    intro hz
    apply hL
    ext x
    have hx := congrArg L (v.sum_repr x)
    simp only [map_sum, map_smul] at hx
    have hv (i : Fin 3) : L (v i) = 0 := congr_fun hz i
    simpa only [hv, smul_zero, Finset.sum_const_zero, _root_.zero_apply]
      using hx.symm
  have hsymbol : divSymbolTwo (fun i => L (v i)) *ᵥ r = 0 := by
    rw [rawTwoSpatial_symbol, hr]
    exact funext hRn
  obtain ⟨G, hdiv, hs, he⟩ := exists_localized_two_flux v χ L h r hχ hξ hsymbol hp hm
  let F : ℝ → Fin 2 → E → E := fun k j x => rawTwoSpatial v (fun i => (G k i).val x) j
  refine ⟨F, (fun k j => smooth_rawTwoSpatial v (G k) j),
    (fun k j => support_rawTwoSpatial v (G k) (isClosed_tsupport _) (hs k) j),
    (fun k x => rawTwoSpatial_symmetry v D h0 h1 h2 _), ?_, ?_⟩
  · intro k j ψ hψ
    let Ψ : SmoothScalar E := ⟨ψ, hψ⟩
    change (∫ x, fderiv ℝ Ψ.val x (rawTwoSpatial v (fun i => (G k i).val x) j) ∂μ) = 0
    simp_rw [rawTwoSpatial_pairing]
    apply smooth_divergence_zero_pairing μ v _ _ _ Ψ
    · have hc (i : Fin 5) : HasCompactSupport (G k i).val :=
        hχ.of_isClosed_subset (isClosed_tsupport _) (hs k i)
      intro i
      fin_cases j <;> fin_cases i <;> exact hc _
    · rw [twoFluxColumns_divergence, hdiv]
      rfl
  · intro j
    have ht := rawTwoSpatial_error_tendsto v (fun k x i => (G k i).val x) r
      (fun k x => χ.val x * h.val (k * L x)) he j
    simpa only [hr] using ht

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPiolaFluxSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma localPiolaFlux_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F G : E → E) :
    localPiolaFlux X (fun x => F x - G x) =
      fun x => localPiolaFlux X F x - localPiolaFlux X G x := by
  classical
  funext x
  by_cases hx : x ∈ X.target <;> simp [localPiolaFlux, hx, map_sub, smul_sub]

lemma localPiolaFlux_linear_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ X.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ (F : E → E), Function.support F ⊆ K → ∀ y,
      ‖localPiolaFlux X F y‖ ≤ B * ‖F (X.symm y)‖ := by
  classical
  let T : E → E →L[ℝ] E := fun x => |(fderiv ℝ X x).det|⁻¹ • fderiv ℝ X x
  have hT : ContinuousOn T X.source := by
    intro x hx
    have hd : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ X) x :=
      (hX.contDiffAt (X.open_source.mem_nhds hx)).fderiv_right (by simp)
    have hdet0 := local_fderiv_det_ne_zero X (hX.differentiableOn (by simp))
      (hXi.differentiableOn (by simp)) hx
    have hdet := ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).contDiffAt.comp x hd).abs hdet0
    exact ((hdet.inv (abs_ne_zero.mpr hdet0)).smul hd).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hT.mono hKs)).isBounded.exists_norm_le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro F hF y
  by_cases hy : y ∈ X.target
  · by_cases hxy : X.symm y ∈ K
    · change ‖(if y ∈ X.target then _ else 0)‖ ≤ _
      simp only [ite_eq_left hy]
      change ‖T (X.symm y) (F (X.symm y))‖ ≤ _
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((hC _ (mem_image_of_mem _ hxy)).trans (le_max_left _ _))
          (norm_nonneg _))
    · have hz : F (X.symm y) = 0 := by
        by_contra hn
        exact hxy (hF hn)
      simp [localPiolaFlux, hy, hz]
  · simp [localPiolaFlux, hy, mul_nonneg (le_trans zero_le_one (le_max_right C 1))
      (norm_nonneg (F (X.symm y)))]

lemma localPiolaFlux_uniform_error
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {l : Filter I}
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {K : Set E} (hK : IsCompact K) (hKs : K ⊆ X.source)
    (F G : I → E → E) (hs : ∀ i, Function.support (fun x => F i x - G i x) ⊆ K)
    (he : TendstoUniformly (fun i x => F i x - G i x) (fun _ => 0) l) :
    TendstoUniformly (fun i x => localPiolaFlux X (F i) x - localPiolaFlux X (G i) x)
      (fun _ => 0) l := by
  obtain ⟨B, hB, hb⟩ := localPiolaFlux_linear_bound X hX hXi hK hKs
  rw [Metric.tendstoUniformly_iff] at he ⊢
  intro ε hε
  filter_upwards [he (ε / B) (div_pos hε hB)] with i hi x
  have hix : ‖F i (X.symm x) - G i (X.symm x)‖ < ε / B := by
    simpa only [dist_zero_left] using hi (X.symm x)
  have hii := hb (fun y => F i y - G i y) (hs i) x
  rw [localPiolaFlux_sub] at hii
  simpa only [dist_zero_left] using hii.trans_lt ((lt_div_iff₀' hB).mp hix)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology

lemma localPullback_support {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) :
    Function.support (localPullback X f) ⊆ X.symm '' (Function.support f ∩ X.target) := by
  intro x hx
  have hxs : x ∈ X.source := by
    by_contra hn
    exact hx (by simp [localPullback, hn])
  refine ⟨X x, ⟨?_, X.map_source hxs⟩, X.left_inv hxs⟩
  simpa only [Function.mem_support, localPullback, ite_eq_left hxs] using hx

lemma localPullback_tsupport {E V : Type*} [TopologicalSpace E] [T2Space E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ X.target) :
    HasCompactSupport (localPullback X f) ∧
      tsupport (localPullback X f) ⊆ X.symm '' tsupport f ∧
      tsupport (localPullback X f) ⊆ X.source := by
  have hK := hf.image_of_continuousOn (X.symm.continuousOn.mono hs)
  have hsub : Function.support (localPullback X f) ⊆ X.symm '' tsupport f :=
    (localPullback_support X f).trans (image_mono (fun _ hx => subset_closure hx.1))
  have ht : tsupport (localPullback X f) ⊆ X.symm '' tsupport f :=
    closure_minimal hsub hK.isClosed
  refine ⟨HasCompactSupport.of_support_subset_isCompact hK hsub, ht, ?_⟩
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := ht hx
  exact X.map_target (hs hy)

lemma localPullback_contDiff {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (f : E → V) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ X.target) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localPullback X f) := by
  apply contDiff_of_contDiffOn_tsupport X.open_source _
    (localPullback_tsupport X f hfc hfs).2.2
  intro x hx
  have hxs := hx
  have heq : localPullback X f =ᶠ[𝓝 x] f ∘ X := by
    filter_upwards [X.open_source.mem_nhds hxs] with y hy
    simp only [localPullback, ite_eq_left hy, Function.comp_apply]
  exact ((hf.contDiffAt.comp x ((hX x hxs).contDiffAt
    (X.open_source.mem_nhds hxs))).congr_of_eventuallyEq heq).contDiffWithinAt

lemma localPullback_comp {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) {z : E} (hz : z ∈ X.target) :
    localPullback X f (X.symm z) = f z := by
  simp only [localPullback, ite_eq_left (X.map_target hz), X.right_inv hz]

lemma localPullback_bounds {E : Type*} [TopologicalSpace E]
    (X : OpenPartialHomeomorph E E) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ localPullback X f x ∧ localPullback X f x ≤ 1 := by
  intro x
  by_cases hx : x ∈ X.source
  · simpa only [localPullback, ite_eq_left hx] using hf (X x)
  · simp only [localPullback, ite_eq_right hx, le_refl, zero_le_one, and_self]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_ChartTwoFluxLocalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

theorem exists_chart_two_flux_localized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    (χ : SmoothScalar E) (hχ : HasCompactSupport χ.val) (hχs : tsupport χ.val ⊆ X.target)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (h : SmoothScalar ℝ) (hp : Function.Periodic h.val 1)
    (hm : ∫ t in (0 : ℝ)..1, h.val t = 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0) :
    ∃ F : ℝ → Fin 2 → E → E,
      (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
      (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ X.source ∧
        tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
      (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
      (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
        (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
      ∀ j, TendstoUniformly
        (fun k y => F k j y - localPiolaFlux X.symm
          (fun x => (χ.val x * h.val (k * L x)) • R j) y) (fun _ => 0) atTop := by
  classical
  obtain ⟨G, hg, hs, hsym, hdiv, he⟩ := exists_physical_two_flux hdim μ D hD
    χ hχ L hL h hp hm R hRs hRn
  have hc (k : ℝ) (j : Fin 2) : HasCompactSupport (G k j) :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (hs k j)
  have hgs (k : ℝ) (j : Fin 2) : tsupport (G k j) ⊆ X.target := (hs k j).trans hχs
  refine ⟨fun k j => localPiolaFlux X.symm (G k j), ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    exact localPiolaFlux_smooth X.symm hXi hX (G k j) (hg k j) (hc k j) (hgs k j)
  · intro k j
    refine ⟨localPiolaFlux_hasCompactSupport X.symm _ (hc k j) (hgs k j),
      localPiolaFlux_tsupport X.symm _ (hc k j) (hgs k j), ?_⟩
    apply closure_minimal
      ((localPiolaFlux_support X.symm (G k j)).trans
        (image_mono (fun _ hx => hs k j (subset_closure hx.1))))
      ((hχ.image_of_continuousOn (X.symm.continuousOn.mono hχs)).isClosed)
  · intro k y
    by_cases hy : y ∈ X.source
    · rw [localPiolaFlux_potential_pairing X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) D u hu (G k 0) hy,
        localPiolaFlux_potential_pairing X (hX.differentiableOn (by simp))
        (hXi.differentiableOn (by simp)) D u hu (G k 1) hy]
      simp only [Pi.smul_apply, smul_eq_mul, hsym]
    · simp [localPiolaFlux, hy]
  · intro k j ψ hψ
    exact localPiolaFlux_zero_pairing μ X.symm hXi hX _ (hc k j) (hgs k j) (hdiv k j) ψ hψ
  · intro j
    apply localPiolaFlux_uniform_error X.symm hXi hX hχ hχs
      (fun k => G k j) (fun k x => (χ.val x * h.val (k * L x)) • R j) _ (he j)
    intro k x hx
    by_contra hn
    have hz : χ.val x = 0 := image_eq_zero_of_notMem_tsupport hn
    have hgz : G k j x = 0 := image_eq_zero_of_notMem_tsupport (fun hx => hn (hs k j hx))
    apply hx
    simp [hz, hgz]

theorem exists_frozen_chart_two_flux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ X.source ∧
      ∀ h : SmoothScalar ℝ, Function.Periodic h.val 1 →
        (∫ t in (0 : ℝ)..1, h.val t = 0) → (∀ t, |h.val t| ≤ 1) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → E → E,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
          (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∀ j y,
            ‖F k j y - (localPullback X χ.val y * h.val (k * L (X y))) • R j‖ < ε := by
  let B := ‖R 0‖ + ‖R 1‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : ∀ j, ‖R j‖ ≤ B := by
    intro j
    fin_cases j <;> dsimp [B] <;> linarith only [norm_nonneg (R 0), norm_nonneg (R 1)]
  obtain ⟨V, hV, haV, hVs, hfreeze⟩ := inverseChartPiola_freezing X hX hXi ha hDa
    (div_pos (half_pos hε) hB)
  refine ⟨V, hV, haV, hVs, ?_⟩
  intro h hp hm hb χ hχ hχV hχb
  have hχs : tsupport χ.val ⊆ X.target := by
    rintro z hz
    obtain ⟨y, hy, rfl⟩ := hχV hz
    exact X.map_source (hVs hy)
  obtain ⟨F, hF, hFs, hsym, hdiv, he⟩ := exists_chart_two_flux_localized hdim μ X hX hXi
    D hD u hu χ hχ hχs L hL h hp hm R hRs hRn
  have hFi : ∀ k j, tsupport (F k j) ⊆ V := by
    intro k j y hy
    obtain ⟨z, hz, rfl⟩ := (hFs k j).2.2 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hVs hw)] using hw
  have hχi : tsupport (localPullback X χ.val) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (localPullback_tsupport X χ.val hχ hχs).2.1 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hVs hw)] using hw
  refine ⟨F, hF, fun k j => ⟨(hFs k j).1, hFi k j, (hFs k j).2.2⟩, hsym, hdiv, ?_⟩
  have herr : ∀ᶠ k : ℝ in atTop, ∀ j y,
      ‖F k j y - localPiolaFlux X.symm
        (fun z => (χ.val z * h.val (k * L z)) • R j) y‖ < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro j
    simpa only [dist_zero_left] using (Metric.tendstoUniformly_iff.mp (he j)) _ (half_pos hε)
  filter_upwards [herr] with k hk j y
  by_cases hy : y ∈ V
  · have hfr := hfreeze (localPullback X χ.val) (fun z => h.val (k * L z)) (R j) y hy
    have hpre : localPiolaFlux X.symm
        (fun z => (localPullback X χ.val (X.symm z) * h.val (k * L z)) • R j) y =
        localPiolaFlux X.symm (fun z => (χ.val z * h.val (k * L z)) • R j) y := by
      rw [localPiolaFlux_inverse_eq X _ (hVs hy), localPiolaFlux_inverse_eq X _ (hVs hy),
        localPullback_comp X _ (X.map_source (hVs hy))]
    rw [hpre] at hfr
    have hcb := localPullback_bounds X χ.val hχb y
    have habs : |localPullback X χ.val y * h.val (k * L (X y))| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hcb.1]
      exact (mul_le_mul_of_nonneg_left (hb _) hcb.1).trans (by simpa using hcb.2)
    have hnorm : |localPullback X χ.val y * h.val (k * L (X y))| * ‖R j‖ ≤ B :=
      (mul_le_mul_of_nonneg_right habs (norm_nonneg _)).trans (by simpa using hR j)
    have hsmall : ‖localPiolaFlux X.symm
        (fun z => (χ.val z * h.val (k * L z)) • R j) y -
          (localPullback X χ.val y * h.val (k * L (X y))) • R j‖ ≤ ε / 2 :=
      hfr.trans ((mul_le_mul_of_nonneg_left hnorm (div_pos (half_pos hε) hB).le).trans
        (le_of_eq (div_mul_cancel₀ _ hB.ne')))
    exact (norm_sub_le_norm_sub_add_norm_sub (F k j y) _ _).trans_lt (by linarith only [hk j y, hsmall])
  · have hFz : F k j y = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hy (hFi k j hz))
    have hχz : localPullback X χ.val y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz => hy (hχi hz))
    simpa only [hFz, hχz, zero_mul, zero_smul, sub_zero, norm_zero] using hε

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_LinearPhaseDerivativeIntegralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem linear_phase_derivative_integral_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (v : E) (L : E →L[ℝ] ℝ) (hv : L v = 1)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (H : SmoothScalar ℝ) (C : ℝ) (hC : ∀ t, |H.val t| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    |∫ x, f.val x * (smoothDirection 1 H).val (k * L x) ∂μ| ≤
      k⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ := by
  let g : SmoothScalar E := k⁻¹ • smoothPhase (k • L) H
  have hg : smoothDirection v g = smoothPhase (k • L) (smoothDirection 1 H) := by
    dsimp [g]
    rw [map_smul, smoothDirection_phase, smul_smul]
    simp [hv, hk.ne']
  have hibp := smooth_integration_by_parts μ v f g hf
  rw [hg] at hibp
  change (∫ x, f.val x * (smoothDirection 1 H).val (k * L x) ∂μ) = _ at hibp
  rw [hibp, abs_neg]
  have hi : Integrable (fun x => |(smoothDirection v f).val x|) μ :=
    ((smoothScalar_contDiff (smoothDirection v f)).continuous.abs).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection v hf).abs
  calc
    |∫ x, (smoothDirection v f).val x * g.val x ∂μ| ≤
        ∫ x, |(smoothDirection v f).val x * g.val x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (k⁻¹ * C) * |(smoothDirection v f).val x| ∂μ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x
        positivity
      · exact hi.const_mul _
      · filter_upwards [] with x
        change |(smoothDirection v f).val x * (k⁻¹ * H.val (k * L x))| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hk.le)]
        nlinarith [mul_le_mul_of_nonneg_left (hC (k * L x))
          (mul_nonneg (abs_nonneg ((smoothDirection v f).val x)) (inv_nonneg.mpr hk.le))]
    _ = _ := by rw [integral_const_mul]

theorem periodic_oscillations_weak
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (h : SmoothScalar ℝ) (hper : Function.Periodic h.val 1)
    (hmean : ∫ t in (0 : ℝ)..1, h.val t = 0) :
    Filter.Tendsto (fun n : ℕ => ∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨v, hv⟩ : ∃ v, L v = 1 := by
    have hex : ∃ w, L w ≠ 0 := by
      by_contra hn
      apply hL
      ext w
      simpa using not_exists.mp hn w
    obtain ⟨w, hw⟩ := hex
    refine ⟨(L w)⁻¹ • w, ?_⟩
    simp [hw]
  obtain ⟨H₁, H₂, hd₁, hd₂, hp₁, hp₂, ⟨C, hb₁⟩, hb₂⟩ :=
    periodic_two_primitives h hper hmean
  have hb (n : ℕ) := linear_phase_derivative_integral_bound μ v L hv f hf H₁ C hb₁
    (by positivity : (0 : ℝ) < n + 1)
  simp only [hd₁] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => -((n + 1 : ℝ)⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ))
    (h := fun n : ℕ => (n + 1 : ℝ)⁻¹ * C * ∫ x, |(smoothDirection v f).val x| ∂μ)
  · simpa using ((tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const C
      |>.mul_const (∫ x, |(smoothDirection v f).val x| ∂μ)).neg
  · simpa using ((tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).mul_const C
      |>.mul_const (∫ x, |(smoothDirection v f).val x| ∂μ))
  · exact fun n => (abs_le.mp (hb n)).1
  · exact fun n => (abs_le.mp (hb n)).2

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_DerivativeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology

open Set MeasureTheory Filter Topology
open scoped BigOperators

lemma flatPulse_smooth (θ δ : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (flatPulse θ δ) := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ))

lemma flatPulse_zero_left {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (ht : t ≤ 0) :
    flatPulse θ δ t = 0 := by
  rw [flatPulse, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hδ.le),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), sub_self]

lemma flatPulse_zero_right {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) (ht : θ + δ ≤ t) :
    flatPulse θ δ t = 0 := by
  rw [flatPulse, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)), sub_self]

lemma flatPulse_one {θ δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (htθ : t ≤ θ) :
    flatPulse θ δ t = 1 := by
  rw [flatPulse, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htθ) hδ.le), sub_zero]

lemma flatPulse_bounds {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ) (t : ℝ) :
    0 ≤ flatPulse θ δ t ∧ flatPulse θ δ t ≤ 1 := by
  by_cases ht : t ≤ θ
  · rw [flatPulse, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le), sub_zero]
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [flatPulse, Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hδ).2 (by linarith))]
    exact ⟨sub_nonneg.2 (Real.smoothTransition.le_one _),
      sub_le_self _ (Real.smoothTransition.nonneg _)⟩

lemma flatPulse_support {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    Function.support (flatPulse θ δ) ⊆ Ioo 0 (θ + δ) := by
  intro t ht
  constructor
  · by_contra hn
    exact ht (flatPulse_zero_left hθ hδ (not_lt.mp hn))
  · by_contra hn
    exact ht (flatPulse_zero_right hθ hδ (not_lt.mp hn))

lemma pulse_translates_locallyFinite {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    LocallyFinite (fun n : ℤ => Function.support (fun t : ℝ => flatPulse θ δ (t - n))) := by
  have hl : Tendsto (fun n : ℤ => (n : ℝ)) atTop atTop := tendsto_intCast_atTop_atTop
  have hu : Tendsto (fun n : ℤ => (n : ℝ) + (θ + δ)) atBot atBot := by
    exact tendsto_atBot_add_const_right _ _ (tendsto_intCast_atBot_iff.2 tendsto_id)
  apply (locallyFinite_Icc_of_tendsto hl hu).subset
  intro n t ht
  have ht' := flatPulse_support hθ hδ ht
  exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩

lemma periodicPulse_smooth {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (periodicPulse θ δ) := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun n =>
    (contMDiff_iff_contDiff).2 ((flatPulse_smooth θ δ).comp (contDiff_id.sub contDiff_const)))
      (pulse_translates_locallyFinite hθ hδ)

lemma periodicPulse_periodic (θ δ : ℝ) : Function.Periodic (periodicPulse θ δ) 1 := by
  intro t
  unfold periodicPulse
  calc
    _ = ∑ᶠ n : ℤ, flatPulse θ δ (t + 1 - (n + 1 : ℤ)) :=
      (finsum_comp_equiv (Equiv.addRight (1 : ℤ))).symm
    _ = _ := by congr 1; funext n; congr 1; push_cast; ring

lemma periodicPulse_eq {θ δ t : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) (ht : t ∈ Icc 0 1) : periodicPulse θ δ t = flatPulse θ δ t := by
  unfold periodicPulse
  have hz : ∀ n : ℤ, n ≠ 0 → flatPulse θ δ (t - n) = 0 := by
    intro n hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · apply flatPulse_zero_right hθ hδ
      have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      linarith [ht.1]
    · apply flatPulse_zero_left hθ hδ
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [ht.2]
  simpa using finsum_eq_single _ 0 hz

lemma periodicPulse_bounds {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hwidth : θ + δ ≤ 1) (t : ℝ) :
    0 ≤ periodicPulse θ δ t ∧ periodicPulse θ δ t ≤ 1 := by
  have ht : t - (⌊t⌋ : ℤ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (Int.floor_le t)
    · linarith [Int.lt_floor_add_one t]
  have he : periodicPulse θ δ (t - (⌊t⌋ : ℤ)) = periodicPulse θ δ t := by
    simpa using (periodicPulse_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  rw [← he, periodicPulse_eq (hδ.le.trans hδθ) hδ hwidth ht]
  exact flatPulse_bounds hδ hδθ _

lemma smoothStep_integral {δ a b : ℝ} (hδ : 0 < δ) (ha : a ≤ 0) (hb : δ ≤ b) :
    (∫ t in a..b, Real.smoothTransition (t / δ)) =
      (∫ t in (0 : ℝ)..δ, Real.smoothTransition (t / δ)) + (b - δ) := by
  have hs : Continuous (fun t : ℝ => Real.smoothTransition (t / δ)) := by fun_prop
  have hl : (∫ t in a..0, Real.smoothTransition (t / δ)) = 0 := by
    calc
      _ = ∫ _t in a..0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le ha] at ht
        exact Real.smoothTransition.zero_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg ht.2 hδ.le)
      _ = 0 := by simp
  have hr : (∫ t in δ..b, Real.smoothTransition (t / δ)) = b - δ := by
    calc
      _ = ∫ _t in δ..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply Real.smoothTransition.one_of_one_le
        apply (le_div_iff₀ hδ).2
        rw [uIcc_of_le hb] at ht
        simpa only [one_mul] using ht.1
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable a 0)
    (hs.intervalIntegrable 0 b),
    ← intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable 0 δ)
    (hs.intervalIntegrable δ b), hl, hr, zero_add]

lemma flatPulse_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) : (∫ t in (0 : ℝ)..1, flatPulse θ δ t) = θ := by
  have hs : Continuous (fun t : ℝ => Real.smoothTransition (t / δ)) := by fun_prop
  have hs' : Continuous (fun t : ℝ => Real.smoothTransition ((t - θ) / δ)) := by fun_prop
  simp only [flatPulse]
  rw [intervalIntegral.integral_sub (hs.intervalIntegrable _ _)
    (hs'.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.smoothTransition (t / δ)) θ]
  rw [smoothStep_integral (δ := δ) (a := 0) (b := 1) hδ le_rfl (by linarith),
    smoothStep_integral (δ := δ) (a := 0 - θ) (b := 1 - θ) hδ (by linarith) (by linarith)]
  ring

lemma periodicPulse_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwidth : θ + δ ≤ 1) : (∫ t in (0 : ℝ)..1, periodicPulse θ δ t) = θ := by
  convert flatPulse_integral hθ hδ hwidth using 1
  all_goals try with_reducible_and_instances rfl
  apply intervalIntegral.integral_congr
  intro t ht
  exact periodicPulse_eq hθ hδ hwidth (by simpa using ht)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_TransitionMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
namespace ScalarConductivity

lemma transitionMajorant_smooth {θ δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (transitionMajorant θ δ) := by
  have hp := periodicPulse_smooth (by positivity : 0 ≤ 2 * δ) hδ
  exact (hp.comp (contDiff_id.add contDiff_const)).add
    (hp.comp ((contDiff_id.sub contDiff_const).add contDiff_const))

lemma transitionMajorant_periodic (θ δ : ℝ) :
    Function.Periodic (transitionMajorant θ δ) 1 := by
  intro t
  simp only [transitionMajorant]
  rw [show t + 1 + δ = (t + δ) + 1 by ring,
    show t + 1 - θ + δ = (t - θ + δ) + 1 by ring,
    periodicPulse_periodic, periodicPulse_periodic]

lemma transitionMajorant_bounds {θ δ : ℝ} (hδ : 0 < δ) (hw : 3 * δ ≤ 1) (t : ℝ) :
    0 ≤ transitionMajorant θ δ t ∧ transitionMajorant θ δ t ≤ 2 := by
  have h₁ := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1) (t + δ)
  have h₂ := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1) (t - θ + δ)
  unfold transitionMajorant
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma periodicPulse_shift_integral {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hw : θ + δ ≤ 1) (r : ℝ) :
    (∫ t in (0 : ℝ)..1, periodicPulse θ δ (t + r)) = θ := by
  rw [intervalIntegral.integral_comp_add_right]
  have he := (periodicPulse_periodic θ δ).intervalIntegral_add_eq r 0
  simp only [zero_add] at he
  rw [zero_add, add_comm 1 r, he, periodicPulse_integral hθ hδ hw]

lemma transitionMajorant_integral {θ δ : ℝ} (hδ : 0 < δ) (hw : 3 * δ ≤ 1) :
    (∫ t in (0 : ℝ)..1, transitionMajorant θ δ t) = 4 * δ := by
  have hp := periodicPulse_smooth (by positivity : 0 ≤ 2 * δ) hδ
  have hi₁ : IntervalIntegrable (fun t : ℝ => periodicPulse (2 * δ) δ (t + δ)) volume 0 1 :=
    (hp.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun t : ℝ => periodicPulse (2 * δ) δ (t - θ + δ)) volume 0 1 :=
    (hp.continuous.comp ((continuous_id.sub continuous_const).add continuous_const)).intervalIntegrable _ _
  dsimp [transitionMajorant]
  rw [intervalIntegral.integral_add hi₁ hi₂]
  simp_rw [show ∀ t : ℝ, t - θ + δ = t + (δ - θ) by intro t; ring]
  rw [periodicPulse_shift_integral (by positivity) hδ (by linarith),
    periodicPulse_shift_integral (by positivity) hδ (by linarith)]
  ring

lemma periodicPulse_impure_subset {θ δ t : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) (ht : t ∈ Icc 0 1)
    (hl : periodicPulse θ δ t ≠ 0) (hu : periodicPulse θ δ t ≠ 1) :
    t ∈ Ioo 0 δ ∪ Ioo θ (θ + δ) := by
  have hθ : 0 ≤ θ := hδ.le.trans hδθ
  rw [periodicPulse_eq hθ hδ hw ht] at hl hu
  by_cases htd : t < δ
  · left
    refine ⟨?_, htd⟩
    by_contra hn
    exact hl (flatPulse_zero_left hθ hδ (not_lt.mp hn))
  · right
    constructor
    · by_contra hn
      exact hu (flatPulse_one hδ (not_lt.mp htd) (not_lt.mp hn))
    · by_contra hn
      exact hl (flatPulse_zero_right hθ hδ (not_lt.mp hn))

lemma transitionMajorant_dominates {θ δ t : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) (hδw : 3 * δ ≤ 1)
    (hl : periodicPulse θ δ t ≠ 0) (hu : periodicPulse θ δ t ≠ 1) :
    1 ≤ transitionMajorant θ δ t := by
  let r := t - (⌊t⌋ : ℤ)
  have hr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hp : periodicPulse θ δ r = periodicPulse θ δ t := by
    simpa [r] using (periodicPulse_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  have hm : transitionMajorant θ δ r = transitionMajorant θ δ t := by
    simpa [r] using (transitionMajorant_periodic θ δ).sub_zsmul_eq (x := t) ⌊t⌋
  rw [← hm]
  have hbase := periodicPulse_bounds hδ (by linarith : δ ≤ 2 * δ)
    (by linarith : 2 * δ + δ ≤ 1)
  have heq (v : ℝ) (hv : v ∈ Icc δ (2 * δ)) : periodicPulse (2 * δ) δ v = 1 := by
    rw [periodicPulse_eq (by positivity) hδ (by linarith)
      (show v ∈ Icc 0 1 from ⟨by linarith [hv.1], by linarith [hv.2]⟩)]
    exact flatPulse_one hδ hv.1 hv.2
  rcases periodicPulse_impure_subset hδ hδθ hw hr (by rwa [hp]) (by rwa [hp]) with hr' | hr'
  · unfold transitionMajorant
    rw [heq (r + δ) ⟨by linarith [hr'.1], by linarith [hr'.2]⟩]
    linarith [(hbase (r - θ + δ)).1]
  · unfold transitionMajorant
    rw [heq (r - θ + δ) ⟨by linarith [hr'.1], by linarith [hr'.2]⟩]
    linarith [(hbase (r + δ)).1]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_PeriodicAveragingSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
namespace ScalarConductivity

theorem periodic_averaging_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val)
    (h : SmoothScalar ℝ) (hper : Function.Periodic h.val 1) :
    Tendsto (fun n : ℕ => ∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ)
      atTop (𝓝 ((∫ t in (0 : ℝ)..1, h.val t) * ∫ x, f.val x ∂μ)) := by
  let m : ℝ := ∫ t in (0 : ℝ)..1, h.val t
  let g : SmoothScalar ℝ := h - algebraMap ℝ (SmoothScalar ℝ) m
  have hg : Function.Periodic g.val 1 := by
    intro t
    change h.val (t + 1) - m = h.val t - m
    rw [hper t]
  have hm : (∫ t in (0 : ℝ)..1, g.val t) = 0 := by
    change (∫ t in (0 : ℝ)..1, h.val t - m) = 0
    rw [intervalIntegral.integral_sub ((smoothScalar_contDiff h).continuous.intervalIntegrable _ _)
      intervalIntegrable_const]
    simp [m]
  have hi : Integrable f.val μ := (smoothScalar_contDiff f).continuous.integrable_of_hasCompactSupport hf
  have he (n : ℕ) : (∫ x, f.val x * h.val ((n + 1 : ℝ) * L x) ∂μ) =
      (∫ x, f.val x * g.val ((n + 1 : ℝ) * L x) ∂μ) + m * ∫ x, f.val x ∂μ := by
    have hi' : Integrable (fun x => f.val x * h.val ((n + 1 : ℝ) * L x)) μ :=
      ((smoothScalar_contDiff f).continuous.mul
        ((smoothScalar_contDiff h).continuous.comp (continuous_const.mul L.continuous))).integrable_of_hasCompactSupport (hf.mul_right)
    change _ = (∫ x, f.val x * (h.val ((n + 1 : ℝ) * L x) - m) ∂μ) + _
    simp_rw [mul_sub]
    rw [integral_sub hi' (hi.mul_const m), integral_mul_const]
    ring
  simp_rw [he]
  simpa only [zero_add] using (periodic_oscillations_weak μ L hL f hf g hg hm).add_const
    (m * ∫ x, f.val x ∂μ)

theorem eventually_impure_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (f : SmoothScalar E) (hf : HasCompactSupport f.val) (hfn : ∀ x, 0 ≤ f.val x)
    (S : Set E) (hS : ∀ x ∈ S, 1 ≤ f.val x)
    {θ δ ε : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ) (hw : θ + δ ≤ 1)
    (hδw : 3 * δ ≤ 1) (hε : 4 * δ * (∫ x, f.val x ∂μ) < ε) :
    ∀ᶠ n : ℕ in atTop,
      μ {x | x ∈ S ∧ periodicPulse θ δ ((n + 1 : ℝ) * L x) ≠ 0 ∧
        periodicPulse θ δ ((n + 1 : ℝ) * L x) ≠ 1} ≤ ENNReal.ofReal ε := by
  let H : SmoothScalar ℝ := ⟨transitionMajorant θ δ, transitionMajorant_smooth hδ⟩
  have ht := periodic_averaging_smooth μ L hL f hf H (transitionMajorant_periodic θ δ)
  change Tendsto _ _ (𝓝 ((∫ t in (0 : ℝ)..1, transitionMajorant θ δ t) * ∫ x, f.val x ∂μ)) at ht
  rw [transitionMajorant_integral hδ hδw] at ht
  filter_upwards [ht.eventually_lt_const hε] with n hn
  have hi : Integrable (fun x => f.val x * transitionMajorant θ δ ((n + 1 : ℝ) * L x)) μ :=
    ((smoothScalar_contDiff f).continuous.mul
      ((transitionMajorant_smooth hδ).continuous.comp (continuous_const.mul L.continuous))).integrable_of_hasCompactSupport (hf.mul_right)
  apply (hi.measure_le_integral (ae_of_all μ (fun x => mul_nonneg (hfn x)
    (transitionMajorant_bounds hδ hδw _).1)) ?_).trans (ENNReal.ofReal_le_ofReal hn.le)
  intro x hx
  calc
    1 = 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul (hS x hx.1) (transitionMajorant_dominates hδ hδθ hw hδw hx.2.1 hx.2.2) (by norm_num) (by linarith [hS x hx.1])

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SymmetricCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

section
open Matrix

theorem symmetricCorrection_isSymm {m n : Type*} [Fintype m] [Fintype n]
    (E R : Matrix m n ℝ) (L : Matrix n m ℝ)
    (hER : (Eᵀ * R).IsSymm) : (symmetricCorrection E R L).IsSymm := by
  unfold Matrix.IsSymm symmetricCorrection
  simp only [transpose_sub, transpose_add, transpose_mul, transpose_transpose]
  have hsym : Rᵀ * E = Eᵀ * R := by simpa only [Matrix.IsSymm, transpose_mul, transpose_transpose] using hER
  rw [hsym]
  simp only [Matrix.mul_assoc, add_comm]

theorem symmetricCorrection_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (E R : Matrix m n ℝ) (L : Matrix n m ℝ)
    (hL : L * E = 1) (hER : (Eᵀ * R).IsSymm) :
    symmetricCorrection E R L * E = R := by
  have hsym : Rᵀ * E = Eᵀ * R := by
    simpa only [Matrix.IsSymm, transpose_mul, transpose_transpose] using hER
  simp only [symmetricCorrection, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, hL,
    Matrix.mul_one, hsym]
  exact add_sub_cancel_right _ _

end

open Filter Topology Set TopologicalSpace

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_Symmetrize
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma symmetrize_eq {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.IsSymm) :
    symmetrize M = M := by
  unfold symmetrize
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
  ring

lemma repairError_zero {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E : Matrix (Fin 3) m ℝ) : repairError A E 0 = A := by
  apply Subtype.ext
  simp [repairError, symmetricCorrection, symmetrize]

lemma repairError_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (E R : Matrix (Fin 3) m ℝ)
    (hE : LinearIndependent ℝ E.col) (hER : (Eᵀ * R).IsSymm) :
    (repairError A E R).val * E = A.val * E + R := by
  change (A.val + symmetrize _) * E = _
  rw [symmetrize_eq (symmetricCorrection_isSymm E R _ hER), Matrix.add_mul,
    symmetricCorrection_mul E R _ (gram_leftInverse E hE) hER]

lemma gram_det_ne_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) : (Eᵀ * E).det ≠ 0 := by
  have hinj : Function.Injective E.mulVec := Matrix.mulVec_injective_iff.mpr hE
  have hker : LinearMap.ker (Eᵀ * E).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hker)))

lemma matrix_mul_contAt {X m n p : Type*} [TopologicalSpace X]
    [Fintype n] {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (hA : ContinuousAt A x) (hB : ContinuousAt B x) :
    ContinuousAt (fun y => A y * B y) x :=
  (continuous_fst.matrix_mul continuous_snd).continuousAt.comp (hA.prodMk hB)

lemma matrix_transpose_contAt {X m n : Type*} [TopologicalSpace X]
    {A : X → Matrix m n ℝ} {x : X} (hA : ContinuousAt A x) :
    ContinuousAt (fun y => (A y)ᵀ) x :=
  continuous_id.matrix_transpose.continuousAt.comp hA

lemma continuousAt_gramInverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (hE : LinearIndependent ℝ E.col) :
    ContinuousAt (fun F : Matrix m n ℝ => (Fᵀ * F)⁻¹ * Fᵀ) E := by
  have hi : ContinuousAt (fun M : Matrix n n ℝ => M⁻¹) (Eᵀ * E) :=
    continuousAt_matrix_inv _ (by
      convert continuousAt_inv₀ (gram_det_ne_zero E hE) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      exact Ring.inverse_eq_inv x)
  have hG : Continuous (fun F : Matrix m n ℝ => Fᵀ * F) :=
    (continuous_id : Continuous (id : Matrix m n ℝ → Matrix m n ℝ)).matrix_transpose.matrix_mul
      continuous_id
  have hT : Continuous (fun F : Matrix m n ℝ => Fᵀ) :=
    (continuous_id : Continuous (id : Matrix m n ℝ → Matrix m n ℝ)).matrix_transpose
  have hGi : ContinuousAt (fun F : Matrix m n ℝ => (Fᵀ * F)⁻¹) E := by
    exact ContinuousAt.comp (f := fun F : Matrix m n ℝ => Fᵀ * F)
      (g := fun M : Matrix n n ℝ => M⁻¹) hi hG.continuousAt
  exact matrix_mul_contAt hGi hT.continuousAt

lemma continuousAt_repairError {m X : Type*} [Fintype m] [DecidableEq m]
    [TopologicalSpace X] (A : X → Symmetric3) (E R : X → Matrix (Fin 3) m ℝ)
    {x : X} (hA : ContinuousAt A x) (hE : ContinuousAt E x) (hR : ContinuousAt R x)
    (hi : LinearIndependent ℝ (E x).col) :
    ContinuousAt (fun y => repairError (A y) (E y) (R y)) x := by
  apply IsInducing.subtypeVal.continuousAt_iff.mpr
  have hL := (continuousAt_gramInverse (E x) hi).comp hE
  have hC : ContinuousAt (fun y =>
      symmetricCorrection (E y) (R y) (((E y)ᵀ * E y)⁻¹ * (E y)ᵀ)) x := by
    unfold symmetricCorrection
    exact ((matrix_mul_contAt hR hL).add
      (matrix_mul_contAt (matrix_transpose_contAt hL) (matrix_transpose_contAt hR))).sub
      (matrix_mul_contAt (matrix_mul_contAt (matrix_transpose_contAt hL)
        (matrix_mul_contAt (matrix_transpose_contAt hE) hR)) hL)
  exact (continuousAt_subtype_val.comp hA).add
    ((hC.add (matrix_transpose_contAt hC)).const_smul (1 / 2 : ℝ))

lemma compact_zero_stability {P V W : Type*} [TopologicalSpace P]
    [SeminormedAddCommGroup V] [TopologicalSpace W]
    {K : Set P} (hK : IsCompact K) (f : P × V → W)
    (hf : ∀ p ∈ K, ContinuousAt f (p, 0))
    {U : Set W} (hU : IsOpen U) (hmem : ∀ p ∈ K, f (p, 0) ∈ U) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ O, ∀ v : V, ‖v‖ < ε → f (p, v) ∈ U := by
  let N := interior (f ⁻¹' U)
  have hKN : K ×ˢ ({0} : Set V) ⊆ N := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact mem_interior_iff_mem_nhds.mpr ((hf p hp).preimage_mem_nhds (hU.mem_nhds (hmem p hp)))
  obtain ⟨O, Z, hO, hZ, hKO, h0Z, hOZ⟩ :=
    generalized_tube_lemma hK isCompact_singleton isOpen_interior hKN
  obtain ⟨ε, hε, he⟩ := Metric.isOpen_iff.mp hZ 0 (h0Z (mem_singleton 0))
  refine ⟨O, hO, hKO, ε, hε, ?_⟩
  intro p hp v hv
  have hvZ : v ∈ Z := he (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hm : (p, v) ∈ interior (f ⁻¹' U) := hOZ ⟨hp, hvZ⟩
  exact (interior_subset : interior (f ⁻¹' U) ⊆ f ⁻¹' U) hm

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CrossingHxx
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma pushGradient_rank {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) (hE : LinearIndependent ℝ E.col) :
    LinearIndependent ℝ (pushGradient J E).col := by
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  apply Matrix.mulVec_injective_iff.mpr hE
  have h := congrArg Jᵀ.mulVec hvw
  simpa only [Matrix.mulVec_mulVec, pushGradient_leftInverse J hJ E] using h

lemma push_pairing {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E F : Matrix (Fin 3) m ℝ) :
    (pushGradient J E)ᵀ * pushFlux J F = J.det⁻¹ • (Eᵀ * F) := by
  have hj := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hJ)
  unfold pushGradient pushFlux
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul]
  congr 1
  calc
    Eᵀ * J⁻¹ * (J * F) = Eᵀ * (J⁻¹ * J) * F := by simp only [Matrix.mul_assoc]
    _ = Eᵀ * F := by rw [hj, Matrix.mul_one]

lemma pushFlux_constitutive {m : Type*} [Fintype m] (J B : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) :
    pushFlux J (B * E) = (J.det⁻¹ • (J * B * Jᵀ)) * pushGradient J E := by
  rw [Matrix.smul_mul, Matrix.mul_assoc, pushGradient_leftInverse J hJ E]
  simp only [pushFlux, Matrix.mul_assoc]

lemma symmetric_gram_pairing {m : Type*} [Fintype m]
    (A : Symmetric3) (E : Matrix (Fin 3) m ℝ) : (Eᵀ * (A.val * E)).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (Matrix.isHermitian_iff_isSymm.mp A.property).eq]
  exact Matrix.mul_assoc _ _ _

lemma repairPushed_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J : Mat3) (E F : Matrix (Fin 3) m ℝ)
    (hJ : J.det ≠ 0) (hE : LinearIndependent ℝ E.col) (hEF : (Eᵀ * F).IsSymm) :
    (repairPushed A J E F).val * pushGradient J E = pushFlux J F := by
  unfold repairPushed
  rw [repairError_mul A _ _ (pushGradient_rank J hJ E hE)]
  · exact add_sub_cancel _ _
  · rw [Matrix.mul_sub, push_pairing J hJ E F]
    exact (hEF.smul _).sub (symmetric_gram_pairing A _)

lemma repairPushed_exact {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J B : Mat3) (E : Matrix (Fin 3) m ℝ)
    (hJ : J.det ≠ 0) (hA : A.val = J.det⁻¹ • (J * B * Jᵀ)) :
    repairPushed A J E (B * E) = A := by
  unfold repairPushed
  rw [hA, ← pushFlux_constitutive J B hJ E, sub_self, repairError_zero]

lemma continuousAt_matrixInverse (J : Mat3) (hJ : J.det ≠ 0) :
    ContinuousAt (fun M : Mat3 => M⁻¹) J := by
  apply continuousAt_matrix_inv
  convert continuousAt_inv₀ hJ using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact Ring.inverse_eq_inv x

lemma continuousAt_pushGradient {m X : Type*} [Fintype m] [TopologicalSpace X]
    (J : X → Mat3) (E : X → Matrix (Fin 3) m ℝ) {x : X}
    (hJ : ContinuousAt J x) (hE : ContinuousAt E x) (hdet : (J x).det ≠ 0) :
    ContinuousAt (fun y => pushGradient (J y) (E y)) x := by
  have hi : ContinuousAt (fun y => (J y)⁻¹) x :=
    ContinuousAt.comp (f := J) (continuousAt_matrixInverse (J x) hdet) hJ
  exact matrix_mul_contAt (matrix_transpose_contAt hi) hE

lemma continuousAt_pushFlux {m X : Type*} [Fintype m] [TopologicalSpace X]
    (J : X → Mat3) (F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hJ : ContinuousAt J x) (hF : ContinuousAt F x) (hdet : (J x).det ≠ 0) :
    ContinuousAt (fun y => pushFlux (J y) (F y)) x := by
  have hc : Continuous (fun M : Mat3 => M.det) := continuous_id.matrix_det
  have hd : ContinuousAt (fun y => (J y).det) x := hc.continuousAt.comp hJ
  exact (hd.inv₀ hdet).smul (matrix_mul_contAt hJ hF)

lemma continuousAt_repairPushed {m X : Type*} [Fintype m] [DecidableEq m]
    [TopologicalSpace X] (A : X → Symmetric3) (J : X → Mat3)
    (E F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContinuousAt A x) (hJ : ContinuousAt J x)
    (hE : ContinuousAt E x) (hF : ContinuousAt F x)
    (hdet : (J x).det ≠ 0) (hi : LinearIndependent ℝ (E x).col) :
    ContinuousAt (fun y => repairPushed (A y) (J y) (E y) (F y)) x := by
  have hG := continuousAt_pushGradient J E hJ hE hdet
  have hP := continuousAt_pushFlux J F hJ hF hdet
  exact continuousAt_repairError _ _ _ hA hG
    (hP.sub (matrix_mul_contAt (continuousAt_subtype_val.comp hA) hG))
    (pushGradient_rank (J x) hdet (E x) hi)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_GramRankDetNe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma gram_rank_of_det_ne_zero {m : Type*} [Fintype m] [DecidableEq m]
    (E : Matrix (Fin 3) m ℝ) (h : (Eᵀ * E).det ≠ 0) : LinearIndependent ℝ E.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  apply Matrix.mulVec_injective_iff.mpr (Matrix.linearIndependent_cols_of_det_ne_zero h)
  simpa only [Matrix.mulVec_mulVec] using congrArg Eᵀ.mulVec hvw

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Filter Topology

lemma smoothDirection_compose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (φ : SmoothScalar E) (H : SmoothScalar ℝ) :
    smoothDirection v (smoothCompose φ H) =
      smoothDirection v φ * smoothCompose φ (smoothDirection 1 H) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (H.val ∘ φ.val) x v =
    fderiv ℝ φ.val x v * fderiv ℝ H.val (φ.val x) 1
  rw [fderiv_comp x ((smoothScalar_contDiff H).differentiable (by simp) _)
    ((smoothScalar_contDiff φ).differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  simpa only [smul_eq_mul, mul_one] using
    (fderiv ℝ H.val (φ.val x)).map_smul (fderiv ℝ φ.val x v) 1

lemma nonlinearFirstPotential_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    smoothDirection v (nonlinearFirstPotential χ φ H k) =
      smoothDirection v φ * χ * smoothCompose (k • φ) (smoothDirection 1 H) +
        k⁻¹ • (smoothCompose (k • φ) H * smoothDirection v χ) := by
  simp only [nonlinearFirstPotential, map_smul, smoothDirection_mul,
    smoothDirection_compose]
  apply Subtype.ext
  funext x
  change k⁻¹ * (χ.val x * ((k * (smoothDirection v φ).val x) *
    (smoothDirection 1 H).val (k * φ.val x)) +
    H.val (k * φ.val x) * (smoothDirection v χ).val x) =
    (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
      k⁻¹ * (H.val (k * φ.val x) * (smoothDirection v χ).val x)
  field_simp

lemma nonlinearFirstPotential_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    {k : ℝ} (hk : k ≠ 0) (x : E) :
    fderiv ℝ (nonlinearFirstPotential χ φ H k).val x =
      (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x +
        (k⁻¹ * H.val (k * φ.val x)) • fderiv ℝ χ.val x := by
  ext v
  have h := congrArg (fun f : SmoothScalar E => f.val x)
    (nonlinearFirstPotential_derivative v χ φ H hk)
  change fderiv ℝ (nonlinearFirstPotential χ φ H k).val x v =
    (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) * fderiv ℝ φ.val x v +
      (k⁻¹ * H.val (k * φ.val x)) * fderiv ℝ χ.val x v
  change fderiv ℝ (nonlinearFirstPotential χ φ H k).val x v =
    fderiv ℝ φ.val x v * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
      k⁻¹ * (H.val (k * φ.val x) * fderiv ℝ χ.val x v) at h
  rw [h]
  ring

lemma nonlinearFirstPotential_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ) (k : ℝ) :
    tsupport (nonlinearFirstPotential χ φ H k).val ⊆ tsupport χ.val := by
  apply closure_mono
  intro x hx hχx
  apply hx
  change k⁻¹ * (χ.val x * H.val (k * φ.val x)) = 0
  rw [hχx, zero_mul, mul_zero]

lemma nonlinearFirstPotential_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => (smoothDirection v (nonlinearFirstPotential χ φ H k)).val x -
        (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := (smoothScalar_contDiff (smoothDirection v χ)).continuous
    |>.bounded_above_of_compact_support (compactSupport_smoothDirection v hχ)
  obtain ⟨B, hB⟩ := hH
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    have he := congrArg (fun f : SmoothScalar E => f.val x)
      (nonlinearFirstPotential_derivative v χ φ H (ne_of_gt hk))
    change (smoothDirection v (nonlinearFirstPotential χ φ H k)).val x =
      (smoothDirection v φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x) +
        k⁻¹ * (H.val (k * φ.val x) * (smoothDirection v χ).val x) at he
    rw [he, add_sub_cancel_left, abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hA x)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB0)

lemma nonlinearFirstPotential_eventually_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (c m : ℝ) (hm : 0 < m)
    (hpos : ∀ k x, m ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))) :
    ∀ᶠ k : ℝ in atTop, ∀ x,
      0 < 1 + fderiv ℝ (c • nonlinearFirstPotential χ φ H k).val x d := by
  have ht := ((ContinuousLinearMap.id ℝ ℝ).smulRight c).uniformContinuous.comp_tendstoUniformly
    (nonlinearFirstPotential_error_tendsto d χ φ H hχ hH)
  have hs : ∀ᶠ k : ℝ in atTop, ∀ x,
      |c * ((smoothDirection d (nonlinearFirstPotential χ φ H k)).val x -
        (smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))| < m := by
    simpa [Function.comp_def, mul_comm, dist_zero_left, Real.norm_eq_abs] using
      (Metric.tendstoUniformly_iff.mp ht) m hm
  filter_upwards [hs] with k hk x
  change 0 < 1 + (smoothDirection d (c • nonlinearFirstPotential χ φ H k)).val x
  rw [map_smul]
  change 0 < 1 + c * (smoothDirection d (nonlinearFirstPotential χ φ H k)).val x
  have he := (abs_lt.mp (hk x)).1
  have hp := hpos k x
  nlinarith

theorem nonlinearFirstPotential_diffeomorphisms {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C)
    (c m : ℝ) (hm : 0 < m)
    (hpos : ∀ k x, m ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x))) :
    ∀ᶠ k : ℝ in atTop, ∃ X : E ≃ E,
      (∀ x, X x = x + (c * (nonlinearFirstPotential χ φ H k).val x) • d) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm := by
  filter_upwards [nonlinearFirstPotential_eventually_positive d χ φ H hχ hH c m hm hpos]
    with k hk
  apply exists_smooth_lineShift_inverse d (c • nonlinearFirstPotential χ φ H k) hk
  have hc : HasCompactSupport (nonlinearFirstPotential χ φ H k).val :=
    hχ.of_isClosed_subset (isClosed_tsupport _) (nonlinearFirstPotential_support χ φ H k)
  exact (smoothScalar_contDiff (c • nonlinearFirstPotential χ φ H k)).continuous
    |>.bounded_above_of_compact_support (hc.smul_left)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_UniformNormBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Filter Topology

lemma uniform_zero_norm_of_bound {X I V : Type*} [NormedAddCommGroup V]
    {l : Filter I} {f : I → X → V} {b : I → ℝ}
    (hb : Tendsto b l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ x, ‖f i x‖ ≤ b i) :
    TendstoUniformly f (fun _ => 0) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hf, hb.eventually_lt_const hε] with i hi hib x
  simpa only [dist_zero_left] using (hi x).trans_lt hib

lemma nonlinearFirstPotential_fderiv_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ C : ℝ, ∀ t, |H.val t| ≤ C) :
    TendstoUniformly
      (fun k x => fderiv ℝ (nonlinearFirstPotential χ φ H k).val x -
        (χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x)
      (fun _ => 0) atTop := by
  obtain ⟨A, hA⟩ := ((smoothScalar_contDiff χ).continuous_fderiv (by simp))
    |>.bounded_above_of_compact_support (hχ.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := hH
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  apply uniform_zero_norm_of_bound (b := fun k : ℝ => |k⁻¹| * B * A)
  · simpa using ((tendsto_inv_atTop_zero.abs.mul_const B).mul_const A)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk x
    rw [nonlinearFirstPotential_fderiv χ φ H hk.ne', add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)) (hA x)
      (norm_nonneg _) (mul_nonneg (abs_nonneg _) hB0)

lemma scalar_cutoff_segment {a b c z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c ∧ c ≤ 1) (hz : -a ≤ z ∧ z ≤ b) :
    -a ≤ c * z ∧ c * z ≤ b := by
  constructor
  · calc
      -a ≤ c * (-a) := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) ha]
      _ ≤ c * z := mul_le_mul_of_nonneg_left hz.1 hc.1
  · calc
      c * z ≤ c * b := mul_le_mul_of_nonneg_left hz.2 hc.1
      _ ≤ b := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) hb]

lemma nonlinear_phase_leading_positive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχb : ∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1)
    {a b c m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (_hm : 0 < m) (hpath : ∀ z ∈ Set.Icc (-a) b, m ≤ 1 + c * z)
    (hH : ∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b)
    (hphase : ∀ x ∈ tsupport χ.val,
      |(smoothDirection d φ).val x - 1| ≤ m / (2 * (|c| + 1))) :
    ∀ k x, m / 2 ≤ 1 + c *
      ((smoothDirection d φ).val x * χ.val x * (smoothDirection 1 H).val (k * φ.val x)) := by
  intro k x
  let z := χ.val x * (smoothDirection 1 H).val (k * φ.val x)
  have hz := scalar_cutoff_segment ha hb (hχb x) (hH (k * φ.val x))
  change -a ≤ z ∧ z ≤ b at hz
  have hzabs : |z| ≤ 1 := abs_le.mpr ⟨by linarith only [hz.1, ha1],
    by linarith only [hz.2, hb1]⟩
  have hp := hpath z hz
  by_cases hx : x ∈ tsupport χ.val
  · have hden : 0 < 2 * (|c| + 1) := by positivity
    have hd := (le_div_iff₀ hden).mp (hphase x hx)
    have he : |c * ((smoothDirection d φ).val x - 1) * z| ≤ m / 2 := by
      rw [abs_mul, abs_mul]
      have hmul : |c| * |(smoothDirection d φ).val x - 1| ≤ m / 2 := by
        nlinarith only [hd, abs_nonneg ((smoothDirection d φ).val x - 1)]
      exact (mul_le_mul_of_nonneg_left hzabs (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hmul)
    have hlow := (abs_le.mp he).1
    change m / 2 ≤ 1 + c * ((smoothDirection d φ).val x * χ.val x * _)
    have hzdef : (smoothDirection d φ).val x * χ.val x *
        (smoothDirection 1 H).val (k * φ.val x) = (smoothDirection d φ).val x * z := by
      dsimp [z]; ring
    rw [hzdef]
    nlinarith only [hp, hlow]
  · have hzero := image_eq_zero_of_notMem_tsupport hx
    have hm1 := hpath 0 ⟨by linarith, hb⟩
    simp only [hzero, mul_zero, zero_mul, add_zero]
    linarith only [hm1, _hm]

end

open Set Filter Topology

lemma lineShift_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : E) {f : E → ℝ} {x : E} {L : E →L[ℝ] ℝ} (hf : HasFDerivAt f L x) :
    HasFDerivAt (lineShift d f) (ContinuousLinearMap.id ℝ E + L.smulRight d) x := by
  exact (hasFDerivAt_id x).add (hf.smul_const d)

lemma nonlinearLineShift_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c k : ℝ) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (x : E) :
    fderiv ℝ (lineShift d (c • nonlinearFirstPotential χ φ H k).val) x =
      ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
        (fderiv ℝ (nonlinearFirstPotential χ φ H k).val x) := by
  rw [(lineShift_hasFDerivAt d
    ((smoothScalar_contDiff (c • nonlinearFirstPotential χ φ H k)).differentiable
      (by simp) x).hasFDerivAt).fderiv]
  congr 1
  ext v
  change fderiv ℝ (fun y => c • (nonlinearFirstPotential χ φ H k).val y) x v • d = _
  have hs := (((smoothScalar_contDiff (nonlinearFirstPotential χ φ H k)).differentiable
    (by simp) x).hasFDerivAt.const_smul c).fderiv
  change (fderiv ℝ (c • (nonlinearFirstPotential χ φ H k).val) x) v • d = _
  rw [hs]
  simp [lineShiftGradientOperator, smul_smul]

lemma nonlinearLineShift_fderiv_error_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (d : E) (c : ℝ) (χ φ : SmoothScalar E) (H : SmoothScalar ℝ)
    (hχ : HasCompactSupport χ.val) (hH : ∃ B : ℝ, ∀ t, |H.val t| ≤ B) :
    TendstoUniformly
      (fun k x => fderiv ℝ (lineShift d (c • nonlinearFirstPotential χ φ H k).val) x -
        (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
          ((χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • fderiv ℝ φ.val x)))
      (fun _ => 0) atTop := by
  have ht := (lineShiftGradientOperator d c).uniformContinuous.comp_tendstoUniformly
    (nonlinearFirstPotential_fderiv_error_tendsto χ φ H hχ hH)
  simpa only [Function.comp_def, map_sub, map_zero, nonlinearLineShift_fderiv,
    add_sub_add_left_eq_sub] using ht

lemma equiv_image_set_of_eq_off {E : Type*} (X : E ≃ E) (V : Set E)
    (h : ∀ x ∉ V, X x = x) : X '' V = V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_contra hy
    have he := X.injective (h (X x) hy)
    exact hy (by simpa only [he] using hx)
  · intro hy
    refine ⟨X.symm y, ?_, X.apply_symm_apply y⟩
    by_contra hx
    have he : y = X.symm y := (X.apply_symm_apply y).symm.trans (h _ hx)
    exact hx (he ▸ hy)

theorem exists_local_phase_diffeomorphisms
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : E) (φ : SmoothScalar E)
    {p : E} {L : E →L[ℝ] ℝ} (hLp : fderiv ℝ φ.val p = L) (hLd : L d = 1)
    {a b c m ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hε : 0 < ε)
    (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    {U : Set E} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∀ H : SmoothScalar ℝ, (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∀ᶠ k : ℝ in atTop, ∃ X : E ≃ E,
          (∀ x, X x = lineShift d (c • nonlinearFirstPotential χ φ H k).val x) ∧
          ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) X.symm ∧
          (∀ x ∉ V, X x = x) ∧ X '' V = V ∧
          ∀ x, ‖fderiv ℝ X x -
            (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
              ((χ.val x * (smoothDirection 1 H).val (k * φ.val x)) • L))‖ < ε := by
  let T := lineShiftGradientOperator d c
  let δ := min (ε / (2 * (‖T‖ + 1))) (m / (2 * (|c| + 1) * (‖d‖ + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hevent : ∀ᶠ x in 𝓝 p, ‖fderiv ℝ φ.val x - L‖ < δ := by
    simpa only [dist_eq_norm, hLp] using
      ((smoothScalar_contDiff φ).continuous_fderiv (by simp)).continuousAt.eventually
        (Metric.ball_mem_nhds (fderiv ℝ φ.val p) hδ)
  obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp hevent
  let V := U ∩ W
  refine ⟨V, hU.inter hWo, ⟨hp, hpW⟩, inter_subset_left, ?_⟩
  intro H hH hHr χ hχ hχV hχb
  have hphase : ∀ x ∈ tsupport χ.val,
      |(smoothDirection d φ).val x - 1| ≤ m / (2 * (|c| + 1)) := by
    intro x hx
    have hd := (fderiv ℝ φ.val x - L).le_opNorm d
    change ‖(fderiv ℝ φ.val x) d - L d‖ ≤ ‖fderiv ℝ φ.val x - L‖ * ‖d‖ at hd
    rw [hLd, Real.norm_eq_abs] at hd
    change |(fderiv ℝ φ.val x) d - 1| ≤ _
    have hsmall := (show ‖fderiv ℝ φ.val x - L‖ < δ from hW (hχV hx).2).le.trans (min_le_right _ _)
    have hden : 0 < 2 * (|c| + 1) * (‖d‖ + 1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hsmall
    apply (le_div_iff₀ (by positivity : 0 < 2 * (|c| + 1))).mpr
    nlinarith only [hd, hmul, norm_nonneg (fderiv ℝ φ.val x - L), abs_nonneg c]
  have hpos := nonlinear_phase_leading_positive d χ φ H hχb ha hb ha1 hb1 hm hpath hHr hphase
  have hmaps := nonlinearFirstPotential_diffeomorphisms d χ φ H hχ hH c (m/2)
    (half_pos hm) hpos
  have he := (Metric.tendstoUniformly_iff.mp
    (nonlinearLineShift_fderiv_error_tendsto d c χ φ H hχ hH)) (ε/2) (half_pos hε)
  filter_upwards [hmaps, he] with k hk hke
  obtain ⟨X, hX, hXs, hXi⟩ := hk
  have hXeq : (X : E → E) = lineShift d (c • nonlinearFirstPotential χ φ H k).val :=
    funext hX
  have hoff : ∀ x ∉ V, X x = x := by
    intro x hx
    have hz : (nonlinearFirstPotential χ φ H k).val x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hx (hχV (nonlinearFirstPotential_support χ φ H k ht)))
    rw [hX]
    simp only [hz, mul_zero, zero_smul, add_zero]
  refine ⟨X, hX, hXs, hXi, hoff, equiv_image_set_of_eq_off X V hoff, ?_⟩
  intro x
  let z := χ.val x * (smoothDirection 1 H).val (k * φ.val x)
  have he1 : ‖fderiv ℝ X x - (ContinuousLinearMap.id ℝ E + T (z • fderiv ℝ φ.val x))‖ < ε/2 := by
    simpa only [hXeq, dist_zero_left] using hke x
  have he2 : ‖(ContinuousLinearMap.id ℝ E + T (z • fderiv ℝ φ.val x)) -
      (ContinuousLinearMap.id ℝ E + T (z • L))‖ ≤ ε/2 := by
    rw [add_sub_add_left_eq_sub, ← map_sub, ← smul_sub z (fderiv ℝ φ.val x) L, map_smul, norm_smul, Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport χ.val
    · have hz := scalar_cutoff_segment ha hb (hχb x) (hHr (k * φ.val x))
      change -a ≤ z ∧ z ≤ b at hz
      have hza : |z| ≤ 1 := abs_le.mpr ⟨by linarith only [hz.1, ha1], by linarith only [hz.2, hb1]⟩
      have hsmall := (show ‖fderiv ℝ φ.val x - L‖ < δ from hW (hχV hx).2).le.trans (min_le_left _ _)
      have hbound := T.le_opNorm (fderiv ℝ φ.val x - L)
      have hden : 0 < 2 * (‖T‖ + 1) := by positivity
      have hmul := (le_div_iff₀ hden).mp hsmall
      have hbnd : ‖T (fderiv ℝ φ.val x - L)‖ ≤ ε/2 := by
        nlinarith only [hbound, hmul, norm_nonneg (fderiv ℝ φ.val x - L)]
      exact (mul_le_mul_of_nonneg_right hza (norm_nonneg _)).trans (by simpa using hbnd)
    · have hz : z = 0 := by dsimp [z]; rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hz, abs_zero, zero_mul]
      exact (half_pos hε).le
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (by linarith only [he1, he2])

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_RepairPushedGraphStability
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma repairPushed_graph_stability
    {P m : Type*} [TopologicalSpace P] [Fintype m] [DecidableEq m]
    {K : Set P} (hK : IsCompact K)
    (A : P → Symmetric3) (J : P → Mat3) (E F : P → Matrix (Fin 3) m ℝ)
    (hA : ∀ p ∈ K, ContinuousAt A p) (hJ : ∀ p ∈ K, ContinuousAt J p)
    (hE : ∀ p ∈ K, ContinuousAt E p) (hF : ∀ p ∈ K, ContinuousAt F p)
    (hdet : ∀ p ∈ K, 0 < (J p).det) (hrank : ∀ p ∈ K, LinearIndependent ℝ (E p).col)
    {U : Set (P × Symmetric3)} (hU : IsOpen U)
    (hmem : ∀ p ∈ K, (p, repairPushed (A p) (J p) (E p) (F p)) ∈ U) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ O, ∀ (dJ : Mat3) (dE dF : Matrix (Fin 3) m ℝ),
        ‖(dJ, dE, dF)‖ < ε →
          0 < (J p + dJ).det ∧ LinearIndependent ℝ (E p + dE).col ∧
          (p, repairPushed (A p) (J p + dJ) (E p + dE) (F p + dF)) ∈ U := by
  let V := Mat3 × Matrix (Fin 3) m ℝ × Matrix (Fin 3) m ℝ
  let a : P × V → Symmetric3 := fun q => A q.1
  let j : P × V → Mat3 := fun q => J q.1 + q.2.1
  let e : P × V → Matrix (Fin 3) m ℝ := fun q => E q.1 + q.2.2.1
  let f : P × V → Matrix (Fin 3) m ℝ := fun q => F q.1 + q.2.2.2
  let T : P × V → (P × Symmetric3) × ℝ × ℝ := fun q =>
    ((q.1, repairPushed (a q) (j q) (e q) (f q)), (j q).det, ((e q)ᵀ * e q).det)
  have hT : ∀ p ∈ K, ContinuousAt T (p, 0) := by
    intro p hp
    have ha : ContinuousAt a (p, 0) := (hA p hp).comp continuousAt_fst
    have hj : ContinuousAt j (p, 0) := ((hJ p hp).comp continuousAt_fst).add
      (continuousAt_fst.comp continuousAt_snd)
    have he : ContinuousAt e (p, 0) := ((hE p hp).comp continuousAt_fst).add
      (continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd))
    have hf : ContinuousAt f (p, 0) := ((hF p hp).comp continuousAt_fst).add
      (continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd))
    have hj0 : j (p, 0) = J p := by simp [j]
    have he0 : e (p, 0) = E p := by simp [e]
    have hc : Continuous (fun M : Mat3 => M.det) := continuous_id.matrix_det
    have hg : Continuous (fun M : Matrix m m ℝ => M.det) := continuous_id.matrix_det
    exact (continuousAt_fst.prodMk (continuousAt_repairPushed a j e f ha hj he hf
      (hj0 ▸ (hdet p hp).ne') (he0 ▸ hrank p hp))).prodMk
        ((hc.continuousAt.comp hj).prodMk
          (hg.continuousAt.comp (matrix_mul_contAt (matrix_transpose_contAt he) he)))
  let W : Set ((P × Symmetric3) × ℝ × ℝ) := U ×ˢ Ioi 0 ×ˢ ({0} : Set ℝ)ᶜ
  have hW : IsOpen W := hU.prod (isOpen_Ioi.prod isClosed_singleton.isOpen_compl)
  have hTW : ∀ p ∈ K, T (p, 0) ∈ W := by
    intro p hp
    simpa [T, W, a, j, e, f] using
      And.intro (hmem p hp) (And.intro (hdet p hp) (gram_det_ne_zero (E p) (hrank p hp)))
  obtain ⟨O, hO, hKO, ε, hε, heps⟩ := compact_zero_stability hK T hT hW hTW
  refine ⟨O, hO, hKO, ε, hε, ?_⟩
  intro p hp dJ dE dF hd
  have ht := heps p hp (dJ, dE, dF) hd
  exact ⟨ht.2.1, gram_rank_of_det_ne_zero _ ht.2.2, ht.1⟩

end

section
open Set MeasureTheory

lemma exists_det_bound_of_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ D : E →L[ℝ] E, ‖D‖ ≤ R → |D.det| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) R).exists_bound_of_continuousOn
    (contDiff_clm_det (E := E) 1).continuous.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro D hD
  have hb := hC D (by simpa only [Metric.mem_closedBall, dist_zero_right] using hD)
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (by linarith only [le_max_left C (0 : ℝ)])

lemma exists_bounded_chart_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : Continuous X)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source) {p : E} (hp : p ∈ V) :
    ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ closure W ⊆ V ∧ IsCompact (closure W) ∧
      Bornology.IsBounded (X '' W) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ X '' W, |(fderiv ℝ X.symm y).det| ≤ C := by
  obtain ⟨K, hpK, hKV, hK⟩ := local_compact_nhds (hV.mem_nhds hp)
  have hXK : IsCompact (X '' K) := hK.image hX
  have hKt : X '' K ⊆ X.target := by
    rintro y ⟨x, hx, rfl⟩
    exact X.map_source (hVX (hKV hx))
  have hc : ContinuousOn (fun y => (fderiv ℝ X.symm y).det) X.target :=
    (contDiff_clm_det (E := E) 1).continuous.comp_continuousOn
      (hXi.continuousOn_fderiv_of_isOpen X.open_target (by simp))
  obtain ⟨C, hC⟩ := hXK.exists_bound_of_continuousOn (hc.mono hKt)
  have hcl : closure (interior K) ⊆ K := hK.isClosed.closure_subset_iff.mpr interior_subset
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hpK,
    hcl.trans hKV, hK.of_isClosed_subset isClosed_closure hcl,
    hXK.isBounded.subset (image_mono interior_subset), max C 0 + 1, by positivity, ?_⟩
  intro y hy
  have hb := hC y (image_mono interior_subset hy)
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (by linarith only [le_max_left C (0 : ℝ)])

end

lemma synchronized_det_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E) (c : ℝ) (L : E →L[ℝ] ℝ) (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : E →L[ℝ] E) (z : ℝ), |z| ≤ 1 →
      ‖D - (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c (z • L))‖ ≤ ε →
      |D.det| ≤ C := by
  let T := lineShiftGradientOperator d c
  obtain ⟨C, hC, hb⟩ := exists_det_bound_of_norm (E := E)
    (ε + ‖ContinuousLinearMap.id ℝ E‖ + ‖T‖ * ‖L‖)
  refine ⟨C, hC, ?_⟩
  intro D z hz he
  apply hb D
  have hnorm : ‖T (z • L)‖ ≤ ‖T‖ * ‖L‖ := by
    apply (T.le_opNorm _).trans
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hz (norm_nonneg L)).trans_eq (one_mul _)) (norm_nonneg T)
  have hj := norm_add_le (ContinuousLinearMap.id ℝ E) (T (z • L))
  have ht : ‖D‖ ≤ ‖D - (ContinuousLinearMap.id ℝ E + T (z • L))‖ +
      ‖ContinuousLinearMap.id ℝ E + T (z • L)‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (D - (ContinuousLinearMap.id ℝ E + T (z • L)))
      (ContinuousLinearMap.id ℝ E + T (z • L))
  linarith only [hnorm, hj, ht, he]
end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_GradientColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix
open scoped Matrix.Norms.Elementwise

theorem symmetric_wave_polarization
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (B : Matrix (Fin 3) (Fin 3) ℝ) (hB : B.IsSymm)
    (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (hL : ∀ v, L (B *ᵥ v) = 0) :
    let R := (B * gradientColumns D).col
    D (R 0) 1 = D (R 1) 0 ∧ ∀ j, L (R j) = 0 := by
  dsimp only
  constructor
  · rw [gradientColumns_pairing, gradientColumns_pairing]
    have hsym : ((gradientColumns D)ᵀ * (B * gradientColumns D)).IsSymm := by
      unfold Matrix.IsSymm
      rw [transpose_mul, transpose_mul, transpose_transpose, hB]
      exact Matrix.mul_assoc _ _ _
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hsym
  · intro j
    convert hL ((gradientColumns D).col j) using 1
    all_goals try with_reducible_and_instances rfl
    rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SynchronizedChartWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Set Filter Topology MeasureTheory

theorem exists_synchronized_chart_waves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (hX : ContDiff ℝ (↑(⊤ : ℕ∞)) X)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    (D : E →L[ℝ] (Fin 2 → ℝ)) (hD : Function.Surjective D)
    (u : E → Fin 2 → ℝ) (hu : ∀ y ∈ X.source, D (X y) = u y)
    {p : E} (hp : p ∈ X.source) (hDp : fderiv ℝ X p = ContinuousLinearMap.id ℝ E)
    (d : E) (L : E →L[ℝ] ℝ) (hLd : L d = 1)
    {a b c m ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hε : 0 < ε) (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    (R : Fin 2 → E) (hRs : D (R 0) 1 = D (R 1) 0) (hRn : ∀ j, L (R j) = 0) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ X.source ∧
      ∀ H : SmoothScalar ℝ, Function.Periodic (smoothDirection 1 H).val 1 →
        (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t = 0) →
        (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar E, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → E → E,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k y, fderiv ℝ u y (F k 0 y) 1 = fderiv ℝ u y (F k 1 y) 0) ∧
          (∀ k j (ψ : E → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∃ Y : E ≃ E,
            ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
            (∀ x ∉ V, Y x = x) ∧ Y '' V = V ∧
            (∀ x, Y x = x + (c * k⁻¹ * localPullback X χ.val x *
              H.val (k * L (X x))) • d) ∧
            (∀ j x, ‖F k j x - (localPullback X χ.val x *
              (smoothDirection 1 H).val (k * L (X x))) • R j‖ < ε) ∧
            ∀ x, ‖fderiv ℝ Y x -
              (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c
                ((localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))) • L))‖ < ε := by
  have hL : L ≠ 0 := by intro hz; simp only [hz, _root_.zero_apply] at hLd; norm_num at hLd
  obtain ⟨W, hW, hpW, hWs, hflux⟩ := exists_frozen_chart_two_flux hdim μ X hX.contDiffOn hXi
    D hD u hu hp hDp L hL R hRs hRn hε
  let φ : SmoothScalar E := ⟨fun x => L (X x), L.contDiff.comp hX⟩
  have hφ : fderiv ℝ φ.val p = L := by
    change fderiv ℝ ((L : E → ℝ) ∘ (X : E → E)) p = L
    rw [fderiv_comp p L.differentiableAt (hX.differentiable (by simp) p), hDp]
    simp
  obtain ⟨V, hV, hpV, hVW, hmaps⟩ := exists_local_phase_diffeomorphisms d φ hφ hLd
    ha hb ha1 hb1 hm hε hpath hW hpW
  refine ⟨V, hV, hpV, hVW.trans hWs, ?_⟩
  intro H hHp hHm hH hHr χ hχ hχV hχb
  have hHabs : ∀ t, |(smoothDirection 1 H).val t| ≤ 1 := by
    intro t
    exact abs_le.mpr ⟨by linarith only [(hHr t).1, ha1], by linarith only [(hHr t).2, hb1]⟩
  have hχW : tsupport χ.val ⊆ X '' W := hχV.trans (image_mono hVW)
  have hχs : tsupport χ.val ⊆ X.target := hχW.trans (by
    rintro z ⟨x, hx, rfl⟩; exact X.map_source (hWs hx))
  let χp : SmoothScalar E := ⟨localPullback X χ.val,
    localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχ hχs⟩
  have hχp : HasCompactSupport χp.val := (localPullback_tsupport X χ.val hχ hχs).1
  have hχpV : tsupport χp.val ⊆ V := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (localPullback_tsupport X χ.val hχ hχs).2.1 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hWs (hVW hw))] using hw
  have hbχ : ∀ x, 0 ≤ χp.val x ∧ χp.val x ≤ 1 := localPullback_bounds X χ.val hχb
  obtain ⟨F, hF, hFs, hsym, hdiv, he⟩ := hflux (smoothDirection 1 H) hHp hHm hHabs χ hχ hχW hχb
  have hFfine : ∀ k j, tsupport (F k j) ⊆ V := by
    intro k j y hy
    obtain ⟨z, hz, rfl⟩ := (hFs k j).2.2 hy
    obtain ⟨w, hw, rfl⟩ := hχV hz
    simpa only [X.left_inv (hWs (hVW hw))] using hw
  refine ⟨F, hF, fun k j => ⟨(hFs k j).1, hFfine k j, (hFs k j).2.2⟩, hsym, hdiv, ?_⟩
  filter_upwards [he, hmaps H hH hHr χp hχp hχpV hbχ] with k hk hmap
  obtain ⟨Y, hY, hYs, hYi, hoff, himage, hderiv⟩ := hmap
  refine ⟨Y, hYs, hYi, hoff, himage, ?_, hk, hderiv⟩
  intro x
  rw [hY]
  change x + (c * (k⁻¹ * (localPullback X χ.val x * H.val (k * L (X x))))) • d = _
  congr 2
  ring

end

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma operatorMatrix_norm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D : (n → ℝ) →L[ℝ] (m → ℝ)) : ‖operatorMatrix D‖ ≤ ‖D‖ := by
  apply Matrix.norm_le_iff (norm_nonneg D) |>.mpr
  intro i j
  exact (norm_le_pi_norm (D (Pi.single j 1)) i).trans (by
    simpa only [Pi.norm_single, norm_one, mul_one] using D.le_opNorm (Pi.single j 1))

lemma operatorMatrix_sub {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (D E : (n → ℝ) →L[ℝ] (m → ℝ)) :
    operatorMatrix (D - E) = operatorMatrix D - operatorMatrix E := by
  ext i j; rfl

lemma operatorMatrix_continuous {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] :
    Continuous (operatorMatrix : ((n → ℝ) →L[ℝ] (m → ℝ)) → Matrix m n ℝ) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (continuous_apply i).comp (continuous_id.clm_apply continuous_const)

lemma columns_norm_lt {m : Type*} [Fintype m] (F : Matrix (Fin 3) m ℝ)
    {ε : ℝ} (hε : 0 < ε) (h : ∀ j, ‖F.col j‖ < ε) : ‖F‖ < ε := by
  apply (Matrix.norm_lt_iff hε).mpr
  intro i j
  exact (norm_le_pi_norm (F.col j) i).trans_lt (h j)

lemma operatorMatrix_inverse_fderiv (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm) (x : Coord3) :
    operatorMatrix (fderiv ℝ X.symm (X x)) = (operatorMatrix (fderiv ℝ X x))⁻¹ := by
  have h := fderiv_equiv_symm_comp X hX hXi x
  have hm := congrArg operatorMatrix h
  rw [operatorMatrix_comp, operatorMatrix_id] at hm
  exact Matrix.inv_eq_left_inv hm |>.symm

lemma gradientColumns_recomposition (X : Coord3 ≃ Coord3)
    (hX : Differentiable ℝ X) (hXi : Differentiable ℝ X.symm)
    (u : Coord3 → Fin 2 → ℝ) (hu : Differentiable ℝ u) (x : Coord3) :
    gradientColumns (fderiv ℝ (u ∘ X.symm) (X x)) =
      pushGradient (operatorMatrix (fderiv ℝ X x)) (gradientColumns (fderiv ℝ u x)) := by
  rw [fderiv_comp (X x) (hu _) (hXi _), X.symm_apply_apply]
  change (operatorMatrix ((fderiv ℝ u x).comp (fderiv ℝ X.symm (X x))))ᵀ = _
  rw [operatorMatrix_comp, Matrix.transpose_mul, operatorMatrix_inverse_fderiv X hX hXi]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_SplitJacobian
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma splitJacobian_continuous (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (c : ℝ) :
    Continuous (splitJacobian d L c) :=
  operatorMatrix_continuous.comp (continuous_const.add
    ((lineShiftGradientOperator d c).continuous.comp (continuous_id.smul continuous_const)))

lemma matrix_two_pairing_symm (E F : Matrix (Fin 3) (Fin 2) ℝ)
    (h : (Eᵀ * F) 1 0 = (Eᵀ * F) 0 1) : (Eᵀ * F).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.transpose_apply]

theorem exists_local_two_field_split
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {a b c m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-a) b, m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-a) b, ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-a) b, 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-a) b,
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-a) b, (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (V : Set Coord3),
      IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ V ⊆ X.source ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      ∃ M : ℝ, 0 < M ∧
      ∀ H : SmoothScalar ℝ, Function.Periodic (smoothDirection 1 H).val 1 →
        (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t = 0) →
        (∃ B : ℝ, ∀ t, |H.val t| ≤ B) →
        (∀ t, -a ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ b) →
      ∀ χ : SmoothScalar Coord3, HasCompactSupport χ.val → tsupport χ.val ⊆ X '' V →
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) →
        ∃ F : ℝ → Fin 2 → Coord3 → Coord3,
          (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
          (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ V ∧
            tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
          (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
            (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
          ∀ᶠ k : ℝ in atTop, ∃ Y : Coord3 ≃ Coord3,
            ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
            (∀ x ∉ V, Y x = x) ∧ Y '' V = V ∧
            (∀ x, Y x = x + (c * k⁻¹ * localPullback X χ.val x *
              H.val (k * L (X x))) • d) ∧
            (∀ x, |(fderiv ℝ Y x).det| ≤ M) ∧
            ∀ x ∈ V,
              let z := localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))
              let E := gradientColumns (fderiv ℝ u x)
              let Ft : Matrix (Fin 3) (Fin 2) ℝ := (A x).val * E + Matrix.of (fun i j => F k j x i)
              let J := operatorMatrix (fderiv ℝ Y x)
              let At := repairPushed (C z) J E Ft
              0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
                At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  classical
  let D := fderiv ℝ u p
  let E₀ := gradientColumns D
  let E : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun y => gradientColumns (fderiv ℝ u y)
  let F₀ := (A p).val * E₀
  let Fe : Coord3 → Matrix (Fin 3) (Fin 2) ℝ := fun y => (A y).val * E y
  let J := splitJacobian d L c
  let Fb : ℝ → Matrix (Fin 3) (Fin 2) ℝ := fun z => ((A p).val + z • B) * E₀
  have hEc : Continuous E := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact (continuous_apply j).comp ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hFc : ContinuousAt Fe p := matrix_mul_contAt (continuousAt_subtype_val.comp hA) hEc.continuousAt
  have hFbc : Continuous Fb := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact matrix_mul_contAt (continuousAt_const.add (continuousAt_id.smul continuousAt_const)) continuousAt_const
  have hrank : LinearIndependent ℝ E₀.col := gradientColumns_rank D hD
  have hexact : ∀ z ∈ Icc (-a) b, repairPushed (C z) (J z) E₀ (Fb z) = C z := by
    intro z hz
    exact repairPushed_exact (C z) (J z) ((A p).val + z • B) E₀ (hdet z hz).ne' (hconstit z hz)
  obtain ⟨O, _, hKO, ε, hε, heps⟩ := repairPushed_graph_stability isCompact_Icc
    C J (fun _ => E₀) Fb hC (fun _ _ => (splitJacobian_continuous d L c).continuousAt)
    (fun _ _ => continuousAt_const) (fun _ _ => hFbc.continuousAt) hdet (fun _ _ => hrank) hG
    (fun z hz => by rw [hexact z hz]; exact hCG z hz)
  have hnb : ∀ᶠ x in 𝓝 p, ‖E x - E₀‖ < ε/2 ∧ ‖Fe x - F₀‖ < ε/2 := by
    have he := hEc.continuousAt.eventually (Metric.ball_mem_nhds (E p) (half_pos hε))
    have hf := hFc.eventually (Metric.ball_mem_nhds (Fe p) (half_pos hε))
    simpa only [Metric.mem_ball, dist_eq_norm] using he.and hf
  obtain ⟨W, hWb, hWo, hpW⟩ := mem_nhds_iff.mp hnb
  obtain ⟨X, hpX, hXs, hX, hXi, hXu, hDX⟩ := exists_potential_chart hu p hD
    (hU.inter hWo) ⟨hpU, hpW⟩
  have hpol := symmetric_wave_polarization D B hB L hBn
  obtain ⟨V, hV, hpV, hVs, hpert⟩ := exists_synchronized_chart_waves
    (by simp [Coord3]) μ X hX hXi D hD u (fun y _ => hXu y)
    hpX hDX d L hLd ha hb ha1 hb1 hm (by positivity : 0 < ε/2)
    hpath (B * E₀).col hpol.1 hpol.2
  obtain ⟨M, hM, hMbd⟩ := synchronized_det_bound d c L (ε/2)
  refine ⟨X, V, hV, hpV, hVs.trans (fun _ hx => (hXs hx).1), hVs, hX, hXi, M, hM, ?_⟩
  intro H hHp hHm hH hHr χ hχ hχV hχb
  obtain ⟨F, hF, hFs, hsym, hdiv, hlim⟩ := hpert H hHp hHm hH hHr χ hχ hχV hχb
  refine ⟨F, hF, hFs, hdiv, ?_⟩
  filter_upwards [hlim] with k hk
  obtain ⟨Y, hY, hYi, hoff, himage, hform, hFerr, hJerr⟩ := hk
  refine ⟨Y, hY, hYi, hoff, himage, hform, ?_, ?_⟩
  · intro x
    apply hMbd _ _ _ (hJerr x).le
    have hz := scalar_cutoff_segment ha hb (localPullback_bounds X χ.val hχb x) (hHr (k * L (X x)))
    exact abs_le.mpr ⟨by linarith only [hz.1, ha1], by linarith only [hz.2, hb1]⟩
  intro x hx
  let z := localPullback X χ.val x * (smoothDirection 1 H).val (k * L (X x))
  let Q : Matrix (Fin 3) (Fin 2) ℝ := fun i j => F k j x i
  let Jy := operatorMatrix (fderiv ℝ Y x)
  have hz : z ∈ Icc (-a) b := scalar_cutoff_segment ha hb
    (localPullback_bounds X χ.val hχb x) (hHr _)
  have hsmall := hWb (hXs (hVs hx)).2
  have hdJ : ‖Jy - J z‖ < ε/2 := by
    change ‖operatorMatrix (fderiv ℝ Y x) - operatorMatrix _‖ < ε/2
    rw [← operatorMatrix_sub]
    exact (operatorMatrix_norm_le _).trans_lt (hJerr x)
  have hdF : ‖Fe x + Q - Fb z‖ < ε := by
    have hq : ‖Q - z • (B * E₀)‖ < ε/2 := by
      apply columns_norm_lt _ (half_pos hε)
      intro j
      exact hFerr j x
    have heq : Fe x + Q - Fb z = (Fe x - F₀) + (Q - z • (B * E₀)) := by
      dsimp only [Fb, F₀]
      rw [Matrix.add_mul, Matrix.smul_mul]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans_lt (by linarith only [hq, hsmall.2])
  have hbound : ‖(Jy - J z, E x - E₀, Fe x + Q - Fb z)‖ < ε := by
    rw [Prod.norm_def, Prod.norm_def, max_lt_iff, max_lt_iff]
    exact ⟨hdJ.trans (by linarith), hsmall.1.trans (by linarith), hdF⟩
  have hs := heps z (hKO hz) (Jy - J z) (E x - E₀) (Fe x + Q - Fb z) hbound
  simp only [add_sub_cancel] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  rw [gradientColumns_recomposition Y (hY.differentiable (by simp))
    (hYi.differentiable (by simp)) u (hu.differentiable (by simp))]
  apply repairPushed_mul _ _ _ _ hs.1.ne' hs.2.1
  rw [Matrix.mul_add]
  apply (symmetric_gram_pairing (A x) (E x)).add
  apply matrix_two_pairing_symm
  rw [← gradientColumns_pairing, ← gradientColumns_pairing]
  exact hsym k x

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_NormalStretch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

open MeasureTheory Set Filter Topology

lemma chart_impure_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (L : E →L[ℝ] ℝ)
    {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    {C : ℝ} (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    (θ δ k : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    μ {x | x ∈ V ∧ periodicPulse θ δ (k * L (X x)) ≠ 0 ∧
      periodicPulse θ δ (k * L (X x)) ≠ 1} ≤
    ENNReal.ofReal C * μ {y | y ∈ X '' V ∧ periodicPulse θ δ (k * L y) ≠ 0 ∧
      periodicPulse θ δ (k * L y) ≠ 1} := by
  have hθδ : Continuous (periodicPulse θ δ) := (periodicPulse_smooth hθ hδ).continuous
  let s := {y | y ∈ X '' V ∧ periodicPulse θ δ (k * L y) ≠ 0 ∧
      periodicPulse θ δ (k * L y) ≠ 1}
  have hXV : IsOpen (X '' V) := X.isOpen_image_of_subset_source hV hVX
  have hp : Continuous (fun y => periodicPulse θ δ (k * L y)) :=
    hθδ.comp (continuous_const.mul L.continuous)
  have hs : MeasurableSet s := hXV.measurableSet.inter
    ((isOpen_ne.preimage hp).measurableSet.inter
      (isOpen_ne.preimage hp).measurableSet)
  have hsX : s ⊆ X.target := fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := hy.1
    exact X.map_source (hVX hx)
  have he : X.symm '' s = {x | x ∈ V ∧ periodicPulse θ δ (k * L (X x)) ≠ 0 ∧
      periodicPulse θ δ (k * L (X x)) ≠ 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hy.1
      change X.symm (X z) ∈ V ∧
        periodicPulse θ δ (k * L (X (X.symm (X z)))) ≠ 0 ∧
        periodicPulse θ δ (k * L (X (X.symm (X z)))) ≠ 1
      rw [X.left_inv (hVX hz)]
      exact ⟨hz, hy.2⟩
    · intro hx
      exact ⟨X x, ⟨⟨x, hx.1, rfl⟩, hx.2⟩, X.left_inv (hVX hx.1)⟩
  rw [← he]
  exact measure_image_le_det μ hs
    (fun y hy => (hXi y (hsX hy)).differentiableAt (X.open_target.mem_nhds (hsX hy)))
    (X.symm.injOn.mono hsX) (fun y hy => hC y hy.1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_LocalPullbackTsupportInside
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise

lemma localPullback_tsupport_inside
    {E V : Type*} [TopologicalSpace E] [T2Space E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (hf : HasCompactSupport f)
    {U : Set E} (hU : U ⊆ X.source) (hfs : tsupport f ⊆ X '' U) :
    tsupport (localPullback X f) ⊆ U := by
  have ht : tsupport f ⊆ X.target := hfs.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hU hx))
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (localPullback_tsupport X f hf ht).2.1 hx
  obtain ⟨z, hz, rfl⟩ := hfs hy
  simpa only [X.left_inv (hU hz)] using hz

lemma pushed_exception_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (Y : E ≃ E) (hY : Differentiable ℝ Y) {U : Set E} (hU : MeasurableSet U)
    (hYU : Y '' U = U) (z : E → ℝ) (hz : Continuous z) (a b : ℝ)
    {C : ℝ} (hC : ∀ x, |(fderiv ℝ Y x).det| ≤ C) :
    μ {x | x ∈ U ∧ z (Y.symm x) ≠ a ∧ z (Y.symm x) ≠ b} ≤
      ENNReal.ofReal C * μ {x | x ∈ U ∧ z x ≠ a ∧ z x ≠ b} := by
  let S := {x | x ∈ U ∧ z x ≠ a ∧ z x ≠ b}
  have hS : MeasurableSet S := hU.inter
    (((isOpen_ne.preimage hz).measurableSet).inter ((isOpen_ne.preimage hz).measurableSet))
  have he : Y '' S = {x | x ∈ U ∧ z (Y.symm x) ≠ a ∧ z (Y.symm x) ≠ b} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hYU ▸ mem_image_of_mem Y hy.1, by simpa only [Y.symm_apply_apply] using hy.2⟩
    · intro hx
      have hxU : Y.symm x ∈ U := by
        obtain ⟨y, hy, he⟩ := (show x ∈ Y '' U from hYU.symm ▸ hx.1)
        simpa only [← he, Y.symm_apply_apply] using hy
      exact ⟨Y.symm x, ⟨hxU, hx.2⟩, Y.apply_symm_apply x⟩
  rw [← he]
  exact measure_image_le_det μ hS (fun x _ => hY x) Y.injective.injOn (fun x _ => hC x)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_MatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

lemma exists_two_state_primitive {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) :
    ∃ H : SmoothScalar ℝ,
      (∀ t, (smoothDirection 1 H).val t = periodicPulse θ δ t - θ) ∧
      Function.Periodic (smoothDirection 1 H).val 1 ∧
      (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t) = 0 ∧
      (∃ b : ℝ, ∀ t, |H.val t| ≤ b) ∧
      (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧
        (smoothDirection 1 H).val t ≤ 1 - θ) := by
  let h : SmoothScalar ℝ := ⟨fun t => periodicPulse θ δ t - θ,
    (periodicPulse_smooth (hδ.le.trans hδθ) hδ).sub contDiff_const⟩
  have hp : Function.Periodic h.val 1 := by
    intro t
    change periodicPulse θ δ (t + 1) - θ = periodicPulse θ δ t - θ
    rw [show periodicPulse θ δ (t + 1) = periodicPulse θ δ t from periodicPulse_periodic θ δ t]
  have hm : (∫ t in (0 : ℝ)..1, h.val t) = 0 := by
    change (∫ t in (0 : ℝ)..1, periodicPulse θ δ t - θ) = 0
    rw [intervalIntegral.integral_sub
      ((periodicPulse_smooth (hδ.le.trans hδθ) hδ).continuous.intervalIntegrable _ _)
      intervalIntegrable_const, periodicPulse_integral (hδ.le.trans hδθ) hδ hw]
    simp
  refine ⟨meanZeroPrimitive h, ?_, by simpa using hp, by simpa using hm,
    periodic_smoothScalar_bounded _ (meanZeroPrimitive_periodic h hp hm), ?_⟩
  · intro t; rw [smoothDirection_meanZeroPrimitive]
  · intro t
    rw [smoothDirection_meanZeroPrimitive]
    change -θ ≤ periodicPulse θ δ t - θ ∧ periodicPulse θ δ t - θ ≤ 1 - θ
    obtain ⟨hl, hu⟩ := periodicPulse_bounds hδ hδθ hw t
    constructor <;> linarith

lemma exists_transition_width {θ ε M : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ θ ∧ θ + δ ≤ 1 ∧ 3 * δ ≤ 1 ∧ 4 * δ * M < ε := by
  let b := min θ (min (1-θ) (min (1/3) (ε / (4 * (|M|+1)))))
  have hb : 0 < b := by
    dsimp only [b]
    exact lt_min hθ (lt_min (by linarith) (lt_min (by norm_num) (by positivity)))
  refine ⟨b/2, half_pos hb, ?_, ?_, ?_, ?_⟩
  · exact (half_le_self hb.le).trans (min_le_left _ _)
  · have h : b ≤ 1-θ := (min_le_right θ _).trans (min_le_left (1-θ) _)
    linarith
  · have h : b ≤ 1/3 := (min_le_right θ _).trans ((min_le_right (1-θ) _).trans
      (min_le_left (1/3) _))
    linarith
  · have h : b ≤ ε / (4 * (|M|+1)) := (min_le_right θ _).trans ((min_le_right (1-θ) _).trans
      (min_le_right (1/3) _))
    have hd : 0 < 4 * (|M|+1) := by positivity
    have he := (le_div_iff₀ hd).mp h
    have ha := le_abs_self M
    nlinarith [abs_nonneg M, mul_nonneg hb.le (sub_nonneg.mpr ha)]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_SmoothCutoffSmallMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
namespace ScalarConductivity

theorem exists_smooth_cutoff_small_margin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.InnerRegularCompactLTTop μ]
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hμU : μ U ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ χ : E → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, χ x ∈ Icc 0 1) ∧ μ {x | x ∈ U ∧ χ x ≠ 1} < ε := by
  obtain ⟨K, hKU, hK, hKμ⟩ := hU.measurableSet.exists_isCompact_sdiff_lt hμU hε
  obtain ⟨χ, hχ₀, hχ₁, hχb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
    hU.isClosed_compl hK.isClosed (disjoint_left.mpr (fun _ hx hxK => hx (hKU hxK))) (n := ⊤)
  have ht : tsupport (χ : E → ℝ) ⊆ U := by
    intro x hx
    by_contra hxU
    apply (notMem_tsupport_iff_eventuallyEq.mpr
      (hχ₀.filter_mono (nhds_le_nhdsSet hxU))) hx
  refine ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff,
    (hUb.subset ht).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) subset_closure,
    ht, hχb, ?_⟩
  apply (measure_mono ?_).trans_lt hKμ
  intro x hx
  exact ⟨hx.1, fun hxK => hx.2 ((hχ₁.filter_mono (nhds_le_nhdsSet hxK)).self_of_nhds)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PairedPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set

namespace ScalarConductivity
open MeasureTheory Set Filter Topology
open scoped Manifold ENNReal

lemma exists_smooth_compact_majorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) :
    ∃ f : SmoothScalar E, HasCompactSupport f.val ∧
      (∀ x, 0 ≤ f.val x ∧ f.val x ≤ 1) ∧ ∀ x ∈ K, f.val x = 1 := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨f, hf₀, hf₁, hfb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
    Metric.isOpen_ball.isClosed_compl hK.isClosed
    (disjoint_left.mpr (fun _ hx hxK => hx (hr hxK))) (n := ⊤)
  have ht : tsupport (f : E → ℝ) ⊆ Metric.ball 0 r := by
    intro x hx
    by_contra hxU
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (hf₀.filter_mono (nhds_le_nhdsSet hxU))) hx
  refine ⟨⟨f, contMDiff_iff_contDiff.mp f.contMDiff⟩, ?_, hfb, ?_⟩
  · exact (Metric.isBounded_ball.subset ht).isCompact_closure.of_isClosed_subset
      (isClosed_tsupport _) subset_closure
  · intro x hx
    exact (hf₁.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds

lemma chart_pullback_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) {V : Set E} (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    {C : ℝ} (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    {s : Set E} (hs : MeasurableSet s) (hsV : s ⊆ X '' V) :
    μ {x | x ∈ V ∧ X x ∈ s} ≤ ENNReal.ofReal C * μ s := by
  have hsX : s ⊆ X.target := hsV.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hVX hx))
  have he : X.symm '' s = {x | x ∈ V ∧ X x ∈ s} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hyz⟩ := hsV hy
      subst y
      rw [X.left_inv (hVX hz)]
      exact ⟨hz, hy⟩
    · intro hx
      exact ⟨X x, hx.2, X.left_inv (hVX hx.1)⟩
  rw [← he]
  exact measure_image_le_det μ hs
    (fun y hy => (hXi y (hsX hy)).differentiableAt (X.open_target.mem_nhds (hsX hy)))
    (X.symm.injOn.mono hsX) (fun y hy => hC y (hsV hy))

theorem exists_chart_pure_profile
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    (hSb : Bornology.IsBounded (X '' V)) (hμS : μ (X '' V) ≠ ∞)
    {C : ℝ} (hCpos : 0 < C) (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) {θ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) :
    ∃ (χ : SmoothScalar E) (H : SmoothScalar ℝ),
      HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' V ∧
      (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
      Function.Periodic (smoothDirection 1 H).val 1 ∧
      (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t) = 0 ∧
      (∃ b : ℝ, ∀ t, |H.val t| ≤ b) ∧
      (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧
        (smoothDirection 1 H).val t ≤ 1-θ) ∧
      ∀ᶠ n : ℕ in atTop,
        μ {x | x ∈ V ∧
          localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x)) ≠ -θ ∧
          localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x)) ≠ 1-θ} ≤
          ENNReal.ofReal ε := by
  let η := ε / (4*C)
  have hη : 0 < η := by dsimp [η]; positivity
  have hS : IsOpen (X '' V) := X.isOpen_image_of_subset_source hV hVX
  obtain ⟨χ, hχs, hχc, hχV, hχb, hmargin⟩ := exists_smooth_cutoff_small_margin μ hS hSb hμS
    (ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  let χ' : SmoothScalar E := ⟨χ, hχs⟩
  obtain ⟨f, hfc, hfb, hfS⟩ := exists_smooth_compact_majorant hSb.isCompact_closure
  obtain ⟨δ, hδ, hδθ, hw, hδw, hδη⟩ := exists_transition_width hθ hθ1 hη
    (M := ∫ x, f.val x ∂μ)
  obtain ⟨H, hHder, hHp, hHm, hHb, hHr⟩ := exists_two_state_primitive hδ hδθ hw
  refine ⟨χ', H, hχc, hχV, hχb, hHp, hHm, hHb, hHr, ?_⟩
  have hpure := eventually_impure_measure_le μ L hL f hfc (fun x => (hfb x).1)
    (X '' V) (fun x hx => (hfS x (subset_closure hx)).ge) hδ hδθ hw hδw hδη
  have hcm : μ {x | x ∈ V ∧ χ (X x) ≠ 1} ≤ ENNReal.ofReal C * ENNReal.ofReal η := by
    have hcmeas : MeasurableSet {y | y ∈ X '' V ∧ χ y ≠ 1} :=
      hS.measurableSet.inter (isOpen_ne.preimage hχs.continuous).measurableSet
    have hh := chart_pullback_measure_le μ X hVX hXi hC hcmeas (fun _ hy => hy.1)
    have hset : {x | x ∈ V ∧ X x ∈ {y | y ∈ X '' V ∧ χ y ≠ 1}} =
        {x | x ∈ V ∧ χ (X x) ≠ 1} := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, ⟨x, hx.1, rfl⟩, hx.2⟩⟩
    rw [hset] at hh
    exact hh.trans (mul_le_mul_right hmargin.le _)
  filter_upwards [hpure] with n hn
  have himpure := (chart_impure_measure_le μ X L hV hVX hXi hC θ δ (n+1) hθ.le hδ).trans
    (mul_le_mul_right hn (ENNReal.ofReal C))
  calc
    _ ≤ μ ({x | x ∈ V ∧ χ (X x) ≠ 1} ∪
        {x | x ∈ V ∧ periodicPulse θ δ ((n+1 : ℝ) * L (X x)) ≠ 0 ∧
          periodicPulse θ δ ((n+1 : ℝ) * L (X x)) ≠ 1}) := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      by_cases hc : χ (X x) = 1
      · right
        have hd : localPullback X χ'.val x = 1 := by
          simp only [localPullback, ite_eq_left (hVX hx.1)]
          exact hc
        rw [hd, one_mul, hHder] at hx
        exact ⟨hx.1, fun hz => hx.2.1 (by rw [hz]; ring),
          fun hz => hx.2.2 (by rw [hz])⟩
      · exact Or.inl ⟨hx.1, hc⟩
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal η + ENNReal.ofReal C * ENNReal.ofReal η :=
      add_le_add hcm himpure
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hCpos.le, ← ENNReal.ofReal_add (mul_nonneg hCpos.le hη.le)
        (mul_nonneg hCpos.le hη.le)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [η]
      field_simp
      nlinarith

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_LocalSplitSubpatchRetained
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3 _root_.OAI.ScalarConductivity.instMeasurableSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set MeasureTheory Filter Topology
open scoped ENNReal Matrix.Norms.Elementwise
theorem exists_local_split_on_subpatch_retained_oai
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    (u : Coord3 → Fin 2 → ℝ) (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (A : Coord3 → Symmetric3) {p : Coord3} (hA : ContinuousAt A p)
    (hD : Function.Surjective (fderiv ℝ u p))
    (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (hLd : L d = 1)
    (B : Mat3) (hB : B.IsSymm) (hBn : ∀ v, L (B *ᵥ v) = 0)
    {θ c m : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hm : 0 < m) (hpath : ∀ z ∈ Icc (-θ) (1-θ), m ≤ 1 + c * z)
    (C : ℝ → Symmetric3) (hC : ∀ z ∈ Icc (-θ) (1-θ), ContinuousAt C z)
    (hdet : ∀ z ∈ Icc (-θ) (1-θ), 0 < (splitJacobian d L c z).det)
    (hconstit : ∀ z ∈ Icc (-θ) (1-θ),
      (C z).val = (splitJacobian d L c z).det⁻¹ •
        (splitJacobian d L c z * ((A p).val + z • B) * (splitJacobian d L c z)ᵀ))
    {G : Set (ℝ × Symmetric3)} (hG : IsOpen G)
    (hCG : ∀ z ∈ Icc (-θ) (1-θ), (z, C z) ∈ G)
    {U : Set Coord3} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ (X : OpenPartialHomeomorph Coord3 Coord3) (W : Set Coord3),
      IsOpen W ∧ p ∈ W ∧ closure W ⊆ U ∧ IsCompact (closure W) ∧ W ⊆ X.source ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) X ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target ∧
      ∀ O : Set Coord3, IsOpen O → O ⊆ W →
      ∀ ε : ℝ, 0 < ε →
      ∃ (χ : SmoothScalar Coord3) (H : SmoothScalar ℝ) (F : ℝ → Fin 2 → Coord3 → Coord3),
        HasCompactSupport χ.val ∧ tsupport χ.val ⊆ X '' O ∧
        (∀ x, 0 ≤ χ.val x ∧ χ.val x ≤ 1) ∧
        (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧ (smoothDirection 1 H).val t ≤ 1-θ) ∧
        (∀ k j, ContDiff ℝ (↑(⊤ : ℕ∞)) (F k j)) ∧
        (∀ k j, HasCompactSupport (F k j) ∧ tsupport (F k j) ⊆ O ∧ tsupport (F k j) ⊆ X.symm '' tsupport χ.val) ∧
        (∀ k j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ →
          (∫ y, fderiv ℝ ψ y (F k j y) ∂μ) = 0) ∧
        ∀ᶠ n : ℕ in atTop, ∃ Y : Coord3 ≃ Coord3,
          ContDiff ℝ (↑(⊤ : ℕ∞)) Y ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) Y.symm ∧
          (∀ x ∉ O, Y x = x) ∧ Y '' O = O ∧
          (∀ x, Y x = x + (c * (n+1 : ℝ)⁻¹ * localPullback X χ.val x *
            H.val ((n+1 : ℝ) * L (X x))) • d) ∧
          μ {x | x ∈ O ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ -θ ∧
            localPullback X χ.val (Y.symm x) *
              (smoothDirection 1 H).val ((n+1 : ℝ) * L (X (Y.symm x))) ≠ 1-θ} ≤
            ENNReal.ofReal ε ∧
          ∀ x ∈ O,
            let z := localPullback X χ.val x * (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
            let E := gradientColumns (fderiv ℝ u x)
            let Ft := (A x).val * E + Matrix.of (fun i j => F (n+1 : ℝ) j x i)
            let J := operatorMatrix (fderiv ℝ Y x)
            let At := repairPushed (C z) J E Ft
            0 < J.det ∧ LinearIndependent ℝ E.col ∧ (z, At) ∈ G ∧
              At.val * gradientColumns (fderiv ℝ (u ∘ Y.symm) (Y x)) = pushFlux J Ft := by
  have hb : 0 ≤ 1-θ := by linarith
  have hb1 : 1-θ ≤ 1 := by linarith
  obtain ⟨X, V, hV, hpV, hVU, hVX, hX, hXi, M, hM, hop⟩ :=
    exists_local_two_field_split μ u hu A hA hD d L hLd B hB hBn
      hθ.le hb hθ1.le hb1 hm hpath C hC hdet hconstit hG hCG hU hpU
  obtain ⟨W, hW, hpW, hWV, hWc, hXW, D, hDpos, hDb⟩ :=
    exists_bounded_chart_neighborhood X hX.continuous hXi hV hVX hpV
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hWX : W ⊆ X.source := hWV'.trans hVX
  have hL : L ≠ 0 := by intro hz; simp only [hz, _root_.zero_apply] at hLd; norm_num at hLd
  refine ⟨X, W, hW, hpW, hWV.trans hVU, hWc, hWX, hX, hXi, ?_⟩
  intro O hO hOW ε hε
  have hOX : O ⊆ X.source := hOW.trans hWX
  have hOV : O ⊆ V := hOW.trans hWV'
  have hXO := hXW.subset (image_mono hOW)
  obtain ⟨χ, H, hχc, hχW, hχb, hHp, hHm, hHb, hHr, hpure⟩ :=
    exists_chart_pure_profile μ X hO hOX (hXi.differentiableOn (by simp))
      hXO hXO.measure_lt_top.ne hDpos (fun x hx => hDb x (image_mono hOW hx)) L hL hθ hθ1 (div_pos hε hM)
  obtain ⟨F, hF, hFs, hdiv, hlim⟩ := hop H hHp hHm hHb hHr χ hχc
    (hχW.trans (image_mono hOV)) hχb
  have hχt : tsupport χ.val ⊆ X.target := hχW.trans (by
    rintro y ⟨x, hx, rfl⟩; exact X.map_source (hOX hx))
  have hχp : tsupport (localPullback X χ.val) ⊆ O :=
    localPullback_tsupport_inside X χ.val hχc hOX hχW
  refine ⟨χ, H, F, hχc, hχW, hχb, hHr, hF, ?_, hdiv, ?_⟩
  · intro k j
    refine ⟨(hFs k j).1, ?_, (hFs k j).2.2⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hFs k j).2.2 hx
    obtain ⟨z, hz, rfl⟩ := hχW hy
    simpa only [X.left_inv (hOX hz)] using hz
  have hnat : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually hlim, hpure] with n hn hnp
  obtain ⟨Y, hY, hYi, _, _, hform, hYM, hstate⟩ := hn
  have hoff : ∀ x ∉ O, Y x = x := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport (fun h => hx (hχp h))
    rw [hform x, hz, mul_zero, zero_mul, zero_smul, add_zero]
  have himage := equiv_image_set_of_eq_off Y O hoff
  refine ⟨Y, hY, hYi, hoff, himage, hform, ?_, fun x hx => hstate x (hOV hx)⟩
  let z : Coord3 → ℝ := fun x => localPullback X χ.val x *
    (smoothDirection 1 H).val ((n+1 : ℝ) * L (X x))
  have hz : Continuous z :=
    (localPullback_contDiff X hX.contDiffOn χ.val (smoothScalar_contDiff χ) hχc hχt).continuous.mul
      ((smoothScalar_contDiff (smoothDirection 1 H)).continuous.comp
        (continuous_const.mul (L.continuous.comp hX.continuous)))
  have he := pushed_exception_measure_le μ Y (hY.differentiable (by simp))
    hO.measurableSet himage z hz (-θ) (1-θ) hYM
  calc
    _ ≤ ENNReal.ofReal M * μ {x | x ∈ O ∧ z x ≠ -θ ∧ z x ≠ 1-θ} := he
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (ε/M) := mul_le_mul_right hnp _
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hM.le, mul_div_cancel₀ ε hM.ne']

end ScalarConductivity

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.exists_local_split_on_subpatch_retained_oai := @OAI.ScalarConductivity.exists_local_split_on_subpatch_retained_oai
