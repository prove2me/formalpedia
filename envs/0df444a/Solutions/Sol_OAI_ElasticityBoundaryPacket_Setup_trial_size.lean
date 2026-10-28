-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.trial_size
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:11:13.336571+00:00
-- url     : https://prove2.me/submissions/3d00da84-249b-4629-a8dc-1d5b4a35a0c8

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_field_gradient_mass
import Theorems.Thm_OAI_ElasticityBoundaryPacketMass_cutoff_value_bound

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal first and second coordinate chain rules. The maps are genuine
Frechet-smooth maps; a tensor pullback will use these identities, rather
than postulating a transformed elasticity operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChainRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_dd {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dd f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end ElasticityBoundaryChainRule

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Honest L2 bounds and exact change of variables for physical boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryProfileBounds
open ElasticityBoundaryMVCalculus ElasticityBoundaryScaling ElasticityBoundaryWeights
  ElasticityBoundaryProfile
lemma measurable_halfspace : MeasurableSet halfspace :=
  (isOpen_lt continuous_const (continuous_apply 2)).measurableSet

end ElasticityBoundaryProfileBounds

end
end
section
/-! Orthogonal covariance of the literal isotropic tensor in physical
coordinates. The frame is an actual Euclidean isometry, not a gauge freedom. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryRotation
open ElasticityBoundaryLayerOperator

lemma frameMatrix_orthogonal (Q : X ≃ₗᵢ[ℝ] X) (j k : I) :
    (∑ i, frameMatrix Q i j*frameMatrix Q i k)=if j=k then 1 else 0 := by
  have hreal : (∑ i, Q (EuclideanSpace.single j 1) i*Q (EuclideanSpace.single k 1) i)=
      if j=k then 1 else 0 := by
    calc
      _ = inner ℝ (Q (EuclideanSpace.single k 1)) (Q (EuclideanSpace.single j 1)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        rfl
      _ = inner ℝ (EuclideanSpace.single k 1) (EuclideanSpace.single j 1) := Q.inner_map_map _ _
      _ = _ := by simp [EuclideanSpace.inner_single_left, PiLp.single_apply, eq_comm]
  simpa only [frameMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_sum, apply_ite,
    Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal hreal

end ElasticityBoundaryRotation

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Transferring a trial supported in an honest chart produces an actual
 globally smooth compact physical field, without imposing artificial boundary
 data. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma chartTransfer_apply (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {y : E} (hy : y∈e.source) :
    chartTransfer e η u (e y)=u y := by
  unfold chartTransfer
  rw [e.left_inv hy]
  by_cases h : u y=0
  · simp [h]
  · rw [hη _ (mem_image_of_mem e (hu h)),one_smul]

end ElasticityBoundary

end
end
section
/-! Locality and true support control for the physical differential operator
and the compact chart transfer. These use germs, not formal coefficients. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryOperatorLocal
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryPhysicalStrong
  ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
lemma chartTransfer_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (e.symm z)) := by
  filter_upwards [e.open_target.mem_nhds hx] with z hz
  have h := chartTransfer_apply e hη hu (e.map_target hz)
  simpa only [e.right_inv hz] using h

omit [NormedSpace ℝ E] in
lemma chartTransfer_extension_germ (e : OpenPartialHomeomorph E E) {K : Set E}
    {η : E → ℝ} (hη : ∀ x∈e '' K, η x=1)
    {u : E → F} (hu : Function.support u⊆K) {x : E} (hx : x∈e.target)
    {Ψ : E → E} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) :
    chartTransfer e η u =ᶠ[𝓝 x] (fun z => u (Ψ z)) := by
  filter_upwards [chartTransfer_germ e hη hu hx,hΨ] with z hz hΨz
  rw [hz,hΨz]

end ElasticityBoundaryOperatorLocal

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryParametrix
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Physical displacements obtained from compact chart fields. Their literal
strong Lamé force is the constructed curved-coordinate operator on the
whole trial support, rather than a formally equated auxiliary DN system. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalTransfer
open ElasticityBoundary ElasticityBoundaryChainRule ElasticityBoundaryPullback
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryRotation ElasticityBoundaryFrameOperator
  ElasticityBoundaryChartOperator ElasticityBoundaryOperatorLocal ElasticityBoundaryStrongLayer

lemma transferred_germ (e : OpenPartialHomeomorph X X) {K : Set X}
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) {x : X} (hx : x∈e.target)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 x] e.symm) (i : I) :
    transferred e η Q u i =ᶠ[𝓝 x]
      mix (frameMatrix Q) (fun j z => u j (Ψ z).ofLp) i :=
  chartTransfer_extension_germ e hη (support_lifted Q u hu i) hx hΨ

end ElasticityBoundaryPhysicalTransfer

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The exact inverse derivative at normalized physical boundary charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityBoundaryInverseGeometry
open Elasticity ElasticityBoundaryChainRule ElasticityBoundaryRotation

lemma inverse_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (k α : I) :
    Q.symm (EuclideanSpace.single k 1) α=Q (EuclideanSpace.single α 1) k := by
  have h := Q.inner_map_eq_flip (EuclideanSpace.single α 1) (EuclideanSpace.single k 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul, mul_one, starRingEnd_apply, star_trivial] using h.symm

end ElasticityBoundaryInverseGeometry

end
end
section
/-! Exact inversion of the fixed physical orthogonal frame, including
quantitative component control needed for the genuine residual norm. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameInverse
open ElasticityBoundaryRotation ElasticityBoundaryInverseGeometry ElasticityBoundaryFrameOperator

lemma frameMatrix_symm (Q : X ≃ₗᵢ[ℝ] X) (i j : I) :
    frameMatrix Q.symm i j=frameMatrix Q j i := by
  exact congrArg Complex.ofReal (inverse_frame_entry Q j i)

lemma frameMatrix_rows (Q : X ≃ₗᵢ[ℝ] X) (i j : I) :
    (∑ s, frameMatrix Q i s*frameMatrix Q j s)=if i=j then 1 else 0 := by
  simpa only [frameMatrix_symm] using frameMatrix_orthogonal Q.symm i j

lemma frame_inverse (Q : X ≃ₗᵢ[ℝ] X) (v : I → ℂ) (i : I) :
    (∑ s, frameMatrix Q i s*(∑ j, frameMatrix Q j s*v j))=v i := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,frameMatrix_rows]
  simp

lemma norm_sq_sum_three (v : I → ℂ) : ‖∑ i, v i‖^2 ≤ 3*∑ i, ‖v i‖^2 := by
  have h := norm_sum_le Finset.univ v
  have h0 : 0≤∑ i, ‖v i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs : (∑ i, ‖v i‖)^2≤3*∑ i, ‖v i‖^2 := by
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖v 0‖-‖v 1‖),sq_nonneg (‖v 0‖-‖v 2‖),sq_nonneg (‖v 1‖-‖v 2‖)]
  exact (sq_le_sq₀ (norm_nonneg _) h0 |>.mpr h).trans hs

lemma norm_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (i j : I) : ‖frameMatrix Q i j‖≤1 := by
  have h := PiLp.norm_apply_le (p := (2:ENNReal)) (Q (EuclideanSpace.single j 1)) i
  simpa only [frameMatrix,Complex.norm_real,Q.norm_map,EuclideanSpace.single,PiLp.norm_single,Real.norm_eq_abs,abs_one] using h

end ElasticityBoundaryFrameInverse

end
end
section
/-! Honest physical boundary change of variables. The Jacobian is not
normalized away: it is retained exactly and bounded only on the actual
compact trial support. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ElasticityBoundaryChartIntegral
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A compactly supported physical integrand pulls back with its exact
Jacobian, including the domain's half-space indicator. -/
theorem compact_chart_integral (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set E} (hs : K⊆e.source) (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : E → E} (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (f g : E → ℝ) (hf : Function.support f⊆e '' K) (hg : Function.support g⊆K)
    (hfg : ∀ y∈e.source, f (e y)=g y) :
    (∫ x in Ω, f x ∂μ)=(∫ y in H, |(fderiv ℝ Φ y).det| *g y ∂μ) := by
  have hd (y : E) (hy : y∈e.source) : HasFDerivAt e (fderiv ℝ e y) y :=
    ((he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hy)).hasFDerivAt
  rw [← integral_indicator hΩ]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) (f := Ω.indicator f)
    (fun x hx => by
      have hh : f x=0 := by
        by_contra hn
        obtain ⟨y,hy,rfl⟩ := hf hn
        exact hx (e.map_source (hs hy))
      simp only [indicator,hh,ite_self])]
  rw [integral_target_eq_integral_abs_det_fderiv_smul μ hd]
  have heq : (∫ y in e.source, |(fderiv ℝ e y).det| • Ω.indicator f (e y) ∂μ)=
      ∫ y in e.source, H.indicator (fun z => |(fderiv ℝ Φ z).det| *g z) y ∂μ := by
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro y hy
    dsimp only
    by_cases hyK : y∈K
    · rw [← (hΦ y hyK).fderiv_eq]
      by_cases hyH : y∈H
      · rw [indicator_of_mem ((hhalf y hy).mpr hyH),indicator_of_mem hyH,hfg y hy]
        rfl
      · rw [indicator_of_notMem (fun h => hyH ((hhalf y hy).mp h)),indicator_of_notMem hyH,smul_zero]
    · have hz : g y=0 := Function.notMem_support.mp (fun h => hyK (hg h))
      simp only [indicator, hfg y hy]
      simp only [hz,mul_zero,smul_eq_mul,ite_self]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_indicator hH
  · intro y hy
    have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs (hg h)))
    simp only [indicator,hz,mul_zero,ite_self]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_abs_det_bound {K : Set E} (hK : IsCompact K) {Φ : E → E}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ y∈K, |(fderiv ℝ Φ y).det|≤C := by
  have hc : Continuous (fun y => |(fderiv ℝ Φ y).det|) := by
    exact (ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv (by simp))).abs
  obtain ⟨C,hC⟩ := (hK.image hc).bddAbove
  exact ⟨max C 0,le_max_right _ _,fun y hy => (hC (mem_image_of_mem _ hy)).trans (le_max_left _ _)⟩

omit [FiniteDimensional ℝ E] in
/-- The physical mass bound used for actual localized stress residuals. -/
theorem compact_jacobian_mass_bound {K H : Set E} (hK : IsCompact K)
    {Φ : E → E} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∃ C : ℝ, 0≤C ∧ ∀ g : E → ℝ, Continuous g → HasCompactSupport g →
      Function.support g⊆K → (∀ y, 0≤g y) →
      (∫ y in H, |(fderiv ℝ Φ y).det| *g y ∂μ)≤C*(∫ y in H, g y ∂μ) := by
  obtain ⟨C,hC,hb⟩ := compact_abs_det_bound hK hΦ
  refine ⟨C,hC,fun g hg hc hs hn => ?_⟩
  have hdet : Continuous (fun y => |(fderiv ℝ Φ y).det|) :=
    (ContinuousLinearMap.continuous_det.comp (hΦ.continuous_fderiv (by simp))).abs
  have hInt : Integrable (fun y => |(fderiv ℝ Φ y).det| *g y) μ :=
    (hdet.mul hg).integrable_of_hasCompactSupport hc.mul_left
  rw [← integral_const_mul]
  apply integral_mono hInt.integrableOn ((hg.integrable_of_hasCompactSupport hc).const_mul C).integrableOn
  intro y
  by_cases hy : y∈K
  · exact mul_le_mul_of_nonneg_right (hb y hy) (hn y)
  · have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs h))
    simp only [hz,mul_zero,le_refl]

end ElasticityBoundaryChartIntegral

end
end
section
/-! A quantitative physical L2 transfer through an honest boundary chart.
The constants are independent of trial fields and concentration parameters. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryChartMass
open ElasticityBoundaryChartIntegral ElasticityBoundaryFrameInverse
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation

lemma inverseMix_support (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) {K : Set X}
    (hg : ∀ j, Function.support (g j)⊆K) (i : I) :
    Function.support (inverseMix Q g i)⊆K := by
  intro y hy
  by_contra hn
  apply hy
  apply Finset.sum_eq_zero
  intro j _
  have hz : g j y=0 := Function.notMem_support.mp (fun h => hn (hg j h))
  rw [hz,mul_zero]

lemma inverseMix_bound (Q : X ≃ₗᵢ[ℝ] X) (g : I → X → ℂ) (i : I) (y : X) :
    ‖inverseMix Q g i y‖^2≤3*∑ j, ‖g j y‖^2 := by
  apply (norm_sq_sum_three _).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_frame_entry Q i j))

lemma norm_sq_integrableOn {g : X → ℂ} {K : Set X} (hK : IsCompact K)
    (hg : Continuous g) (hs : Function.support g⊆K) (H : Set X) :
    IntegrableOn (fun y => ‖g y‖^2) H := by
  have hc : HasCompactSupport g := hK.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs hK.isClosed)
  have hc' : HasCompactSupport (fun y => ‖g y‖^2) :=
    hc.norm.comp_left (g := fun r : ℝ => r^2) (by norm_num)
  exact ((hg.norm.pow 2).integrable_of_hasCompactSupport hc').integrableOn

/-- Uniform transfer of the exact strong residual. There is no assumed
physical/augmented DN equality and no suppressed determinant. -/
theorem chart_frame_mass_bound (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : X → X} (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (Q : X ≃ₗᵢ[ℝ] X) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f g : I → X → ℂ),
      (∀ i, Function.support (f i)⊆e '' K) →
      (∀ j, Continuous (g j)) → (∀ j, Function.support (g j)⊆K) →
      (∀ y∈e.source, ∀ s, (∑ i, frameMatrix Q i s*f i (e y))=g s y) →
      ∀ i, (∫ x in Ω, ‖f i x‖^2)≤C*∑ s, (∫ y in H, ‖g s y‖^2) := by
  obtain ⟨C,hC,hb⟩ := compact_jacobian_mass_bound (volume : Measure X) (H := H) hK hΦs
  refine ⟨C*3,mul_nonneg hC (by norm_num),fun f g hfs hgc hgs hfg i => ?_⟩
  have hscale : ∀ y∈e.source, f i (e y)=inverseMix Q g i y := by
    intro y hy
    rw [← frame_inverse Q (fun j => f j (e y)) i]
    simp only [inverseMix, hfg y hy]
  have hcont : Continuous (inverseMix Q g i) :=
    continuous_finsetSum _ (fun j _ => continuous_const.mul (hgc j))
  have hsup : Function.support (fun y => ‖inverseMix Q g i y‖^2)⊆K := by
    intro y hy
    apply inverseMix_support Q g hgs i
    intro hz
    exact hy (by simp [hz])
  have hcc : HasCompactSupport (fun y => ‖inverseMix Q g i y‖^2) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsup hK.isClosed)
  have hfsq : Function.support (fun x => ‖f i x‖^2)⊆e '' K := by
    intro x hx
    apply hfs i
    intro hz
    exact hx (by simp [hz])
  rw [compact_chart_integral (volume : Measure X) e he hs hΩ hH hhalf hΦ
    (fun x => ‖f i x‖^2) (fun y => ‖inverseMix Q g i y‖^2) hfsq hsup
    (fun y hy => congrArg (fun z : ℂ => ‖z‖^2) (hscale y hy))]
  apply (hb _ (hcont.norm.pow 2) hcc hsup (fun _ => sq_nonneg _)).trans
  have hgi (j : I) : IntegrableOn (fun y => ‖g j y‖^2) H :=
    norm_sq_integrableOn hK (hgc j) (hgs j) H
  have hsum : (∫ y in H, ‖inverseMix Q g i y‖^2)≤3*∑ j, (∫ y in H, ‖g j y‖^2) := by
    rw [← integral_finsetSum _ (fun j _ => hgi j),← integral_const_mul]
    exact integral_mono ((hcont.norm.pow 2).integrable_of_hasCompactSupport hcc).integrableOn
      ((integrable_finsetSum _ (fun j _ => hgi j)).const_mul 3) (inverseMix_bound Q g i)
  calc
    _ ≤ C*(3*∑ j, (∫ y in H, ‖g j y‖^2)) := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by ring

end ElasticityBoundaryChartMass

end
end
section
/-! Literal first derivatives of the compact physical trial and their exact
rotated chart expression. No trace reconstruction is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientTransfer
open ElasticityBoundaryPhysicalMass ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryRotation ElasticityBoundaryFrameInverse ElasticityBoundaryOperatorLocal
  ElasticityBoundaryChainRule ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix

lemma frame_forward (Q : X ≃ₗᵢ[ℝ] X) (v : I → ℂ) (s : I) :
    (∑ i, frameMatrix Q i s*(∑ j, frameMatrix Q i j*v j))=v s := by
  simpa only [frameMatrix_symm] using frame_inverse Q.symm v s

end ElasticityBoundaryGradientTransfer

end
end
section
/-! Uniform physical H1 control through the honest chart. Both the coordinate
Jacobian and the orthogonal output frame are accounted for. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryGradientMass
open ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartMass ElasticityBoundaryCompactMatrix ElasticityBoundaryForceSupport
  ElasticityBoundaryFrameOperator ElasticityBoundaryRotation ElasticityBoundaryChainRule
  ElasticityBoundaryStrongLayer ElasticityBoundaryChartOperator

lemma transferred_value (e : OpenPartialHomeomorph X X) {K : Set X}
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    {y : X} (hy : y∈e.source) (s : I) :
    (∑ i, frameMatrix Q i s*transferred e η Q u i (e y))=u s y.ofLp := by
  have he (i : I) := (transferred_germ e hη Q u hus (e.map_source hy)
    (Filter.EventuallyEq.refl (𝓝 (e y)) e.symm) i).eq_of_nhds
  simp only [ElasticityBoundaryFrameOperator.mix,e.left_inv hy] at he
  simp only [he,frame_forward]

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)

include he hK hs hΩ hH hhalf hηs hη hΦs hΦ in
lemma transferred_value_mass : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
    (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
    ∀ i, (∫ x in Ω, ‖transferred e η Q u i x‖^2)≤
      C*∑ s, (∫ y in H, ‖u s y.ofLp‖^2) := by
  obtain ⟨C,hC,hb⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  refine ⟨C,hC,fun u hu hus i => hb (transferred e η Q u) (fun s y => u s y.ofLp)
    (support_transferred e hηs Q u hus)
    (fun s => ((hu s).comp PiLp.contDiff_ofLp).continuous) hus ?_ i⟩
  exact fun y hy s => transferred_value e hη Q u hus hy s

end ElasticityBoundaryGradientMass

end
end
section
/-! Value mass and the exact identification of Euclidean and product Lebesgue
measure used by the physical boundary packets. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryPacketMass
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryProfile ElasticityBoundaryParameter ElasticityBoundaryParameterBounds
  ElasticityBoundaryOrderBound ElasticityBoundaryCutoffBound ElasticityBoundaryScaling
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryMVCalculus
  ElasticityBoundaryTensorSeries ElasticityBoundaryProfileBounds ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
lemma measurable_H : MeasurableSet H :=
  (isOpen_lt (continuous_const : Continuous (fun _ : X => (0:ℝ)))
    (EuclideanSpace.proj 2).continuous).measurableSet

lemma integral_ofLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Y → F) : (∫ x in H, f x.ofLp)=∫ y in halfspace, f y := by
  rw [← integral_indicator measurable_H,← integral_indicator measurable_halfspace]
  have hh (x : X) : H.indicator (fun x => f x.ofLp) x=halfspace.indicator f x.ofLp := rfl
  simp_rw [hh]
  exact (PiLp.volume_preserving_ofLp I).integral_comp
    (PiLp.homeomorph 2 (fun _ : I => ℝ)).measurableEmbedding _

end ElasticityBoundaryPacketMass

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
/-! Exact agreement of the variational trial energy with classical smooth
physical fields and their literal derivatives. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma realField_derivative (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) (i j : Fin 3) (x : X) :
    coordDeriv (realField w u) j x i=
      w (ElasticityBoundaryChainRule.dd (u i) (coordVector j) x) := by
  have h1 := (EuclideanSpace.proj i : V →L[ℝ] ℝ).hasFDerivAt.comp x
    (((smooth_realField w u hu).differentiable (by simp)) x).hasFDerivAt
  have h2 := w.hasFDerivAt.comp x (((hu i).differentiable (by simp)) x).hasFDerivAt
  have he : (EuclideanSpace.proj i : V →L[ℝ] ℝ) ∘ realField w u=w ∘ u i := rfl
  rw [he] at h1
  have hh := congrArg (fun A : X →L[ℝ] ℝ => A (coordVector j)) (h1.unique h2)
  exact hh

end Elasticity
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryResidualMass
open Elasticity ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule

lemma projected_force_mass_le {Ω : Set X} (w : ℂ →L[ℝ] ℝ) {F : X → ℂ}
    (hF : MemLp F 2 (volume.restrict Ω)) :
    (∫ x in Ω, ‖w (F x)‖^2)≤‖w‖^2*(∫ x in Ω, ‖F x‖^2) := by
  have hInt := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hwF : MemLp (fun x => w (F x)) 2 (volume.restrict Ω) := hF.continuousLinearMap_comp w
  rw [← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hwF.aestronglyMeasurable).mp hwF)
    (hInt.const_mul _)
  intro x
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (w.le_opNorm (F x)) 2

end ElasticityBoundaryResidualMass

end
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
section
open Set MeasureTheory
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma vector_toLp_norm_sq (f : X → V) (hf : MemLp f 2 (volume.restrict Ω)) :
    ‖hf.toLp f‖^2=∑ i, (∫ x in Ω, ‖f x i‖^2) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  have hi (i : Fin 3) : IntegrableOn (fun x => ‖f x i‖^2) Ω := by
    have hh := hf.continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx,real_inner_self_eq_norm_sq,PiLp.norm_sq_eq_of_L2]

lemma smoothTrial_norm_sq (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    ‖smoothTrial f hs hf hd‖^2=(∑ i, (∫ x in Ω, ‖f x i‖^2))+
      ∑ j, ∑ i, (∫ x in Ω, ‖coordDeriv f j x i‖^2) := by
  change ‖(smoothTrial f hs hf hd).val‖^2=_
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option]
  simp only [smoothTrial_value,smoothTrial_deriv,vector_toLp_norm_sq]

end Elasticity
namespace ElasticityBoundaryTrialMass
open Elasticity ElasticityBoundaryResidualMass ElasticityBoundaryChainRule

lemma projected_trial_mass {Ω : Set X} (w : ℂ →L[ℝ] ℝ)
    (u : I → X → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hm : ∀ j, MemLp (u j) 2 (volume.restrict Ω))
    (hdm : ∀ i j, MemLp (dd (u i) (coordVector j)) 2 (volume.restrict Ω))
    (hf : MemLp (realField w u) 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv (realField w u) j) 2 (volume.restrict Ω)) :
    ‖smoothTrial (realField w u) (smooth_realField w u hu) hf hdf‖^2≤
      ‖w‖^2*((∑ i, (∫ x in Ω, ‖u i x‖^2))+
        ∑ j, ∑ i, (∫ x in Ω, ‖dd (u i) (coordVector j) x‖^2)) := by
  rw [smoothTrial_norm_sq,mul_add]
  simp only [Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact projected_force_mass_le w (hm i)
  · apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    simp only [realField_derivative w u hu]
    exact projected_force_mass_le w (hdm i j)

end ElasticityBoundaryTrialMass

end
namespace ElasticityBoundaryPacket
/-! Actual smooth compact physical fields selected from the curved boundary
parametrix, on an arbitrary honest smooth domain. -/
open Set MeasureTheory Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryCutoffLayer ElasticityBoundaryCutoffParametrix ElasticityBoundaryPacketMass
  ElasticityBoundaryGradientMass ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryStrongLayer
  ElasticityBoundaryLocalParametrix ElasticityBoundaryMVNormal ElasticityBoundaryActualTower
  ElasticityBoundaryProfileBounds ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.field_compact (s : Setup Ω x) (q : Polynomial W) (δ : ℝ) (i : I) :
    HasCompactSupport (s.field q δ i) :=
  s.image_compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (s.field_support q δ i) s.image_compact.isClosed)

lemma Setup.field_value_mass (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
      (∫ z in Ω, ‖s.field q δ i z‖^2)≤C := by
  obtain ⟨A,hA,hbound⟩ := transferred_value_mass s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Φ_smooth s.Φ_germ
  choose B hB hBbound using cutoff_value_bound s.cutoff_smooth s.cutoff_compact q
  refine ⟨A*∑ j, B j,mul_nonneg hA (Finset.sum_nonneg (fun j _ => hB j)),fun δ hδ hδ1 i => ?_⟩
  apply (hbound _ (smooth_cutoffLayer s.cutoff_smooth q δ) (s.cutoff_layer_support q δ) i).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply Finset.sum_le_sum
  intro j _
  rw [integral_ofLp (fun y => ‖cutoffLayer s.cutoff q δ j y‖^2)]
  exact ((hBbound j δ hδ hδ1).2).trans (mul_le_of_le_one_right (hB j) (pow_le_one₀ hδ.le hδ1))

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket
/-! The physical quasimodes are genuine elements of the H1/trace construction
used by the real DN map, with uniform norm and arbitrary dual-residual decay. -/
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
open Elasticity ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryProjectedStress ElasticityBoundaryPhysicalStrong ElasticityBoundaryChainRule
  ElasticityBoundaryResidualMass ElasticityBoundaryTrialMass ElasticityBoundaryActualTower
  ElasticityBoundaryMVNormal ElasticityBoundaryChartOperator

variable {Ω : Set X} {x : X}

lemma coarse_sq_bound {A t r : ℝ} (hA : 0≤A) (ht : 0≤t) (hr : 0 ≤ r)
    (h : r^2≤A*t^2) : r≤(A+1)*t := by
  apply (sq_le_sq₀ hr (mul_nonneg (by positivity) ht)).mp
  have hC : A≤(A+1)^2 := by nlinarith [sq_nonneg A]
  calc
    _ ≤ A*t^2 := h
    _ ≤ (A+1)^2*t^2 := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
    _ = _ := (mul_pow _ _ _).symm

lemma Setup.trial_size_oai (s : Setup Ω x) (hΩ : MeasurableSet Ω) (q : Polynomial W) :
    ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤C := by
  obtain ⟨A,hA,hAb⟩ := s.field_value_mass hΩ q
  obtain ⟨B,hB,hBb⟩ := s.field_gradient_mass hΩ q
  let T := 3*A+9*B
  have hT : 0≤T := by dsimp [T]; positivity
  have hb (w : ℂ →L[ℝ] ℝ) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
      ‖projectedTrial (Ω := Ω) w (s.field q δ) (s.field_smooth q δ) s.image_compact (s.field_support q δ)‖≤
        (T+1)*‖w‖ := by
    apply coarse_sq_bound hT (norm_nonneg _) (norm_nonneg _)
    have hu := s.field_smooth q δ
    have hc := s.field_compact q δ
    have hm (i) := (hu i).continuous.memLp_of_hasCompactSupport (hc i) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    have hdm (i j) := (smooth_dd (hu i) (coordVector j)).continuous.memLp_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ _) (p := (2:ℝ≥0∞)) (μ := volume) |>.restrict Ω
    apply (projected_trial_mass w _ hu hm hdm _ _).trans
    have hreal : (∑ i, (∫ z in Ω, ‖s.field q δ i z‖^2))+
        (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤T := by
      have h1 := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => hAb δ hδ hδ1 i)
      have h2 := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset I)) =>
        Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => hBb δ hδ hδ1 i j))
      have h1' : (∑ i, (∫ z in Ω, ‖s.field q δ i z‖^2))≤3*A := by simpa using h1
      have h2' : (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤9*B := by
        have hh : (∑ j, ∑ i, (∫ z in Ω, ‖dd (s.field q δ i) (coordVector j) z‖^2))≤(3:ℝ)*(3*B) := by
          simpa [basis,coordVector] using h2
        exact hh.trans_eq (by ring)
      exact add_le_add h1' h2'
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hreal (sq_nonneg ‖w‖)
  refine ⟨(T+1)*(‖Complex.reCLM‖+‖Complex.imCLM‖),mul_nonneg (by positivity) (by positivity),
    fun δ hδ hδ1 => ?_⟩
  exact (add_le_add (hb Complex.reCLM δ hδ hδ1) (hb Complex.imCLM δ hδ hδ1)).trans_eq (mul_add _ _ _).symm

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.trial_size_oai := @OAI.ElasticityBoundaryPacket.Setup.trial_size_oai
