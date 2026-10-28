-- Prove2me | solution 1 for OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:48:56.364098+00:00
-- url     : https://prove2.me/submissions/73d04428-3f60-40c3-b502-76531741ee84

import Mathlib
import Definitions.Def_OAIQ6El004

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

lemma smooth_jac {ψ : E → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : E) (α : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) :=
  (contDiff_apply ℝ ℝ α).comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma fderiv_basis (f : Y → ℂ) (x v : Y) :
    fderiv ℝ f x v=∑ α, (v α:ℂ)*cp f α x := by
  have hv : v=∑ α : Fin 3, v α • Pi.single α (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    _ = fderiv ℝ f x (∑ α, v α • Pi.single α (1:ℝ)) := congrArg _ hv
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [map_smul]
      exact Complex.real_smul

lemma dd_comp {f : Y → ℂ} {ψ : E → Y} (hf : Differentiable ℝ f)
    (hψ : Differentiable ℝ ψ) (v x : E) :
    dd (fun x => f (ψ x)) v x=∑ α, (jac ψ v α x:ℂ)*cp f α (ψ x) := by
  change fderiv ℝ (f ∘ ψ) x v=_
  rw [fderiv_comp x (hf _) (hψ x), ContinuousLinearMap.comp_apply, fderiv_basis]
  rfl

lemma dd_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i∈s, Differentiable ℝ (f i)) (v x : E) :
    dd (fun z => ∑ i∈s, f i z) v x=∑ i∈s, dd (f i) v x := by
  rw [dd, fderiv_fun_sum (fun i hi => hf i hi x), sum_apply]
  rfl

lemma dd_mul {f g : E → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v x : E) : dd (fun z => f z*g z) v x=dd f v x*g x+f x*dd g v x := by
  rw [dd, fderiv_fun_mul (hf x) (hg x)]
  simp only [add_apply, smul_apply, smul_eq_mul, dd]
  ring

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
section
/-! Exact constant-frame transformation of the strong differential operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryFrameOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dd_mix (Q : I → I → ℂ) (u : I → E → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) (v x : E) :
    dd (mix Q u i) v x=∑ j, Q i j*dd (u j) v x := by
  change dd (fun z => ∑ j, Q i j*u j z) v x=_
  rw [dd_sum Finset.univ (fun j z => Q i j*u j z)
    (fun j _ => (contDiff_const.mul (hu j)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dd_mul (differentiable_const _) ((hu j).differentiable (by simp))]
  have hz : dd (fun _ : E => Q i j) v x=0 := by simp [dd]
  rw [hz,zero_mul,zero_add]

end ElasticityBoundaryFrameOperator

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

lemma dd_germ {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v =ᶠ[𝓝 x] dd g v := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun A : E →L[ℝ] ℂ => A v) hy

lemma dd_germ_eq {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    dd f v x=dd g v x := (dd_germ h v).eq_of_nhds

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
section
/-! Cut off actual boundary fields. The complete product-rule residual is
retained; its derivatives are flat at the concentration point. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryCutoffLayer
open MvPolynomial ElasticityBoundaryMVCalculus ElasticityBoundaryMVNormal
  ElasticityBoundaryParameter ElasticityBoundaryParameterBounds ElasticityBoundaryTensorSeries
  ElasticityBoundaryActualTower ElasticityBoundarySmoothOperator ElasticityBoundaryProfile
  ElasticityBoundaryProfileBounds ElasticityBoundaryScaling ElasticityBoundaryLayerOperator
  ElasticityBoundaryWeights ElasticityBoundaryStrongLayer ElasticityBoundaryOrderBound
  ElasticityBoundaryCutoffBound

lemma smooth_dpart {f : Y → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (dpart f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end ElasticityBoundaryCutoffLayer

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
/-! Uniform compactly supported matrix-multiplier mass estimates, for the
true coordinate Jacobian acting on first derivatives of boundary layers. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryCompactMatrix
open ElasticityBoundaryChartMass ElasticityBoundaryFrameInverse

lemma compact_array_bound {K : Set X} (hK : IsCompact K) (a : I → I → X → ℂ)
    (ha : ∀ r j, Continuous (a r j)) :
    ∃ B : ℝ, 0≤B ∧ ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B := by
  have hc : Continuous (fun y => ∑ r, ∑ j, ‖a r j y‖^2) :=
    continuous_finsetSum _ (fun r _ => continuous_finsetSum _ (fun j _ => (ha r j).norm.pow 2))
  obtain ⟨B,hB⟩ := (hK.image hc).bddAbove
  refine ⟨max B 0,le_max_right _ _,fun y hy r j => ?_⟩
  have h1 : ‖a r j y‖^2≤∑ k, ‖a r k y‖^2 :=
    Finset.single_le_sum (f := fun k => ‖a r k y‖^2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ k, ‖a r k y‖^2)≤∑ s, ∑ k, ‖a s k y‖^2 :=
    Finset.single_le_sum (f := fun s => ∑ k, ‖a s k y‖^2) (fun s _ => Finset.sum_nonneg (fun k _ => sq_nonneg _)) (Finset.mem_univ r)
  exact h1.trans (h2.trans ((hB (mem_image_of_mem _ hy)).trans (le_max_left _ _)))

lemma row_support (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) {K : Set X}
    (hv : ∀ j, Function.support (v j)⊆K) : Function.support (row a r v)⊆K := by
  intro y hy
  by_contra hn
  apply hy
  apply Finset.sum_eq_zero
  intro j _
  have hz : v j y=0 := Function.notMem_support.mp (fun h => hn (hv j h))
  rw [hz,mul_zero]

lemma continuous_row (a : I → I → X → ℂ) (ha : ∀ r j, Continuous (a r j))
    (r : I) (v : I → X → ℂ) (hv : ∀ j, Continuous (v j)) : Continuous (row a r v) :=
  continuous_finsetSum _ (fun j _ => (ha r j).mul (hv j))

lemma row_bound (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) {K : Set X}
    (hv : ∀ j, Function.support (v j)⊆K) {B : ℝ}
    (hb : ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B) (y : X) :
    ‖row a r v y‖^2≤3*B*∑ j, ‖v j y‖^2 := by
  by_cases hy : y∈K
  · apply (norm_sq_sum_three _).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_right (hb y hy r j) (sq_nonneg _)
  · have hz (j : I) : v j y=0 := Function.notMem_support.mp (fun h => hy (hv j h))
    simp only [row,hz,mul_zero,Finset.sum_const_zero,norm_zero,zero_pow (by omega : 2≠0),le_refl]

lemma row_mass_bound {K H : Set X} (hK : IsCompact K) (a : I → I → X → ℂ)
    (ha : ∀ r j, Continuous (a r j)) {B : ℝ}
    (hb : ∀ y∈K, ∀ r j, ‖a r j y‖^2≤B)
    (r : I) (v : I → X → ℂ) (hvc : ∀ j, Continuous (v j))
    (hvs : ∀ j, Function.support (v j)⊆K) :
    (∫ y in H, ‖row a r v y‖^2)≤3*B*∑ j, (∫ y in H, ‖v j y‖^2) := by
  have hi (j : I) := norm_sq_integrableOn hK (hvc j) (hvs j) H
  rw [← integral_finsetSum _ (fun j _ => hi j),← integral_const_mul]
  exact integral_mono (norm_sq_integrableOn hK (continuous_row a ha r v hvc) (row_support a r v hvs) H)
    ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _) (row_bound a r v hvs hb)

end ElasticityBoundaryCompactMatrix

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

lemma dd_support {f : X → ℂ} {K : Set X} (hK : IsClosed K)
    (hf : Function.support f⊆K) (v : X) : Function.support (dd f v)⊆K := by
  intro x hx
  apply closure_minimal hf hK
  exact tsupport_fderiv_apply_subset ℝ v (subset_tsupport _ hx)

lemma dpart_support_lifted {f : Y → ℂ} {K : Set X} (hK : IsClosed K)
    (hf : Function.support (fun z : X => f z.ofLp)⊆K) (α : I) :
    Function.support (fun z : X => dpart f α z.ofLp)⊆K := by
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} :=
    hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hs : Function.support f⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro y hy
    exact hf hy
  intro x hx
  exact closure_minimal hs hcl (tsupport_fderiv_apply_subset ℝ (Pi.single α 1) (subset_tsupport _ hx))

lemma smooth_jacobian {Φ Ψ : X → X} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (d α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jacobian Φ Ψ d α) :=
  Complex.ofRealCLM.contDiff.comp ((ElasticityBoundaryChainRule.smooth_jac
    (PiLp.contDiff_ofLp.comp hΨ) (basis d) α).comp hΦ)

lemma gradient_at_support (e : OpenPartialHomeomorph X X) {K : Set X} (hs : K⊆e.source)
    {η : X → ℝ} (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    {y : X} (hy : y∈K) (hΦy : Φ y=e y) (hΨy : Ψ =ᶠ[𝓝 (e y)] e.symm) (s d : I) :
    (∑ i, frameMatrix Q i s*dd (transferred e η Q u i) (basis d) (e y))=
      row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y := by
  have he (i : I) : dd (transferred e η Q u i) (basis d) (e y)=
      ∑ j, frameMatrix Q i j*row (jacobian Φ Ψ) d (fun α z => dpart (u j) α z.ofLp) y := by
    rw [dd_germ_eq (transferred_germ e hη Q u hus (e.map_source (hs hy)) hΨy i)]
    have hum (j : I) : ContDiff ℝ (⊤ : ℕ∞) (fun z => u j (Ψ z).ofLp) :=
      (hu j).comp (PiLp.contDiff_ofLp.comp hΨ)
    rw [dd_mix (frameMatrix Q) _ hum]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun z => frameMatrix Q i j*z)
    have hps : Differentiable ℝ (fun z => (Ψ z).ofLp) :=
      (PiLp.contDiff_ofLp.comp hΨ).differentiable (by simp)
    rw [dd_comp ((hu j).differentiable (by simp)) hps]
    have hid : (Ψ (e y)).ofLp=y.ofLp := by rw [hΨy.eq_of_nhds,e.left_inv (hs hy)]
    simp only [hid,row,jacobian,hΦy]
    rfl
  simp only [he,frame_forward]

lemma gradient_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {y : X} (hy : y∈e.source) (s d : I) :
    (∑ i, frameMatrix Q i s*dd (transferred e η Q u i) (basis d) (e y))=
      row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y := by
  by_cases hyK : y∈K
  · exact gradient_at_support e hs hη Q u hu hus Φ Ψ hΨ hyK (hΦ y hyK)
      (hΨe _ (mem_image_of_mem e hyK)) s d
  · have hn : e y∉e '' K := by
      rintro ⟨z,hz,he⟩
      exact hyK (e.injOn (hs hz) hy he ▸ hz)
    have hz (i : I) : dd (transferred e η Q u i) (basis d) (e y)=0 :=
      Function.notMem_support.mp (fun h => hn (dd_support (compact_image e hK hs).isClosed
        (support_transferred e hηs Q u hus i) (basis d) h))
    have hr : row (jacobian Φ Ψ) d (fun α z => dpart (u s) α z.ofLp) y=0 :=
      Function.notMem_support.mp (fun h => hyK (row_support _ _ _
        (fun α => dpart_support_lifted hK.isClosed (hus s) α) h))
    simp only [hz,mul_zero,Finset.sum_const_zero,hr]

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

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)

include he hK hs hΩ hH hhalf hηs hη hΦs hΨs hΦ hΨ in
lemma transferred_gradient_mass_oai : ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
    (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
    ∀ i d, (∫ x in Ω, ‖dd (transferred e η Q u i) (basis d) x‖^2)≤
      C*∑ s, ∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2) := by
  obtain ⟨C,hC,hb⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  have hJ (d α : I) := (smooth_jacobian hΦs hΨs d α).continuous
  obtain ⟨B,hB,hbB⟩ := compact_array_bound hK (jacobian Φ Ψ) hJ
  refine ⟨C*(3*B),mul_nonneg hC (mul_nonneg (by norm_num) hB),fun u hu hus i d => ?_⟩
  have hds (s α : I) := dpart_support_lifted hK.isClosed (hus s) α
  have hdc (s α : I) : Continuous (fun y : X => dpart (u s) α y.ofLp) :=
    ((ElasticityBoundaryCutoffLayer.smooth_dpart (hu s) α).comp PiLp.contDiff_ofLp).continuous
  have h1 := hb (fun i => dd (transferred e η Q u i) (basis d))
    (fun s => row (jacobian Φ Ψ) d (fun α y => dpart (u s) α y.ofLp))
    (fun i => dd_support (compact_image e hK hs).isClosed (support_transferred e hηs Q u hus i) _)
    (fun s => continuous_row _ hJ _ _ (hdc s)) (fun s => row_support _ _ _ (hds s))
    (fun y hy s => gradient_all e hK hs hηs hη Q u hu hus Φ Ψ hΨs
      (fun y hy => (hΦ y hy).eq_of_nhds) hΨ hy s d) i
  apply h1.trans
  calc
    _ ≤ C*∑ s, (3*B*∑ α, (∫ y in H, ‖dpart (u s) α y.ofLp‖^2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ =>
        row_mass_bound hK _ hJ hbB d _ (hdc s) (hds s))) hC
    _ = _ := by rw [← Finset.mul_sum]; ring

end ElasticityBoundaryGradientMass

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass_oai := @OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass_oai
