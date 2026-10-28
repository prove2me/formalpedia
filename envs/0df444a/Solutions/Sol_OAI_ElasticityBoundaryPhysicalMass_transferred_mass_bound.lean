-- Prove2me | solution 1 for OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:11:36.42431+00:00
-- url     : https://prove2.me/submissions/880d4799-3b2e-49f3-8628-f97c33c656e9

import Mathlib
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryForceSupport_transferred_force_all

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
/-! The boundary-coordinate differential operator is obtained from literal
physical elasticity by the chain rule and a fixed Euclidean rotation. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChartOperator
open ElasticityBoundaryChainRule ElasticityBoundaryPullback ElasticityBoundaryRotation
  ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundarySmoothOperator ElasticityBoundaryLayerOperator ElasticityBoundaryStrongLayer

lemma smooth_jac {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) := by
  exact contDiff_apply ℝ ℝ α |>.comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma smooth_hess {ψ : X → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v w : X) (α : I) :
    ContDiff ℝ (⊤ : ℕ∞) (hess ψ v w α) := by
  exact ((smooth_jac hψ w α).fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_chartPrincipal (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s α r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartPrincipal Q Φ ψ l m s α r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.sum; intro k _
  apply ContDiff.sum; intro v _
  apply ContDiff.mul
  · apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis k) α)
  · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

lemma smooth_chartLower (Q : X ≃ₗᵢ[ℝ] X) {Φ : Y → X} {ψ : X → Y}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (s r β : I) : ContDiff ℝ (⊤ : ℕ∞) (chartLower Q Φ ψ l m s r β) := by
  apply ContDiff.comp _ hΦ
  apply ContDiff.add
  · apply ContDiff.sum; intro k _
    apply ContDiff.sum; intro v _
    apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold coeff elasticityTensor
      exact (hl.mul contDiff_const |>.mul contDiff_const).add (hm.mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_hess hψ (basis k) (basis v) β)
  · apply ContDiff.sum; intro v _
    apply ContDiff.mul
    · apply ContDiff.sum; intro i _
      apply ContDiff.sum; intro j _
      apply ContDiff.mul _ contDiff_const
      apply ContDiff.mul contDiff_const
      unfold lower
      exact (((smooth_dd hl _).mul contDiff_const).add
        ((smooth_dd hm _).mul contDiff_const)).add ((smooth_dd hm _).mul contDiff_const)
    · exact Complex.ofRealCLM.contDiff.comp (smooth_jac hψ (basis v) β)

end ElasticityBoundaryChartOperator

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

lemma directional_germ_eq (e : I → E) (a : Tensor E) (b : Lower E)
    {u v : I → E → ℂ} {x : E} (h : ∀ j, u j =ᶠ[𝓝 x] v j) (i : I) :
    directional e a b u i x=directional e a b v i x := by
  unfold directional
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (dd_germ (h j) (e l)) (e k)]
  · apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro l _
    rw [dd_germ_eq (h j) (e l)]

lemma directional_zero (e : I → E) (a : Tensor E) (b : Lower E) (i : I) (x : E) :
    directional e a b (fun _ _ => 0) i x=0 := by
  have hz (v : E) : dd (fun _ : E => (0:ℂ)) v=(fun _ => 0) := by
    funext y
    simp [dd]
  simp only [directional,hz,mul_zero,Finset.sum_const_zero,add_zero]

lemma directional_support (e : I → E) (a : Tensor E) (b : Lower E)
    {K : Set E} (hK : IsClosed K) (u : I → E → ℂ)
    (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (directional e a b u i)⊆K := by
  intro x hx
  by_contra hn
  have hg (j : I) : u j =ᶠ[𝓝 x] (fun _ => 0) := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    exact fun h => hn (closure_minimal (hu j) hK h)
  have heq := directional_germ_eq e a b hg i
  rw [directional_zero] at heq
  exact hx heq

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
section
/-! Local boundary layers for arbitrary smooth coefficients. Auxiliary compact
coefficient extensions are removed on the actual trial support; thus no
artificial compactness or global geometry assumption is imposed on a chart. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryLocalParametrix
open ElasticityBoundaryCutoffParametrix ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundarySmoothOperator
  ElasticityBoundaryMVNormal ElasticityBoundaryActualTower ElasticityBoundaryLayerOperator ElasticityBoundaryProfile ElasticityBoundaryOperatorLocal
  ElasticityBoundary ElasticityBoundaryProfileBounds

lemma strong_support (a : SmoothTensor) (b : SmoothLower) {K : Set Y} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (strong a b u i)⊆K :=
  directional_support (fun j => Pi.single j 1) a b hK u hu i

end ElasticityBoundaryLocalParametrix

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
/-! Support-complete physical force identification. The coordinate expression
is valid on the entire chart source, including all zero regions, and the
physical force is supported in the genuine compact image. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryForceSupport
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryOperatorLocal
  ElasticityBoundaryLocalParametrix ElasticityBoundaryStrongLayer
  ElasticityBoundaryChartOperator ElasticityBoundaryFrameOperator
  ElasticityBoundaryFrameInverse ElasticityBoundaryRotation

lemma force_support (l m : X → ℂ) (u : I → X → ℂ) {K : Set X}
    (hK : IsClosed K) (hu : ∀ j, Function.support (u j)⊆K) (i : I) :
    Function.support (force l m u i)⊆K :=
  directional_support basis _ _ hK u hu i

lemma transferred_force_support (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hη : tsupport η⊆e.target)
    (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (l m : X → ℂ) (i : I) :
    Function.support (force l m (transferred e η Q u) i)⊆e '' K :=
  force_support l m _ (compact_image e hK hs).isClosed (support_transferred e hη Q u hu) i

lemma strong_support_lifted (a : ElasticityBoundarySmoothOperator.SmoothTensor)
    (b : ElasticityBoundarySmoothOperator.SmoothLower) {K : Set X} (hK : IsClosed K)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) (i : I) :
    Function.support (fun z : X => strong a b u i z.ofLp)⊆K := by
  intro x hx
  have hcl : IsClosed {y : Y | WithLp.toLp 2 y∈K} := hK.preimage (PiLp.continuous_toLp 2 (fun _ : I => ℝ))
  have hh : ∀ j, Function.support (u j)⊆{y : Y | WithLp.toLp 2 y∈K} := by
    intro j y hy
    exact hu j hy
  exact strong_support a b hcl u hh i hx

end ElasticityBoundaryForceSupport

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
/-! The honest physical strong residual has the same quantitative L2 scale as
its fully curved coordinate expression. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPhysicalMass
open ElasticityBoundary ElasticityBoundaryPhysicalTransfer ElasticityBoundaryForceSupport
  ElasticityBoundaryChartMass ElasticityBoundaryChartOperator ElasticityBoundaryRotation
  ElasticityBoundarySmoothOperator ElasticityBoundaryStrongLayer ElasticityBoundaryCutoffLayer
  ElasticityBoundaryFrameOperator

lemma smooth_strong (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    (u : I → Y → ℂ) (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (i : I) :
    ContDiff ℝ (⊤ : ℕ∞) (strong a b u i) := by
  exact (ContDiff.sum (fun α _ => ContDiff.sum (fun j _ => ContDiff.sum (fun β _ =>
    (ha i α j β).mul (smooth_dpart (smooth_dpart (hu j) β) α))))).add
    (ContDiff.sum (fun j _ => ContDiff.sum (fun β _ => (hb i j β).mul (smooth_dpart (hu j) β))))

/-- The multiplicative constant depends only on the fixed chart, not on the
field, its frequency, or the chosen finite parametrix order. -/
theorem transferred_mass_bound_oai (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set X} (hK : IsCompact K) (hs : K⊆e.source)
    (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {η : X → ℝ} (hηs : tsupport η⊆e.target) (hη : ∀ z∈e '' K, η z=1)
    (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨs : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e) (hΨ : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    :
    ∃ C : ℝ, 0≤C ∧ ∀ (u : I → Y → ℂ),
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) →
      (∀ j, Function.support (fun z : X => u j z.ofLp)⊆K) →
      ∀ i, (∫ x in Ω, ‖force l m (transferred e η Q u) i x‖^2)≤
        C*∑ s, (∫ y in H, ‖strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp‖^2) := by
  have ha := smooth_chartPrincipal Q (hΦs.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp hΨs) hl hm
  have hb := smooth_chartLower Q (hΦs.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp hΨs) hl hm
  obtain ⟨C,hC,hbound⟩ := chart_frame_mass_bound e he hK hs hΩ hH hhalf hΦs hΦ Q
  refine ⟨C,hC,fun u hu hus i => ?_⟩
  apply hbound (force l m (transferred e η Q u))
    (fun s y => strong (principal Q Φ Ψ l m) (lower Q Φ Ψ l m) u s y.ofLp)
  · exact transferred_force_support e hK hs hηs Q u hus l m
  · exact fun s => ((smooth_strong _ _ ha hb u hu s).comp PiLp.contDiff_ofLp).continuous
  · exact strong_support_lifted _ _ hK.isClosed u hus
  · intro y hy s
    exact transferred_force_all e hK hs hηs hη Q u hus hu Φ Ψ hΨs
      (fun x hx => (hΦ x hx).eq_of_nhds) hΨ hl hm y hy s

end ElasticityBoundaryPhysicalMass

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound_oai := @OAI.ElasticityBoundaryPhysicalMass.transferred_mass_bound_oai
