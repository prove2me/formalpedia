-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.energy_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:08:54.06099+00:00
-- url     : https://prove2.me/submissions/30029bd8-e43a-4a9b-816d-5286b7ad362d

import Mathlib
import Definitions.Def_ElasticityUniqueness
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

end ElasticityBoundaryFrameInverse

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

lemma row_support (a : I → I → X → ℂ) (r : I) (v : I → X → ℂ) {K : Set X}
    (hv : ∀ j, Function.support (v j)⊆K) : Function.support (row a r v)⊆K := by
  intro y hy
  by_contra hn
  apply hy
  apply Finset.sum_eq_zero
  intro j _
  have hz : v j y=0 := Function.notMem_support.mp (fun h => hn (hv j h))
  rw [hz,mul_zero]

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
-- module Solutions.OAIQ6_Elast.Elasticity_Restriction
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
lemma energy_eq_ambient (lam mu : X → ℝ) (u v : H1 Ω) :
    energy Ω lam mu u v=ambientEnergy lam mu u.val v.val := rfl
end Elasticity

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

lemma smoothTrial_gradient_ae (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    gradient (h1Equiv Ω (smoothTrial f hs hf hd)).val =ᵐ[volume.restrict Ω]
      (fun x j => coordDeriv f j x) := by
  have hh := Filter.eventually_all.mpr (fun j => (hd j).coeFn_toLp)
  filter_upwards [hh] with x hx
  exact funext hx

lemma smoothTrial_energy (l m : X → ℝ) (f g : X → V)
    (hsf : ContDiff ℝ (⊤ : ℕ∞) f) (hsg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hdf : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω))
    (hdg : ∀ j, MemLp (coordDeriv g j) 2 (volume.restrict Ω)) :
    energy Ω l m (h1Equiv Ω (smoothTrial f hsf hf hdf)) (h1Equiv Ω (smoothTrial g hsg hg hdg))=
      ∫ x in Ω, elasticDensity (l x) (m x) (fun j => coordDeriv f j x) (fun j => coordDeriv g j x) := by
  rw [energy_eq_ambient]
  apply integral_congr_ae
  filter_upwards [smoothTrial_gradient_ae f hsf hf hdf,smoothTrial_gradient_ae g hsg hg hdg] with x h1 h2
  exact congrArg₂ (elasticDensity (l x) (m x)) h1 h2

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
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
namespace Elasticity
/-! Complex geometric displacements as genuine pairs of real H1 trials. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

lemma classicalDensity_integrable {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (P Q : X → Fin 3 → V)
    (hP : ∀ j, MemLp (fun x => P x j) 2 (volume.restrict Ω))
    (hQ : ∀ j, MemLp (fun x => Q x j) 2 (volume.restrict Ω)) :
    IntegrableOn (fun x => elasticDensity (l x) (m x) (P x) (Q x)) Ω := by
  have hp (i j : Fin 3) : MemLp (fun x => P x j i) 2 (volume.restrict Ω) := (hP j).continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
  have hq (i j : Fin 3) : MemLp (fun x => Q x j i) 2 (volume.restrict Ω) := (hQ j).continuousLinearMap_comp (EuclideanSpace.proj i : V →L[ℝ] ℝ)
  have hdP : MemLp (fun x => ∑ i, P x i i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => hp i i)
  have hdQ : MemLp (fun x => ∑ i, Q x i i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => hq i i)
  have hsP (i j : Fin 3) : MemLp (fun x => (P x j i+P x i j)/2) 2 (volume.restrict Ω) := by
    simpa only [div_eq_mul_inv,Pi.add_apply] using ((hp i j).add (hp j i)).mul_const (2:ℝ)⁻¹
  have hsQ (i j : Fin 3) : MemLp (fun x => (Q x j i+Q x i j)/2) 2 (volume.restrict Ω) := by
    simpa only [div_eq_mul_inv,Pi.add_apply] using ((hq i j).add (hq j i)).mul_const (2:ℝ)⁻¹
  have hL := (hl.mul_memLp_fun hdP).integrable_mul hdQ
  have hS (i j) := (hm.mul_memLp_fun (hsP i j)).integrable_mul (hsQ i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hS i j))
  apply (hL.add (hsum.const_mul 2)).congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [elasticDensity,Pi.mul_apply,Pi.add_apply,Finset.mul_sum,mul_assoc])

lemma realMatrix_gradient (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (x : X) :
    realMatrix w (fieldGradient u x)=(fun j => coordDeriv (realField w u) j x) := by
  funext j
  ext i
  exact (realField_derivative w u hu i j x).symm

lemma complexFieldTrial_energy {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (u v : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hus : ∀ j, Function.support (u j)⊆K) (hvs : ∀ j, Function.support (v j)⊆L) :
    complexTrialEnergy (Ω := Ω) l m (complexFieldTrial u hu hK hus) (complexFieldTrial v hv hL hvs)=
      ∫ x in Ω, complexDensity (l x) (m x) (fieldGradient u x) (fieldGradient v x) := by
  have hi (w z : ℂ →L[ℝ] ℝ) : Integrable (fun x =>
      elasticDensity (l x) (m x) (realMatrix w (fieldGradient u x))
        (realMatrix z (fieldGradient v x))) (volume.restrict Ω) := by
    simp only [realMatrix_gradient w u hu,realMatrix_gradient z v hv]
    exact classicalDensity_integrable hl hm _ _
      (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2
      (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).2
  have he (w z : ℂ →L[ℝ] ℝ) := smoothTrial_energy (Ω := Ω) l m (realField w u) (realField z v)
    (smooth_realField w u hu) (smooth_realField z v hv)
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).1
    (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).1
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2
    (smooth_compact_memLp (smooth_realField z v hv) (compact_realField z v hL hvs)).2
  simp only [complexTrialEnergy,complexFieldTrial,projectedTrial,he,complexDensity]
  simp only [← realMatrix_gradient _ u hu,← realMatrix_gradient _ v hv]
  rw [integral_add ((hi _ _).ofReal.add (hi _ _).ofReal)
    (((hi _ _).ofReal.sub (hi _ _).ofReal).const_mul _),
    integral_add (hi _ _).ofReal (hi _ _).ofReal,integral_const_mul,
    integral_sub (hi _ _).ofReal (hi _ _).ofReal]
  simp only [integral_complex_ofReal]

end Elasticity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryTensorPull
/-! Finite sesquilinear tensor change of coordinates. The real change of
variables assumption is explicit and is proved for the actual Jacobian. -/
open scoped BigOperators

lemma sum_four_exchange {ι κ σ τ A : Type*} [Fintype ι] [Fintype κ]
    [Fintype σ] [Fintype τ] [AddCommMonoid A] (f : ι → κ → σ → τ → A) :
    (∑ i, ∑ j, ∑ r, ∑ s, f i j r s)=∑ r, ∑ s, ∑ i, ∑ j, f i j r s := by
  calc
    _ = ∑ i, ∑ r, ∑ j, ∑ s, f i j r s := by
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ j, ∑ s, f i j r s := Finset.sum_comm
    _ = ∑ r, ∑ i, ∑ s, ∑ j, f i j r s := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
    _ = _ := by apply Finset.sum_congr rfl; intro r _; exact Finset.sum_comm

lemma sesqui_pull {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ι → ℂ) (R : ι → κ → ℂ) (hR : ∀ i j, star (R i j)=R i j)
    (u v : κ → ℂ) :
    (∑ i, ∑ j, a i j*(∑ r, R i r*u r)*star (∑ s, R j s*v s))=
      ∑ r, ∑ s, (∑ i, ∑ j, R i r*a i j*R j s)*u r*star (v s) := by
  simp only [star_sum,star_mul,hR,Finset.mul_sum,Finset.sum_mul]
  rw [sum_four_exchange,Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

end ElasticityBoundaryTensorPull
namespace Elasticity
/-! The complex physical variational density is exactly the Hermitian
contraction of the literal isotropic elasticity tensor. -/
open scoped BigOperators
open ElasticityBoundaryLayerOperator

lemma complexDensity_sesqui (l m : ℝ) (P Q : CMatrix) :
    complexDensity l m P Q=sesquiDensity (l:ℂ) (m:ℂ) P Q := by
  apply Complex.ext <;>
    simp only [complexDensity,realMatrix,elasticDensity,sesquiDensity,
      Fin.sum_univ_three,PiLp.toLp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.div_ofNat_re,Complex.div_ofNat_im] <;> ring

lemma tensorDensity_isotropic (l m : ℂ) (P Q : CMatrix) :
    tensorDensity (elasticityTensor l m) P Q=sesquiDensity l m P Q := by
  unfold tensorDensity elasticityTensor
  simp only [add_mul,mul_add,Finset.sum_add_distrib,mul_ite,ite_mul,mul_one,mul_zero,
    zero_mul,Finset.sum_ite_irrel,Fintype.sum_ite_eq,Finset.sum_const_zero]
  simp only [sesquiDensity,Fin.sum_univ_three,star_add]
  ring

lemma complexDensity_tensor (l m : ℝ) (P Q : CMatrix) :
    complexDensity l m P Q=tensorDensity (elasticityTensor (l:ℂ) (m:ℂ)) P Q := by
  rw [complexDensity_sesqui,tensorDensity_isotropic]

end Elasticity
namespace ElasticityBoundaryDensityPull
open Set Filter
open scoped Topology BigOperators

section
/-! The exact physical elastic density under the honest boundary chart. -/
open Elasticity ElasticityBoundaryTensorPull ElasticityBoundaryRotation
  ElasticityBoundaryGradientTransfer ElasticityBoundaryFrameInverse
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryPhysicalTransfer ElasticityBoundaryPullback ElasticityBoundaryFrameOperator
  ElasticityBoundaryPhysicalStrong ElasticityBoundaryStrongLayer ElasticityBoundaryCompactMatrix
  ElasticityBoundaryLayerOperator

lemma tensor_pull (Q J : I → I → ℂ) (hQ : ∀ i j, star (Q i j)=Q i j)
    (hJ : ∀ i j, star (J i j)=J i j) (a : I → I → I → I → ℂ) (U V : CMatrix) :
    tensorDensity a (pullMatrix Q J U) (pullMatrix Q J V)=tensorDensity (pullTensor Q J a) U V := by
  have hh := sesqui_pull (fun p q : I×I => a p.1 p.2 q.1 q.2)
    (fun p q : I×I => Q p.1 q.1*J p.2 q.2)
    (fun p q => by rw [star_mul,hQ,hJ]; ring) (fun p : I×I => U p.1 p.2) (fun p : I×I => V p.1 p.2)
  simpa only [Fintype.sum_prod_type,tensorDensity,pullMatrix,pullTensor] using hh

lemma principal_pullTensor (Q : X ≃ₗᵢ[ℝ] X) (Φ Ψ : X → X) (l m : X → ℂ)
    (y : X) (s α r β : I) :
    ElasticityBoundaryPhysicalMass.principal Q Φ Ψ l m s α r β y.ofLp=
      pullTensor (frameMatrix Q) (fun k a => jacobian Φ Ψ k a y)
        (elasticityTensor (l (Φ y)) (m (Φ y))) s α r β := by
  unfold ElasticityBoundaryPhysicalMass.principal chartPrincipal principalPull mixedTensor coeff pullTensor
  simp only [WithLp.toLp_ofLp,Finset.sum_mul]
  rw [sum_four_exchange]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro v _
  simp only [jacobian]
  ring

lemma gradient_pullMatrix (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    {y : X} (hy : y∈e.source) :
    fieldGradient (transferred e η Q u) (e y)=
      pullMatrix (frameMatrix Q) (fun k a => jacobian Φ Ψ k a y) (fun i α => dpart (u i) α y.ofLp) := by
  funext i d
  have hh := frame_inverse Q (fun j => dd (transferred e η Q u j) (basis d) (e y)) i
  simp only [gradient_all e hK hs hηs hη Q u hu hus Φ Ψ hΨ hΦ hΨe hy] at hh
  change dd (transferred e η Q u i) (basis d) (e y) = _
  rw [← hh]
  simp only [row,pullMatrix,Finset.mul_sum,mul_assoc]

lemma density_chart (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u v : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hvs : ∀ j, Function.support (fun z : X => v j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    (l m : X → ℝ) {y : X} (hy : y∈K) :
    complexDensity (l (e y)) (m (e y)) (fieldGradient (transferred e η Q u) (e y))
      (fieldGradient (transferred e η Q v) (e y))=
      tensorDensity (fun i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
        (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
        (fun i α => dpart (u i) α y.ofLp) (fun i α => dpart (v i) α y.ofLp) := by
  rw [complexDensity_tensor,gradient_pullMatrix e hK hs hηs hη Q u hu hus Φ Ψ hΨ hΦ hΨe (hs hy),
    gradient_pullMatrix e hK hs hηs hη Q v hv hvs Φ Ψ hΨ hΦ hΨe (hs hy)]
  have hR (i j : I) : star (frameMatrix Q i j)=frameMatrix Q i j := Complex.conj_ofReal _
  have hJ (i j : I) : star (jacobian Φ Ψ i j y)=jacobian Φ Ψ i j y := Complex.conj_ofReal _
  rw [tensor_pull _ _ hR hJ]
  simp only [principal_pullTensor,hΦ y hy]

end
/-! The exact tensor-density identity extends over the whole honest chart;
all derivatives vanish outside the actual compact packet support. -/
open Elasticity ElasticityBoundaryGradientTransfer ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryChainRule ElasticityBoundaryChartOperator ElasticityBoundaryPhysicalMass
  ElasticityBoundaryStrongLayer ElasticityBoundaryForceSupport

lemma tensor_zero_left (a : I → I → I → I → ℂ) (V : CMatrix) :
    tensorDensity a 0 V=0 := by simp [tensorDensity]

lemma physical_density_support {K : Set X} (hK : IsClosed K) (l m : X → ℝ)
    (u v : I → X → ℂ) (hus : ∀ i, Function.support (u i)⊆K) :
    Function.support (fun z => complexDensity (l z) (m z) (fieldGradient u z) (fieldGradient v z))⊆K := by
  intro z hz
  by_contra hn
  have ht : fieldGradient u z=0 := by
    funext i d
    exact Function.notMem_support.mp (fun h => hn (dd_support hK (hus i) (basis d) h))
  exact hz (by dsimp only; rw [complexDensity_tensor,ht,tensor_zero_left])

lemma chart_density_support {K : Set X} (hK : IsClosed K)
    (a : X → I → I → I → I → ℂ) (u v : I → Y → ℂ)
    (hus : ∀ i, Function.support (fun z : X => u i z.ofLp)⊆K) :
    Function.support (fun z : X => tensorDensity (a z)
      (fun i α => dpart (u i) α z.ofLp) (fun i α => dpart (v i) α z.ofLp))⊆K := by
  intro z hz
  by_contra hn
  have ht : (fun i α => dpart (u i) α z.ofLp)=(0:CMatrix) := by
    funext i d
    exact Function.notMem_support.mp (fun h => hn (dpart_support_lifted hK (hus i) d h))
  exact hz (by dsimp only; rw [ht,tensor_zero_left])

lemma density_chart_all (e : OpenPartialHomeomorph X X) {K : Set X}
    (hK : IsCompact K) (hs : K⊆e.source) {η : X → ℝ} (hηs : tsupport η⊆e.target)
    (hη : ∀ z∈e '' K, η z=1) (Q : X ≃ₗᵢ[ℝ] X) (u v : I → Y → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hus : ∀ j, Function.support (fun z : X => u j z.ofLp)⊆K)
    (hvs : ∀ j, Function.support (fun z : X => v j z.ofLp)⊆K)
    (Φ Ψ : X → X) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΦ : ∀ y∈K, Φ y=e y) (hΨe : ∀ z∈e '' K, Ψ =ᶠ[𝓝 z] e.symm)
    (l m : X → ℝ) {y : X} (hy : y∈e.source) :
    complexDensity (l (e y)) (m (e y)) (fieldGradient (transferred e η Q u) (e y))
      (fieldGradient (transferred e η Q v) (e y))=
      tensorDensity (fun i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
        (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
        (fun i α => dpart (u i) α y.ofLp) (fun i α => dpart (v i) α y.ofLp) := by
  by_cases hyK : y∈K
  · exact density_chart e hK hs hηs hη Q u v hu hv hus hvs Φ Ψ hΨ hΦ hΨe l m hyK
  · have hn : e y∉e '' K := by
      rintro ⟨z,hz,he⟩
      exact hyK (e.injOn (hs hz) hy he ▸ hz)
    rw [Function.notMem_support.mp (fun h => hn
      (physical_density_support (compact_image e hK hs).isClosed l m _ _
        (support_transferred e hηs Q u hus) h)),
      Function.notMem_support.mp (fun h => hyK (chart_density_support hK.isClosed
        (fun z i α j β => ElasticityBoundaryPhysicalMass.principal Q Φ Ψ
          (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β z.ofLp) u v hus h))]

end ElasticityBoundaryDensityPull
namespace ElasticityBoundaryEnergyChart
/-! Exact complex physical energy change of variables for the actual packets. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A compactly supported physical integrand pulls back with its exact
Jacobian, including the domain's half-space indicator. -/
theorem compact_chart_integral_complex (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    {K Ω H : Set E} (hs : K⊆e.source) (hΩ : MeasurableSet Ω) (hH : MeasurableSet H)
    (hhalf : ∀ y∈e.source, e y∈Ω ↔ y∈H)
    {Φ : E → E} (hΦ : ∀ y∈K, Φ =ᶠ[𝓝 y] e)
    (f g : E → ℂ) (hf : Function.support f⊆e '' K) (hg : Function.support g⊆K)
    (hfg : ∀ y∈e.source, f (e y)=g y) :
    (∫ x in Ω, f x ∂μ)=(∫ y in H, |(fderiv ℝ Φ y).det| • g y ∂μ) := by
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
      ∫ y in e.source, H.indicator (fun z => |(fderiv ℝ Φ z).det| • g z) y ∂μ := by
    apply setIntegral_congr_fun e.open_source.measurableSet
    intro y hy
    dsimp only
    by_cases hyK : y∈K
    · rw [← (hΦ y hyK).fderiv_eq]
      by_cases hyH : y∈H
      · rw [indicator_of_mem ((hhalf y hy).mpr hyH),indicator_of_mem hyH,hfg y hy]
      · rw [indicator_of_notMem (fun h => hyH ((hhalf y hy).mp h)),indicator_of_notMem hyH,smul_zero]
    · have hz : g y=0 := Function.notMem_support.mp (fun h => hyK (hg h))
      simp only [indicator, hfg y hy]
      simp only [hz,smul_zero,ite_self]
  rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_indicator hH
  · intro y hy
    have hz : g y=0 := Function.notMem_support.mp (fun h => hy (hs (hg h)))
    simp only [indicator,hz,smul_zero,ite_self]

end ElasticityBoundaryEnergyChart
namespace ElasticityBoundaryPacket
/-! Exact physical variational packet energy, with its true compact chart
Jacobian, equals the finite mixed coordinate-energy integrals. -/
open Set Filter MeasureTheory
open scoped Topology BigOperators
open Elasticity ElasticityBoundaryDensityPull ElasticityBoundaryEnergyChart
  ElasticityBoundaryPacketMass ElasticityBoundaryPhysicalMass ElasticityBoundaryCutoffLayer
  ElasticityBoundaryStrongLayer ElasticityBoundaryMixedScaling ElasticityBoundaryGradientTransfer
  ElasticityBoundaryChartOperator ElasticityBoundaryMVNormal ElasticityBoundaryPhysicalTransfer
  ElasticityBoundaryCutoffParametrix ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma Setup.energy_chart_oai (s : Setup Ω x) (hΩ : MeasurableSet Ω) {l m : X → ℝ}
    (hl : BoundedCoefficient Ω l) (hm : BoundedCoefficient Ω m) (p q : Polynomial W) (δ : ℝ) :
    complexTrialEnergy l m (s.trial p δ) (s.trial q δ)=
      ∫ y in ElasticityBoundaryProfileBounds.halfspace,
        tensorDensity (fun i α j β => s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
          (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
          (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y) := by
  rw [Setup.trial,Setup.trial,complexFieldTrial_energy hl hm]
  have he := compact_chart_integral_complex volume s.e s.smooth s.source hΩ measurable_H s.inside
    s.Φ_germ
    (fun z => complexDensity (l z) (m z) (fieldGradient (s.field p δ) z) (fieldGradient (s.field q δ) z))
    (fun y : X => tensorDensity (fun i α j β => principal s.Q s.Φ s.Ψ
      (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y.ofLp)
      (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y.ofLp)
      (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y.ofLp))
    (physical_density_support s.image_compact.isClosed l m _ _ (s.field_support p δ))
    (chart_density_support s.compact.isClosed _ _ _ (s.cutoff_layer_support p δ))
    (fun y hy => density_chart_all s.e s.compact s.source s.η_support s.η_one s.Q _ _
      (smooth_cutoffLayer s.cutoff_smooth p δ) (smooth_cutoffLayer s.cutoff_smooth q δ)
      (s.cutoff_layer_support p δ) (s.cutoff_layer_support q δ) s.Φ s.Ψ s.Ψ_smooth
      (fun z hz => (s.Φ_germ z hz).eq_of_nhds) s.Ψ_germ l m hy)
  rw [he]
  rw [← integral_ofLp (fun y => tensorDensity (fun i α j β =>
    s.rawCoeff (fun z => (l z:ℂ)) (fun z => (m z:ℂ)) i α j β y)
    (fun i α => dpart (cutoffLayer s.cutoff p δ i) α y)
    (fun i α => dpart (cutoffLayer s.cutoff q δ i) α y))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    simp only [tensorDensity,Setup.rawCoeff,Setup.jacobian,WithLp.toLp_ofLp,
      Complex.real_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro β _
    ring)

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.energy_chart_oai := @OAI.ElasticityBoundaryPacket.Setup.energy_chart_oai
