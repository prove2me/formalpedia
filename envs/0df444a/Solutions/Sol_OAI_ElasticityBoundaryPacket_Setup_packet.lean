-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.packet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:10:49.063741+00:00
-- url     : https://prove2.me/submissions/46624c34-b380-45cf-8a16-8cc89b7506b6

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004
import Theorems.Thm_OAI_ElasticityBoundaryCutoffParametrix_finite_cutoff_layer
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_trial_residual
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_trial_size
import Theorems.Thm_OAI_ElasticityBoundaryPhysicalMass_transferred_mass_bound

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

lemma rotate_isotropic_formula (Q : I → I → ℂ) (l m : ℂ) (s α r β : I) :
    rotateTensor Q (elasticityTensor l m) s α r β =
      l*columnDot Q s α*columnDot Q r β+
      m*(columnDot Q s r*columnDot Q α β+columnDot Q s β*columnDot Q α r) := by
  unfold rotateTensor elasticityTensor
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_irrel, Fintype.sum_ite_eq, Finset.sum_const_zero]
  unfold columnDot
  simp only [Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Simultaneously transporting displacement and spatial coordinates by the
same actual orthogonal frame leaves the frozen physical tensor unchanged. -/
theorem rotate_isotropic (Q : X ≃ₗᵢ[ℝ] X) (l m : ℂ) (s α r β : I) :
    rotateTensor (frameMatrix Q) (elasticityTensor l m) s α r β=elasticityTensor l m s α r β := by
  rw [rotate_isotropic_formula]
  simp only [columnDot, frameMatrix_orthogonal, elasticityTensor]

end ElasticityBoundaryRotation

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

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

lemma chartPrincipal_frozen (Q : X ≃ₗᵢ[ℝ] X) (Φ : Y → X) (ψ : X → Y)
    (l m : X → ℂ) (hj : ∀ k α, (jac ψ (basis k) α (Φ 0):ℂ)=frameMatrix Q k α)
    (s α r β : I) :
    chartPrincipal Q Φ ψ l m s α r β 0=elasticityTensor (l (Φ 0)) (m (Φ 0)) s α r β := by
  have he : chartPrincipal Q Φ ψ l m s α r β 0=
      rotateTensor (frameMatrix Q) (elasticityTensor (l (Φ 0)) (m (Φ 0))) s α r β := by
    unfold chartPrincipal principalPull mixedTensor coeff rotateTensor
    simp only [hj, Finset.sum_mul]
    calc
      _ = ∑ k, ∑ i, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := by
        apply Finset.sum_congr rfl; intro k _
        exact Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ v, ∑ j, frameMatrix Q i s *
          elasticityTensor (l (Φ 0)) (m (Φ 0)) i k j v * frameMatrix Q j r *
          frameMatrix Q k α * frameMatrix Q v β := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro v _
        ring
  rw [he,rotate_isotropic]

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

lemma strong_mul_coeff (κ : Y → ℂ) (a : SmoothTensor) (b : SmoothLower)
    (u : I → Y → ℂ) (i : I) (y : Y) :
    strong (fun i α j β z => κ z*a i α j β z) (fun i j β z => κ z*b i j β z) u i y=
      κ y*strong a b u i y := by
  simp only [strong,mul_assoc,← Finset.mul_sum,mul_add]

lemma localize_strong (κ : Y → ℂ) (a : SmoothTensor) (b : SmoothLower)
    {K : Set Y} (hK : IsClosed K) (hκ : ∀ y∈K, κ y=1)
    (u : I → Y → ℂ) (hu : ∀ j, Function.support (u j)⊆K) :
    strong (fun i α j β z => κ z*a i α j β z) (fun i j β z => κ z*b i j β z) u=
      strong a b u := by
  funext i y
  rw [strong_mul_coeff]
  by_cases hy : y∈K
  · rw [hκ y hy,one_mul]
  · have hz : strong a b u i y=0 := Function.notMem_support.mp
      (fun h => hy (strong_support a b hK u hu i h))
    rw [hz,mul_zero]

lemma cutoff_support {χ : Y → ℂ} (q : Polynomial W) (δ : ℝ) (j : I) :
    Function.support (cutoffLayer χ q δ j)⊆tsupport χ := by
  intro y hy
  apply subset_tsupport χ
  intro hz
  exact hy (by simp [cutoffLayer,hz])

lemma compact_coefficients (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    {K : Set Y} (hK : IsCompact K) :
    ∃ (a' : SmoothTensor) (b' : SmoothLower),
      (∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a' i α j β) ∧ HasCompactSupport (a' i α j β)) ∧
      (∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b' i j β) ∧ HasCompactSupport (b' i j β)) ∧
      (∀ y∈K, ∀ i α j β, a' i α j β y=a i α j β y) ∧
      ∀ u : I → Y → ℂ, (∀ j, Function.support (u j)⊆K) → strong a' b' u=strong a b u := by
  obtain ⟨κ,hκ,hκc,_,hκ1,_⟩ := compact_smooth_cutoff hK isOpen_univ (subset_univ _)
  let κc : Y → ℂ := fun y => (κ y:ℂ)
  have hκcs : ContDiff ℝ (⊤ : ℕ∞) κc := Complex.ofRealCLM.contDiff.comp hκ
  have hκcc : HasCompactSupport κc :=
    hκc.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hκK (y : Y) (hy : y∈K) : κc y=1 := by
    change (κ y:ℂ)=1
    exact_mod_cast hκ1.self_of_nhdsSet y hy
  refine ⟨(fun i α j β z => κc z*a i α j β z),
    (fun i j β z => κc z*b i j β z),?_,?_,?_,?_⟩
  · exact fun i α j β => ⟨hκcs.mul (ha i α j β),hκcc.mul_right⟩
  · exact fun i j β => ⟨hκcs.mul (hb i j β),hκcc.mul_right⟩
  · intro y hy i α j β
    dsimp only
    rw [hκK y hy,one_mul]
  · exact fun u hu => localize_strong κc a b hK.isClosed hκK u hu

/-- The true arbitrary-order strong quasimode theorem needs only local
smoothness of the physical pullback. Compact coefficients used during the
Taylor construction leave the literal final operator unchanged. -/
theorem finite_local_layer (a : SmoothTensor) (b : SmoothLower)
    (ha : ∀ i α j β, ContDiff ℝ (⊤ : ℕ∞) (a i α j β))
    (hb : ∀ i j β, ContDiff ℝ (⊤ : ℕ∞) (b i j β))
    {χ : Y → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχ0 : χ =ᶠ[𝓝 (0:Y)] fun _ => 1)
    (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (ha0 : ∀ i α j β, a i α j β 0=elasticityTensor l m i α j β)
    (p₀ : W) (h₀ : normal l m p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ i : I, ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 →
        MemLp (strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i) 2 (volume.restrict halfspace) ∧
        (∫ z in halfspace, ‖strong a b (cutoffLayer χ (amplitude p (N+1)) δ) i z‖^2) ≤ C*δ^(2*N) := by
  obtain ⟨a',b',ha',hb',haa,hEq⟩ := compact_coefficients a b ha hb hc
  have h00 : (0:Y)∈tsupport χ := subset_tsupport χ (by
    change χ 0≠0
    rw [hχ0.eq_of_nhds]
    exact one_ne_zero)
  have ha'0 : ∀ i α j β, a' i α j β 0=elasticityTensor l m i α j β := by
    intro i α j β
    exact (haa 0 h00 i α j β).trans (ha0 i α j β)
  obtain ⟨p,hp0,hpb,hpB⟩ := finite_cutoff_layer a' b' ha' hb'
    hχ hc hχ0 l m hm he hp ha'0 p₀ h₀ N
  refine ⟨p,hp0,hpb,fun i => ?_⟩
  obtain ⟨C,hC,hB⟩ := hpB i
  refine ⟨C,hC,fun δ hδ hδ1 => ?_⟩
  have heq := hEq (cutoffLayer χ (amplitude p (N+1)) δ) (cutoff_support _ δ)
  simpa only [heq] using hB δ hδ hδ1

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

lemma inverse_derivative (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x) :
    HasFDerivAt e.symm Q.symm.toContinuousLinearEquiv.toContinuousLinearMap (e x) := by
  have hd := (hi.differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hinv := chart_fderiv_left_inverse e he hi hx
  rw [hQ.fderiv] at hinv
  have hf : fderiv ℝ e.symm (e x)=Q.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : X →L[ℝ] X => A (Q.symm v)) hinv
    change fderiv ℝ e.symm (e x) (Q (Q.symm v))=Q.symm v at h
    change fderiv ℝ e.symm (e x) v=Q.symm v
    simpa only [Q.apply_symm_apply] using h
  rw [← hf]
  exact hd.hasFDerivAt

lemma inverse_frame_entry (Q : X ≃ₗᵢ[ℝ] X) (k α : I) :
    Q.symm (EuclideanSpace.single k 1) α=Q (EuclideanSpace.single α 1) k := by
  have h := Q.inner_map_eq_flip (EuclideanSpace.single α 1) (EuclideanSpace.single k 1)
  simpa only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul, mul_one, starRingEnd_apply, star_trivial] using h.symm

lemma coordinate_inverse_jac (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x∈e.source) (Q : X ≃ₗᵢ[ℝ] X)
    (hQ : HasFDerivAt e Q.toContinuousLinearEquiv.toContinuousLinearMap x)
    {Ψ : X → X} (hΨ : Ψ =ᶠ[𝓝 (e x)] e.symm) (k α : I) :
    (jac (fun z => (Ψ z).ofLp) (EuclideanSpace.single k 1) α (e x):ℂ)=frameMatrix Q k α := by
  have hder := (inverse_derivative e he hi hx Q hQ).congr_of_eventuallyEq hΨ
  have hcoords := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).hasFDerivAt.comp (e x) hder
  change ((fderiv ℝ (fun z => (Ψ z).ofLp) (e x) (EuclideanSpace.single k 1)) α:ℂ)=_
  change HasFDerivAt (fun z => (Ψ z).ofLp) _ (e x) at hcoords
  rw [hcoords.fderiv]
  change (Q.symm (EuclideanSpace.single k 1) α:ℂ)=_
  rw [inverse_frame_entry]
  rfl

end ElasticityBoundaryInverseGeometry

end
end
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer
  ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryLayerOperator ElasticityBoundaryPhysicalTransfer

lemma Setup.zero_mem {Ω : Set X} {x : X} (s : Setup Ω x) : (0:X)∈s.K := by
  apply s.cutoff_support
  change s.cutoff 0≠0
  rw [s.cutoff_one.eq_of_nhds]
  exact one_ne_zero

lemma Setup.Φ_zero {Ω : Set X} {x : X} (s : Setup Ω x) : s.Φ 0=x :=
  (s.Φ_germ 0 s.zero_mem).eq_of_nhds.trans s.center

lemma Setup.frozen {Ω : Set X} {x : X} (s : Setup Ω x) (l m : X → ℂ)
    (i α j β : I) : principal s.Q s.Φ s.Ψ l m i α j β 0=elasticityTensor (l x) (m x) i α j β := by
  unfold ElasticityBoundaryPhysicalMass.principal
  rw [chartPrincipal_frozen]
  · simp only [WithLp.toLp_zero,s.Φ_zero]
  · intro k a
    simp only [WithLp.toLp_zero]
    rw [(s.Φ_germ 0 s.zero_mem).eq_of_nhds]
    exact coordinate_inverse_jac s.e s.smooth s.inverse_smooth s.at_zero s.Q s.deriv
      (s.Ψ_germ _ (mem_image_of_mem s.e s.zero_mem)) k a

end ElasticityBoundaryPacket

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

/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
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

/-- Uniform strong force of arbitrary order for the literal physical Lamé
operator; its lower terms and the actual curved chart are retained. -/
lemma Setup.field_force_mass (s : Setup Ω x) (hΩ : MeasurableSet Ω)
    {l m : X → ℂ} (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hm0 : m x≠0) (he0 : l x+2*m x≠0) (hp0 : l x+3*m x≠0)
    (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
    ∃ p : ℕ → W, p 0=p₀ ∧ (∀ n, 0<n → boundary (p n)=0) ∧
      ∃ C : ℝ, 0≤C ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ i,
        (∫ z in Ω, ‖force l m (s.field (amplitude p (N+1)) δ) i z‖^2)≤C*δ^(2*N) := by
  have ha := smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm
  have hb := smooth_chartLower s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
    (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm
  obtain ⟨p,hp,hpb,hbound⟩ := finite_local_layer _ _ ha hb s.cutoff_smooth s.cutoff_compact
    s.cutoff_one (l x) (m x) hm0 he0 hp0 (s.frozen l m) p₀ h₀ N
  obtain ⟨A,hA,hAbound⟩ := transferred_mass_bound s.e s.smooth s.compact s.source
    hΩ measurable_H s.inside s.η_support s.η_one s.Q s.Φ s.Ψ s.Φ_smooth s.Ψ_smooth s.Φ_germ s.Ψ_germ hl hm
  choose B hB hBbound using hbound
  refine ⟨p,hp,hpb,A*∑ i, B i,mul_nonneg hA (Finset.sum_nonneg (fun i _ => hB i)),
    fun δ hδ hδ1 i => ?_⟩
  apply (hAbound _ (smooth_cutoffLayer s.cutoff_smooth _ δ) (s.cutoff_layer_support _ δ) i).trans
  calc
    _ ≤ A*∑ j, (B j*δ^(2*N)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum; intro j _
      rw [integral_ofLp (fun y => ‖strong (ElasticityBoundaryPhysicalMass.principal s.Q s.Φ s.Ψ l m)
        (ElasticityBoundaryPhysicalMass.lower s.Q s.Φ s.Ψ l m) (cutoffLayer s.cutoff (amplitude p (N+1)) δ) j y‖^2)]
      exact (hBbound j δ hδ hδ1).2
    _ = _ := by rw [← Finset.sum_mul,mul_assoc]

end ElasticityBoundaryPacket
namespace ElasticityBoundaryPacket

section
/-! Arbitrary-order actual physical boundary packets. All coefficient and
ellipticity assumptions here follow from the admissibility. -/
open Set MeasureTheory
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal ElasticityBoundaryActualTower

variable {Ω : Set X} {x : X}

lemma amplitude_zero (p : ℕ → W) (N : ℕ) : (amplitude p N).coeff 0=p 0 := by
  simp [amplitude,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]

lemma ellipticity_at {l m : X → ℝ} (ha : Admissible Ω l m) (hx : x∈closure Ω) :
    (m x:ℂ)≠0 ∧ (l x:ℂ)+2*m x≠0 ∧ (l x:ℂ)+3*m x≠0 := by
  obtain ⟨hm,he⟩ := ha.2.2 x hx
  have h2 : 0<l x+2*m x := by linarith
  have h3 : 0<l x+3*m x := by linarith
  exact ⟨Complex.ofReal_ne_zero.mpr hm.ne',
    by exact_mod_cast h2.ne',by exact_mod_cast h3.ne'⟩

/-- Genuine physical trace-space test, prescribed leading frozen solution,
uniform H1 norm and arbitrarily small dual Lamé residual. -/
lemma Setup.packet_oai (s : Setup Ω x) {l m : X → ℝ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (ha : Admissible Ω l m) (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hx : x∈closure Ω) (p₀ : W) (h₀ : normal (l x) (m x) p₀=0) (N : ℕ) :
    ∃ q : Polynomial W, q.coeff 0=p₀ ∧ ∃ A B : ℝ, 0≤A ∧ 0≤B ∧
      ∀ δ : ℝ, 0<δ → δ≤1 → complexTrialSize (s.trial q δ)≤A ∧
      complexResidualSize (ha.1.boundedCoefficient hO hB)
        (ha.2.1.boundedCoefficient hO hB) (s.trial q δ)≤B*δ^N := by
  obtain ⟨hm0,he0,hp0⟩ := ellipticity_at ha hx
  obtain ⟨p,hp,_hpb,C,hC,hf⟩ := s.field_force_mass hO.measurableSet
    (Complex.ofRealCLM.contDiff.comp hl) (Complex.ofRealCLM.contDiff.comp hm)
    hm0 he0 hp0 p₀ h₀ N
  obtain ⟨A,hA,hAb⟩ := s.trial_size hO.measurableSet (amplitude p (N+1))
  obtain ⟨B,hB0,hBb⟩ := s.trial_residual hB hl hm (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) _ N hC hf
  refine ⟨amplitude p (N+1),(amplitude_zero p _).trans hp,A,B,hA,hB0,fun δ hδ hδ1 => ?_⟩
  exact ⟨hAb δ hδ hδ1,hBb δ hδ hδ1⟩

end
/-! Equal full real physical DN maps control two genuine, independently
corrected physical packets; the traces need not coincide. -/
open Set
open scoped BigOperators
open Elasticity ElasticityBoundaryMVNormal

end ElasticityBoundaryPacket

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.packet_oai := @OAI.ElasticityBoundaryPacket.Setup.packet_oai
