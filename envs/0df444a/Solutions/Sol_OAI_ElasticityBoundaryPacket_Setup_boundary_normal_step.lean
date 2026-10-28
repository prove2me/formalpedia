-- Prove2me | solution 1 for OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:50:50.599203+00:00
-- url     : https://prove2.me/submissions/068b1b2f-e398-4f81-8c08-4b4158f07f47

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El001
import Theorems.Thm_OAI_ElasticityBoundaryPacket_Setup_extract_normal
import Theorems.Thm_OAI_ElasticityBoundaryPacket_pair_separates

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryLayers
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

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
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

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityBoundaryPacket
/-! Smooth compact localization of the literal pulled physical energy tensor.
The true chart Jacobian is retained, including its nonzero value at the center. -/
open Set Filter
open scoped Topology BigOperators
open Elasticity ElasticityBoundary ElasticityBoundaryPhysicalMass
  ElasticityBoundaryChartOperator ElasticityBoundaryLayerOperator

variable {Ω : Set X} {x : X}

lemma Setup.jacobian_continuous (s : Setup Ω x) : Continuous s.jacobian :=
  ((ContinuousLinearMap.continuous_det.comp (s.Φ_smooth.continuous_fderiv (by simp))).abs).comp
    (PiLp.continuous_toLp 2 (fun _ : I => ℝ))

lemma Setup.jacobian_pos (s : Setup Ω x) : 0 < s.jacobian 0 := by
  have hf : fderiv ℝ s.Φ 0=s.Q.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [(s.Φ_germ 0 s.zero_mem).fderiv_eq]
    exact s.deriv.fderiv
  simp only [Setup.jacobian,WithLp.toLp_zero,hf]
  exact abs_pos.mpr s.Q.toLinearEquiv.isUnit_det'.ne_zero

lemma Setup.rawCoeff_continuous (s : Setup Ω x) {l m : X → ℂ}
    (hl : ContDiff ℝ (⊤ : ℕ∞) l) (hm : ContDiff ℝ (⊤ : ℕ∞) m) (i α j β : I) :
    Continuous (s.rawCoeff l m i α j β) := by
  exact (Complex.continuous_ofReal.comp s.jacobian_continuous).mul
    (smooth_chartPrincipal s.Q (s.Φ_smooth.comp PiLp.contDiff_toLp)
      (PiLp.contDiff_ofLp.comp s.Ψ_smooth) hl hm i α j β).continuous

lemma Setup.rawCoeff_zero (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) :
    s.rawCoeff l m i α j β 0=(s.jacobian 0:ℂ)*elasticityTensor (l x) (m x) i α j β := by
  rw [Setup.rawCoeff,s.frozen]

end ElasticityBoundaryPacket

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Boundary values of BOTH Lamé parameters from the literal physical DN map
on an arbitrary honest smooth domain. This is not a near-boundary assumption. -/
noncomputable section
open Set
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma admissible_frozen_ne {l m : X → ℝ} (ha : Admissible Ω l m) (hx : x∈closure Ω) :
    (m x:ℂ)≠0 ∧ (l x:ℂ)+3*(m x:ℂ)≠0 := by
  obtain ⟨hm,he⟩ := ha.2.2 x hx
  constructor
  · exact Complex.ofReal_ne_zero.mpr hm.ne'
  · have hp : 0<l x+3*m x := by linarith
    exact_mod_cast hp.ne'

end ElasticityBoundaryPacket

end
end
section
/-! Honest continuous normal Taylor quotients, obtained from the integral
remainder. These are actual functions of the coefficients, not assumed jets. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryNormalTaylor

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma normalJet_continuous {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    Continuous (normalJet n f) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Y) F (fun _ => en)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

lemma travel_continuous : Continuous (fun z : Y × ℝ => travel z.1 z.2) := by
  unfold travel projection
  fun_prop

omit [CompleteSpace F] in
lemma quotient_continuous {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    Continuous (quotient n f) := by
  have hc : Continuous (Function.uncurry (fun y (t:ℝ) => (1-t)^n • normalJet (n+1) f (travel y t))) :=
    ((continuous_const.sub continuous_snd).pow n).smul
      ((normalJet_continuous hf (n+1)).comp travel_continuous)
  have h := continuous_parametric_integral_of_continuous (μ := volume) hc (isCompact_Icc (a := (0:ℝ)) (b := 1))
  have he (y : Y) : (∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t))=
      ∫ t in Icc (0:ℝ) 1, (1-t)^n • normalJet (n+1) f (travel y t) := by
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  change Continuous (fun y : Y => (n.factorial:ℝ)⁻¹ • ∫ t in (0:ℝ)..1, (1-t)^n • normalJet (n+1) f (travel y t))
  simp_rw [he]
  exact (continuous_const : Continuous (fun _ : Y => (n.factorial:ℝ)⁻¹)).smul h

lemma normal_factor {f : Y → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (y : Y)
    (hz : ∀ k≤n, normalJet k f (projection y)=0) :
    f y=(y 2)^(n+1) • quotient n f y := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := projection y) (y := (y 2) • en) (n := n)
    (fun _ _ => hf.contDiffAt.of_le (by exact_mod_cast le_top))
  have hv (k : ℕ) (z : Y) :
      iteratedFDeriv ℝ k f z (fun _ => (y 2) • en)=(y 2)^k • normalJet k f z := by
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,normalJet]
  rw [show projection y+y 2 • en=y by simp [projection]] at h
  rw [Finset.sum_eq_zero (fun k hk => by
    have hk' : k<n+1 := Finset.mem_range.mp hk
    rw [hv,hz k (by omega),smul_zero,smul_zero]),zero_add] at h
  simp_rw [hv] at h
  rw [show (fun t => (1-t)^n • ((y 2)^(n+1) • normalJet (n+1) f
    (projection y+t • (y 2 • en))))=
      (fun t => (y 2)^(n+1) • ((1-t)^n • normalJet (n+1) f (travel y t))) from by
        funext t; rw [smul_comm]; rfl] at h
  rw [intervalIntegral.integral_smul] at h
  simpa only [quotient,smul_comm (n.factorial:ℝ)⁻¹] using h

lemma quotient_zero (n : ℕ) (f : Y → F) :
    quotient n f 0=((n+1).factorial:ℝ)⁻¹ • normalJet (n+1) f 0 := by
  simp only [quotient,travel_zero]
  rw [intervalIntegral.integral_smul_const]
  have hi : (∫ t in (0:ℝ)..1, (1-t)^n)=(n+1:ℝ)⁻¹ := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^n) 1]
    simp [integral_pow]
  rw [hi,smul_smul]
  congr 1
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_inv_rev]

end ElasticityBoundaryNormalTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Projection-stable packet supports are constructed inside honest open charts. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundary ElasticityBoundaryNormalTaylor
  ElasticityBoundaryInverseGeometry ElasticityBoundaryGradientTransfer

lemma projection_norm_le (y : Y) :
    ‖WithLp.toLp 2 (projection y)‖ ≤ ‖(WithLp.toLp 2 y : X)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,projection]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i=2
  · subst i
    simp only [Pi.sub_apply,Pi.smul_apply,en,Pi.single_eq_same,smul_eq_mul,mul_one,sub_self,zero_pow (by omega : 2≠0)]
    exact sq_nonneg _
  · simp [en,hi]

lemma projection_mem {r : ℝ} {y : Y} (hy : WithLp.toLp 2 y∈Metric.closedBall (0:X) r) :
    WithLp.toLp 2 (projection y)∈Metric.closedBall (0:X) r := by
  exact Metric.mem_closedBall.mpr (by
    simpa only [dist_zero_right] using (projection_norm_le y).trans (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hy))

end ElasticityBoundaryPacket

end
end
section
/-! Flat finite jets remain flat under arbitrary honest smooth coordinates.
This is a consequence of the actual Faà di Bruno formula. -/
noncomputable section
namespace ElasticityBoundaryFlatComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma comp_flat {f : F → G} {g : E → F} {x : E} (n : ℕ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (g x)) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hz : ∀ k≤n, iteratedFDeriv ℝ k f (g x)=0) :
    iteratedFDeriv ℝ n (f ∘ g) x=0 := by
  rw [iteratedFDeriv_comp hf hg (by exact_mod_cast le_top)]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, hz c.length c.length_le,zero_apply]

end ElasticityBoundaryFlatComposition

end
end
section
/-! The flattened zero plane consists of actual boundary points; lower
physical jets give actual normal Taylor remainders on a ball packet support. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor ElasticityBoundaryFlatComposition
variable {Ω : Set X} {x : X}

lemma Setup.plane_frontier (s : Setup Ω x) (hO : IsOpen Ω)
    {y : X} (hy : y∈s.e.source) (hz : y 2=0) : s.e y∈frontier Ω := by
  have hn : s.e y∉Ω := by
    rw [s.inside y hy,hz]
    exact lt_irrefl 0
  have hct : Continuous (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun t : ℝ => y+t • EuclideanSpace.single 2 (1:ℝ)) (𝓝[>] 0) (𝓝 y) := by
    simpa only [zero_smul,add_zero] using hct.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hm : ∀ᶠ t : ℝ in 𝓝[>] 0, s.e (y+t • EuclideanSpace.single 2 (1:ℝ))∈Ω := by
    filter_upwards [ht (s.e.open_source.mem_nhds hy),self_mem_nhdsWithin] with t hty htp
    rw [s.inside _ hty]
    simpa [hz,PiLp.single_apply] using htp
  have hc : s.e y∈closure Ω := mem_closure_of_tendsto
    (((s.smooth.continuousOn y hy).continuousAt (s.e.open_source.mem_nhds hy)).tendsto.comp ht) hm
  rw [hO.frontier_eq]
  exact ⟨hc,hn⟩

lemma Setup.chartFunction_smooth (s : Setup Ω x) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (s.chartFunction f) :=
  hf.comp (s.Φ_smooth.comp PiLp.contDiff_toLp)

lemma Setup.chart_flat (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {y : Y} (hy : WithLp.toLp 2 y∈s.K) (hy0 : y 2=0) :
    iteratedFDeriv ℝ n (s.chartFunction f) y=0 := by
  apply comp_flat n hf.contDiffAt (s.Φ_smooth.comp PiLp.contDiff_toLp).contDiffAt
  intro k hk
  change iteratedFDeriv ℝ k f (s.Φ (WithLp.toLp 2 y))=0
  rw [(s.Φ_germ _ hy).eq_of_nhds]
  exact hz k hk _ (s.plane_frontier hO (s.source hy) hy0)

lemma Setup.chart_normal_factor (s : Setup Ω x) (hO : IsOpen Ω) {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ)
    (hz : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k f z=0)
    {r : ℝ} (hK : s.K=Metric.closedBall 0 r) {y : Y} (hy : WithLp.toLp 2 y∈s.K) :
    s.chartFunction f y=(y 2)^(n+1)*quotient n (s.chartFunction f) y := by
  apply normal_factor (s.chartFunction_smooth hf) n y
  intro k hk
  rw [normalJet,s.chart_flat hO hf k (fun j hj => hz j (hj.trans hk))]
  · rfl
  · rw [hK] at hy ⊢
    exact projection_mem hy
  · exact projection_two y

end ElasticityBoundaryPacket

end
end
section
/-! Pointwise linearity of the literal pulled energy tensor in the two
scalar Lamé values. Geometric coefficients are not frozen off-center. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryPhysicalMass ElasticityBoundaryChartOperator
  ElasticityBoundaryPullback ElasticityBoundaryFrameOperator ElasticityBoundaryPhysicalStrong
  ElasticityBoundaryLayerOperator
variable {Ω : Set X} {x : X}

lemma elasticityTensor_decomp (l m : ℂ) (i α j β : I) :
    elasticityTensor l m i α j β=l*elasticityTensor 1 0 i α j β+
      m*elasticityTensor 0 1 i α j β := by
  unfold elasticityTensor
  ring

lemma Setup.rawCoeff_decomp (s : Setup Ω x) (l m : X → ℂ) (i α j β : I) (y : Y) :
    s.rawCoeff l m i α j β y=
      l (s.Φ (WithLp.toLp 2 y))*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y+
      m (s.Φ (WithLp.toLp 2 y))*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y := by
  unfold Setup.rawCoeff ElasticityBoundaryPhysicalMass.principal chartPrincipal principalPull mixedTensor coeff
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [elasticityTensor_decomp (l _) (m _)]
  ring

lemma Setup.linearCoeff_continuous (s : Setup Ω x) {l m : Y → ℂ}
    (hl : Continuous l) (hm : Continuous m) (i α j β : I) :
    Continuous (s.linearCoeff l m i α j β) :=
  (hl.mul (s.rawCoeff_continuous contDiff_const contDiff_const i α j β)).add
    (hm.mul (s.rawCoeff_continuous contDiff_const contDiff_const i α j β))

lemma Setup.linearCoeff_zero (s : Setup Ω x) (l m : Y → ℂ) (i α j β : I) :
    s.linearCoeff l m i α j β 0=(s.jacobian 0:ℂ)*elasticityTensor (l 0) (m 0) i α j β := by
  rw [Setup.linearCoeff,s.rawCoeff_zero,s.rawCoeff_zero,elasticityTensor_decomp (l 0) (m 0)]
  ring

lemma Setup.localize_linearCoeff (s : Setup Ω x) {l m : Y → ℂ}
    (hl : Continuous l) (hm : Continuous m) :
    ∃ H : I → I → I → I → Y → ℂ,
      (∀ i α j β, Continuous (H i α j β)) ∧
      (∀ i α j β, HasCompactSupport (H i α j β)) ∧
      (∀ i α j β y, WithLp.toLp 2 y∈s.K → H i α j β y=s.linearCoeff l m i α j β y) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    s.compact isOpen_univ (subset_univ s.K)
  let ρc : Y → ℂ := fun y => (ρ (WithLp.toLp 2 y):ℂ)
  have hρcc : HasCompactSupport ρc :=
    (hρc.comp_homeomorph (PiLp.homeomorph 2 (fun _ : I => ℝ)).symm).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  refine ⟨fun i α j β y => ρc y*s.linearCoeff l m i α j β y,?_,?_,?_⟩
  · intro i α j β
    exact (Complex.continuous_ofReal.comp (hρ.continuous.comp
      (PiLp.continuous_toLp 2 (fun _ : I => ℝ)))).mul (s.linearCoeff_continuous hl hm i α j β)
  · intro i α j β
    exact hρcc.mul_right
  · intro i α j β y hy
    simp only [ρc,hρ1.self_of_nhdsSet _ hy,Complex.ofReal_one,one_mul]

end ElasticityBoundaryPacket

end
end
section
/-! Actual normal jet induction step from the physical DN map. The quotient
is the concrete Taylor integral; no pseudodifferential symbol or jet conclusion
is postulated. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityBoundaryPacket
open Elasticity ElasticityBoundaryNormalTaylor
variable {Ω : Set X} {x : X}

lemma Setup.boundary_normal_step_oai (s : Setup Ω x) {l₁ m₁ l₂ m₂ : X → ℝ}
    (hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁) (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁)
    (hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂) (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂)
    (ha₁ : Admissible Ω l₁ m₁) (ha₂ : Admissible Ω l₂ m₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) (hx : x∈closure Ω)
    (hDN : DN Ω l₁ m₁=DN Ω l₂ m₂)
    (n : ℕ) (hzl : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (l₁-l₂) z=0)
    (hzm : ∀ k≤n, ∀ z∈frontier Ω, iteratedFDeriv ℝ k (m₁-m₂) z=0)
    {r : ℝ} (hK : s.K=Metric.closedBall 0 r) :
    normalJet (n+1) (s.chartFunction (l₁-l₂)) 0=0 ∧
      normalJet (n+1) (s.chartFunction (m₁-m₂)) 0=0 := by
  let L := quotient n (s.chartFunction (l₁-l₂))
  let M := quotient n (s.chartFunction (m₁-m₂))
  have hLc : Continuous (fun y => (L y:ℂ)) := Complex.continuous_ofReal.comp
    (quotient_continuous (s.chartFunction_smooth (hl₁.sub hl₂)) n)
  have hMc : Continuous (fun y => (M y:ℂ)) := Complex.continuous_ofReal.comp
    (quotient_continuous (s.chartFunction_smooth (hm₁.sub hm₂)) n)
  obtain ⟨H,hHc,hHs,hHe⟩ := s.localize_linearCoeff hLc hMc
  have hH (i α j β : I) (y : Y) (hy : WithLp.toLp 2 y∈s.K) :
      s.rawCoeff (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)) i α j β y-
      s.rawCoeff (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ)) i α j β y=(y 2:ℂ)^(n+1)*H i α j β y := by
    rw [hHe i α j β y hy,Setup.linearCoeff,
      s.rawCoeff_decomp (fun z => (l₁ z:ℂ)) (fun z => (m₁ z:ℂ)),
      s.rawCoeff_decomp (fun z => (l₂ z:ℂ)) (fun z => (m₂ z:ℂ))]
    have hl := s.chart_normal_factor hO (hl₁.sub hl₂) n hzl hK hy
    have hm := s.chart_normal_factor hO (hm₁.sub hm₂) n hzm hK hy
    change l₁ (s.Φ (WithLp.toLp 2 y))-l₂ (s.Φ (WithLp.toLp 2 y))=(y 2)^(n+1)*L y at hl
    change m₁ (s.Φ (WithLp.toLp 2 y))-m₂ (s.Φ (WithLp.toLp 2 y))=(y 2)^(n+1)*M y at hm
    have hlc : (l₁ (s.Φ (WithLp.toLp 2 y)):ℂ)-(l₂ (s.Φ (WithLp.toLp 2 y)):ℂ)=
        (y 2:ℂ)^(n+1)*(L y:ℂ) := by exact_mod_cast hl
    have hmc : (m₁ (s.Φ (WithLp.toLp 2 y)):ℂ)-(m₂ (s.Φ (WithLp.toLp 2 y)):ℂ)=
        (y 2:ℂ)^(n+1)*(M y:ℂ) := by exact_mod_cast hm
    linear_combination hlc*s.rawCoeff (fun _ => 1) (fun _ => 0) i α j β y +
      hmc*s.rawCoeff (fun _ => 0) (fun _ => 1) i α j β y
  have hH0 : (fun i α j β => H i α j β 0)=
      (fun i α j β => (s.jacobian 0:ℂ)*ElasticityBoundaryLayerOperator.elasticityTensor
        (L 0) (M 0) i α j β) := by
    funext i α j β
    rw [hHe i α j β 0 (by simpa using s.zero_mem),s.linearCoeff_zero]
  have hpair := pair_separates (n+1) (l₁ x) (m₁ x) (l₂ x) (m₂ x) (s.jacobian 0)
    (L 0) (M 0)
    (admissible_frozen_ne ha₁ hx).1 (admissible_frozen_ne ha₂ hx).1
    (admissible_frozen_ne ha₁ hx).2 (admissible_frozen_ne ha₂ hx).2
    (Complex.ofReal_ne_zero.mpr s.jacobian_pos.ne') (by
      intro p q hp hq
      rw [← hH0]
      exact s.extract_normal hl₁ hm₁ hl₂ hm₂ ha₁ ha₂ hO hB hx hDN (n+1) H hHc hHs hH p q hp hq)
  have hL : L 0=0 := Complex.ofReal_eq_zero.mp hpair.1
  have hM : M 0=0 := Complex.ofReal_eq_zero.mp hpair.2
  have hfac : ((n+1).factorial:ℝ)⁻¹≠0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  dsimp only [L] at hL
  dsimp only [M] at hM
  rw [quotient_zero] at hL hM
  exact ⟨(smul_eq_zero.mp hL).resolve_left hfac,(smul_eq_zero.mp hM).resolve_left hfac⟩

end ElasticityBoundaryPacket

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step_oai := @OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step_oai
