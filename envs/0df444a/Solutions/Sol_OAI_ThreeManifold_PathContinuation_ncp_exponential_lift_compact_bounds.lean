-- Prove2me | solution 1 for OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:27.151702+00:00
-- url     : https://prove2.me/submissions/66ce9082-f34c-4b8e-af27-d74230b5d11e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Continuation.lean:L508-L581
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation

-- ---- from OAI.Geometry.ConjugatePoints.Geodesics ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Geodesic flow, variation equations, and the Gauss lemma.
-/

section

open Set Filter Topology Asymptotics
open scoped NNReal
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ThreeManifold.ODEVariation
end

section
open Set Filter Topology Metric
open scoped NNReal
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end ThreeManifold.ODEVariation
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ODEVariation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end ThreeManifold.ODEVariation
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle
namespace ThreeManifold

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle
namespace ThreeManifold.CompactEnergy
variable {B : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

end ThreeManifold.CompactEnergy
end

section
open Set Filter Topology Bundle Manifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation

namespace Equation
variable {X : Type*} (P : Equation X)
end Equation
end ThreeManifold.FlowContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section

open Set Filter Topology Manifold
open scoped ContDiff
namespace ThreeManifold.FlowContinuation
variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

end ThreeManifold.FlowContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ThreeManifold.RiemannianCoordinates
end

section

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma curvatureAlong_velocity_pairing (g : SmoothMetric M) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) :
    g.inner (γ s) (curvatureAlong g γ J s) (velocity γ s) = 0 := by
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hx := mem_chart_source E3 (γ s)
  rw [← metric_field_coordinates g (curvatureAlong g γ J) (velocity γ) hc hx,
    curvatureAlong_coordinates g J hγ hc hx,velocity_coordinates hγ hc hx]
  have h := curvature_pairing_skew g hc (c.map_source hx)
    (fieldCoordinates γ J c s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)
  rw [chartBilin_symm g c] at h
  rw [chartBilin_symm g (chartAt E3 (γ s))]
  change _ + _ = 0 at h
  linarith

lemma jacobi_velocity_pairing (g : SmoothMetric M) {γ : ℝ → M}
    (hγ : IsGeodesicOn g γ univ) {J : ∀ s, TangentSpace I3 (γ s)}
    (hJ : IsJacobiFieldOn g γ J univ) (h0 : J 0 = 0) (s : ℝ) :
    g.inner (γ s) (J s) (velocity γ s) =
      s * g.inner (γ 0) (covariantDerivative g γ J 0) (velocity γ 0) := by
  let D := covariantDerivative g γ J
  have hD := covariantDerivative_smooth g isOpen_univ hγ.1 (jacobi_smoothField g hJ)
  have hd (t : ℝ) : HasDerivAt (fun r => g.inner (γ r) (D r) (velocity γ r)) 0 t := by
    have h := intrinsic_pairing_hasDerivAt g isOpen_univ hγ.1 hD
      (velocity_smooth isOpen_univ hγ.1) (mem_univ t)
    have he := jacobi_intrinsic_equation g isOpen_univ hγ.1 hJ (mem_univ t)
    change covariantDerivative g γ D t + curvatureAlong g γ J t = 0 at he
    have he' := eq_neg_of_add_eq_zero_left he
    dsimp only [D] at he'
    simpa only [he',geodesic_acceleration_zero g isOpen_univ hγ (mem_univ t),map_zero,
      map_neg,_root_.neg_apply,curvatureAlong_velocity_pairing g J (hγ.1.contMDiffAt (by simp)),
      neg_zero,add_zero] using h
  have hconst (t : ℝ) : g.inner (γ t) (D t) (velocity γ t) = g.inner (γ 0) (D 0) (velocity γ 0) :=
    isOpen_univ.is_const_of_deriv_eq_zero (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (fun t _ => (hd t).deriv) (mem_univ t) (mem_univ 0)
  have hp (t : ℝ) : HasDerivAt (fun r => g.inner (γ r) (J r) (velocity γ r))
      (g.inner (γ 0) (D 0) (velocity γ 0)) t := by
    have h := intrinsic_pairing_hasDerivAt g isOpen_univ hγ.1 (jacobi_smoothField g hJ)
      (velocity_smooth isOpen_univ hγ.1) (mem_univ t)
    simp only [geodesic_acceleration_zero g isOpen_univ hγ (mem_univ t),map_zero,add_zero] at h
    exact h.congr_deriv (hconst t)
  have hh := isOpen_univ.eqOn_of_deriv_eq (convex_univ : Convex ℝ (univ : Set ℝ)).isPreconnected
    (fun t _ => (hp t).differentiableAt.differentiableWithinAt)
    ((differentiable_id.mul_const (g.inner (γ 0) (D 0) (velocity γ 0))).differentiableOn)
    (fun t _ => by rw [(hp t).deriv]; simp)
    (mem_univ 0) (by simp only [h0,map_zero,_root_.zero_apply,zero_mul,id_eq])
  exact hh (mem_univ s)

variable [CompactSpace M] [T2Space M]
lemma exponential_radial_differential (g : SmoothMetric M) (p : M) (v : E3) :
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v v = velocity (globalGeodesic g (fiberPhase p v)) 1 := by
  have he : (fun t : ℝ => exponential g p (t • v)) = globalGeodesic g (fiberPhase p v) :=
    funext (exponential_scale g p v)
  have hh := mfderiv_comp (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,E3)) (I'' := I3)
    (f := fun t : ℝ => t • v) (g := exponential g p) (1:ℝ)
    ((exponential_contMDiff g p).mdifferentiable (by simp) (1 • v))
    ((contDiff_id.smul contDiff_const : ContDiff ℝ 1 (fun t : ℝ => t • v)).differentiable (by simp) 1).mdifferentiableAt
  have h := congrArg (fun L : ℝ →L[ℝ] E3 => L 1) hh
  simp only [Function.comp_def] at h
  rw [he] at h
  have hd : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun t : ℝ => t • v) 1 1 = v := by
    rw [mfderiv_eq_fderiv]
    change deriv (fun t : ℝ => t • v) 1 = v
    simpa using ((hasDerivAt_id (1:ℝ)).smul_const v).deriv
  change velocity (globalGeodesic g (fiberPhase p v)) 1 =
    mfderiv 𝓘(ℝ,E3) I3 (exponential g p) (1 • v)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) (fun t : ℝ => t • v) 1 1) at h
  rw [hd,one_smul] at h
  exact h.symm

theorem exponential_gauss (g : SmoothMetric M) (p : M) (v b : E3) :
    g.inner (exponential g p v) (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b)
      (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v v) = g.inner p b v := by
  have hf := ((fiberPhase_contMDiff p).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).contMDiffAt (x := v)
  have hh := jacobi_velocity_pairing g (geodesicFamily_isGeodesic g (fiberPhase p) v)
    (geodesicVariation_isJacobi g hf b) (exponentialVariation_zero g p v b) 1
  rw [exponentialVariation_initial_covariantDerivative,exponentialFamily_zero,one_mul] at hh
  have hv : (velocity (geodesicFamily g (fiberPhase p) v) 0 : E3) = v :=
    congrArg (fun q : TangentBundle I3 M => (q.snd : E3)) (globalGeodesic_initial g (fiberPhase p v))
  rw [hv] at hh
  rw [exponential_radial_differential]
  exact hh
end ThreeManifold.RiemannianCoordinates

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Continuation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Geodesic continuation and the covering exponential map.
-/

section
open Set Filter Topology
namespace ThreeManifold.FlowContinuation.Equation
variable {X : Type*} (P : Equation X)

end ThreeManifold.FlowContinuation.Equation

namespace ThreeManifold.PathContinuation
variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Y]
variable (f : E → Y) (γ : ℝ → Y)
end ThreeManifold.PathContinuation
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}
open RiemannianCoordinates

end ThreeManifold.PathContinuation
end

section
open Set Filter Topology
namespace ThreeManifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable {f : E3 → M} {γ : ℝ → M}

variable [CompactSpace M] [T2Space M]

end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

lemma regularRadius_hasDerivAt (g : SmoothMetric M) (p : M) {v : ℝ → E3} {b : E3} {s : ℝ}
    (hv : HasDerivAt v b s) :
    HasDerivAt (fun t => regularRadius g p (v t))
      (g.inner p b (v s) / regularRadius g p (v s)) s := by
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner p
  have hd : HasDerivAt (fun t => B (v t) (v t)) (B b (v s) + B (v s) b) s := by
    simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      ((B.hasFDerivAt.comp s hv.hasFDerivAt).hasDerivAt.clm_apply hv)
  have hp : 0 < B (v s) (v s) + 1 := by
    have hn : 0 ≤ B (v s) (v s) := inner_self_nonneg g p (v s)
    linarith
  have hh := (hd.add_const 1).sqrt hp.ne'
  apply hh.congr_deriv
  change (g.inner p b (v s) + g.inner p (v s) b) / (2 * regularRadius g p (v s)) = _
  rw [g.symm p (v s) b]
  ring

variable [CompactSpace M] [T2Space M]
lemma exponential_radial_bound (g : SmoothMetric M) (p : M) (v b : E3) :
    (g.inner p b v / regularRadius g p v)^2 ≤
      g.inner (exponential g p v) (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b)
        (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b) := by
  have hg := exponential_gauss g p v b
  have hv := exponential_gauss g p v v
  have hc := metric_cauchy_schwarz g (exponential g p v)
    (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b)
    (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v v)
  rw [hg,hv] at hc
  have hp : 0 < g.inner p v v + 1 := by have := inner_self_nonneg g p v; linarith
  rw [div_pow,regularRadius,Real.sq_sqrt hp.le]
  apply (div_le_iff₀ hp).2
  have hn := inner_self_nonneg g (exponential g p v) (mfderiv 𝓘(ℝ,E3) I3 (exponential g p) v b)
  nlinarith
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.PathContinuation
open RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M] {γ : ℝ → M}

theorem ncp_exponential_lift_compact_bounds (g : SmoothMetric M)
    (hn : NoConjugatePoints g) (p : M)
    (hγ : ContMDiff 𝓘(ℝ,ℝ) I3 1 γ) (x : State (exponential g p) γ)
    (A : ℝ) (_hA : 0 < A) :
    ∃ K : Set (State (exponential g p) γ), IsCompact K ∧ ∀ z a,
      0 < a → a ≤ A → z 0 = x →
      (equation (exponential g p) γ (exponential_isLocalHomeomorph g hn p)).CurveOn z (Ioo (-a) a) →
      MapsTo z (Ioo (-a) a) K := by
  let f := exponential g p
  have hf := exponential_contMDiff g p
  let hl := exponential_isLocalHomeomorph g hn p
  obtain ⟨C,hC,hCb⟩ := positive_bilinear_norm_bound (E := E3)
    (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner p) (fun v hv => g.pos p v hv)
  have hec : Continuous (fun s => g.inner (γ s) (velocity γ s) (velocity γ s)) :=
    (continuous_phaseEnergy g).comp (continuous_phaseLift_C1 hγ)
  obtain ⟨D,hD⟩ := ((isCompact_Icc : IsCompact (Icc (x.val.1-A) (x.val.1+A))).image hec).bddAbove
  let R := Real.sqrt (max D 0)
  let Q := regularRadius g p x.val.2 + R*A
  let K0 := Icc (x.val.1-A) (x.val.1+A) ×ˢ Metric.closedBall (0:E3) (Real.sqrt C * Q)
  let K : Set (State f γ) := Subtype.val ⁻¹' K0
  have hclosed : IsClosed {q : ℝ × E3 | f q.2 = γ q.1} :=
    isClosed_eq (hf.continuous.comp continuous_snd) (hγ.continuous.comp continuous_fst)
  have hK : IsCompact K := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_Icc.prod (isCompact_closedBall _ _))
  refine ⟨K,hK,fun z a ha haA hz0 hz t ht => ?_⟩
  have htime := time_affine f γ hl ha hz
  have htime' : ∀ s ∈ Ioo (-a) a, (z s).val.1 = s+x.val.1 := by
    intro s hs; simpa only [hz0] using htime hs
  have hst : ∀ s ∈ Ioo (-a) a, (z s).val.1 ∈ Icc (x.val.1-A) (x.val.1+A) := by
    intro s hs; rw [htime' s hs]; constructor <;> linarith [hs.1,hs.2]
  let r : ℝ → ℝ := fun s => regularRadius g p (z s).val.2
  have hdr (s : ℝ) (hs : s ∈ Ioo (-a) a) : HasDerivAt r
      (g.inner p (deriv (fun r => (z r).val.2) s) (z s).val.2 / r s) s :=
    regularRadius_hasDerivAt g p ((holds_space_derivative f γ (hz s hs)).hasDerivAt)
  have hdb (s : ℝ) (hs : s ∈ Ioo (-a) a) : ‖deriv r s‖ ≤ R := by
    rw [(hdr s hs).deriv,Real.norm_eq_abs]
    have hde : (show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2)
        (deriv (fun r => (z r).val.2) s) =
        (show E3 from velocity γ (z s).val.1) := lift_derivative_eq hf hγ (hz s hs)
    have hh := exponential_radial_bound g p (z s).val.2 (deriv (fun r => (z r).val.2) s)
    change _ ≤ (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner (f (z s).val.2))
      ((show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2) _)
      ((show E3 →L[ℝ] E3 from mfderiv 𝓘(ℝ,E3) I3 f (z s).val.2) _) at hh
    rw [hde] at hh
    have he := congrArg (fun q : M => (show E3 →L[ℝ] E3 →L[ℝ] ℝ from g.inner q)
      (show E3 from velocity γ (z s).val.1) (show E3 from velocity γ (z s).val.1)) (z s).property
    have hb := hh.trans_eq he
    have hb' := hb.trans ((hD (mem_image_of_mem _ (hst s hs))).trans (le_max_left D 0))
    apply (Real.le_sqrt (abs_nonneg _) (le_max_right D 0)).mpr
    rw [sq_abs]
    exact hb'
  have hr := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hdr s hs).differentiableAt) hdb (convex_Ioo (-a) a)
    (show (0:ℝ) ∈ Ioo (-a) a from ⟨by linarith,ha⟩) ht
  have hrt : r t ≤ Q := by
    simp only [sub_zero,Real.norm_eq_abs] at hr
    have hh := (le_abs_self (r t-r 0)).trans hr
    have hRA := mul_le_mul_of_nonneg_left (le_trans (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) haA)
      (Real.sqrt_nonneg (max D 0))
    have hr0 : r 0 = regularRadius g p x.val.2 := by dsimp [r]; rw [hz0]
    dsimp only [Q]; linarith
  change (z t).val.1 ∈ _ ∧ (z t).val.2 ∈ _
  refine ⟨hst t ht,?_⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  have hsqrt : (r t)^2 = g.inner p (z t).val.2 (z t).val.2 + 1 :=
    Real.sq_sqrt (by have := inner_self_nonneg g p (z t).val.2; linarith)
  have hnorm : ‖(z t).val.2‖ ≤ Real.sqrt C * r t := by
    have hq := Real.sq_sqrt hC.le
    have hb : ‖(z t).val.2‖^2 ≤ C * (r t ^ 2 - 1) := by
      rw [hsqrt,add_sub_cancel_right]
      exact hCb (z t).val.2
    have hn : 0 ≤ r t := Real.sqrt_nonneg _
    nlinarith [norm_nonneg (z t).val.2,Real.sqrt_nonneg C,mul_nonneg (Real.sqrt_nonneg C) hn]
  exact hnorm.trans (mul_le_mul_of_nonneg_left hrt (Real.sqrt_nonneg C))
end ThreeManifold.PathContinuation

namespace ThreeManifold.RiemannianCoordinates
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology unitInterval
namespace ThreeManifold
variable {E X : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
variable {p : E → X}

end ThreeManifold
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
local notation "𝕀" => unitInterval
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

variable [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates

section
open PathContinuation
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
variable [CompactSpace M] [T2Space M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction HyperbolicCore
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_2
end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.PathContinuation
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
open RiemannianCoordinates


theorem solution : type_of% @_root_.OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds := @_root_.OAI.ThreeManifold.PathContinuation.ncp_exponential_lift_compact_bounds
