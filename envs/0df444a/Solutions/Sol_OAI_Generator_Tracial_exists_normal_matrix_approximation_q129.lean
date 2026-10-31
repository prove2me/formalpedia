-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_normal_matrix_approximation_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:58:27.190637+00:00
-- url     : https://prove2.me/submissions/d769c9c3-2db2-4cc0-874a-02206efcb822

import Mathlib
import Definitions.Def_OAIQ129G010
import Definitions.Def_OAIQ129G012

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

/-- Unitary norm bound without requiring a separate nontriviality instance. -/
theorem unitary_norm_le (w : M.toStarSubalgebra) (hw : star w*w = 1) : ‖w‖ ≤ 1 := by
  have h : ‖star w*w‖ = ‖w‖*‖w‖ := CStarRing.norm_star_mul_self
  rw [hw] at h
  have hone : ‖(1 : M.toStarSubalgebra)‖ ≤ 1 := operator_norm_one_le
  nlinarith [norm_nonneg w]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The trace image of an operator-norm ball is norm closed in H. -/
theorem trace_ball_isClosed (C : ℝ) :
    IsClosed {ξ : H | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ} := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha he using hz
  have hC : 0 ≤ C := (norm_nonneg (a 0)).trans (ha 0)
  apply bounded_trace_limit τ a C hC ha z
  simpa only [he] using hlim

theorem trace_ball_convex (C : ℝ) :
    Convex ℝ {ξ : H | ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ} := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  refine ⟨s • a + t • b, ?_, rfl⟩
  calc
    ‖s • a + t • b‖ ≤ ‖s • a‖ + ‖t • b‖ := norm_add_le _ _
    _ = s * ‖a‖ + t * ‖b‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
    _ ≤ s * C + t * C := add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
    _ = C := by rw [← add_mul, hst, one_mul]

/-- Every point of the actual closed convex hull has an algebra representative
with the same operator norm bound. -/
theorem bounded_representative_of_closed_convexHull (s : Set H) (C : ℝ)
    (hs : ∀ ξ ∈ s, ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧
      (b : H →L[ℂ] H) τ.vector = ξ)
    {ξ : H} (hξ : ξ ∈ closure (convexHull ℝ s)) :
    ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ := by
  exact (closure_minimal (convexHull_min hs (trace_ball_convex τ C))
    (trace_ball_isClosed τ C)) hξ

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

theorem conjugateLinear_mul (u v : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    conjugateLinear (u*v) a = conjugateLinear u (conjugateLinear v a) := by
  change ((u : M.toStarSubalgebra)*(v : M.toStarSubalgebra))*a*star ((u : M.toStarSubalgebra)*(v : M.toStarSubalgebra)) = _
  simp only [conjugateLinear, LinearMap.coe_mk, AddHom.coe_mk, star_mul, mul_assoc]

theorem conjugate_norm_le (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    ‖conjugateLinear u a‖ ≤ ‖a‖ := by
  have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
  have hs := unitary_norm_le (star (u : M.toStarSubalgebra)) (by simp)
  calc
    ‖conjugateLinear u a‖ ≤ (‖(u : M.toStarSubalgebra)‖ * ‖a‖) * ‖star (u : M.toStarSubalgebra)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖a‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hs (norm_nonneg _) (by simp)
    _ = ‖a‖ := by ring

theorem conjugate_norm₂_le (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u a) ≤ τ.norm₂ a := by
  have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
  have hs := unitary_norm_le (star (u : M.toStarSubalgebra)) (by simp)
  calc
    τ.norm₂ (conjugateLinear u a) ≤ τ.norm₂ ((u : M.toStarSubalgebra)*a) * ‖star (u : M.toStarSubalgebra)‖ := τ.norm₂_mul_le_right _ _
    _ ≤ (‖(u : M.toStarSubalgebra)‖ * τ.norm₂ a) * ‖star (u : M.toStarSubalgebra)‖ :=
      mul_le_mul_of_nonneg_right (τ.norm₂_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * τ.norm₂ a) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hs (norm_nonneg _) (by simpa only [one_mul] using (show 0 ≤ τ.norm₂ a from norm_nonneg _))
    _ = τ.norm₂ a := by ring

theorem conjugate_norm₂ (u : unitary M.toStarSubalgebra) (a : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u a) = τ.norm₂ a := by
  apply le_antisymm (conjugate_norm₂_le τ u a)
  have h := conjugate_norm₂_le τ u⁻¹ (conjugateLinear u a)
  simpa only [← conjugateLinear_mul, inv_mul_cancel, conjugateLinear_one] using h

theorem traceOrbitHull_eq (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) :
    traceOrbitHull τ G b = closure (baseVector τ '' convexHull ℝ (algebraOrbit G b)) := by
  exact congrArg closure ((baseVector τ |>.restrictScalars ℝ).image_convexHull (algebraOrbit G b)).symm

theorem traceOrbitHull_nonempty (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) :
    (traceOrbitHull τ G b).Nonempty := by
  refine ⟨baseVector τ b, subset_closure (subset_convexHull ℝ _ ?_)⟩
  exact ⟨b, ⟨1, conjugateLinear_one b⟩, rfl⟩

theorem traceOrbitHull_representative (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra)
    {ξ : H} (hξ : ξ ∈ traceOrbitHull τ G b) :
    ∃ c : M.toStarSubalgebra, ‖c‖ ≤ ‖b‖ ∧ baseVector τ c = ξ := by
  apply bounded_representative_of_closed_convexHull τ _ ‖b‖ _ hξ
  rintro ξ ⟨a, ⟨u, rfl⟩, rfl⟩
  exact ⟨conjugateLinear u.val b, conjugate_norm_le _ _, rfl⟩

theorem conjugate_mem_convexHull (G : Subgroup (unitary M.toStarSubalgebra))
    (b : M.toStarSubalgebra) (u : G) {a : M.toStarSubalgebra}
    (ha : a ∈ convexHull ℝ (algebraOrbit G b)) :
    conjugateLinear u.val a ∈ convexHull ℝ (algebraOrbit G b) := by
  have h := Set.mem_image_of_mem (conjugateLinear u.val) ha
  change conjugateLinear u.val a ∈ (conjugateLinear u.val |>.restrictScalars ℝ) '' convexHull ℝ (algebraOrbit G b) at h
  rw [(conjugateLinear u.val |>.restrictScalars ℝ).image_convexHull] at h
  apply convexHull_mono _ h
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact ⟨u*v, conjugateLinear_mul _ _ _⟩

theorem conjugate_mem_traceOrbitHull (G : Subgroup (unitary M.toStarSubalgebra))
    (b c : M.toStarSubalgebra) (u : G)
    (hc : baseVector τ c ∈ traceOrbitHull τ G b) :
    baseVector τ (conjugateLinear u.val c) ∈ traceOrbitHull τ G b := by
  rw [traceOrbitHull_eq] at hc ⊢
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hc
  choose a ha he using hv
  apply mem_closure_of_tendsto (b := atTop) (f := fun n => baseVector τ (conjugateLinear u.val (a n)))
  · rw [tendsto_iff_norm_sub_tendsto_zero] at ht ⊢
    have hn (n : ℕ) : ‖baseVector τ (conjugateLinear u.val (a n)) - baseVector τ (conjugateLinear u.val c)‖ = ‖v n - baseVector τ c‖ := by
      rw [← map_sub, ← map_sub]
      change τ.norm₂ (conjugateLinear u.val (a n-c)) = ‖v n-baseVector τ c‖
      rw [conjugate_norm₂]
      change ‖baseVector τ (a n)-baseVector τ c‖ = _
      rw [he n]
    simpa only [hn] using ht
  · exact Eventually.of_forall fun n => Set.mem_image_of_mem _ (conjugate_mem_convexHull G b u (ha n))

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem baseVector_injective : Function.Injective (baseVector τ) := by
  intro a b h
  apply sub_eq_zero.mp
  apply τ.separating
  change baseVector τ (a-b) = 0
  rw [map_sub, h, sub_self]

omit [CompleteSpace H] in
theorem convex_minimum_unique {K : Set H} (hK : Convex ℝ K) {x y : H}
    (hx : x ∈ K) (hy : y ∈ K) (hmin : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hnorm : ‖y‖ = ‖x‖) : x = y := by
  have hm := hmin ((1/2 : ℝ) • x + (1/2 : ℝ) • y)
    (hK hx hy (by norm_num) (by norm_num) (by norm_num))
  rw [← smul_add, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hm
  have hp := parallelogram_law_with_norm ℂ x y
  have htriangle := norm_add_le x y
  have he : ‖x+y‖ = 2*‖x‖ := by linarith
  rw [he, hnorm] at hp
  have hz : ‖x-y‖ ^ 2 = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem traceOrbitHull_minimum (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) :
    ∃ c : M.toStarSubalgebra, ‖c‖ ≤ ‖b‖ ∧ baseVector τ c ∈ traceOrbitHull τ G b ∧
      (∀ ξ ∈ traceOrbitHull τ G b, τ.norm₂ c ≤ ‖ξ‖) ∧
      (∀ u : G, conjugateLinear u.val c = c) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hK : Convex ℝ (traceOrbitHull τ G b) := (convex_convexHull ℝ _).closure
  obtain ⟨ξ, hξ, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (traceOrbitHull_nonempty τ G b) isClosed_closure.isComplete hK (0 : H)
  obtain ⟨c, hc, rfl⟩ := traceOrbitHull_representative τ G b hξ
  have hle : ∀ z ∈ traceOrbitHull τ G b, τ.norm₂ c ≤ ‖z‖ := by
    intro z hz
    have hi := ciInf_le (show BddBelow (Set.range (fun w : traceOrbitHull τ G b => ‖(0:H)-w.val‖)) from
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩) (⟨z,hz⟩ : traceOrbitHull τ G b)
    rw [← hmin] at hi
    change ‖baseVector τ c‖ ≤ ‖z‖
    simpa only [zero_sub, norm_neg] using hi
  refine ⟨c, hc, hξ, hle, ?_⟩
  intro u
  apply baseVector_injective τ
  apply (convex_minimum_unique hK hξ (conjugate_mem_traceOrbitHull τ G b c u hξ) hle ?_).symm
  exact conjugate_norm₂ τ u.val c

theorem trace_conjugate (u : unitary M.toStarSubalgebra) (b : M.toStarSubalgebra) :
    τ.trace (conjugateLinear u b) = τ.trace b := by
  change τ.trace ((u : M.toStarSubalgebra)*b*star (u : M.toStarSubalgebra)) = _
  rw [τ.trace_mul_comm]
  simp [← mul_assoc]

theorem traceOrbitHull_trace (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra)
    {ξ : H} (hξ : ξ ∈ traceOrbitHull τ G b) : inner ℂ τ.vector ξ = τ.trace b := by
  have hclosed : IsClosed {ξ : H | inner ℂ τ.vector ξ = τ.trace b} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hconv : Convex ℝ {ξ : H | inner ℂ τ.vector ξ = τ.trace b} := by
    intro x hx y hy s t hs ht hst
    change inner ℂ τ.vector (s • x+t • y) = _
    rw [inner_add_right]
    rw [inner_smul_right_eq_smul, inner_smul_right_eq_smul, hx, hy, ← add_smul, hst, one_smul]
  apply (closure_minimal (convexHull_min ?_ hconv) hclosed) hξ
  rintro ξ ⟨a, ⟨u, rfl⟩, rfl⟩
  exact trace_conjugate τ u.val b

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_limit_mul {I : Type*} {l : Filter I}
    (a c : I → M.toStarSubalgebra) (b d : M.toStarSubalgebra)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C)
    (ha : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (c i-d)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (a i*c i-b*d)) l (𝓝 0) := by
  have hbound : ∀ i, τ.norm₂ (a i*c i-b*d) ≤ C*τ.norm₂ (c i-d)+τ.norm₂ (a i-b)*‖d‖ := by
    intro i
    have he : a i*c i-b*d = a i*(c i-d)+(a i-b)*d := by
      simp only [mul_sub,sub_mul]; abel
    rw [he]
    exact (τ.norm₂_add_le _ _).trans (add_le_add
      ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
      (τ.norm₂_mul_le_right _ _))
  apply squeeze_zero (fun i => norm_nonneg _) hbound
  simpa using (hc.const_mul C).add (ha.mul_const ‖d‖)

theorem norm₂_limit_trace {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.trace (a i)) l (𝓝 (τ.trace b)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => ?_) h
  rw [← trace_sub]
  exact τ.norm_trace_le_norm₂ _

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The least-norm unitary-orbit point is scalar when the coordinate inclusion has scalar commutant. -/
section
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem commutes_of_fixed_unitaries (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (c : M.toStarSubalgebra)
    (hc : ∀ u : subalgebraUnitaries P, conjugateLinear u.val c = c) :
    ∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra) := by
  let : CStarAlgebra P := {}
  intro a
  obtain ⟨u, s, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  have hu (i : Fin 4) : ((u i).val : M.toStarSubalgebra)*c = c*((u i).val : M.toStarSubalgebra) := by
    have h := congrArg (fun z : M.toStarSubalgebra => z * ((u i).val : M.toStarSubalgebra)) (hc (ambientUnitary P (u i)))
    change (((u i).val : M.toStarSubalgebra)*c*star ((u i).val : M.toStarSubalgebra))*((u i).val : M.toStarSubalgebra) = _ at h
    have he : star ((u i).val : M.toStarSubalgebra)*((u i).val : M.toStarSubalgebra) = 1 :=
      congrArg Subtype.val (u i).property.1
    simpa only [mul_assoc, he, mul_one] using h
  change P.subtype a*c = c*P.subtype a
  rw [ha, map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, smul_mul_assoc, mul_smul_comm]
  exact congrArg (fun z : M.toStarSubalgebra => s i • z) (hu i)

/-- Irreducibility is exactly the coordinate relative-commutant hypothesis.
Completeness of P is automatic for a von Neumann subalgebra, and is used only
to express its elements as sums of four unitaries. -/
theorem scalar_mem_traceOrbitHull (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hirr : ∀ c : M.toStarSubalgebra, (∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra)) (b : M.toStarSubalgebra) :
    baseVector τ (τ.trace b • (1 : M.toStarSubalgebra)) ∈ traceOrbitHull τ (subalgebraUnitaries P) b := by
  obtain ⟨c, _, hc, _, hfixed⟩ := traceOrbitHull_minimum τ (subalgebraUnitaries P) b
  obtain ⟨z, rfl⟩ := hirr c (commutes_of_fixed_unitaries P c hfixed)
  have hz := traceOrbitHull_trace τ (subalgebraUnitaries P) b hc
  have he : z = τ.trace b := by
    change inner ℂ τ.vector (z • τ.vector) = _ at hz
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, τ.norm_vector] at hz
    simpa using hz
  simpa only [he] using hc

end

/-! Irreducibility excludes disconnected nonzero ambient projections.
This gives the projection part of irreducibility in every nonzero corner. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

theorem baseVector_inner_eq_trace (a b : M.toStarSubalgebra) :
    inner ℂ (baseVector τ a) (baseVector τ b)=τ.trace (star a*b) := by
  change _ = inner ℂ τ.vector (star (a : H →L[ℂ] H) ((b : H →L[ℂ] H) τ.vector))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- A continuous trace test vanishing on an orbit vanishes on its closed
convex hull. -/
theorem orbitHull_trace_test_zero (G : Subgroup (unitary M.toStarSubalgebra))
    (b d : M.toStarSubalgebra)
    (hd : ∀ u : G, τ.trace (star d * conjugateLinear u.val b)=0)
    {ξ : H} (hξ : ξ ∈ traceOrbitHull τ G b) :
    inner ℂ (baseVector τ d) ξ=0 := by
  let K : Set H := {ξ | inner ℂ (baseVector τ d) ξ=0}
  have hc : IsClosed K := isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hv : Convex ℝ K := by
    intro x hx y hy s t hs ht hst
    change inner ℂ (baseVector τ d) (s • x+t • y)=0
    rw [inner_add_right,inner_smul_right_eq_smul,inner_smul_right_eq_smul]
    change s • inner ℂ (baseVector τ d) x+t • inner ℂ (baseVector τ d) y=0
    rw [show inner ℂ (baseVector τ d) x=0 from hx,
      show inner ℂ (baseVector τ d) y=0 from hy,smul_zero,smul_zero,add_zero]
  apply (closure_minimal (convexHull_min ?_ hv) hc) hξ
  rintro _ ⟨a,⟨u,rfl⟩,rfl⟩
  exact (baseVector_inner_eq_trace τ d (conjugateLinear u.val b)).trans (hd u)

include τ hirr in
/-- Nonzero ambient projections cannot have all their P matrix coefficients
zero in an irreducible inclusion. No comparison theorem is assumed. -/
theorem projection_eq_zero_or_eq_zero_of_no_links (r s : AlgebraProjection M)
    (hlink : ∀ a : P, s.val*(a : M.toStarSubalgebra)*r.val=0) :
    r.val=0 ∨ s.val=0 := by
  have htest : ∀ u : subalgebraUnitaries P,
      τ.trace (star s.val*conjugateLinear u.val r.val)=0 := by
    intro u
    change τ.trace (star s.val*((u.val : M.toStarSubalgebra)*r.val*
      star (u.val : M.toStarSubalgebra)))=0
    rw [s.property.isSelfAdjoint.star_eq,← mul_assoc,← mul_assoc,
      hlink ⟨u.val.val,u.property⟩,zero_mul]
    exact inner_zero_right _
  have hz := orbitHull_trace_test_zero τ (subalgebraUnitaries P) r.val s.val htest
    (scalar_mem_traceOrbitHull τ P hirr r.val)
  rw [map_smul,inner_smul_right,baseVector_inner_eq_trace,
    s.property.isSelfAdjoint.star_eq,mul_one] at hz
  rcases mul_eq_zero.mp hz with hr | hs
  · left
    by_contra hn
    have hp := projection_trace_pos τ r.val r.property hn
    rw [hr,Complex.zero_re] at hp
    exact (lt_irrefl 0 hp)
  · right
    by_contra hn
    have hp := projection_trace_pos τ s.val s.property hn
    rw [hs,Complex.zero_re] at hp
    exact (lt_irrefl 0 hp)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialIsometry

theorem trace_support_eq_target (τ : TracialRepresentation M) (v : PartialIsometry M) :
    τ.trace v.support.val=τ.trace v.target.val := by
  rw [← v.initial]
  exact τ.trace_mul_comm _ _

theorem difference_square {v w : PartialIsometry M} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support.val-v.support.val := by
  simp only [star_sub,sub_mul,mul_sub,w.initial,v.initial,
    cross_initial h,cross_initial_rev h,sub_self,sub_zero]

theorem distance_sq (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    τ.norm₂ (w.val-v.val)^2=(τ.trace w.support.val).re-(τ.trace v.support.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul (w.val-v.val))
  rw [difference_square h,trace_sub,Complex.sub_re] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem support_trace_mono (τ : TracialRepresentation M) {v w : PartialIsometry M} (h : v ≤ w) :
    (τ.trace v.support.val).re ≤ (τ.trace w.support.val).re := by
  have he := distance_sq τ h
  nlinarith [sq_nonneg (τ.norm₂ (w.val-v.val))]

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem support_trace_le_one (v : PartialIsometry M) : (τ.trace v.support.val).re ≤ 1 := by
  rw [projection_trace_sq τ _ v.support.property]
  have h := (τ.norm₂_le_norm v.support.val).trans v.support.property.norm_le
  nlinarith [show 0 ≤ τ.norm₂ v.support.val from norm_nonneg _]

theorem monotone_cauchy (a : ℕ → PartialIsometry M) (ha : Monotone a) :
    CauchySeq (fun n => ((a n).val : H →L[ℂ] H) τ.vector) := by
  let t : ℕ → ℝ := fun n => (τ.trace (a n).support.val).re
  have ht : Monotone t := fun i j hij => support_trace_mono τ (ha hij)
  have hb : BddAbove (Set.range t) := ⟨1,by rintro _ ⟨n,rfl⟩; exact support_trace_le_one τ (a n)⟩
  have hc := tendsto_atTop_ciSup ht hb
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc (Ioi_mem_nhds (show (⨆ n, t n)-ε^2 < ⨆ n,t n by nlinarith)))
  refine ⟨N,fun n hn => ?_⟩
  have hupper : t n ≤ ⨆ n,t n := le_ciSup hb n
  have hsmall : (⨆ n,t n)-ε^2 < t N := hN N le_rfl
  have he := distance_sq τ (ha hn)
  change τ.norm₂ ((a n).val-(a N).val)^2=t n-t N at he
  rw [dist_eq_norm]
  change τ.norm₂ ((a n).val-(a N).val)<ε
  nlinarith [show 0 ≤ τ.norm₂ ((a n).val-(a N).val) from norm_nonneg _]

/-- Closedness of actual partial isometries in the operator norm unit ball
for L2 convergence. -/
theorem of_L2_limit (a : ℕ → PartialIsometry M) (b : M.toStarSubalgebra)
    (hb : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0)) :
    ∃ v : PartialIsometry M, v.val=b := by
  let p : M.toStarSubalgebra := star b*b
  have hp : Tendsto (fun n => τ.norm₂ ((a n).support.val-p)) atTop (𝓝 0) := by
    have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
      (star b) b 1 (fun n => (a n).adjoint.norm_le_one)
      (norm₂_limit_star τ _ _ hb) hb
    simpa only [(a _).initial] using ht
  have hproj : IsStarProjection p := by
    constructor
    · have ht := norm₂_limit_mul τ (fun n => (a n).support.val) (fun n => (a n).support.val)
        p p 1 (fun n => (a n).support.property.norm_le) hp hp
      have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-p*p)) atTop (𝓝 0) := by
        simpa only [(a _).support.property.isIdempotentElem.eq] using ht
      exact norm₂_limit_unique τ _ ht' hp
    · change star (star b*b)=star b*b
      simp only [star_mul,star_star]
  exact ⟨⟨⟨p,hproj⟩,b,rfl⟩,rfl⟩

/-- A bounded L2 limit retains every eventually fixed extension. -/
theorem le_of_eventually_le_limit (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, w ≤ a n) : w ≤ v := by
  have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => w.support.val)
    v.val w.support.val 1 (fun n => (a n).norm_le_one) hv
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
  have hc : Tendsto (fun n => τ.norm₂ ((a n).val*w.support.val-w.val)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    rw [show (a n).val*w.support.val=w.val from hn,sub_self,τ.norm₂_zero]
  exact norm₂_limit_unique τ _ ht hc

theorem monotone_limit (a : ℕ → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ n, a n ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete (monotone_cauchy τ a ha)
  obtain ⟨b,hb,hbξ⟩ := bounded_trace_limit τ (fun n => (a n).val) 1 (by norm_num)
    (fun n => (a n).norm_le_one) ξ hξ
  have ht : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ b).mp
    simpa only [hbξ] using hξ
  obtain ⟨v,hv⟩ := of_L2_limit τ a b ht
  rw [← hv] at ht
  refine ⟨v,fun n => ?_,ht⟩
  apply le_of_eventually_le_limit τ a v (a n) ht
  exact (eventually_ge_atTop n).mono (fun m hm => ha hm)

/-! Every nonempty chain of actual partial isometries has an upper bound which
is an L2 limit of a sequence from the chain. This is the analytic chain
construction underlying the projection-comparison Zorn argument. -/

theorem eq_of_le_of_trace_eq {v w : PartialIsometry M} (h : v ≤ w)
    (ht : (τ.trace v.support.val).re=(τ.trace w.support.val).re) : v=w := by
  have he := distance_sq τ h
  rw [ht,sub_self] at he
  have hz := (τ.norm₂_eq_zero_iff _).mp (sq_eq_zero_iff.mp he)
  exact ext (sub_eq_zero.mp hz).symm

theorem support_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => τ.norm₂ ((a n).support.val-v.support.val)) atTop (𝓝 0) := by
  have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
    (star v.val) v.val 1 (fun n => (a n).adjoint.norm_le_one)
    (norm₂_limit_star τ _ _ hv) hv
  simpa only [(a _).initial,v.initial] using ht

theorem support_trace_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => (τ.trace (a n).support.val).re) atTop (𝓝 (τ.trace v.support.val).re) :=
  (Complex.continuous_re.tendsto _).comp (norm₂_limit_trace τ _ _ (support_limit τ a v hv))

theorem limit_le_of_le (a : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ n, a n ≤ w) : v ≤ w := by
  have ht := norm₂_limit_mul τ (fun _ => w.val) (fun n => (a n).support.val)
    w.val v.support.val 1 (fun _ => w.norm_le_one)
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    (support_limit τ a v hv)
  have he : (fun n => w.val*(a n).support.val)=(fun n => (a n).val) := funext hw
  simp only [show ∀ n, w.val*(a n).support.val=(a n).val from hw] at ht
  exact norm₂_limit_unique τ _ ht hv

/-- A nonempty chain has a sequential L2 upper bound; no countability of the
chain and no cyclicity of the trace vector are assumed. -/
theorem chain_limit (c : Set (PartialIsometry M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ (a : ℕ → PartialIsometry M) (v : PartialIsometry M),
      (∀ n, a n ∈ c) ∧ Monotone a ∧ (∀ w ∈ c, w ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  classical
  let t : PartialIsometry M → ℝ := fun v => (τ.trace v.support.val).re
  have hb : BddAbove (t '' c) := ⟨1,by rintro _ ⟨w,hw,rfl⟩; exact support_trace_le_one τ w⟩
  obtain ⟨r,hrmono,hrlim,hrmem⟩ := exists_seq_tendsto_sSup (hne.image t) hb
  choose a hac har using hrmem
  have htotal : ∀ u ∈ c, ∀ v ∈ c, u ≤ v ∨ v ≤ u := by
    intro u hu v hv
    by_cases he : u=v
    · exact Or.inl he.le
    · exact hc hu hv he
  have hmono : Monotone a := by
    intro i j hij
    rcases htotal (a i) (hac i) (a j) (hac j) with h | h
    · exact h
    · have he : t (a j)=t (a i) := le_antisymm (support_trace_mono τ h)
        (by rw [har,har]; exact hrmono hij)
      exact (eq_of_le_of_trace_eq τ h he).symm.le
  obtain ⟨v,hav,hlim⟩ := monotone_limit τ a hmono
  have htv : t v=sSup (t '' c) := by
    apply tendsto_nhds_unique (support_trace_limit τ a v hlim)
    change Tendsto (fun n => t (a n)) atTop (𝓝 (sSup (t '' c)))
    simpa only [har] using hrlim
  refine ⟨a,v,hac,hmono,?_,hlim⟩
  intro w hw
  by_cases hex : ∃ n, w ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (hav n)
  · have haw : ∀ n, a n ≤ w := by
      intro n
      exact (htotal (a n) (hac n) w hw).resolve_right (fun h => hex ⟨n,h⟩)
    have hvw := limit_le_of_le τ a v w hlim haw
    have htw : t w ≤ t v := by rw [htv]; exact le_csSup hb ⟨w,hw,rfl⟩
    have he : t v=t w := le_antisymm (support_trace_mono τ hvw) htw
    exact (eq_of_le_of_trace_eq τ hvw he).symm.le

end PartialIsometry

end

/-! Orthogonal patching with distinct source and target supports. -/

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialIsometry

theorem supports_of_L2_limit (a : ℕ → PartialIsometry M) (v : PartialIsometry M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (p q : AlgebraProjection M)
    (hp : ∀ n, (a n).support ≤ p) (hq : ∀ n, (a n).target ≤ q) :
    v.support ≤ p ∧ v.target ≤ q := by
  constructor
  · apply (v.support_le_iff_mul p).mpr
    have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => p.val)
      v.val p.val 1 (fun n => (a n).norm_le_one) hv
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    have he : ∀ n, (a n).val*p.val=(a n).val := fun n =>
      ((a n).support_le_iff_mul p).mp (hp n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv
  · apply (v.target_le_iff_mul q).mpr
    have ht := norm₂_limit_mul τ (fun _ => q.val) (fun n => (a n).val)
      q.val v.val 1 (fun _ => q.property.norm_le)
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds) hv
    have he : ∀ n, q.val*(a n).val=(a n).val := fun n =>
      ((a n).target_le_iff_mul q).mp (hq n)
    simp only [he] at ht
    exact norm₂_limit_unique τ _ ht hv

include τ in
theorem exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨a,v,ha,_,hcv,hlim⟩ := chain_limit τ c hchain hne
      exact ⟨v,supports_of_L2_limit τ a v hlim p q
        (fun n => (hc (ha n)).1) (fun n => (hc (ha n)).2),hcv⟩
    · refine ⟨zero,⟨?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero coefficient linking two projections produces an actual nonzero
partial isometry between subprojections. Scalar center supplies such coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_nonzero_partialIsometry_between_projections
    (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  classical
  let P : StarSubalgebra ℂ M.toStarSubalgebra := ⊤
  let : CompleteSpace P := isClosed_univ.completeSpace_coe
  have hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hfactor c (fun a => hc ⟨a,StarSubalgebra.mem_top⟩)
  have hex : ∃ a : P, q.val*(a : M.toStarSubalgebra)*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : P, q.val*(a : M.toStarSubalgebra)*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (projection_eq_zero_or_eq_zero_of_no_links τ P hirr p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*(a : M.toStarSubalgebra)*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

end

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hfactor in
theorem exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.exists_maximal_between τ p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      exists_nonzero_partialIsometry_between_projections τ hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

theorem projection_eq_of_le_of_trace_eq {p q : AlgebraProjection M}
    (hpq : p ≤ q) (ht : τ.trace p.val=τ.trace q.val) : p=q := by
  let r : AlgebraProjection M := ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property hpq⟩
  have hz : τ.trace r.val=0 := by
    change τ.trace (q.val-p.val)=0
    rw [trace_sub,ht,sub_self]
  have hr : r.val=0 := by
    by_contra hn
    have hh := projection_trace_pos τ r.val r.property hn
    rw [hz,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  exact Subtype.ext (sub_eq_zero.mp hr).symm

include hfactor in
theorem exists_partialIsometry_of_trace_eq (p q : AlgebraProjection M)
    (ht : τ.trace p.val=τ.trace q.val) :
    ∃ v : M.toStarSubalgebra, star v*v=p.val ∧ v*star v=q.val := by
  obtain ⟨v,hvp,hvq,hfull⟩ := exists_partialIsometry_comparison τ hfactor p q
  have he := v.trace_support_eq_target τ
  have hboth : v.support=p ∧ v.target=q := by
    rcases hfull with hp | hq
    · refine ⟨hp,projection_eq_of_le_of_trace_eq τ hvq ?_⟩
      rw [← he,hp,ht]
    · refine ⟨projection_eq_of_le_of_trace_eq τ hvp ?_,hq⟩
      rw [he,hq,ht]
  exact ⟨v.val,v.initial.trans (congrArg (fun z : AlgebraProjection M => z.val) hboth.1),
    congrArg (fun z : AlgebraProjection M => z.val) hboth.2⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem trace_total : (∑ i, (τ.trace (Q.piece i).val).re) = (τ.trace p.val).re := by
  rw [← Complex.re_sum]
  change (∑ i, coordinateTraceLinear τ (Q.piece i).val).re = _
  rw [← map_sum, Q.total]
  rfl

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

theorem exists_joint_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c d : Fin S.size → ℝ),
      ‖p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val‖ < ε ∧
      ‖p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val‖ < ε := by
  obtain ⟨Q,c,hQfix,hQ,hc⟩ := exists_finite_spectral_approximation_preserving_commutant p a ha ε hε
  obtain ⟨R,d,hRfix,hR,hd⟩ := exists_finite_spectral_approximation_preserving_commutant p b hb ε hε
  have hcross (i : Fin Q.size) (j : Fin R.size) : Commute (Q.piece i).val (R.piece j).val := by
    have hqp : Commute p.val (Q.piece i).val :=
      (hQ p.val hpa.symm (Commute.refl _) i).symm
    exact (hR (Q.piece i).val (hQ b hab hpb i).symm hqp j).symm
  let e := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm
  refine ⟨Q.joint R hcross,fun i => c (e i).1,fun i => d (e i).2,?_,?_⟩
  · have he := Equiv.sum_comp e (fun i => (c i.1 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*a*p.val-∑ i, (c (e i).1 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_left R hcross (fun i => (c i : ℂ))]
    exact hc
  · have he := Equiv.sum_comp e (fun i => (d i.2 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*b*p.val-∑ i, (d (e i).2 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_right R hcross (fun i => (d i : ℂ))]
    exact hd

/-- Complex finite spectral sums are constructed from the joint real and
imaginary approximations. No small pinching-energy premise occurs. -/
theorem exists_complex_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c : Fin S.size → ℂ),
      ‖p.val*(a+Complex.I • b)*p.val-∑ i, c i • (S.piece i).val‖ < ε := by
  obtain ⟨S,c,d,hc,hd⟩ := exists_joint_spectral_approximation p a b ha hb hab hpa hpb
    (ε/2) (half_pos hε)
  refine ⟨S,fun i => (c i : ℂ)+Complex.I*(d i : ℂ),?_⟩
  have he : p.val*(a+Complex.I • b)*p.val-
      (∑ i, ((c i : ℂ)+Complex.I*(d i : ℂ)) • (S.piece i).val) =
      (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)+
        Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val) := by
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_smul,
      mul_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_sub]
    abel
  rw [he]
  have hn := norm_add_le (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)
    (Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val))
  rw [norm_smul,Complex.norm_I,one_mul] at hn
  linarith

end

/-! Finite spectral approximation for an actual normal operator. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_normal_spectral_approximation (x : M.toStarSubalgebra) [IsStarNormal x]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      ‖x-∑ i, c i • (Q.piece i).val‖ < ε := by
  obtain ⟨Q,c,h⟩ := exists_complex_spectral_approximation (identityProjection M)
    (ℜ x) (ℑ x) (ℜ x).property (ℑ x).property (Commute.realPart_imaginaryPart x)
    (Commute.one_left _) (Commute.one_left _) ε hε
  refine ⟨Q,c,?_⟩
  simpa only [identityProjection,one_mul,mul_one,realPart_add_I_smul_imaginaryPart] using h

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem orthogonal_family_sum_projection {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    IsStarProjection (∑ i,(q i).val) := by
  classical
  constructor
  · show (∑ i,(q i).val)*(∑ i,(q i).val)=∑ i,(q i).val
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq i j hji.symm
    · simp
  · show star (∑ i,(q i).val)=∑ i,(q i).val
    simp only [star_sum, (q _).property.isSelfAdjoint.star_eq]

theorem exists_completed_orthogonal_family {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    ∃ Q : CornerPartition (identityProjection M),
      ∃ e : Option ι ≃ Fin Q.size,
        (∀ i,Q.piece (e (some i))=q i) ∧
        (Q.piece (e none)).val=1-∑ i,(q i).val := by
  classical
  let s := ∑ i,(q i).val
  have hs : IsStarProjection s := orthogonal_family_sum_projection q hq
  let a : Option ι → AlgebraProjection M := fun i =>
    i.elim ⟨1-s,hs.one_sub⟩ q
  have hleft (i : ι) : s*(q i).val=(q i).val := by
    dsimp [s]
    rw [Finset.sum_mul,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq j i hji
    · simp
  have hright (i : ι) : (q i).val*s=(q i).val := by
    simpa only [star_mul,hs.isSelfAdjoint.star_eq,
      (q i).property.isSelfAdjoint.star_eq] using congrArg star (hleft i)
  have ha (i j : Option ι) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => change (1-s)*(q j).val=0; rw [sub_mul,one_mul,hleft,sub_self]
    | some i =>
      cases j with
      | none => change (q i).val*(1-s)=0; rw [mul_sub,mul_one,hright,sub_self]
      | some j => exact hq i j (fun h => hij (congrArg some h))
  have ht : (∑ i,(a i).val)=(identityProjection M).val := by
    rw [Fintype.sum_option]
    change (1-s)+s=1
    abel
  let Q := CornerPartition.ofFamily a ha ht
  refine ⟨Q,Fintype.equivFin (Option ι),?_,?_⟩
  · intro i
    change a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) (some i)))=q i
    rw [Equiv.symm_apply_apply]
    rfl
  · change (a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) none))).val=1-s
    rw [Equiv.symm_apply_apply]
    rfl

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockIndices_disjoint {i j : Fin Q.size} (hij : i ≠ j) :
    Disjoint (Q.blockIndices R i) (Q.blockIndices R j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_blockIndices (i : Fin Q.size) :
    (∑ j ∈ Q.blockIndices R i,((Q.refineBlocks R).piece j).val)=(Q.piece i).val := by
  classical
  rw [blockIndices,Finset.sum_filter]
  let e := (Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm
  change (∑ j,if (e j).1=i then ((R (e j).1).piece (e j).2).val else 0)=_
  rw [Equiv.sum_comp e (fun a => if a.1=i then ((R a.1).piece a.2).val else 0),
    Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,(R _).total]
  simp

end CornerPartition

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem exists_matrixUnits_for_partition {p : AlgebraProjection M}
    (Q : CornerPartition p) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Fin Q.size → Fin Q.size → M.toStarSubalgebra,
      (∀ i, E i i=(Q.piece i).val) ∧
      (∀ i j, star (E i j)=E j i) ∧
      (∀ i j k l, E i j*E k l=if j=k then E i l else 0) ∧
      (∑ i, E i i)=p.val := by
  classical
  let o : Fin Q.size := ⟨0,hn⟩
  have hv : ∀ i, ∃ v : M.toStarSubalgebra,
      star v*v=(Q.piece o).val ∧ v*star v=(Q.piece i).val := fun i =>
    exists_partialIsometry_of_trace_eq τ hfactor (Q.piece o) (Q.piece i) (ht o i)
  choose v hvi hvf using hv
  let V (i : Fin Q.size) : PartialIsometry M := ⟨Q.piece o,v i,hvi i⟩
  have htarget (i : Fin Q.size) : (V i).target=Q.piece i := Subtype.ext (hvf i)
  have hcross (i j : Fin Q.size) (hij : i≠j) : star (v i)*v j=0 := by
    exact (V i).adjoint.mul_eq_zero (V j) (by
      change (V i).target.val*(V j).target.val=0
      rw [htarget,htarget]
      exact Q.orthogonal i j hij)
  let E (i j : Fin Q.size) := v i*star (v j)
  refine ⟨E,hvf,?_,?_,?_⟩
  · intro i j
    simp only [E,star_mul,star_star]
  · intro i j k l
    by_cases hjk : j=k
    · subst k
      rw [ite_eq_left rfl]
      change (v i*star (v j))*(v j*star (v l))=v i*star (v l)
      calc _ = (v i*(star (v j)*v j))*star (v l) := by simp only [mul_assoc]
           _ = v i*star (v l) := by
             rw [hvi,show v i*(Q.piece o).val=v i from (V i).mul_support]
    · rw [ite_eq_right hjk]
      change (v i*star (v j))*(v k*star (v l))=0
      calc _ = (v i*(star (v j)*v k))*star (v l) := by simp only [mul_assoc]
           _ = 0 := by rw [hcross j k hjk,mul_zero,zero_mul]
  · simpa only [E,hvf] using Q.total

end Tracial

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_UniformPartitions
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite equal-trace partitions in an actual diffuse algebra, constructed
by repeated exact trace cuts. No matrix units or comparison theorem are
assumed. These partitions do not yet approximate an arbitrary given
spectral partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_uniform_trace_partition (n : ℕ) (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) (ht : τ.trace p.val=((n : ℝ)*r : ℂ)) :
    ∃ Q : CornerPartition p,Q.size=n ∧ ∀ i,τ.trace (Q.piece i).val=(r : ℂ) := by
  induction n generalizing p with
  | zero =>
    have hp0 : p.val=0 := by
      by_contra h
      have hpos := projection_trace_pos τ p.val p.property h
      simp only [Nat.cast_zero,zero_mul,Complex.ofReal_zero] at ht
      rw [ht,Complex.zero_re] at hpos
      exact (lt_irrefl 0 hpos)
    refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_⟩,rfl,fun i => Fin.elim0 i⟩
    simpa only [Finset.univ_eq_empty,Finset.sum_empty] using hp0.symm
  | succ n ih =>
    have hrp : r ≤ (τ.trace p.val).re := by
      have htR := congrArg Complex.re ht
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero,Nat.cast_succ] at htR
      rw [htR]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨q,hq,hpq,hqp,hqt⟩ :=
      exists_exact_trace_subprojection τ hdiff p.val p.property r hr hrp
    let s : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
    have hst : τ.trace s.val=((n : ℝ)*r : ℂ) := by
      change τ.trace (p.val-q)=_
      rw [trace_sub,ht,hqt]
      push_cast
      ring
    obtain ⟨Q,hsize,hQ⟩ := ih s hst
    have hleft (i : Fin Q.size) : q*(Q.piece i).val=0 := by
      have hle : (p.val-q)*(Q.piece i).val=(Q.piece i).val := Q.piece_le i
      calc q*(Q.piece i).val = q*((p.val-q)*(Q.piece i).val) := by rw [hle]
        _ = 0 := by rw [← mul_assoc,mul_sub,hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
    have hright (i : Fin Q.size) : (Q.piece i).val*q=0 := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq,
        (Q.piece i).property.isSelfAdjoint.star_eq,star_zero] using congrArg star (hleft i)
    let a : Fin (Q.size+1) → AlgebraProjection M := Fin.cons ⟨q,hq⟩ Q.piece
    have ha (i j : Fin (Q.size+1)) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact hleft j
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact hright i
        · intro hij
          exact Q.orthogonal i j (fun h => hij (congrArg Fin.succ h))
    have hat : (∑ i,(a i).val)=p.val := by
      rw [Fin.sum_univ_succ]
      change q+(∑ i,(Q.piece i).val)=p.val
      rw [Q.total]
      change q+(p.val-q)=p.val
      abel
    let R : CornerPartition p := ⟨Q.size+1,a,ha,hat⟩
    refine ⟨R,congrArg (fun k => k+1) hsize,?_⟩
    intro i
    exact Fin.cases hqt hQ i

/-! Complete finitely many orthogonal grid-trace projections to an actual
equal-trace unit partition, retaining explicit disjoint groups of pieces. -/

include hdiff in
theorem exists_uniform_trace_extension {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j,i ≠ j → (q i).val*(q j).val=0)
    (n : ℕ) (hn : 0 < n) (m : ι → ℕ) (hm : ∑ i,m i ≤ n)
    (ht : ∀ i,τ.trace (q i).val=(((m i : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ)) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : ι → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        ∀ i,(∑ j ∈ J i,(R.piece j).val)=(q i).val := by
  classical
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  obtain ⟨C,e,he,hrem⟩ := exists_completed_orthogonal_family q hq
  let count : Option ι → ℕ := fun a => a.elim (n-∑ i,m i) m
  have hsum : τ.trace (∑ i,(q i).val)=
      ((((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    change coordinateTraceLinear τ (∑ i,(q i).val)=_
    rw [map_sum]
    change (∑ i,τ.trace (q i).val)=_
    simp only [ht]
    push_cast
    rw [Finset.sum_mul]
  have hc (a : Option ι) : τ.trace (C.piece (e a)).val=
      (((count a : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    cases a with
    | some i => simpa only [he,count,Option.elim_some] using ht i
    | none =>
      rw [hrem,trace_sub,τ.trace_one,hsum]
      dsimp [count]
      rw [Nat.cast_sub hm]
      push_cast
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR
      field_simp
  have hC (j : Fin C.size) : τ.trace (C.piece j).val=
      (((count (e.symm j) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa only [Equiv.apply_symm_apply] using hc (e.symm j)
  choose D hDsize hDt using fun j => exists_uniform_trace_partition τ hdiff
    (count (e.symm j)) (C.piece j) (n : ℝ)⁻¹ (by positivity) (by simpa only [Complex.ofReal_mul] using hC j)
  let R := C.refineBlocks D
  have hRt (j : Fin R.size) : τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact hDt _ _
  have hsize : R.size=n := by
    have htotal := R.trace_total τ
    have heq : (R.size : ℝ)*(n : ℝ)⁻¹=1 := by
      simpa only [hRt,Complex.ofReal_re,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,identityProjection,τ.trace_one,Complex.one_re] using htotal
    have hmul := mul_inv_cancel₀ hnR
    have hreal : (R.size : ℝ)=(n : ℝ) :=
      (mul_right_cancel₀ (inv_ne_zero hnR)) (heq.trans hmul.symm)
    exact_mod_cast hreal
  refine ⟨R,hsize,hRt,fun i => C.blockIndices D (e (some i)),?_,?_⟩
  · intro i j hij
    apply C.blockIndices_disjoint
    intro h
    exact hij (Option.some.inj (e.injective h))
  · intro i
    exact (C.sum_blockIndices D (e (some i))).trans (congrArg Subtype.val (he i))

/-! Quantitative equal-trace approximation by rounding down spectral pieces.
All projections and partitions are constructed in the given diffuse algebra. -/

include hdiff in
theorem exists_rounded_trace_subprojection (p : AlgebraProjection M)
    (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∃ q : AlgebraProjection M, q ≤ p ∧
      τ.trace q.val=(((m : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) ∧
      τ.norm₂ (p.val-q.val)^2 < (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let t := (τ.trace p.val).re
  have ht : 0 ≤ t := by
    dsimp [t]
    rw [projection_trace_sq τ p.val p.property]
    positivity
  let m := ⌊t*(n : ℝ)⌋₊
  have hlow : (m : ℝ)*(n : ℝ)⁻¹ ≤ t := by
    apply (mul_le_mul_iff_left₀ hnR).mp
    have h := Nat.floor_le (mul_nonneg ht hnR.le)
    dsimp [m]
    field_simp
    nlinarith
  have herror : t-(m : ℝ)*(n : ℝ)⁻¹ < (n : ℝ)⁻¹ := by
    have h := Nat.lt_floor_add_one (t*(n : ℝ))
    apply (mul_lt_mul_iff_left₀ hnR).mp
    dsimp [m]
    field_simp
    nlinarith
  obtain ⟨q,hq,hpq,_,hqt⟩ := exists_exact_trace_subprojection τ hdiff p.val p.property
    ((m : ℝ)*(n : ℝ)⁻¹) (by positivity) hlow
  refine ⟨m,⟨q,hq⟩,hpq,hqt,?_⟩
  rw [← projection_trace_sq τ _ (hq.sub_of_mul_eq_right p.property hpq),
    trace_sub,hqt,Complex.sub_re,Complex.ofReal_re]
  exact herror

include hdiff in
theorem exists_uniform_trace_approximation
    (Q : CornerPartition (identityProjection M)) (n : ℕ) (hn : 0 < n) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < (n : ℝ)⁻¹ := by
  classical
  choose m q hle ht herr using fun i => exists_rounded_trace_subprojection τ hdiff (Q.piece i) n hn
  have horth (i j : Fin Q.size) (hij : i ≠ j) : (q i).val*(q j).val=0 :=
    orthogonal_subprojections (Q.orthogonal i j hij) (hle i) (hle j)
  have htracele (i : Fin Q.size) : (m i : ℝ)*(n : ℝ)⁻¹ ≤ (τ.trace (Q.piece i).val).re := by
    have hpos : 0 ≤ (τ.trace ((Q.piece i).val-(q i).val)).re := by
      rw [projection_trace_sq τ _ ((q i).property.sub_of_mul_eq_right (Q.piece i).property (hle i))]
      positivity
    rw [trace_sub,ht,Complex.sub_re,Complex.ofReal_re] at hpos
    linarith
  have hsum : (∑ i,m i : ℕ) ≤ n := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => htracele i)
    rw [Q.trace_total τ] at h
    have hreal : ((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ ≤ 1 := by
      simpa only [Nat.cast_sum,Finset.sum_mul,identityProjection,τ.trace_one,Complex.one_re] using h
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hmul := mul_inv_cancel₀ (ne_of_gt hnR)
    have hbound : ((∑ i,m i : ℕ) : ℝ) ≤ (n : ℝ) :=
      (mul_le_mul_iff_left₀ (inv_pos.mpr hnR)).mp (hreal.trans_eq hmul.symm)
    exact_mod_cast hbound
  obtain ⟨R,hsize,hRt,J,hJdis,hJsum⟩ := exists_uniform_trace_extension τ hdiff q horth n hn m hsum ht
  refine ⟨R,hsize,hRt,J,hJdis,?_,?_⟩
  · intro i
    rw [hJsum]
    exact hle i
  · intro i
    rw [hJsum]
    exact herr i

include hdiff in
theorem exists_dyadic_trace_approximation
    (Q : CornerPartition (identityProjection M)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < ε := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk' : (((2^k : ℕ) : ℝ)⁻¹ : ℝ) < ε := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hk
  obtain ⟨R,hsize,ht,J,hd,hle,herr⟩ := exists_uniform_trace_approximation τ hdiff Q (2^k) (by positivity)
  exact ⟨k,R,hsize,ht,J,hd,hle,fun i => (herr i).trans hk'⟩

end

/-! A finite commuting self-adjoint family admits simultaneous L2 spectral
approximation on one constructed dyadic equal-trace partition. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_finset_sum_le {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) :
    τ.norm₂ (∑ i ∈ F,x i) ≤ ∑ i ∈ F,τ.norm₂ (x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (τ.norm₂_add_le _ _).trans (add_le_add le_rfl ih)

variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_dyadic_spectral_sum_approximation {ι : Type*} [Fintype ι]
    (Q : CornerPartition (identityProjection M)) (c : ι → Fin Q.size → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ d : ι → Fin R.size → ℂ, ∀ i,
        τ.norm₂ ((∑ l,c i l • (Q.piece l).val)-∑ j,d i j • (R.piece j).val) < ε := by
  classical
  let A : ℝ := ∑ i,∑ l,‖c i l‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ := ε/(A+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : A*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < A+1)).mpr
    nlinarith
  obtain ⟨k,R,hsize,ht,J,_,_,herr⟩ := exists_dyadic_trace_approximation τ hdiff Q (δ^2) (sq_pos_of_pos hδ)
  let d : ι → Fin R.size → ℂ := fun i j => ∑ l,if j ∈ J l then c i l else 0
  have hd (i : ι) : (∑ j,d i j • (R.piece j).val)=
      ∑ l,c i l • (∑ j ∈ J l,(R.piece j).val) := by
    simp only [d,Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
    simp only [ite_smul,zero_smul]
    simp
  have herr' (l : Fin Q.size) :
      τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) ≤ δ := by
    have h := herr l
    have hnonneg : 0 ≤ τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) := norm_nonneg _
    nlinarith
  refine ⟨k,R,hsize,ht,d,?_⟩
  intro i
  rw [hd,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    τ.norm₂ (∑ l,c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) ≤
        ∑ l,τ.norm₂ (c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) :=
      norm₂_finset_sum_le τ Finset.univ _
    _ ≤ ∑ l,‖c i l‖*δ := by
      apply Finset.sum_le_sum
      intro l _
      rw [τ.norm₂_smul]
      exact mul_le_mul_of_nonneg_left (herr' l) (norm_nonneg _)
    _ = (∑ l,‖c i l‖)*δ := (Finset.sum_mul _ _ _).symm
    _ ≤ A*δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _)) (Finset.mem_univ i)
    _ < ε := hsmall

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/
namespace Tracial
open scoped BigOperators

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_normal_matrix_approximation_q129_oai
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (x : M.toStarSubalgebra) [IsStarNormal x] (ε : ℝ) (hε : 0 < ε) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) M.toStarSubalgebra,
      ∃ c : Fin n → ℂ,τ.norm₂ (x-∑ j,c j • E.entry j j) < ε := by
  obtain ⟨Q,c,hc⟩ := exists_normal_spectral_approximation x (ε/2) (by positivity)
  obtain ⟨k,R,hn,ht,d,hd⟩ := exists_dyadic_spectral_sum_approximation τ hdiff Q
    (fun _ : Unit => c) (ε/2) (by positivity)
  obtain ⟨E,hdiag,hstar,hmul,hsum⟩ := exists_matrixUnits_for_partition τ hfactor R
    (by rw [hn]; positivity) (fun i j => (ht i).trans (ht j).symm)
  let F : MatrixUnitSystem (Fin R.size) M.toStarSubalgebra := ⟨E,hstar,hmul,hsum⟩
  refine ⟨k,R.size,hn,F,d (),?_⟩
  change τ.norm₂ (x-∑ j,d () j • E j j) < ε
  simp only [hdiag]
  have he : x-∑ j,d () j • (R.piece j).val =
      (x-∑ i,c i • (Q.piece i).val)+
      ((∑ i,c i • (Q.piece i).val)-∑ j,d () j • (R.piece j).val) := by abel
  rw [he]
  exact (τ.norm₂_add_le _ _).trans_lt (by
    have h₁ := (τ.norm₂_le_norm _).trans_lt hc
    have h₂ := hd ()
    linarith)

end

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_normal_matrix_approximation_q129_oai.{u_1} := @OAI.Generator.Tracial.exists_normal_matrix_approximation_q129_oai.{u_1}
