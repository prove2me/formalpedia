-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_matrixUnits_for_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:08:38.506286+00:00
-- url     : https://prove2.me/submissions/f29ba960-50e9-4307-86cc-6fbac5ab43df

import Mathlib
import Definitions.Def_OAIQ11Fg009
import Definitions.Def_OAIQ11Fg010

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialIsometries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
theorem exists_matrixUnits_for_partition_oai {p : AlgebraProjection M}
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

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_matrixUnits_for_partition_oai.{u_1} := @OAI.Generator.Tracial.exists_matrixUnits_for_partition_oai.{u_1}
