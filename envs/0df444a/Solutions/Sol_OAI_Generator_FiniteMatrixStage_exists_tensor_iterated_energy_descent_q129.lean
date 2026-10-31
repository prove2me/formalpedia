-- Prove2me | solution 1 for OAI.Generator.FiniteMatrixStage.exists_tensor_iterated_energy_descent_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:21:05.946119+00:00
-- url     : https://prove2.me/submissions/ac3eed09-42b5-43d0-9811-2f2abee15688

import Mathlib
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_exists_normal_matrix_approximation_q129

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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
-- module Solutions.OAIQ129_RG2.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

theorem insideAlgebra_closed : IsClosed (insideAlgebra (M := M) (P := P) : Set M.toStarSubalgebra) :=
  (base_norm_closed P).preimage continuous_subtype_val

instance insideAlgebra_complete : CompleteSpace (insideAlgebra (M := M) (P := P)) :=
  (insideAlgebra_closed (M := M) (P := P)).completeSpace_coe

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.traceCyclicOperator_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
variable (hx : TraceOrthogonal τ P x)
include hx

theorem trace_zero : τ.trace x=0 := by simpa using hx (1 : P)

end TraceOrthogonal

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_EnergyDescent
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Quantitative descent for a finite spectral pinching, and actual unitary
displacement from irreducibility. A compatible spectral partition in a
residual corner is not postulated as a local-quantization theorem. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- The strict displacement used before finite spectral approximation in
Popa A.1.1, Step 1, in the scalar-commutant case. -/
theorem exists_strict_centered_displacement
    (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, (a : M.toStarSubalgebra)*c = c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ, c = z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x = 0) :
    ∃ u : subalgebraUnitaries P, τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
  by_contra hn
  push Not at hn
  let K : Set H := {ξ | τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re}
  have hclosed : IsClosed K := isClosed_le continuous_const
    (Complex.continuous_re.comp (continuous_const.inner continuous_id))
  have hconv : Convex ℝ K := by
    intro ξ hξ η hη s t hs ht' hst
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (s • ξ+t • η)).re
    simp only [inner_add_right, inner_smul_right_eq_smul, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) ξ).re at hξ
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) η).re at hη
    nlinarith [mul_le_mul_of_nonneg_left hξ hs, mul_le_mul_of_nonneg_left hη ht']
  have horbit : baseVector τ '' algebraOrbit (subalgebraUnitaries P) x ⊆ K := by
    rintro ξ ⟨a,⟨u,rfl⟩,rfl⟩
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hn u) 2
    change τ.norm₂ (conjugateLinear u.val x-x)^2 ≤ τ.norm₂ x^2 at hsq
    have hid := norm_sub_sq (𝕜 := ℂ) (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)
    change τ.norm₂ (conjugateLinear u.val x-x)^2 = τ.norm₂ (conjugateLinear u.val x)^2 -
      2*(inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re + τ.norm₂ x^2 at hid
    rw [conjugate_norm₂] at hid
    have hisym : (inner ℂ (baseVector τ (conjugateLinear u.val x)) (baseVector τ x)).re =
        (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [hisym] at hid
    change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) (baseVector τ (conjugateLinear u.val x))).re
    linarith
  have hz : (0 : H) ∈ traceOrbitHull τ (subalgebraUnitaries P) x := by
    simpa only [ht, zero_smul, map_zero] using scalar_mem_traceOrbitHull τ P hirr x
  have hzero := (closure_minimal (convexHull_min horbit hconv) hclosed) hz
  change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) 0).re at hzero
  rw [inner_zero_right, Complex.zero_re] at hzero
  have hpos : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero (fun he => hx ((τ.norm₂_eq_zero_iff x).mp he))
  linarith

theorem displacement_le_commutator (u : unitary M.toStarSubalgebra)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conjugateLinear u x-x) ≤ τ.norm₂ ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra)) := by
  have he : conjugateLinear u x-x=
      ((u : M.toStarSubalgebra)*x-x*(u : M.toStarSubalgebra))*star (u : M.toStarSubalgebra) := by
    change (u : M.toStarSubalgebra)*x*star (u : M.toStarSubalgebra)-x=_
    rw [sub_mul,mul_assoc x,u.property.2,mul_one]
  rw [he]
  exact (τ.norm₂_mul_le_right _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _)
      (unitary_norm_le _ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))

end

/-! The one-step energy decrease has pieces in the prescribed von Neumann
subalgebra. Irreducibility supplies the unitary, not an assumed energy budget. -/

/-! Strict displacement from zero in the actual closed convex orbit hull,
without imposing a scalar commutant on a block diagonal algebra. -/

/-! Actual compatible 63/64 descent for the orthogonal component of Popa
A.1.1 in an irreducible inclusion. Both displacement and finite spectral
partitions are constructed, and all pieces remain in the prescribed N. -/

/-! Geometric iteration and finite-family small-energy partitions for the
orthogonal component. No energy budget or block displacement is assumed. -/

/-! Assembly of the orthogonal budget with an explicitly controlled
subalgebra component. This constructs the further refinement; constructing
the initial subalgebra-component budget is not asserted here. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_fixed (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : x.val ∈ N) :
    conditionalExpectation τ hNM x=x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM x x hx
  intro a
  simp only [sub_self,mul_zero]
  exact inner_zero_right _

theorem conditionalExpectation_trace (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.trace (conditionalExpectation τ hNM x)=τ.trace x := by
  have h := (conditionalExpectation_orthogonal τ hNM x).trace_zero τ
  rw [trace_sub,sub_eq_zero] at h
  exact h.symm

theorem conditionalExpectation_selfAdjoint (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (conditionalExpectation τ hNM x) ∧ ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  obtain ⟨c,hc,hn,ho⟩ := exists_selfAdjoint_expectation τ hNM x hx
  rw [conditionalExpectation_eq_of_orthogonal τ hNM x (coordinateInclusion hNM c) c.property ho]
  exact ⟨included_selfAdjoint hNM c hc,hn⟩

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem expectation_trace_adjoint (x : M.toStarSubalgebra) : τ.trace (star x)=star (τ.trace x) := by
  change τ.trace (star x)=(starRingEnd ℂ) (τ.trace x)
  have h := inner_conj_symm (𝕜 := ℂ) (baseVector τ x) (baseVector τ 1)
  simpa only [baseVector_inner_trace,star_one,one_mul,mul_one] using h.symm

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x : M.toStarSubalgebra}
theorem mul_left (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (a*x) := by
  intro b
  exact mul_assoc (b : M.toStarSubalgebra) a x ▸ hx ⟨(b : M.toStarSubalgebra)*a,P.mul_mem b.property ha⟩
theorem mul_right (hx : TraceOrthogonal τ P x) (a : M.toStarSubalgebra) (ha : a ∈ P) :
    TraceOrthogonal τ P (x*a) := by
  intro b
  rw [← mul_assoc,τ.trace_mul_comm,← mul_assoc]
  exact hx ⟨a*(b : M.toStarSubalgebra),P.mul_mem ha b.property⟩
theorem adjoint (hx : TraceOrthogonal τ P x) : TraceOrthogonal τ P (star x) := by
  intro a
  have h := congrArg star (hx ⟨star (a : M.toStarSubalgebra),P.star_mem' a.property⟩)
  change star (τ.trace (star (a : M.toStarSubalgebra)*x))=star (0 : ℂ) at h
  rw [← expectation_trace_adjoint,star_mul,star_star,star_zero,τ.trace_mul_comm] at h
  exact h
end TraceOrthogonal

theorem conditionalExpectation_mul_left (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (a*x)=a*conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem ha (conditionalExpectation_mem τ hNM x)
  · simpa only [mul_sub] using (conditionalExpectation_orthogonal τ hNM x).mul_left τ a ha

theorem conditionalExpectation_mul_right (hNM : N ≤ M) (a x : M.toStarSubalgebra)
    (ha : a.val ∈ N) : conditionalExpectation τ hNM (x*a)=conditionalExpectation τ hNM x*a := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact N.mul_mem (conditionalExpectation_mem τ hNM x) ha
  · simpa only [sub_mul] using (conditionalExpectation_orthogonal τ hNM x).mul_right τ a ha

theorem conditionalExpectation_star (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (star x)=star (conditionalExpectation τ hNM x) := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact star_mem (conditionalExpectation_mem τ hNM x)
  · simpa only [star_sub] using (conditionalExpectation_orthogonal τ hNM x).adjoint τ

theorem conditionalExpectation_pythagoras (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (x-conditionalExpectation τ hNM x)^2=τ.norm₂ x^2 := by
  have ho := conditionalExpectation_orthogonal τ hNM x
    ⟨star (conditionalExpectation τ hNM x),star_mem (conditionalExpectation_mem τ hNM x)⟩
  have hi : inner ℂ (baseVector τ (conditionalExpectation τ hNM x))
      (baseVector τ (x-conditionalExpectation τ hNM x))=0 := by
    rw [baseVector_inner_trace]; exact ho
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  rw [← map_add,add_sub_cancel] at h
  change τ.norm₂ x*τ.norm₂ x=τ.norm₂ (conditionalExpectation τ hNM x)*τ.norm₂ (conditionalExpectation τ hNM x)+
    τ.norm₂ (x-conditionalExpectation τ hNM x)*τ.norm₂ (x-conditionalExpectation τ hNM x) at h
  simpa only [pow_two] using h.symm

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
attribute [local instance] OAI.Generator.Tracial.expectationPosCStar
attribute [local instance] OAI.Generator.Tracial.expectationPosOrder
local instance expectationPosPreorder_r1d285f_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.expectationPosLE
local instance expectationPosStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem negPart_mem_inside (c : M.toStarSubalgebra) (hc : c.val ∈ N) :
    c⁻ ∈ insideAlgebra (M := M) (P := N) := by
  rw [CFC.negPart_def,cfcₙ_eq_cfc]
  let : IsClosed (insideAlgebra (M := M) (P := N) : Set M.toStarSubalgebra) :=
    insideAlgebra_closed (M := M) (P := N)
  exact cfc_mem (𝕜' := ℂ) (s := insideAlgebra (M := M) (P := N)) (fun t : ℝ => t⁻) hc

theorem conditionalExpectation_nonneg (hNM : N ≤ M) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ conditionalExpectation τ hNM x := by
  let c := conditionalExpectation τ hNM x
  have hc : IsSelfAdjoint c := (conditionalExpectation_selfAdjoint τ hNM x hx.isSelfAdjoint).1
  have hd := CFC.negPart_nonneg c
  have hmem := negPart_mem_inside c (conditionalExpectation_mem τ hNM x)
  have ho := conditionalExpectation_orthogonal τ hNM x ⟨c⁻,hmem⟩
  change τ.trace (c⁻*(x-c))=0 at ho
  rw [mul_sub,trace_sub,sub_eq_zero] at ho
  have hprod : c⁻*c= -(c⁻*c⁻) := by
    nth_rw 2 [← CFC.posPart_sub_negPart c hc]
    rw [mul_sub,CFC.negPart_mul_posPart,zero_sub]
  have hp := trace_mul_nonneg τ c⁻ x hd hx
  rw [ho,hprod] at hp
  have htrace : τ.trace (-(c⁻*c⁻))= -τ.trace (c⁻*c⁻) := map_neg (coordinateTraceLinear τ) _
  have hsq : (τ.trace (c⁻*c⁻)).re=τ.norm₂ c⁻^2 := by
    rw [norm₂_sq_trace τ,hd.isSelfAdjoint.star_eq]
  rw [htrace,Complex.neg_re,hsq] at hp
  have hz := (τ.norm₂_eq_zero_iff c⁻).mp (sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (τ.norm₂ c⁻)]))
  exact (CFC.negPart_eq_zero_iff c hc).mp hz

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
attribute [local instance] OAI.Generator.Tracial.expectationContractiveCStar
attribute [local instance] OAI.Generator.Tracial.expectationContractiveOrder
attribute [local instance] OAI.Generator.Tracial.expectationContractivePreorder
attribute [local instance] OAI.Generator.Tracial.expectationContractiveLE
local instance expectationContractiveStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem conditionalExpectation_schwarz (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    star (conditionalExpectation τ hNM x)*conditionalExpectation τ hNM x ≤
      conditionalExpectation τ hNM (star x*x) := by
  let y := conditionalExpectation τ hNM x
  have hy : y.val ∈ N := conditionalExpectation_mem τ hNM x
  have hys : (star y).val ∈ N := star_mem hy
  have hp := conditionalExpectation_nonneg τ hNM (star (x-y)*(x-y)) (star_mul_self_nonneg _)
  have he : conditionalExpectation τ hNM (star (x-y)*(x-y))=
      conditionalExpectation τ hNM (star x*x)-star y*y := by
    simp only [star_sub,sub_mul,mul_sub]
    change conditionalExpectationCLM τ hNM _= _
    rw [map_sub,map_sub,map_sub]
    change conditionalExpectation τ hNM (star x*x)-conditionalExpectation τ hNM (star y*x)-
      (conditionalExpectation τ hNM (star x*y)-conditionalExpectation τ hNM (star y*y))= _
    rw [conditionalExpectation_mul_right τ hNM y (star x) hy,
      conditionalExpectation_star τ hNM,
      conditionalExpectation_mul_left τ hNM (star y) x hys,
      conditionalExpectation_fixed τ hNM (star y*y) (N.mul_mem hys hy)]
    change conditionalExpectation τ hNM (star x*x)-star y*y-(star y*y-star y*y)=
      conditionalExpectation τ hNM (star x*x)-star y*y
    abel
  rw [he] at hp
  exact sub_nonneg.mp hp

theorem conditionalExpectation_norm_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    ‖conditionalExpectation τ hNM x‖ ≤ ‖x‖ := by
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (conditionalExpectation_schwarz τ hNM x) (star_mul_self_nonneg (conditionalExpectation τ hNM x))
  have hn := (conditionalExpectation_selfAdjoint τ hNM (star x*x)
    (star_mul_self_nonneg x).isSelfAdjoint).2
  rw [CStarRing.norm_star_mul_self] at h hn
  nlinarith [norm_nonneg x,norm_nonneg (conditionalExpectation τ hNM x)]

end

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_tower (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    conditionalExpectation τ hNM (conditionalExpectation τ hPM x)=conditionalExpectation τ hNM x := by
  apply conditionalExpectation_eq_of_orthogonal τ hNM
  · exact conditionalExpectation_mem τ hNM x
  · have hP : TraceOrthogonal τ (insideAlgebra (M := M) (P := N))
        (x-conditionalExpectation τ hPM x) := by
      intro a
      exact conditionalExpectation_orthogonal τ hPM x
        ⟨(a : M.toStarSubalgebra),hNP a.property⟩
    have h := (conditionalExpectation_orthogonal τ hNM x).sub τ hP
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    abel

theorem conditionalExpectation_nested_energy (hNM : N ≤ M) (hPM : P ≤ M) (hNP : N ≤ P)
    (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x)^2+
      τ.norm₂ (conditionalExpectation τ hPM x-conditionalExpectation τ hNM x)^2=
        τ.norm₂ (conditionalExpectation τ hPM x)^2 := by
  have h := conditionalExpectation_pythagoras τ hNM (conditionalExpectation τ hPM x)
  rwa [conditionalExpectation_tower τ hNM hPM hNP x] at h

end

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129UMul _root_.OAI.UltrapowerBridge.q129UOne _root_.OAI.UltrapowerBridge.q129UStar _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

theorem mem_algebra (x : A) : x ∈ E.algebra ↔
    ∃ a : Matrix ι ι ℂ, (∑ i, ∑ j, a i j • E.entry i j) = x := Iff.rfl

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

theorem commute_algebra_iff (x : A) :
    (∀ a ∈ E.algebra, Commute a x) ↔ ∀ i j, Commute (E.entry i j) x := by
  constructor
  · exact fun h i j => h _ (E.entry_mem i j)
  · intro h a ha
    obtain ⟨b,rfl⟩ := (E.mem_algebra a).mp ha
    show (∑ i, ∑ j, b i j • E.entry i j)*x=x*(∑ i, ∑ j, b i j • E.entry i j)
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      (h _ _).eq]

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

omit [StarModule ℂ A] in
theorem product_entry (a b : ι × κ) :
    (E.product F hc).entry a b = E.entry a.1 b.1 * F.entry a.2 b.2 := rfl

omit [StarModule ℂ A] in
theorem product_sum_left (i j : ι) :
    (∑ k, (E.product F hc).entry (i,k) (j,k)) = E.entry i j := by
  simp only [product_entry, ← Finset.mul_sum, F.total, mul_one]

omit [StarModule ℂ A] in
theorem product_sum_right (k l : κ) :
    (∑ i, (E.product F hc).entry (i,k) (i,l)) = F.entry k l := by
  simp only [product_entry, ← Finset.sum_mul, E.total, one_mul]

theorem algebra_le_product_left : E.algebra ≤ (E.product F hc).algebra := by
  apply (E.algebra_le_iff _).mpr
  intro i j
  rw [← E.product_sum_left F hc i j]
  exact (E.product F hc).algebra.sum_mem fun k _ => (E.product F hc).entry_mem _ _

theorem algebra_le_product_right : F.algebra ≤ (E.product F hc).algebra := by
  apply (F.algebra_le_iff _).mpr
  intro k l
  rw [← E.product_sum_right F hc k l]
  exact (E.product F hc).algebra.sum_mem fun i _ => (E.product F hc).entry_mem _ _

theorem product_algebra_eq_sup : (E.product F hc).algebra = E.algebra ⊔ F.algebra := by
  apply le_antisymm
  · apply ((E.product F hc).algebra_le_iff _).mpr
    intro a b
    exact (E.algebra ⊔ F.algebra).mul_mem ((show E.algebra ≤ E.algebra ⊔ F.algebra from le_sup_left) (E.entry_mem a.1 b.1))
      ((show F.algebra ≤ E.algebra ⊔ F.algebra from le_sup_right) (F.entry_mem a.2 b.2))
  · exact sup_le (E.algebra_le_product_left F hc) (E.algebra_le_product_right F hc)

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem entry_mul_amplify (o i j : ι) (x : A) :
    E.entry i j * E.amplify o x = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.mul_sum,← mul_assoc,E.mul_entry]
  simp [ite_mul]

omit [StarModule ℂ A] in
theorem amplify_mul_entry (o i j : ι) (x : A) :
    E.amplify o x * E.entry i j = E.entry i o*x*E.entry o j := by
  simp only [amplify,Finset.sum_mul,mul_assoc,E.mul_entry]
  simp [mul_ite]

theorem amplify_mem (o : ι) (x : A) : E.amplify o x ∈ E.commutant := by
  intro i j
  show E.entry i j * E.amplify o x = E.amplify o x * E.entry i j
  rw [E.entry_mul_amplify,E.amplify_mul_entry]

omit [StarModule ℂ A] in
theorem amplify_star (o : ι) (x : A) : star (E.amplify o x)=E.amplify o (star x) := by
  simp only [amplify,star_sum,star_mul,E.star_entry,mul_assoc]

omit [StarModule ℂ A] in
theorem amplify_zero (o : ι) : E.amplify o 0=0 := by simp [amplify]

omit [StarModule ℂ A] in
theorem amplify_corner (o i j : ι) (x : A) :
    E.entry i o*E.amplify o x*E.entry o j = E.entry i o*x*E.entry o j := by
  rw [E.entry_mul_amplify]
  simp only [mul_assoc,E.mul_entry,ite_true, if_true]

omit [StarModule ℂ A] in
theorem amplify_mul (o : ι) (x y : A) :
    E.amplify o x*E.amplify o y=E.amplify o (x*E.entry o o*y) := by
  simp only [amplify,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (E.entry i o*x*E.entry o i)*E.amplify o y = _
  rw [mul_assoc,E.entry_mul_amplify]
  simp only [mul_assoc]

theorem amplify_compression (o : ι) (x : A) (hx : x ∈ E.commutant) :
    E.amplify o (E.entry o o*x)=x := by
  simp only [amplify]
  calc _ = ∑ i, E.entry i i*x := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [← mul_assoc,E.mul_entry,ite_eq_left rfl,mul_assoc,← (hx o i).eq,
               ← mul_assoc,E.mul_entry,ite_eq_left rfl]
       _ = x := by rw [← Finset.sum_mul,E.total,one_mul]

omit [StarModule ℂ A] in
theorem reconstruct (o : ι) (x : A) :
    (∑ i, ∑ j, E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j)=x := by
  simp only [E.amplify_corner]
  have h (i j : ι) : E.entry i o*(E.entry o i*x*E.entry j o)*E.entry o j=
      E.entry i i*x*E.entry j j := by
    calc _ = (E.entry i o*E.entry o i)*x*(E.entry j o*E.entry o j) := by
               simp only [mul_assoc]
         _ = _ := by simp only [E.mul_entry,ite_true, if_true]
  simp only [h,← Finset.mul_sum,E.total,mul_one,← Finset.sum_mul,one_mul]

/-- The commutant of a full unital matrix algebra in a scalar-center algebra
has scalar center. The finite matrix decomposition is constructed above. -/
theorem commutant_scalar_center (o : ι)
    (hfactor : ∀ c : A, (∀ a : A,a*c=c*a) → ∃ z : ℂ,c=z • (1 : A))
    (c : E.commutant) (hc : ∀ a : E.commutant,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.commutant) := by
  obtain ⟨z,hz⟩ := hfactor c.val (by
    intro x
    have h (i j : ι) : Commute
        (E.entry i o*E.amplify o (E.entry o i*x*E.entry j o)*E.entry o j) c.val := by
      have hm : Commute (E.amplify o (E.entry o i*x*E.entry j o)) c.val :=
        congrArg Subtype.val (hc ⟨_,E.amplify_mem o _⟩)
      exact ((c.property i o).mul_left hm).mul_left (c.property o j)
    rw [← E.reconstruct o x]
    simp only [Finset.sum_mul,Finset.mul_sum,(h _ _).eq])
  exact ⟨z,Subtype.ext hz⟩

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

omit [StarModule ℂ A] in
theorem amplify_projection (o : ι) (q : A) (hq : IsStarProjection q)
    (hs : q*E.entry o o=q) : IsStarProjection (E.amplify o q) := by
  constructor
  · show E.amplify o q*E.amplify o q=E.amplify o q
    rw [E.amplify_mul,hs,hq.isIdempotentElem.eq]
  · show star (E.amplify o q)=E.amplify o q
    rw [E.amplify_star,hq.isSelfAdjoint.star_eq]

theorem commutant_diffuse (o : ι)
    (hdiff : ∀ p : A,IsStarProjection p → p ≠ 0 →
      ∃ q : A,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.commutant) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.commutant,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  have hpA : IsStarProjection p.val := hp.map E.commutant.subtype
  let r : A := E.entry o o*p.val
  have hr : IsStarProjection r := (E.diagonal_projection o).mul hpA (p.property o o)
  have hr0 : r ≠ 0 := by
    intro h
    have he := E.amplify_compression o p.val p.property
    rw [show E.entry o o*p.val=0 from h,E.amplify_zero] at he
    exact hp0 (Subtype.ext he.symm)
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff r hr hr0
  have hqs : q*E.entry o o=q := by
    have hre : r*E.entry o o=r := by
      dsimp [r]
      rw [mul_assoc,← (p.property o o).eq,← mul_assoc,
        (E.diagonal_projection o).isIdempotentElem.eq]
    calc q*E.entry o o = (q*r)*E.entry o o := by rw [hqr']
         _ = q*r := by rw [mul_assoc,hre]
         _ = q := hqr'
  have hsq : E.entry o o*q=q := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,E.star_entry] using congrArg star hqs
  let Q : E.commutant := ⟨E.amplify o q,E.amplify_mem o q⟩
  have hQ : IsStarProjection Q := by
    constructor
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isIdempotentElem.eq
    · exact Subtype.ext (E.amplify_projection o q hq hqs).isSelfAdjoint.star_eq
  have hrec : E.entry o o*Q.val*E.entry o o=q := by
    change E.entry o o*E.amplify o q*E.entry o o=q
    rw [E.amplify_corner,hsq,hqs]
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro h
    have hz : Q.val=0 := congrArg Subtype.val h
    rw [hz,mul_zero,zero_mul] at hrec
    exact hq0 hrec.symm
  · intro h
    have hz : Q.val=p.val := congrArg Subtype.val h
    rw [hz,mul_assoc,← (p.property o o).eq,← mul_assoc,
      (E.diagonal_projection o).isIdempotentElem.eq] at hrec
    exact hqr hrec.symm
  · apply Subtype.ext
    change p.val*E.amplify o q=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul]
    congr 1
    rw [mul_assoc,hsq]
    exact hrq
  · apply Subtype.ext
    change E.amplify o q*p.val=E.amplify o q
    rw [← E.amplify_compression o p.val p.property,E.amplify_mul,hqs]
    exact congrArg (E.amplify o) hqr'

open scoped BigOperators

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

theorem relative_scalar_center (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.relativeVonNeumann.toStarSubalgebra) := by
  obtain ⟨z,hz⟩ := E.commutant_scalar_center o hfactor (E.relativeEquiv.symm c) (by
    intro a
    apply E.relativeEquiv.injective
    change E.relativeEquiv (a*E.relativeEquiv.symm c)=
      E.relativeEquiv (E.relativeEquiv.symm c*a)
    rw [map_mul,map_mul,E.relativeEquiv.apply_symm_apply]
    exact hc (E.relativeEquiv a))
  refine ⟨z,?_⟩
  have h := congrArg E.relativeEquiv hz
  simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using h

theorem relative_diffuse (o : ι)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.relativeVonNeumann.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.relativeVonNeumann.toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := E.commutant_diffuse o hdiff
    (E.relativeEquiv.symm p) (hp.map E.relativeEquiv.symm) (by
      intro h
      apply hp0
      simpa using congrArg E.relativeEquiv h)
  refine ⟨E.relativeEquiv q,?_,?_,?_,?_,?_⟩
  · exact hq.map E.relativeEquiv.toStarAlgHom
  · intro h
    apply hq0
    exact E.relativeEquiv.injective (h.trans (map_zero E.relativeEquiv).symm)
  · intro h
    apply hqp
    exact E.relativeEquiv.injective (h.trans (E.relativeEquiv.apply_symm_apply p).symm)
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hpq
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hqp'

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem commute_mapped_of_amplify (E : MatrixUnitSystem ι A) (o : ι)
    (f : A →⋆ₐ[ℂ] B) (y : B)
    (hE : ∀ i j,Commute (f (E.entry i j)) y)
    (hamp : ∀ a : A,Commute (f (E.amplify o a)) y) (x : A) : Commute (f x) y := by
  rw [← E.reconstruct o x,map_sum]
  apply Commute.sum_left
  intro i hi
  rw [map_sum]
  apply Commute.sum_left
  intro j hj
  rw [map_mul,map_mul]
  exact ((hE i o).mul_left (hamp _)).mul_left (hE o j)

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem ι N.toStarSubalgebra) (hNM : N ≤ M)

theorem relative_irreducible (o : ι)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
        ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,
      coordinateInclusion (E.relative_inclusion hNM) a*c=
        c*coordinateInclusion (E.relative_inclusion hNM) a) :
    ∃ z : ℂ,c=z • (1 : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra) := by
  let F := E.map (coordinateInclusion hNM)
  let cM := coordinateInclusion F.relativeVonNeumann_le c
  have hentries : ∀ i j,Commute (coordinateInclusion hNM (E.entry i j)) cM := by
    intro i j
    apply Subtype.ext
    exact ((F.relativeStar_mem c.val).mp c.property).2 i j
  have hamp (a : N.toStarSubalgebra) : Commute
      (coordinateInclusion hNM (E.amplify o a)) cM := by
    let b : E.relativeVonNeumann.toStarSubalgebra :=
      E.relativeEquiv ⟨E.amplify o a,E.amplify_mem o a⟩
    apply Subtype.ext
    exact congrArg (fun t : F.relativeVonNeumann.toStarSubalgebra => t.val) (hc b)
  obtain ⟨z,hz⟩ := hirr cM (fun x =>
    E.commute_mapped_of_amplify o (coordinateInclusion hNM) cM hentries hamp x)
  exact ⟨z,Subtype.ext (congrArg (fun t : M.toStarSubalgebra => t.val) hz)⟩

end MatrixUnitSystem

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! A constructed full matrix algebra reduces the actual relative-commutant
expectation energy by a uniform factor for a centered nonzero element. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N D M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem commutator_norm₂_bound (a b : M.toStarSubalgebra) :
    τ.norm₂ (a*b-b*a) ≤ 2*‖a‖*τ.norm₂ b := by
  have h := norm_sub_le (baseVector τ (a*b)) (baseVector τ (b*a))
  change τ.norm₂ (a*b-b*a) ≤ τ.norm₂ (a*b)+τ.norm₂ (b*a) at h
  have hl := τ.norm₂_mul_le a b
  have hr := τ.norm₂_mul_le_right b a
  nlinarith

theorem commutator_norm₂_approximation (u v x z : M.toStarSubalgebra)
    (hc : v*z=z*v) :
    τ.norm₂ (u*x-x*u) ≤ 2*‖u‖*τ.norm₂ (x-z)+2*‖z‖*τ.norm₂ (u-v) := by
  have he : u*x-x*u=(u*(x-z)-(x-z)*u)- (z*(u-v)-(u-v)*z) := by
    simp only [mul_sub,sub_mul]
    rw [hc]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (u*(x-z)-(x-z)*u))
    (baseVector τ (z*(u-v)-(u-v)*z))
  change τ.norm₂ ((u*(x-z)-(x-z)*u)-(z*(u-v)-(u-v)*z)) ≤
    τ.norm₂ (u*(x-z)-(x-z)*u)+τ.norm₂ (z*(u-v)-(u-v)*z) at h
  exact h.trans (add_le_add (commutator_norm₂_bound τ u (x-z))
    (commutator_norm₂_bound τ z (u-v)))

theorem expectation_energy_descent_of_unitary_approximation (hDM : D ≤ M)
    (u : unitary M.toStarSubalgebra) (v x : M.toStarSubalgebra)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x))
    (hclose : τ.norm₂ ((u : M.toStarSubalgebra)-v) <
      τ.norm₂ x/(4*(‖x‖+1)))
    (hc : ∀ z : M.toStarSubalgebra,z.val ∈ D → v*z=z*v) :
    τ.norm₂ (conditionalExpectation τ hDM x)^2 ≤ (15/16 : ℝ)*τ.norm₂ x^2 := by
  let z := conditionalExpectation τ hDM x
  have hcomm := commutator_norm₂_approximation τ (u : M.toStarSubalgebra) v x z
    (hc z (conditionalExpectation_mem τ hDM x))
  have hdisp := displacement_le_commutator τ u x
  have hu := unitary_norm_le (u : M.toStarSubalgebra) u.property.1
  have hz := conditionalExpectation_norm_le τ hDM x
  have hn : 0 ≤ τ.norm₂ (x-z) := norm_nonneg _
  have hδ : 0 ≤ τ.norm₂ ((u : M.toStarSubalgebra)-v) := norm_nonneg _
  have hsmall : 4*(‖x‖+1)*τ.norm₂ ((u : M.toStarSubalgebra)-v) < τ.norm₂ x := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*(‖x‖+1))).mp hclose
    nlinarith
  have hr : τ.norm₂ x/4 ≤ τ.norm₂ (x-z) := by
    have h₁ := mul_le_mul_of_nonneg_right hu hn
    have h₂ := mul_le_mul_of_nonneg_right hz hδ
    nlinarith
  have hpy := conditionalExpectation_pythagoras τ hDM x
  change τ.norm₂ z^2+τ.norm₂ (x-z)^2=τ.norm₂ x^2 at hpy
  nlinarith [sq_nonneg (τ.norm₂ (x-z)-τ.norm₂ x/4),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

theorem exists_irreducible_matrix_energy_descent (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0) (ht : τ.trace x=0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ E : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      τ.norm₂ (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
        (15/16 : ℝ)*τ.norm₂ x^2 := by
  let P := insideAlgebra (M := M) (P := N)
  obtain ⟨u,hu⟩ := exists_strict_centered_displacement τ P (by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hNM a,a.property⟩)) x hx ht
  let a : N.toStarSubalgebra := ⟨(u.val : M.toStarSubalgebra).val,u.property⟩
  let : IsStarNormal a := ⟨by
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val)
      (u.val.property.1.trans u.val.property.2.symm)⟩
  have hxpos : 0 < τ.norm₂ x := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hx ((τ.norm₂_eq_zero_iff x).mp h.symm))
  obtain ⟨k,n,hn,E,c,hc⟩ := exists_normal_matrix_approximation_q129 (restrictedTrace τ hNM)
    hfactor hdiff a (τ.norm₂ x/(4*(‖x‖+1))) (by positivity)
  let F := E.map (coordinateInclusion hNM)
  let v : M.toStarSubalgebra := ∑ j,c j • F.entry j j
  refine ⟨k,n,hn,E,expectation_energy_descent_of_unitary_approximation τ
    F.relativeVonNeumann_le u.val v x hu.le ?_ ?_⟩
  · change τ.norm₂ (coordinateInclusion hNM (a-∑ j,c j • E.entry j j)) < _ at hc
    rw [map_sub,map_sum] at hc
    simp only [map_smul] at hc
    exact hc
  · intro z hz
    have hz' := ((F.relativeStar_mem z.val).mp hz).2
    change (∑ j,c j • F.entry j j)*z=z*(∑ j,c j • F.entry j j)
    simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun b : M.toStarSubalgebra => c j • b) (Subtype.ext (hz' j j))

end Tracial

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {D P M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem conditionalExpectation_restricted (hPM : P ≤ M) (hDP : D ≤ P)
    (x : P.toStarSubalgebra) :
    conditionalExpectation τ (hDP.trans hPM) (coordinateInclusion hPM x)=
      coordinateInclusion hPM (conditionalExpectation (restrictedTrace τ hPM) hDP x) := by
  apply conditionalExpectation_eq_of_orthogonal τ (hDP.trans hPM)
  · exact conditionalExpectation_mem (restrictedTrace τ hPM) hDP x
  · intro a
    let b : insideAlgebra (M := P) (P := D) := ⟨⟨a.val.val,hDP a.property⟩,a.property⟩
    exact conditionalExpectation_orthogonal (restrictedTrace τ hPM) hDP x b

end Tracial
namespace MatrixUnitSystem
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem relative_antitone (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ M.toStarSubalgebra) (h : E.algebra ≤ F.algebra) :
    F.relativeVonNeumann ≤ E.relativeVonNeumann := by
  intro x hx
  have hx' := (F.relativeStar_mem x).mp hx
  apply (E.relativeStar_mem x).mpr
  refine ⟨hx'.1,?_⟩
  let y : M.toStarSubalgebra := ⟨x,hx'.1⟩
  have hF : ∀ i j,Commute (F.entry i j) y := fun i j => Subtype.ext (hx'.2 i j)
  intro i j
  exact congrArg Subtype.val (((F.commute_algebra_iff y).mpr hF) _ (h (E.entry_mem i j))).eq

/-- The product commutant is exactly the commutant of the new system inside
of the old commutant, with both algebras represented on the same H. -/
theorem relative_product_inside (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ i j k l,Commute (E.entry i j)
      ((F.map (coordinateInclusion E.relativeVonNeumann_le)).entry k l)) :
    (E.product (F.map (coordinateInclusion E.relativeVonNeumann_le)) hc).relativeVonNeumann =
      F.relativeVonNeumann := by
  let G := F.map (coordinateInclusion E.relativeVonNeumann_le)
  apply le_antisymm
  · intro x hx
    have hE := E.relative_antitone (E.product G hc) (E.algebra_le_product_left G hc) hx
    have hG := G.relative_antitone (E.product G hc) (E.algebra_le_product_right G hc) hx
    exact (F.relativeStar_mem x).mpr ⟨hE,((G.relativeStar_mem x).mp hG).2⟩
  · intro x hx
    have hF := (F.relativeStar_mem x).mp hx
    have hE := (E.relativeStar_mem x).mp hF.1
    apply ((E.product G hc).relativeStar_mem x).mpr
    refine ⟨hE.1,?_⟩
    intro a b
    change ((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)*x=
      x*((E.entry a.1 b.1).val*(F.entry a.2 b.2).val)
    rw [mul_assoc,hF.2,← mul_assoc,hE.2,mul_assoc]

end MatrixUnitSystem

end

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_compatible_matrix_energy_descent (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (E : MatrixUnitSystem ι N.toStarSubalgebra) (o : ι)
    (x : M.toStarSubalgebra) (ht : τ.trace x=0)
    (hy : conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x ≠ 0) :
    ∃ k n : ℕ,n=2^k ∧ ∃ F : MatrixUnitSystem (Fin n) N.toStarSubalgebra,
      ∃ hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m),
        E.algebra ≤ (E.product F hc).algebra ∧
        τ.norm₂ (conditionalExpectation τ
          ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤
          (15/16 : ℝ)*τ.norm₂
            (conditionalExpectation τ (E.map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 := by
  let EM := E.map (coordinateInclusion hNM)
  let C := EM.relativeVonNeumann
  let hCM := EM.relativeVonNeumann_le
  let y := conditionalExpectation τ hCM x
  let yC : C.toStarSubalgebra := ⟨y.val,conditionalExpectation_mem τ hCM x⟩
  let τC := restrictedTrace τ hCM
  have hyC : yC ≠ 0 := by
    intro h
    apply hy
    exact Subtype.ext (congrArg (fun b : C.toStarSubalgebra => b.val) h)
  have htC : τC.trace yC=0 := (conditionalExpectation_trace τ hCM x).trans ht
  obtain ⟨k,n,hn,G,hG⟩ := exists_irreducible_matrix_energy_descent τC
    (E.relative_inclusion hNM) (E.relative_scalar_center o hfactor)
    (E.relative_diffuse o hdiff) (E.relative_irreducible hNM o hirr) yC hyC htC
  let F := G.map (coordinateInclusion E.relativeVonNeumann_le)
  have hc : ∀ i j l m,Commute (E.entry i j) (F.entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact ((E.relativeStar_mem (G.entry l m).val).mp (G.entry l m).property).2 i j
  let GM := G.map (coordinateInclusion (E.relative_inclusion hNM))
  have hcM : ∀ i j l m,Commute (EM.entry i j)
      ((GM.map (coordinateInclusion hCM)).entry l m) := by
    intro i j l m
    apply Subtype.ext
    exact congrArg (fun b : N.toStarSubalgebra => b.val) (hc i j l m).eq
  have hproduct : ((E.product F hc).map (coordinateInclusion hNM)).relativeVonNeumann =
      GM.relativeVonNeumann := by
    convert EM.relative_product_inside GM hcM using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  let hDC := GM.relativeVonNeumann_le
  have he : conditionalExpectation τ (hDC.trans hCM) x =
      coordinateInclusion hCM (conditionalExpectation τC hDC yC) := by
    rw [← conditionalExpectation_tower τ (hDC.trans hCM) hCM hDC x]
    exact conditionalExpectation_restricted τ hCM hDC yC
  refine ⟨k,n,hn,F,hc,E.algebra_le_product_left F hc,?_⟩
  have hnorm : τ.norm₂ (conditionalExpectation τ (hDC.trans hCM) x)^2 ≤
      (15/16 : ℝ)*τ.norm₂ y^2 := by
    rw [he]
    exact hG
  simpa only [hproduct] using hnorm

end Tracial

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem reindex_algebra (E : MatrixUnitSystem ι A) (e : κ ≃ ι) :
    (E.reindex e).algebra=E.algebra := by
  apply le_antisymm
  · exact ((E.reindex e).algebra_le_iff _).mpr (fun i j => E.entry_mem _ _)
  · apply (E.algebra_le_iff _).mpr
    intro i j
    simpa only [reindex,Equiv.apply_symm_apply] using
      (E.reindex e).entry_mem (e.symm i) (e.symm j)

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem map_algebra_mono (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (F : MatrixUnitSystem κ N.toStarSubalgebra) (h : E.algebra ≤ F.algebra)
    (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    (E.map f).algebra ≤ (F.map f).algebra := by
  apply ((E.map f).algebra_le_iff _).mpr
  intro i j
  obtain ⟨a,ha⟩ := (F.mem_algebra (E.entry i j)).mp (h (E.entry_mem i j))
  change f (E.entry i j) ∈ (F.map f).algebra
  rw [← ha]
  simp only [map_sum,map_smul]
  exact (F.map f).algebra.sum_mem fun k _ =>
    (F.map f).algebra.sum_mem fun l _ => (F.map f).algebra.smul_mem ((F.map f).entry_mem k l) _

theorem mapped_reindex_relative (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (e : κ ≃ ι) (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    ((E.reindex e).map f).relativeVonNeumann=(E.map f).relativeVonNeumann := by
  apply le_antisymm
  · exact (E.map f).relative_antitone _ (E.map_algebra_mono _ (E.reindex_algebra e).ge f)
  · exact ((E.reindex e).map f).relative_antitone _ ((E.reindex e).map_algebra_mono _
      (E.reindex_algebra e).le f)

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

theorem commutant_antitone (E F : FiniteMatrixStage N) (hNM : N ≤ M)
    (hEF : E.units.algebra ≤ F.units.algebra) : F.commutant hNM ≤ E.commutant hNM :=
  (E.units.map (coordinateInclusion hNM)).relative_antitone _
    (E.units.map_algebra_mono F.units hEF (coordinateInclusion hNM))

theorem energy_antitone (E F : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (hEF : E.units.algebra ≤ F.units.algebra) (x : M.toStarSubalgebra) :
    F.energy τ hNM x ≤ E.energy τ hNM x := by
  have h := conditionalExpectation_nested_energy τ (F.commutant_le hNM) (E.commutant_le hNM)
    (E.commutant_antitone F hNM hEF) x
  dsimp [energy]
  nlinarith [sq_nonneg (τ.norm₂ (conditionalExpectation τ (E.commutant_le hNM) x-
    conditionalExpectation τ (F.commutant_le hNM) x))]

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TensorRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.FiniteMatrixStage

/-! A finite refinement retaining its actual commuting matrix factor.
The relation composes, so finite energy descent can retain these witnesses. -/
section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem TensorExtension.algebra_le {E F : FiniteMatrixStage N} (h : TensorExtension E F) :
    E.units.algebra ≤ F.units.algebra := by
  obtain ⟨G,_,hG⟩ := h
  rw [hG]
  exact le_sup_left

theorem TensorExtension.refl (E : FiniteMatrixStage N) : TensorExtension E E := by
  refine ⟨scalarStage N,fun _ _ _ _ => Commute.one_right _,?_⟩
  symm
  apply sup_eq_left.mpr
  apply ((scalarStage N).units.algebra_le_iff _).mpr
  intro i j
  exact E.units.algebra.one_mem

theorem TensorExtension.trans {E F G : FiniteMatrixStage N}
    (hEF : TensorExtension E F) (hFG : TensorExtension F G) : TensorExtension E G := by
  obtain ⟨D,hD,hFD⟩ := hEF
  obtain ⟨K,hK,hGK⟩ := hFG
  have hDF : D.units.algebra ≤ F.units.algebra := by rw [hFD]; exact le_sup_right
  have hEF : E.units.algebra ≤ F.units.algebra := by rw [hFD]; exact le_sup_left
  have hDK : ∀ i j k l,Commute (D.units.entry i j) (K.units.entry k l) := by
    intro i j k l
    exact (F.units.commute_algebra_iff _).mpr (fun a b => hK a b k l) _
      (hDF (D.units.entry_mem i j))
  let P := D.units.product K.units hDK
  let eqv := (Fintype.equivFin (Fin D.size × Fin K.size)).symm
  let L : FiniteMatrixStage N := ⟨Fintype.card (Fin D.size × Fin K.size),by
    simpa using Nat.mul_pos D.positive K.positive,P.reindex eqv⟩
  refine ⟨L,?_,?_⟩
  · intro i j k l
    change Commute (E.units.entry i j)
      (D.units.entry (eqv k).1 (eqv l).1*K.units.entry (eqv k).2 (eqv l).2)
    apply (hD i j _ _).mul_right
    exact (F.units.commute_algebra_iff _).mpr (fun a b => hK a b _ _) _
      (hEF (E.units.entry_mem i j))
  · change G.units.algebra=E.units.algebra ⊔ (P.reindex eqv).algebra
    rw [P.reindex_algebra,D.units.product_algebra_eq_sup,hGK,hFD,sup_assoc]

theorem exists_tensor_refinement_descent (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (ht : τ.trace x=0) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      F.energy τ hNM x ≤ (15/16 : ℝ)*E.energy τ hNM x := by
  by_cases hz : conditionalExpectation τ (E.commutant_le hNM) x=0
  · refine ⟨E,TensorExtension.refl E,?_⟩
    simp [energy,hz]
  · obtain ⟨k,n,hn,F,hc,_,hdesc⟩ := exists_compatible_matrix_energy_descent τ hNM
      hfactor hdiff hirr E.units ⟨0,E.positive⟩ x ht hz
    have hnpos : 0 < n := by rw [hn]; positivity
    let G := E.units.product F hc
    let eqv := (Fintype.equivFin (Fin E.size × Fin n)).symm
    let S : FiniteMatrixStage N := ⟨Fintype.card (Fin E.size × Fin n),by
      simpa using Nat.mul_pos E.positive hnpos,G.reindex eqv⟩
    refine ⟨S,⟨⟨n,hnpos,F⟩,hc,?_⟩,?_⟩
    · change (G.reindex eqv).algebra=E.units.algebra ⊔ F.algebra
      rw [G.reindex_algebra,E.units.product_algebra_eq_sup]
    · change τ.norm₂ (conditionalExpectation τ
        ((G.reindex eqv).map (coordinateInclusion hNM)).relativeVonNeumann_le x)^2 ≤ _
      simp only [G.mapped_reindex_relative eqv (coordinateInclusion hNM)]
      exact hdesc

end

/-! Tensor-factor-retaining compatible refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/
section
open scoped BigOperators
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hfactor hdiff hirr

theorem exists_tensor_finite_family_descent {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)*E.energy τ hNM (x s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E,TensorExtension.refl E,by simp⟩
  | @insert s S hs ih =>
    obtain ⟨F,hEF,hF⟩ := ih (fun t ht' => ht t (Finset.mem_insert_of_mem ht'))
    obtain ⟨G,hFG,hG⟩ := F.exists_tensor_refinement_descent τ hNM hfactor hdiff hirr (x s)
      (ht s (Finset.mem_insert_self s S))
    refine ⟨G,hEF.trans hFG,?_⟩
    intro t ht'
    rcases Finset.mem_insert.mp ht' with rfl | ht'
    · exact hG.trans (mul_le_mul_of_nonneg_left (E.energy_antitone F τ hNM hEF.algebra_le _) (by norm_num))
    · exact (F.energy_antitone G τ hNM hFG.algebra_le _).trans (hF t ht')

theorem exists_tensor_iterated_energy_descent_q129_oai {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (r : ℕ) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      ∀ s ∈ S,F.energy τ hNM (x s) ≤ (15/16 : ℝ)^r*E.energy τ hNM (x s) := by
  induction r with
  | zero => exact ⟨E,TensorExtension.refl E,by simp⟩
  | succ r ih =>
    obtain ⟨F,hEF,hF⟩ := ih
    obtain ⟨G,hFG,hG⟩ := exists_tensor_finite_family_descent τ hNM hfactor hdiff hirr S x ht F
    refine ⟨G,hEF.trans hFG,?_⟩
    intro s hs
    calc G.energy τ hNM (x s) ≤ (15/16 : ℝ)*F.energy τ hNM (x s) := hG s hs
      _ ≤ (15/16 : ℝ)*((15/16 : ℝ)^r*E.energy τ hNM (x s)) :=
        mul_le_mul_of_nonneg_left (hF s hs) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

end

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial

end Generator.FiniteMatrixStage

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.FiniteMatrixStage.exists_tensor_iterated_energy_descent_q129_oai.{u_1, u_2} := @OAI.Generator.FiniteMatrixStage.exists_tensor_iterated_energy_descent_q129_oai.{u_1, u_2}
