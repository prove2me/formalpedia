-- Prove2me | solution 1 for OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:27:18.443986+00:00
-- url     : https://prove2.me/submissions/8605eff8-0d71-482b-ac00-31ea4a8453e9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_FiniteMatrixStage_exists_tensor_iterated_energy_descent_q129
import Theorems.Thm_OAI_Generator_Tracial_represented_relative_generation_q129

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

include τ hirr in
/-- Every projection commuting with pPp inside pMp is either zero or p. -/
theorem corner_commutant_projection_trivial (p r : AlgebraProjection M)
    (hrp : r ≤ p)
    (hr : ∀ a : P, Commute r.val (p.val*(a : M.toStarSubalgebra)*p.val)) :
    r.val=0 ∨ r.val=p.val := by
  let s : AlgebraProjection M := ⟨p.val-r.val,r.property.sub_of_mul_eq_right p.property hrp⟩
  have hlink (a : P) : s.val*(a : M.toStarSubalgebra)*r.val=0 := by
    have hl : p.val*r.val=r.val := hrp
    have hright := projection_mul_of_le hrp
    have he := congrArg (fun z : M.toStarSubalgebra => z*r.val) (hr a).eq
    simp only [mul_assoc,hl,r.property.isIdempotentElem.eq] at he
    have he' : r.val*((p.val*(a : M.toStarSubalgebra))*r.val)=
        (p.val*(a : M.toStarSubalgebra))*r.val := by
      simpa only [mul_assoc,hl,r.property.isIdempotentElem.eq] using he
    have he'' : r.val*(a : M.toStarSubalgebra)*r.val=
        p.val*(a : M.toStarSubalgebra)*r.val := by
      simpa only [← mul_assoc,hright] using he'
    change (p.val-r.val)*(a : M.toStarSubalgebra)*r.val=0
    rw [sub_mul,sub_mul,he'',sub_self]
  rcases projection_eq_zero_or_eq_zero_of_no_links τ P hirr r s hlink with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

theorem wstar_mono {s t : Set (H →L[ℂ] H)} (h : s ⊆ t) : wstar s ≤ wstar t := by
  intro x hx
  apply StarSubalgebra.mem_sInf.mpr
  intro S hS
  exact StarSubalgebra.mem_sInf.mp hx S ⟨hS.1, h.trans hS.2⟩

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotClosed_normClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    IsClosed (S : Set (H →L[ℂ] H)) :=
  hS.preimage ContinuousLinearMapWOT.continuous_ofCLM

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionComparison
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! Projection comparison and equal-trace equivalence in the actual factor.
Both polar decomposition and the maximal partial isometry are constructed. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/

attribute [local instance] OAI.Generator.Tracial.approximationCStar
attribute [local instance] OAI.Generator.Tracial.approximationOrder
attribute [local instance] OAI.Generator.Tracial.approximationPreorder
attribute [local instance] OAI.Generator.Tracial.approximationLE
attribute [local instance] OAI.Generator.Tracial.approximationStarOrder
/-- An actual finite orthogonal spectral approximation of a compressed
self-adjoint operator. All projections and coefficients are constructed. -/
theorem exists_finite_spectral_approximation (p : AlgebraProjection M)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition p) (c : Fin Q.size → ℝ),
      Q.pinch x=p.val*x*p.val ∧
      ‖p.val*x*p.val-∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval p x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,hn⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,I.partition_pinch hx n,?_⟩
  have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val)
  change ‖p.val*x*p.val-∑ i, ((I.level hx n (e i)).lo : ℂ) •
    (I.level hx n (e i)).proj.val‖ < ε
  rw [he]
  exact hn

end

/-! Constructed cuts preserve commutation with other operators. -/

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cornerCompressOperator_apply _root_.OAI.Generator.Tracial.cornerCompress_embedding _root_.OAI.Generator.Tracial.cornerCompress_extend _root_.OAI.Generator.Tracial.cornerEmbedding_compress _root_.OAI.Generator.Tracial.cornerEmbedding_left _root_.OAI.Generator.Tracial.cornerEmbedding_one _root_.OAI.Generator.Tracial.cornerEmbedding_right _root_.OAI.Generator.Tracial.cornerExtend_add _root_.OAI.Generator.Tracial.cornerExtend_apply _root_.OAI.Generator.Tracial.cornerExtend_left _root_.OAI.Generator.Tracial.cornerExtend_mul _root_.OAI.Generator.Tracial.cornerExtend_one _root_.OAI.Generator.Tracial.cornerExtend_right _root_.OAI.Generator.Tracial.cornerExtend_smul _root_.OAI.Generator.Tracial.cornerExtend_star _root_.OAI.Generator.Tracial.cornerExtend_zero _root_.OAI.Generator.Tracial.cornerProject_coe _root_.OAI.Generator.Tracial.cornerProject_subtype _root_.OAI.Generator.Tracial.mem_cornerSpace _root_.OAI.Generator.Tracial.signedCornerUnitary_val
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

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c) : ∃ z : ℂ,c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hm : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,_,hd⟩ := exists_finite_spectral_approximation p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      rcases hmin (Q.piece i) (Q.piece_le i) with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i,(d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  rw [hclosed.closure_eq] at hm
  exact (Submodule.mem_span_singleton.mp hm).imp (fun z hz => hz.symm)

theorem corner_scalar_of_projections (p : AlgebraProjection M)
    (hmin : ∀ q : AlgebraProjection M,q ≤ p → q.val=0 ∨ q.val=p.val)
    (c : M.toStarSubalgebra) (hl : p.val*c=c) (hr : c*p.val=c) :
    ∃ z : ℂ,c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  obtain ⟨a,ha⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr])
  obtain ⟨b,hb⟩ := selfAdjoint_corner_scalar_of_projections p hmin (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr])
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_diffuse (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (p : P.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  classical
  by_contra hn
  let pP : AlgebraProjection P := ⟨p,hp⟩
  have hmin : ∀ q : AlgebraProjection P,q ≤ pP → q.val=0 ∨ q.val=p := by
    intro q hq
    by_cases hq0 : q.val=0
    · exact Or.inl hq0
    by_cases hqp : q.val=p
    · exact Or.inr hqp
    exact False.elim (hn ⟨q.val,q.property,hq0,hqp,hq,projection_mul_of_le hq⟩)
  let pM := includedProjection hPM pP
  have hpM0 : pM.val ≠ 0 := by
    intro h
    apply hp0
    exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff pM.val pM.property hpM0
  let Q : StarSubalgebra ℂ M.toStarSubalgebra := insideAlgebra (M := M) (P := P)
  have hirrQ : ∀ c : M.toStarSubalgebra,
      (∀ a : Q,(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    exact hirr c (fun a => hc ⟨coordinateInclusion hPM a,a.property⟩)
  have hcomm : ∀ a : Q,Commute q (pM.val*(a : M.toStarSubalgebra)*pM.val) := by
    intro a
    let aP : P.toStarSubalgebra := ⟨a.val.val,a.property⟩
    obtain ⟨z,hz⟩ := corner_scalar_of_projections pP hmin (p*aP*p)
      (by change p*(p*aP*p)=p*aP*p; simp only [← mul_assoc,hp.isIdempotentElem.eq])
      (by change (p*aP*p)*p=p*aP*p; simp only [mul_assoc,hp.isIdempotentElem.eq])
    have he : pM.val*(a : M.toStarSubalgebra)*pM.val=z • pM.val := by
      exact Subtype.ext (congrArg (fun b : P.toStarSubalgebra => b.val) hz)
    rw [he]
    show q*(z • pM.val)=(z • pM.val)*q
    rw [mul_smul_comm,smul_mul_assoc,hqp',hpq]
  exact (corner_commutant_projection_trivial τ Q hirrQ pM ⟨q,hq⟩ hpq hcomm).elim hq0 hqp

theorem tracial_isometry_coisometry (τ : TracialRepresentation M)
    (v : M.toStarSubalgebra) (hv : star v*v=1) : v*star v=1 := by
  let p : AlgebraProjection M := ⟨v*star v,by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc _ = v*(star v*v)*star v := by simp only [mul_assoc]
           _ = v*star v := by rw [hv,mul_one]
    · simp only [IsSelfAdjoint,star_mul,star_star]⟩
  have ht : τ.trace p.val=τ.trace (identityProjection M).val := by
    change τ.trace (v*star v)=τ.trace 1
    rw [τ.trace_mul_comm,hv]
  have h := projection_eq_of_le_of_trace_eq τ (p := p) (q := identityProjection M)
    (one_mul _) ht
  exact congrArg Subtype.val h

theorem tracial_nonzero (τ : TracialRepresentation M) : (0 : H →L[ℂ] H) ≠ 1 := by
  intro h
  have hzero : τ.vector=0 := by
    have he := congrArg (fun T : H →L[ℂ] H => T τ.vector) h
    exact he.symm
  have hn := τ.norm_vector
  rw [hzero,norm_zero] at hn
  exact zero_ne_one hn

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

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

theorem conditionalExpectation_norm₂_le (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.norm₂ (conditionalExpectation τ hNM x) ≤ τ.norm₂ x := by
  have h := conditionalExpectation_pythagoras τ hNM x
  nlinarith [sq_nonneg (τ.norm₂ (x-conditionalExpectation τ hNM x)),
    show 0 ≤ τ.norm₂ x from norm_nonneg _]

end

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
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

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [StarModule ℂ A] in
theorem diagonal_projection (o : ι) : IsStarProjection (E.entry o o) := by
  exact ⟨by show E.entry o o*E.entry o o=E.entry o o; simpa using E.mul_entry o o o o,E.star_entry o o⟩

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

theorem energy_nonneg (E : FiniteMatrixStage N) (τ : TracialRepresentation M)
    (hNM : N ≤ M) (x : M.toStarSubalgebra) : 0 ≤ E.energy τ hNM x := sq_nonneg _

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/
section
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_countable_norm₂_dense (S : Set M.toStarSubalgebra)
    (hne : S.Nonempty) (hsep : TopologicalSpace.IsSeparable (baseVector τ '' S)) :
    ∃ a : ℕ → M.toStarSubalgebra,(∀ n,a n ∈ S) ∧
      ∀ b ∈ S,∀ ε : ℝ,0 < ε → ∃ n,τ.norm₂ (b-a n) < ε := by
  let T := baseVector τ '' S
  let : TopologicalSpace.SeparableSpace T := hsep.separableSpace
  let : Nonempty T := ⟨⟨baseVector τ hne.choose,Set.mem_image_of_mem _ hne.choose_spec⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := T)
  have hex (n : ℕ) : ∃ a ∈ S,baseVector τ a=(v n).val := (v n).property
  choose a ha he using hex
  refine ⟨a,ha,?_⟩
  intro b hb ε hε
  let z : T := ⟨baseVector τ b,Set.mem_image_of_mem _ hb⟩
  obtain ⟨w,⟨n,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (hv z) ε hε
  refine ⟨n,?_⟩
  change ‖baseVector τ (b-a n)‖ < ε
  rw [map_sub,he n]
  simpa only [Subtype.dist_eq,dist_eq_norm] using hw

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem scalar_common_commutant_of_dense_energy_decay (τ : TracialRepresentation M) (hNM : N ≤ M)
    (A : ℕ → FiniteMatrixStage N) (x : ℕ → M.toStarSubalgebra)
    (hdense : ∀ b : M.toStarSubalgebra,τ.trace b=0 → ∀ ε : ℝ,0 < ε →
      ∃ s,τ.norm₂ (b-x s) < ε)
    (hlim : ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0))
    (c : M.toStarSubalgebra) (hc : ∀ n,c.val ∈ (A n).commutant hNM) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  let y := c-τ.trace c • (1 : M.toStarSubalgebra)
  have hyt : τ.trace y=0 := by
    dsimp [y]
    rw [trace_sub,cornerTrace_smul,τ.trace_one,mul_one,sub_self]
  have hym (n : ℕ) : y.val ∈ (A n).commutant hNM :=
    ((A n).commutant hNM).sub_mem (hc n)
      (((A n).commutant hNM).smul_mem ((A n).commutant hNM).one_mem _)
  suffices y=0 from sub_eq_zero.mp this
  by_contra hy
  have hp : 0 < τ.norm₂ y := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hy ((τ.norm₂_eq_zero_iff y).mp h.symm))
  obtain ⟨s,hs⟩ := hdense y hyt (τ.norm₂ y/4) (by positivity)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp (hlim s)).2 ((τ.norm₂ y/4)^2) (by positivity)).exists
  let hDM := (A n).commutant_le hNM
  let z := conditionalExpectation τ hDM (x s)
  have hz : τ.norm₂ z < τ.norm₂ y/4 := by
    change τ.norm₂ z^2 < (τ.norm₂ y/4)^2 at hn
    nlinarith [show 0 ≤ τ.norm₂ z from norm_nonneg _]
  have hdiff : τ.norm₂ (y-z) ≤ τ.norm₂ (y-x s) := by
    have he : conditionalExpectation τ hDM (y-x s)=y-z := by
      change conditionalExpectationCLM τ hDM (y-x s)=y-z
      rw [map_sub]
      change conditionalExpectation τ hDM y-z=y-z
      rw [conditionalExpectation_fixed τ hDM y (hym n)]
    rw [← he]
    exact conditionalExpectation_norm₂_le τ hDM _
  have hadd := τ.norm₂_add_le (y-z) z
  rw [sub_add_cancel] at hadd
  linarith

end FiniteMatrixStage

end

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem stage_le_generated (A : ℕ → FiniteMatrixStage N) (n : ℕ) :
    (A n).units.concreteAlgebra ≤ generated A := by
  intro x hx
  exact subset_wstar _ (Set.mem_iUnion.mpr ⟨n,hx⟩)

theorem generated_le (A : ℕ → FiniteMatrixStage N) : generated A ≤ N.toStarSubalgebra := by
  apply wstar_le (vonNeumann_wotClosed N)
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact (A n).units.concreteAlgebra_le hn

theorem generated_minimal (A : ℕ → FiniteMatrixStage N)
    (R : StarSubalgebra ℂ (H →L[ℂ] H)) (hR : WOTClosed R)
    (h : ∀ n,(A n).units.concreteAlgebra ≤ R) : generated A ≤ R := by
  apply wstar_le hR
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact h n hn

theorem generated_relative_scalar (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ (A n).commutant hNM) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    (c : M.toStarSubalgebra)
    (hc : ∀ a : generated A,a.val*c.val=c.val*a.val) :
    c=τ.trace c • (1 : M.toStarSubalgebra) := by
  apply hirr c
  intro n
  apply (((A n).units.map (coordinateInclusion hNM)).relativeStar_mem c.val).mpr
  refine ⟨c.property,?_⟩
  intro i j
  have hi : ((A n).units.entry i j).val ∈ (A n).units.concreteAlgebra := by
    exact ((A n).units.mem_concreteAlgebra _).mpr ((A n).units.entry_mem i j)
  exact hc ⟨((A n).units.entry i j).val,stage_le_generated A n hi⟩

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem irreducible_subalgebra_isII1 (τ : TracialRepresentation M) (hPM : P ≤ M)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) : IsII1Factor P.toStarSubalgebra where
  nonzero := tracial_nonzero τ
  weaklyClosed := vonNeumann_wotClosed P
  factor c hc := by
    obtain ⟨z,hz⟩ := hirr (coordinateInclusion hPM c) (fun a => by
      simpa only [map_mul] using congrArg (coordinateInclusion hPM) (hc a))
    refine ⟨z,?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    apply Subtype.ext
    exact congrArg (fun b : M.toStarSubalgebra => b.val) hz
  finite := tracial_isometry_coisometry (restrictedTrace τ hPM)
  diffuse := irreducible_subalgebra_diffuse τ hPM hdiff hirr

end Tracial
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generatedVonNeumann_le (A : ℕ → FiniteMatrixStage N) : generatedVonNeumann A ≤ N :=
  generated_le A

theorem generated_isII1 (A : ℕ → FiniteMatrixStage N)
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra)) : IsII1Factor (generated A) := by
  apply irreducible_subalgebra_isII1 (restrictedTrace τ hNM) (generatedVonNeumann_le A) hdiff
  intro c hc
  have h := hirr (coordinateInclusion hNM c) (fun a =>
    congrArg (fun b : N.toStarSubalgebra => b.val) (hc a))
  refine ⟨τ.trace (coordinateInclusion hNM c),?_⟩
  exact Subtype.ext (congrArg (fun b : M.toStarSubalgebra => b.val) h)

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProjectionEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129MulOneClass _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! A separated idempotent is recovered from commutation with a norm-small
perturbation. This is an elementary substitute for the spectral-cut step. -/
section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem offDiagonal_eq_zero_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : p*x*(1-p)=0 := by
  let y := p*x*(1-p)
  have hleft : p*(a • p+t) = a • p+p*t := by
    rw [mul_add,mul_smul_comm,hp]
  have hright : (a • p+t)*(1-p)=t*(1-p) := by
    rw [add_mul,smul_mul_assoc,mul_sub,mul_one,hp,sub_self,smul_zero,zero_add]
  have he := congrArg (fun z : A => p*z*(1-p)) hx.eq
  have hy : a • y = y*t-t*y := by
    have ht : t*(1-p)=(1-p)*t := by
      rw [mul_sub,sub_mul,mul_one,one_mul,hpt.eq]
    have h : a • y+t*y=y*t := by
      calc a • y+t*y = (p*(a • p+t))*x*(1-p) := by
             rw [hleft,add_mul,add_mul,smul_mul_assoc,smul_mul_assoc]
             dsimp [y]
             rw [hpt.eq]
             simp only [mul_assoc]
        _ = p*((a • p+t)*x)*(1-p) := by simp only [mul_assoc]
        _ = p*(x*(a • p+t))*(1-p) := he
        _ = y*t := by
          simp only [mul_assoc]
          rw [hright,ht]
          simp only [y,mul_assoc]
    exact eq_sub_of_add_eq' (by simpa only [add_comm] using h)
  have han : 0 ≤ a := (mul_nonneg (by norm_num) (norm_nonneg t)).trans ha.le
  have hn : a*‖y‖ ≤ 2*‖t‖*‖y‖ := by
    calc a*‖y‖ = ‖a • y‖ := by rw [norm_smul,Real.norm_of_nonneg han]
      _ = ‖y*t-t*y‖ := congrArg norm hy
      _ ≤ ‖y*t‖+‖t*y‖ := norm_sub_le _ _
      _ ≤ ‖y‖*‖t‖+‖t‖*‖y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2*‖t‖*‖y‖ := by ring
  have hz : ‖y‖=0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp hz

theorem commute_projection_of_gap (p t x : A) (hp : p*p=p)
    (hpt : Commute p t) (a : ℝ) (ha : 2*‖t‖ < a)
    (hx : Commute (a • p+t) x) : Commute p x := by
  have h₁ := offDiagonal_eq_zero_of_gap p t x hp hpt a ha hx
  have hcp : (1-p)*(1-p)=1-p := by noncomm_ring [hp]
  have hcpt : Commute (1-p) (-t) := ((Commute.one_left t).sub_left hpt).neg_right
  have hcx : Commute (a • (1-p)+ -t) x := by
    have he : a • (1-p)+ -t = a • (1 : A)-(a • p+t) := by
      rw [smul_sub]; abel
    rw [he]
    exact ((Commute.one_left x).smul_left a).sub_left hx
  have h₂ := offDiagonal_eq_zero_of_gap (1-p) (-t) x hcp hcpt a
    (by simpa only [norm_neg] using ha) hcx
  simp only [sub_sub_cancel] at h₂
  show p*x=x*p
  have h₁' : p*x=p*x*p := by simpa only [mul_sub,mul_one,sub_eq_zero] using h₁
  have h₂' : x*p=p*x*p := by simpa only [sub_mul,one_mul,sub_eq_zero] using h₂
  exact h₁'.trans h₂'.symm

end

/-! Countably many commuting projections have one self-adjoint generator.
We use coefficients 3*4^(-(n+1)), whose strict gap admits direct norm recovery
through the double commutant. No trace, tensor model, or uniqueness is used. -/
namespace CommutingProjectionEncoding
open scoped BigOperators Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem weight_hasSum (n : ℕ) :
    HasSum (fun k => weight (n+k)) ((1/4 : ℝ)^n) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)).mul_left ((3/4:ℝ)*(1/4)^n)
  convert! h using 1
  · ext k; simp only [weight,pow_add]; ring
  · ring

variable (e : ℕ → (H →L[ℂ] H)) (hp : ∀ n, IsStarProjection (e n))
include hp

theorem term_norm_le (n k : ℕ) : ‖(weight (n+k) • e (n+k) : (H →L[ℂ] H))‖ ≤ weight (n+k) := by
  rw [norm_smul,Real.norm_of_nonneg (weight_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hp (n+k)).norm_le (weight_nonneg _)).trans_eq (mul_one _)

theorem tail_summable (n : ℕ) : Summable (fun k => (weight (n+k) • e (n+k) : (H →L[ℂ] H))) := by
  exact (weight_hasSum n).summable.of_norm_bounded (term_norm_le e hp n)

theorem tail_norm_le (n : ℕ) : ‖tail e n‖ ≤ (1/4 : ℝ)^n :=
  tsum_of_norm_bounded (weight_hasSum n) (term_norm_le e hp n)

theorem tail_step (n : ℕ) : tail e n = weight n • e n + tail e (n+1) := by
  have h := (tail_summable e hp n).tsum_eq_zero_add
  simpa only [tail,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem tail_selfAdjoint (n : ℕ) : IsSelfAdjoint (tail e n) := by
  have h := (tail_summable e hp n).hasSum.star
  simp only [star_smul,star_trivial,(hp _).isSelfAdjoint.star_eq] at h
  exact h.unique (tail_summable e hp n).hasSum

theorem tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (he : ∀ n, e n ∈ S) (n : ℕ) : tail e n ∈ S := by
  apply (wotClosed_normClosed S hS).mem_of_tendsto (tail_summable e hp n).hasSum
  exact Eventually.of_forall fun s => S.sum_mem fun k _ => by
    rw [← Complex.coe_smul]
    exact S.smul_mem (he (n+k)) _

variable (hc : ∀ i j, Commute (e i) (e j))
include hc

omit hp [CompleteSpace H] in
theorem projection_commutes_tail (i n : ℕ) : Commute (e i) (tail e n) :=
  Commute.tsum_right _ fun k => (hc i (n+k)).smul_right _

theorem projection_mem_of_tail_mem (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (n : ℕ) (ht : tail e n ∈ S) : e n ∈ S := by
  change e n ∈ (S : Set (H →L[ℂ] H))
  rw [← wotClosed_bicommutant S hS]
  intro x hx
  have hxt : Commute (weight n • e n+tail e (n+1)) x := by
    rw [← tail_step e hp n]
    exact hx _ ht
  have hgap : 2*‖tail e (n+1)‖ < weight n := by
    have h := tail_norm_le e hp (n+1)
    have hn : 0 < (1/4:ℝ)^n := by positivity
    dsimp [weight]
    rw [pow_succ] at h
    nlinarith
  exact (commute_projection_of_gap (e n) (tail e (n+1)) x
    (hp n).isIdempotentElem.eq (projection_commutes_tail e hc n (n+1))
    (weight n) hgap hxt).eq.symm

theorem projection_mem_wstar (n : ℕ) : e n ∈ wstar {tail e 0} := by
  let S := wstar {tail e 0}
  have hS : WOTClosed S := wstar_closed _
  have ht : ∀ k, tail e k ∈ S := by
    intro k
    induction k with
    | zero => exact subset_wstar _ (Set.mem_singleton _)
    | succ k ih =>
      have he := projection_mem_of_tail_mem e hp hc S hS k ih
      have hs : weight k • e k ∈ S := by
        rw [← Complex.coe_smul]
        exact S.smul_mem he _
      have h := S.sub_mem ih hs
      rw [tail_step e hp k,add_sub_cancel_left] at h
      exact h
  exact projection_mem_of_tail_mem e hp hc S hS n (ht n)

theorem wstar_encoding : wstar {tail e 0} = wstar (Set.range e) := by
  apply le_antisymm
  · apply wstar_le (wstar_closed _)
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact tail_mem e hp (wstar (Set.range e)) (wstar_closed _)
      (fun n => subset_wstar (Set.range e) (Set.mem_range_self n)) 0
  · apply wstar_le (wstar_closed _)
    rintro x ⟨n,rfl⟩
    exact projection_mem_wstar e hp hc n

/-- Countable commuting-projection encoding without additional structural hypotheses. -/
theorem exists_selfAdjoint_generator :
    ∃ b : (H →L[ℂ] H), IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) :=
  ⟨tail e 0,tail_selfAdjoint e hp 0,by simpa using tail_norm_le e hp 0,
    wstar_encoding e hp hc⟩

end CommutingProjectionEncoding

/-! The spectral separation step as an exact membership theorem for literal W*. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_AmplificationEncoding
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! One arbitrary operator and a pair of self-adjoint operators generate the same weakly closed star algebra. -/
open scoped ComplexStarModule
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

theorem realPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℜ x : Op) ∈ S := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (add_mem hx (star_mem hx)) _

theorem imaginaryPart_mem (S : StarSubalgebra ℂ Op) {x : Op} (hx : x ∈ S) :
    (ℑ x : Op) ∈ S := by
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
  exact S.smul_mem (S.smul_mem (sub_mem hx (star_mem hx)) _) _

theorem mem_iff_parts_mem (S : StarSubalgebra ℂ Op) (x : Op) :
    x ∈ S ↔ (ℜ x : Op) ∈ S ∧ (ℑ x : Op) ∈ S := by
  refine ⟨fun hx => ⟨realPart_mem S hx, imaginaryPart_mem S hx⟩, ?_⟩
  rintro ⟨hr, hi⟩
  rw [← realPart_add_I_smul_imaginaryPart x]
  exact add_mem hr (S.smul_mem hi _)

end

/-! Two self-adjoint generators for an actual two-by-two amplification
whose actual commutant has four self-adjoint generators. Spectral separation
is proved, and the final generation uses the surjective coefficient map. -/
open scoped BigOperators

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

theorem exists_tensor_finite_matrix_energy_budget {σ : Type*} (S : Finset σ)
    (x : σ → M.toStarSubalgebra) (ht : ∀ s ∈ S,τ.trace (x s)=0)
    (E : FiniteMatrixStage N) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage N,TensorExtension E F ∧
      (∑ s ∈ S,F.energy τ hNM (x s)) < ε := by
  let A := ∑ s ∈ S,E.energy τ hNM (x s)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun s _ => E.energy_nonneg τ hNM (x s))
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one
    (show 0 < ε/(A+1) from div_pos hε (by positivity)) (by norm_num : (15/16 : ℝ) < 1)
  obtain ⟨F,hEF,hF⟩ := exists_tensor_iterated_energy_descent_q129 τ hNM hfactor hdiff hirr S x ht E r
  refine ⟨F,hEF,?_⟩
  have hbound : (∑ s ∈ S,F.energy τ hNM (x s)) ≤ (15/16 : ℝ)^r*A := by
    calc (∑ s ∈ S,F.energy τ hNM (x s)) ≤
        ∑ s ∈ S,(15/16 : ℝ)^r*E.energy τ hNM (x s) :=
          Finset.sum_le_sum (fun s hs => hF s hs)
      _ = _ := (Finset.mul_sum S _ _).symm
  have hsmall := (lt_div_iff₀ (by positivity : 0 < A+1)).mp hr
  have hp : 0 ≤ (15/16 : ℝ)^r := by positivity
  nlinarith

end

/-! A single increasing sequence of full matrix algebras simultaneously
kills every member of a supplied countable centered family in commutant L2. -/
open Filter
open scoped BigOperators Topology
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_countable_tensor_refinement (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : ℕ → M.toStarSubalgebra) (ht : ∀ s,τ.trace (x s)=0) (E : FiniteMatrixStage N) :
    ∃ A : ℕ → FiniteMatrixStage N,A 0=E ∧
      (∀ n,TensorExtension (A n) (A (n+1))) ∧
      Monotone (fun n => (A n).units.algebra) ∧
      (∀ n,(∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n) ∧
      ∀ s,Tendsto (fun n => (A n).energy τ hNM (x s)) atTop (𝓝 0) := by
  have hex (n : ℕ) (F : FiniteMatrixStage N) := exists_tensor_finite_matrix_energy_budget τ hNM
    hfactor hdiff hirr (Finset.range (n+1)) x (fun s _ => ht s) F
    ((1/2 : ℝ)^(n+1)) (by positivity)
  let next (n : ℕ) (F : FiniteMatrixStage N) := (hex n F).choose
  let A : ℕ → FiniteMatrixStage N := fun n => Nat.rec E (fun n F => next n F) n
  have hstep (n : ℕ) : TensorExtension (A n) (A (n+1)) ∧
      (∑ s ∈ Finset.range (n+1),(A (n+1)).energy τ hNM (x s)) < (1/2 : ℝ)^(n+1) :=
    (hex n (A n)).choose_spec
  have hbudget (n : ℕ) :
      (∑ s ∈ Finset.range n,(A n).energy τ hNM (x s)) < (1/2 : ℝ)^n := by
    cases n with
    | zero => simp
    | succ n => exact (hstep n).2
  refine ⟨A,rfl,fun n => (hstep n).1,
    monotone_nat_of_le_succ (fun n => (hstep n).1.algebra_le),hbudget,?_⟩
  intro s
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => (A n).energy_nonneg τ hNM (x s)))
    ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num))
  filter_upwards [eventually_ge_atTop (s+1)] with n hn
  exact (Finset.single_le_sum (fun t _ => (A n).energy_nonneg τ hNM (x t))
    (Finset.mem_range.mpr (by omega))).trans (hbudget n).le

end Generator.FiniteMatrixStage

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixGenerators
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

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

omit [DecidableEq ι] in
theorem fullProjectionMatrix_projection [Nonempty ι] :
    IsStarProjection (fullProjectionMatrix (ι := ι)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · ext i j
    simp only [Matrix.mul_apply,fullProjectionMatrix,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  · ext i j
    simp [fullProjectionMatrix,Matrix.star_apply]

theorem fullProjection_projection [Nonempty ι] : IsStarProjection E.fullProjection :=
  (fullProjectionMatrix_projection (ι := ι)).map E.hom

omit [StarModule ℂ A] in
theorem diagonal_commute (i j : ι) : Commute (E.entry i i) (E.entry j j) := by
  show E.entry i i*E.entry j j=E.entry j j*E.entry i i
  by_cases h : i=j
  · subst j; rfl
  · simp [E.mul_entry,h,Ne.symm h]

theorem cut_fullProjection (i j : ι) :
    E.entry i i*E.fullProjection*E.entry j j=(Fintype.card ι : ℂ)⁻¹ • E.entry i j := by
  simp only [fullProjection,hom_apply,fullProjectionMatrix,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,E.mul_entry,smul_ite,smul_zero]
  simp [E.mul_entry,smul_ite]

theorem recover_entry [Nonempty ι] (i j : ι) :
    (Fintype.card ι : ℂ) • (E.entry i i*E.fullProjection*E.entry j j)=E.entry i j := by
  rw [E.cut_fullProjection,smul_smul,mul_inv_cancel₀,one_smul]
  exact_mod_cast Fintype.card_ne_zero

theorem fullProjection_mem : E.fullProjection ∈ E.algebra := ⟨_,rfl⟩

theorem algebra_le_of_projection_mem [Nonempty ι] (S : StarSubalgebra ℂ A)
    (hd : ∀ i,E.entry i i ∈ S) (hq : E.fullProjection ∈ S) : E.algebra ≤ S := by
  apply (E.algebra_le_iff S).mpr
  intro i j
  rw [← E.recover_entry i j]
  exact S.smul_mem (S.mul_mem (S.mul_mem (hd i) hq) (hd j)) _

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem countable_projection_generator {ι : Type*} [Countable ι] [Nonempty ι]
    (e : ι → (H →L[ℂ] H)) (hp : ∀ i,IsStarProjection (e i))
    (hc : ∀ i j,Commute (e i) (e j)) :
    ∃ b : H →L[ℂ] H,IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) := by
  obtain ⟨f,hf⟩ := exists_surjective_nat ι
  obtain ⟨b,hb,hn,hgen⟩ := CommutingProjectionEncoding.exists_selfAdjoint_generator
    (fun n => e (f n)) (fun n => hp (f n)) (fun n m => hc (f n) (f m))
  refine ⟨b,hb,hn,hgen.trans ?_⟩
  congr 1
  ext x
  constructor
  · rintro ⟨n,rfl⟩; exact ⟨f n,rfl⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨n,rfl⟩ := hf i
    exact ⟨n,rfl⟩

namespace MatrixUnitSystem
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem fullProjection_commute (E : MatrixUnitSystem ι A) (F : MatrixUnitSystem κ A)
    (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l)) :
    Commute E.fullProjection F.fullProjection := by
  apply (E.commute_algebra_iff _).mpr _ _ E.fullProjection_mem
  intro i j
  exact ((F.commute_algebra_iff _).mpr (fun k l => (hc i j k l).symm) _
    F.fullProjection_mem).symm

end MatrixUnitSystem
namespace FiniteMatrixStage
variable {N : VonNeumannAlgebra H}

theorem two_generators_of_commuting_factors (F : ℕ → FiniteMatrixStage N)
    (hc : ∀ n m,n ≠ m → ∀ i j k l,
      Commute ((F n).units.entry i j) ((F m).units.entry k l)) :
    ∃ a ∈ generated F,∃ b ∈ generated F,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated F := by
  classical
  let I := (n : ℕ) × Fin (F n).size
  let : Nonempty I := ⟨⟨0,⟨0,(F 0).positive⟩⟩⟩
  let (n : ℕ) : Nonempty (Fin (F n).size) := ⟨⟨0,(F n).positive⟩⟩
  let d : I → (H →L[ℂ] H) := fun i => ((F i.1).units.entry i.2 i.2).val
  let q : ℕ → (H →L[ℂ] H) := fun n => (F n).units.fullProjection.val
  have hdproj (i : I) : IsStarProjection (d i) :=
    ((F i.1).units.diagonal_projection i.2).map N.toStarSubalgebra.subtype
  have hqproj (n : ℕ) : IsStarProjection (q n) :=
    (F n).units.fullProjection_projection.map N.toStarSubalgebra.subtype
  have hdcomm (i j : I) : Commute (d i) (d j) := by
    obtain ⟨n,i⟩ := i
    obtain ⟨m,j⟩ := j
    by_cases h : n=m
    · subst m
      exact congrArg Subtype.val ((F n).units.diagonal_commute i j).eq
    · exact congrArg Subtype.val (hc n m h i i j j).eq
  have hqcomm (n m : ℕ) : Commute (q n) (q m) := by
    by_cases h : n=m
    · subst m; exact Commute.refl _
    · exact congrArg Subtype.val ((F n).units.fullProjection_commute (F m).units (hc n m h)).eq
  obtain ⟨a,ha,_,hagen⟩ := countable_projection_generator d hdproj hdcomm
  obtain ⟨b,hb,_,hbgen⟩ := countable_projection_generator q hqproj hqcomm
  have hdmem (i : I) : d i ∈ generated F :=
    stage_le_generated F i.1 (((F i.1).units.mem_concreteAlgebra _).mpr
      ((F i.1).units.entry_mem i.2 i.2))
  have hqmem (n : ℕ) : q n ∈ generated F :=
    stage_le_generated F n (((F n).units.mem_concreteAlgebra _).mpr (F n).units.fullProjection_mem)
  have hamem : a ∈ generated F := by
    have hle : wstar {a} ≤ generated F := by
      rw [hagen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨i,rfl⟩; exact hdmem i)
    exact hle (subset_wstar _ rfl)
  have hbmem : b ∈ generated F := by
    have hle : wstar {b} ≤ generated F := by
      rw [hbgen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨n,rfl⟩; exact hqmem n)
    exact hle (subset_wstar _ rfl)
  refine ⟨a,hamem,b,hbmem,ha,hb,le_antisymm ?_ ?_⟩
  · exact wstar_le (generated_closed F) (by rintro _ (rfl | rfl) <;> assumption)
  · apply generated_minimal F _ (wstar_closed _)
    intro n x hx
    let y : N.toStarSubalgebra := ⟨x,(F n).units.concreteAlgebra_le hx⟩
    let S := (wstar {a,b}).comap N.toStarSubalgebra.subtype
    have hdS (i : Fin (F n).size) : (F n).units.entry i i ∈ S := by
      change d ⟨n,i⟩ ∈ wstar {a,b}
      apply (wstar_mono (s := {a}) (t := {a,b}) (by simp))
      rw [hagen]
      exact subset_wstar (Set.range d) (Set.mem_range_self (⟨n,i⟩ : I))
    have hqS : (F n).units.fullProjection ∈ S := by
      change q n ∈ wstar {a,b}
      apply (wstar_mono (s := {b}) (t := {a,b}) (by simp))
      rw [hbgen]
      exact subset_wstar _ (Set.mem_range_self n)
    exact (F n).units.algebra_le_of_projection_mem S hdS hqS
      (((F n).units.mem_concreteAlgebra y).mp hx)

end FiniteMatrixStage

end

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/
namespace FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem concrete_le_iff (E : FiniteMatrixStage N) (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    E.units.concreteAlgebra ≤ S ↔ E.units.algebra ≤ S.comap N.toStarSubalgebra.subtype := by
  constructor
  · intro h x hx
    exact h ((E.units.mem_concreteAlgebra x).mpr hx)
  · intro h x hx
    let y : N.toStarSubalgebra := ⟨x,E.units.concreteAlgebra_le hx⟩
    exact h ((E.units.mem_concreteAlgebra y).mp hx)

theorem exists_commuting_factors_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ F : ℕ → FiniteMatrixStage N,
      (∀ n m,n ≠ m → ∀ i j k l,Commute ((F n).units.entry i j) ((F m).units.entry k l)) ∧
      generated F=generated A := by
  have hm : Monotone (fun n => (A n).units.algebra) :=
    monotone_nat_of_le_succ (fun n => (hstep n).algebra_le)
  choose F hc he using hstep
  have hFA (n : ℕ) : (F n).units.algebra ≤ (A (n+1)).units.algebra := by
    rw [he n]; exact le_sup_right
  have hcomm_lt (n m : ℕ) (hnm : n < m) (i j : Fin (F n).size) (k l : Fin (F m).size) :
      Commute ((F n).units.entry i j) ((F m).units.entry k l) := by
    exact ((A m).units.commute_algebra_iff _).mpr (fun a b => hc m a b k l) _
      (hm (Nat.succ_le_of_lt hnm) (hFA n ((F n).units.entry_mem i j)))
  refine ⟨F,?_,le_antisymm ?_ ?_⟩
  · intro n m hnm i j k l
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hcomm_lt n m h i j k l
    · exact (hcomm_lt m n h k l i j).symm
  · apply generated_minimal F _ (generated_closed A)
    intro n
    apply ((F n).concrete_le_iff _).mpr
    exact (hFA n).trans (((A (n+1)).concrete_le_iff _).mp (stage_le_generated A (n+1)))
  · apply generated_minimal A _ (generated_closed F)
    intro n
    apply ((A n).concrete_le_iff _).mpr
    induction n with
    | zero =>
      rw [hzero]
      apply ((scalarStage N).units.algebra_le_iff _).mpr
      intro i j
      exact (generated F).one_mem
    | succ n ih =>
      rw [he n]
      exact sup_le ih (((F n).concrete_le_iff _).mp (stage_le_generated F n))

theorem two_generators_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ a ∈ generated A,∃ b ∈ generated A,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated A := by
  obtain ⟨F,hF,hgen⟩ := exists_commuting_factors_of_tensor_extensions A hzero hstep
  rw [← hgen]
  exact two_generators_of_commuting_factors F hF

end FiniteMatrixStage

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/
namespace Tracial
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_irreducible_two_generated_subfactor
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ P : VonNeumannAlgebra H,P ≤ N ∧ IsII1Factor P.toStarSubalgebra ∧
      (∀ c : M.toStarSubalgebra,(∀ a : P.toStarSubalgebra,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra)) ∧
      ∃ a ∈ P,∃ b ∈ P,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=P.toStarSubalgebra := by
  let S : Set M.toStarSubalgebra := {b | τ.trace b=0}
  obtain ⟨x,hx,hdense⟩ := exists_countable_norm₂_dense τ S
    ⟨0,by change τ.trace 0=0; simp [TracialRepresentation.trace]⟩
    (hsep.mono (Set.image_subset_range _ _))
  obtain ⟨A,hA,hstep,_,_,hlim⟩ := exists_countable_tensor_refinement τ hNM
    hfactor hdiff hirr x hx (scalarStage N)
  have hscalar := generated_relative_scalar A τ hNM
    (scalar_common_commutant_of_dense_energy_decay τ hNM A x hdense hlim)
  obtain ⟨a,ha,b,hb,hsa,hsb,hgen⟩ := two_generators_of_tensor_extensions A hA hstep
  exact ⟨generatedVonNeumann A,generatedVonNeumann_le A,
    generated_isII1 A τ hNM hdiff hscalar,hscalar,a,ha,b,hb,hsa,hsb,hgen⟩

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Generation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Relative generation under represented-factor hypotheses: unitaries in a dense G-delta set satisfy W*(N,u)=M. -/
open Filter
open scoped Topology

/-! Four generators under a faithful normalized vector trace and trace-vector separability. -/
open scoped ComplexStarModule
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem represented_four_selfAdjoint_generators_q129_oai (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ a ∈ M,∃ b ∈ M,∃ c ∈ M,∃ d ∈ M,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ IsSelfAdjoint c ∧ IsSelfAdjoint d ∧
      wstar {a,b,c,d}=M.toStarSubalgebra := by
  obtain ⟨P,hPM,hP,hscalar,a,ha,b,hb,hsa,hsb,hPgen⟩ :=
    exists_irreducible_two_generated_subfactor τ le_rfl hfactor hdiff
      (fun c hc => hfactor c hc) hsep
  have hPfactor (c : P.toStarSubalgebra) (hc : ∀ a : P.toStarSubalgebra,a*c=c*a) :
      ∃ z : ℂ,c=z • (1 : P.toStarSubalgebra) := by
    obtain ⟨z,hz⟩ := hP.factor c hc
    exact ⟨z,by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hirr (c : M.toStarSubalgebra)
      (hc : ∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) :
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) :=
    ⟨τ.trace c,hscalar c (fun a => congrArg Subtype.val (hc a))⟩
  obtain ⟨C,_,hC,hgen⟩ := represented_relative_generation_q129 τ hPM hPfactor hP.diffuse hirr hsep
  let : Nonempty (TraceUnitary τ) := ⟨⟨1⟩⟩
  obtain ⟨u,hu⟩ := hC.nonempty
  let v : H →L[ℂ] H := (u.algebra τ).val
  have hv : v ∈ M.toStarSubalgebra := (u.algebra τ).property
  have hvgen : wstar ((P : Set (H →L[ℂ] H)) ∪ {v})=M.toStarSubalgebra := hgen u hu
  refine ⟨a,hPM ha,b,hPM hb,ℜ v,realPart_mem _ hv,ℑ v,imaginaryPart_mem _ hv,
    hsa,hsb,(ℜ v).property,(ℑ v).property,le_antisymm ?_ ?_⟩
  · exact wstar_le (vonNeumann_wotClosed M)
      (by rintro _ (rfl | rfl | rfl | rfl)
          · exact hPM ha
          · exact hPM hb
          · exact realPart_mem _ hv
          · exact imaginaryPart_mem _ hv)
  · let Q := wstar {a,b,(ℜ v : H →L[ℂ] H),(ℑ v : H →L[ℂ] H)}
    have hPQ : P.toStarSubalgebra ≤ Q := by
      rw [← hPgen]
      exact wstar_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢; tauto)
    rw [← hvgen]
    apply wstar_le (wstar_closed _)
    rintro x (hx | rfl)
    · exact hPQ hx
    · apply (mem_iff_parts_mem Q v).mpr
      exact ⟨subset_wstar _ (by simp),subset_wstar _ (by simp)⟩

end

/-! Single generation for the explicit faithful normalized vector-trace
representation with separable trace-vector range. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129_oai.{u_1} := @OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129_oai.{u_1}
