-- Prove2me | solution 1 for OAI.Generator.Tracial.representedCorner_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:20:08.006125+00:00
-- url     : https://prove2.me/submissions/bcabb91f-b353-460a-a88b-2c13d212acb5

import Mathlib
import Definitions.Def_OAIQ11Fg012

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ11_FG.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ11_FG.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include τ hirr in
/-- A self-adjoint element of the relative corner commutant is scalar in
that corner, including the zero corner. -/
theorem selfAdjoint_corner_commutant_scalar (p : AlgebraProjection M)
    (c : M.toStarSubalgebra) (hc : IsSelfAdjoint c)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  let L : Submodule ℂ M.toStarSubalgebra := Submodule.span ℂ {p.val}
  have hclosed : IsClosed (L : Set M.toStarSubalgebra) := L.closed_of_finiteDimensional
  have hcL : c ∈ closure (L : Set M.toStarSubalgebra) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q,d,hfix,hQ,hd⟩ :=
      exists_finite_spectral_approximation_preserving_commutant p c hc ε hε
    have hpieces (i : Fin Q.size) : (Q.piece i).val ∈ L := by
      have htriv := corner_commutant_projection_trivial τ P hirr p (Q.piece i)
        (Q.piece_le i) (fun a => hQ (p.val*(a : M.toStarSubalgebra)*p.val)
          (hcomm a) (by
            show p.val*(p.val*(a : M.toStarSubalgebra)*p.val)=
              (p.val*(a : M.toStarSubalgebra)*p.val)*p.val
            simp only [← mul_assoc,p.property.isIdempotentElem.eq]
            simp only [mul_assoc,p.property.isIdempotentElem.eq]) i)
      rcases htriv with h | h
      · rw [h]; exact L.zero_mem
      · rw [h]; exact Submodule.subset_span (Set.mem_singleton _)
    refine ⟨∑ i, (d i : ℂ) • (Q.piece i).val,
      L.sum_mem (fun i _ => L.smul_mem _ (hpieces i)),?_⟩
    simpa only [dist_eq_norm,hl,hr] using hd
  have hm : c ∈ L := by
    change c ∈ (L : Set M.toStarSubalgebra)
    rw [← hclosed.closure_eq]
    exact hcL
  exact Submodule.mem_span_singleton.mp hm |>.imp (fun z hz => hz.symm)

omit [CompleteSpace P] in
/-- Taking adjoints preserves the supported relative-commutant condition. -/
theorem corner_commutant_star (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∀ a : P, Commute (star c) (p.val*(a : M.toStarSubalgebra)*p.val) := by
  intro a
  have h := congrArg star (hcomm (star a)).eq
  change star (c*(p.val*star (a : M.toStarSubalgebra)*p.val)) =
    star ((p.val*star (a : M.toStarSubalgebra)*p.val)*c) at h
  show star c*(p.val*(a : M.toStarSubalgebra)*p.val)=
    (p.val*(a : M.toStarSubalgebra)*p.val)*star c
  simpa only [star_mul,star_star,p.property.isSelfAdjoint.star_eq,
    mul_assoc] using h.symm

include τ hirr in
/-- Exact irreducibility in pMp, stated in ambient coordinates. The scalar
is the normalized corner trace when p is nonzero. -/
theorem corner_commutant_scalar (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hl : p.val*c=c) (hr : c*p.val=c)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∃ z : ℂ, c=z • p.val := by
  have hsl : p.val*star c=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hr
  have hsr : star c*p.val=star c := by
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq] using congrArg star hl
  have hstar := corner_commutant_star P p c hcomm
  have hreal : ∀ a : P, Commute (ℜ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hstar a)).smul_left (2 : ℝ)⁻¹
  have himag : ∀ a : P, Commute (ℑ c : M.toStarSubalgebra)
      (p.val*(a : M.toStarSubalgebra)*p.val) := by
    intro a
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hstar a)).smul_left (2 : ℝ)⁻¹).smul_left (-Complex.I)
  obtain ⟨a,ha⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℜ c)
    (ℜ c).property (by simp [realPart_apply_coe,mul_add,hl,hsl])
    (by simp [realPart_apply_coe,add_mul,hr,hsr]) hreal
  obtain ⟨b,hb⟩ := selfAdjoint_corner_commutant_scalar τ P hirr p (ℑ c)
    (ℑ c).property (by simp [imaginaryPart_apply_coe,mul_sub,hl,hsl])
    (by simp [imaginaryPart_apply_coe,sub_mul,hr,hsr]) himag
  refine ⟨a+Complex.I*b,?_⟩
  calc c = (ℜ c : M.toStarSubalgebra)+Complex.I • (ℑ c : M.toStarSubalgebra) :=
      (realPart_add_I_smul_imaginaryPart c).symm
    _ = (a+Complex.I*b) • p.val := by rw [ha,hb,smul_smul,add_smul]

end

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual corner on pH. Extension by zero identifies its operators with
supported ambient operators; weak closedness is proved by WOT continuity. -/

/-! The normalized faithful vector trace on the actual corner pH. -/

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

include τ in
theorem representedCorner_irreducible_oai (hpN : p.val.val ∈ N) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (representedCorner p).toStarSubalgebra,
      (∀ a : (representedSubcorner p hpN).toStarSubalgebra,
        coordinateInclusion (representedSubcorner_le p hpN hNM) a*c=
          c*coordinateInclusion (representedSubcorner_le p hpN hNM) a) →
      ∃ z : ℂ,c=z • (1 : (representedCorner p).toStarSubalgebra) := by
  intro c hc
  have hirr' : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),(a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hh
    exact hirr c (fun a => hh ⟨coordinateInclusion hNM a,a.property⟩)
  obtain ⟨z,hz⟩ := corner_commutant_scalar τ (insideAlgebra (M := M) (P := N)) hirr' p
    (cornerEmbedding p c) (cornerEmbedding_left p c) (cornerEmbedding_right p c) (by
      intro a
      let b : (representedSubcorner p hpN).toStarSubalgebra :=
        cornerCompress (projectionInSubalgebra p hpN) ⟨a.val.val,a.property⟩
      have hb : cornerEmbedding p
          (coordinateInclusion (representedSubcorner_le p hpN hNM) b)=p.val*a.val*p.val :=
        Subtype.ext (cornerExtend_compress p a.val.val)
      have h := congrArg (cornerEmbedding p) (hc b)
      rw [map_mul,map_mul,hb] at h
      exact h.symm)
  refine ⟨z,cornerEmbedding_injective p ?_⟩
  simpa only [map_smul,cornerEmbedding_one] using hz

end

/-! Transport actual unit partitions on pH to ambient partitions of p. -/

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.representedCorner_irreducible_oai.{u_1} := @OAI.Generator.Tracial.representedCorner_irreducible_oai.{u_1}
