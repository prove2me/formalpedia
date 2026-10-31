-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:14:09.630187+00:00
-- url     : https://prove2.me/submissions/8a48794f-9023-4faf-beb2-a492e2631073

import Mathlib
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_Tracial_exists_normal_matrix_approximation

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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_EnergyDescent
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
local instance expectationPosPreorder_r2bfb0a_1 : Preorder M.toStarSubalgebra :=
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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem exists_irreducible_matrix_energy_descent_oai (hNM : N ≤ M)
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
  obtain ⟨k,n,hn,E,c,hc⟩ := exists_normal_matrix_approximation (restrictedTrace τ hNM)
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

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent_oai.{u_1} := @OAI.Generator.Tracial.exists_irreducible_matrix_energy_descent_oai.{u_1}
