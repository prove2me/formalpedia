-- Prove2me | solution 1 for OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:08:37.41941+00:00
-- url     : https://prove2.me/submissions/4a44a1ac-de89-45b5-ad35-303a832703e8

import Mathlib
import Definitions.Def_OAIQ11Fg008
import Definitions.Def_OAIQ11Fg009
import Definitions.Def_OAIQ11Fg010
import Theorems.Thm_OAI_Generator_Tracial_CornerPartition_block_commutant_mem_subalgebra

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.vectorOrbitClosure_complete
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
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_sub (x y : M.toStarSubalgebra) :
    Q.pinch (x-y) = Q.pinch x - Q.pinch y := by
  simp [pinch, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem pinch_left (i : Fin Q.size) (x : M.toStarSubalgebra) :
    (Q.piece i).val * Q.pinch x = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [← mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [← mul_assoc, Q.orthogonal i j hji.symm, zero_mul]
  · simp

theorem pinch_right (i : Fin Q.size) (x : M.toStarSubalgebra) :
    Q.pinch x * (Q.piece i).val = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [mul_assoc, Q.orthogonal j i hji, mul_zero]
  · simp

theorem pinch_idempotent (x : M.toStarSubalgebra) : Q.pinch (Q.pinch x) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change (Q.piece i).val * Q.pinch x * (Q.piece i).val = _
  rw [Q.pinch_left]
  simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

theorem trace_compression_pairing (q : AlgebraProjection M) (x y : M.toStarSubalgebra) :
    τ.trace (star (q.val*x*q.val)*y) = τ.trace (star x*(q.val*y*q.val)) := by
  simp only [star_mul, q.property.isSelfAdjoint.star_eq]
  rw [mul_assoc q.val (star x*q.val), τ.trace_mul_comm q.val]
  simp only [mul_assoc]

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_pairing (x y : M.toStarSubalgebra) :
    τ.trace (star (Q.pinch x)*y) = τ.trace (star x*Q.pinch y) := by
  simp only [pinch, star_sum, Finset.sum_mul, Finset.mul_sum]
  change coordinateTraceLinear τ _ = coordinateTraceLinear τ _
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i _ => trace_compression_pairing τ (Q.piece i) x y)

theorem pinch_residual_orthogonal (x : M.toStarSubalgebra) :
    inner ℂ (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x)) = 0 := by
  rw [baseVector_inner_trace]
  rw [Q.pinch_pairing τ, Q.pinch_sub, Q.pinch_idempotent, sub_self, mul_zero]
  exact inner_zero_right _

theorem pinch_pythagoras (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 + τ.norm₂ (x-Q.pinch x)^2 = τ.norm₂ x^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x))
    (Q.pinch_residual_orthogonal τ x)
  rw [← map_add, add_sub_cancel] at h
  change τ.norm₂ x * τ.norm₂ x = τ.norm₂ (Q.pinch x)*τ.norm₂ (Q.pinch x) +
    τ.norm₂ (x-Q.pinch x)*τ.norm₂ (x-Q.pinch x) at h
  simpa only [pow_two] using h.symm

theorem pinch_norm₂_le (x : M.toStarSubalgebra) : τ.norm₂ (Q.pinch x) ≤ τ.norm₂ x := by
  have h := Q.pinch_pythagoras τ x
  nlinarith [sq_nonneg (τ.norm₂ (x-Q.pinch x)), show 0 ≤ τ.norm₂ x from norm_nonneg _,
    show 0 ≤ τ.norm₂ (Q.pinch x) from norm_nonneg _]

theorem pinch_block_orthogonal (x : M.toStarSubalgebra) (i j : Fin Q.size) (hij : i ≠ j) :
    star ((Q.piece i).val*x*(Q.piece i).val) * ((Q.piece j).val*x*(Q.piece j).val) = 0 := by
  simp only [star_mul, (Q.piece i).property.isSelfAdjoint.star_eq]
  calc (Q.piece i).val*star x*(Q.piece i).val*((Q.piece j).val*x*(Q.piece j).val) =
      ((Q.piece i).val*star x)*((Q.piece i).val*(Q.piece j).val)*x*(Q.piece j).val := by
        simp only [mul_assoc]
    _ = 0 := by rw [Q.orthogonal i j hij, mul_zero, zero_mul, zero_mul]

theorem pinch_energy (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 = ∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2 := by
  have h : star (Q.pinch x)*Q.pinch x =
      ∑ i, star ((Q.piece i).val*x*(Q.piece i).val)*((Q.piece i).val*x*(Q.piece i).val) := by
    simp only [pinch, star_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => Q.pinch_block_orthogonal x j i hji)
      (by simp)
  rw [norm₂_sq_trace τ, h]
  change (coordinateTraceLinear τ _).re = _
  rw [map_sum, Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => (norm₂_sq_trace τ _).symm)

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem pinch_compress_of_le (r : AlgebraProjection M) (i : Fin Q.size)
    (hr : r ≤ Q.piece i) (x : M.toStarSubalgebra) :
    r.val*Q.pinch x*r.val = r.val*x*r.val := by
  have hl : (Q.piece i).val*r.val = r.val := hr
  have hright := projection_mul_of_le hr
  calc r.val*Q.pinch x*r.val = (r.val*(Q.piece i).val)*Q.pinch x*r.val := by rw [hright]
    _ = r.val*((Q.piece i).val*Q.pinch x)*r.val := by rw [mul_assoc r.val]
    _ = r.val*((Q.piece i).val*x*(Q.piece i).val)*r.val := by rw [Q.pinch_left]
    _ = r.val*x*r.val := by
      simp only [← mul_assoc, hright]
      simp only [mul_assoc, hl]

theorem pinch_refinement (R : CornerPartition p) (h : Q.Refines R) (x : M.toStarSubalgebra) :
    R.pinch (Q.pinch x) = R.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj⟩ := h i
  exact Q.pinch_compress_of_le (R.piece i) j hj x

theorem refinement_energy_le (R : CornerPartition p) (h : Q.Refines R)
    (x : M.toStarSubalgebra) :
    (∑ i, τ.norm₂ ((R.piece i).val*x*(R.piece i).val)^2) ≤
      ∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2 := by
  rw [← R.pinch_energy τ, ← Q.pinch_energy τ, ← Q.pinch_refinement R h x]
  exact pow_le_pow_left₀ (norm_nonneg _) (R.pinch_norm₂_le τ (Q.pinch x)) 2

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem refines_refl : Q.Refines Q := fun i => ⟨i,le_refl _⟩

theorem refines_trans {R S : CornerPartition p} (hQR : Q.Refines R) (hRS : R.Refines S) :
    Q.Refines S := by
  intro i
  obtain ⟨j,hj⟩ := hRS i
  obtain ⟨k,hk⟩ := hQR j
  exact ⟨k,hj.trans hk⟩

end CornerPartition

end

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

theorem joint_refines_left : Q.Refines (Q.joint R hc) := by
  intro i
  let a := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm i
  exact ⟨a.1,Q.jointPiece_le_left R hc a⟩

theorem joint_refines_right : R.Refines (Q.joint R hc) := by
  intro i
  let a := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm i
  exact ⟨a.2,Q.jointPiece_le_right R hc a⟩

end CornerPartition

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

theorem exists_unitary_spectral_approximation (u : unitary M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      ‖(u : M.toStarSubalgebra)-∑ i, c i • (Q.piece i).val‖ < ε := by
  let : IsStarNormal (u : M.toStarSubalgebra) := ⟨by change star (u : M.toStarSubalgebra)*(u : M.toStarSubalgebra) = (u : M.toStarSubalgebra)*star (u : M.toStarSubalgebra); rw [u.property.1,u.property.2]⟩
  exact exists_normal_spectral_approximation (u : M.toStarSubalgebra) ε hε

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem includedUnitPartition_mem (h : N ≤ M) (Q : CornerPartition (identityProjection N))
    (i : Fin Q.size) : ((includedUnitPartition h Q).piece i).val.val ∈ N :=
  (Q.piece i).val.property

theorem exists_unitary_subalgebra_spectral_approximation (h : N ≤ M)
    (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra).val ∈ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      (∀ i, (Q.piece i).val.val ∈ N) ∧
      ‖(u : M.toStarSubalgebra)-∑ i, c i • (Q.piece i).val‖ < ε := by
  let uN : unitary N.toStarSubalgebra := ⟨⟨(u : M.toStarSubalgebra).val,hu⟩,by
    constructor
    · apply Subtype.ext
      exact congrArg (fun z : M.toStarSubalgebra => z.val) u.property.1
    · apply Subtype.ext
      exact congrArg (fun z : M.toStarSubalgebra => z.val) u.property.2⟩
  obtain ⟨Q,c,hc⟩ := exists_unitary_spectral_approximation uN ε hε
  refine ⟨includedUnitPartition h Q,c,includedUnitPartition_mem h Q,?_⟩
  have hn : ‖algebraInclusion h ((uN : N.toStarSubalgebra)-
      ∑ i,c i • (Q.piece i).val)‖=‖(uN : N.toStarSubalgebra)-
      ∑ i,c i • (Q.piece i).val‖ := rfl
  rw [map_sub,map_sum] at hn
  simp only [map_smul] at hn
  change ‖(u : M.toStarSubalgebra)-∑ i,c i • algebraInclusion h (Q.piece i).val‖ < ε
  exact hn ▸ hc

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem blockVonNeumann_le (N : VonNeumannAlgebra H) : Q.blockVonNeumann N ≤ N :=
  fun _ h => h.1

theorem blockVonNeumann_mem_iff (N : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    a.val ∈ Q.blockVonNeumann N ↔ a.val ∈ N ∧ ∀ i, Commute (Q.piece i).val a := by
  constructor
  · rintro ⟨ha,hc⟩
    exact ⟨ha,fun i => Subtype.ext (hc i)⟩
  · rintro ⟨ha,hc⟩
    exact ⟨ha,fun i => congrArg Subtype.val (hc i).eq⟩

end CornerPartition

end

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

theorem compression (p : AlgebraProjection M) (hp : p.val ∈ P) :
    TraceOrthogonal τ P (p.val*x*p.val) := by
  intro a
  have h := hx ⟨p.val*(a : M.toStarSubalgebra)*p.val,P.mul_mem (P.mul_mem hp a.property) hp⟩
  change τ.trace ((p.val*(a : M.toStarSubalgebra)*p.val)*x)=0 at h
  calc τ.trace ((a : M.toStarSubalgebra)*(p.val*x*p.val)) =
      τ.trace (p.val*((a : M.toStarSubalgebra)*(p.val*x))) := by
        rw [← mul_assoc (a : M.toStarSubalgebra),τ.trace_mul_comm]
    _ = 0 := by simpa only [mul_assoc] using h

theorem conjugate (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra) ∈ P) :
    TraceOrthogonal τ P (conjugateLinear u x) := by
  intro a
  have h := hx ⟨star (u : M.toStarSubalgebra)*(a : M.toStarSubalgebra)*(u : M.toStarSubalgebra),
    P.mul_mem (P.mul_mem (P.star_mem' hu) a.property) hu⟩
  change τ.trace ((a : M.toStarSubalgebra)*((u : M.toStarSubalgebra)*x*star (u : M.toStarSubalgebra)))=0
  rw [← mul_assoc (a : M.toStarSubalgebra),τ.trace_mul_comm]
  simpa only [mul_assoc] using h

theorem pinch {p : AlgebraProjection M} (Q : CornerPartition p)
    (hQ : ∀ i,(Q.piece i).val ∈ P) : TraceOrthogonal τ P (Q.pinch x) := by
  intro a
  change coordinateTraceLinear τ ((a : M.toStarSubalgebra)*∑ i,(Q.piece i).val*x*(Q.piece i).val)=0
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_eq_zero (fun i _ => hx.compression τ (Q.piece i) (hQ i) a)

end TraceOrthogonal

/-- If an orthogonal operator is averaged by subalgebra unitaries and all
fixed points lie in the subalgebra, the actual least-norm orbit point is zero. -/
theorem zero_mem_orbitHull_of_orthogonal
    (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (G : Subgroup (unitary M.toStarSubalgebra))
    (hG : ∀ u : G,(u.val : M.toStarSubalgebra) ∈ P)
    (hfixed : ∀ c : M.toStarSubalgebra,
      (∀ u : G,conjugateLinear u.val c=c) → c ∈ P)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ P x) :
    (0 : H) ∈ traceOrbitHull τ G x := by
  obtain ⟨c,_,hc,_,hfix⟩ := traceOrbitHull_minimum τ G x
  have hcP := hfixed c hfix
  have htest : ∀ u : G,τ.trace (star c*conjugateLinear u.val x)=0 :=
    fun u => (hx.conjugate τ u.val (hG u)) ⟨star c,P.star_mem' hcP⟩
  have hz := orbitHull_trace_test_zero τ G x c htest hc
  have hv : baseVector τ c=0 := inner_self_eq_zero.mp hz
  exact hv ▸ hc

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
-- module Solutions.OAIQ11_FG.FactorGeneration_EnergyDescent
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

/-! Finite spectral approximation yields an actual energy-decreasing partition.
The displacement premise is explicit; no small-energy partition is assumed. -/

theorem spectral_sum_commutes_pinch (c : Fin Q.size → ℂ) (x : M.toStarSubalgebra) :
    projectionSum Q.piece c * Q.pinch x = Q.pinch x * projectionSum Q.piece c := by
  simp only [projectionSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Q.pinch_left, Q.pinch_right]

theorem commutator_le_residual (v x : M.toStarSubalgebra)
    (hc : v*Q.pinch x=Q.pinch x*v) :
    τ.norm₂ (v*x-x*v) ≤ 2*‖v‖*τ.norm₂ (x-Q.pinch x) := by
  have he : v*x-x*v=v*(x-Q.pinch x)-(x-Q.pinch x)*v := by
    simp only [mul_sub,sub_mul]
    rw [hc]
    abel
  rw [he]
  have h := norm_sub_le (baseVector τ (v*(x-Q.pinch x)))
    (baseVector τ ((x-Q.pinch x)*v))
  change τ.norm₂ (v*(x-Q.pinch x)-(x-Q.pinch x)*v) ≤
    τ.norm₂ (v*(x-Q.pinch x))+τ.norm₂ ((x-Q.pinch x)*v) at h
  have hl := τ.norm₂_mul_le v (x-Q.pinch x)
  have hr := τ.norm₂_mul_le_right (x-Q.pinch x) v
  nlinarith

end CornerPartition

theorem commutator_perturbation (u v x : M.toStarSubalgebra) :
    τ.norm₂ (u*x-x*u) ≤ τ.norm₂ (v*x-x*v)+2*‖u-v‖*τ.norm₂ x := by
  have he : u*x-x*u=(v*x-x*v)+((u-v)*x-x*(u-v)) := by noncomm_ring
  rw [he]
  have h := τ.norm₂_add_le (v*x-x*v) ((u-v)*x-x*(u-v))
  have h' := norm_sub_le (baseVector τ ((u-v)*x)) (baseVector τ (x*(u-v)))
  change τ.norm₂ ((u-v)*x-x*(u-v)) ≤ τ.norm₂ ((u-v)*x)+τ.norm₂ (x*(u-v)) at h'
  have hl := τ.norm₂_mul_le (u-v) x
  have hr := τ.norm₂_mul_le_right x (u-v)
  nlinarith

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

/-- Energy decrease from a spectral approximation, with the actual
partition and approximation error exposed. -/
theorem CornerPartition.energy_descent_of_spectral_approximation
    {p : AlgebraProjection M} (Q : CornerPartition p)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (c : Fin Q.size → ℂ)
    (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x))
    (hclose : ‖(u : M.toStarSubalgebra)-∑ i,c i • (Q.piece i).val‖ < 1/4) :
    (∑ i,τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤
      (63/64 : ℝ)*τ.norm₂ x^2 := by
  let v := projectionSum Q.piece c
  change ‖(u : M.toStarSubalgebra)-v‖ < 1/4 at hclose
  have hv : ‖v‖ ≤ 2 := by
    have h := norm_sub_le (u : M.toStarSubalgebra) ((u : M.toStarSubalgebra)-v)
    rw [sub_sub_cancel] at h
    have hu := unitary_norm_le (u : M.toStarSubalgebra) (by simp)
    linarith
  have he := Q.commutator_le_residual τ v x (Q.spectral_sum_commutes_pinch c x)
  have hp := commutator_perturbation τ (u : M.toStarSubalgebra) v x
  have hd' := displacement_le_commutator τ u x
  have hn : 0 ≤ τ.norm₂ x := norm_nonneg _
  have hr : 0 ≤ τ.norm₂ (x-Q.pinch x) := norm_nonneg _
  have hres : τ.norm₂ x/8 ≤ τ.norm₂ (x-Q.pinch x) := by
    have hv' := mul_le_mul_of_nonneg_right hv hr
    have hc' := mul_le_mul_of_nonneg_right hclose.le hn
    nlinarith
  rw [← Q.pinch_energy τ]
  have hpy := Q.pinch_pythagoras τ x
  nlinarith [sq_nonneg (τ.norm₂ (x-Q.pinch x)-τ.norm₂ x/8)]

end

/-! The one-step energy decrease has pieces in the prescribed von Neumann
subalgebra. Irreducibility supplies the unitary, not an assumed energy budget. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_subalgebra_partition_energy_descent (h : N ≤ M)
    (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra).val ∈ N)
    (x : M.toStarSubalgebra) (hd : τ.norm₂ x ≤ τ.norm₂ (conjugateLinear u x-x)) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i,τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2) ≤
        (63/64 : ℝ)*τ.norm₂ x^2 := by
  obtain ⟨Q,c,hQ,hc⟩ := exists_unitary_subalgebra_spectral_approximation h u hu (1/4) (by norm_num)
  exact ⟨Q,hQ,Q.energy_descent_of_spectral_approximation τ u x c hd hc⟩

end

/-! Strict displacement from zero in the actual closed convex orbit hull,
without imposing a scalar commutant on a block diagonal algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_strict_displacement_of_zero_orbitHull
    (G : Subgroup (unitary M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : x ≠ 0)
    (hzero : (0 : H) ∈ traceOrbitHull τ G x) :
    ∃ u : G, τ.norm₂ x < τ.norm₂ (conjugateLinear u.val x-x) := by
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
  have horbit : baseVector τ '' algebraOrbit G x ⊆ K := by
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
  have hzero := (closure_minimal (convexHull_min horbit hconv) hclosed) hzero
  change τ.norm₂ x^2/2 ≤ (inner ℂ (baseVector τ x) 0).re at hzero
  rw [inner_zero_right, Complex.zero_re] at hzero
  have hpos : 0 < τ.norm₂ x^2 := sq_pos_of_ne_zero (fun he => hx ((τ.norm₂_eq_zero_iff x).mp he))
  linarith

end

/-! Actual compatible 63/64 descent for the orthogonal component of Popa
A.1.1 in an irreducible inclusion. Both displacement and finite spectral
partitions are constructed, and all pieces remain in the prescribed N. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection M))

theorem exists_compatible_orthogonal_descent (hNM : N ≤ M)
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      τ.norm₂ (R.pinch x)^2 ≤ (63/64 : ℝ)*τ.norm₂ (Q.pinch x)^2 := by
  by_cases hz : Q.pinch x=0
  · refine ⟨Q,Q.refines_refl,hN,?_⟩
    rw [hz]
    change ‖(0 : H)‖^2 ≤ (63/64 : ℝ)*‖(0 : H)‖^2
    simp
  let B := Q.blockVonNeumann N
  let P := insideAlgebra (M := M) (P := N)
  let D := insideAlgebra (M := M) (P := B)
  have hDP : ∀ a : M.toStarSubalgebra,a ∈ D → a ∈ P :=
    fun a ha => (Q.blockVonNeumann_le N) ha
  have hzero : (0 : H) ∈ traceOrbitHull τ (subalgebraUnitaries D) (Q.pinch x) := by
    apply zero_mem_orbitHull_of_orthogonal τ P (subalgebraUnitaries D)
      (fun u => hDP _ u.property)
    · intro c hc
      exact Q.block_commutant_mem_subalgebra τ hN hirr c
        (commutes_of_fixed_unitaries D c hc)
    · exact hx.pinch τ Q hN
  obtain ⟨u,hu⟩ := exists_strict_displacement_of_zero_orbitHull τ
    (subalgebraUnitaries D) (Q.pinch x) hz hzero
  obtain ⟨S,hS,he⟩ := exists_subalgebra_partition_energy_descent τ
    ((Q.blockVonNeumann_le N).trans hNM) u.val u.property (Q.pinch x) hu.le
  have hcross (i : Fin Q.size) (j : Fin S.size) :
      Commute (Q.piece i).val (S.piece j).val :=
    ((Q.blockVonNeumann_mem_iff N _).mp (hS j)).2 i
  let R := Q.joint S hcross
  have hQR : Q.Refines R := Q.joint_refines_left S hcross
  have hSR : S.Refines R := Q.joint_refines_right S hcross
  refine ⟨R,hQR,?_,?_⟩
  · intro i
    let a := (Fintype.equivFin (Fin Q.size × Fin S.size)).symm i
    change ((Q.piece a.1).val*(S.piece a.2).val).val ∈ N
    exact N.mul_mem (hN a.1) ((Q.blockVonNeumann_le N) (hS a.2))
  · have hh := S.refinement_energy_le τ R hSR (Q.pinch x)
    rw [← R.pinch_energy τ,← S.pinch_energy τ,Q.pinch_refinement R hQR] at hh
    rw [← S.pinch_energy τ] at he
    exact hh.trans he

end CornerPartition

end

/-! Geometric iteration and finite-family small-energy partitions for the
orthogonal component. No energy budget or block displacement is assumed. -/
section
open scoped BigOperators Topology
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (hNM : N ≤ M)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : insideAlgebra (M := M) (P := N),
    (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hNM hirr

theorem exists_orthogonal_geometric_refinement
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x)
    (n : ℕ) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      τ.norm₂ (R.pinch x)^2 ≤ (63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2 := by
  induction n with
  | zero => exact ⟨Q,Q.refines_refl,hN,by simp⟩
  | succ n ih =>
    obtain ⟨R,hQR,hR,hE⟩ := ih
    obtain ⟨S,hRS,hS,hSenergy⟩ := R.exists_compatible_orthogonal_descent τ hNM hR hirr x hx
    refine ⟨S,Q.refines_trans hQR hRS,hS,?_⟩
    calc τ.norm₂ (S.pinch x)^2 ≤ (63/64 : ℝ)*τ.norm₂ (R.pinch x)^2 := hSenergy
      _ ≤ (63/64 : ℝ)*((63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2) :=
        mul_le_mul_of_nonneg_left hE (by norm_num)
      _ = (63/64 : ℝ)^(n+1)*τ.norm₂ (Q.pinch x)^2 := by ring

theorem exists_orthogonal_refinement_budget
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    (x : M.toStarSubalgebra) (hx : TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) x)
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ τ.norm₂ (R.pinch x)^2 < b := by
  have ht : Tendsto (fun n : ℕ => (63/64 : ℝ)^n*τ.norm₂ (Q.pinch x)^2) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 63/64)
        (by norm_num : (63/64 : ℝ) < 1)).mul_const (τ.norm₂ (Q.pinch x)^2)
  obtain ⟨n,hn⟩ := (ht.eventually (Iio_mem_nhds hb)).exists
  obtain ⟨R,hQR,hR,hE⟩ := exists_orthogonal_geometric_refinement τ hNM hirr Q hN x hx n
  exact ⟨R,hQR,hR,hE.trans_lt hn⟩

theorem exists_indexed_orthogonal_refinement_budget_oai
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    {ι : Type*} (F : Finset ι) (v : ι → M.toStarSubalgebra)
    (hF : ∀ x ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (v x))
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ (∑ x ∈ F,τ.norm₂ (R.pinch (v x))^2) < b := by
  classical
  induction F using Finset.induction_on generalizing Q b with
  | empty => exact ⟨Q,Q.refines_refl,hN,by simpa using hb⟩
  | @insert x F hxF ih =>
    obtain ⟨R,hQR,hR,hx⟩ := exists_orthogonal_refinement_budget τ hNM hirr Q hN (v x)
      (hF x (Finset.mem_insert_self x F)) (b/2) (half_pos hb)
    obtain ⟨S,hRS,hS,hFS⟩ := ih R hR
      (fun y hy => hF y (Finset.mem_insert_of_mem hy)) (b/2) (half_pos hb)
    refine ⟨S,Q.refines_trans hQR hRS,hS,?_⟩
    have hxS := R.refinement_energy_le τ S hRS (v x)
    rw [← R.pinch_energy τ,← S.pinch_energy τ] at hxS
    rw [Finset.sum_insert hxF]
    linarith

end CornerPartition

end

/-! Assembly of the orthogonal budget with an explicitly controlled
subalgebra component. This constructs the further refinement; constructing
the initial subalgebra-component budget is not asserted here. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_oai.{u_1, u_2} := @OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_oai.{u_1, u_2}
