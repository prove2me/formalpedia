-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_unitResidual_local_compression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:18:39.480769+00:00
-- url     : https://prove2.me/submissions/1a11fb0f-055d-4516-a72b-ad5f1679941d

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_FiniteMatrixStage_exists_irreducible_matrix_generated_II1
import Theorems.Thm_OAI_Generator_FiniteMatrixStage_exists_matrix_generated_centered_partition
import Theorems.Thm_OAI_Generator_Tracial_CornerPartition_exists_indexed_orthogonal_refinement_budget
import Theorems.Thm_OAI_Generator_Tracial_representedCorner_factor
import Theorems.Thm_OAI_Generator_Tracial_representedCorner_irreducible

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem projection_trace_real (τ : TracialRepresentation M) (p : AlgebraProjection M) :
    τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
  have h := τ.trace_star_mul p.val
  rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [h,← Complex.ofReal_pow,Complex.ofReal_re]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm_trace_mul_le (x y : M.toStarSubalgebra) :
    ‖τ.trace (x*y)‖ ≤ τ.norm₂ x * τ.norm₂ y := by
  have he := norm_inner_le_norm (𝕜 := ℂ)
    (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
    ((y : H →L[ℂ] H) τ.vector)
  have hi : inner ℂ (((star x : M.toStarSubalgebra) : H →L[ℂ] H) τ.vector)
      ((y : H →L[ℂ] H) τ.vector) = τ.trace (x*y) := by
    change inner ℂ (star (x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    rfl
  rw [hi] at he
  change ‖τ.trace (x*y)‖ ≤ τ.norm₂ (star x)*τ.norm₂ y at he
  simpa only [τ.norm₂_star] using he

theorem cornerCentered_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    p.val * cornerCentered τ p x = cornerCentered τ p x ∧
    cornerCentered τ p x * p.val = cornerCentered τ p x := by
  constructor
  · simp [cornerCentered,mul_sub,← mul_assoc,p.property.isIdempotentElem.eq]
  · simp [cornerCentered,sub_mul,mul_assoc,p.property.isIdempotentElem.eq]

theorem cornerCentered_trace (p : AlgebraProjection M) (hp : p.val ≠ 0)
    (x : M.toStarSubalgebra) : τ.trace (cornerCentered τ p x) = 0 := by
  have hn : τ.trace p.val ≠ 0 := by
    intro h
    have hh := projection_trace_pos τ p.val p.property hp
    rw [h,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  rw [cornerCentered,trace_sub,cornerTrace_smul,cornerScalar,div_mul_cancel₀ _ hn,sub_self]

theorem compress_cornerCentered {p q : AlgebraProjection M} (hqp : q ≤ p)
    (x : M.toStarSubalgebra) :
    q.val*cornerCentered τ p x*q.val = q.val*x*q.val-cornerScalar τ p x • q.val := by
  simp only [cornerCentered,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  have hl : p.val*q.val=q.val := hqp
  have hr := projection_mul_of_le hqp
  simp only [← mul_assoc,hr]
  simp only [mul_assoc,hl,q.property.isIdempotentElem.eq]

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (τ : TracialRepresentation M)

attribute [local instance] OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Generator.Tracial.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
theorem traceAbs_selfAdjoint (x : M.toStarSubalgebra) : IsSelfAdjoint (traceAbs x) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

theorem traceAbs_sq (x : M.toStarSubalgebra) : traceAbs x * traceAbs x = star x*x :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)

theorem traceAbs_norm₂ (x : M.toStarSubalgebra) : τ.norm₂ (traceAbs x) = τ.norm₂ x := by
  have h := congrArg Complex.re (τ.trace_star_mul (traceAbs x))
  rw [(traceAbs_selfAdjoint x).star_eq,traceAbs_sq,τ.trace_star_mul] at h
  simp only [← Complex.ofReal_pow,Complex.ofReal_re] at h
  nlinarith [show 0 ≤ τ.norm₂ x from norm_nonneg _,
    show 0 ≤ τ.norm₂ (traceAbs x) from norm_nonneg _]

/-- Right support passes to the positive square root without a polar decomposition. -/
theorem traceAbs_support (q : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : x*q.val=x) : traceAbs x*q.val=traceAbs x := by
  have he : star (traceAbs x*(1-q.val))*(traceAbs x*(1-q.val))=0 := by
    rw [star_mul,star_sub,star_one,q.property.isSelfAdjoint.star_eq,
      (traceAbs_selfAdjoint x).star_eq]
    calc (1-q.val)*traceAbs x*(traceAbs x*(1-q.val)) =
        (1-q.val)*(traceAbs x*traceAbs x)*(1-q.val) := by simp only [mul_assoc]
         _ = 0 := by
           rw [traceAbs_sq]
           simp only [mul_assoc,mul_sub,mul_one,hx,sub_self]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp he
  rw [mul_sub,mul_one,sub_eq_zero] at hz
  exact hz.symm

/-- The trace scale needed in corner local quantization. -/
theorem norm₁_le_support_norm₂ (q : AlgebraProjection M) (x : M.toStarSubalgebra)
    (hx : x*q.val=x) : norm₁ τ x ≤ τ.norm₂ x * τ.norm₂ q.val := by
  calc norm₁ τ x ≤ ‖τ.trace (traceAbs x)‖ := Complex.re_le_norm _
       _ = ‖τ.trace (traceAbs x*q.val)‖ := by rw [traceAbs_support q x hx]
       _ ≤ τ.norm₂ (traceAbs x) * τ.norm₂ q.val := norm_trace_mul_le τ _ _
       _ = τ.norm₂ x * τ.norm₂ q.val := by rw [traceAbs_norm₂]

theorem compression_norm₁_le (q : AlgebraProjection M) (x : M.toStarSubalgebra) :
    norm₁ τ (q.val*x*q.val) ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val := by
  apply norm₁_le_support_norm₂
  rw [mul_assoc,q.property.isIdempotentElem.eq]

/-- A strict corner L2 estimate supplies the manuscript's actual L1 estimate. -/
theorem compression_norm₁_lt_of_norm₂ (q : AlgebraProjection M) (hq : q.val ≠ 0)
    (x : M.toStarSubalgebra) (ε : ℝ)
    (h : τ.norm₂ (q.val*x*q.val) < ε*τ.norm₂ q.val) :
    norm₁ τ (q.val*x*q.val) < ε*(τ.trace q.val).re := by
  have hp : 0 < τ.norm₂ q.val := lt_of_le_of_ne (norm_nonneg _)
    (fun h => hq ((τ.norm₂_eq_zero_iff q.val).mp h.symm))
  have he := projection_trace_sq τ q.val q.property
  calc norm₁ τ (q.val*x*q.val) ≤ τ.norm₂ (q.val*x*q.val)*τ.norm₂ q.val :=
         compression_norm₁_le τ q x
       _ < (ε*τ.norm₂ q.val)*τ.norm₂ q.val := mul_lt_mul_of_pos_right h hp
       _ = ε*(τ.trace q.val).re := by rw [he]; ring

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_small_energy_piece {I J : Type*} (s : Finset I) (F : Finset J)
    (t : I → ℝ) (a : I → J → ℝ) (ε : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (ha : ∀ i ∈ s, ∀ j ∈ F, 0 ≤ a i j)
    (h : ∑ i ∈ s, ∑ j ∈ F, a i j < ε * ∑ i ∈ s, t i) :
    ∃ i ∈ s, 0 < t i ∧ ∀ j ∈ F, a i j < ε*t i := by
  classical
  have hex : ∃ i ∈ s, (∑ j ∈ F, a i j) < ε*t i := by
    by_contra hn
    push Not at hn
    have he := Finset.sum_le_sum hn
    rw [← Finset.mul_sum] at he
    exact (not_lt_of_ge he) h
  obtain ⟨i,hi,he⟩ := hex
  have htpos : 0 < t i := by
    by_contra hn
    have hz : t i=0 := le_antisymm (le_of_not_gt hn) (ht i hi)
    rw [hz,mul_zero] at he
    exact (not_lt_of_ge (Finset.sum_nonneg (ha i hi))) he
  refine ⟨i,hi,htpos,fun j hj => ?_⟩
  exact (Finset.single_le_sum (ha i hi) hj).trans_lt he

end

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Target
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wstar_le {s : Set (H →L[ℂ] H)} {S : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hS : WOTClosed S) (hs : s ⊆ S) : wstar s ≤ S :=
  sInf_le ⟨hS, hs⟩

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

theorem pinch_smul (c : ℂ) (x : M.toStarSubalgebra) :
    Q.pinch (c • x) = c • Q.pinch x := by
  simp [pinch, Finset.smul_sum]

theorem pinch_support (x : M.toStarSubalgebra) :
    p.val * Q.pinch x = Q.pinch x ∧ Q.pinch x * p.val = Q.pinch x := by
  constructor
  · have h (i : Fin Q.size) : p.val * (Q.piece i).val = (Q.piece i).val := Q.piece_le i
    simp only [pinch, Finset.mul_sum, ← mul_assoc, h]
  · simp only [pinch, Finset.sum_mul, mul_assoc, projection_mul_of_le (Q.piece_le _)]

theorem pinch_left (i : Fin Q.size) (x : M.toStarSubalgebra) :
    (Q.piece i).val * Q.pinch x = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [← mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [← mul_assoc, Q.orthogonal i j hji.symm, zero_mul]
  · simp

theorem pinch_idempotent (x : M.toStarSubalgebra) : Q.pinch (Q.pinch x) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change (Q.piece i).val * Q.pinch x * (Q.piece i).val = _
  rw [Q.pinch_left]
  simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]

theorem pinch_trace (x : M.toStarSubalgebra) :
    τ.trace (Q.pinch x) = τ.trace (p.val*x*p.val) := by
  have hq (i : Fin Q.size) :
      τ.trace ((Q.piece i).val*x*(Q.piece i).val) = τ.trace (x*(Q.piece i).val) := by
    rw [τ.trace_mul_comm, ← mul_assoc, (Q.piece i).property.isIdempotentElem.eq,
      τ.trace_mul_comm]
  change coordinateTraceLinear τ (∑ i, (Q.piece i).val*x*(Q.piece i).val) = _
  rw [map_sum]
  change (∑ i, τ.trace ((Q.piece i).val*x*(Q.piece i).val)) = _
  simp only [hq]
  change (∑ i, coordinateTraceLinear τ (x*(Q.piece i).val)) = _
  rw [← map_sum (coordinateTraceLinear τ), ← Finset.mul_sum, Q.total]
  change τ.trace (x*p.val) = _
  rw [τ.trace_mul_comm (p.val*x) p.val, ← mul_assoc, p.property.isIdempotentElem.eq,
    τ.trace_mul_comm p.val x]

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

theorem pinch_corner : Q.pinch p.val = p.val := by
  unfold pinch
  calc (∑ i, (Q.piece i).val*p.val*(Q.piece i).val) = ∑ i, (Q.piece i).val := by
         apply Finset.sum_congr rfl
         intro i _
         rw [projection_mul_of_le (Q.piece_le i), (Q.piece i).property.isIdempotentElem.eq]
    _ = p.val := Q.total

theorem pinch_cornerCentered (x : M.toStarSubalgebra) :
    Q.pinch (cornerCentered τ p x) = Q.pinch x - cornerScalar τ p x • p.val := by
  rw [cornerCentered, Q.pinch_sub, Q.pinch_smul, Q.pinch_corner, Q.pinch_corner_compression]

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
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem refineBlocks_pinch (x : M.toStarSubalgebra) :
    (Q.refineBlocks R).pinch x = ∑ i, (R i).pinch x := by
  rw [refineBlocks,ofFamily_pinch,Fintype.sum_sigma]
  rfl

/-- Energy splits into the actual energies of the independently refined blocks. -/
theorem refineBlocks_energy (τ : TracialRepresentation M) (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.refineBlocks R).pinch x)^2 = ∑ i, τ.norm₂ ((R i).pinch x)^2 := by
  rw [(Q.refineBlocks R).pinch_energy τ]
  change (∑ j, τ.norm₂ (((Q.refineBlocks R).piece j).val*x*
    ((Q.refineBlocks R).piece j).val)^2) = _
  let e := (Fintype.equivFin ((i : Fin Q.size) × Fin (R i).size)).symm
  change (∑ j, τ.norm₂ (((R (e j).1).piece (e j).2).val*x*
    ((R (e j).1).piece (e j).2).val)^2) = _
  rw [show (∑ j, τ.norm₂ (((R (e j).1).piece (e j).2).val*x*
    ((R (e j).1).piece (e j).2).val)^2) =
    ∑ a : (i : Fin Q.size) × Fin (R i).size,
      τ.norm₂ (((R a.1).piece a.2).val*x*((R a.1).piece a.2).val)^2 from
        Equiv.sum_comp e (fun a => τ.norm₂ (((R a.1).piece a.2).val*x*
          ((R a.1).piece a.2).val)^2),Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => ((R i).pinch_energy τ x).symm)

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cornerCentered_trace_all (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    τ.trace (cornerCentered τ p x)=0 := by
  by_cases hp : p.val=0
  · simp only [cornerCentered,hp,zero_mul,mul_zero,smul_zero,sub_zero]
    exact inner_zero_right _
  · exact cornerCentered_trace τ p hp x

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_centered_trace (x : M.toStarSubalgebra) :
    τ.trace (Q.pinch (cornerCentered τ p x))=0 := by
  rw [Q.pinch_trace τ,(cornerCentered_support τ p x).1,
    (cornerCentered_support τ p x).2,cornerCentered_trace_all]

theorem pinch_centered_orthogonal (x : M.toStarSubalgebra) (c : ℂ) :
    inner ℂ (baseVector τ (c • p.val))
      (baseVector τ (Q.pinch (cornerCentered τ p x))) = 0 := by
  rw [map_smul,inner_smul_left,baseVector_inner_trace,p.property.isSelfAdjoint.star_eq,
    (Q.pinch_support _).1,Q.pinch_centered_trace τ]
  simp

/-- Pinching energy is centered energy plus the unchanged corner scalar energy. -/
theorem pinch_scalar_energy (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 = τ.norm₂ (Q.pinch (cornerCentered τ p x))^2 +
      ‖cornerScalar τ p x‖^2 * (τ.trace p.val).re := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseVector τ (cornerScalar τ p x • p.val))
    (baseVector τ (Q.pinch (cornerCentered τ p x)))
    (Q.pinch_centered_orthogonal τ x _)
  rw [← map_add,Q.pinch_cornerCentered τ] at h
  have he : cornerScalar τ p x • p.val +
      (Q.pinch x-cornerScalar τ p x • p.val) = Q.pinch x := by abel
  rw [he,← Q.pinch_cornerCentered τ] at h
  change τ.norm₂ (Q.pinch x)*τ.norm₂ (Q.pinch x) =
    τ.norm₂ (cornerScalar τ p x • p.val)*τ.norm₂ (cornerScalar τ p x • p.val) +
      τ.norm₂ (Q.pinch (cornerCentered τ p x))*τ.norm₂ (Q.pinch (cornerCentered τ p x)) at h
  rw [τ.norm₂_smul] at h
  rw [projection_trace_sq τ p.val p.property]
  nlinarith only [h]

end CornerPartition

end

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem refineBlocks_scalar_energy (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.refineBlocks R).pinch x)^2 =
      (∑ i, τ.norm₂ ((R i).pinch (cornerCentered τ (Q.piece i) x))^2) + Q.scalarEnergy τ x := by
  rw [Q.refineBlocks_energy R τ]
  simp only [scalarEnergy,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (R i).pinch_scalar_energy τ x)

theorem scalarEnergy_le_refineBlocks (x : M.toStarSubalgebra) :
    Q.scalarEnergy τ x ≤ τ.norm₂ ((Q.refineBlocks R).pinch x)^2 := by
  rw [Q.refineBlocks_scalar_energy τ R]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CornerPartition

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

theorem compression (p : AlgebraProjection M) (hp : p.val ∈ P) :
    TraceOrthogonal τ P (p.val*x*p.val) := by
  intro a
  have h := hx ⟨p.val*(a : M.toStarSubalgebra)*p.val,P.mul_mem (P.mul_mem hp a.property) hp⟩
  change τ.trace ((p.val*(a : M.toStarSubalgebra)*p.val)*x)=0 at h
  calc τ.trace ((a : M.toStarSubalgebra)*(p.val*x*p.val)) =
      τ.trace (p.val*((a : M.toStarSubalgebra)*(p.val*x))) := by
        rw [← mul_assoc (a : M.toStarSubalgebra),τ.trace_mul_comm]
    _ = 0 := by simpa only [mul_assoc] using h

theorem pinch {p : AlgebraProjection M} (Q : CornerPartition p)
    (hQ : ∀ i,(Q.piece i).val ∈ P) : TraceOrthogonal τ P (Q.pinch x) := by
  intro a
  change coordinateTraceLinear τ ((a : M.toStarSubalgebra)*∑ i,(Q.piece i).val*x*(Q.piece i).val)=0
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_eq_zero (fun i _ => hx.compression τ (Q.piece i) (hQ i) a)

end TraceOrthogonal

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem scalarEnergy_le_energy (x : M.toStarSubalgebra) :
    Q.scalarEnergy τ x ≤ τ.norm₂ (Q.pinch x)^2 := by
  have h := Q.scalarEnergy_le_refineBlocks τ (fun i => single (Q.piece i)) x
  rw [Q.refineBlocks_pinch] at h
  have he : (∑ i,(single (Q.piece i)).pinch x)=Q.pinch x := by
    simp only [single_pinch]
    rfl
  rw [he] at h
  exact h

theorem cornerScalar_eq_of_orthogonal_difference
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hp : p.val ∈ P)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    cornerScalar τ p x=cornerScalar τ p y := by
  have h := (hxy.compression τ p hp).trace_zero τ
  rw [mul_sub,sub_mul,trace_sub,sub_eq_zero] at h
  exact congrArg (fun t : ℂ => t/τ.trace p.val) h

theorem scalarEnergy_eq_of_orthogonal_difference
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hQ : ∀ i,(Q.piece i).val ∈ P)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    Q.scalarEnergy τ x=Q.scalarEnergy τ y := by
  unfold scalarEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [cornerScalar_eq_of_orthogonal_difference τ (p := Q.piece i) P (hQ i) x y hxy]

/-- All later scalar terms are bounded by the already controlled coarse
energy of the subalgebra component. There is no claim that global centering
provides this bound. -/
theorem refinement_scalarEnergy_le_component
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (R : CornerPartition p)
    (hR : ∀ i,(R.piece i).val ∈ P) (hQR : Q.Refines R)
    (x y : M.toStarSubalgebra) (hxy : TraceOrthogonal τ P (x-y)) :
    R.scalarEnergy τ x ≤ τ.norm₂ (Q.pinch y)^2 := by
  rw [R.scalarEnergy_eq_of_orthogonal_difference τ P hR x y hxy]
  have h := Q.refinement_energy_le τ R hQR y
  rw [← Q.pinch_energy τ,← R.pinch_energy τ] at h
  exact (R.scalarEnergy_le_energy τ y).trans h

theorem pinch_mem (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (hQ : ∀ i,(Q.piece i).val ∈ P) (y : M.toStarSubalgebra) (hy : y ∈ P) :
    Q.pinch y ∈ P :=
  P.sum_mem (fun i _ => P.mul_mem (P.mul_mem (hQ i) hy) (hQ i))

/-- Pythagoras separates the orthogonal component from the component in P. -/
theorem orthogonal_component_energy
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hQ : ∀ i,(Q.piece i).val ∈ P)
    (x y : M.toStarSubalgebra) (hy : y ∈ P) (hxy : TraceOrthogonal τ P (x-y)) :
    τ.norm₂ (Q.pinch x)^2 = τ.norm₂ (Q.pinch (x-y))^2+τ.norm₂ (Q.pinch y)^2 := by
  have ho : inner ℂ (baseVector τ (Q.pinch y)) (baseVector τ (Q.pinch (x-y)))=0 := by
    rw [baseVector_inner_eq_trace]
    exact (hxy.pinch τ Q hQ) ⟨star (Q.pinch y),P.star_mem' (Q.pinch_mem P hQ y hy)⟩
  have he : Q.pinch x=Q.pinch y+Q.pinch (x-y) := by rw [Q.pinch_sub]; abel
  rw [he]
  change ‖baseVector τ (Q.pinch y+Q.pinch (x-y))‖^2 = _
  rw [map_add,norm_add_sq (𝕜 := ℂ),ho]
  change τ.norm₂ (Q.pinch y)^2+2*0+τ.norm₂ (Q.pinch (x-y))^2=_
  ring

end CornerPartition

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Any previously established coarse component budget survives the actual
finite-family quantization of the orthogonal residual. -/
theorem exists_component_controlled_refinement (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (Q : CornerPartition (identityProjection M))
    (hQ : ∀ i,(Q.piece i).val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x y : ι → M.toStarSubalgebra)
    (hy : ∀ i ∈ F,(y i).val ∈ N)
    (hxy : ∀ i ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (x i-y i))
    (b η : ℝ) (hη : 0 < η) (hb : (∑ i ∈ F,τ.norm₂ (Q.pinch (y i))^2) ≤ b) :
    ∃ R : CornerPartition (identityProjection M),Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (R.pinch (x i))^2) < b+η ∧
      ∀ i ∈ F,R.scalarEnergy τ (x i) ≤ τ.norm₂ (Q.pinch (y i))^2 := by
  obtain ⟨R,hQR,hR,hE⟩ := CornerPartition.exists_indexed_orthogonal_refinement_budget τ hNM hirr
    Q hQ F (fun i => x i-y i) hxy η hη
  refine ⟨R,hQR,hR,?_,fun i hi => Q.refinement_scalarEnergy_le_component τ
    (insideAlgebra (M := M) (P := N)) R hR hQR (x i) (y i) (hxy i hi)⟩
  have hid : (∑ i ∈ F,τ.norm₂ (R.pinch (x i))^2)=
      (∑ i ∈ F,τ.norm₂ (R.pinch (x i-y i))^2)+(∑ i ∈ F,τ.norm₂ (R.pinch (y i))^2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi => R.orthogonal_component_energy τ
      (insideAlgebra (M := M) (P := N)) hR (x i) (y i) (hy i hi) (hxy i hi))
  have hcomp : (∑ i ∈ F,τ.norm₂ (R.pinch (y i))^2) ≤
      ∑ i ∈ F,τ.norm₂ (Q.pinch (y i))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h := Q.refinement_energy_le τ R hQR (y i)
    rwa [← Q.pinch_energy τ,← R.pinch_energy τ] at h
  rw [hid]
  linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

theorem conditionalExpectation_trace (hNM : N ≤ M) (x : M.toStarSubalgebra) :
    τ.trace (conditionalExpectation τ hNM x)=τ.trace x := by
  have h := (conditionalExpectation_orthogonal τ hNM x).trace_zero τ
  rw [trace_sub,sub_eq_zero] at h
  exact h.symm

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generated_le (A : ℕ → FiniteMatrixStage N) : generated A ≤ N.toStarSubalgebra := by
  apply wstar_le (vonNeumann_wotClosed N)
  intro x hx
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
  exact (A n).units.concreteAlgebra_le hn

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem generatedVonNeumann_le (A : ℕ → FiniteMatrixStage N) : generatedVonNeumann A ≤ N :=
  generated_le A

end FiniteMatrixStage

end

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalQuantization
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! An actual irreducible subalgebra and its constructed conditional
expectation give finite pinching partitions with energy arbitrarily close
to the expectation energy. No partition or expectation is supplied. -/
open scoped BigOperators

/-! Convert the source's decreasing irreducible chain into actual finite
pinching partitions. The chain and its irreducibility are explicit inputs;
its existence in an arbitrary factor is not asserted. -/
open scoped BigOperators

/-! Restrict a compatible unit partition to an actual corner, retaining
all pieces and the exact compression. -/
open scoped BigOperators

/-! Complete a corner partition by the complementary projection. This lets
the existing compatible refinement construction act on an actual p-corner. -/
open scoped BigOperators

/-! Transfer actual corner partitions along a concrete von Neumann
subalgebra inclusion, preserving pieces, pinching and tracial energy. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection N} (Q : CornerPartition p)

theorem include_pinch (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    (Q.mapInclusion hNM).pinch (coordinateInclusion hNM x)=coordinateInclusion hNM (Q.pinch x) := by
  unfold pinch
  change (∑ i,coordinateInclusion hNM (Q.piece i).val*coordinateInclusion hNM x*
    coordinateInclusion hNM (Q.piece i).val)=coordinateInclusion hNM _
  simp only [← map_mul,← map_sum]

theorem include_piece_mem (hNM : N ≤ M) (i : Fin Q.size) :
    ((Q.mapInclusion hNM).piece i).val.val ∈ N := (Q.piece i).val.property

theorem includeUnit_pinch (Q : CornerPartition (identityProjection N))
    (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    (Q.includeUnit hNM).pinch (coordinateInclusion hNM x)=coordinateInclusion hNM (Q.pinch x) :=
  Q.include_pinch hNM x

theorem includeUnit_energy (Q : CornerPartition (identityProjection N))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    τ.norm₂ ((Q.includeUnit hNM).pinch (coordinateInclusion hNM x))^2=
      (restrictedTrace τ hNM).norm₂ (Q.pinch x)^2 := by
  rw [Q.includeUnit_pinch]
  rfl

end CornerPartition
end

/-! The two applications of orthogonal refinement in Popa A.1.2, equations
(2) and (3). The inner decreasing chain need only be irreducible in N;
irreducibility of its terms in the ambient M is not imposed. -/
open scoped BigOperators

/-! Nonzero local projections obtained from the constructed nested-chain
partition. This implements the finite squared-energy selection at the end
of A.1.2, while retaining the chain as a structural premise. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Finite pinching energy selects one nonzero projection with simultaneous
strict squared-L2 bounds, with the actual trace as the weight. -/
theorem CornerPartition.exists_indexed_local_L2_piece
    {p : AlgebraProjection M} (Q : CornerPartition p)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hE : (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε*(τ.trace p.val).re) :
    ∃ j : Fin Q.size,(Q.piece j).val ≠ 0 ∧
      ∀ i ∈ F,τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2 <
        ε*(τ.trace (Q.piece j).val).re := by
  have htrace := Q.trace_total τ
  have he : (∑ j : Fin Q.size,∑ i ∈ F,τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2) <
      ε*∑ j : Fin Q.size,(τ.trace (Q.piece j).val).re := by
    rw [Finset.sum_comm,htrace]
    simpa only [← Q.pinch_energy τ] using hE
  obtain ⟨j,_,hj,hjE⟩ := exists_small_energy_piece Finset.univ F
    (fun j => (τ.trace (Q.piece j).val).re)
    (fun j i => τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2) ε
    (fun j _ => by rw [projection_trace_sq τ _ (Q.piece j).property]; positivity)
    (fun _ _ _ _ => sq_nonneg _) he
  refine ⟨j,?_,hjE⟩
  intro hz
  have ht : τ.trace (Q.piece j).val=0 := by rw [hz]; exact inner_zero_right _
  rw [ht,Complex.zero_re] at hj
  exact (lt_irrefl 0 hj)

end

/-! Local quantization by finite matrix approximation and Bell pinching under represented trace-vector separability. -/
open scoped BigOperators
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_matrix_generated_ambient_centered_partition
    (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hNM : N ≤ M) (hfactor : IsII1Factor (generated A))
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ generated A) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  let R := generatedVonNeumann A
  have hRM : R ≤ M := (generatedVonNeumann_le A).trans hNM
  have hirrR : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := R),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    refine ⟨τ.trace c,hirr c (fun a => ?_)⟩
    exact congrArg Subtype.val (hc ⟨⟨a.val,hRM a.property⟩,a.property⟩)
  let y : ι → R.toStarSubalgebra := fun i =>
    ⟨(conditionalExpectation τ hRM (x i)).val,conditionalExpectation_mem τ hRM (x i)⟩
  have he (i : ι) : coordinateInclusion hRM (y i)=conditionalExpectation τ hRM (x i) := rfl
  have hy : ∀ i ∈ F,(restrictedTrace τ hRM).trace (y i)=0 := by
    intro i hi
    rw [restrictedTrace_trace,he,conditionalExpectation_trace,hx i hi]
  obtain ⟨Q,hE⟩ := exists_matrix_generated_centered_partition A hA
    (restrictedTrace τ hRM) hfactor F y hy (ε/2) (half_pos hε)
  let Q' := Q.includeUnit hRM
  have hQ' : ∀ i,(Q'.piece i).val.val ∈ R := Q.include_piece_mem hRM
  have hb : (∑ i ∈ F,τ.norm₂ (Q'.pinch (conditionalExpectation τ hRM (x i)))^2) ≤ ε/2 := by
    have hi (i : ι) : τ.norm₂ (Q'.pinch (conditionalExpectation τ hRM (x i)))^2=
        (restrictedTrace τ hRM).norm₂ (Q.pinch (y i))^2 := by
      rw [← he]
      exact Q.includeUnit_energy τ hRM (y i)
    simpa only [hi] using hE.le
  obtain ⟨S,_,hS,hSE,_⟩ := exists_component_controlled_refinement τ hRM hirrR Q' hQ'
    F x (conditionalExpectation τ hRM ∘ x)
    (fun i _ => conditionalExpectation_mem τ hRM (x i))
    (fun i _ => conditionalExpectation_orthogonal τ hRM (x i))
    (ε/2) (ε/2) (half_pos hε) hb
  exact ⟨S,hS,by linarith⟩

theorem exists_irreducible_centered_partition (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  obtain ⟨A,_,hA,_,hR,hRN,hRM⟩ :=
    exists_irreducible_matrix_generated_II1 τ hNM hfactor hdiff hirr hsep
  obtain ⟨Q,hQ,hE⟩ := exists_matrix_generated_ambient_centered_partition τ A hA hNM hR hRM
    F x hx ε hε
  exact ⟨Q,fun i => hRN (hQ i),hE⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RepresentedCorners
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed _root_.OAI.Generator.predualFunctionals_normedSpace
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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

theorem representedCornerTrace_norm₂ (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (representedCornerTrace τ p hp).norm₂ a=τ.norm₂ (cornerEmbedding p a)/τ.norm₂ p.val := by
  change ‖a.val (((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector)‖=_
  rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (show 0 ≤ τ.norm₂ p.val from norm_nonneg _)]
  change (τ.norm₂ p.val)⁻¹*τ.norm₂ (cornerEmbedding p a)=_
  exact (div_eq_inv_mul _ _).symm

theorem representedCornerTrace_trace (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (representedCornerTrace τ p hp).trace a=τ.trace (cornerEmbedding p a)/τ.trace p.val := by
  change inner ℂ (normalizedCornerVector τ p) (a.val (normalizedCornerVector τ p))=_
  rw [normalizedCornerVector_pairing]
  have ht : τ.trace p.val=(τ.norm₂ p.val : ℂ)^2 := by
    have h := τ.trace_star_mul p.val
    rwa [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [ht,div_eq_inv_mul]

end

/-! Subcorner inclusion, inherited diffuseness/irreducibility, and L2 separability. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

theorem representedCorner_diffuse
    (hdiff : ∀ r : M.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q) :
    ∀ r : (representedCorner p).toStarSubalgebra,IsStarProjection r → r ≠ 0 →
      ∃ q : (representedCorner p).toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q := by
  intro r hr hr0
  have hr' := hr.map (cornerEmbedding p)
  have hr0' : cornerEmbedding p r ≠ 0 := by
    intro h
    exact hr0 (cornerEmbedding_injective p (h.trans (map_zero (cornerEmbedding p)).symm))
  obtain ⟨q,hq,hq0,hqr,hrq,hqr'⟩ := hdiff _ hr' hr0'
  have hl : p.val*q=q := by
    rw [← hrq,← mul_assoc,cornerEmbedding_left,hrq]
  have hh : q*p.val=q := by
    rw [← hqr',mul_assoc,cornerEmbedding_right,hqr']
  let q' := cornerCompress p q
  have he : cornerEmbedding p q'=q := by rw [cornerEmbedding_compress,hl,hh]
  have hi := cornerEmbedding_injective p
  refine ⟨q',⟨?_,?_⟩,?_,?_,?_,?_⟩
  · apply hi
    rw [map_mul,he,hq.isIdempotentElem.eq]
  · apply hi
    rw [map_star,he,hq.isSelfAdjoint.star_eq]
  · intro hz
    apply hq0
    rw [← he,hz,map_zero]
  · intro hz
    exact hqr (he.symm.trans (congrArg (cornerEmbedding p) hz))
  · apply hi
    rw [map_mul,he,hrq]
  · apply hi
    rw [map_mul,he,hqr']

theorem representedCorner_separable (hp : p.val ≠ 0)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    TopologicalSpace.IsSeparable (Set.range (baseVector (representedCornerTrace τ p hp))) := by
  let f : H → cornerSpace p := fun x => ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p x
  have hf : Continuous f := by
    dsimp [f]
    exact (cornerProject p).continuous.const_smul ((τ.norm₂ p.val : ℂ)⁻¹)
  apply (hsep.image hf).mono
  rintro y ⟨a,rfl⟩
  refine ⟨baseVector τ (cornerEmbedding p a),⟨cornerEmbedding p a,rfl⟩,?_⟩
  change ((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p (a.val (cornerProject p τ.vector)).val=
    a.val (((τ.norm₂ p.val : ℂ)⁻¹) • cornerProject p τ.vector)
  rw [cornerProject_subtype,map_smul]

end

/-! Transport actual unit partitions on pH to ambient partitions of p. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)
namespace CornerPartition
variable (Q : CornerPartition (identityProjection (representedCorner p)))

theorem fromRepresentedCorner_pinch (x : (representedCorner p).toStarSubalgebra) :
    (Q.fromRepresentedCorner p).pinch (cornerEmbedding p x)=cornerEmbedding p (Q.pinch x) := by
  unfold pinch
  change (∑ i,cornerEmbedding p (Q.piece i).val*cornerEmbedding p x*
    cornerEmbedding p (Q.piece i).val)=cornerEmbedding p _
  simp only [← map_mul,← map_sum]

theorem fromRepresentedCorner_pinch_compress (x : M.toStarSubalgebra) :
    (Q.fromRepresentedCorner p).pinch x=cornerEmbedding p (Q.pinch (cornerCompress p x)) := by
  rw [← Q.fromRepresentedCorner_pinch,cornerEmbedding_compress]
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change cornerEmbedding p (Q.piece i).val*x*cornerEmbedding p (Q.piece i).val=
    cornerEmbedding p (Q.piece i).val*(p.val*x*p.val)*cornerEmbedding p (Q.piece i).val
  simp only [← mul_assoc,cornerEmbedding_right]
  simp only [mul_assoc,cornerEmbedding_left]

theorem fromRepresentedCorner_mem {N : VonNeumannAlgebra H} (hpN : p.val.val ∈ N)
    (hQ : ∀ i,(Q.piece i).val.val ∈ representedSubcorner p hpN) :
    ∀ i,((Q.fromRepresentedCorner p).piece i).val.val ∈ N := hQ

theorem fromRepresentedCorner_energy (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.fromRepresentedCorner p).pinch x)^2=
      (τ.trace p.val).re*(representedCornerTrace τ p hp).norm₂ (Q.pinch (cornerCompress p x))^2 := by
  rw [Q.fromRepresentedCorner_pinch_compress,representedCornerTrace_norm₂,projection_trace_sq τ _ p.property]
  field_simp [(corner_norm₂_pos τ p hp).ne']

end CornerPartition

end

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_irreducible_corner_zero_trace_partition
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (p.val*x i*p.val)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition p,(∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε*(τ.trace p.val).re := by
  let τp := representedCornerTrace τ p hp
  let pN := projectionInSubalgebra p hpN
  let hinc := representedSubcorner_le p hpN hNM
  have hf := representedCorner_factor (restrictedTrace τ hNM) pN hfactor
  have hd := representedCorner_diffuse pN hdiff
  have hi := representedCorner_irreducible τ p hpN hNM hirr
  have hs := representedCorner_separable τ p hp hsep
  let y : ι → (representedCorner p).toStarSubalgebra := fun i => cornerCompress p (x i)
  have hy : ∀ i ∈ F,τp.trace (y i)=0 := by
    intro i hi
    rw [representedCornerTrace_trace,cornerEmbedding_compress,hx i hi,zero_div]
  obtain ⟨Q,hQ,hE⟩ := exists_irreducible_centered_partition τp hinc hf hd hi hs F y hy ε hε
  refine ⟨Q.fromRepresentedCorner p,Q.fromRepresentedCorner_mem p hpN hQ,?_⟩
  have henergy : (∑ i ∈ F,τ.norm₂ ((Q.fromRepresentedCorner p).pinch (x i))^2)=
      (τ.trace p.val).re*(∑ i ∈ F,τp.norm₂ (Q.pinch (y i))^2) := by
    simp only [Q.fromRepresentedCorner_energy p τ hp,Finset.mul_sum,τp,y]
  rw [henergy,mul_comm ε]
  exact mul_lt_mul_of_pos_left hE (projection_trace_pos τ p.val p.property hp)

theorem exists_irreducible_corner_centered_partition
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition p,(∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (cornerCentered τ p (x i)))^2) < ε^2*(τ.trace p.val).re := by
  apply exists_irreducible_corner_zero_trace_partition τ hNM hfactor hdiff hirr hsep
    p hp hpN F (fun i => cornerCentered τ p (x i)) _ (ε^2) (sq_pos_of_pos hε)
  intro i _
  rw [(cornerCentered_support τ p (x i)).1,(cornerCentered_support τ p (x i)).2,
    cornerCentered_trace τ p hp]

theorem exists_irreducible_corner_local_piece
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (hpN : p.val.val ∈ N)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : AlgebraProjection M,q ≤ p ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,
        τ.norm₂ (q.val*x i*q.val-cornerScalar τ p (x i) • q.val) < ε*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val-cornerScalar τ p (x i) • q.val) < ε*(τ.trace q.val).re := by
  obtain ⟨Q,hQ,hE⟩ := exists_irreducible_corner_centered_partition τ hNM hfactor hdiff hirr hsep
    p hp hpN F x ε hε
  obtain ⟨j,hj,hjE⟩ := Q.exists_indexed_local_L2_piece τ F (fun i => cornerCentered τ p (x i)) (ε^2) hE
  refine ⟨Q.piece j,Q.piece_le j,hj,hQ j,fun i hi => ?_⟩
  have ht := hjE i hi
  rw [projection_trace_sq τ _ (Q.piece j).property] at ht
  have hn : τ.norm₂ ((Q.piece j).val*cornerCentered τ p (x i)*(Q.piece j).val) <
      ε*τ.norm₂ (Q.piece j).val := by
    nlinarith [show 0 ≤ τ.norm₂ ((Q.piece j).val*cornerCentered τ p (x i)*(Q.piece j).val) from norm_nonneg _,
      mul_nonneg hε.le (show 0 ≤ τ.norm₂ (Q.piece j).val from norm_nonneg _)]
  have h₁ := compression_norm₁_lt_of_norm₂ τ (Q.piece j) hj (cornerCentered τ p (x i)) ε hn
  rw [compress_cornerCentered τ (Q.piece_le j)] at hn h₁
  exact ⟨hn,h₁⟩

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualEstimates
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Correct residual-corner trace identity for arbitrary f. The first term
is trace(f*x), not trace(x); they agree when f=1. This is the distinction
at Popa 1308.3982v3 Lemma 3.2, equation (5). -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem projection_compression_trace (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    τ.trace (p.val*x*p.val) = τ.trace (x*p.val) := by
  rw [τ.trace_mul_comm,← mul_assoc,p.property.isIdempotentElem.eq,τ.trace_mul_comm]

theorem residualCorner_compression_trace (f : AlgebraProjection M) (v : PartialUnitary M)
    (hv : v.support ≤ f) (x : M.toStarSubalgebra) :
    τ.trace ((residualCorner f v hv).val*x*(residualCorner f v hv).val) =
      τ.trace (f.val*x)-τ.trace (star v.val*x*v.val) := by
  rw [projection_compression_trace]
  change τ.trace (x*(f.val-v.support.val)) = _
  rw [mul_sub,trace_sub,τ.trace_mul_comm x f.val]
  congr 1
  calc τ.trace (x*v.support.val) = τ.trace ((x*v.val)*star v.val) := by
         rw [mul_assoc,v.unitary.final]
    _ = τ.trace (star v.val*x*v.val) := by
      rw [τ.trace_mul_comm]
      simp only [mul_assoc]

end

/-! The justified f=1 scalar estimate in the support-growth argument.
Every estimate is tied to the current partial unitary's actual residual;
there is no arbitrary-corner centering assertion. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem unitResidual_trace (v : PartialUnitary M) :
    τ.trace (unitResidual v).val=1-τ.trace v.support.val := by
  rw [unitResidual,trace_sub,τ.trace_one]

theorem unitResidual_positive (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4) :
    0 < (τ.trace (unitResidual v).val).re := by
  rw [unitResidual_trace,Complex.sub_re,Complex.one_re]
  linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Construct local patches in the actual f=1 residual. Both residual trace
terms are retained. Admissibility of the full extended word family is not asserted. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
theorem unitResidual_scalar_two_moment_bound (v : PartialUnitary M)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    (x : M.toStarSubalgebra) (A B : ℝ) (hAB : 0 ≤ A+B)
    (hA : ‖τ.trace x‖ ≤ A*(τ.trace v.support.val).re)
    (hB : ‖τ.trace (star v.val*x*v.val)‖ ≤ B*(τ.trace v.support.val).re) :
    ‖cornerScalar τ (unitResidual v) x‖ ≤ (A+B)/3 := by
  have htrace : τ.trace ((unitResidual v).val*x*(unitResidual v).val)=
      τ.trace x-τ.trace (star v.val*x*v.val) := by
    simpa only [residualCorner,unitResidual,identityProjection,one_mul] using
      residualCorner_compression_trace τ (identityProjection M) v (one_mul _) x
  rw [cornerScalar,htrace,norm_div,projection_trace_real τ (unitResidual v),
    Complex.norm_real,Real.norm_of_nonneg (unitResidual_positive τ v hsmall).le]
  rw [div_le_iff₀ (unitResidual_positive τ v hsmall)]
  have hn := norm_sub_le (τ.trace x) (τ.trace (star v.val*x*v.val))
  rw [unitResidual_trace,Complex.sub_re,Complex.one_re]
  nlinarith [mul_le_mul_of_nonneg_left hsmall hAB]

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_unitResidual_local_compression_oai
    (v : PartialUnitary M) (hvN : v.val.val ∈ N)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
    (hAB : ∀ i ∈ F,0 ≤ A i+B i)
    (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
    (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
    (η : ℝ) (hη : 0 < η) :
    ∃ q : AlgebraProjection M,q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val) < (η+(A i+B i)/3)*(τ.trace q.val).re := by
  have hp : (unitResidual v).val ≠ 0 := by
    intro h
    have hh := unitResidual_positive τ v hsmall
    rw [h,show τ.trace 0=0 from inner_zero_right _,Complex.zero_re] at hh
    exact (lt_irrefl _ hh)
  have hpN : (unitResidual v).val.val ∈ N := by
    have hvp : v.support.val.val ∈ N := by
      rw [← v.unitary.initial]
      exact N.mul_mem (N.toStarSubalgebra.star_mem' hvN) hvN
    exact N.sub_mem N.one_mem hvp
  obtain ⟨q,hqp,hq,hqN,hlocal⟩ := exists_irreducible_corner_local_piece τ hNM hfactor hdiff hirr hsep
    (unitResidual v) hp hpN F x η hη
  refine ⟨q,hqp,hq,hqN,fun i hi => ?_⟩
  have hs := unitResidual_scalar_two_moment_bound τ v hsmall (x i) (A i) (B i)
    (hAB i hi) (hA i hi) (hB i hi)
  have hn : τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val := by
    have ht := τ.norm₂_add_le (q.val*x i*q.val-cornerScalar τ (unitResidual v) (x i) • q.val)
      (cornerScalar τ (unitResidual v) (x i) • q.val)
    rw [sub_add_cancel,τ.norm₂_smul] at ht
    have hmul := mul_le_mul_of_nonneg_right hs (show 0 ≤ τ.norm₂ q.val from norm_nonneg _)
    have hh := (hlocal i hi).1
    nlinarith only [ht,hmul,hh]
  exact ⟨hn,compression_norm₁_lt_of_norm₂ τ q hq (x i) _ hn⟩

end

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.Tracial.exists_unitResidual_local_compression_oai.{u_1, u_2} := @OAI.Generator.Tracial.exists_unitResidual_local_compression_oai.{u_1, u_2}
