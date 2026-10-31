-- Prove2me | solution 1 for OAI.Generator.Tracial.represented_relative_generation_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:40:18.888367+00:00
-- url     : https://prove2.me/submissions/91f7cf87-56c6-4700-9d6e-fcd3360d6fda

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_commonPerturbation_norm_q129
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_perturbedWord_correlation_q129
import Theorems.Thm_OAI_Generator_Tracial_nonempty_successiveCoordinateHaar_q129

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
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

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/
namespace Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem traceCyclicSpace_separable
    (hsep : TopologicalSpace.IsSeparable
      (Set.range (fun a : M.toStarSubalgebra => a.val τ.vector))) :
    TopologicalSpace.SeparableSpace (traceCyclicSpace τ) :=
  hsep.closure.separableSpace

end

/-! The faithful cyclic restriction sends actual algebra balls to compact
weak-operator balls. On each bounded ball it is a closed topological embedding. -/
open scoped Topology
open UltrapowerBridge

end Tracial

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_UnitaryMetric
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Bounded self-adjoint least-distance elements in a von Neumann subalgebra. -/

/-! Countable determination of a relative commutant from actual L2
separability. Operator norm separability is not required. -/

/-! The unitary metric induced by a faithful trace vector, distinguishing the trace two-norm topology from the operator norm topology. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceUnitary

theorem vector_isometry : Isometry (vector τ) := fun _ _ => rfl

theorem algebra_norm_le (u : TraceUnitary τ) : ‖u.algebra τ‖ ≤ 1 :=
  unitary_norm_le _ u.toUnitary.property.1

theorem unitary_of_limit (u : ℕ → TraceUnitary τ) (a : M.toStarSubalgebra)
    (ha : Tendsto (fun n => τ.norm₂ ((u n).algebra τ-a)) atTop (𝓝 0)) :
    a ∈ unitary M.toStarSubalgebra := by
  have hs := norm₂_limit_star τ (fun n => (u n).algebra τ) a ha
  have hleft := norm₂_limit_mul τ (fun n => star ((u n).algebra τ))
    (fun n => (u n).algebra τ) (star a) a 1
    (fun n => by
      change ‖star ((u n).algebra τ).val‖ ≤ 1
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint.norm_map]
      exact algebra_norm_le τ (u n)) hs ha
  have hright := norm₂_limit_mul τ (fun n => (u n).algebra τ)
    (fun n => star ((u n).algebra τ)) a (star a) 1
    (fun n => algebra_norm_le τ (u n)) ha hs
  have hconst : Tendsto (fun _ : ℕ => τ.norm₂ ((1 : M.toStarSubalgebra)-1))
      atTop (𝓝 0) := by simpa only [sub_self,τ.norm₂_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hl (n : ℕ) : star ((u n).algebra τ)*(u n).algebra τ=1 :=
    (u n).toUnitary.property.1
  have hr (n : ℕ) : (u n).algebra τ*star ((u n).algebra τ)=1 :=
    (u n).toUnitary.property.2
  simp only [hl] at hleft
  simp only [hr] at hright
  exact ⟨norm₂_limit_unique τ _ hleft hconst, norm₂_limit_unique τ _ hright hconst⟩

theorem vector_range_closed : IsClosed (Set.range (vector τ)) := by
  apply IsSeqClosed.isClosed
  intro x y hx hxy
  choose u hu using hx
  obtain ⟨a,_,hay⟩ := bounded_trace_limit τ (fun n => (u n).algebra τ) 1 zero_le_one
    (fun n => algebra_norm_le τ (u n)) y (by change Tendsto (fun n => vector τ (u n)) atTop (𝓝 y); simpa only [hu] using hxy)
  have ht : Tendsto (fun n => τ.norm₂ ((u n).algebra τ-a)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ a).mp
    change Tendsto (fun n => vector τ (u n)) atTop (𝓝 (a.val τ.vector))
    simpa only [hu,hay] using hxy
  exact ⟨⟨⟨a,unitary_of_limit τ u a ht⟩⟩,hay⟩

instance instCompleteSpace : CompleteSpace (TraceUnitary τ) :=
  (completeSpace_iff_isComplete_range (vector_isometry τ).isUniformInducing).mpr
    (vector_range_closed τ).isComplete

/-- Convergence in the constructed metric is exactly trace two-norm convergence. -/
theorem tendsto_iff {I : Type*} (l : Filter I) (u : I → TraceUnitary τ)
    (v : TraceUnitary τ) :
    Tendsto u l (𝓝 v) ↔ Tendsto (fun i => τ.norm₂ ((u i).algebra τ-v.algebra τ)) l (𝓝 0) := by
  simpa only [dist_eq] using (tendsto_iff_dist_tendsto_zero (f := u) (a := v) (x := l))

end TraceUnitary

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutantVonNeumann_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantVonNeumann S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  exact bicommutantStar_coe S

theorem wstar_starAlgebra_eq_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    wstar (S : Set (H →L[ℂ] H))=(bicommutantVonNeumann S).toStarSubalgebra := by
  apply le_antisymm
  · apply wstar_le (Tracial.vonNeumann_wotClosed _)
    intro a ha
    change a ∈ (bicommutantVonNeumann S : Set (H →L[ℂ] H))
    rw [bicommutantVonNeumann_coe]
    exact fun b hb => (hb a ha).symm
  · intro a ha
    have hb : a ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
      rwa [← bicommutantVonNeumann_coe]
    rw [← SetLike.mem_coe,← wotClosed_bicommutant _ (wstar_closed _)]
    exact fun b hb' => hb b (fun c hc => hb' c (subset_wstar _ hc))

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instCompleteSpace _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Literal ultralimit inner product, including the complex orientation. -/
theorem sequence_inner_tendsto (a b : Sequences M) :
    Tendsto (fun n => τ.trace (star (a n)*b n)) (ω : Filter ℕ)
      (𝓝 (inner ℂ (sequenceInclusion τ ω a) (sequenceInclusion τ ω b))) := by
  rw [sequenceInclusion_apply, sequenceInclusion_apply, inclusion_inner]
  exact traceRep_tendsto τ ω (star (boundedMap a)*boundedMap b)

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

/-- Operator-norm exponentials of bounded sequences evaluate coordinatewise. -/
theorem sequence_exp_apply (a : Sequences M) (n : ℕ) :
    (NormedSpace.exp a) n = NormedSpace.exp (a n) :=
  NormedSpace.map_exp (sequenceEval n)
    (BoundedContinuousFunction.lipschitz_eval_const n).continuous a

/-- Both limits hold at one coordinate, with the same positive tolerance. -/
theorem select_coordinate (a ξ b : Sequences M) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, τ.norm₂ (a n) < ‖sequenceQuotient τ ω a‖ + ε ∧
      ‖τ.trace (star (ξ n)*b n) -
        inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b)‖ < ε := by
  have hn : ∀ᶠ n in (ω : Filter ℕ), τ.norm₂ (a n) < ‖sequenceQuotient τ ω a‖ + ε :=
    (sequence_norm_tendsto τ ω a)
    (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  have ht := Metric.tendsto_nhds.mp (sequence_inner_tendsto τ ω ξ b) ε hε
  obtain ⟨n, hn, ht⟩ := (hn.and ht).exists
  exact ⟨n, hn, by simpa only [dist_eq_norm] using ht⟩

/-- Source-facing error transfer: a common representative index preserves a
quotient size bound and a complex trace-correlation bound, up to epsilon. -/
theorem select_coordinate_with_bounds (a ξ b : Sequences M)
    (d r ε : ℝ) (target : ℂ) (hε : 0 < ε)
    (ha : ‖sequenceQuotient τ ω a‖ ≤ d)
    (hb : ‖inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b) - target‖ ≤ r) :
    ∃ n : ℕ, τ.norm₂ (a n) < d + ε ∧ ‖τ.trace (star (ξ n)*b n)-target‖ < r+ε := by
  obtain ⟨n,hn,ht⟩ := select_coordinate τ ω a ξ b ε hε
  refine ⟨n, hn.trans_le (add_le_add ha le_rfl), ?_⟩
  have h := norm_sub_le_norm_sub_add_norm_sub (τ.trace (star (ξ n)*b n))
    (inner ℂ (sequenceInclusion τ ω ξ) (sequenceInclusion τ ω b)) target
  linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinatePerturbation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Group-ring maps from actual bounded unitary coordinates, with quotient
transport and coordinate Gram limits. -/

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.haarSequence_apply (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j k : ℕ) : (F.haarSequence τ ω j : Sequences M) k=
      coordinateInclusion hNM ((F.step j).coordinates.val k) :=
  boundedToSequence_apply _ k

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Correlation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

namespace Generator

/-! Scalar error budgets and lower bounds for perturbation correlation. -/

/-- The strict nonlinear error budget in the manuscript, with its original constants. -/
theorem correlation_error_budget {s α : ℝ} (hs : 0 < s) (hα : 0 < α)
    (hquarter : α < 1 / 4) (hsmall : α < s / 32) :
    s * (4 * α ^ 2 / (1 - 2 * α)) < α * s ^ 2 / 4 := by
  have hden : 0 < 1 - 2 * α := by linarith
  have hnum : 0 < 4 * α ^ 2 := by positivity
  have hquot : 4 * α ^ 2 / (1 - 2 * α) < 8 * α ^ 2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hnum (show 0 < 1 - 4 * α by linarith)]
  have hfirst := mul_lt_mul_of_pos_left hquot hs
  have hsecond : 8 * s * α ^ 2 < α * s ^ 2 / 4 := by
    have hp : 0 < α * s := mul_pos hα hs
    nlinarith [mul_pos hp (show 0 < s - 32 * α by linarith)]
  nlinarith

/-- Triangle-inequality step converting the correlation error into a lower bound. -/
theorem correlation_lower_bound {s α δ : ℝ} (hs : 0 < s) (hα : 0 < α)
    (hquarter : α < 1 / 4) (hsmall : α < s / 32) {c : ℂ}
    (hc : ‖c - ((α * s ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      s * (4 * α ^ 2 / (1 - 2 * α)) + δ) :
    α * s ^ 2 / 4 - δ ≤ ‖c‖ := by
  have he := correlation_error_budget hs hα hquarter hsmall
  have hcenter : 0 ≤ α * s ^ 2 / 2 := by positivity
  have ht := norm_sub_le c (c - ((α * s ^ 2 / 2 : ℝ) : ℂ))
  rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcenter] at ht
  linarith

/-! The numerical and topological contradiction for a continuous correlated sequence. -/
open Filter Topology

theorem no_continuous_correlated_sequence {X : Type*} [TopologicalSpace X]
    (F : X → ℝ) {x : X} (hF : ContinuousAt F x) (hzero : F x = 0)
    (u : ℕ → X) (hu : Tendsto u atTop (𝓝 x))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (c : ℕ → ℂ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (hq : α < 1 / 4) (hsmall : α < s / 32)
    (hc : ∀ n, ‖c n - ((α * s ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      s * (4 * α ^ 2 / (1 - 2 * α)) + δ n)
    (hproj : ∀ n, ‖c n‖ ≤ F (u n)) : False := by
  have hFu : Tendsto (fun n => F (u n)) atTop (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hF.tendsto.comp hu
  have hpos : 0 < α * s ^ 2 / 8 := by positivity
  have hnearF := Metric.tendsto_nhds.mp hFu (α * s ^ 2 / 8) hpos
  have hnearδ := Metric.tendsto_nhds.mp hδ (α * s ^ 2 / 8) hpos
  obtain ⟨n, hnF, hnδ⟩ := (hnearF.and hnearδ).exists
  rw [Real.dist_eq, sub_zero] at hnF hnδ
  have hlow := correlation_lower_bound hs hα hq hsmall (hc n)
  have hupp := hproj n
  have hFlt := (abs_lt.mp hnF).2
  have hδlt := (abs_lt.mp hnδ).2
  linarith

end Generator

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PerturbationBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_exp_sub_one_le (K : M.toStarSubalgebra) (hK : star K = -K) :
    τ.norm₂ (NormedSpace.exp K-1) ≤ τ.norm₂ K := by
  let V := (traceVectorCLM τ).restrictScalars ℝ
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => V (NormedSpace.exp (s • K)))
      (V (NormedSpace.exp (t • K)*K)) t :=
    V.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const K t)
  have hb (t : ℝ) : ‖V (NormedSpace.exp (t • K)*K)‖ ≤ τ.norm₂ K := by
    have hu : NormedSpace.exp (t • K) ∈ unitary M.toStarSubalgebra := by
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      rw [skewAdjoint.mem_iff,star_smul,star_trivial,hK]
      exact smul_neg _ _
    have hn := unitary_norm_le (NormedSpace.exp (t • K)) hu.1
    change τ.norm₂ (NormedSpace.exp (t • K)*K) ≤ _
    calc
      _ ≤ ‖NormedSpace.exp (t • K)‖*τ.norm₂ K := τ.norm₂_mul_le _ _
      _ ≤ 1*τ.norm₂ K := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t)
  change ‖V (NormedSpace.exp K-1)‖ ≤ _
  rw [map_sub]
  simpa only [one_smul,zero_smul,NormedSpace.exp_zero] using h

theorem norm₂_exp_mul_sub_le (K : M.toStarSubalgebra) (hK : star K = -K)
    (u : unitary M.toStarSubalgebra) :
    τ.norm₂ (NormedSpace.exp K*(u : M.toStarSubalgebra)-u) ≤ τ.norm₂ K := by
  have he : NormedSpace.exp K*(u : M.toStarSubalgebra)-u=
      (NormedSpace.exp K-1)*(u : M.toStarSubalgebra) := by rw [sub_mul,one_mul]
  rw [he]
  have hn := unitary_norm_le (u : M.toStarSubalgebra) u.property.1
  calc
    _ ≤ τ.norm₂ (NormedSpace.exp K-1)*‖(u : M.toStarSubalgebra)‖ := τ.norm₂_mul_le_right _ _
    _ ≤ τ.norm₂ (NormedSpace.exp K-1)*1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ ≤ τ.norm₂ K := by rw [mul_one]; exact norm₂_exp_sub_one_le τ K hK

end

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.perturbedUnitary_apply
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    (F.perturbedUnitary τ ω u z ell α : Sequences M) n=
      NormedSpace.exp (F.commonPerturbation τ ω u z ell α n)*(u : M.toStarSubalgebra) := by
  change (NormedSpace.exp (F.commonPerturbation τ ω u z ell α)) n*(u : M.toStarSubalgebra)=_
  rw [sequence_exp_apply]

theorem SuccessiveCoordinateHaar.perturbedUnitary_distance
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    τ.norm₂ ((F.perturbedUnitary τ ω u z ell α : Sequences M) n-u) ≤
      τ.norm₂ (F.commonPerturbation τ ω u z ell α n) := by
  rw [F.perturbedUnitary_apply]
  exact norm₂_exp_mul_sub_le τ _
    (congrArg (fun a : Sequences M => a n) (F.commonPerturbation_skew τ ω u z ell α)) u

theorem SuccessiveCoordinateHaar.perturbedWord_apply
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    (F.perturbedWord τ ω u z ell α : Sequences M) n=
      coordinateInclusion hNM (F.retainedUnitary τ ω 0 n : N.toStarSubalgebra)*
        ((List.range ell).map (fun j =>
          (F.perturbedUnitary τ ω u z ell α : Sequences M) n*
            coordinateInclusion hNM (F.retainedUnitary τ ω (j+1) n : N.toStarSubalgebra))).prod := by
  change sequenceEval n (F.perturbedWord τ ω u z ell α : Sequences M)=_
  simp only [perturbedWord,Submonoid.coe_mul,Submonoid.coe_list_prod,map_mul,map_list_prod,
    List.map_map,Function.comp_def]
  change (F.haarSequence τ ω 0 : Sequences M) n*
    ((List.range ell).map (fun j => (F.perturbedUnitary τ ω u z ell α : Sequences M) n*
      (F.haarSequence τ ω (j+1) : Sequences M) n)).prod=_
  simp only [F.haarSequence_apply,retainedUnitary]

set_option maxHeartbeats 1600000 in
theorem SuccessiveCoordinateHaar.select_perturbation_coordinate
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : constantQuotient τ ω xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ∃ n : ℕ,
      τ.norm₂ ((F.perturbedUnitary τ ω u z ell α : Sequences M) n-u) <
        α/Real.sqrt (2*ell)+1/(ell : ℝ) ∧
      ‖τ.trace (star xi*(F.perturbedWord τ ω u z ell α : Sequences M) n)-
        (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ <
          τ.norm₂ xi*(4*α^2/(1-2*α))+1/(ell : ℝ) := by
  have hε : (0 : ℝ)<1/(ell : ℝ) := by positivity
  have hc := F.perturbedWord_correlation_q129 τ ω u z (constantQuotient τ ω xi) hu hz hxi ell hell α hα hhalf
  have hb : ‖inner ℂ (sequenceInclusion τ ω (constantSequence xi))
      (sequenceInclusion τ ω (F.perturbedWord τ ω u z ell α : Sequences M))-
      (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ ≤ τ.norm₂ xi*(4*α^2/(1-2*α)) := by
    have ht : quotientTrace τ ω (star (constantQuotient τ ω xi)*
        (constantQuotientUnitary τ ω z : Q τ ω))=τ.trace (star xi*(z : M.toStarSubalgebra)) := by
      change quotientTrace τ ω (star (constantQuotient τ ω xi)*
        constantQuotient τ ω (z : M.toStarSubalgebra))=_
      rw [← map_star,← map_mul,constantQuotient_trace]
    rw [ht,constantQuotient_norm] at hc
    rw [sequenceInclusion_apply,sequenceInclusion_apply,inclusion_inner]
    exact hc
  obtain ⟨n,hn,ht⟩ := select_coordinate_with_bounds τ ω
    (F.commonPerturbation τ ω u z ell α) (constantSequence xi)
    (F.perturbedWord τ ω u z ell α : Sequences M)
    (α/Real.sqrt (2*ell)) (τ.norm₂ xi*(4*α^2/(1-2*α))) (1/(ell : ℝ))
    ((α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))) hε
    (F.commonPerturbation_norm_q129 τ ω u z hu hz ell hell α hα.le).le hb
  exact ⟨n,(F.perturbedUnitary_distance τ ω u z ell α n).trans_lt hn,ht⟩

end

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_represented_perturbation (hω : (ω : Filter ℕ) ≤ atTop)
    (u z : unitary M.toStarSubalgebra) (xi : M.toStarSubalgebra)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ∃ u' : unitary M.toStarSubalgebra, ∃ t : ℕ → unitary N.toStarSubalgebra,
      τ.norm₂ ((u' : M.toStarSubalgebra)-u) ≤ α/Real.sqrt (2*ell)+1/(ell : ℝ) ∧
      ‖τ.trace (star xi*(coordinateInclusion hNM (t 0 : N.toStarSubalgebra)*
        ((List.range ell).map (fun j => (u' : M.toStarSubalgebra)*
          coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod))-
        (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ ≤
          τ.norm₂ xi*(4*α^2/(1-2*α))+1/(ell : ℝ) := by
  obtain ⟨F⟩ := nonempty_successiveCoordinateHaar_q129 τ ω hNM hfactor hdiff hirr hsep hω
    {(constantQuotientUnitary τ ω u : Q τ ω),(constantQuotientUnitary τ ω z : Q τ ω),
      constantQuotient τ ω xi}
    (((Set.countable_singleton (constantQuotient τ ω xi)).insert _).insert _)
  obtain ⟨n,hn,ht⟩ := F.select_perturbation_coordinate τ ω u z xi
    (by simp) (by simp) (by simp) ell hell α hα hhalf
  refine ⟨unitaryCoordinate (F.perturbedUnitary τ ω u z ell α) n,
    (fun j => F.retainedUnitary τ ω j n),hn.le,?_⟩
  have he := F.perturbedWord_apply τ ω u z ell α n
  simpa only [unitaryCoordinate,he] using ht.le

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129NUNAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129One _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/
section
open Set Filter Topology
variable {X : Type*} [TopologicalSpace X]

theorem continuityCore_isGδ (f : X → ℝ) : IsGδ (continuityCore f) :=
  IsGδ.iInter_of_isOpen fun _ => isClosed_frontier.isOpen_compl

theorem continuityCore_dense [BaireSpace X] {f : X → ℝ}
    (hf : LowerSemicontinuous f) : Dense (continuityCore f) := by
  apply dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
  intro q
  exact interior_eq_empty_iff_dense_compl.mp (interior_frontier (hf.isClosed_preimage q))

theorem continuousAt_of_mem_continuityCore {f : X → ℝ}
    (hf : LowerSemicontinuous f) {x : X} (hx : x ∈ continuityCore f) :
    ContinuousAt f x := by
  apply continuousAt_iff_lower_upperSemicontinuousAt.mpr
  refine ⟨hf x, ?_⟩
  intro b hb
  obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn hb
  have hnot : x ∉ frontier {y | f y ≤ (q : ℝ)} := Set.mem_iInter.mp hx q
  have hint : x ∈ interior {y | f y ≤ (q : ℝ)} :=
    (mem_interior_iff_notMem_frontier (show x ∈ {y | f y ≤ (q : ℝ)} from hxq.le)).mpr hnot
  have hnhds : {y | f y ≤ (q : ℝ)} ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hint
  exact Filter.mem_of_superset hnhds fun y hy => lt_of_le_of_lt hy hqb

/-- The common continuity set for a countable family, as used before
extending the projection-norm conclusion to all L2 vectors. -/
theorem common_continuity_core [BaireSpace X] (f : ℕ → X → ℝ)
    (hf : ∀ n, LowerSemicontinuous (f n)) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ ∀ x ∈ C, ∀ n, ContinuousAt (f n) x := by
  refine ⟨⋂ n, continuityCore (f n), IsGδ.iInter (fun n => continuityCore_isGδ (f n)),
    dense_iInter_of_Gδ (fun n => continuityCore_isGδ (f n))
      (fun n => continuityCore_dense (hf n)), ?_⟩
  intro x hx n
  exact continuousAt_of_mem_continuityCore (hf n) (Set.mem_iInter.mp hx n)

/-- The uniform Lipschitz estimate in the vector variable extends continuity
from a dense sequence to every vector (eq:projection-vector-lipschitz). -/
theorem continuousAt_of_dense_lipschitz {E : Type*} [PseudoMetricSpace E]
    (F : E → X → ℝ) (e : ℕ → E) (he : DenseRange e)
    (hLip : ∀ x a b, dist (F a x) (F b x) ≤ dist a b)
    {x : X} (hcont : ∀ n, ContinuousAt (F (e n)) x) (a : E) :
    ContinuousAt (F a) x := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ := he.exists_dist_lt a (show 0 < ε / 3 by linarith)
  have hncont := Metric.continuousAt_iff'.mp (hcont n) (ε / 3) (by linarith)
  filter_upwards [hncont] with y hy
  have hleft := hLip y a (e n)
  have hright := hLip x (e n) a
  rw [dist_comm (e n) a] at hright
  calc
    dist (F a y) (F a x) ≤ dist (F a y) (F (e n) y) +
        dist (F (e n) y) (F a x) := dist_triangle _ _ _
    _ ≤ dist (F a y) (F (e n) y) +
        (dist (F (e n) y) (F (e n) x) + dist (F (e n) x) (F a x)) :=
      by linarith [dist_triangle (F (e n) y) (F (e n) x) (F a x)]
    _ < ε := by linarith

/-- Baire continuity of a family of Hilbert-space projections. -/
theorem common_continuity_of_lipschitz [BaireSpace X]
    {E : Type*} [PseudoMetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]
    (F : E → X → ℝ) (hf : ∀ a, LowerSemicontinuous (F a))
    (hLip : ∀ x a b, dist (F a x) (F b x) ≤ dist a b) :
    ∃ C : Set X, IsGδ C ∧ Dense C ∧ ∀ x ∈ C, ∀ a, ContinuousAt (F a) x := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (α := E)
  obtain ⟨C, hG, hd, hC⟩ := common_continuity_core (fun n => F (e n)) (fun n => hf (e n))
  exact ⟨C, hG, hd, fun x hx a => continuousAt_of_dense_lipschitz F e he hLip (hC x hx) a⟩

end

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/
section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

theorem projectionNorm_bounds (ξ : E) :
    0 ≤ projectionNorm K ξ ∧ projectionNorm K ξ ≤ ‖ξ‖ :=
  ⟨norm_nonneg _, K.norm_starProjection_apply_le ξ⟩

theorem projectionNorm_lipschitz (ξ η : E) :
    dist (projectionNorm K ξ) (projectionNorm K η) ≤ dist ξ η := by
  calc
    dist (projectionNorm K ξ) (projectionNorm K η) ≤
        dist (K.starProjection ξ) (K.starProjection η) := by
      simpa only [projectionNorm, dist_eq_norm] using
        dist_norm_norm_le (K.starProjection ξ) (K.starProjection η)
    _ ≤ dist ξ η := by
      simp only [dist_eq_norm, ← map_sub]
      exact K.norm_starProjection_apply_le (ξ - η)

theorem correlation_le_projectionNorm (ξ W : E) (hW : W ∈ K) (hunit : ‖W‖ = 1) :
    ‖inner ℂ ξ W‖ ≤ projectionNorm K ξ := by
  have hfix : K.starProjection W = W := K.starProjection_eq_self_iff.mpr hW
  have hi : inner ℂ (K.starProjection ξ) W = inner ℂ ξ W := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [← hi]
  simpa [projectionNorm, hunit] using norm_inner_le_norm (K.starProjection ξ) W

theorem residual_projection_zero (z : E) : K.starProjection (residual K z) = 0 := by
  apply K.starProjection_apply_eq_zero_iff.mpr
  exact K.sub_starProjection_mem_orthogonal z

theorem residual_correlation (z : E) :
    inner ℂ (residual K z) z = (‖residual K z‖ : ℂ) ^ 2 := by
  have horth : inner ℂ (residual K z) (K.starProjection z) = 0 :=
    K.starProjection_inner_eq_zero z _ (K.starProjection_apply_mem z)
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (residual K z)
  calc
    inner ℂ (residual K z) z =
        inner ℂ (residual K z) (residual K z + K.starProjection z) := by
      simp only [residual, sub_add_cancel]
    _ = inner ℂ (residual K z) (residual K z) := by rw [inner_add_right, horth, add_zero]
    _ = _ := hself

end

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem normalizedCorrelation_continuousAt (ξ : E) {w : E} (hw : w ≠ 0) :
    ContinuousAt (normalizedCorrelation ξ) w := by
  exact (continuous_const.inner continuous_id).norm.continuousAt.div
    continuous_norm.continuousAt (norm_ne_zero_iff.mpr hw)

theorem normalizedCorrelation_le_projectionNorm (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (ξ w : E) (hw : w ∈ K) :
    normalizedCorrelation ξ w ≤ projectionNorm K ξ := by
  by_cases hzero : w = 0
  · simpa [normalizedCorrelation, hzero] using (projectionNorm_bounds K ξ).1
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hzero
  apply (div_le_iff₀ hnorm).mpr
  have hfix : K.starProjection w = w := K.starProjection_eq_self_iff.mpr hw
  have hi : inner ℂ (K.starProjection ξ) w = inner ℂ ξ w := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [← hi]
  exact norm_inner_le_norm _ _

theorem normalizedCorrelation_starProjection (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (ξ : E) :
    normalizedCorrelation ξ (K.starProjection ξ) = projectionNorm K ξ := by
  by_cases hz : K.starProjection ξ = 0
  · simp [normalizedCorrelation, projectionNorm, hz]
  have hfix : K.starProjection (K.starProjection ξ) = K.starProjection ξ :=
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem ξ)
  have hi : inner ℂ (K.starProjection ξ) (K.starProjection ξ) =
      inner ℂ ξ (K.starProjection ξ) := by
    rw [K.inner_starProjection_left_eq_right, hfix]
  rw [normalizedCorrelation, ← hi, inner_self_eq_norm_sq_to_K]
  simp [projectionNorm, Complex.norm_real, pow_two, norm_ne_zero_iff.mpr hz]

/-- Dense continuous sections imply lower semicontinuity of every projection norm.
The index type need not be countable, matching the P-coefficient polynomials. -/
theorem projectionNorm_lowerSemicontinuous {X I : Type*} [TopologicalSpace X]
    (L : X → Submodule ℂ E) [∀ x, (L x).HasOrthogonalProjection]
    (b : I → X → E) (hb : ∀ i x, b i x ∈ L x) (hc : ∀ i, Continuous (b i))
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x))) (ξ : E) :
    LowerSemicontinuous (fun x => projectionNorm (L x) ξ) := by
  intro x r hr
  by_cases hneg : r < 0
  · exact Filter.Eventually.of_forall fun y => hneg.trans_le (projectionNorm_bounds (L y) ξ).1
  have hr0 : 0 ≤ r := le_of_not_gt hneg
  have hp : 0 < projectionNorm (L x) ξ := lt_of_le_of_lt hr0 hr
  have hv : (L x).starProjection ξ ≠ 0 := norm_pos_iff.mp hp
  have hqcont := normalizedCorrelation_continuousAt ξ hv
  have hqvalue := normalizedCorrelation_starProjection (L x) ξ
  obtain ⟨δ, hδ, hδprop⟩ := Metric.continuousAt_iff.mp hqcont
    ((projectionNorm (L x) ξ - r) / 2) (by linarith)
  obtain ⟨i, hi⟩ := (hd x).exists_dist_lt ((L x).orthogonalProjectionOnto ξ) hδ
  have hidist : dist (b i x) ((L x).starProjection ξ) < δ := by
    simpa only [Submodule.starProjection_apply, Subtype.dist_eq, dist_comm] using hi
  have hiq : r < normalizedCorrelation ξ (b i x) := by
    have ht := hδprop hidist
    rw [hqvalue, Real.dist_eq] at ht
    have hl := (abs_lt.mp ht).1
    linarith
  have hbinz : b i x ≠ 0 := by
    intro hz
    simp [normalizedCorrelation, hz] at hiq
    linarith
  have hbq : ContinuousAt (fun y => normalizedCorrelation ξ (b i y)) x :=
    (normalizedCorrelation_continuousAt ξ hbinz).comp (hc i).continuousAt
  have hevent : ∀ᶠ y in 𝓝 x, r < normalizedCorrelation ξ (b i y) :=
    hbq (Ioi_mem_nhds hiq)
  exact hevent.mono fun y hy =>
    hy.trans_le (normalizedCorrelation_le_projectionNorm (L y) ξ (b i y) (hb i y))

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_RelativeGeneration
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)
namespace RelativePolynomial

theorem norm_bound (p : Generator.RelativePolynomial N.toStarSubalgebra) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TraceUnitary τ, ‖eval τ hNM p u‖ ≤ C := by
  induction p with
  | coeff a => exact ⟨‖a‖,norm_nonneg _,fun _ => le_rfl⟩
  | indeterminate => exact ⟨1,zero_le_one,TraceUnitary.algebra_norm_le τ⟩
  | add p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C+D,add_nonneg hC hD,fun u => (norm_add_le _ _).trans (add_le_add (hp u) (hq u))⟩
  | mul p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C*D,mul_nonneg hC hD,fun u => (norm_mul_le _ _).trans
      (mul_le_mul (hp u) (hq u) (norm_nonneg _) hC)⟩
  | smul z p hp =>
    obtain ⟨C,hC,hp⟩ := hp
    refine ⟨‖z‖*C,mul_nonneg (norm_nonneg _) hC,fun u => ?_⟩
    simpa only [eval,norm_smul] using mul_le_mul_of_nonneg_left (hp u) (norm_nonneg z)
  | adjoint p hp =>
    obtain ⟨C,hC,hp⟩ := hp
    refine ⟨C,hC,fun u => ?_⟩
    change ‖star (eval τ hNM p u).val‖ ≤ C
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map]
    exact hp u

theorem continuous_sectionVector (p : Generator.RelativePolynomial N.toStarSubalgebra) :
    Continuous (sectionVector τ hNM p) := by
  induction p with
  | coeff a =>
    change Continuous (fun _ : TraceUnitary τ => (coordinateInclusion hNM a).val τ.vector)
    exact continuous_const
  | indeterminate => exact (TraceUnitary.vector_isometry τ).continuous
  | add p q hp hq => exact hp.add hq
  | smul z p hp => exact continuous_const.smul hp
  | adjoint p hp =>
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mpr
    exact norm₂_limit_star τ _ _ ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hp.continuousAt)
  | mul p q hp hq =>
    obtain ⟨C,_,hC⟩ := norm_bound τ hNM p
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mpr
    exact norm₂_limit_mul τ _ _ _ _ C hC
      ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hp.continuousAt)
      ((tendsto_vector_iff_norm₂ τ (𝓝 u) _ _).mp hq.continuousAt)

end RelativePolynomial
end Tracial

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

include hNM in
theorem relativeGenerated_le (u : TraceUnitary τ) : relativeGenerated (N := N) τ u ≤ M := by
  apply wstar_le (vonNeumann_wotClosed M)
  intro a ha
  rcases ha with ha | ha
  · exact hNM ha
  · rcases Set.mem_singleton_iff.mp ha with rfl
    exact (u.algebra τ).property

theorem le_relativeGenerated (u : TraceUnitary τ) : N ≤ relativeGenerated (N := N) τ u :=
  fun _ ha => subset_wstar _ (Or.inl ha)

theorem unitary_mem_relativeGenerated (u : TraceUnitary τ) :
    (u.algebra τ).val ∈ relativeGenerated (N := N) τ u :=
  subset_wstar _ (Or.inr rfl)

namespace RelativePolynomial

theorem exists_eval (u : TraceUnitary τ) (a : valueAlgebra (N := N) τ u) :
    ∃ p : Generator.RelativePolynomial N.toStarSubalgebra, (eval τ hNM p u).val=a.val := by
  rcases a with ⟨a,ha⟩
  induction ha using StarAlgebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact ⟨.coeff ⟨a,ha⟩,rfl⟩
    · rcases Set.mem_singleton_iff.mp ha with rfl
      exact ⟨.indeterminate,rfl⟩
  | algebraMap z => exact ⟨.smul z (.coeff 1),by simp [eval,Algebra.algebraMap_eq_smul_one]⟩
  | add a b _ _ ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨.add p q,by change (eval τ hNM p u).val+(eval τ hNM q u).val=a+b; rw [hp,hq]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨.mul p q,by change (eval τ hNM p u).val*(eval τ hNM q u).val=a*b; rw [hp,hq]⟩
  | star a _ ha =>
    obtain ⟨p,hp⟩ := ha
    exact ⟨.adjoint p,by change star (eval τ hNM p u).val=star a; rw [hp]⟩

theorem generated_eq_wstar_values (u : TraceUnitary τ) :
    (relativeGenerated (N := N) τ u).toStarSubalgebra =
      wstar (valueAlgebra (N := N) τ u : Set (H →L[ℂ] H)) := by
  apply le_antisymm
  · exact wstar_mono (StarAlgebra.subset_adjoin ℂ _)
  · exact wstar_le (wstar_closed _) (valueAlgebra_le τ u)

theorem exists_vector_approximation (u : TraceUnitary τ)
    (a : (relativeGenerated (N := N) τ u).toStarSubalgebra) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Generator.RelativePolynomial N.toStarSubalgebra,
      ‖a.val τ.vector-sectionVector τ hNM p u‖ < ε := by
  classical
  have ha : a.val ∈ Set.centralizer (Set.centralizer
      (valueAlgebra (N := N) τ u : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    change a.val ∈ (bicommutantVonNeumann (valueAlgebra (N := N) τ u)).toStarSubalgebra
    rw [← wstar_starAlgebra_eq_bicommutant,← generated_eq_wstar_values]
    exact a.property
  obtain ⟨b,hb⟩ := bicommutant_finite_strong_approximation _ a.val ha {τ.vector} ε hε
  obtain ⟨p,hp⟩ := exists_eval τ hNM u b
  exact ⟨p,by simpa only [sectionVector,hp] using hb τ.vector (Finset.mem_singleton_self _)⟩

end RelativePolynomial

theorem polynomialVector_dense (u : TraceUnitary τ) :
    DenseRange (fun p : Generator.RelativePolynomial N.toStarSubalgebra =>
      (⟨RelativePolynomial.sectionVector τ hNM p u,polynomialVector_mem τ hNM p u⟩ :
        relativeTraceSpace (N := N) τ u)) := by
  intro ξ
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hξ : ξ.val ∈ closure (Set.range (fun a : (relativeGenerated (N := N) τ u).toStarSubalgebra =>
      a.val τ.vector)) := ξ.property
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp hξ (ε/2) (half_pos hε)
  obtain ⟨p,hp⟩ := RelativePolynomial.exists_vector_approximation τ hNM u a (ε/2) (half_pos hε)
  refine ⟨_,⟨p,rfl⟩,?_⟩
  change dist ξ.val (RelativePolynomial.sectionVector τ hNM p u) < ε
  have hdist := dist_triangle ξ.val (a.val τ.vector) (RelativePolynomial.sectionVector τ hNM p u)
  rw [dist_eq_norm (a.val τ.vector)] at hdist
  linarith

end Tracial

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

theorem relativeUnitaryWord_mem_unitary (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    relativeUnitaryWord τ hNM u t ell ∈ unitary M.toStarSubalgebra := by
  apply (unitary M.toStarSubalgebra).mul_mem
  · exact Unitary.map_mem (coordinateInclusion hNM) (t 0).property
  · apply (unitary M.toStarSubalgebra).list_prod_mem
    intro a ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact (unitary M.toStarSubalgebra).mul_mem u.toUnitary.property
      (Unitary.map_mem (coordinateInclusion hNM) (t (j+1)).property)

theorem relativeUnitaryWord_mem_generated (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) :
    (relativeUnitaryWord τ hNM u t ell).val ∈ relativeGenerated (N := N) τ u := by
  let S := (relativeGenerated (N := N) τ u).toStarSubalgebra
  have hn (j : ℕ) : (coordinateInclusion hNM (t j : N.toStarSubalgebra)).val ∈ S :=
    le_relativeGenerated τ u (t j).val.property
  apply S.mul_mem (hn 0)
  change ((List.range ell).map (fun j => u.algebra τ*
    coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod ∈
      insideAlgebra (M := M) (P := relativeGenerated (N := N) τ u)
  apply (insideAlgebra (M := M) (P := relativeGenerated (N := N) τ u)).list_prod_mem
  intro a ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
  exact S.mul_mem (unitary_mem_relativeGenerated τ u) (hn (j+1))

theorem norm₂_unitary (u : unitary M.toStarSubalgebra) :
    τ.norm₂ (u : M.toStarSubalgebra)=1 := by
  have h := norm₂_sq_trace τ (u : M.toStarSubalgebra)
  rw [u.property.1,τ.trace_one,Complex.one_re] at h
  nlinarith [show 0 ≤ τ.norm₂ (u : M.toStarSubalgebra) from norm_nonneg _]

theorem relativeUnitaryWord_correlation_le (u : TraceUnitary τ)
    (t : ℕ → unitary N.toStarSubalgebra) (ell : ℕ) (xi : M.toStarSubalgebra) :
    ‖τ.trace (star xi*relativeUnitaryWord τ hNM u t ell)‖ ≤
      projectionNorm (relativeTraceSpace (N := N) τ u) (baseVector τ xi) := by
  rw [← baseVector_inner_trace]
  apply correlation_le_projectionNorm
  · exact Submodule.le_topologicalClosure _ ⟨⟨(relativeUnitaryWord τ hNM u t ell).val,
      relativeUnitaryWord_mem_generated τ hNM u t ell⟩,rfl⟩
  · exact norm₂_unitary τ ⟨_,relativeUnitaryWord_mem_unitary τ hNM u t ell⟩

theorem perturbation_size_tendsto (α : ℝ) :
    Tendsto (fun n : ℕ => α/Real.sqrt (2*((n+1 : ℕ) : ℝ))+1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ => 2*((n+1 : ℕ) : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hs := (Real.tendsto_sqrt_atTop.comp ht).const_div_atTop α
  have hi := hn.const_div_atTop (1 : ℝ)
  simpa only [add_zero,Function.comp_def] using hs.add hi

end Tracial

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

include hNM in
theorem relative_projection_lowerSemicontinuous (ξ : H) :
    LowerSemicontinuous (fun u : TraceUnitary τ =>
      projectionNorm (relativeTraceSpace (N := N) τ u) ξ) :=
  projectionNorm_lowerSemicontinuous (relativeTraceSpace (N := N) τ)
    (RelativePolynomial.sectionVector τ hNM) (polynomialVector_mem τ hNM)
    (RelativePolynomial.continuous_sectionVector τ hNM) (polynomialVector_dense τ hNM) ξ

include hNM in
theorem common_relative_projection_continuity
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, ∀ ξ : traceCyclicSpace τ,
        ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) ξ.val) u := by
  let := traceCyclicSpace_separable τ hsep
  exact common_continuity_of_lipschitz
    (fun (ξ : traceCyclicSpace τ) u => projectionNorm (relativeTraceSpace (N := N) τ u) ξ.val)
    (fun ξ => relative_projection_lowerSemicontinuous τ hNM ξ.val)
    (fun u ξ η => projectionNorm_lipschitz (relativeTraceSpace (N := N) τ u) ξ.val η.val)

include hNM in
theorem common_relative_projection_continuity_algebra
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, ∀ x : M.toStarSubalgebra,
        ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ x)) u := by
  obtain ⟨C,hC,hd,hcont⟩ := common_relative_projection_continuity τ hNM hsep
  exact ⟨C,hC,hd,fun u hu x => hcont u hu
    ⟨baseVector τ x,Submodule.le_topologicalClosure _ ⟨x,rfl⟩⟩⟩

/-! The bounded conditional expectation agrees with the actual Hilbert
projection. Proper subalgebras have a unitary outside them, yielding the
nonzero represented residual used by thm:relative-generation. -/

theorem conditionalExpectation_vector_projection (x : M.toStarSubalgebra) :
    (vectorOrbitClosure N.toStarSubalgebra τ.vector).starProjection (baseVector τ x) =
      baseVector τ (conditionalExpectation τ hNM x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.le_topologicalClosure _
      ⟨⟨(conditionalExpectation τ hNM x).val,conditionalExpectation_mem τ hNM x⟩,rfl⟩
  · intro w hw
    rw [← map_sub]
    apply inner_eq_zero_symm.mp
    have hc : IsClosed {y : H | inner ℂ y (baseVector τ (x-conditionalExpectation τ hNM x))=0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal (t := {y : H | inner ℂ y (baseVector τ (x-conditionalExpectation τ hNM x))=0})
      ?_ hc hw
    rintro _ ⟨a,rfl⟩
    change inner ℂ (baseVector τ (coordinateInclusion hNM a))
      (baseVector τ (x-conditionalExpectation τ hNM x))=0
    rw [baseVector_inner_trace]
    exact conditionalExpectation_orthogonal τ hNM x
      ⟨star (coordinateInclusion hNM a),N.toStarSubalgebra.star_mem' a.property⟩

include hNM in
theorem exists_unitary_outside (hne : N ≠ M) :
    ∃ z : unitary M.toStarSubalgebra, (z : M.toStarSubalgebra).val ∉ N := by
  classical
  by_contra h
  have hu : ∀ z : unitary M.toStarSubalgebra, (z : M.toStarSubalgebra).val ∈ N := by
    simpa only [not_exists,not_not] using h
  let : CStarAlgebra M.toStarSubalgebra := {}
  let S := (insideAlgebra (M := M) (P := N)).toSubalgebra.toSubmodule
  have hs : (⊤ : Submodule ℂ M.toStarSubalgebra) ≤ S := by
    rw [← CStarAlgebra.span_unitary M.toStarSubalgebra]
    exact Submodule.span_le.mpr (fun z hz => hu ⟨z,hz⟩)
  apply hne
  apply le_antisymm hNM
  intro a ha
  exact hs (show (⟨a,ha⟩ : M.toStarSubalgebra) ∈ (⊤ : Submodule ℂ M.toStarSubalgebra) from trivial)

theorem subalgebraResidual_vector (x : M.toStarSubalgebra) :
    baseVector τ (subalgebraResidual τ hNM x) =
      residual (vectorOrbitClosure N.toStarSubalgebra τ.vector) (baseVector τ x) := by
  rw [residual,conditionalExpectation_vector_projection τ hNM]
  exact map_sub (baseVector τ) _ _

theorem subalgebraResidual_projection (x : M.toStarSubalgebra) :
    (vectorOrbitClosure N.toStarSubalgebra τ.vector).starProjection
      (baseVector τ (subalgebraResidual τ hNM x))=0 := by
  rw [subalgebraResidual_vector]
  exact residual_projection_zero _ _

theorem subalgebraResidual_correlation (x : M.toStarSubalgebra) :
    τ.trace (star (subalgebraResidual τ hNM x)*x)=
      (τ.norm₂ (subalgebraResidual τ hNM x) : ℂ)^2 := by
  rw [← baseVector_inner_trace]
  change inner ℂ (baseVector τ (subalgebraResidual τ hNM x)) (baseVector τ x)=
    (‖baseVector τ (subalgebraResidual τ hNM x)‖ : ℂ)^2
  rw [subalgebraResidual_vector]
  exact residual_correlation _ _

theorem subalgebraResidual_norm_pos (x : M.toStarSubalgebra) (hx : x.val ∉ N) :
    0 < τ.norm₂ (subalgebraResidual τ hNM x) := by
  apply lt_of_le_of_ne (norm_nonneg _)
  intro h
  have hz := (τ.norm₂_eq_zero_iff _).mp h.symm
  have he : x=conditionalExpectation τ hNM x := sub_eq_zero.mp hz
  exact hx (he ▸ conditionalExpectation_mem τ hNM x)

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Generation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem relative_generation_at_continuity (u : TraceUnitary τ)
    (hcont : ∀ x : M.toStarSubalgebra,
      ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ x)) u) :
    relativeGenerated (N := N) τ u=M := by
  classical
  by_contra hneq
  let Q := relativeGenerated (N := N) τ u
  have hQM : Q ≤ M := relativeGenerated_le τ hNM u
  obtain ⟨z,hz⟩ := exists_unitary_outside hQM hneq
  let xi := subalgebraResidual τ hQM (z : M.toStarSubalgebra)
  let s : ℝ := τ.norm₂ xi
  have hs : 0 < s := subalgebraResidual_norm_pos τ hQM _ hz
  let α : ℝ := min (1/4) (s/32)/2
  have hα : 0 < α := half_pos (lt_min (by norm_num) (by positivity))
  have hq : α < 1/4 := by
    have h := min_le_left (1/4 : ℝ) (s/32)
    dsimp [α] at hα ⊢
    linarith
  have hsmall : α < s/32 := by
    have h := min_le_right (1/4 : ℝ) (s/32)
    dsimp [α] at hα ⊢
    linarith
  have hhalf : α < 1/2 := by linarith
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have he (n : ℕ) := exists_represented_perturbation τ ω hNM hfactor hdiff hirr hsep hω
    u.toUnitary z xi (n+1) (Nat.succ_pos _) α hα hhalf
  choose v t hv ht using he
  let V : ℕ → TraceUnitary τ := fun n => ⟨v n⟩
  have hV : Tendsto V atTop (𝓝 u) := by
    apply (TraceUnitary.tendsto_iff τ atTop V u).mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hv (perturbation_size_tendsto α)
  let F : TraceUnitary τ → ℝ := fun v =>
    projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ xi)
  have hFzero : F u=0 := by
    change ‖(vectorOrbitClosure Q.toStarSubalgebra τ.vector).starProjection
      (baseVector τ (subalgebraResidual τ hQM (z : M.toStarSubalgebra)))‖=0
    rw [subalgebraResidual_projection,norm_zero]
  let δ : ℕ → ℝ := fun n => 1/((n+1 : ℕ) : ℝ)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  let c : ℕ → ℂ := fun n => τ.trace (star xi*relativeUnitaryWord τ hNM (V n) (t n) (n+1))
  have hc (n : ℕ) : ‖c n-((α*s^2/2 : ℝ) : ℂ)‖ ≤
      s*(4*α^2/(1-2*α))+δ n := by
    have hn := ht n
    have hcorr : τ.trace (star xi*(z : M.toStarSubalgebra))=(s : ℂ)^2 :=
      subalgebraResidual_correlation τ hQM (z : M.toStarSubalgebra)
    rw [hcorr] at hn
    have heq : ((α*s^2/2 : ℝ) : ℂ)=(α : ℂ)/2*(s : ℂ)^2 := by
      push_cast
      ring
    rw [heq]
    exact hn
  have hproj (n : ℕ) : ‖c n‖ ≤ F (V n) :=
    relativeUnitaryWord_correlation_le τ hNM (V n) (t n) (n+1) xi
  exact no_continuous_correlated_sequence F (hcont xi) hFzero V hV δ hδ c
    hs hα hq hsmall hc hproj

theorem represented_relative_generation_q129_oai :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val})=M.toStarSubalgebra := by
  obtain ⟨C,hC,hd,hcont⟩ := common_relative_projection_continuity_algebra τ hNM hsep
  refine ⟨C,hC,hd,fun u hu => ?_⟩
  exact congrArg VonNeumannAlgebra.toStarSubalgebra
    (relative_generation_at_continuity τ hNM hfactor hdiff hirr hsep u (hcont u hu))

end

/-! Four generators under a faithful normalized vector trace and trace-vector separability. -/
open scoped ComplexStarModule

/-! Single generation for the explicit faithful normalized vector-trace
representation with separable trace-vector range. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.represented_relative_generation_q129_oai.{u_1} := @OAI.Generator.Tracial.represented_relative_generation_q129_oai.{u_1}
