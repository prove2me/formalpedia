-- Prove2me | solution 1 for OAI.RelativeGeneration.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:04:35+00:00
-- url     : https://prove2.me/submissions/24eac4bb-5003-4524-bb93-3fed61014e0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_RelativeGeneration
import Definitions.Def_OAIQ129G002
import Definitions.Def_OAIQ129G016
import Theorems.Thm_OAI_Generator_Tracial_represented_relative_generation_q129
import Theorems.Thm_OAI_Generator_Tracial_traceOrbit_isSeparable_of_separablePredual_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129SMul _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace UltrapowerBridge

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {H}
omit [CompleteSpace H] in
theorem vectorFunctional_ultraweak_continuous (ξ η : H) :
    @Continuous _ _ (ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => inner ℂ ξ (T η)) := by
  let x : ℕ → H := fun n => if n = 0 then ξ else 0
  let y : ℕ → H := fun n => if n = 0 then η else 0
  have hs : Summable (fun n => ‖x n‖ * ‖y n‖) := by
    exact (hasSum_ite_eq (0 : ℕ) (‖ξ‖ * ‖η‖)).summable.congr (by intro n; by_cases h : n = 0 <;> simp [x,y,h])
  have hc : @Continuous _ _ (ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => ∑' n, inner ℂ (x n) (T (y n))) :=
    continuous_iInf_dom (i := x) (continuous_iInf_dom (i := y)
      (continuous_iInf_dom (i := hs) continuous_induced_dom))
  have he (T : H →L[ℂ] H) :
      (fun n => inner ℂ (x n) (T (y n))) =
        (fun n => if n = 0 then inner ℂ ξ (T η) else 0) := by
    funext n
    by_cases h : n = 0 <;> simp [x,y,h]
  have hf : (fun T : H →L[ℂ] H => ∑' n, inner ℂ (x n) (T (y n))) =
      (fun T => inner ℂ ξ (T η)) := by
    funext T
    rw [he]
    exact tsum_ite_eq 0 _
  rw [hf] at hc
  exact hc

end UltrapowerBridge

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/

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
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceNormalCStar
theorem traceFreeTrace_normal :
    @Continuous _ _ (UltrapowerBridge.algebraUltraweakTopology M) inferInstance
      (traceFreeTrace hfactor hdiff hfinite hunit) := by
  obtain ⟨n,ξ,η,h⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have hc : @Continuous _ _ (UltrapowerBridge.ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => ∑ i, inner ℂ (η i) (T (ξ i))) := by
    let : TopologicalSpace (H →L[ℂ] H) := UltrapowerBridge.ultraweakTopology H
    exact continuous_finsetSum _ (fun i _ => UltrapowerBridge.vectorFunctional_ultraweak_continuous (η i) (ξ i))
  have he : (traceFreeTrace hfactor hdiff hfinite hunit : M.toStarSubalgebra → ℂ)=
      (fun x => ∑ i, inner ℂ (η i) (x.val (ξ i))) := funext h
  rw [he]
  exact @Continuous.comp _ _ _ (UltrapowerBridge.algebraUltraweakTopology M)
    (UltrapowerBridge.ultraweakTopology H) _ _ _ hc continuous_induced_dom

end Generator.Tracial

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
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

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

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.FactorTraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Literal weak-operator generation under a concrete star-algebra isomorphism.
Continuity is explicitly for the restricted WOT, not the operator norm topology.
This transport does not construct a trace representation of a finite factor. -/
section
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}
  {T : StarSubalgebra ℂ (K →L[ℂ] K)}

theorem concretePreimage_le (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) : concretePreimage φ Q ≤ S := by
  rintro a ⟨b, _, rfl⟩
  exact b.property

theorem mem_concretePreimage (φ : S →⋆ₐ[ℂ] T)
    (Q : StarSubalgebra ℂ (K →L[ℂ] K)) (a : S) :
    a.val ∈ concretePreimage φ Q ↔ (φ a).val ∈ Q := by
  constructor
  · rintro ⟨b, hb, hab⟩
    have h : b = a := Subtype.ext hab
    subst b
    exact hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! Transport of the unchanged finite diffuse factor predicate.
The algebraic fields use the actual star isomorphism; target WOT closedness
is explicit. No trace or separability conclusion is inferred. -/

theorem isII1Factor_of_starAlgEquiv (e : S ≃⋆ₐ[ℂ] T)
    (hS : IsII1Factor S) (hT : WOTClosed T) : IsII1Factor T where
  nonzero := by
    intro h
    have ht : (0 : T) = 1 := Subtype.ext h
    have hs : (0 : S) = 1 := e.injective (by simpa only [map_zero, map_one] using ht)
    exact hS.nonzero (congrArg Subtype.val hs)
  weaklyClosed := hT
  factor := by
    intro x hx
    have hc : ∀ y : S, y * e.symm x = e.symm x * y := by
      intro y
      apply e.injective
      change e (y * e.symm x) = e (e.symm x * y)
      simpa only [map_mul, e.apply_symm_apply] using hx (e y)
    obtain ⟨c, hc⟩ := hS.factor (e.symm x) hc
    refine ⟨c, ?_⟩
    calc x = e (e.symm x) := (e.apply_symm_apply x).symm
         _ = e (algebraMap ℂ S c) := congrArg e hc
         _ = algebraMap ℂ T c := e.toAlgEquiv.commutes c
  finite := by
    intro v hv
    have h : star (e.symm v) * e.symm v = 1 := by
      simpa only [map_mul, map_star, map_one] using congrArg e.symm hv
    have hf := hS.finite (e.symm v) h
    simpa only [map_mul, map_star, map_one, e.apply_symm_apply] using congrArg e hf
  diffuse := by
    intro p hp hp0
    have hsp : IsStarProjection (e.symm p) := hp.map e.symm
    have hsp0 : e.symm p ≠ 0 := by
      intro hz
      apply hp0
      simpa only [e.apply_symm_apply, map_zero] using congrArg e hz
    obtain ⟨q, hq, hq0, hqp, hpq, hqp'⟩ := hS.diffuse (e.symm p) hsp hsp0
    refine ⟨e q, hq.map e, ?_, ?_, ?_, ?_⟩
    · intro hz
      apply hq0
      apply e.injective
      change e q = e 0
      simpa only [map_zero] using hz
    · intro heq
      apply hqp
      apply e.injective
      change e q = e (e.symm p)
      simpa only [e.apply_symm_apply] using heq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hpq
    · simpa only [map_mul, e.apply_symm_apply] using congrArg e hqp'

end

/-! Compact original image balls and spectral clipping identify the actual
bicommutant with the original algebra's represented image. -/
open Filter
open scoped ComplexConjugate ComplexStarModule CStarAlgebra Pointwise Topology
namespace Tracial

/-! Algebraic and isometric transport of factor structure and existential Banach preduals. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

local instance traceHilbertTransportOperatorCStar_r8ec97b_1 : CStarAlgebra (K →L[ℂ] K) := {}
attribute [local instance] OAI.Generator.Tracial.traceHilbertTransportClosureCStar
theorem traceFreeHilbertClosure_hasSeparablePredual
    (hsep : HasSeparablePredual M.toStarSubalgebra) : HasSeparablePredual (N).toStarSubalgebra := by
  obtain ⟨X,g,s,c,hs,⟨d⟩⟩ := hsep
  exact ⟨X,g,s,c,hs,⟨d.trans (traceFreeHilbertIsometry hfactor hdiff hfinite hunit)⟩⟩

end Tracial

/-! First step of generation transport: compact balls and closed vector balls
for the represented intersection with any original WOT-closed subalgebra. -/
open Filter
open scoped Topology CStarAlgebra

/-! Closed images of original WOT-closed subalgebras in the constructed representation. -/
open Filter
open scoped Topology CStarAlgebra ComplexStarModule

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_ConditionalMembership
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- This is the actual bounded conditional-expectation step, including faithfulness. -/
theorem mem_subalgebra_of_baseVector_mem {Q : VonNeumannAlgebra H}
    (hQM : Q ≤ M) (x : M.toStarSubalgebra)
    (hx : baseVector τ x ∈ vectorOrbitClosure Q.toStarSubalgebra τ.vector) :
    x.val ∈ Q := by
  have hv := (vectorOrbitClosure Q.toStarSubalgebra τ.vector).starProjection_eq_self_iff.mpr hx
  rw [conditionalExpectation_vector_projection τ hQM x] at hv
  have he : conditionalExpectation τ hQM x = x := baseVector_injective τ hv
  exact he ▸ conditionalExpectation_mem τ hQM x

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_DistanceSections
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.UltrapowerBridge.q129Add _root_.OAI.UltrapowerBridge.q129AddCommGroup _root_.OAI.UltrapowerBridge.q129Monoid _root_.OAI.UltrapowerBridge.q129Mul _root_.OAI.UltrapowerBridge.q129NAS _root_.OAI.UltrapowerBridge.q129Neg _root_.OAI.UltrapowerBridge.q129Ring _root_.OAI.UltrapowerBridge.q129Semiring _root_.OAI.UltrapowerBridge.q129Sub _root_.OAI.UltrapowerBridge.q129Zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- Distance sublevels for sets with dense continuous sections.
   In the relative-generation application, the sections are coefficient-polynomial vectors. -/
open scoped Topology
namespace Generator.RelativeCompletion
variable {E X I : Type*} [PseudoMetricSpace E]

theorem infDist_lt_iff_dense_sections
    (L : X → Set E) (b : I → X → E)
    (hb : ∀ i x, b i x ∈ L x)
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x)))
    (hne : ∀ x, (L x).Nonempty) (ξ : E) (x : X) (ε : ℝ) :
    Metric.infDist ξ (L x) < ε ↔ ∃ i, dist ξ (b i x) < ε := by
  constructor
  · intro h
    obtain ⟨y, hy, hdist⟩ := (Metric.infDist_lt_iff (hne x)).mp h
    obtain ⟨i, hi⟩ := (hd x).exists_dist_lt ⟨y,hy⟩ (sub_pos.mpr hdist)
    refine ⟨i, ?_⟩
    have ht := dist_triangle ξ y (b i x)
    have hi' : dist y (b i x) < ε - dist ξ y := hi
    linarith
  · rintro ⟨i,hi⟩
    exact (Metric.infDist_le_dist_of_mem (hb i x)).trans_lt hi

variable [TopologicalSpace X]

theorem isOpen_infDist_lt_dense_sections
    (L : X → Set E) (b : I → X → E)
    (hb : ∀ i x, b i x ∈ L x)
    (hc : ∀ i, Continuous (b i))
    (hd : ∀ x, DenseRange (fun i => (⟨b i x, hb i x⟩ : L x)))
    (hne : ∀ x, (L x).Nonempty) (ξ : E) (ε : ℝ) :
    IsOpen {x | Metric.infDist ξ (L x) < ε} := by
  have he : {x | Metric.infDist ξ (L x) < ε} =
      ⋃ i, {x | dist ξ (b i x) < ε} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact infDist_lt_iff_dense_sections L b hb hd hne ξ x ε
  rw [he]
  exact isOpen_iUnion fun i => isOpen_lt (continuous_const.dist (hc i)) continuous_const

end Generator.RelativeCompletion

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_OriginalTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- Original-factor relative transport. The forward direction is
   proved from concrete strong approximation and the constructed trace, not
   from a postulated representation/normality interface. -/
open Filter
open scoped Topology
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)
local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "σ" => traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit
local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

/-- Strong convergence in the original representation implies trace-vector
convergence in the constructed representation. No norm bound or ambient
Hilbert-space separability is assumed. The finite-vector formula is already
proved for the faithful normalized trace of an original II₁ factor. -/
theorem traceFreeHilbertVector_tendsto_of_strong
    {I : Type*} (l : Filter I) (a : I → M.toStarSubalgebra) (x : M.toStarSubalgebra)
    (ha : ∀ v : H, Tendsto (fun i => (a i).val v) l (𝓝 (x.val v))) :
    Tendsto (fun i => π (a i) Ω) l (𝓝 (π x Ω)) := by
  obtain ⟨n,ξ,η,htrace⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have hnorm (b : M.toStarSubalgebra) :
      ‖π b Ω‖^2 = ∑ j, (inner ℂ (b.val (η j)) (b.val (ξ j))).re := by
    rw [traceFreeHilbertAction_vector, LinearIsometry.norm_map,
      traceFreeCopy_norm_sq, htrace, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (inner ℂ (η j) (star b.val (b.val (ξ j)))).re = _
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hdiffv (v : H) : Tendsto (fun i => ((a i)-x).val v) l (𝓝 0) := by
    change Tendsto (fun i => (a i).val v-x.val v) l (𝓝 0)
    simpa only [sub_self] using (ha v).sub
      (tendsto_const_nhds : Tendsto (fun _ : I => x.val v) l (𝓝 (x.val v)))
  have hs : Tendsto (fun i => ‖π (a i-x) Ω‖^2) l (𝓝 0) := by
    simp_rw [hnorm]
    have hh := tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => (Complex.continuous_re.tendsto _).comp ((hdiffv (η j)).inner (hdiffv (ξ j))))
    simpa only [Function.comp_apply,inner_zero_left, Complex.zero_re, Finset.sum_const_zero] using hh
  have hn : Tendsto (fun i => ‖π (a i-x) Ω‖) l (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simpa only [dist_eq_norm, map_sub, sub_apply] using hn

/-- Forward closure transport, with the actual conditional expectation used
   to pass from trace-vector closure back to bounded-algebra membership. -/
theorem traceFreeHilbert_mem_of_wstar
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAM : A ≤ M.toStarSubalgebra)
    (Q : VonNeumannAlgebra K) (hQR : Q ≤ R)
    (hAQ : ∀ a : M.toStarSubalgebra, a.val ∈ A → π a ∈ Q)
    (x : M.toStarSubalgebra) (hx : x.val ∈ wstar (A : Set (H →L[ℂ] H))) :
    π x ∈ Q := by
  classical
  have hxb : x.val ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
    rw [← bicommutantVonNeumann_coe]
    rwa [wstar_starAlgebra_eq_bicommutant] at hx
  obtain ⟨a,ha⟩ := bicommutant_exists_strong_net A x.val hxb
  let b : Finset H × ℕ → M.toStarSubalgebra := fun i => ⟨(a i).val,hAM (a i).property⟩
  have hb := traceFreeHilbertVector_tendsto_of_strong hfactor hdiff hfinite hunit atTop b x ha
  apply mem_subalgebra_of_baseVector_mem σ hQR (e x)
  apply (Submodule.isClosed_topologicalClosure (vectorOrbitMap Q.toStarSubalgebra Ω).range).mem_of_tendsto hb
  exact Eventually.of_forall fun i =>
    Submodule.le_topologicalClosure _ ⟨⟨π (b i),hAQ (b i) (a i).property⟩,rfl⟩

/-- The preimage of a represented von Neumann subalgebra is genuinely WOT
closed, proved from the actual constructed representation. -/
theorem traceFreeHilbert_preimage_wotClosed
    (Q : VonNeumannAlgebra K) (hQR : Q ≤ R) :
    WOTClosed (concretePreimage (e).toStarAlgHom Q.toStarSubalgebra) := by
  let A := concretePreimage (e).toStarAlgHom Q.toStarSubalgebra
  have hAM : A ≤ M.toStarSubalgebra := concretePreimage_le _ _
  have heq : wstar (A : Set (H →L[ℂ] H)) = A := by
    refine le_antisymm ?_ (show A ≤ wstar (A : Set (H →L[ℂ] H)) from subset_wstar _)
    intro x hx
    have hxM : x ∈ M.toStarSubalgebra := wstar_le (vonNeumann_wotClosed M) hAM hx
    apply (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra ⟨x,hxM⟩).mpr
    exact traceFreeHilbert_mem_of_wstar hfactor hdiff hfinite hunit A hAM Q hQR
      (fun a ha => (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra a).mp ha)
      ⟨x,hxM⟩ hx
  change WOTClosed A
  rw [← heq]
  exact wstar_closed _

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_InclusionTransport
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.FactorTraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- Actual image inclusion, algebra equivalence, hypotheses, and relative generation. -/
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)
local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "R" => traceFreeHilbertClosure hfactor hdiff hfinite hunit
local notation "e" => traceFreeHilbertEquiv hfactor hdiff hfinite hunit

variable (P : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : WOTClosed P)
local notation "N" => traceFreeRelativeImage hfactor hdiff hfinite hunit P hP

variable (hPM : P ≤ M.toStarSubalgebra)

include hPM in
theorem traceFreeRelativeImage_isII1Factor (hII : IsII1Factor P) :
    IsII1Factor (N).toStarSubalgebra :=
  isII1Factor_of_starAlgEquiv
    (traceFreeRelativeImageEquiv hfactor hdiff hfinite hunit P hP hPM) hII
    (vonNeumann_wotClosed N)

theorem traceFreeRelativeImage_irreducible
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : P, StarSubalgebra.inclusion hPM a*c=c*StarSubalgebra.inclusion hPM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (R).toStarSubalgebra,
      (∀ a : (N).toStarSubalgebra,
        coordinateInclusion (traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP) a*c =
        c*coordinateInclusion (traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP) a) →
      ∃ z : ℂ,c=z • (1 : (R).toStarSubalgebra) := by
  intro c hc
  have hcomm (a : P) :
      StarSubalgebra.inclusion hPM a*(e).symm c=(e).symm c*StarSubalgebra.inclusion hPM a := by
    apply (e).injective
    rw [map_mul,map_mul]
    change (e) (StarSubalgebra.inclusion hPM a)*(e) ((e).symm c) =
      (e) ((e).symm c)*(e) (StarSubalgebra.inclusion hPM a)
    rw [StarAlgEquiv.apply_symm_apply]
    exact hc (traceFreeRelativeImageEquiv hfactor hdiff hfinite hunit P hP hPM a)
  obtain ⟨z,hz⟩ := hirr ((e).symm c) hcomm
  exact ⟨z,by simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using congrArg (e) hz⟩

include hPM in
/-- Generation is transported both ways, using closed preimages and closed images. -/
theorem traceFreeRelativeGeneration_iff (u : M.toStarSubalgebra) :
    wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val}) = M.toStarSubalgebra ↔
      wstar ((N : Set (K →L[ℂ] K)) ∪ {π u}) = (R).toStarSubalgebra := by
  constructor
  · intro hgen
    let Q := vonNeumannOfWOTClosed
      (wstar ((N : Set (K →L[ℂ] K)) ∪ {π u})) (wstar_closed _)
    have hQR : Q ≤ R := wstar_le (vonNeumann_wotClosed R) (by
      rintro a (ha|ha)
      · exact traceFreeRelativeImage_le hfactor hdiff hfinite hunit P hP ha
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit u)
    have hpre : M.toStarSubalgebra ≤ concretePreimage (e).toStarAlgHom Q.toStarSubalgebra := by
      apply le_trans (le_of_eq hgen.symm)
      apply wstar_le (traceFreeHilbert_preimage_wotClosed hfactor hdiff hfinite hunit Q hQR)
      rintro a (ha|ha)
      · apply (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra ⟨a,hPM ha⟩).mpr
        exact subset_wstar _ (Or.inl ⟨⟨a,hPM ha⟩,ha,rfl⟩)
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra u).mpr
          (subset_wstar _ (Or.inr (Set.mem_singleton _)))
    apply le_antisymm (show Q.toStarSubalgebra ≤ (R).toStarSubalgebra from hQR)
    intro b hb
    let a := (e).symm ⟨b,hb⟩
    have ha := (mem_concretePreimage (e).toStarAlgHom Q.toStarSubalgebra a).mp (hpre a.property)
    change ((e) ((e).symm ⟨b,hb⟩)).val ∈ Q.toStarSubalgebra at ha
    simpa only [StarAlgEquiv.apply_symm_apply] using ha
  · intro hgen
    let A := wstar ((P : Set (H →L[ℂ] H)) ∪ {u.val})
    have hAM : A ≤ M.toStarSubalgebra := wstar_le (vonNeumann_wotClosed M) (by
      rintro a (ha|ha)
      · exact hPM ha
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact u.property)
    let B := (A.comap M.toStarSubalgebra.subtype).map π
    have hRB : (R).toStarSubalgebra ≤ B := by
      apply le_trans (le_of_eq hgen.symm)
      apply wstar_le (traceFreeSubalgebraImage_wotClosed hfactor hdiff hfinite hunit A
        (wstar_closed _))
      rintro a (ha|ha)
      · obtain ⟨b,hb,rfl⟩ := ha
        exact ⟨b,subset_wstar _ (Or.inl hb),rfl⟩
      · obtain rfl := Set.mem_singleton_iff.mp ha
        exact ⟨u,subset_wstar _ (Or.inr (Set.mem_singleton _)),rfl⟩
    apply le_antisymm hAM
    intro a ha
    obtain ⟨b,hb,he⟩ := hRB (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit ⟨a,ha⟩)
    have he' := traceFreeHilbertAction_injective hfactor hdiff hfinite hunit he
    change b.val ∈ A at hb
    rwa [he'] at hb

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_LocusTopology
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

open scoped Topology

namespace Generator.Tracial

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

include hNM in
theorem relativeDistance_sublevel_open (ξ : H) (ε : ℝ) :
    IsOpen {unitary : TraceUnitary τ | relativeDistance (N := N) τ ξ unitary < ε} :=
  RelativeCompletion.isOpen_infDist_lt_dense_sections
    (fun unitary => (relativeTraceSpace (N := N) τ unitary : Set H))
    (RelativePolynomial.sectionVector τ hNM) (polynomialVector_mem τ hNM)
    (RelativePolynomial.continuous_sectionVector τ hNM)
    (polynomialVector_dense τ hNM)
    (fun unitary => ⟨0, (relativeTraceSpace (N := N) τ unitary).zero_mem⟩) ξ ε

include hNM in
theorem relativeGenerated_eq_iff_dense_distances
    (η : ℕ → traceCyclicSpace τ) (hη : DenseRange η) (unitary : TraceUnitary τ) :
    relativeGenerated (N := N) τ unitary = M ↔
      ∀ index level : ℕ,
        relativeDistance (N := N) τ (η index).val unitary < 1 / (level + 1 : ℝ) := by
  constructor
  · intro heq index level
    have hmem : (η index).val ∈ relativeTraceSpace (N := N) τ unitary := by
      change (η index).val ∈
        vectorOrbitClosure (relativeGenerated (N := N) τ unitary).toStarSubalgebra τ.vector
      rw [heq]
      exact (η index).property
    change Metric.infDist _ _ < _
    rw [Metric.infDist_zero_of_mem hmem]
    positivity
  · intro hdist
    let traceSpace := relativeTraceSpace (N := N) τ unitary
    have hclosed : IsClosed (traceSpace : Set H) := Submodule.isClosed_topologicalClosure _
    have hmem (index : ℕ) : (η index).val ∈ traceSpace := by
      apply (hclosed.mem_iff_infDist_zero ⟨0, traceSpace.zero_mem⟩).mpr
      apply le_antisymm _ Metric.infDist_nonneg
      by_contra hpos
      obtain ⟨level, hlevel⟩ := exists_nat_one_div_lt (lt_of_not_ge hpos)
      exact (not_lt_of_ge (hdist index level).le) hlevel
    have hall (ξ : traceCyclicSpace τ) : ξ.val ∈ traceSpace := by
      have hpreimage : IsClosed {ξ : traceCyclicSpace τ | ξ.val ∈ traceSpace} :=
        hclosed.preimage continuous_subtype_val
      exact closure_minimal (by rintro _ ⟨index, rfl⟩; exact hmem index) hpreimage (hη ξ)
    apply le_antisymm (relativeGenerated_le τ hNM unitary)
    intro element helement
    exact mem_subalgebra_of_baseVector_mem τ (relativeGenerated_le τ hNM unitary)
      ⟨element, helement⟩
      (hall ⟨baseVector τ ⟨element, helement⟩,
        Submodule.le_topologicalClosure _ ⟨⟨element, helement⟩, rfl⟩⟩)

include hNM in
theorem relativeGeneratingLocus_eq_iInter
    (η : ℕ → traceCyclicSpace τ) (hη : DenseRange η) :
    {unitary : TraceUnitary τ | relativeGenerated (N := N) τ unitary = M} =
      ⋂ index : ℕ, ⋂ level : ℕ,
        {unitary | relativeDistance (N := N) τ (η index).val unitary <
          1 / (level + 1 : ℝ)} := by
  ext unitary
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact relativeGenerated_eq_iff_dense_distances τ hNM η hη unitary

include hNM in
theorem relativeGeneratingLocus_isGδ
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    IsGδ {unitary : TraceUnitary τ | relativeGenerated (N := N) τ unitary = M} := by
  let := traceCyclicSpace_separable τ hsep
  obtain ⟨η, hη⟩ := TopologicalSpace.exists_dense_seq (traceCyclicSpace τ)
  rw [relativeGeneratingLocus_eq_iInter τ hNM η hη]
  exact IsGδ.iInter fun index => IsGδ.iInter_of_isOpen fun level =>
    relativeDistance_sublevel_open τ hNM (η index).val (1 / (level + 1 : ℝ))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_OriginalUnitary
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- Normalized trace-two topology on actual unitaries of the original factor.
   The wrapper avoids Mathlib's existing operator-norm topology on unitary S. -/
open scoped Topology
namespace Generator
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {S : StarSubalgebra ℂ (H →L[ℂ] H)}

open Tracial
variable (S) (hS : IsII1Factor S)
local notation "hf" => hS.factor_smul
local notation "hu" => hS.one_ne_zero

attribute [local instance] OAI.Generator.factorTracePreNormed
attribute [local instance] OAI.Generator.factorTracePreInner
/-- The trace constructed from the factor hypotheses is faithful, normal, and normalized. -/
theorem normalizedFactorTrace_isNormalizedTrace :
    RelativeGeneration.IsNormalizedTrace S (normalizedFactorTrace S hS) := by
  let : CompleteSpace (factorVonNeumann hS).toStarSubalgebra :=
    baseCompleteSpace (factorVonNeumann hS)
  let : CStarAlgebra (factorVonNeumann hS).toStarSubalgebra := {}
  let : PartialOrder (factorVonNeumann hS).toStarSubalgebra :=
    CStarAlgebra.spectralOrder _
  let : StarOrderedRing (factorVonNeumann hS).toStarSubalgebra :=
    CStarAlgebra.spectralOrderedRing _
  obtain ⟨_, normalized, positive, star_preserving, tracial⟩ :=
    traceFreeTrace_spec (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu
  refine
    { normalized := normalized
      positive := fun element => positive (star element * element) (star_mul_self_nonneg element)
      star_preserving := star_preserving
      tracial := tracial
      faithful := ?_
      normal := traceFreeTrace_normal (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu }
  intro element trace_zero
  apply (CStarRing.star_mul_self_eq_zero_iff element).mp
  exact (traceFreeTrace_faithful (M := factorVonNeumann hS) hf hS.diffuse hS.finite hu
    (star element * element) (star_mul_self_nonneg element)).mp trace_zero

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_RepresentedLocus
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

open scoped Topology

/- The whole relative-generating locus, not only a residual subset. -/
namespace Generator.Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

/-- Full represented theorem: the previously proved residual subset is reused only for density. -/
theorem represented_full_relative_generation
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ r : N.toStarSubalgebra, IsStarProjection r → r ≠ 0 →
      ∃ q : N.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra, coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    IsGδ {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} ∧
    Dense {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} := by
  have he : {u : TraceUnitary τ |
      wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val}) = M.toStarSubalgebra} =
      {u : TraceUnitary τ | relativeGenerated (N := N) τ u = M} := by
    ext u
    change (relativeGenerated (N := N) τ u).toStarSubalgebra = M.toStarSubalgebra ↔ _
    constructor
    · intro h
      apply VonNeumannAlgebra.ext
      intro x
      change x ∈ (relativeGenerated (N := N) τ u).toStarSubalgebra ↔ x ∈ M.toStarSubalgebra
      rw [h]
    · exact fun h => congrArg _ h
  refine ⟨he.symm ▸ relativeGeneratingLocus_isGδ τ hNM hsep, ?_⟩
  obtain ⟨C,_,hC,hm⟩ := represented_relative_generation_q129 τ hNM hfactor hdiff hirr hsep
  exact hC.mono hm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.RelativeGeneration_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

/- The full relative-generating locus of the original inclusion,
   together with the single-generation corollary. -/
namespace Generator
open Tracial UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Relative generation for the original concrete
factors and the arbitrary given irreducible inclusion. No ambient separability,
cyclicity, or perturbation hypothesis appears. The entire generating locus is
Gδ and dense, for the metric identified with normalized trace-2 in
`FactorTraceUnitary.dist_eq_trace`. -/
theorem relative_generation_of_II1_separable_predual
    (P S : StarSubalgebra ℂ (H →L[ℂ] H)) (hP : IsII1Factor P) (hS : IsII1Factor S)
    (hPS : P ≤ S)
    (hirr : ∀ c : S,
      (∀ a : P,StarSubalgebra.inclusion hPS a*c=c*StarSubalgebra.inclusion hPS a) →
      ∃ z : ℂ,c=algebraMap ℂ S z)
    (hsep : HasSeparablePredual S) :
    IsGδ {u : FactorTraceUnitary S hS |
      wstar ((P : Set (H →L[ℂ] H)) ∪ {(u.algebra S hS).val})=S} ∧
    Dense {u : FactorTraceUnitary S hS |
      wstar ((P : Set (H →L[ℂ] H)) ∪ {(u.algebra S hS).val})=S} := by
  let hf := hS.factor_smul
  let hu := hS.one_ne_zero
  let K := TraceFreeHilbert hf hS.diffuse hS.finite hu
  let R := traceFreeHilbertClosure hf hS.diffuse hS.finite hu
  let σ := traceFreeHilbertClosureTrace hf hS.diffuse hS.finite hu
  let N := traceFreeRelativeImage hf hS.diffuse hS.finite hu P hP.weaklyClosed
  have hNR : N ≤ R := traceFreeRelativeImage_le hf hS.diffuse hS.finite hu P hP.weaklyClosed
  have hN : IsII1Factor N.toStarSubalgebra :=
    traceFreeRelativeImage_isII1Factor hf hS.diffuse hS.finite hu P hP.weaklyClosed hPS hP
  have hfN : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z,hz⟩ := hN.factor c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  have hirr' : ∀ c : S,
      (∀ a : P,StarSubalgebra.inclusion hPS a*c=c*StarSubalgebra.inclusion hPS a) →
      ∃ z : ℂ,c=z • (1 : S) := by
    intro c hc
    obtain ⟨z,hz⟩ := hirr c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  have hi := traceFreeRelativeImage_irreducible hf hS.diffuse hS.finite hu
    P hP.weaklyClosed hPS hirr'
  have hs := traceOrbit_isSeparable_of_separablePredual_q129 σ
    (traceFreeHilbertClosure_hasSeparablePredual hf hS.diffuse hS.finite hu hsep)
  obtain ⟨hg,hd⟩ := represented_full_relative_generation σ hNR hfN hN.diffuse hi hs
  let f := FactorTraceUnitary.representedHomeomorph S hS
  have he : {u : FactorTraceUnitary S hS |
      wstar ((P : Set (H →L[ℂ] H)) ∪ {(u.algebra S hS).val})=S} =
      f ⁻¹' {v : TraceUnitary σ |
        wstar ((N : Set (K →L[ℂ] K)) ∪ {(v.algebra σ).val})=R.toStarSubalgebra} := by
    ext u
    exact traceFreeRelativeGeneration_iff hf hS.diffuse hS.finite hu P hP.weaklyClosed hPS
      (u.algebra S hS)
  rw [he]
  exact ⟨IsGδ.preimage f.continuous hg, f.isOpenQuotientMap.dense_preimage_iff.mpr hd⟩

end Generator

namespace RelativeGeneration

universe level

/-- The concrete finite diffuse factor hypotheses are the ones used in the trace construction. -/
theorem IsII1Factor.toGenerator {Hilbert : Type level} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℂ Hilbert] [CompleteSpace Hilbert]
    {algebra : StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert)} (factor : IsII1Factor algebra) :
    Generator.IsII1Factor algebra :=
  ⟨factor.nonzero, factor.weaklyClosed, factor.factor, factor.finite, factor.diffuse⟩

/-- The entire relative-generator locus of an irreducible inclusion is dense Gδ in the
normalized trace two-topology on the original, genuine unitaries. -/
theorem main_theorem_oai : MainTarget.{level} := by
  intro Hilbert _ _ _ small large smallFactor largeFactor inclusion irreducible separablePredual
  let smallFactor' := smallFactor.toGenerator
  let largeFactor' := largeFactor.toGenerator
  obtain ⟨gdelta, dense⟩ := Generator.relative_generation_of_II1_separable_predual
    small large smallFactor' largeFactor' inclusion irreducible separablePredual
  refine ⟨Generator.normalizedFactorTrace large largeFactor',
    Generator.normalizedFactorTrace_isNormalizedTrace large largeFactor', ?_⟩
  let : TopologicalSpace (unitary large) :=
    traceTopology large (Generator.normalizedFactorTrace large largeFactor')
  let unitaryHomeomorph := Generator.FactorTraceUnitary.traceHomeomorph large largeFactor'
  have locus_eq : relativeGeneratorLocus small large = unitaryHomeomorph.symm ⁻¹'
      {element : Generator.FactorTraceUnitary large largeFactor' |
        Generator.wstar ((small : Set (Hilbert →L[ℂ] Hilbert)) ∪
          {(element.algebra large largeFactor').val}) = large} := by
    ext element
    rfl
  rw [locus_eq]
  exact ⟨IsGδ.preimage unitaryHomeomorph.symm.continuous gdelta,
    unitaryHomeomorph.symm.isOpenQuotientMap.dense_preimage_iff.mpr dense⟩

end RelativeGeneration

end

end OAI
end

theorem solution.{level} : type_of% @OAI.RelativeGeneration.main_theorem_oai.{level} := @OAI.RelativeGeneration.main_theorem_oai.{level}
