-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:35:15.705569+00:00
-- url     : https://prove2.me/submissions/b2fe20fa-97df-4977-8534-98226ab1369a

import Mathlib
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_exists_exact_residual_iteration_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

theorem quotientMap_surjective : Function.Surjective (quotientMap τ l) := Quotient.mk_surjective

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotientTrace_mul_comm (a b : TracialQuotient τ (ω : Filter ℕ)) :
    quotientTrace τ ω (a*b) = quotientTrace τ ω (b*a) := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      change traceRep τ ω (a*b) = traceRep τ ω (b*a)
      apply tendsto_nhds_unique (traceRep_tendsto τ ω (a*b))
      have ht := traceRep_tendsto τ ω (b*a)
      change Tendsto (fun n => τ.trace (b.val n*a.val n)) _ _ at ht
      change Tendsto (fun n => τ.trace (a.val n*b.val n)) _ _
      simpa only [τ.trace_mul_comm] using ht

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.boundedCompletedUnitary_apply _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.inclusion_inner _root_.OAI.Generator.Tracial.inner_eq_trace _root_.OAI.Generator.Tracial.quotient_norm_one _root_.OAI.Generator.Tracial.quotient_trace_sub _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.trace_add _root_.OAI.Generator.Tracial.trace_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace PartialUnitary

theorem cross_initial {v w : PartialUnitary M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.unitary.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialUnitary M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem difference_square {v w : PartialUnitary M} (h : v ≤ w) :
    star (w.val-v.val)*(w.val-v.val)=w.support.val-v.support.val := by
  simp only [star_sub,sub_mul,mul_sub,w.unitary.initial,v.unitary.initial,
    cross_initial h,cross_initial_rev h,sub_self,sub_zero]

theorem distance_sq (τ : TracialRepresentation M) {v w : PartialUnitary M} (h : v ≤ w) :
    τ.norm₂ (w.val-v.val)^2=(τ.trace w.support.val).re-(τ.trace v.support.val).re := by
  have he := congrArg Complex.re (τ.trace_star_mul (w.val-v.val))
  rw [difference_square h,trace_sub,Complex.sub_re] at he
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using he.symm

theorem support_trace_mono (τ : TracialRepresentation M) {v w : PartialUnitary M} (h : v ≤ w) :
    (τ.trace v.support.val).re ≤ (τ.trace w.support.val).re := by
  have he := distance_sq τ h
  nlinarith [sq_nonneg (τ.norm₂ (w.val-v.val))]

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace PartialUnitary

theorem support_trace_le_one (v : PartialUnitary M) : (τ.trace v.support.val).re ≤ 1 := by
  rw [projection_trace_sq τ _ v.support.property]
  have h := (τ.norm₂_le_norm v.support.val).trans v.support.property.norm_le
  nlinarith [show 0 ≤ τ.norm₂ v.support.val from norm_nonneg _]

theorem monotone_cauchy (a : ℕ → PartialUnitary M) (ha : Monotone a) :
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

/-- Closedness of actual partial unitaries in the operator norm unit ball
for L2 convergence. -/
theorem of_L2_limit (a : ℕ → PartialUnitary M) (b : M.toStarSubalgebra)
    (hb : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0)) :
    ∃ v : PartialUnitary M, v.val=b := by
  let p : M.toStarSubalgebra := star b*b
  have hp : Tendsto (fun n => τ.norm₂ ((a n).support.val-p)) atTop (𝓝 0) := by
    have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
      (star b) b 1 (fun n => (a n).unitary.adjoint.norm_le_one)
      (norm₂_limit_star τ _ _ hb) hb
    simpa only [(a _).unitary.initial] using ht
  have hfinal : b*star b=p := by
    have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun n => star (a n).val)
      b (star b) 1 (fun n => (a n).unitary.norm_le_one) hb (norm₂_limit_star τ _ _ hb)
    have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-b*star b)) atTop (𝓝 0) := by
      simpa only [(a _).unitary.final] using ht
    exact norm₂_limit_unique τ _ ht' hp
  have hproj : IsStarProjection p := by
    constructor
    · have ht := norm₂_limit_mul τ (fun n => (a n).support.val) (fun n => (a n).support.val)
        p p 1 (fun n => (a n).support.property.norm_le) hp hp
      have ht' : Tendsto (fun n => τ.norm₂ ((a n).support.val-p*p)) atTop (𝓝 0) := by
        simpa only [(a _).support.property.isIdempotentElem.eq] using ht
      exact norm₂_limit_unique τ _ ht' hp
    · change star (star b*b)=star b*b
      simp only [star_mul,star_star]
  exact ⟨⟨⟨p,hproj⟩,⟨b,rfl,hfinal⟩⟩,rfl⟩

/-- A bounded L2 limit retains every eventually fixed extension. -/
theorem le_of_eventually_le_limit (a : ℕ → PartialUnitary M) (v w : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ᶠ n in atTop, w ≤ a n) : w ≤ v := by
  have ht := norm₂_limit_mul τ (fun n => (a n).val) (fun _ => w.support.val)
    v.val w.support.val 1 (fun n => (a n).unitary.norm_le_one) hv
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
  have hc : Tendsto (fun n => τ.norm₂ ((a n).val*w.support.val-w.val)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw] with n hn
    rw [show (a n).val*w.support.val=w.val from hn,sub_self,τ.norm₂_zero]
  exact norm₂_limit_unique τ _ ht hc

theorem monotone_limit (a : ℕ → PartialUnitary M) (ha : Monotone a) :
    ∃ v : PartialUnitary M, (∀ n, a n ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  obtain ⟨ξ,hξ⟩ := cauchySeq_tendsto_of_complete (monotone_cauchy τ a ha)
  obtain ⟨b,hb,hbξ⟩ := bounded_trace_limit τ (fun n => (a n).val) 1 (by norm_num)
    (fun n => (a n).unitary.norm_le_one) ξ hξ
  have ht : Tendsto (fun n => τ.norm₂ ((a n).val-b)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ b).mp
    simpa only [hbξ] using hξ
  obtain ⟨v,hv⟩ := of_L2_limit τ a b ht
  rw [← hv] at ht
  refine ⟨v,fun n => ?_,ht⟩
  apply le_of_eventually_le_limit τ a v (a n) ht
  exact (eventually_ge_atTop n).mono (fun m hm => ha hm)

/-! Every nonempty chain of actual partial unitaries has an upper bound which
is an L2 limit of a sequence from the chain. This is the analytic chain
construction underlying the error-constrained Zorn argument. -/

end PartialUnitary

end

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

include hPM
theorem inclusion_mem_of_bounded_L2_limit (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, ‖a n‖ ≤ C)
    (hmem : ∀ n, (a n).val ∈ P)
    (hb : Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0)) : b.val ∈ P := by
  let aP : ℕ → P.toStarSubalgebra := fun n => ⟨(a n).val,hmem n⟩
  have ht := (tendsto_vector_iff_norm₂ τ atTop a b).mpr hb
  obtain ⟨c,hc,he⟩ := bounded_trace_limit (restrictedTrace τ hPM) aP C hC ha
    ((b : H →L[ℂ] H) τ.vector) ht
  have hcb : coordinateInclusion hPM c=b := by
    apply sub_eq_zero.mp
    apply τ.separating
    change (c : H →L[ℂ] H) τ.vector-(b : H →L[ℂ] H) τ.vector=0
    exact sub_eq_zero.mpr he
  have hv := congrArg Subtype.val hcb
  rw [← hv]
  exact c.property

end

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem boundedPartialSupport_projection (v : ℕ → PartialUnitary M) :
    IsStarProjection (boundedPartialSupport v) := by
  constructor
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isIdempotentElem
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isSelfAdjoint

theorem boundedPartialUnitary_initial (v : ℕ → PartialUnitary M) :
    star (boundedPartialUnitary v)*boundedPartialUnitary v = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.initial

theorem boundedPartialUnitary_final (v : ℕ → PartialUnitary M) :
    boundedPartialUnitary v*star (boundedPartialUnitary v) = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.final

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.TraceUnitary.dist_eq _root_.OAI.Generator.Tracial.constantQuotient_inner _root_.OAI.Generator.Tracial.constantQuotient_norm _root_.OAI.Generator.Tracial.constantQuotient_trace _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.Generator.Tracial.sequenceInclusion_apply _root_.OAI.Generator.Tracial.traceCyclicOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual trace Hilbert completion of the bounded-sequence tracial quotient.
The vector-trace representation is explicit data; its existence for an arbitrary
factor is not asserted here. No free-independence premise occurs. -/
open Filter
open scoped Topology ComplexConjugate

/-! Centering actual bounded representatives changes no centered quotient
class. Every such class is a nonzero scalar multiple of a coordinatewise
centered contraction representative. -/
open Filter
open scoped Topology

/-! Trace Cauchy–Schwarz and unitary invariance on the tracial quotient. -/
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem quotient_norm_star (a : Q τ ω) : ‖star a‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_eq_trace, inner_eq_trace, star_star, quotientTrace_mul_comm τ ω a (star a)]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

theorem algebraWordCore_endpoints {A : Type*} [Monoid A] [Star A]
    (v : A) (x : ℕ → A) (last : Option ℕ) (s : Bool) (xs : List (Bool × ℕ)) :
    algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++
      [(s,optionalCoefficient x last)])=algebraWordCore v x s xs*optionalCoefficient x last := by
  induction xs with
  | nil => simp [algebraPatchingWord,algebraWordCore]
  | cons a xs ih => simp [algebraPatchingWord,algebraWordCore,ih,mul_assoc]

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

theorem quotient_norm_tendsto (a : Bounded M) :
    Tendsto (fun n => τ.norm₂ (a.val n)) (ω : Filter ℕ)
      (𝓝 ‖quotientMap τ (ω : Filter ℕ) a‖) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_eq_trace]
  exact norm₂_tendsto τ ω a

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.boundedCompletedUnitary_apply _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual residual projections, null-set masking, and coordinatewise
orthogonal partial-unitary patching. -/

/-! An actual positive residual support increment with exact ordered moments
for arbitrary countably many centered compressed quotient coefficients. -/
open Filter

/-! Faithful-trace completion criterion and the exact quarter-increment
residual estimate for actual orthogonal coordinate patches. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_projection_eq_zero_of_trace_re (p : Q τ ω) (hp : IsStarProjection p)
    (ht : (quotientTrace τ ω p).re=0) : p=0 := by
  have h : ‖p‖^2=0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_eq_trace,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
    exact ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h)

theorem quotient_unitary_of_zero_residual (v : ℕ → PartialUnitary M)
    (ht : (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))).re=0) :
    star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))*
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)=1 ∧
    quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)*
      star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))=1 := by
  have hp := ((boundedPartialSupport_projection v).one_sub).map (quotientStarAlgHom τ (ω : Filter ℕ))
  have hz := quotient_projection_eq_zero_of_trace_re τ ω _ hp ht
  change quotientMap τ (ω : Filter ℕ) (1-boundedPartialSupport v)=0 at hz
  rw [map_sub,map_one,sub_eq_zero] at hz
  constructor
  · rw [← quotientMap_star,← map_mul,boundedPartialUnitary_initial]
    exact hz.symm
  · rw [← quotientMap_star,← map_mul,boundedPartialUnitary_final]
    exact hz.symm

end

/-! Actual moment-preserving residual extensions, retaining coordinate partial
unitaries in N and the quantitative decrease of residual support. -/

/-! Iteration of actual moment-preserving partial-unitary extensions. Every
stage retains its coordinate representatives and a geometric residual bound. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem quotientResidualTrace_nonneg (ω : Ultrafilter ℕ) (v : ℕ → PartialUnitary M) :
    0 ≤ quotientResidualTrace τ ω v := by
  have hp := ((boundedPartialSupport_projection v).one_sub).map
    (quotientStarAlgHom τ (ω : Filter ℕ))
  change IsStarProjection (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v)) at hp
  have hh := trace_square_nonneg τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialResidual v))
  rwa [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] at hh

end

/-! Coordinatewise monotone upper bounds and quantitative convergence in the
actual quotient two-norm. No completeness of the quotient is assumed. -/
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_trace_sub' (a b : Q τ ω) :
    quotientTrace τ ω (a-b)=quotientTrace τ ω a-quotientTrace τ ω b :=
  (traceLinear τ ω).map_sub a b

theorem quotientResidualTrace_eq (v : ℕ → PartialUnitary M) :
    quotientResidualTrace τ ω v =
      1-(quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re := by
  simp only [quotientResidualTrace,boundedPartialResidual,map_sub,map_one,
    quotient_trace_sub',quotientTrace_one,Complex.sub_re,Complex.one_re]

theorem quotient_partial_distance_sq (v w : ℕ → PartialUnitary M) (h : ∀ j,v j ≤ w j) :
    ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)‖^2=
      quotientResidualTrace τ ω v-quotientResidualTrace τ ω w := by
  have he : star (boundedPartialUnitary w-boundedPartialUnitary v)*
      (boundedPartialUnitary w-boundedPartialUnitary v)=boundedPartialSupport w-boundedPartialSupport v := by
    apply Subtype.ext
    funext j
    exact PartialUnitary.difference_square (h j)
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_eq_trace,← map_sub,← quotientMap_star,← map_mul,he,
    map_sub,quotient_trace_sub']
  change (quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport w))-
    quotientTrace τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialSupport v))).re = _
  rw [Complex.sub_re,quotientResidualTrace_eq,quotientResidualTrace_eq]
  ring

theorem quotientResidualTrace_antitone (v w : ℕ → PartialUnitary M) (h : ∀ j,v j ≤ w j) :
    quotientResidualTrace τ ω w ≤ quotientResidualTrace τ ω v := by
  have he := quotient_partial_distance_sq τ ω v w h
  nlinarith [sq_nonneg ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary w)-
    quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)‖]

include τ in
theorem exists_coordinate_monotone_upper (hNM : N ≤ M)
    (a : ℕ → ℕ → PartialUnitary M) (ha : ∀ j,Monotone (fun n => a n j))
    (hN : ∀ n j,(a n j).val.val ∈ N) :
    ∃ u : ℕ → PartialUnitary M,(∀ j,(u j).val.val ∈ N) ∧ ∀ n j,a n j ≤ u j := by
  choose u hu hlim using fun j => PartialUnitary.monotone_limit τ (fun n => a n j) (ha j)
  refine ⟨u,fun j => ?_,fun n j => hu j n⟩
  exact inclusion_mem_of_bounded_L2_limit τ hNM (fun n => (a n j).val) (u j).val
    1 zero_le_one (fun n => (a n j).unitary.norm_le_one) (fun n => hN n j) (hlim j)

theorem quotient_geometric_upper_completion
    (a : ℕ → ℕ → PartialUnitary M) (u : ℕ → PartialUnitary M)
    (hu : ∀ n j,a n j ≤ u j) (r : ℝ)
    (hr : ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*r) :
    quotientResidualTrace τ ω u=0 ∧
    Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop
      (𝓝 (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))) := by
  have ht : Tendsto (fun n : ℕ => (3/4 : ℝ)^n*r) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3/4) (by norm_num : (3/4 : ℝ) < 1)).mul_const r
  have hz : quotientResidualTrace τ ω u=0 := by
    apply le_antisymm _ (quotientResidualTrace_nonneg τ ω u)
    apply ge_of_tendsto ht
    exact Eventually.of_forall (fun n =>
      (quotientResidualTrace_antitone τ ω (a n) u (hu n)).trans (hr n))
  refine ⟨hz,?_⟩
  have hs : Tendsto (fun n => ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _ ht
    intro n
    rw [quotient_partial_distance_sq τ ω (a n) u (hu n),hz,sub_zero]
    exact hr n
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn : Tendsto (fun n => ‖quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)-
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs.sqrt
  exact hn.congr (fun n => norm_sub_rev _ _)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_HaarIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.boundedCompletedUnitary_apply _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Two-norm continuity of ordered moments along uniformly operator-bounded
representatives. No topological-ring structure on the two-norm quotient is used. -/
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem quotient_bounded_mul_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖quotientMap τ (ω : Filter ℕ) a*b‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (a*b)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    exact Eventually.of_forall (fun j => (τ.norm₂_mul_le (a.val j) (b.val j)).trans
      (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)))

theorem quotient_mul_bounded_norm (a : Bounded M) (C : ℝ) (ha : ∀ j,‖a.val j‖ ≤ C)
    (b : Q τ ω) : ‖b*quotientMap τ (ω : Filter ℕ) a‖ ≤ C*‖b‖ := by
  induction b using Quotient.inductionOn with
  | h b =>
    have hp := quotient_norm_tendsto τ ω (b*a)
    have hb := (quotient_norm_tendsto τ ω b).const_mul C
    rw [map_mul] at hp
    apply le_of_tendsto_of_tendsto hp hb
    apply Eventually.of_forall
    intro j
    calc τ.norm₂ (b.val j*a.val j) ≤ τ.norm₂ (b.val j)*‖a.val j‖ := τ.norm₂_mul_le_right _ _
         _ ≤ τ.norm₂ (b.val j)*C := mul_le_mul_of_nonneg_left (ha j) (norm_nonneg _)
         _ = C*τ.norm₂ (b.val j) := mul_comm _ _

theorem quotient_fixed_right_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => a n*b) atTop (𝓝 (v*b)) := by
  obtain ⟨b',hb⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (tendsto_iff_norm_sub_tendsto_zero.mp ha).const_mul C
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero] using ht)
  intro n
  rw [← sub_mul,← hb]
  exact quotient_mul_bounded_norm τ ω b' C hbound (a n-v)

theorem quotient_bounded_mul_tendsto (a : ℕ → Bounded M) (C : ℝ)
    (hC : ∀ n j,‖(a n).val j‖ ≤ C) (v : Q τ ω) (b : ℕ → Q τ ω) (w : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)) atTop (𝓝 v))
    (hb : Tendsto b atTop (𝓝 w)) :
    Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (a n)*b n) atTop (𝓝 (v*w)) := by
  have ht1 := (tendsto_iff_norm_sub_tendsto_zero.mp hb).const_mul C
  have ht2 := tendsto_iff_norm_sub_tendsto_zero.mp (quotient_fixed_right_tendsto τ ω w _ v ha)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa only [mul_zero,zero_add] using ht1.add ht2)
  intro n
  have he : quotientMap τ (ω : Filter ℕ) (a n)*b n-v*w=
      quotientMap τ (ω : Filter ℕ) (a n)*(b n-w)+
        (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w) := by rw [mul_sub,sub_add_sub_cancel]
  rw [he]
  exact (norm_add_le (quotientMap τ (ω : Filter ℕ) (a n)*(b n-w))
    (quotientMap τ (ω : Filter ℕ) (a n)*w-v*w)).trans
      (add_le_add (quotient_bounded_mul_norm τ ω (a n) C (hC n) (b n-w)) le_rfl)

theorem quotient_fixed_left_tendsto (b : Q τ ω) (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => b*a n) atTop (𝓝 (b*v)) := by
  obtain ⟨b',rfl⟩ := quotientMap_surjective τ (ω : Filter ℕ) b
  obtain ⟨C,_,hbound⟩ := b'.property
  exact quotient_bounded_mul_tendsto τ ω (fun _ => b') C (fun _ => hbound) _ a v tendsto_const_nhds ha

theorem quotient_star_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) : Tendsto (fun n => star (a n)) atTop (𝓝 (star v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [← star_sub,quotient_norm_star] using tendsto_iff_norm_sub_tendsto_zero.mp ha

theorem quotient_partial_signed_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (s : Bool) : Tendsto (fun n => quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) s)) atTop (𝓝 (algebraSignedLetter v s)) := by
  cases s with
  | false => exact ha
  | true => simpa only [algebraSignedLetter,↓reduceIte,quotientMap_star] using quotient_star_tendsto τ ω _ v ha

theorem quotient_partial_core_tendsto (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω) (s : Bool) (xs : List (Bool × ℕ)) :
    Tendsto (fun n => algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      atTop (𝓝 (algebraWordCore v x s xs)) := by
  have hsign (t : Bool) := quotient_partial_signed_tendsto τ ω a v ha t
  have he (n : ℕ) (t : Bool) : quotientMap τ (ω : Filter ℕ)
      (algebraSignedLetter (boundedPartialUnitary (a n)) t)=
      algebraSignedLetter (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) t := by
    cases t <;> simp only [algebraSignedLetter,Bool.false_eq_true,↓reduceIte,quotientMap_star]
  induction xs with
  | nil => simpa only [algebraWordCore,he] using hsign s
  | cons t xs ih =>
    have hbound : ∀ n j,‖(algebraSignedLetter (boundedPartialUnitary (a n)) t.1).val j‖ ≤ 1 := by
      intro n j
      cases t.1 with
      | false =>
        change ‖(a n j).val‖ ≤ 1
        exact (a n j).unitary.norm_le_one
      | true =>
        change ‖star (a n j).val‖ ≤ 1
        exact (a n j).unitary.adjoint.norm_le_one
    have hh := quotient_bounded_mul_tendsto τ ω
      (fun n => algebraSignedLetter (boundedPartialUnitary (a n)) t.1) 1 hbound _
      (fun n => x t.2*algebraWordCore (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x s xs)
      _ (hsign t.1) (quotient_fixed_left_tendsto τ ω (x t.2) _ _ ih)
    simpa only [he,algebraWordCore,mul_assoc] using hh

theorem quotient_trace_tendsto (a : ℕ → Q τ ω) (v : Q τ ω)
    (ha : Tendsto a atTop (𝓝 v)) :
    Tendsto (fun n => quotientTrace τ ω (a n)) atTop (𝓝 (quotientTrace τ ω v)) := by
  have he (b : Q τ ω) : quotientTrace τ ω b=inner ℂ (1 : Q τ ω) b := by
    rw [inner_eq_trace,star_one,one_mul]
  simp only [he]
  exact tendsto_const_nhds.inner ha

theorem exactOrderedMoments_partial_limit (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω)
    (hm : ∀ n,ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) :
    ExactOrderedMoments τ ω v x := by
  intro first last xs s
  have ht := quotient_partial_core_tendsto τ ω a v ha x s xs
  have ht' := quotient_trace_tendsto τ ω _ _ (quotient_fixed_left_tendsto τ ω
    (optionalCoefficient x first) _ _ (quotient_fixed_right_tendsto τ ω (optionalCoefficient x last) _ _ ht))
  rw [algebraWordCore_endpoints]
  apply tendsto_nhds_unique ht'
  apply tendsto_const_nhds.congr
  intro n
  have hh := hm n first last xs s
  rw [algebraWordCore_endpoints] at hh
  exact hh.symm

end

/-! A genuine unitary in the included quotient with every signed ordered
moment zero. This statement does not assert all Haar powers or freeness. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exactOrderedMoments_zero (ω : Ultrafilter ℕ) (x : ℕ → Q τ ω) :
    ExactOrderedMoments τ ω 0 x := by
  intro first last xs s
  have hz : algebraPatchingWord (0 : Q τ ω)
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])=0 := by
    cases xs <;> simp [algebraPatchingWord,algebraSignedLetter]
  rw [hz,mul_zero]
  exact (traceLinear τ ω).map_zero

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

theorem exists_full_support_ordered_independence
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧
      star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))*
        quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)=1 ∧
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)*
        star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))=1 ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x := by
  let v : ℕ → PartialUnitary M := fun _ => zeroPartialUnitary
  have hv : ∀ j,(v j).val.val ∈ N := fun _ => N.zero_mem
  have hz : quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)=0 := by
    change quotientMap τ (ω : Filter ℕ) 0=0
    exact map_zero _
  have hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x := by
    rw [hz]
    exact exactOrderedMoments_zero τ ω x
  obtain ⟨a,ha⟩ := exists_exact_residual_iteration_q129 (H := H) (N := N) (M := M)
    τ hNM hfactor hdiff hirr hsep ω hω v hv x hx hm
  obtain ⟨u,hu⟩ := exists_coordinate_monotone_upper τ hNM a ha.2.2.1 ha.2.1
  have hc := quotient_geometric_upper_completion τ ω a u hu.2
    (quotientResidualTrace τ ω v) ha.2.2.2.2
  have hunit := quotient_unitary_of_zero_residual τ ω u hc.1
  exact ⟨u,hu.1,hunit.1,hunit.2,
    exactOrderedMoments_partial_limit τ ω a _ hc.2 x ha.2.2.2.1⟩

end

/-! Two actual applications of ordered independence produce a unitary with
all reduced signed moments, including runs of same-sign letters. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete each supported partial unitary by the identity on its orthogonal
complement. If the quotient support is one, the quotient value is unchanged. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem PartialUnitary.completed_unitary (v : PartialUnitary M) :
    v.completed ∈ _root_.unitary M.toStarSubalgebra := by
  have hp := v.support.property.isIdempotentElem.eq
  have hs := v.support.property.isSelfAdjoint.star_eq
  have hi := v.unitary.initial
  have hf := v.unitary.final
  have hleft := v.unitary.support_mul
  have hright := v.unitary.mul_support
  have hleft' := v.unitary.adjoint.support_mul
  have hright' := v.unitary.adjoint.mul_support
  dsimp only [CornerUnitary.adjoint] at hleft' hright'
  constructor <;>
    simp only [PartialUnitary.completed,star_add,star_sub,star_one,hs,add_mul,mul_add,
      sub_mul,mul_sub,one_mul,mul_one,hi,hf,hleft,hright,hleft',hright',hp] <;> abel

theorem PartialUnitary.completed_mem (v : PartialUnitary M)
    (hv : v.val.val ∈ N) : v.completed.val ∈ N := by
  have hp : v.support.val.val ∈ N := by
    rw [← v.unitary.initial]
    have hstar : star v.val.val ∈ N := star_mem hv
    exact N.mul_mem hstar hv
  exact N.add_mem hv (N.sub_mem N.one_mem hp)

theorem boundedCompletedUnitary_unitary (u : ℕ → PartialUnitary M) (j : ℕ) :
    (boundedCompletedUnitary u).val j ∈ _root_.unitary M.toStarSubalgebra :=
  (u j).completed_unitary

theorem quotient_completed_eq (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
    (u : ℕ → PartialUnitary M)
    (hi : star (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u))*
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)=1) :
    quotientMap τ (ω : Filter ℕ) (boundedCompletedUnitary u)=
      quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u) := by
  have hp : quotientMap τ (ω : Filter ℕ) (boundedPartialSupport u)=1 := by
    rw [← boundedPartialUnitary_initial,map_mul,quotientMap_star]
    exact hi
  let q := quotientMap τ (ω : Filter ℕ)
  have hs : q (1-boundedPartialSupport u)=0 :=
    (map_sub q 1 (boundedPartialSupport u)).trans
      ((congrArg₂ (fun a b => a-b) (map_one q) hp).trans (sub_self _))
  exact (map_add q (boundedPartialUnitary u) (1-boundedPartialSupport u)).trans
    ((congrArg (fun b => q (boundedPartialUnitary u)+b) hs).trans (add_zero _))

end

/-! Ordered independence with actual coordinate unitaries in the included
algebra, obtained by completing the constructed partial-unitary coordinates. -/
section
open UltrapowerBridge Filter
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

theorem exists_coordinate_ordered_unitary_q129_oai
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0) :
    ∃ b : Bounded M,
      (∀ j,b.val j ∈ unitary M.toStarSubalgebra ∧ (b.val j).val ∈ N) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) b) x := by
  obtain ⟨u,hu,hi,hf,hm⟩ := exists_full_support_ordered_independence τ hNM
    hfactor hdiff hirr hsep ω hω x hx
  refine ⟨boundedCompletedUnitary u,?_,?_⟩
  · intro j
    exact ⟨boundedCompletedUnitary_unitary u j,(u j).completed_mem (hu j)⟩
  · rwa [quotient_completed_eq τ ω u hi]

end

/-! Two coordinate-unitary witnesses produce the reduced-moment Haar precursor
while retaining actual unitary coordinates in the included algebra. -/

/-! Full integer endpoint moments and an actual included coordinate-unitary
Haar witness, before imposing an operator topology on generated algebras. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129_oai.{u_1} := @OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129_oai.{u_1}
