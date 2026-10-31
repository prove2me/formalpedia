-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_supported_corner_partial_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:18:16.958447+00:00
-- url     : https://prove2.me/submissions/2bbafdb9-1164-425a-8b7d-49247ddb091c

import Mathlib
import Definitions.Def_OAIQ11Fg012
import Theorems.Thm_OAI_Generator_Tracial_exists_strict_admissible_unit_patch
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
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem eq_of_le_of_trace_eq {v w : PartialUnitary M} (h : v ≤ w)
    (ht : (τ.trace v.support.val).re=(τ.trace w.support.val).re) : v=w := by
  have he := distance_sq τ h
  rw [ht,sub_self] at he
  have hz := (τ.norm₂_eq_zero_iff _).mp (sq_eq_zero_iff.mp he)
  exact ext (sub_eq_zero.mp hz).symm

theorem support_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => τ.norm₂ ((a n).support.val-v.support.val)) atTop (𝓝 0) := by
  have ht := norm₂_limit_mul τ (fun n => star (a n).val) (fun n => (a n).val)
    (star v.val) v.val 1 (fun n => (a n).unitary.adjoint.norm_le_one)
    (norm₂_limit_star τ _ _ hv) hv
  simpa only [(a _).unitary.initial,v.unitary.initial] using ht

theorem support_trace_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0)) :
    Tendsto (fun n => (τ.trace (a n).support.val).re) atTop (𝓝 (τ.trace v.support.val).re) :=
  (Complex.continuous_re.tendsto _).comp (norm₂_limit_trace τ _ _ (support_limit τ a v hv))

theorem limit_le_of_le (a : ℕ → PartialUnitary M) (v w : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (hw : ∀ n, a n ≤ w) : v ≤ w := by
  have ht := norm₂_limit_mul τ (fun _ => w.val) (fun n => (a n).support.val)
    w.val v.support.val 1 (fun _ => w.unitary.norm_le_one)
    (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds)
    (support_limit τ a v hv)
  have he : (fun n => w.val*(a n).support.val)=(fun n => (a n).val) := funext hw
  simp only [show ∀ n, w.val*(a n).support.val=(a n).val from hw] at ht
  exact norm₂_limit_unique τ _ ht hv

/-- A nonempty chain has a sequential L2 upper bound; no countability of the
chain and no cyclicity of the trace vector are assumed. -/
theorem chain_limit (c : Set (PartialUnitary M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ (a : ℕ → PartialUnitary M) (v : PartialUnitary M),
      (∀ n, a n ∈ c) ∧ Monotone a ∧ (∀ w ∈ c, w ≤ v) ∧
      Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0) := by
  classical
  let t : PartialUnitary M → ℝ := fun v => (τ.trace v.support.val).re
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
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem signedLetter_norm (v : M.toStarSubalgebra) (s : Bool) :
    ‖signedLetter v s‖=‖v‖ := by
  cases s
  · rfl
  · change ‖star (v : H →L[ℂ] H)‖=‖(v : H →L[ℂ] H)‖
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint.norm_map _

theorem signedLetter_sub (v w : M.toStarSubalgebra) (s : Bool) :
    signedLetter v s-signedLetter w s=signedLetter (v-w) s := by
  cases s <;> simp [signedLetter,star_sub]

theorem signedLetter_norm₂ (τ : TracialRepresentation M) (v : M.toStarSubalgebra) (s : Bool) :
    τ.norm₂ (signedLetter v s)=τ.norm₂ v := by cases s <;> simp [signedLetter,τ.norm₂_star]

theorem patchingWord_norm_le_one (v : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    ‖patchingWord v xs‖ ≤ 1 := by
  induction xs with
  | nil => exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht := ih (fun b hb => hx b (by simp [hb]))
    have hs : ‖signedLetter v a.1*a.2‖ ≤ 1 :=
      (norm_mul_le _ _).trans ((mul_le_mul (by rw [signedLetter_norm]; exact hv) ha
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
    exact (norm_mul_le _ _).trans ((mul_le_mul hs ht (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))

theorem patchingWord_norm₂_sub_le (τ : TracialRepresentation M)
    (v w : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    τ.norm₂ (patchingWord v xs-patchingWord w xs) ≤ xs.length*τ.norm₂ (v-w) := by
  induction xs with
  | nil => simp [patchingWord]
  | cons a xs ih =>
    have ha := hx a (by simp)
    have htail : ∀ b ∈ xs, ‖b.2‖ ≤ 1 := fun b hb => hx b (by simp [hb])
    have he : patchingWord v (a::xs)-patchingWord w (a::xs) =
        ((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs+
        (signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs) := by
      simp [patchingWord,sub_mul,mul_sub]
    have hfirst : τ.norm₂ (((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs) ≤
        τ.norm₂ (v-w) := by
      have h1 := τ.norm₂_mul_le_right ((signedLetter v a.1-signedLetter w a.1)*a.2) (patchingWord v xs)
      have h2 := τ.norm₂_mul_le_right (signedLetter v a.1-signedLetter w a.1) a.2
      rw [signedLetter_sub,signedLetter_norm₂] at h2
      calc _ ≤ τ.norm₂ ((signedLetter v a.1-signedLetter w a.1)*a.2) :=
             h1.trans (mul_le_of_le_one_right (norm_nonneg _) (patchingWord_norm_le_one v hv xs htail))
           _ ≤ τ.norm₂ (v-w) := by
             rw [signedLetter_sub]
             exact h2.trans (mul_le_of_le_one_right (norm_nonneg _) ha)
    have hs : ‖signedLetter w a.1*a.2‖ ≤ 1 := by
      calc _ ≤ ‖signedLetter w a.1‖*‖a.2‖ := norm_mul_le _ _
           _ ≤ 1 := by rw [signedLetter_norm]; nlinarith [norm_nonneg w,norm_nonneg a.2]
    have hsecond : τ.norm₂ ((signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs)) ≤
        xs.length*τ.norm₂ (v-w) := by
      exact ((τ.norm₂_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hs)).trans (ih htail)
    rw [he]
    have hsum := τ.norm₂_add_le
      (((signedLetter v a.1-signedLetter w a.1)*a.2)*patchingWord v xs)
      ((signedLetter w a.1*a.2)*(patchingWord v xs-patchingWord w xs))
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- Uniform trace continuity of every actual signed mixed word. -/
theorem mixed_trace_sub_le (τ : TracialRepresentation M)
    (v w x₀ : M.toStarSubalgebra) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    ‖τ.trace (x₀*patchingWord v xs)-τ.trace (x₀*patchingWord w xs)‖ ≤
      xs.length*τ.norm₂ (v-w) := by
  rw [← trace_sub,← mul_sub]
  exact ((τ.norm_trace_le_norm₂ _).trans ((τ.norm₂_mul_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) h₀))).trans
    (patchingWord_norm₂_sub_le τ v w hv hw xs hx)

end

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingCoefficients_norm (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (xs : List (Bool × M.toStarSubalgebra))
    (hx : patchingCoefficients F xs) : ∀ a ∈ xs, ‖a.2‖ ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil =>
      have ha : ‖a.2‖ ≤ 1 := by
        rcases hx with h | h
        · exact hF _ h
        · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
      simpa using ha
    | cons b xs =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hF _ hx.1
      · exact ih hx.2 c hc

theorem mixed_trace_limit (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (hv : Tendsto (fun n => τ.norm₂ ((a n).val-v.val)) atTop (𝓝 0))
    (x₀ : M.toStarSubalgebra) (h₀ : ‖x₀‖ ≤ 1)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs, ‖a.2‖ ≤ 1) :
    Tendsto (fun n => τ.trace (x₀*patchingWord (a n).val xs)) atTop
      (𝓝 (τ.trace (x₀*patchingWord v.val xs))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => mixed_trace_sub_le τ _ _ _ (a n).unitary.norm_le_one v.unitary.norm_le_one h₀ xs hx)
  simpa using hv.const_mul (xs.length : ℝ)

theorem patchingAdmissible_limit (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ)
    (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (ha : ∀ i, PatchingAdmissible τ f F n ε (a i))
    (hv : Tendsto (fun i => τ.norm₂ ((a i).val-v.val)) atTop (𝓝 0)) :
    PatchingAdmissible τ f F n ε v := by
  have hp := PartialUnitary.support_limit τ a v hv
  have hsupport : v.support ≤ f := by
    have ht := norm₂_limit_mul τ (fun _ => f.val) (fun i => (a i).support.val)
      f.val v.support.val 1 (fun _ => f.property.norm_le)
      (by simp only [sub_self,TracialRepresentation.norm₂_zero]; exact tendsto_const_nhds) hp
    have he : (fun i => f.val*(a i).support.val)=(fun i => (a i).support.val) :=
      funext (fun i => (ha i).1)
    simp only [show ∀ i, f.val*(a i).support.val=(a i).support.val from fun i => (ha i).1] at ht
    exact norm₂_limit_unique τ _ ht hp
  refine ⟨hsupport,fun x₀ hx₀ xs hlen hn hx => ?_⟩
  have h₀ : ‖x₀‖ ≤ 1 := by
    rcases hx₀ with h | h
    · exact hF _ h
    · rw [Set.mem_singleton_iff.mp h]; exact (IsStarProjection.one (M.toStarSubalgebra)).norm_le
  have ht := (mixed_trace_limit τ a v hv x₀ h₀ xs (patchingCoefficients_norm F hF xs hx)).norm
  have hr := (PartialUnitary.support_trace_limit τ a v hv).const_mul (ε xs.length)
  exact le_of_tendsto_of_tendsto ht hr (Eventually.of_forall (fun i => (ha i).2 x₀ hx₀ xs hlen hn hx))

theorem patchingAdmissible_zero (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (n : ℕ) (ε : ℕ → ℝ) : PatchingAdmissible τ f F n ε zeroPartialUnitary := by
  constructor
  · change f.val*0=0; exact mul_zero _
  · intro x₀ hx₀ xs hlen hn hx
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hs : signedLetter (0 : M.toStarSubalgebra) a.1=0 := by
        cases a.1 <;> simp [signedLetter]
      change ‖τ.trace (x₀*(signedLetter 0 a.1*a.2*patchingWord 0 xs))‖ ≤
        ε (xs.length+1)*(τ.trace 0).re
      simp only [hs,zero_mul,mul_zero]
      have ht : τ.trace 0=0 := inner_zero_right _
      rw [ht,norm_zero,Complex.zero_re,mul_zero]

end

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

theorem patchingAdmissibleIn_limit (f : AlgebraProjection M) (F : Set M.toStarSubalgebra)
    (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ)
    (a : ℕ → PartialUnitary M) (v : PartialUnitary M)
    (ha : ∀ i, PatchingAdmissibleIn (P := P) τ f F n ε (a i))
    (hv : Tendsto (fun i => τ.norm₂ ((a i).val-v.val)) atTop (𝓝 0)) :
    PatchingAdmissibleIn (P := P) τ f F n ε v := by
  exact ⟨patchingAdmissible_limit τ f F hF n ε a v (fun i => (ha i).1) hv,
    inclusion_mem_of_bounded_L2_limit τ hPM _ _ 1 (by norm_num)
      (fun i => (a i).unitary.norm_le_one) (fun i => (ha i).2) hv⟩

/-- The actual maximal admissible partial unitary lies in P, with mixed-word
errors measured in the ambient tracial algebra M. No support-growth bound. -/
theorem exists_maximal_patchingAdmissibleIn (f : AlgebraProjection M)
    (F : Set M.toStarSubalgebra) (hF : ∀ x ∈ F, ‖x‖ ≤ 1) (n : ℕ) (ε : ℕ → ℝ) :
    ∃ v : PartialUnitary M, PatchingAdmissibleIn (P := P) τ f F n ε v ∧
      ∀ w : PartialUnitary M, PatchingAdmissibleIn (P := P) τ f F n ε w → v ≤ w → w ≤ v := by
  obtain ⟨v,hv⟩ := zorn_le₀ {v | PatchingAdmissibleIn (P := P) τ f F n ε v} (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨a,v,hac,ham,hav,hlim⟩ := PartialUnitary.chain_limit τ c hchain hne
      exact ⟨v,patchingAdmissibleIn_limit τ hPM f F hF n ε a v (fun i => hc (hac i)) hlim,hav⟩
    · refine ⟨zeroPartialUnitary,⟨patchingAdmissible_zero τ f F n ε,?_⟩,
        fun w hw => (hne ⟨w,hw⟩).elim⟩
      exact P.zero_mem)
  exact ⟨v,hv.1,fun w hw hvw => hv.2 hw hvw⟩

end

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingCoefficients_append_endpoint (F : Set M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) (hx : ∀ a ∈ xs,a.2 ∈ F)
    (a : Bool × M.toStarSubalgebra) (ha : a.2 ∈ F ∪ {1}) :
    patchingCoefficients F (xs ++ [a]) := by
  induction xs with
  | nil => exact ha
  | cons b xs ih =>
    have ht := ih (fun c hc => hx c (by simp [hc]))
    cases xs with
    | nil => exact ⟨hx b (by simp),ht⟩
    | cons c xs => exact ⟨hx b (by simp),ht⟩

end

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingBounds
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact positive tolerance recurrence used in Popa Lemma 3.2. -/
section

theorem patchingTolerance_pos (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    0 < patchingTolerance δ k := by
  induction k with
  | zero => exact hδ
  | succ k ih => exact mul_pos (pow_pos (by norm_num) _) ih

theorem patchingTolerance_four_mul_le (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    4*patchingTolerance δ k ≤ patchingTolerance δ (k+1) := by
  have hp : (4 : ℝ) ≤ 2^(k+2) := by
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := k)
    rw [pow_add]
    norm_num
    nlinarith only [h]
  exact mul_le_mul_of_nonneg_right hp (patchingTolerance_pos δ hδ k).le

theorem patchingTolerance_mono (δ : ℝ) (hδ : 0 < δ) : Monotone (patchingTolerance δ) := by
  apply monotone_nat_of_le_succ
  intro k
  have hp := patchingTolerance_pos δ hδ k
  have hh := patchingTolerance_four_mul_le δ hδ k
  linarith

end

/-! Explicit binary masks for the existing ordered expansion. A true bit is a
patch letter. Occurrences are retained even when their operator values coincide. -/

/-! Mask uniqueness and a deliberately coarse budget that avoids off-by-one
counts: 2^k ordinary budgets plus one exceptional budget fit epsilon_k. -/

/-! Extract actual coefficient segments and fixed one-patch outer factors.
These lemmas apply to the source lists without assuming segment membership. -/

/-! The triangle inequality for the exact noncommutative mask expansion. -/
open UltrapowerBridge

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

/-! Actual centered pNp pinching partitions and local pieces. The corner,
normalized trace, structural properties, and separability are constructed. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
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

/-! A single actual residual patch controls every finite internal word of the
source family. All scalar moment premises are proved from admissibility. -/

/-! Trace estimates for each actual binary-mask term, using the constructed
finite families. No moment estimate or middle-family extraction is assumed. -/

/-! Strict support growth for the actual f=1 admissible set. The single patch
is chosen from the finite coefficient families before any word is tested. -/
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

/-- The maximal-element contradiction now gives support trace strictly greater
than one quarter in the f=1 scalar-commutant setting. -/
theorem exists_large_admissible_partialUnitary
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ v : PartialUnitary M,
      PatchingAdmissibleIn (P := N) τ (identityProjection M) F n (patchingTolerance δ) v ∧
      1/4 < (τ.trace v.support.val).re := by
  obtain ⟨v,hv,hmax⟩ := exists_maximal_patchingAdmissibleIn τ hNM (identityProjection M) F hF n (patchingTolerance δ)
  refine ⟨v,hv,?_⟩
  by_contra h
  obtain ⟨u,hu,hvu,hgrow⟩ := exists_strict_admissible_unit_patch τ hNM hfactor hdiff hirr hsep
    F hF hcenter n δ hδ v hv (by linarith)
  have hh := PartialUnitary.support_trace_mono τ (hmax u hu hvu)
  linarith

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingTolerance_scale (δ : ℝ) (k : ℕ) :
    patchingTolerance δ k=δ*patchingTolerance 1 k := by
  induction k with
  | zero => simp
  | succ k ih => rw [patchingTolerance_succ,patchingTolerance_succ,ih]; ring

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

theorem exists_finite_partial_independence
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : PartialUnitary M,v.val.val ∈ N ∧ 1/4 < (τ.trace v.support.val).re ∧
      ∀ x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1},∀ xs : List (Bool × M.toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ n → patchingCoefficients (F : Set M.toStarSubalgebra) xs →
        ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε := by
  let δ := ε/patchingTolerance 1 n
  have ht := patchingTolerance_pos 1 (by norm_num) n
  have hδ : 0 < δ := div_pos hε ht
  obtain ⟨v,hv,hs⟩ := exists_large_admissible_partialUnitary τ hNM hfactor hdiff hirr hsep
    F hF hcenter n δ hδ
  have he : patchingTolerance δ n=ε := by
    rw [patchingTolerance_scale]
    exact div_mul_cancel₀ ε ht.ne'
  refine ⟨v,hv.2,hs,?_⟩
  intro x₀ hx₀ xs hpos hn hc
  have hh := hv.1.2 x₀ hx₀ xs hpos hn hc
  have hmono := patchingTolerance_mono δ hδ hn
  rw [he] at hmono
  exact hh.trans ((mul_le_of_le_one_right (patchingTolerance_pos δ hδ xs.length).le
    (PartialUnitary.support_trace_le_one τ v)).trans hmono)

end

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem eventually_list_indices (is : List ℕ) : ∀ᶠ j : ℕ in atTop,∀ i ∈ is,i ≤ j := by
  induction is with
  | nil => exact Eventually.of_forall (fun _ => by simp)
  | cons i is ih =>
    filter_upwards [ih,eventually_ge_atTop i] with j hj hi
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hi
    · exact hj a ha

end

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Extension of actual partial unitaries and ordered words from pH.
The empty word maps to p, so word transport retains a final p. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

theorem PartialUnitary.fromRepresentedCorner_support_le
    (v : PartialUnitary (representedCorner p)) : (v.fromRepresentedCorner p).support ≤ p :=
  cornerEmbedding_left p v.support.val

theorem cornerEmbedding_signedLetter (v : (representedCorner p).toStarSubalgebra) (s : Bool) :
    cornerEmbedding p (signedLetter v s)=signedLetter (cornerEmbedding p v) s := by
  cases s with
  | false => rfl
  | true => exact map_star (cornerEmbedding p) v

theorem cornerEmbedding_trace (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    τ.trace (cornerEmbedding p a)=τ.trace p.val*(representedCornerTrace τ p hp).trace a := by
  rw [representedCornerTrace_trace]
  have ht : τ.trace p.val ≠ 0 := by
    intro h
    have := projection_trace_pos τ p.val p.property hp
    simp [h] at this
  exact (mul_div_cancel₀ _ ht).symm

theorem cornerEmbedding_trace_re (τ : TracialRepresentation M) (hp : p.val ≠ 0)
    (a : (representedCorner p).toStarSubalgebra) :
    (τ.trace (cornerEmbedding p a)).re=
      (τ.trace p.val).re*((representedCornerTrace τ p hp).trace a).re := by
  rw [cornerEmbedding_trace p τ hp,projection_trace_real τ p,Complex.mul_re]
  simp

end

/-! Finite partial independence in every nonzero represented subcorner,
with actual ambient support, membership and trace estimates. -/

/-! Ordered-word transport with ambient unit endpoints, and contractive
compression of supported centered coefficients. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (p : AlgebraProjection M)

theorem cornerCompress_norm_le (a : M.toStarSubalgebra) : ‖cornerCompress p a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  change ‖p.val.val (a.val y.val)‖ ≤ ‖a‖*‖y‖
  exact ((p.val.val.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) p.property.norm_le)).trans (a.val.le_opNorm y.val)

theorem cornerCompress_supported (a : M.toStarSubalgebra)
    (hl : p.val*a=a) (hr : a*p.val=a) : cornerEmbedding p (cornerCompress p a)=a := by
  rw [cornerEmbedding_compress,hl,hr]

theorem cornerEmbedding_ordered_tail (v : (representedCorner p).toStarSubalgebra)
    (x : ℕ → (representedCorner p).toStarSubalgebra) (xs : List (Bool × ℕ))
    (s : Bool) (last : Option ℕ) :
    cornerEmbedding p (patchingWord v
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=
    patchingWord (cornerEmbedding p v)
      (xs.map (fun a => (a.1,cornerEmbedding p (x a.2))) ++
        [(s,optionalCoefficient (fun i => cornerEmbedding p (x i)) last)]) := by
  induction xs with
  | nil =>
    cases last <;>
      simp only [List.map_nil,List.nil_append,patchingWord,mul_one,optionalCoefficient,
        map_mul,← cornerEmbedding_signedLetter]
  | cons a xs ih =>
    change cornerEmbedding p (signedLetter v a.1*x a.2*patchingWord v
      (xs.map (fun b => (b.1,x b.2)) ++ [(s,optionalCoefficient x last)])) = _
    exact (map_mul (cornerEmbedding p) (signedLetter v a.1 * x a.2) _).trans
      (congrArg₂ (fun y z : M.toStarSubalgebra => y * z)
        ((map_mul (cornerEmbedding p) (signedLetter v a.1) (x a.2)).trans
          (congrArg (fun y => y * cornerEmbedding p (x a.2))
            (cornerEmbedding_signedLetter p v a.1))) ih)

theorem cornerEmbedding_ordered_moment (v : (representedCorner p).toStarSubalgebra)
    (x : ℕ → (representedCorner p).toStarSubalgebra) (first last : Option ℕ)
    (xs : List (Bool × ℕ)) (s : Bool) :
    cornerEmbedding p (optionalCoefficient x first * patchingWord v
      (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]))=
    optionalCoefficient (fun i => cornerEmbedding p (x i)) first *
      patchingWord (cornerEmbedding p v)
        (xs.map (fun a => (a.1,cornerEmbedding p (x a.2))) ++
          [(s,optionalCoefficient (fun i => cornerEmbedding p (x i)) last)]) := by
  cases first with
  | none => simpa only [optionalCoefficient,one_mul] using
      cornerEmbedding_ordered_tail p v x xs s last
  | some i =>
    rw [map_mul,cornerEmbedding_ordered_tail]
    rfl

end

/-! Diagonal partial independence in genuinely varying Hilbert-space corners.
The result retains an actual ambient partial-unitary sequence. -/
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

theorem exists_varying_corner_partial_independence
    (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
    (hp : ∀ j,(p j).val ≠ 0)
    (x : (j : ℕ) → ℕ → (representedCorner (p j)).toStarSubalgebra)
    (hx : ∀ j i,‖x j i‖ ≤ 1)
    (hc : ∀ j i,τ.trace (cornerEmbedding (p j) (x j i))=0) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
      (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (
          optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) first *
          patchingWord (v j).val
            (xs.map (fun a => (a.1,cornerEmbedding (p j) (x j a.2))) ++
              [(s,optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) last)])))
          atTop (𝓝 0) := by
  classical
  let σ := fun j => representedCornerTrace τ (p j) (hp j)
  let F := fun j => (Finset.range (j+1)).image (x j)
  have hstage (j : ℕ) := exists_finite_partial_independence (σ j)
    (representedSubcorner_le (p j) (hpN j) hNM)
    (representedCorner_factor (restrictedTrace τ hNM)
      (projectionInSubalgebra (p j) (hpN j)) hfactor)
    (representedCorner_diffuse (projectionInSubalgebra (p j) (hpN j)) hdiff)
    (representedCorner_irreducible τ (p j) (hpN j) hNM hirr)
    (representedCorner_separable τ (p j) (hp j) hsep)
    (F j) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact hx j i) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      rw [representedCornerTrace_trace,hc j i,zero_div])
    (j+1) (1/((j : ℝ)+1)) (by positivity)
  choose u hu ht hw using hstage
  let v := fun j => (u j).fromRepresentedCorner (p j)
  refine ⟨v,hu,fun j => (u j).fromRepresentedCorner_support_le (p j),?_,?_⟩
  · intro j
    change (τ.trace (p j).val).re/4 < (τ.trace (cornerEmbedding (p j) (u j).support.val)).re
    rw [cornerEmbedding_trace_re (p j) τ (hp j)]
    have h := mul_lt_mul_of_pos_left (ht j)
      (projection_trace_pos τ (p j).val (p j).property (hp j))
    dsimp [σ] at h
    linarith
  · intro first last xs s
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hopt (i : Option ℕ) : ∀ᶠ j : ℕ in atTop,
        optionalCoefficient (x j) i ∈ (F j : Set _) ∪ {1} := by
      cases i with
      | none => exact Eventually.of_forall (fun _ => Or.inr rfl)
      | some i =>
        filter_upwards [eventually_ge_atTop i] with j hj
        exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩)
    filter_upwards [eventually_list_indices (xs.map Prod.snd),eventually_ge_atTop xs.length,
      hopt first,hopt last] with j hj hlen hfirst hlast
    have he := cornerEmbedding_ordered_moment (p j) (u j).val (x j) first last xs s
    change ‖τ.trace (optionalCoefficient (fun i => cornerEmbedding (p j) (x j i)) first *
      patchingWord (cornerEmbedding (p j) (u j).val) _)‖ ≤ _
    rw [← he,cornerEmbedding_trace (p j) τ (hp j),norm_mul]
    have hb : ‖(σ j).trace (optionalCoefficient (x j) first *
        patchingWord (u j).val (xs.map (fun a => (a.1,x j a.2)) ++
          [(s,optionalCoefficient (x j) last)]))‖ ≤ 1/((j : ℝ)+1) := by
      apply hw j _ hfirst _ (by simp) (by simpa using Nat.add_le_add_right hlen 1)
      apply patchingCoefficients_append_endpoint _ _ ?_ (s,optionalCoefficient (x j) last) hlast
      intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      exact Finset.mem_image.mpr ⟨b.2,Finset.mem_range.mpr (by
        have hh := hj b.2 (List.mem_map.mpr ⟨b,hb,rfl⟩)
        omega),rfl⟩
    have htrace : ‖τ.trace (p j).val‖ ≤ 1 :=
      ((τ.norm_trace_le_norm₂ _).trans (τ.norm₂_le_norm _)).trans (p j).property.norm_le
    exact (mul_le_of_le_one_left (norm_nonneg _) htrace).trans hb

end

/-! Actual coordinate partial-unitary witnesses in supported corners, followed
by exact quotient moments and the ambient quarter-support bound. -/
open Filter
open scoped Topology
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

theorem exists_supported_corner_partial_sequence_oai
    (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
    (hp : ∀ j,(p j).val ≠ 0)
    (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
    (hc : ∀ i j,τ.trace (x i j)=0)
    (hl : ∀ i j,(p j).val*x i j=x i j) (hr : ∀ i j,x i j*(p j).val=x i j) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
      (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (indexedCoefficient x j first *
          patchingWord (v j).val (xs.map (fun a => (a.1,x a.2 j)) ++
            [(s,indexedCoefficient x j last)]))) atTop (𝓝 0) := by
  let y := fun j i => cornerCompress (p j) (x i j)
  have he (j i : ℕ) : cornerEmbedding (p j) (y j i)=x i j :=
    cornerCompress_supported (p j) (x i j) (hl i j) (hr i j)
  obtain ⟨v,hv,hs,ht,hw⟩ := exists_varying_corner_partial_independence τ hNM hfactor hdiff hirr hsep
    p hpN hp y (fun j i => (cornerCompress_norm_le (p j) (x i j)).trans (hx i j))
    (fun j i => by rw [he]; exact hc i j)
  refine ⟨v,hv,hs,ht,?_⟩
  intro first last xs s
  have hh := hw first last xs s
  cases first <;> cases last <;>
    simpa only [he,optionalCoefficient,indexedCoefficient] using hh

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_supported_corner_partial_sequence_oai.{u_1} := @OAI.Generator.Tracial.exists_supported_corner_partial_sequence_oai.{u_1}
