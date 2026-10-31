-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:29:29.612434+00:00
-- url     : https://prove2.me/submissions/a1451eac-8c13-41fc-a9f3-78f41b2ecb7a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_conjugate_trace_q129
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_linearized_correlation_q129
import Theorems.Thm_OAI_Generator_Tracial_tracial_remainder_of_coordinate_moments_q129

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

theorem quotient_norm_mul_unitary (a u : Q τ ω) (hu : u*star u = 1) :
    ‖a*u‖ = ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    inner_eq_trace, inner_eq_trace, star_mul]
  have he : quotientTrace τ ω (star u*star a*(a*u)) = quotientTrace τ ω (star a*a) := by
    rw [mul_assoc, quotientTrace_mul_comm τ ω (star u) (star a*(a*u))]
    simp only [mul_assoc, hu, mul_one]
  rw [he]

theorem quotient_trace_cauchy_schwarz (a b : Q τ ω) :
    ‖quotientTrace τ ω (star a*b)‖ ≤ ‖a‖*‖b‖ :=
  norm_inner_le_norm a b

/-- The source's complex trace error bound from its actual first-order identity
and the actual quotient remainder, with unitary right multiplication accounted for. -/
theorem quotient_correlation_remainder (ξ v c w : Q τ ω) (target : ℂ) (R : ℝ)
    (hw : w*star w = 1)
    (hfirst : quotientTrace τ ω (star ξ*((1+c)*w)) = target)
    (hrem : ‖v-(1+c)‖ ≤ R) :
    ‖quotientTrace τ ω (star ξ*(v*w))-target‖ ≤ ‖ξ‖*R := by
  have he : quotientTrace τ ω (star ξ*(v*w))-target =
      quotientTrace τ ω (star ξ*((v-(1+c))*w)) := by
    rw [← hfirst, sub_mul, mul_sub, quotient_trace_sub]
  rw [he]
  apply (quotient_trace_cauchy_schwarz τ ω ξ _).trans
  rw [quotient_norm_mul_unitary τ ω _ w hw]
  exact mul_le_mul_of_nonneg_left hrem (norm_nonneg ξ)

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/

/-! The actual free-group representation furnished by successive Haar variables. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem unitaryRepresentation_gram {A : Type*} [DecidableEq A]
    (v : A → unitary (Q τ ω))
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω v g : Q τ ω)=0)
    (g h : FreeGroup A) :
    quotientTrace τ ω (star (unitaryRepresentation τ ω v g : Q τ ω)*
      (unitaryRepresentation τ ω v h : Q τ ω))=if g=h then 1 else 0 := by
  have he : star (unitaryRepresentation τ ω v g : Q τ ω)*
      (unitaryRepresentation τ ω v h : Q τ ω)=
      (unitaryRepresentation τ ω v (g⁻¹*h) : Q τ ω) := by
    exact (congrArg (fun a : unitary (Q τ ω) => (a : Q τ ω))
      (((unitaryRepresentation τ ω v).map_mul (g⁻¹) h).trans
        (congrArg (fun a => a*unitaryRepresentation τ ω v h)
          ((unitaryRepresentation τ ω v).map_inv g)))).symm
  apply (congrArg (quotientTrace τ ω) he).trans
  by_cases hgh : g=h
  · subst h
    rw [_root_.inv_mul_cancel,map_one,ite_eq_left rfl]
    exact quotientTrace_one τ ω
  · rw [ite_eq_right hgh]
    exact hzero _ (fun heq => hgh (_root_.inv_mul_eq_one.mp heq))

end

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

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
section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem sequenceUnitaryQuotient_bounded (b : Bounded M)
    (hb : ∀ k,b.val k ∈ unitary M.toStarSubalgebra) :
    (sequenceUnitaryQuotient τ ω (boundedUnitarySequence b hb) : Q τ ω)=
      quotientMap τ (ω : Filter ℕ) b := by
  change quotientMap τ (ω : Filter ℕ) (boundedMap (boundedToSequence b))=_
  rw [boundedToSequence_map]

theorem coordinateGroupRing_single {A : Type*} (v : A → unitary (Sequences M))
    (g : FreeGroup A) : coordinateGroupRing v (MonoidAlgebra.single g 1)=(FreeGroup.lift v g : Sequences M) := by
  simp [coordinateGroupRing]

theorem freeGroup_quotient {A : Type*} (v : A → unitary (Sequences M))
    (q : A → unitary (Q τ ω)) (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (g : FreeGroup A) : sequenceUnitaryQuotient τ ω (FreeGroup.lift v g)=
      unitaryRepresentation τ ω q g := by
  exact FreeGroup.lift_unique ((sequenceUnitaryQuotient τ ω).comp (FreeGroup.lift v))
    (fun a => by simpa only [MonoidHom.comp_apply,FreeGroup.lift_apply_of] using hv a)

theorem coordinateGroupRing_quotient_single {A : Type*} (v : A → unitary (Sequences M))
    (q : A → unitary (Q τ ω)) (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (g : FreeGroup A) : sequenceQuotient τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))=
      (unitaryRepresentation τ ω q g : Q τ ω) := by
  rw [coordinateGroupRing_single]
  exact congrArg Subtype.val (freeGroup_quotient τ ω v q hv g)

theorem coordinateGroupRing_gram_limits {A : Type*} [DecidableEq A]
    (v : A → unitary (Sequences M)) (q : A → unitary (Q τ ω))
    (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω q g : Q τ ω)=0)
    (g h : FreeGroup A) :
    Tendsto (fun k => τ.trace (star (coordinateGroupRing v (MonoidAlgebra.single g 1) k)*
      coordinateGroupRing v (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g=h then 1 else 0)) := by
  have ht := sequence_inner_tendsto τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))
    (coordinateGroupRing v (MonoidAlgebra.single h 1))
  simpa only [sequenceInclusion_apply,inclusion_inner,
    coordinateGroupRing_quotient_single τ ω v q hv,unitaryRepresentation_gram τ ω q hzero] using ht

end

/-! Prefix labels and conjugate-word Gram identities for free-group perturbations. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

set_option maxHeartbeats 1600000 in
theorem unitaryRepresentation_prefix (u : unitary (Q τ ω))
    (t : ℕ → unitary (Q τ ω)) (k : ℕ) :
    unitaryRepresentation τ ω (prefixVariable τ ω u t) (freePrefix k)=
      prefixProduct τ ω u t k := by
  induction k with
  | zero => exact map_one _
  | succ k ih =>
    rw [freePrefix,(unitaryRepresentation τ ω (prefixVariable τ ω u t)).map_mul,ih]
    change prefixProduct τ ω u t k*FreeGroup.lift (prefixVariable τ ω u t) (FreeGroup.of k)=_
    rw [FreeGroup.lift_apply_of]
    rfl

end

/-! The literal bounded coordinate model of the finite-prefix free group.
The t_j sequences are the witnesses retained by the successive construction. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.haarSequence_quotient (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j : ℕ) : sequenceUnitaryQuotient τ ω (F.haarSequence τ ω j)=(F.step j).t := by
  apply Subtype.ext
  exact (sequenceUnitaryQuotient_bounded τ ω
    (boundedInclusion hNM (F.step j).coordinates)
    (fun k => Unitary.map_mem (coordinateInclusion hNM) ((F.step j).unitary_coordinates k))).trans
      (F.step j).represents

theorem SuccessiveCoordinateHaar.coordinateVariables_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra) (j : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinateVariables τ ω u j)=
      prefixVariable τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) j := by
  cases j with
  | zero => exact F.haarSequence_quotient τ ω 0
  | succ j =>
    change sequenceUnitaryQuotient τ ω (constantSequenceUnitary u*F.haarSequence τ ω (j+1))=_
    rw [(sequenceUnitaryQuotient τ ω).map_mul,F.haarSequence_quotient]
    rfl

theorem SuccessiveCoordinateHaar.coordinateLabels_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u : unitary M.toStarSubalgebra)
    (ell : ℕ) (p : PrefixLabel ell) :
    sequenceUnitaryQuotient τ ω (F.coordinateLabels τ ω u ell p)=
      F.labelUnitary τ ω (constantQuotientUnitary τ ω u) ell p :=
  freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u) p.val

theorem SuccessiveCoordinateHaar.coordinateTarget_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra) (ell : ℕ) :
    sequenceUnitaryQuotient τ ω (F.coordinateTarget τ ω u z ell)=
      F.targetUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell := by
  let q := sequenceUnitaryQuotient τ ω
  let a := FreeGroup.lift (F.coordinateVariables τ ω u) (freePrefix (ell+1))
  have hp := (freeGroup_quotient τ ω _ _ (F.coordinateVariables_quotient τ ω u)
    (freePrefix (ell+1))).trans
      (unitaryRepresentation_prefix τ ω (constantQuotientUnitary τ ω u)
        (fun k => (F.step k).t) (ell+1))
  exact (q.map_mul (constantSequenceUnitary z) a⁻¹).trans
    (congrArg (fun b => constantQuotientUnitary τ ω z*b)
      ((q.map_inv a).trans (congrArg Inv.inv hp)))

theorem SuccessiveCoordinateHaar.coordinateConjugates_quotient
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (p : PrefixLabel ell) :
    sequenceUnitaryQuotient τ ω (F.coordinateConjugates τ ω u z ell p)=
      F.conjugateUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell p := by
  let q := sequenceUnitaryQuotient τ ω
  let a := F.coordinateLabels τ ω u ell p
  let b := F.coordinateTarget τ ω u z ell
  have ha := F.coordinateLabels_quotient τ ω u ell p
  have hb := F.coordinateTarget_quotient τ ω u z ell
  exact (q.map_mul (a*b) a⁻¹).trans
    (congrArg₂ (fun x y => x*y)
      ((q.map_mul a b).trans (congrArg₂ (fun x y => x*y) ha hb))
      ((q.map_inv a).trans (congrArg Inv.inv ha)))

theorem SuccessiveCoordinateHaar.perturbationMap_gram
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (g h : FreeGroup (PrefixLabel ell)) :
    Tendsto (fun k => τ.trace (star (F.perturbationMap τ ω u z ell (MonoidAlgebra.single g 1) k)*
      F.perturbationMap τ ω u z ell (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g=h then 1 else 0)) := by
  classical
  exact coordinateGroupRing_gram_limits τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell)
    (F.conjugate_trace_q129 τ ω _ _ hu hz ell) g h

theorem SuccessiveCoordinateHaar.perturbation_remainder
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖sequenceQuotient τ ω (remainderSequence ell α (F.perturbationMap τ ω u z ell))‖ ≤
      4*α^2/(1-2*α) :=
  tracial_remainder_of_coordinate_moments_q129 τ ω ell hell _
    (F.perturbationMap_gram τ ω u z hu hz ell) α hα hhalf

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
-- module Solutions.OAIQ129_RG2.FactorGeneration_WordCorrelation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Ordered prefix cancellation for the actual common perturbed unitary.
All identities are identities of bounded coordinate sequences. -/
namespace Tracial

/-! The exact first-order trace calculation for the manuscript's prefix labels. -/

/-! The first-order term is exactly the sum of the mapped formal rows, and
its correlation is the manuscript's alpha/2 coefficient. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.perturbationMap_firstOrder
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) :
    sequenceQuotient τ ω (((finitePerturbationRows ell α).map (F.perturbationMap τ ω u z ell)).sum)=
      F.firstOrderTerm τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z)
        ell ((α/(2*ell) : ℝ) : ℂ) := by
  let Ψ := (sequenceQuotient τ ω).toAlgHom.comp (F.perturbationMap τ ω u z ell)
  let Y := F.conjugateUnitary τ ω (constantQuotientUnitary τ ω u) (constantQuotientUnitary τ ω z) ell
  have hword (g : FreeGroup (PrefixLabel ell)) : Ψ (MonoidAlgebra.single g 1)=
      (unitaryRepresentation τ ω Y g : Q τ ω) :=
    coordinateGroupRing_quotient_single τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell) g
  have hgen (p : PrefixLabel ell) : Ψ (MonoidAlgebra.single (FreeGroup.of p) 1)=(Y p : Q τ ω) := by
    rw [hword]
    exact congrArg Subtype.val (show FreeGroup.lift Y (FreeGroup.of p)=Y p from FreeGroup.lift_apply_of)
  have hinv (p : PrefixLabel ell) : Ψ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (Y p : Q τ ω) := by
    rw [hword,(unitaryRepresentation τ ω Y).map_inv]
    change star (FreeGroup.lift Y (FreeGroup.of p) : Q τ ω)=_
    rw [FreeGroup.lift_apply_of]
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Ψ (r • a)=r • Ψ a :=
    map_smul (Ψ.restrictScalars ℝ).toLinearMap r a
  have hrow (k : Fin ell) : Ψ (finitePerturbationRow α k)=
      (α/(2*ell) : ℝ) • ∑ j : Fin ell,((Y (pairLabel k j) : Q τ ω)-star (Y (pairLabel k j) : Q τ ω)) := by
    rw [finitePerturbationRow,hs]
    congr 1
    simp only [map_sum,map_sub,hgen,hinv]
  change (sequenceQuotient τ ω) (((List.ofFn (finitePerturbationRow (n := ell) α)).map
    (F.perturbationMap τ ω u z ell)).sum)=_
  rw [List.map_ofFn,List.sum_ofFn,map_sum]
  change (∑ k : Fin ell,Ψ (finitePerturbationRow α k))=_
  simp only [hrow,← Finset.smul_sum]
  exact (IsScalarTower.algebraMap_smul ℂ (α/(2*ell) : ℝ) _).symm

theorem SuccessiveCoordinateHaar.coordinate_linearized_correlation
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) :
    quotientTrace τ ω (star xi*(1+sequenceQuotient τ ω
      (((finitePerturbationRows ell α).map (F.perturbationMap τ ω u z ell)).sum))*
      (prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω)) := by
  rw [F.perturbationMap_firstOrder,F.linearized_correlation_q129 τ ω _ _ xi hu hz hxi]
  have hn : (ell : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hell)
  push_cast
  field_simp [hn]

end

/-! The uniform trace correlation for the actual product of coordinate
exponentials. Identifying that product with a single-unitary perturbation word
is a separate remaining step. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.exponential_product_correlation_q129_oai
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖quotientTrace τ ω (star xi*(sequenceQuotient τ ω
      (((finitePerturbationRows ell α).map (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod)*
      (prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1) : Q τ ω)))-
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
        ‖xi‖*(4*α^2/(1-2*α)) := by
  let W := prefixProduct τ ω (constantQuotientUnitary τ ω u) (fun k => (F.step k).t) (ell+1)
  apply quotient_correlation_remainder τ ω xi _ _ (W : Q τ ω) _ _
    (Unitary.coe_mul_star_self W)
  · simpa only [mul_assoc] using F.coordinate_linearized_correlation τ ω u z xi hu hz hxi ell hell α
  · have h := F.perturbation_remainder τ ω u z hu hz ell hell α hα hhalf
    simpa only [remainderSequence,map_sub,map_one,sub_add_eq_sub_sub] using h

end

/-! The uniform correlation now belongs to the literal word in one common
perturbed unitary, as required by eq:perturbation-prefix. -/
open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129_oai.{u_1}
