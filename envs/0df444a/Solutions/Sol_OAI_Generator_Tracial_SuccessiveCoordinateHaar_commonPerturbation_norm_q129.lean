-- Prove2me | solution 1 for OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_q129
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:27:40.994545+00:00
-- url     : https://prove2.me/submissions/58e9eac5-d610-4d68-ba05-78163691b0c9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014
import Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_conjugate_trace_q129

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_Convolution
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}

theorem letter_false (a : A) : letter (a, false) = (FreeGroup.of a)⁻¹ := by
  simpa [inverseLetter] using letter_inverse (a, true)

theorem letter_injective : Function.Injective (letter : Letter A → FreeGroup A) := by
  intro a b h
  have hw := congrArg FreeGroup.toWord h
  simpa only [letter_toWord, List.singleton_inj] using hw

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

end Generator

end

end OAI
end

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

theorem coordinateGroupRing_orthonormal {A : Type*} [DecidableEq A]
    (v : A → unitary (Sequences M)) (q : A → unitary (Q τ ω))
    (hv : ∀ a,sequenceUnitaryQuotient τ ω (v a)=q a)
    (hzero : ∀ g : FreeGroup A,g ≠ 1 →
      quotientTrace τ ω (unitaryRepresentation τ ω q g : Q τ ω)=0) :
    Orthonormal ℂ (fun g => sequenceInclusion τ ω (coordinateGroupRing v (MonoidAlgebra.single g 1))) := by
  rw [orthonormal_iff_ite]
  intro g h
  simp only [sequenceInclusion_apply,inclusion_inner,
    coordinateGroupRing_quotient_single τ ω v q hv,unitaryRepresentation_gram τ ω q hzero]

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

end

/-! The one literal bounded skew-adjoint perturbation K = i h. Every formal
row is its conjugate by the corresponding actual coordinate prefix. -/
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.coordinateLabels_pair
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u : unitary M.toStarSubalgebra) {ell : ℕ} (k j : Fin ell) :
    F.coordinateLabels τ ω u ell (pairLabel k j)=
      F.coordinatePrefix τ ω u (k.val+1)*(F.coordinatePrefix τ ω u (j.val+1))⁻¹ := by
  change FreeGroup.lift _ (freePrefix _*(freePrefix _)⁻¹)=_
  rw [(FreeGroup.lift (F.coordinateVariables τ ω u)).map_mul,
    (FreeGroup.lift (F.coordinateVariables τ ω u)).map_inv]
  rfl

theorem SuccessiveCoordinateHaar.perturbationMap_row
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) {ell : ℕ} (α : ℝ) (k : Fin ell) :
    F.perturbationMap τ ω u z ell (finitePerturbationRow α k)=
      (F.coordinatePrefix τ ω u (k.val+1) : Sequences M)*
        F.commonPerturbation τ ω u z ell α*
        star (F.coordinatePrefix τ ω u (k.val+1) : Sequences M) := by
  let Φ := F.perturbationMap τ ω u z ell
  have hs (r : ℝ) (a : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell))) : Φ (r • a)=r • Φ a :=
    map_smul (Φ.restrictScalars ℝ).toLinearMap r a
  have hgen (p : PrefixLabel ell) : Φ (MonoidAlgebra.single (FreeGroup.of p) 1)=
      (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,FreeGroup.lift_apply_of]
  have hinv (p : PrefixLabel ell) : Φ (MonoidAlgebra.single ((FreeGroup.of p)⁻¹) 1)=
      star (F.coordinateConjugates τ ω u z ell p : Sequences M) := by
    change coordinateGroupRing _ _=_
    rw [coordinateGroupRing_single,map_inv,FreeGroup.lift_apply_of]
    rfl
  change Φ (finitePerturbationRow α k)=_
  rw [finitePerturbationRow,hs,commonPerturbation]
  simp only [map_sum,map_sub,hgen,hinv,mul_smul_comm,smul_mul_assoc,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateConjugates,coordinateLabels_pair]
  simp only [← Unitary.star_eq_inv,Submonoid.coe_mul,Unitary.coe_star]
  simp only [star_mul,star_star,mul_sub,sub_mul,mul_assoc]

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_PerturbationBounds
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

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators InnerProductSpace
open FreeConvolution

theorem pairLabel_right_injective {ell : ℕ} (k : Fin ell) :
    Function.Injective (pairLabel k) := by
  intro i j hij
  have h := congrArg Subtype.val hij
  change freePrefix (k.val+1)*(freePrefix (i.val+1))⁻¹=
    freePrefix (k.val+1)*(freePrefix (j.val+1))⁻¹ at h
  have he := freePrefix_injective (inv_injective (mul_left_cancel h))
  exact Fin.ext (Nat.add_right_cancel he)

theorem rowSignedWord_injective {ell : ℕ} (k : Fin ell) :
    Function.Injective (rowSignedWord k) := by
  intro a b hab
  have h := letter_injective hab
  exact Prod.ext (pairLabel_right_injective k (congrArg Prod.fst h)) (congrArg (fun x : PrefixLabel ell × Bool => x.2) h)

theorem finitePerturbationRow_signed {ell : ℕ} (α : ℝ) (k : Fin ell) :
    finitePerturbationRow α k=
      ∑ a : Fin ell × Bool, (if a.2 then ((α/(2*ell) : ℝ) : ℂ) else -((α/(2*ell) : ℝ) : ℂ)) •
        MonoidAlgebra.single (rowSignedWord k a) 1 := by
  rw [finitePerturbationRow,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,rowSignedWord,letter_true,letter_false,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true,neg_smul,← sub_eq_add_neg,← smul_sub,← Finset.smul_sum]
  exact (IsScalarTower.algebraMap_smul ℂ (α/(2*ell) : ℝ) _).symm

theorem finitePerturbationRow_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ell : ℕ} (α : ℝ) (k : Fin ell)
    (Ψ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell)) →ₗ[ℂ] E)
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1))) :
    ‖Ψ (finitePerturbationRow α k)‖^2=2*ell*(α/(2*ell))^2 := by
  have hv : Orthonormal ℂ (fun a => Ψ (MonoidAlgebra.single (rowSignedWord k a) 1)) :=
    hΨ.comp (rowSignedWord k) (rowSignedWord_injective k)
  rw [finitePerturbationRow_signed,map_sum]
  simp only [map_smul]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),hv.inner_sum,map_sum]
  calc
    _ = ∑ a : Fin ell × Bool, ‖(if a.2 then ((α/(2*ell) : ℝ) : ℂ)
        else -((α/(2*ell) : ℝ) : ℂ))‖^2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_comm]
      exact inner_self_eq_norm_sq (𝕜 := ℂ)
        (if a.2 then ((α/(2*ell) : ℝ) : ℂ) else -((α/(2*ell) : ℝ) : ℂ))
    _ = _ := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
        norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      ring

end

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem quotient_norm_unitary_mul (g : unitary (Q τ ω)) (a : Q τ ω) :
    ‖(g : Q τ ω)*a‖=‖a‖ := by
  rw [← quotient_norm_star,star_mul,quotient_norm_mul_unitary τ ω _ (star (g : Q τ ω)),
    quotient_norm_star]
  simpa only [star_star] using g.property.1

theorem SuccessiveCoordinateHaar.commonPerturbation_norm_sq
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) :
    ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖^2=
      2*ell*(α/(2*ell))^2 := by
  let k : Fin ell := ⟨0,hell⟩
  let Ψ := (sequenceInclusion τ ω).toLinearMap.comp (F.perturbationMap τ ω u z ell).toLinearMap
  have ho := coordinateGroupRing_orthonormal τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell)
    (F.conjugate_trace_q129 τ ω _ _ hu hz ell)
  have hr := finitePerturbationRow_norm_sq α k Ψ ho
  have hn : ‖Ψ (finitePerturbationRow α k)‖=
      ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖ := by
    change ‖sequenceInclusion τ ω (F.perturbationMap τ ω u z ell (finitePerturbationRow α k))‖=_
    rw [sequenceInclusion_apply,LinearIsometry.norm_map,F.perturbationMap_row,map_mul,map_mul,map_star]
    let g := sequenceUnitaryQuotient τ ω (F.coordinatePrefix τ ω u (k.val+1))
    change ‖(g : Q τ ω)*sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)*star (g : Q τ ω)‖=_
    rw [quotient_norm_mul_unitary τ ω _ (star (g : Q τ ω)),quotient_norm_unitary_mul]
    simpa only [star_star] using g.property.1
  rwa [hn] at hr

theorem SuccessiveCoordinateHaar.commonPerturbation_norm_q129_oai
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 ≤ α) :
    ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖=
      α/Real.sqrt (2*ell) := by
  have hn : (0 : ℝ)<2*ell := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg hα (Real.sqrt_nonneg _))).mp
  rw [F.commonPerturbation_norm_sq τ ω u z hu hz ell hell α]
  simp only [div_pow,Real.sq_sqrt hn.le]
  field_simp [ne_of_gt hn]

end

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter

end Tracial

end Generator

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_q129_oai.{u_1} := @OAI.Generator.Tracial.SuccessiveCoordinateHaar.commonPerturbation_norm_q129_oai.{u_1}
