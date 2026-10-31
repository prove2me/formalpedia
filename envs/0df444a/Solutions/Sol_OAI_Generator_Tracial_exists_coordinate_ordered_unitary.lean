-- Prove2me | solution 1 for OAI.Generator.Tracial.exists_coordinate_ordered_unitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:32:34.102419+00:00
-- url     : https://prove2.me/submissions/37412884-f625-4f1b-a622-ae377fc4b2e5

import Mathlib
import Definitions.Def_OAIQ11Fg023
import Theorems.Thm_OAI_Generator_Tracial_exactOrderedMoments_partial_limit
import Theorems.Thm_OAI_Generator_Tracial_exists_coordinate_monotone_upper
import Theorems.Thm_OAI_Generator_Tracial_exists_exact_residual_step

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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

end PartialUnitary

end

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

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
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
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
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualCompletion
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem exists_exact_residual_iteration (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ a : ℕ → ℕ → PartialUnitary M,a 0=v ∧
      (∀ n j,(a n j).val.val ∈ N) ∧ (∀ j,Monotone (fun n => a n j)) ∧
      (∀ n,ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) ∧
      ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*quotientResidualTrace τ ω v := by
  let S := {u : ℕ → PartialUnitary M // (∀ j,(u j).val.val ∈ N) ∧
    ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x}
  have next (u : S) : ∃ w : S,(∀ j,u.val j ≤ w.val j) ∧
      quotientResidualTrace τ ω w.val ≤ (3/4 : ℝ)*quotientResidualTrace τ ω u.val := by
    obtain ⟨w,hw,hle,hmw,hr⟩ := exists_exact_residual_step (H := H) (N := N) (M := M) τ hNM hfactor hdiff hirr hsep
      ω hω u.val u.property.1 x hx u.property.2
    exact ⟨⟨w,hw,hmw⟩,hle,hr⟩
  let step : S → S := fun u => (next u).choose
  have hs (u : S) := (next u).choose_spec
  let a : ℕ → S := fun n => Nat.rec (⟨v,hv,hm⟩ : S) (fun _ u => step u) n
  refine ⟨fun n => (a n).val,rfl,fun n => (a n).property.1,?_,fun n => (a n).property.2,?_⟩
  · intro j
    apply monotone_nat_of_le_succ
    intro n
    exact (hs (a n)).1 j
  · intro n
    induction n with
    | zero => simp only [pow_zero,one_mul]; exact le_rfl
    | succ n ih =>
      calc quotientResidualTrace τ ω (a (n+1)).val ≤
          (3/4 : ℝ)*quotientResidualTrace τ ω (a n).val := (hs (a n)).2
           _ ≤ (3/4 : ℝ)*((3/4 : ℝ)^n*quotientResidualTrace τ ω v) :=
             mul_le_mul_of_nonneg_left ih (by norm_num)
           _ = _ := by rw [pow_succ]; ring

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
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarIndependence
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Two-norm continuity of ordered moments along uniformly operator-bounded
representatives. No topological-ring structure on the two-norm quotient is used. -/

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
  obtain ⟨a,ha⟩ := exists_exact_residual_iteration (H := H) (N := N) (M := M)
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
-- module Solutions.OAIQ11_FG.FactorGeneration_CoordinateUnitaries
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

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

theorem exists_coordinate_ordered_unitary_oai
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

theorem solution.{u_1} : type_of% @OAI.Generator.Tracial.exists_coordinate_ordered_unitary_oai.{u_1} := @OAI.Generator.Tracial.exists_coordinate_ordered_unitary_oai.{u_1}
