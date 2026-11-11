-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.factor_isTypeII1FactorWithVector
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:02.094978+00:00
-- url     : https://prove2.me/submissions/cbbdb8f0-9066-4102-9e3c-f3209557f9ca

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Piecewise
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialProjectionTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal

namespace Invariant233.TracialProjectionTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem vectorTrace_projection (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    vectorTrace ξ p.starProjection = (‖p.starProjection ξ‖ ^ 2 : ℂ) := by
  unfold vectorTrace
  calc
    inner ℂ ξ (p.starProjection ξ) =
        inner ℂ (p.starProjection ξ) (p.starProjection ξ) := by
      rw [Submodule.inner_starProjection_left_eq_right]
      rw [Submodule.starProjection_eq_self_iff.mpr (p.starProjection_apply_mem ξ)]
    _ = _ := inner_self_eq_norm_sq_to_K _

theorem vectorTrace_projection_re (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    (vectorTrace ξ p.starProjection).re = ‖p.starProjection ξ‖ ^ 2 := by
  rw [vectorTrace_projection]
  norm_cast

theorem vectorTrace_projection_mono (ξ : H) {p q : Submodule ℂ H}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (hpq : p ≤ q) :
    (vectorTrace ξ p.starProjection).re ≤ (vectorTrace ξ q.starProjection).re := by
  rw [vectorTrace_projection_re, vectorTrace_projection_re]
  have hnorm := p.norm_starProjection_apply_le (q.starProjection ξ)
  have heq := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le hpq) ξ
  change p.starProjection (q.starProjection ξ) = p.starProjection ξ at heq
  rw [heq] at hnorm
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem vectorTrace_projection_orthogonal (ξ : H) (p : Submodule ℂ H)
    [p.HasOrthogonalProjection] :
    vectorTrace ξ pᗮ.starProjection = (‖ξ‖ ^ 2 : ℂ) - vectorTrace ξ p.starProjection := by
  unfold vectorTrace
  rw [Submodule.starProjection_orthogonal]
  simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_right]
  rw [inner_self_eq_norm_sq_to_K]
  rfl


end Invariant233.TracialProjectionTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ProjectionMeetTrace
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Invariant233.ProjectionMeetTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_one_sub_gram_le_one (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) :
    ‖1 - star A * A‖ ≤ 1 := by
  have hgram : 0 ≤ star A * A := star_mul_self_nonneg A
  have hnorm : ‖star A * A‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg A]
  have hle : star A * A ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hgram).mp hnorm
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hle)).mpr
    (sub_le_self _ hgram)

omit [CompleteSpace H] in

theorem mul_complement_pow (a b : H →L[ℂ] H) (n : ℕ) :
    a * (1 - b * a) ^ n = (1 - a * b) ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    noncomm_ring

theorem vectorTrace_complement_pow_eq
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M) (n : ℕ) :
    vectorTrace ξ ((1 - a * b) ^ n) = vectorTrace ξ ((1 - b * a) ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : (1 - a * b) ^ n ∈ M := pow_mem (sub_mem (one_mem M) (mul_mem ha hb)) n
    have hcycle := htrace ((1 - a * b) ^ n * a) b (mul_mem hp ha) hb
    have hterm : vectorTrace ξ (((1 - a * b) ^ n * a) * b) =
        vectorTrace ξ (((1 - b * a) ^ n * b) * a) := by
      rw [hcycle, ← mul_assoc, mul_complement_pow b a n]
    simpa only [pow_succ, mul_sub, mul_one, ← mul_assoc,
      vectorTrace, sub_apply, inner_sub_right] using congrArg₂ (fun x y : ℂ => x - y) ih hterm

omit [CompleteSpace H] in

theorem meanOperator_apply (A : H →L[ℂ] H) (n : ℕ) (x : H) :
    meanOperator A n x = birkhoffAverage ℂ A id n x := by
  simp only [meanOperator, birkhoffAverage, birkhoffSum, smul_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (congrArg (fun f : H →ₗ[ℂ] H => f x) (ContinuousLinearMap.toLinearMap_pow A k)).trans
    (congrFun (Module.End.coe_pow A.toLinearMap k) x)

theorem eqLocus_one_sub_gram (A : H →L[ℂ] H) :
    (1 - star A * A).eqLocus (1 : H →L[ℂ] H) = A.ker := by
  rw [← A.ker_adjoint_comp_self]
  ext x
  change x - (A.adjoint (A x)) = x ↔ A.adjoint (A x) = 0
  exact sub_eq_self

theorem meanOperator_one_sub_gram_tendsto (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x : H) :
    Tendsto (fun n => meanOperator (1 - star A * A) n x) atTop
      (𝓝 (A.ker.starProjection x)) := by
  have ht := (1 - star A * A).tendsto_birkhoffAverage_orthogonalProjection
    (norm_one_sub_gram_le_one A hA) x
  simp only [← meanOperator_apply] at ht
  change Tendsto (fun n => meanOperator (1 - star A * A) n x) atTop
    (𝓝 (((1 - star A * A).eqLocus (1 : H →L[ℂ] H)).starProjection x)) at ht
  simpa only [eqLocus_one_sub_gram] using ht

theorem vectorTrace_kernel_eq_adjoint_kernel
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (A : H →L[ℂ] H) (hA : A ∈ M) (hnorm : ‖A‖ ≤ 1) :
    vectorTrace ξ A.ker.starProjection = vectorTrace ξ A.adjoint.ker.starProjection := by
  have hnstar : ‖star A‖ ≤ 1 := by simpa using hnorm
  have hlim : Tendsto (fun n => vectorTrace ξ (meanOperator (1 - star A * A) n))
      atTop (𝓝 (vectorTrace ξ A.ker.starProjection)) :=
    tendsto_const_nhds.inner (meanOperator_one_sub_gram_tendsto A hnorm ξ)
  have hlimStar : Tendsto (fun n => vectorTrace ξ
      (meanOperator (1 - star (star A) * star A) n)) atTop
      (𝓝 (vectorTrace ξ (star A).ker.starProjection)) :=
    tendsto_const_nhds.inner (meanOperator_one_sub_gram_tendsto (star A) hnstar ξ)
  have heq : ∀ n, vectorTrace ξ (meanOperator (1 - star A * A) n) =
      vectorTrace ξ (meanOperator (1 - star (star A) * star A) n) := by
    intro n
    change vectorFunctional ξ (meanOperator (1 - star A * A) n) =
      vectorFunctional ξ (meanOperator (1 - star (star A) * star A) n)
    simp only [meanOperator, map_smul, map_sum, star_star]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact vectorTrace_complement_pow_eq M ξ htrace (star A) A (star_mem hA) hA k
  have hlim' : Tendsto (fun n => vectorTrace ξ
      (meanOperator (1 - star (star A) * star A) n)) atTop
      (𝓝 (vectorTrace ξ A.ker.starProjection)) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact (heq n).symm
  have hresult := tendsto_nhds_unique hlim' hlimStar
  simpa only [vectorTrace, ContinuousLinearMap.star_eq_adjoint] using hresult

omit [CompleteSpace H] in

theorem projection_mul_of_le {p q : Submodule ℂ H}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (h : p ≤ q) :
    q.starProjection * p.starProjection = p.starProjection := by
  ext x
  exact q.starProjection_eq_self_iff.mpr (h (p.starProjection_apply_mem x))

theorem kernel_projection_complement_mul (p q : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace q] :
    ((1 - q.starProjection) * p.starProjection).ker.starProjection =
      1 - p.starProjection + (p ⊓ q).starProjection := by
  let A := (1 - q.starProjection) * p.starProjection
  let R := (p ⊓ q).starProjection
  have hpR : p.starProjection * R = R := projection_mul_of_le inf_le_left
  have hRp : R * p.starProjection = R :=
    Submodule.starProjection_comp_starProjection_of_le inf_le_left
  have hqR : q.starProjection * R = R := projection_mul_of_le inf_le_right
  have horth : (1 - p.starProjection) * R = 0 := by
    rw [sub_mul, one_mul, hpR, sub_self]
  have hproj : IsStarProjection (1 - p.starProjection + R) :=
    isStarProjection_starProjection.one_sub.add isStarProjection_starProjection horth
  have hAp : A * (1 - p.starProjection + R) = 0 := by
    dsimp [A]
    have hpp := p.isIdempotentElem_starProjection.eq
    noncomm_ring [hpp, hpR, hqR]
  have hrange : (1 - p.starProjection + R).range = A.ker := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      change A ((1 - p.starProjection + R) x) = 0
      have hx := congrArg (fun B : H →L[ℂ] H => B x) hAp
      exact hx
    · intro x hx
      have hAx : p.starProjection x - q.starProjection (p.starProjection x) = 0 := hx
      have hpq : p.starProjection x ∈ p ⊓ q := by
        exact ⟨p.starProjection_apply_mem x,
          q.starProjection_eq_self_iff.mp (sub_eq_zero.mp hAx).symm⟩
      have hRx : R x = p.starProjection x := by
        have h1 : R (p.starProjection x) = p.starProjection x :=
          (p ⊓ q).starProjection_eq_self_iff.mpr hpq
        have h2 := congrArg (fun B : H →L[ℂ] H => B x) hRp
        exact h2.symm.trans h1
      refine ⟨x, ?_⟩
      change x - p.starProjection x + R x = x
      rw [hRx, sub_add_cancel]
  obtain ⟨hinst, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hproj
  simpa only [hrange] using heq.symm

theorem meet_projection_mem (M : VonNeumannAlgebra H) (p q : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (p ⊓ q).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  have hpW := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hp W hW
  have hqW := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hq W hW
  rw [Submodule.range_starProjection] at hpW hqW
  intro x hx
  exact ⟨hpW hx.1, hqW hx.2⟩

omit [CompleteSpace H] in

theorem norm_projection_le_one (p : Submodule ℂ H) [p.HasOrthogonalProjection] :
    ‖p.starProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using p.norm_starProjection_apply_le x

theorem vectorTrace_meet_lower_bound
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ q.starProjection).re -
      ‖ξ‖ ^ 2 ≤ (vectorTrace ξ (p ⊓ q).starProjection).re := by
  let A := (1 - q.starProjection) * p.starProjection
  have hAmem : A ∈ M := mul_mem (sub_mem (one_mem M) hq) hp
  have hqn : ‖1 - q.starProjection‖ ≤ 1 := by
    have hh := norm_projection_le_one qᗮ
    simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.one_def] using hh
  have hpn := norm_projection_le_one p
  have hAn : ‖A‖ ≤ 1 := by
    apply (norm_mul_le _ _).trans
    nlinarith [norm_nonneg (1 - q.starProjection), norm_nonneg p.starProjection]
  have hstar : A.adjoint = p.starProjection * (1 - q.starProjection) := by
    change star A = _
    simp only [A, star_mul, star_sub, star_one,
      (isSelfAdjoint_starProjection p).star_eq, (isSelfAdjoint_starProjection q).star_eq]
  have hqker : q ≤ A.adjoint.ker := by
    intro x hx
    change A.adjoint x = 0
    rw [hstar]
    change p.starProjection (x - q.starProjection x) = 0
    rw [q.starProjection_eq_self_iff.mpr hx, sub_self, map_zero]
  have hmono := TracialProjectionTransport.vectorTrace_projection_mono ξ hqker
  have hsame := vectorTrace_kernel_eq_adjoint_kernel M ξ htrace A hAmem hAn
  rw [← hsame] at hmono
  change (vectorTrace ξ q.starProjection).re ≤
    (vectorTrace ξ (((1 - q.starProjection) * p.starProjection).ker.starProjection)).re at hmono
  rw [kernel_projection_complement_mul] at hmono
  have hone : (vectorTrace ξ (1 : H →L[ℂ] H)).re = ‖ξ‖ ^ 2 := by
    exact inner_self_eq_norm_sq (𝕜 := ℂ) ξ
  have hadd : vectorTrace ξ (1 - p.starProjection + (p ⊓ q).starProjection) =
      vectorTrace ξ 1 - vectorTrace ξ p.starProjection +
        vectorTrace ξ (p ⊓ q).starProjection := by
    simp only [vectorTrace, add_apply, sub_apply, inner_add_right, inner_sub_right]
  rw [hadd, Complex.add_re, Complex.sub_re, hone] at hmono
  linarith

end Invariant233.ProjectionMeetTrace

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DiffuseFromSmallPartitions
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projectionAtom_mul_eq_zero_of_trace_lt
    (M : VonNeumannAlgebra H) (ξ : H)
    (htrace : ∀ a b : H →L[ℂ] H, a ∈ M → b ∈ M →
      vectorTrace ξ (a * b) = vectorTrace ξ (b * a))
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : IsProjectionAtom M p.starProjection) (hq : q.starProjection ∈ M)
    (hlt : (vectorTrace ξ q.starProjection).re < (vectorTrace ξ p.starProjection).re) :
    q.starProjection * p.starProjection = 0 := by
  have hqorth : qᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.one_def] using
      sub_mem (one_mem M) hq
  have hr := ProjectionMeetTrace.meet_projection_mem M p qᗮ hp.1 hqorth
  have hRp : (p ⊓ qᗮ).starProjection * p.starProjection = (p ⊓ qᗮ).starProjection :=
    Submodule.starProjection_comp_starProjection_of_le inf_le_left
  rcases hp.2.2.2 (p ⊓ qᗮ).starProjection hr isStarProjection_starProjection hRp with hzero | heq
  · have hb := ProjectionMeetTrace.vectorTrace_meet_lower_bound M ξ htrace p qᗮ hp.1 hqorth
    have hc : (vectorTrace ξ qᗮ.starProjection).re =
        ‖ξ‖ ^ 2 - (vectorTrace ξ q.starProjection).re := by
      rw [TracialProjectionTransport.vectorTrace_projection_orthogonal]
      simp only [Complex.sub_re]
      norm_cast
    rw [hc, hzero] at hb
    simp only [vectorTrace, zero_apply, inner_zero_right, Complex.zero_re] at hb
    change (inner ℂ ξ (q.starProjection ξ)).re < (inner ℂ ξ (p.starProjection ξ)).re at hlt
    linarith
  · have hpq : p ≤ qᗮ := by
      intro x hx
      have hfix := p.starProjection_eq_self_iff.mpr hx
      rw [← heq] at hfix
      exact ((p ⊓ qᗮ).starProjection_eq_self_iff.mp hfix).2
    ext x
    exact q.starProjection_apply_eq_zero_iff.mpr (hpq (p.starProjection_apply_mem x))

theorem isDiffuse_of_small_trace_separating_families
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (hpart : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Q : Fin n → H →L[ℂ] H),
      (∀ i, Q i ∈ M) ∧ (∀ i, IsStarProjection (Q i)) ∧
      (∀ i, (vectorTrace ξ (Q i)).re < ε) ∧
      (∀ v : H, (∀ i, Q i v = 0) → v = 0)) :
    IsDiffuseVonNeumannAlgebra M := by
  intro P hP
  obtain ⟨hproj, hPeq⟩ := isStarProjection_iff_eq_starProjection_range.mp hP.2.1
  let := hproj
  let : CompleteSpace P.range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.2.1.isIdempotentElem).completeSpace_coe
  have hPpos : P.IsPositive := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    simpa only [hP.2.1.isSelfAdjoint.star_eq, hP.2.1.isIdempotentElem.eq] using
      star_mul_self_nonneg P
  have hnonneg : 0 ≤ (vectorTrace ξ P).re := hPpos.re_inner_nonneg_right ξ
  have hmass : 0 < (vectorTrace ξ P).re := by
    by_contra hn
    have hzre : (vectorTrace ξ P).re = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hz : vectorTrace ξ P = 0 := by
      rw [hPeq, TracialProjectionTransport.vectorTrace_projection] at hzre ⊢
      exact_mod_cast hzre
    exact hP.2.2.1 (hξ.2.2 P hP.1 hPpos hz)
  obtain ⟨n, Q, hQmem, hQproj, hQmass, hQsep⟩ := hpart _ hmass
  have hzero (i : Fin n) : Q i * P = 0 := by
    obtain ⟨hqproj, hQeq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hQproj i)
    let := hqproj
    let : CompleteSpace (Q i).range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range (hQproj i).isIdempotentElem).completeSpace_coe
    rw [hPeq, hQeq]
    apply projectionAtom_mul_eq_zero_of_trace_lt M ξ hξ.2.1 P.range (Q i).range
    · simpa only [← hPeq] using hP
    · simpa only [← hQeq] using hQmem i
    · simpa only [← hPeq, ← hQeq] using hQmass i
  apply hP.2.2.1
  ext v
  apply hQsep
  intro i
  exact congrArg (fun A : H →L[ℂ] H => A v) (hzero i)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiberCentrality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.FiberCentrality

open scoped ENNReal

local notation "K" => lp (fun _ : ℤ => ℂ) 2

theorem map_single_eq_smul_of_commute_diagonal
    (A D : K →L[ℂ] K) (d : ℤ → ℂ)
    (hd : Function.Injective d)
    (hD : ∀ (v : K) (k : ℤ), D v k = d k * v k)
    (hAD : A * D = D * A) (j : ℤ) :
    A (lp.single 2 j (1 : ℂ)) =
      (A (lp.single 2 j (1 : ℂ)) j) • lp.single 2 j (1 : ℂ) := by
  have hDe : D (lp.single 2 j (1 : ℂ)) =
      d j • lp.single 2 j (1 : ℂ) := by
    ext k
    by_cases h : j = k
    · subst k
      simp [hD]
    · simp [hD, lp.single_apply, h]
  ext k
  by_cases h : j = k
  · subst k
    simp
  · have heq := congrArg
        (fun L : K →L[ℂ] K => L (lp.single 2 j (1 : ℂ)) k) hAD
    have heq' : d j * A (lp.single 2 j (1 : ℂ)) k =
        d k * A (lp.single 2 j (1 : ℂ)) k := by
      simpa only [mul_apply_eq_comp, hDe, map_smul,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hD] using heq
    have hz : A (lp.single 2 j (1 : ℂ)) k = 0 := by
      have hp : (d j - d k) * A (lp.single 2 j (1 : ℂ)) k = 0 := by
        rw [sub_mul, heq', sub_self]
      exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (fun e => h (hd e)))
    simp [lp.single_apply, h, hz]

theorem scalar_of_commute_diagonal_and_shift
    (A D S : K →L[ℂ] K) (d : ℤ → ℂ)
    (hd : Function.Injective d)
    (hD : ∀ (v : K) (k : ℤ), D v k = d k * v k)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hAD : A * D = D * A) (hAS : A * S = S * A) :
    ∃ c : ℂ, A = c • (1 : K →L[ℂ] K) := by
  let a : ℤ → ℂ := fun j => A (lp.single 2 j (1 : ℂ)) j
  have hAe (j : ℤ) : A (lp.single 2 j (1 : ℂ)) =
      a j • lp.single 2 j (1 : ℂ) :=
    map_single_eq_smul_of_commute_diagonal A D d hd hD hAD j
  have hsucc (j : ℤ) : a (j + 1) = a j := by
    have heq : A (S (lp.single 2 j (1 : ℂ))) =
        S (A (lp.single 2 j (1 : ℂ))) :=
      congrArg (fun L : K →L[ℂ] K => L (lp.single 2 j (1 : ℂ))) hAS
    rw [hS, hAe, hAe, map_smul, hS] at heq
    have hcoord := congrArg (fun v : K => v (j + 1)) heq
    simpa using hcoord
  have ha (j : ℤ) : a j = a 0 := by
    induction j using Int.induction_on with
    | zero => rfl
    | succ n ih => exact (hsucc n).trans ih
    | pred n ih =>
      have h := hsucc (-(n : ℤ) - 1)
      simp only [sub_add_cancel] at h
      exact h.symm.trans ih
  refine ⟨a 0, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext_ring
  change A (lp.single 2 j (1 : ℂ)) = a 0 • lp.single 2 j (1 : ℂ)
  rw [hAe, ha]

theorem injective_integer_rotation_orbit (θ : ℝ) (hθ : Irrational θ)
    (x : AddCircle (1 : ℝ)) :
    Function.Injective (fun k : ℤ => x + k • (θ : AddCircle (1 : ℝ))) := by
  intro j k heq
  have hzero : (j - k) • (θ : AddCircle (1 : ℝ)) = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_zero]
    exact add_left_cancel heq
  have hreal : (((j - k : ℤ) : ℝ) * θ : AddCircle (1 : ℝ)) = 0 := by
    simpa only [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul] using hzero
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hreal
  by_contra hjk
  apply (hθ.intCast_mul (sub_ne_zero.mpr hjk)).ne_int n
  simpa only [zsmul_eq_mul, mul_one] using hn.symm

theorem injective_irrational_diagonal (θ : ℝ) (hθ : Irrational θ)
    (x : AddCircle (1 : ℝ)) :
    Function.Injective (fun k : ℤ =>
      (AddCircle.toCircle (x + k • (θ : AddCircle (1 : ℝ))) : ℂ)) := by
  intro j k h
  apply injective_integer_rotation_orbit θ hθ x
  exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)

end Invariant233.FiberCentrality

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldCentrality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.FiberCentrality

open MeasureTheory Filter
open scoped ENNReal

local notation "K" => lp (fun _ : ℤ => ℂ) 2

theorem ae_eq_scalar_of_ergodic_covariance
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → K →L[ℂ] K) (S : K →L[ℂ] K)
    (hS : ∀ j : ℤ, S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ))
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hscalar : ∀ᵐ x ∂μ, ∃ c : ℂ, A x = c • (1 : K →L[ℂ] K))
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : K →L[ℂ] K) := by
  let a : X → ℂ := fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0
  have hscalar' : ∀ᵐ x ∂μ, A x = a x • (1 : K →L[ℂ] K) := by
    filter_upwards [hscalar] with x hx
    obtain ⟨c, hc⟩ := hx
    have ha : a x = c := by
      dsimp [a]
      simp [hc]
    rw [ha]
    exact hc
  have hscalarσ : ∀ᵐ x ∂μ, A (σ x) = a (σ x) • (1 : K →L[ℂ] K) :=
    hσ.toMeasurePreserving.quasiMeasurePreserving.ae hscalar'
  have hSminus : S (lp.single 2 (-1 : ℤ) (1 : ℂ)) =
      lp.single 2 (0 : ℤ) (1 : ℂ) := by
    simpa using hS (-1)
  have hinv : a ∘ σ =ᵐ[μ] a := by
    filter_upwards [hscalar', hscalarσ, hcov] with x hx hσx hcovx
    have hv : S (A (σ x) (lp.single 2 (-1 : ℤ) (1 : ℂ))) =
        A x (S (lp.single 2 (-1 : ℤ) (1 : ℂ))) :=
      congrArg (fun L : K →L[ℂ] K => L (lp.single 2 (-1 : ℤ) (1 : ℂ))) hcovx
    rw [hσx, hx] at hv
    simp only [smul_apply, one_apply_eq_self,
      map_smul, hSminus] at hv
    have hv0 := congrArg (fun v : K => v (0 : ℤ)) hv
    simpa [a, Function.comp_def] using hv0
  obtain ⟨c, hc⟩ := hσ.ae_eq_const_of_ae_eq_comp₀ hm hinv
  refine ⟨c, ?_⟩
  filter_upwards [hscalar', hc] with x hx hcx
  exact hx.trans (congrArg (fun z : ℂ => z • (1 : K →L[ℂ] K)) hcx)

end Invariant233.FiberCentrality

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_HilbertModelSize
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.HilbertModelSize

open TopologicalSpace MeasureTheory
open scoped lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem not_finiteDimensional_of_infinite_orthonormal {ι : Type*} [Infinite ι]
    {v : ι → E} (hv : Orthonormal ℂ v) : ¬ FiniteDimensional ℂ E := by
  intro h
  let := h
  have : Finite ι := hv.linearIndependent.finite
  exact not_finite ι

theorem not_finiteDimensional_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (ℓ²(ι, ℂ)) :=
  not_finiteDimensional_of_infinite_orthonormal
    (default : HilbertBasis ι ℂ (ℓ²(ι, ℂ))).orthonormal

section BochnerLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem not_finiteDimensional_L2 (hE : ¬ FiniteDimensional ℂ E) :
    ¬ FiniteDimensional ℂ (Lp E 2 μ) := by
  intro h
  let := h
  exact hE (FiniteDimensional.of_injective (constL2Isometry μ).toLinearMap
    (constL2Isometry μ).injective)

theorem not_finiteDimensional_L2_l2 (ι : Type*) [Infinite ι] :
    ¬ FiniteDimensional ℂ (Lp (ℓ²(ι, ℂ)) 2 μ) :=
  not_finiteDimensional_L2 μ (not_finiteDimensional_l2 ι)

end BochnerLp

end Invariant233.HilbertModelSize

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldCovariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem ae_covariance_of_commute [TopologicalSpace.SeparableSpace E]
    (T J : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (J ξ) x = S (ξ (σ x)))
    (hcomm : Commute T J) :
    ∀ᵐ x ∂μ, A x * S = S * A (σ x) := by
  let v := TopologicalSpace.denseSeq E
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq E
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (S (v n)) = S (A (σ x) (v n)) :=
    ae_all_iff.mpr (fun n => ae_covariance_apply_of_commute T J A S σ hσ hT hJ hcomm (v n))
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  intro w
  exact hv.induction_on w
    (isClosed_eq ((A x).continuous.comp S.continuous)
      (S.continuous.comp (A (σ x)).continuous)) hx

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarFieldLift
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.DirectIntegral

open MeasureTheory Filter
open scoped ENNReal

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_smul_id_of_representation_ae_scalar
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hrep : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (c : ℂ) (hc : ∀ᵐ x ∂μ, A x = c • (1 : E →L[ℂ] E)) :
    T = c • (1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hrep f, hc, Lp.coeFn_smul c f] with x hfx hcx hsmul
  change (T f) x = (c • f) x
  rw [hfx, hcx]
  change c • f x = (c • f) x
  exact hsmul.symm

theorem scalar_of_representation_ae_scalar
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hrep : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hc : ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : E →L[ℂ] E)) :
    ∃ c : ℂ, T = c • (1 : Lp E 2 μ →L[ℂ] Lp E 2 μ) := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, eq_smul_id_of_representation_ae_scalar T A hrep c hc⟩

end Invariant233.DirectIntegral

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_RepresentedCommutation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.DirectIntegral

open MeasureTheory Filter
open scoped ENNReal

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Countable ι]

omit [IsFiniteMeasure μ] in
theorem represented_mul
    (T U : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : X → E →L[ℂ] E)
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hU : ∀ f : Lp E 2 μ, U f =ᵐ[μ] fun x => B x (f x))
    (f : Lp E 2 μ) :
    (T * U) f =ᵐ[μ] fun x => (A x * B x) (f x) := by
  filter_upwards [hT (U f), hU f] with x hx hy
  change T (U f) x = A x (B x (f x))
  rw [hx, hy]

theorem ae_commute_of_represented_commute
    (b : HilbertBasis ι ℂ E)
    (T U : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A B : X → E →L[ℂ] E)
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => A x (f x))
    (hU : ∀ f : Lp E 2 μ, U f =ᵐ[μ] fun x => B x (f x))
    (hcomm : Commute T U) : ∀ᵐ x ∂μ, Commute (A x) (B x) := by
  have hAB : (fun x => A x * B x) =ᵐ[μ] (fun x => B x * A x) := by
    apply L2Multiplication.field_unique_of_representation b (T * U)
    · exact represented_mul T U A B hT hU
    · rw [hcomm.eq]
      exact represented_mul U T B A hU hT
  filter_upwards [hAB] with x hx
  exact hx

end Invariant233.DirectIntegral

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentRotation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Invariant233.IndependentRotation

theorem irrational_finsupp_rat_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (c : ι →₀ ℚ) (hc : c ≠ 0) :
    Irrational (c.sum (fun i q => (q : ℝ) * θ i)) := by
  rintro ⟨r, hr⟩
  let l : Option ι →₀ ℚ := c.optionElim (-r)
  have hl : Finsupp.linearCombination ℚ (fun o : Option ι => o.elim 1 θ) l = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul]
    simp only [l, Finsupp.optionElim_apply_eq_elim, Option.elim_none,
      Finsupp.some_optionElim, Option.elim_some, Rat.smul_def, Rat.cast_neg, mul_one]
    linarith
  exact (Finsupp.optionElim_ne_zero_of_right (-r) c hc)
    ((linearIndependent_iff.mp hθ) l hl)

theorem irrational_coordinate {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ)) (i : ι) :
    Irrational (θ i) := by
  simpa using irrational_finsupp_rat_sum hθ (Finsupp.single i 1) (by simp)

theorem irrational_finsupp_int_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) :
    Irrational (v.sum (fun i n => (n : ℝ) * θ i)) := by
  let c : ι →₀ ℚ := v.mapRange (fun n : ℤ => (n : ℚ)) (by simp)
  have hc : c ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := DFunLike.congr_fun h i
    dsimp [c] at hi
    exact_mod_cast hi
  have h := irrational_finsupp_rat_sum hθ c hc
  simpa [c, Finsupp.sum_mapRange_index] using h

end Invariant233.IndependentRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ErgodicCharacterCriterion
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Invariant233.Characters

theorem integral_eq_zero_of_eigenfunction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {z : ℂ} (hz : z ≠ 1)
    (heigen : ∀ᵐ x ∂μ, f (σ x) = z * f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hfm : AEStronglyMeasurable f (μ.map σ) := by rwa [hσ.map_eq]
  have hmap := integral_map hσ.measurable.aemeasurable hfm
  rw [hσ.map_eq] at hmap
  have heq : (∫ x, f x ∂μ) = z * ∫ x, f x ∂μ := by
    calc
      _ = ∫ x, f (σ x) ∂μ := hmap
      _ = ∫ x, z * f x ∂μ := integral_congr_ae heigen
      _ = _ := integral_const_mul z f
  have hzero : (1 - z) * (∫ x, f x ∂μ) = 0 := by
    calc
      _ = (∫ x, f x ∂μ) - z * (∫ x, f x ∂μ) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz.symm)

theorem eq_zero_of_dense_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) (χ : ι → E)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hinner : ∀ i, inner ℂ v (χ i) = 0) : v = 0 := by
  let L : E →L[ℂ] ℂ := innerSL ℂ v
  have hspan : Submodule.span ℂ (Set.range χ) ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hinner i
  have htop := (Submodule.span ℂ (Set.range χ)).topologicalClosure_minimal
    hspan L.isClosed_ker
  rw [hdense] at htop
  have hv : L v = 0 := htop (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ E))
  exact inner_self_eq_zero.mp hv

theorem ergodic_of_dense_L2_eigenfunctions {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {σ : X → X}
    (hσ : MeasurePreserving σ μ μ) (i₀ : ι) (χ : ι → X → ℂ) (z : ι → ℂ)
    (hχ : ∀ i, MemLp (χ i) 2 μ)
    (hconst : χ i₀ =ᵐ[μ] fun _ => 1)
    (hdense : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ᵐ x ∂μ, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  classical
  refine ⟨hσ, ⟨?_⟩⟩
  intro s hs hinv
  let p : ℝ := μ.real s
  let u : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  let e : Lp ℂ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1
  have hσs : MeasurePreserving σ (μ.restrict s) (μ.restrict s) := by
    simpa only [hinv] using hσ.restrict_preimage hs
  have hpair : ∀ i,
      inner ℂ u ((hχ i).toLp (χ i)) = (p : ℂ) * inner ℂ e ((hχ i).toLp (χ i)) := by
    intro i
    have hfull : inner ℂ e ((hχ i).toLp (χ i)) = ∫ x, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
      exact integral_congr_ae (hχ i).coeFn_toLp
    have hset : inner ℂ u ((hχ i).toLp (χ i)) = ∫ x in s, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one]
      exact integral_congr_ae ((hχ i).coeFn_toLp.filter_mono (ae_mono Measure.restrict_le_self))
    rw [hfull, hset]
    by_cases hi : i = i₀
    · subst i
      rw [integral_congr_ae hconst,
        integral_congr_ae (hconst.filter_mono (ae_mono Measure.restrict_le_self))]
      simp [p]
    · have hzero := integral_eq_zero_of_eigenfunction hσ (hχ i).aestronglyMeasurable
        (hz i hi) (heigen i hi)
      have hzeros := integral_eq_zero_of_eigenfunction hσs
        (hχ i).aestronglyMeasurable.restrict (hz i hi)
        ((heigen i hi).filter_mono (ae_mono Measure.restrict_le_self))
      rw [hzero, hzeros, mul_zero]
  have heq : u = (p : ℂ) • e := by
    apply sub_eq_zero.mp
    apply eq_zero_of_dense_inner (u - (p : ℂ) • e)
      (fun i => (hχ i).toLp (χ i)) hdense
    intro i
    rw [inner_sub_left, inner_smul_left, hpair i]
    simp
  have huu : inner ℂ u u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have heu : inner ℂ e u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have hpalg := congrArg (fun v : Lp ℂ 2 μ => inner ℂ v u) heq
  rw [huu, inner_smul_left, heu] at hpalg
  have hpalg' := congrArg Complex.re hpalg
  simp at hpalg'
  have hp01 : p = 0 ∨ p = 1 := by
    have hpzero : p * (p - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hpzero with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sub_eq_zero.mp hp)
  apply eventuallyConst_set.mpr
  rcases hp01 with hp | hp
  · right
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (measureReal_eq_zero_iff (μ := μ)).mp hp
  · left
    rw [ae_iff]
    have hpc : μ.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr hp.symm
    exact (measureReal_eq_zero_iff (μ := μ)).mp hpc

theorem ergodic_of_dense_continuous_eigenfunctions {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    (i₀ : ι) (χ : ι → C(X, ℂ)) (z : ι → ℂ)
    (hconst : χ i₀ = 1)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ x, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  let hχ : ∀ i, MemLp (χ i) 2 μ := fun i => ContinuousMap.memLp μ ℂ (χ i)
  have hlp : (fun i => (hχ i).toLp (χ i)) =
      (fun i => ContinuousMap.toLp 2 μ ℂ (χ i)) := by
    funext i
    apply Lp.ext
    exact (hχ i).coeFn_toLp.trans (ContinuousMap.coeFn_toLp μ (χ i)).symm
  have hdenseLp : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤ := by
    rw [hlp]
    have hd := (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule hdense
    rw [Submodule.map_span, ← Set.range_comp'] at hd
    exact hd
  refine ergodic_of_dense_L2_eigenfunctions hσ i₀ (fun i => χ i) z hχ ?_ hdenseLp hz ?_
  · exact Eventually.of_forall fun x => by rw [hconst]; rfl
  · intro i hi
    exact Eventually.of_forall (heigen i hi)

end Invariant233.Characters

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductCharacters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators ComplexConjugate
open Set Algebra Submodule

variable {ι : Type*}

theorem characterPhase_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    characterPhase v (x + y) = characterPhase v x + characterPhase v y := by
  simp [characterPhase, Finsupp.sum_add]

theorem characterPhase_add_index (v w : ι →₀ ℤ) (x : ι → UnitAddCircle) :
    characterPhase (v + w) x = characterPhase v x + characterPhase w x := by
  classical
  simp [characterPhase, Finsupp.sum_add_index, add_zsmul]

theorem productCharacter_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    productCharacter v (x + y) = productCharacter v x * productCharacter v y := by
  simp [productCharacter, characterPhase_add, AddCircle.toCircle_add]

theorem productCharacter_add_index (v w : ι →₀ ℤ) :
    productCharacter (v + w) = productCharacter v * productCharacter w := by
  ext x
  simp [productCharacter, characterPhase_add_index, AddCircle.toCircle_add]

theorem productCharacter_neg (v : ι →₀ ℤ) :
    productCharacter (-v) = star (productCharacter v) := by
  ext x
  simp [productCharacter, characterPhase, Finsupp.sum_neg_index,
    Finsupp.sum_neg, AddCircle.toCircle_neg]
  exact Circle.coe_inv_eq_conj _

theorem productFourierAlgebra_separatesPoints :
    (productFourierAlgebra ι).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨productCharacter (Finsupp.single i 1),
    StarAlgebra.subset_adjoin ℂ _ ⟨Finsupp.single i 1, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hi
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Subtype.coe_injective
  simpa only [productCharacter_single_one] using heq

theorem productFourierAlgebra_closure_eq_top :
    (productFourierAlgebra ι).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    productFourierAlgebra_separatesPoints

theorem productFourierAlgebra_toSubmodule :
    (productFourierAlgebra ι).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (productCharacter (ι := ι))) := by
  classical
  rw [productFourierAlgebra, StarAlgebra.adjoin_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · intro f hf
    induction hf using Submonoid.closure_induction with
    | mem f hf =>
      rcases hf with hf | hf
      · exact hf
      · obtain ⟨v, hv⟩ := hf
        exact ⟨-v, by rw [productCharacter_neg, hv, star_star]⟩
    | one => exact ⟨0, productCharacter_zero⟩
    | mul f g hf hg ihf ihg =>
      obtain ⟨v, rfl⟩ := ihf
      obtain ⟨w, rfl⟩ := ihg
      exact ⟨v + w, productCharacter_add_index v w⟩
  · intro f hf
    exact Submonoid.subset_closure (Or.inl hf)

theorem span_productCharacter_closure_eq_top :
    (Submodule.span ℂ (Set.range (productCharacter (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← productFourierAlgebra_toSubmodule]
  exact congr_arg (fun A : StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) =>
    A.toSubalgebra.toSubmodule) productFourierAlgebra_closure_eq_top

theorem mul_sum_ne_int (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) (k : ℤ) :
    (q : ℝ) * v.sum (fun i z => (z : ℝ) * θ i) ≠ (k : ℝ) := by
  intro heq
  have hz : q • v = 0 := hθ (q • v) k (by
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    simpa only [Int.cast_mul, mul_assoc, Finsupp.sum, Finset.mul_sum] using heq)
  exact (smul_ne_zero hq hv) hz

theorem characterPhase_coe (v : ι →₀ ℤ) (θ : ι → ℝ) :
    characterPhase v (fun i => (θ i : UnitAddCircle)) =
      ((v.sum (fun i z => (z : ℝ) * θ i) : ℝ) : UnitAddCircle) := by
  change v.sum (fun i n => n • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (θ i)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (v.sum (fun i z => (z : ℝ) * θ i))
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [zsmul_eq_mul] using
    (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (v i) (θ i)).symm

theorem productCharacter_ne_one (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) :
    productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) ≠ 1 := by
  intro heq
  have hphase : characterPhase v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    apply Subtype.coe_injective
    simpa [productCharacter] using heq
  rw [characterPhase_coe, AddCircle.coe_eq_zero_iff] at hphase
  obtain ⟨k, hk⟩ := hphase
  apply mul_sum_ne_int θ hθ hv hq k
  simpa only [Finsupp.sum, Finset.mul_sum, zsmul_eq_mul, mul_one,
    mul_left_comm, mul_assoc] using hk.symm

theorem productCharacter_translation (v : ι →₀ ℤ) (θ : ι → ℝ) (q : ℤ)
    (x : ι → UnitAddCircle) :
    productCharacter v (fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) *
        productCharacter v x := by
  rw [mul_comm, ← productCharacter_add]
  congr 1

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductErgodicity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open MeasureTheory

variable {ι : Type*}

theorem integer_affine_independent {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (m : ℤ)
    (heq : v.sum (fun i z => (z : ℝ) * θ i) = m) : v = 0 := by
  by_contra hv
  exact (Invariant233.IndependentRotation.irrational_finsupp_int_sum hθ v hv).ne_int m heq

theorem measurePreserving_product_translation (a : ι → UnitAddCircle) :
    MeasurePreserving (fun x : ι → UnitAddCircle => x + a)
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : ι) : MeasurePreserving
      (fun x : UnitAddCircle => x + a i) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))).map
      (fun x i => x i + a i) = _
  rw [Measure.infinitePi_map_pi _ (fun i => (hcoord i).measurable)]
  simp only [(hcoord _).map_eq]

theorem product_rotation_integer_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {q : ℤ} (hq : q ≠ 0) :
    Ergodic (fun x : ι → UnitAddCircle =>
      fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  apply Invariant233.Characters.ergodic_of_dense_continuous_eigenfunctions
    (measurePreserving_product_translation (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    (0 : ι →₀ ℤ) productCharacter
    (fun v => productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    productCharacter_zero span_productCharacter_closure_eq_top
  · intro v hv
    exact productCharacter_ne_one θ (integer_affine_independent hθ) hv hq
  · intro v _ x
    exact productCharacter_translation v θ q x

theorem product_rotation_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ)) :
    Ergodic (fun x : ι → UnitAddCircle => fun i => x i + (θ i : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  simpa only [Int.cast_one, one_mul] using
    product_rotation_integer_ergodic hθ (q := 1) one_ne_zero

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductBaseDynamics
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductModel

open MeasureTheory

theorem rotation_ergodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) :
    Ergodic (rotation θ) baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_ergodic hθ

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

variable {a C hC ha hm}

theorem fieldDiagonal_mul_of_coeff_eq
    {b c : X → Weight} {D E : ℝ} {hD : 0 ≤ D} {hE : 0 ≤ E}
    {hb : ∀ x, ‖b x‖ ≤ D} {hc : ∀ x, ‖c x‖ ≤ E}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    {hp : ∀ k, AEStronglyMeasurable (fun x => c x k) μ}
    (heq : ∀ᵐ x ∂μ, ∀ k, c x k = a x k * b x k) :
    fieldDiagonal c E hE hc hp =
      fieldDiagonal a C hC ha hm * fieldDiagonal b D hD hb hn := by
  ext f
  filter_upwards [fieldDiagonal_coordinate_ae c E hE hc hp f,
    fieldDiagonal_coordinate_ae a C hC ha hm (fieldDiagonal b D hD hb hn f),
    fieldDiagonal_coordinate_ae b D hD hb hn f, heq] with x hx hy hz he
  apply lp.ext
  funext k
  change fieldDiagonal c E hE hc hp f x k =
    fieldDiagonal a C hC ha hm (fieldDiagonal b D hD hb hn f) x k
  rw [hx, hy, hz, he, mul_assoc]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCovariance
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem field_covariance {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F x * (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap =
        (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap *
          F (rotationIterate θ m x) := by
  let := HilbertModelSize.separable_of_countable_hilbertBasis
    (default : HilbertBasis ℤ ℂ Fiber)
  apply ae_all_iff.mpr
  intro m
  exact FieldTraceCyclic.ae_covariance_of_commute T _ F _ _
    (rotationIterate_measurePreserving θ m) hF
    (FieldTraceCyclic.shiftedPullback_ae _ _ _)
    (commute_shiftedPullback_of_mem_factor θ hT m)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductMultiplierFunctionalCalculus
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem vectorTrace_multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    vectorTrace traceVector (multiplier θ g C hC hg hb) = ∫ x, g x ∂baseMeasure := by
  change inner ℂ traceVector (multiplier θ g C hC hg hb traceVector) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : traceVector =ᵐ[baseMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 baseMeasure _
  filter_upwards [hv, multiplier_coordinates_ae θ g C hC hg hb traceVector] with x hv hm
  rw [hv, lp.inner_single_left]
  rw [hm 0, hv]
  simp
  congr 1
  funext i
  simp [Invariant233.ProductModel.rotationIterate]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductHilbert
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

theorem hilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ Hilbert :=
  HilbertModelSize.not_finiteDimensional_L2_l2 baseMeasure ℤ

instance hilbert_nontrivial : Nontrivial Hilbert := by
  cases subsingleton_or_nontrivial Hilbert with
  | inl h =>
    let : Subsingleton Hilbert := h
    exact False.elim (hilbert_not_finiteDimensional inferInstance)
  | inr h => exact h

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftCentrality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.WeightedShift

open MeasureTheory Filter

local notation "S" =>
  LinearIsometry.toContinuousLinearMap (LinearIsometryEquiv.toLinearIsometry (shift 1))

theorem forwardShift_single (j : ℤ) :
    S (lp.single 2 j (1 : ℂ)) = lp.single 2 (j + 1) (1 : ℂ) := by
  ext k
  change shift 1 (lp.single 2 j (1 : ℂ)) k =
    lp.single (E := fun _ : ℤ => ℂ) 2 (j + 1) (1 : ℂ) k
  rw [shift_apply]
  by_cases hk : k = j + 1
  · subst k
    simp
  · have hk' : k - 1 ≠ j := by omega
    simp [lp.single_apply, hk, hk']

theorem scalar_of_commute_diagonal_shift
    (A : Hilbert →L[ℂ] Hilbert) (w : Weight) (hw : Function.Injective w)
    (hD : Commute A (diagonal w)) (hS : Commute A S) :
    ∃ c : ℂ, A = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  exact FiberCentrality.scalar_of_commute_diagonal_and_shift
    A (diagonal w) S w hw (diagonal_apply w) forwardShift_single hD.eq hS.eq

theorem ae_eq_scalar_of_commute_diagonal_shift
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → Hilbert →L[ℂ] Hilbert) (w : X → Weight)
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hw : ∀ᵐ x ∂μ, Function.Injective (w x))
    (hD : ∀ᵐ x ∂μ, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂μ, Commute (A x) S)
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  apply FiberCentrality.ae_eq_scalar_of_ergodic_covariance
    μ σ hσ A S forwardShift_single hm _ hcov
  filter_upwards [hw, hD, hS] with x hwx hDx hSx
  exact scalar_of_commute_diagonal_shift (A x) (w x) hwx hDx hSx

theorem ae_eq_scalar_of_commute_irrational_diagonal_shift
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (σ : X → X)
    (hσ : Ergodic σ μ) (A : X → Hilbert →L[ℂ] Hilbert) (w : X → Weight)
    (θ : ℝ) (hθ : Irrational θ) (x₀ : X → AddCircle (1 : ℝ))
    (hphase : ∀ᵐ x ∂μ, ∀ k : ℤ,
      w x k = (AddCircle.toCircle (x₀ x + k • (θ : AddCircle (1 : ℝ))) : ℂ))
    (hm : NullMeasurable (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) μ)
    (hD : ∀ᵐ x ∂μ, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂μ, Commute (A x) S)
    (hcov : ∀ᵐ x ∂μ, S * A (σ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂μ, A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  apply ae_eq_scalar_of_commute_diagonal_shift μ σ hσ A w hm _ hD hS hcov
  filter_upwards [hphase] with x hx
  intro j k hjk
  apply FiberCentrality.injective_irrational_diagonal θ hθ (x₀ x)
  simpa only [hx] using hjk

end Invariant233.WeightedShift

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ActualRotationCentrality
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_nontrivial _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.WeightedShift

open MeasureTheory Filter

local notation "S" =>
  LinearIsometry.toContinuousLinearMap (LinearIsometryEquiv.toLinearIsometry (shift 1))

theorem ae_eq_scalar_over_product_rotation
    (θ : ℕ → ℝ) (hθ : ProductModel.JointlyRationallyIndependent θ)
    (i : ℕ) (A : ProductModel.Base → Hilbert →L[ℂ] Hilbert)
    (w : ProductModel.Base → Weight)
    (hphase : ∀ᵐ x ∂ProductModel.baseMeasure, ∀ k : ℤ,
      w x k = (AddCircle.toCircle (x i + k • (θ i : Invariant233.Circle)) : ℂ))
    (hm : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) ProductModel.baseMeasure)
    (hD : ∀ᵐ x ∂ProductModel.baseMeasure, Commute (A x) (diagonal (w x)))
    (hS : ∀ᵐ x ∂ProductModel.baseMeasure, Commute (A x) S)
    (hcov : ∀ᵐ x ∂ProductModel.baseMeasure,
      S * A (ProductModel.rotation θ x) = A x * S) :
    ∃ c : ℂ, ∀ᵐ x ∂ProductModel.baseMeasure,
      A x = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  exact ae_eq_scalar_of_commute_irrational_diagonal_shift
    ProductModel.baseMeasure (ProductModel.rotation θ)
    (ProductModel.rotation_ergodic hθ) A w (θ i)
    (Invariant233.IndependentRotation.irrational_coordinate hθ i)
    (fun x => x i) hphase hm hD hS hcov

end Invariant233.WeightedShift

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScalarity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.ProductModel

local notation "S" => LinearIsometry.toContinuousLinearMap
  (LinearIsometryEquiv.toLinearIsometry (WeightedShift.shift 1))

theorem scalar_of_mem_factor_central (θ : ℕ → ℝ)
    (hθ : JointlyRationallyIndependent θ) (T : Hilbert →L[ℂ] Hilbert)
    (hT : T ∈ factor θ)
    (hcentral : ∀ B : Hilbert →L[ℂ] Hilbert, B ∈ factor θ → Commute T B) :
    ∃ c : ℂ, T = c • (1 : Hilbert →L[ℂ] Hilbert) := by
  obtain ⟨A, hbound, hm, hrep, huniq⟩ := exists_unique_field hT
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hS : Commute T shiftOperator :=
    hcentral shiftOperator (subset_vonNeumannGenerated _ (Or.inl (Set.mem_singleton _)))
  have hAS : ∀ᵐ x ∂baseMeasure, Commute (A x) S :=
    DirectIntegral.ae_commute_of_represented_commute b T shiftOperator A (fun _ => S)
      hrep shiftOperator_ae hS
  let g : Base → ℂ := fun x => (AddCircle.toCircle (x 0) : ℂ)
  have hg : Measurable g := by
    exact (continuous_subtype_val.comp
      ((AddCircle.continuous_toCircle (T := (1 : ℝ))).comp
        (show Continuous (fun x : Base => x 0) from continuous_apply 0))).measurable
  have hb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    exact (Circle.norm_coe (AddCircle.toCircle (x 0))).le
  let D := multiplier θ g 1 (by norm_num) hg hb
  have hDmem : D ∈ factor θ := by
    apply subset_vonNeumannGenerated
    exact Or.inr ⟨g, 1, by norm_num, hg, hb, rfl⟩
  have hAD : ∀ᵐ x ∂baseMeasure,
      Commute (A x) (WeightedShift.diagonal (multiplierField θ g 1 hb x)) :=
    DirectIntegral.ae_commute_of_represented_commute b T D A
      (fun x => WeightedShift.diagonal (multiplierField θ g 1 hb x))
      hrep (multiplier_ae θ g 1 (by norm_num) hg hb) (hcentral D hDmem)
  have hmeas : NullMeasurable
      (fun x => A x (lp.single 2 (0 : ℤ) (1 : ℂ)) 0) baseMeasure :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hm (lp.single 2 (0 : ℤ) (1 : ℂ)))).measurable.nullMeasurable
  have hcov : ∀ᵐ x ∂baseMeasure, S * A (rotation θ x) = A x * S := by
    filter_upwards [field_covariance hT A hrep] with x hall
    have hx := hall 1
    have heq : rotationIterate θ 1 x = rotation θ x := by
      funext i
      simp only [rotationIterate, Int.cast_one, one_mul, rotation]
    rw [heq] at hx
    exact hx.symm
  apply DirectIntegral.scalar_of_representation_ae_scalar T A hrep
  apply WeightedShift.ae_eq_scalar_over_product_rotation θ hθ 0 A
    (multiplierField θ g 1 hb) _ hmeas hAD hAS hcov
  apply Eventually.of_forall
  intro x k
  change (AddCircle.toCircle (x 0 + (((k : ℝ) * θ 0 : ℝ) : Circle)) : ℂ) =
    (AddCircle.toCircle (x 0 + k • (θ 0 : Circle)) : ℂ)
  congr 3
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := k) (x := θ 0))

theorem factor_isFactor (θ : ℕ → ℝ) (hθ : JointlyRationallyIndependent θ) :
    IsFactor (factor θ) :=
  ⟨inferInstance, fun T hT hcentral => scalar_of_mem_factor_central θ hθ T hT hcentral⟩

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductDiffuse
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Invariant233.ProductModel

theorem borelSetProjection_mem (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    borelSetProjection θ s hs ∈ factor θ :=
  subset_vonNeumannGenerated _ (Or.inr ⟨_, _, _, _, _, rfl⟩)

theorem borelSetProjection_isStarProjection (θ : ℕ → ℝ) (s : Set Base)
    (hs : MeasurableSet s) : IsStarProjection (borelSetProjection θ s hs) := by
  constructor
  · change borelSetProjection θ s hs * borelSetProjection θ s hs = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_mul_of_coeff_eq
    exact Eventually.of_forall fun x k => by
      change s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) =
        s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) *
          s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x)
      by_cases hx : rotationIterate θ k x ∈ s <;> simp [hx]
  · change star (borelSetProjection θ s hs) = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_star_of_eq
    exact Eventually.of_forall fun x => lp.ext (funext fun k => by
      change s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) =
        star (s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x))
      by_cases hx : rotationIterate θ k x ∈ s <;> simp [hx])

theorem vectorTrace_borelSetProjection (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    vectorTrace traceVector (borelSetProjection θ s hs) = (baseMeasure.real s : ℂ) := by
  unfold borelSetProjection
  rw [vectorTrace_multiplier, integral_indicator hs, integral_const]
  simp [Measure.real]

theorem borelSetProjection_joint_kernel {ι : Type*} [Fintype ι]
    (θ : ℕ → ℝ) (s : ι → Set Base) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ x : Base, ∃ i, x ∈ s i) (v : Hilbert)
    (hv : ∀ i, borelSetProjection θ (s i) (hs i) v = 0) : v = 0 := by
  have hcoord : ∀ i, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (s i).indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) * v x k = 0 := by
    intro i
    have h := multiplier_coordinates_ae θ
      ((s i).indicator (fun _ => (1 : ℂ))) 1 zero_le_one
      (measurable_const.indicator (hs i)) (by intro x; by_cases hx : x ∈ s i <;> simp [hx]) v
    change ∀ᵐ x ∂baseMeasure, ∀ k,
      borelSetProjection θ (s i) (hs i) v x k = _ at h
    rw [hv i] at h
    filter_upwards [h, Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hz
    intro k
    simpa [hz] using (hx k).symm
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hz
  rw [hz]
  apply lp.ext
  funext k
  obtain ⟨i, hi⟩ := hcover (rotationIterate θ k x)
  simpa [hi] using hx i k

theorem factor_isDiffuse (θ : ℕ → ℝ) : IsDiffuseVonNeumannAlgebra (factor θ) := by
  classical
  apply isDiffuse_of_small_trace_separating_families (factor θ) traceVector (traceVector_faithfulTracial θ)
  intro ε hε
  have hsmall (x : Base) : ∃ U : Set Base, x ∈ U ∧ IsOpen U ∧ baseMeasure U < ENNReal.ofReal ε := by
    obtain ⟨U, hxU, hU, hm⟩ := isCompact_singleton.exists_isOpen_lt_of_lt
      (μ := baseMeasure) (K := {x}) (ENNReal.ofReal ε) (by
        have hz0 : circleMeasure {x 0} = 0 := by
          change volume {x 0} = 0
          rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
          norm_num
        have hz : baseMeasure {x} = 0 := by
          apply le_antisymm _ (by positivity)
          calc
            baseMeasure {x} ≤ baseMeasure ((fun y : Base => y 0) ⁻¹' {x 0}) := by
              apply measure_mono
              intro y hy
              change y 0 = x 0
              exact congrArg (fun z : Base => z 0) (Set.mem_singleton_iff.mp hy)
            _ = circleMeasure {x 0} := by
              exact (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) 0).measure_preimage
                (measurableSet_singleton (x 0)).nullMeasurableSet
            _ = 0 := hz0
        rw [hz]
        exact ENNReal.ofReal_pos.mpr hε)
    exact ⟨U, hxU (Set.mem_singleton x), hU, hm⟩
  choose U hxU hU hm using hsmall
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  let e := Fintype.equivFin t
  let s : Fin (Fintype.card t) → Set Base := fun i => U (e.symm i)
  have hs : ∀ i, MeasurableSet (s i) := fun i => (hU (e.symm i)).measurableSet
  refine ⟨Fintype.card t, fun i => borelSetProjection θ (s i) (hs i),
    fun i => borelSetProjection_mem θ (s i) (hs i),
    fun i => borelSetProjection_isStarProjection θ (s i) (hs i), ?_, ?_⟩
  · intro i
    rw [vectorTrace_borelSetProjection]
    change (baseMeasure (s i)).toReal < ε
    exact (ENNReal.toReal_lt_of_lt_ofReal (hm (e.symm i)))
  · apply borelSetProjection_joint_kernel θ s hs
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact ⟨e ⟨y, hy⟩, by simpa only [s, Equiv.symm_apply_apply] using hxy⟩

theorem factor_isTypeII1FactorWithVector_oai (θ : ℕ → ℝ) (hθ : JointlyRationallyIndependent θ) :
    IsTypeII1FactorWithVector (factor θ) traceVector :=
  ⟨factor_isFactor θ hθ, factor_isDiffuse θ, traceVector_faithfulTracial θ⟩

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.factor_isTypeII1FactorWithVector_oai := @OAI.Invariant233.ProductModel.factor_isTypeII1FactorWithVector_oai
