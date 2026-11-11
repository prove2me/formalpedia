-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:09.127855+00:00
-- url     : https://prove2.me/submissions/dd9ee6d9-a625-4848-a3d6-0a234b243a06

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CappedRatios
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

variable {X : Type*}

theorem continuousOn_capped_ratio [TopologicalSpace X]
    (F : X → ℝ) (Q : Set X) (hF : ContinuousOn F Q)
    (hFp : ∀ x ∈ Q, F x ≠ 0) (B : ℝ) :
    ContinuousOn (fun t : X × X => (Complex.ofReal (min B (F t.2 / F t.1)))) (Q ×ˢ Q) := by
  have hfst : ContinuousOn (fun t : X × X => F t.1) (Q ×ˢ Q) :=
    hF.comp continuous_fst.continuousOn (fun _ ht => ht.1)
  have hsnd : ContinuousOn (fun t : X × X => F t.2) (Q ×ˢ Q) :=
    hF.comp continuous_snd.continuousOn (fun _ ht => ht.2)
  have hratio : ContinuousOn (fun t : X × X => F t.2 / F t.1) (Q ×ˢ Q) :=
    hsnd.div hfst (fun t ht => hFp t.1 ht.1)
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.inf hratio)

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Invariant233.CompactTransfer

theorem measure_compl_le_of_tendsto {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hbound : ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun i => (νs i : Measure X) Set.univ) L
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hν.mass
  have hparts : ∀ᶠ i in L,
      (νs i : Measure X) Set.univ ≤ (νs i : Measure X) K + ε := by
    filter_upwards [hbound] with i hi
    rw [← measure_add_measure_compl hK.measurableSet]
    exact add_le_add le_rfl hi
  have hlim := Filter.limsup_le_limsup hparts
  rw [hmass.limsup_eq,
    limsup_add_const L (fun i => (νs i : Measure X) K) ε
      (by isBoundedDefault) (by isBoundedDefault)] at hlim
  have htotal := hlim.trans (add_le_add
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hν hK) le_rfl)
  rw [measure_compl hK.measurableSet (measure_ne_top _ _), tsub_le_iff_right]
  simpa only [add_comm] using htotal

theorem ae_mem_of_closed_approximation {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {S : Set X}
    (happrox : ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X,
      IsClosed K ∧ K ⊆ S ∧ ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ S := by
  apply ae_iff.mpr
  change (ν : Measure X) Sᶜ = 0
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, hKS, hbound⟩ := happrox ε hε
  simpa using
    (measure_mono (Set.compl_subset_compl.mpr hKS)).trans
      (measure_compl_le_of_tendsto hν hK hbound)

end Invariant233.CompactTransfer

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

end Invariant233.EndpointLoss

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InvariantConullCore
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233

theorem exists_invariant_conull_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧
      (∀ᵐ x ∂μ, x ∈ t) ∧ ∀ k, σ k ⁻¹' t = t := by
  let t : Set X := ⋂ k : ℤ, σ k ⁻¹' s
  have ht_mem : ∀ x, x ∈ t ↔ ∀ k, σ k x ∈ s := by
    intro x
    simp only [t, mem_iInter, mem_preimage]
  refine ⟨t, MeasurableSet.iInter (fun k ↦ hs.preimage (hmp k).measurable), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hzero] using (ht_mem x).mp hx 0
  · have h : ∀ᵐ x ∂μ, ∀ k : ℤ, σ k x ∈ s :=
      ae_all_iff.mpr (fun k ↦ (hmp k).quasiMeasurePreserving.ae hfull)
    exact h.mono fun x hx ↦ (ht_mem x).mpr hx
  · intro k
    ext x
    change σ k x ∈ t ↔ x ∈ t
    rw [ht_mem, ht_mem]
    constructor
    · intro hx n
      have h := hx (n - k)
      rw [← hadd] at h
      rw [← add_sub_assoc, add_comm k n, add_sub_cancel_right] at h
      exact h
    · intro hx n
      rw [← hadd]
      exact hx (k + n)

theorem exists_invariant_conull_property
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, P x) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨u, hsub, hu, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  have hfull : ∀ᵐ x ∂μ, x ∈ uᶜ := by
    rw [ae_iff]
    simpa using hnull
  obtain ⟨t, ht, htu, htf, hinv⟩ :=
    exists_invariant_conull_subset σ hzero hadd hmp hu.compl hfull
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx
  by_contra hbad
  exact htu hx (hsub hbad)

theorem exists_invariant_conull_forall
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : I → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, ∀ k i, P i (σ k x)) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨t, ht, htf, hprop, hinv⟩ :=
    exists_invariant_conull_property σ hzero hadd hmp
      (fun x ↦ ∀ i, P i x) (ae_all_iff.mpr hP)
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx k i
  apply hprop (σ k x) _ i
  change x ∈ σ k ⁻¹' t
  rw [hinv]
  exact hx

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Invariant233.EndpointLoss

variable {X ι : Type*} [MeasurableSpace X]

theorem uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X)
    (hfinite : ∀ i, IsFiniteMeasure (ν i)) (H : ℝ)
    (hbound : ∀ i A, MeasurableSet A → (ν i).real A ≤ H * Real.sqrt (μ.real A)) :
    UniformlyAbsolutelyContinuous μ ν := by
  intro ε hε
  have he : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hB : 0 < |H| + 1 := by positivity
  have hd : 0 < (ε : ℝ) / (|H| + 1) := div_pos he hB
  refine ⟨⟨((ε : ℝ) / (|H| + 1)) ^ 2, sq_nonneg _⟩, ?_, ?_⟩
  · change 0 < ((ε : ℝ) / (|H| + 1)) ^ 2
    positivity
  · intro A hA hsmall i
    let := hfinite i
    have hreal : μ.real A < ((ε : ℝ) / (|H| + 1)) ^ 2 := by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top μ A) ENNReal.coe_ne_top).2 hsmall
    have hsqrt : Real.sqrt (μ.real A) < (ε : ℝ) / (|H| + 1) := by
      have ht := Real.sqrt_lt_sqrt (measureReal_nonneg) hreal
      simpa only [Real.sqrt_sq hd.le] using ht
    have hH : H ≤ |H| + 1 := by linarith [le_abs_self H]
    have hν : (ν i).real A < (ε : ℝ) := calc
      (ν i).real A ≤ H * Real.sqrt (μ.real A) := hbound i A hA
      _ ≤ (|H| + 1) * Real.sqrt (μ.real A) :=
        mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)
      _ < (|H| + 1) * ((ε : ℝ) / (|H| + 1)) :=
        mul_lt_mul_of_pos_left hsqrt hB
      _ = (ε : ℝ) := mul_div_cancel₀ _ hB.ne'
    exact (ENNReal.toReal_lt_toReal (measure_ne_top (ν i) A) ENNReal.coe_ne_top).1 hν

theorem uniformlyAbsolutelyContinuous_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (h : ι → X → ℝ)
    (hh : ∀ i, MemLp (h i) 2 μ) (hn : ∀ i, 0 ≤ᵐ[μ] h i) (H : ℝ)
    (hb : ∀ i, Real.sqrt (∫ x, h i x ^ 2 ∂μ) ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (h i x))) := by
  have hfin : ∀ i, IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal ((hh i).integrable (by norm_num)).2
  apply uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound μ _ hfin H
  intro i A hA
  exact (withDensity_measureReal_le_sqrt μ (hh i) (hn i) hA).trans
    (mul_le_mul_of_nonneg_right (hb i) (Real.sqrt_nonneg _))

theorem uniformlyAbsolutelyContinuous_Lp_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (f : ι → Lp ℝ 2 μ)
    (hn : ∀ i, 0 ≤ᵐ[μ] (f i : X → ℝ)) (H : ℝ) (hb : ∀ i, ‖f i‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  apply uniformlyAbsolutelyContinuous_withDensity μ (fun i => f i) (fun i => Lp.memLp (f i)) hn H
  intro i
  simpa only [sqrt_integral_sq_eq_norm] using hb i

theorem uniformlyAbsolutelyContinuous_of_Lp_densities
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X) (H : ℝ)
    (hν : ∀ i, ∃ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] (f : X → ℝ)) ∧
      ν i = μ.withDensity (fun x => ENNReal.ofReal (f x)) ∧ ‖f‖ ≤ H) :
    UniformlyAbsolutelyContinuous μ ν := by
  choose f hn heq hb using hν
  have hfun : ν = fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x)) :=
    funext heq
  rw [hfun]
  exact uniformlyAbsolutelyContinuous_Lp_withDensity μ f hn H hb

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.OrbitInvariance

section Ring
variable {A : Type*} [Ring A] {p T : A}

theorem invariant_iff_compression :
    (1 - p) * T * p = 0 ↔ p * T * p = T * p := by
  rw [sub_mul, one_mul, sub_mul]
  exact sub_eq_zero.trans eq_comm

theorem invariant_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) :
    (1 - p) * T ^ n * p = 0 := by
  have hTp : p * T * p = T * p := invariant_iff_compression.mp hT
  apply invariant_iff_compression.mpr
  induction n with
  | zero => simpa using hp.eq
  | succ n ih =>
    calc
      p * T ^ (n + 1) * p = p * T ^ n * (T * p) := by rw [pow_succ]; simp [mul_assoc]
      _ = p * T ^ n * (p * T * p) := by rw [hTp]
      _ = (p * T ^ n * p) * T * p := by simp [mul_assoc]
      _ = (T ^ n * p) * T * p := by rw [ih]
      _ = T ^ n * (p * T * p) := by simp [mul_assoc]
      _ = T ^ n * (T * p) := by rw [hTp]
      _ = T ^ (n + 1) * p := by rw [pow_succ]; simp [mul_assoc]

theorem orbit_inclusion (W : Aˣ) (D : A)
    (h : (1 - p) * ((W : A) * D) * p = 0) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  have heq : ↑(W⁻¹) * ((1 - p) * ((W : A) * D) * p) =
      (1 - (↑(W⁻¹) * p * (W : A))) * D * p := by
    simp only [mul_sub, sub_mul, one_mul, mul_assoc]
    simp
  rw [← heq, h, mul_zero]

theorem orbit_inclusion_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) (W : Aˣ) (D : A)
    (hfactor : T ^ n = (W : A) * D) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  apply orbit_inclusion W D
  rw [← hfactor]
  exact invariant_pow hp hT n

end Ring


end Invariant233.OrbitInvariance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldMeasurability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.StrongField

open MeasureTheory Filter
open scoped Topology

variable {X ι H F : Type*} [MeasurableSpace X] [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem stronglyMeasurable_of_coordinates (b : HilbertBasis ι ℂ H)
    {v : X → H} (hv : ∀ i, StronglyMeasurable fun x => b.repr (v x) i) :
    StronglyMeasurable v := by
  classical
  let approximant : Finset ι → X → H := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • b i
  have hm (s : Finset ι) : StronglyMeasurable (approximant s) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (hv i).smul_const (b i)
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) hm
  apply tendsto_pi_nhds.mpr
  intro x
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant] using b.hasSum_repr (v x)

theorem stronglyMeasurable_adjoint_apply_of_columns [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] H)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i)) (v : H) :
    StronglyMeasurable fun x => (A x).adjoint v := by
  apply stronglyMeasurable_of_coordinates b
  intro i
  simp only [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right]
  exact (continuous_id.inner continuous_const).comp_stronglyMeasurable (hA i)

end Invariant233.StrongField

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldOperator
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E F G : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable (A : X → E →L[ℂ] F) (C : ℝ)
  (hA : ∀ x, ‖A x‖ ≤ C)
  (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)

theorem fieldOperator_ae (f : Lp E 2 μ) :
    fieldOperator A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldOperatorVec_ae A C hA hm f

variable {A C hA hm}

theorem fieldOperator_comp_of_ae_eq
    {B : X → F →L[ℂ] G} {P : X → E →L[ℂ] G} {D R : ℝ}
    {hB : ∀ x, ‖B x‖ ≤ D} {hP : ∀ x, ‖P x‖ ≤ R}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    {hp : ∀ v, AEStronglyMeasurable (fun x => P x v) μ}
    (heq : P =ᵐ[μ] fun x => (B x).comp (A x)) :
    fieldOperator P R hP hp =
      (fieldOperator B D hB hn).comp (fieldOperator A C hA hm) := by
  ext f
  filter_upwards [fieldOperator_ae P R hP hp f,
    fieldOperator_ae B D hB hn (fieldOperator A C hA hm f),
    fieldOperator_ae A C hA hm f, heq] with x hx hy hz he
  change fieldOperator P R hP hp f x =
    fieldOperator B D hB hn (fieldOperator A C hA hm f) x
  rw [hx, hy, hz, he]
  rfl

theorem fieldOperator_ae_eq_of_eq [IsFiniteMeasure μ] [SeparableSpace E]
    {B : X → E →L[ℂ] F} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : fieldOperator A C hA hm = fieldOperator B D hB hn) : A =ᵐ[μ] B := by
  have hpoint (v : E) : ∀ᵐ x ∂μ, A x v = B x v := by
    have heqv := congrArg (fun T : Lp E 2 μ →L[ℂ] Lp F 2 μ => T (Lp.const 2 μ v)) heq
    have hae : fieldOperator A C hA hm (Lp.const 2 μ v) =ᵐ[μ]
        fieldOperator B D hB hn (Lp.const 2 μ v) := by rw [heqv]
    filter_upwards [fieldOperator_ae A C hA hm (Lp.const 2 μ v),
      fieldOperator_ae B D hB hn (Lp.const 2 μ v), Lp.coeFn_const 2 μ v, hae]
      with x hx hy hv he
    simpa only [hx, hy, hv, Function.const_apply] using he
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (denseSeq E n) = B x (denseSeq E n) :=
    ae_all_iff.mpr fun n => hpoint (denseSeq E n)
  filter_upwards [hseq] with x hx
  have hfunctions : (A x : E → F) = (B x : E → F) :=
    (denseRange_denseSeq E).equalizer (A x).continuous (B x).continuous (funext hx)
  exact DFunLike.ext' hfunctions

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : X → E →L[ℂ] F} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem fieldOperator_adjoint_of_ae_eq
    {B : X → F →L[ℂ] E} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : B =ᵐ[μ] fun x => ContinuousLinearMap.adjoint (A x)) :
    fieldOperator B D hB hn = ContinuousLinearMap.adjoint (fieldOperator A C hA hm) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldOperator_ae B D hB hn f,
    fieldOperator_ae A C hA hm g, heq] with x hx hy he
  rw [hx, hy, he]
  exact (A x).adjoint_inner_left (g x) (f x)

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldProjections
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SeparableSpace E]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem ae_isIdempotentElem_of_fieldOperator (hC : 0 ≤ C)
    (hP : IsIdempotentElem (fieldOperator A C hA hm)) :
    ∀ᵐ x ∂μ, IsIdempotentElem (A x) := by
  have hAA : ∀ x, ‖A x * A x‖ ≤ C * C := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul (hA x) (hA x) (norm_nonneg _) hC)
  have hmAA : ∀ v, AEStronglyMeasurable (fun x => (A x * A x) v) μ := fun v =>
    apply_aestronglyMeasurable A hm (hm v)
  have hmul : fieldOperator (fun x => A x * A x) (C * C) hAA hmAA =
      fieldOperator A C hA hm * fieldOperator A C hA hm :=
    fieldOperator_comp_of_ae_eq (Filter.Eventually.of_forall fun x => rfl)
  have hfield := fieldOperator_ae_eq_of_eq (hmul.trans hP.eq)
  exact hfield

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeparableSpace E] [Countable ι]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}

theorem ae_isSelfAdjoint_of_fieldOperator (b : HilbertBasis ι ℂ E)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsSelfAdjoint (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsSelfAdjoint (A x) := by
  have hB : ∀ x, ‖star (A x)‖ ≤ C := by
    intro x
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact hA x
  have hn : ∀ v, AEStronglyMeasurable (fun x => star (A x) v) μ := by
    intro v
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (StrongField.stronglyMeasurable_adjoint_apply_of_columns b A
        (fun i => hm (b i)) v).aestronglyMeasurable
  have hglobal : fieldOperator (fun x => star (A x)) C hB hn =
      star (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable)) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact fieldOperator_adjoint_of_ae_eq (Filter.Eventually.of_forall fun x =>
      ContinuousLinearMap.star_eq_adjoint (A x))
  exact fieldOperator_ae_eq_of_eq (hglobal.trans hP.star_eq)

theorem ae_isStarProjection_of_fieldOperator (b : HilbertBasis ι ℂ E) (hC : 0 ≤ C)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsStarProjection (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsStarProjection (A x) := by
  filter_upwards [ae_isIdempotentElem_of_fieldOperator hC hP.isIdempotentElem,
    ae_isSelfAdjoint_of_fieldOperator b hm hP.isSelfAdjoint] with x hid hself
  exact ⟨hid, hself⟩

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarMultiplierFields
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [IsFiniteMeasure μ]

variable {ι : Type*} [Countable ι] [CompleteSpace E]

omit [IsFiniteMeasure μ] [CompleteSpace E] in

theorem separableSpace_of_countable_hilbertBasis (b : HilbertBasis ι ℂ E) :
    TopologicalSpace.SeparableSpace E := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hs := ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span] at hs
  exact hs

theorem scalar_multiplier_fields_complete (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) ∧
      (∀ f : Lp E 2 μ, A.adjoint f =ᵐ[μ] fun x => (F x).adjoint (f x)) ∧
      (∀ (B : Lp E 2 μ →L[ℂ] Lp E 2 μ) (G : X → E →L[ℂ] E),
        (∀ f : Lp E 2 μ, B f =ᵐ[μ] fun x => G x (f x)) →
        ∀ f : Lp E 2 μ, (A * B) f =ᵐ[μ] fun x => (F x * G x) (f x)) ∧
      (IsStarProjection A → ∀ᵐ x ∂μ, IsStarProjection (F x)) := by
  let := separableSpace_of_countable_hilbertBasis b
  obtain ⟨F, hnorm, hmeas, hrep, huniq⟩ := exists_unique_field_of_commutes b A hA
  have hAT : A = DirectIntegral.fieldOperator F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hrep f).trans (DirectIntegral.fieldOperatorVec_ae F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) f).symm
  refine ⟨F, hnorm, hmeas, hrep, huniq, ?_, ?_, ?_⟩
  · have hnormAdj : ∀ x, ‖(F x).adjoint‖ ≤ ‖A‖ := by
      intro x
      simpa only [LinearIsometryEquiv.norm_map] using hnorm x
    have hmeasAdj : ∀ v, AEStronglyMeasurable (fun x => (F x).adjoint v) μ := by
      intro v
      exact (StrongField.stronglyMeasurable_adjoint_apply_of_columns b F
        (fun i => hmeas (b i)) v).aestronglyMeasurable
    have hAdj : DirectIntegral.fieldOperator (fun x => (F x).adjoint) ‖A‖ hnormAdj hmeasAdj =
        A.adjoint := by
      calc
        _ = (DirectIntegral.fieldOperator F ‖A‖ hnorm
            (fun v => (hmeas v).aestronglyMeasurable)).adjoint :=
          DirectIntegral.fieldOperator_adjoint_of_ae_eq
            (Filter.Eventually.of_forall fun x => rfl)
        _ = A.adjoint := congrArg ContinuousLinearMap.adjoint hAT.symm
    intro f
    rw [← hAdj]
    exact DirectIntegral.fieldOperator_ae _ _ _ _ f
  · intro B G hG f
    filter_upwards [hrep (B f), hG f] with x hx hy
    change A (B f) x = (F x) (G x (f x))
    rw [hx, hy]
  · intro hP
    have hPT : IsStarProjection (DirectIntegral.fieldOperator (μ := μ) F ‖A‖ hnorm
        (fun v => (hmeas v).aestronglyMeasurable)) := by
      rw [← hAT]
      exact hP
    exact DirectIntegral.ae_isStarProjection_of_fieldOperator b (norm_nonneg A) hmeas hPT

end Invariant233.L2Multiplication

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RepresentedInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_invariance_of_represented
    (b : HilbertBasis ι ℂ E)
    (p T : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (P W : X → E →L[ℂ] E)
    (hp : ∀ f : Lp E 2 μ, p f =ᵐ[μ] fun x => P x (f x))
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => W x (f x))
    (hinv : (1 - p) * T * p = 0) :
    ∀ᵐ x ∂μ, (1 - P x) * W x * P x = 0 := by
  have hzero : ∀ f : Lp E 2 μ, (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) f =ᵐ[μ]
      fun x => ((1 - P x) * W x * P x) (f x) := by
    intro f
    have hfix : T (p f) = p (T (p f)) := by
      have h := congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A f) hinv
      simpa only [mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, zero_apply, sub_eq_zero] using h
    filter_upwards [hp f, hT (p f), hp (T (p f)), Lp.coeFn_zero E 2 μ]
      with x hpf hTf hpTf h0
    change (0 : Lp E 2 μ) x = _
    rw [h0]
    have heq : W x (P x (f x)) = P x (W x (P x (f x))) := by
      calc
        W x (P x (f x)) = T (p f) x := by rw [hTf, hpf]
        _ = p (T (p f)) x := congrArg (fun g : Lp E 2 μ => g x) hfix
        _ = P x (W x (P x (f x))) := by rw [hpTf, hTf, hpf]
    change (0 : E) = W x (P x (f x)) - P x (W x (P x (f x)))
    exact (sub_eq_zero.mpr heq).symm
  have huniq := field_unique_of_representation b
    (0 : Lp E 2 μ →L[ℂ] Lp E 2 μ) (fun x => (1 - P x) * W x * P x)
    (fun _ => 0) hzero (fun f => by
      filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
      change (0 : Lp E 2 μ) x = (0 : E)
      exact hx)
  exact huniq

end Invariant233.L2Multiplication

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SimultaneousLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Topology
open scoped ENNReal

namespace Invariant233.SimultaneousLusin

theorem continuousOn_of_finer_compact {X Y : Type*}
    [t : TopologicalSpace X] [hT2 : T2Space X] [TopologicalSpace Y]
    {t' : TopologicalSpace X} (hle : t' ≤ t)
    {K : Set X} (hK : @IsCompact X t' K) {f : X → Y}
    (hf : @Continuous X Y t' _ f) : @ContinuousOn X Y t _ f K := by
  apply (@continuousOn_iff_isClosed X Y t _ f K).2
  intro s hs
  have hC : @IsCompact X t' (K ∩ f ⁻¹' s) :=
    hK.inter_right (hs.preimage hf)
  have hC' : @IsCompact X t (K ∩ f ⁻¹' s) := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t (K ∩ f ⁻¹' s) id hC (continuous_id_of_le hle))
  exact ⟨K ∩ f ⁻¹' s, @IsCompact.isClosed X t hT2 _ hC',
    by ext x; simp [and_comm]⟩

theorem exists_compact_continuousOn {X Y : Type*}
    [t : TopologicalSpace X] [hPolish : PolishSpace X]
    [m : MeasurableSpace X] [hBorel : BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hfc, hP'⟩ := hf.exists_continuous
  have hB' : @BorelSpace X t' m := by
    constructor
    exact hBorel.measurable_eq.trans
      (MeasureTheory.borel_eq_borel_of_le hP' hPolish hle).symm
  let : TopologicalSpace X := t'
  let : PolishSpace X := hP'
  let : BorelSpace X := hB'
  obtain ⟨K, -, hK, hsmall⟩ :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set X)).exists_isCompact_sdiff_lt
      (measure_ne_top μ Set.univ) hε
  have hKold : @IsCompact X t K := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  refine ⟨K, hKold, ?_, ?_⟩
  · simpa only [← compl_eq_univ_sdiff] using hsmall
  · exact @continuousOn_of_finer_compact X Y t inferInstance _ t' hle K hK f hfc

end Invariant233.SimultaneousLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongContinuityFromColumns
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology

namespace Invariant233.StrongContinuityFromColumns

theorem continuous_apply_of_dense {𝕜 X E F : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) {s : Set E} (hs : Dense s)
    (hcont : ∀ v ∈ s, Continuous (fun x => A x v)) (v : E) :
    Continuous (fun x => A x v) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 3 * (C + 1) := by positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hden)
  have hvw' : C * dist v w < ε / 3 := by
    have hdist : 0 ≤ dist v w := dist_nonneg
    have hlt : dist v w * (3 * (C + 1)) < ε :=
      (lt_div_iff₀ hden).mp hvw
    nlinarith
  have hevent : ∀ᶠ y in 𝓝 x, dist (A y w) (A x w) < ε / 3 :=
    Metric.tendsto_nhds.mp (hcont w hw).continuousAt (ε / 3) (by positivity)
  filter_upwards [hevent] with y hy
  have hleft : dist (A y v) (A y w) ≤ C * dist v w := by
    calc
      dist (A y v) (A y w) ≤ ‖A y‖ * dist v w := (A y).lipschitz.dist_le_mul v w
      _ ≤ C * dist v w := mul_le_mul_of_nonneg_right (hbound y) dist_nonneg
  have hright : dist (A x w) (A x v) ≤ C * dist v w := by
    calc
      dist (A x w) (A x v) ≤ ‖A x‖ * dist w v := (A x).lipschitz.dist_le_mul w v
      _ ≤ C * dist w v := mul_le_mul_of_nonneg_right (hbound x) dist_nonneg
      _ = C * dist v w := by rw [dist_comm w v]
  have htri := dist_triangle4 (A y v) (A y w) (A x w) (A x v)
  linarith

theorem continuous_apply_of_dense_span {𝕜 X E F ι : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : ι → E)
    (hb : (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_apply_of_dense A hC hbound
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr hb) _ v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hcont i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz hwc hzc =>
      simpa only [map_add, Pi.add_def] using hwc.add hzc
  | smul c w hw hwc =>
      simpa only [map_smul, Pi.smul_def] using hwc.const_smul c

theorem continuous_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) :=
  continuous_apply_of_dense_span A hC hbound b b.dense_span hcont v

theorem continuousOn_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) {Q : Set X}
    (hbound : ∀ x ∈ Q, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, ContinuousOn (fun x => A x (b i)) Q) (v : E) :
    ContinuousOn (fun x => A x v) Q := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_apply_of_hilbertBasis (fun x : Q => A x) hC
    (fun x => hbound x x.property) b (fun i => (hcont i).domRestrict) v

end Invariant233.StrongContinuityFromColumns

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open Filter Topology

variable {𝕜 E F G ι X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [TopologicalSpace X]

theorem strong_continuous_of_dense_of_bounded
    {A : X → E →L[𝕜] F} {s : Set E} {C : ℝ}
    (hs : Dense s) (hA : ∀ w ∈ s, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M] <;> positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hM)
  refine ⟨(fun x => A x w), hA w hw, ?_⟩
  intro x
  apply hsub
  calc
    dist (A x v) (A x w) ≤ ‖A x‖ * dist v w := (A x).dist_le_opNorm v w
    _ ≤ M * dist v w := mul_le_mul_of_nonneg_right
      ((hC x).trans ((le_max_left C 0).trans (by dsimp [M]; exact le_add_of_nonneg_right zero_le_one)))
      (dist_nonneg)
    _ < ε := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw

theorem strong_continuous_of_dense_span_of_bounded
    {A : X → E →L[𝕜] F} {b : ι → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ i, Continuous (fun x => A x (b i)))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply strong_continuous_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hA i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz ihw ihz =>
      have h : Continuous (fun x => A x w + A x z) :=
        Continuous.add (f := fun x => A x w) (g := fun x => A x z) ihw ihz
      simpa only [map_add] using h
  | smul c w hw ihw =>
      have h : Continuous (fun x => c • A x w) :=
        Continuous.const_smul (g := fun x => A x w) ihw c
      simpa only [map_smul] using h

theorem strong_continuous_comp_of_bounded
    {A : X → F →L[𝕜] G} {B : X → E →L[𝕜] F} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hB : ∀ v, Continuous (fun x => B x v))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => ((A x).comp (B x)) v) := by
  exact continuous_apply_of_strong_continuous_of_bounded
    (A := A) (v := fun x => B x v) hA hC (hB v)

theorem isClosed_zero_set_of_strong_continuous
    {A : X → E →L[𝕜] F}
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IsClosed {x | A x = 0} := by
  have heq : {x | A x = 0} = ⋂ v : E, {x | A x v = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx v
      simp [hx]
    · intro hx
      ext v
      exact hx v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_eq (hA v) continuous_const

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped ENNReal

namespace Invariant233.StrongLusin

theorem exists_compact_strong_and_continuousOn {𝕜 X E F ι J : Type*}
    {Y : J → Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [∀ j, TopologicalSpace (Y j)] [∀ j, MeasurableSpace (Y j)]
    [∀ j, OpensMeasurableSpace (Y j)] [∀ j, SecondCountableTopology (Y j)]
    [Countable ι] [Countable J] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, Measurable (fun x => A x (b i)))
    (g : ∀ j, X → Y j) (hg : ∀ j, Measurable (g j))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      (∀ v : E, ContinuousOn (fun x => A x v) Q) ∧
      ∀ j, ContinuousOn (g j) Q := by
  have hmeas : Measurable (fun x => ((fun i => A x (b i)), (fun j => g j x))) :=
    (Measurable.of_eval hcolumns).prodMk (Measurable.of_eval hg)
  obtain ⟨Q, hQ, hsmall, hcont⟩ :=
    SimultaneousLusin.exists_compact_continuousOn μ hmeas hε
  refine ⟨Q, hQ, hsmall, ?_, continuousOn_pi.mp hcont.snd⟩
  exact fun v => StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
    (fun x _ => hbound x) b (continuousOn_pi.mp hcont.fst) v

end Invariant233.StrongLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularMarginals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace Invariant233.ProductModel

private theorem rep_measurable_p1 : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

private theorem rep_bounds (x : Circle) :
    0 ≤ circleRepresentative x ∧ circleRepresentative x < 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco (1 : ℝ) 0 x).property

private theorem rep_preserving : MeasurePreserving circleRepresentative circleMeasure
    (volume.restrict (Ico (0 : ℝ) 1)) :=
  CocycleSupport.measurePreserving_circleRepresentative

theorem circleRepresentative_upper_tail (r : ℝ) (hr : 0 ≤ r) :
    circleMeasure {x | r < circleRepresentative x} = ENNReal.ofReal (1 - r) := by
  change circleMeasure (circleRepresentative ⁻¹' Ioi r) = _
  rw [rep_preserving.measure_preimage measurableSet_Ioi.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ioi]
  have hset : Ioi r ∩ Ico (0 : ℝ) 1 = Ioo r 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ico, mem_Ioo]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.1, le_trans hr hx.1.le, hx.2⟩
  rw [hset, Real.volume_Ioo]

theorem circleRepresentative_lower_tail (r : ℝ) (hr : r ≤ 1) :
    circleMeasure {x | circleRepresentative x < r} = ENNReal.ofReal r := by
  change circleMeasure (circleRepresentative ⁻¹' Iio r) = _
  rw [rep_preserving.measure_preimage measurableSet_Iio.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Iio]
  have hset : Iio r ∩ Ico (0 : ℝ) 1 = Ico 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · tauto
    · intro hx
      exact ⟨hx.2, hx.1, lt_of_lt_of_le hx.2 hr⟩
  rw [hset, Real.volume_Ico, sub_zero]

private theorem event_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  simp only [triangularEvent, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt
    (rep_measurable_p1.comp ((measurable_pi_apply i).comp measurable_fst))
    (rep_measurable_p1.comp ((measurable_pi_apply i).comp measurable_snd))

theorem triangularEvent_fiber_mass (I : Finset ℕ) (x : Base) :
    baseMeasure (Prod.mk x ⁻¹' triangularEvent I) =
      ENNReal.ofReal (triangularFirstDensity I x) := by
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure))
    ((I : Set ℕ).pi (fun i => {z | circleRepresentative (x i) < circleRepresentative z})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_lt measurable_const rep_measurable_p1)]
  simp_rw [circleRepresentative_upper_tail _ (rep_bounds _).1]
  rw [triangularFirstDensity, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact sub_nonneg.mpr (rep_bounds (x i)).2.le

theorem fst_restrict_prod_eq_withDensity {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite ν] (E : Set (α × β)) (hE : MeasurableSet E) :
    ((μ.prod ν).restrict E).map Prod.fst =
      μ.withDensity (fun x => ν (Prod.mk x ⁻¹' E)) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    Measure.restrict_apply (measurable_fst hs),
    Measure.prod_apply ((measurable_fst hs).inter hE),
    withDensity_apply _ hs, ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [hx, Set.preimage, Set.indicator_of_mem]
  · simp [hx, Set.preimage, Set.indicator_of_notMem]

theorem triangularLaw_first_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) := by
  have hm : Measurable (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2)) := by
    refine measurable_fst.prodMk (Measurable.of_eval fun index => ?_)
    by_cases hi : index ∈ I
    · simpa [selectedEndpoint, hi, Function.comp_def] using
        (measurable_pi_apply index).comp (measurable_snd : Measurable (Prod.snd : EndpointPair → Base))
    · simpa [selectedEndpoint, hi, Function.comp_def] using
        (measurable_pi_apply index).comp (measurable_fst : Measurable (Prod.fst : EndpointPair → Base))
  rw [triangularLaw, Measure.map_map measurable_fst hm]
  change ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).map Prod.fst = _
  rw [fst_restrict_prod_eq_withDensity _ _ _ (event_measurable I)]
  congr 1
  funext x
  exact triangularEvent_fiber_mass I x

theorem reversedTriangularEvent_fiber_mass (I : Finset ℕ) (x : Base) :
    baseMeasure {z : Base | ∀ i ∈ I,
      circleRepresentative (z i) < circleRepresentative (x i)} =
      ENNReal.ofReal (triangularSecondDensity I x) := by
  change (Measure.infinitePi (fun _ : ℕ => circleMeasure))
    ((I : Set ℕ).pi (fun i => {z | circleRepresentative z < circleRepresentative (x i)})) = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_lt rep_measurable_p1 measurable_const)]
  simp_rw [circleRepresentative_lower_tail _ (rep_bounds _).2.le]
  rw [triangularSecondDensity, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (rep_bounds (x i)).1

theorem reversedTriangularEvent_first_marginal (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict
      {xz : EndpointPair | ∀ i ∈ I,
        circleRepresentative (xz.2 i) < circleRepresentative (xz.1 i)}).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularSecondDensity I x)) := by
  rw [fst_restrict_prod_eq_withDensity]
  · congr 1
    funext x
    exact reversedTriangularEvent_fiber_mass I x
  · simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt
      (rep_measurable_p1.comp ((measurable_pi_apply i).comp measurable_snd))
      (rep_measurable_p1.comp ((measurable_pi_apply i).comp measurable_fst))

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_CoordinateSwap
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.CoordinateSwap

variable {X : Type*} [MeasurableSpace X]

theorem measurePreserving_flatten (μ : Measure X) [IsProbabilityMeasure μ] :
    MeasurePreserving (flatten (X := X))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ)))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) := by
  have hp := MeasurePreserving.symm MeasurableEquiv.finTwoArrow
    (measurePreserving_finTwoArrow (Measure.infinitePi (fun _ : ℕ => μ)))
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin 2) ℕ X).symm
      (Measure.infinitePi (fun _ : Fin 2 => Measure.infinitePi (fun _ : ℕ => μ)))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) := by
    exact ⟨(MeasurableEquiv.curry (Fin 2) ℕ X).symm.measurable,
      Measure.infinitePi_map_curry_symm (fun _ : Fin 2 => fun _ : ℕ => μ)⟩
  apply hp.trans
  simpa only [Measure.infinitePi_eq_pi] using hc

theorem measurePreserving_swap (μ : Measure X) [IsProbabilityMeasure μ] (I : Finset ℕ) :
    MeasurePreserving (swapEquiv (X := X) I)
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ)))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => μ))) := by
  have hr : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × ℕ => X) (swapIndex I))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ))
      (Measure.infinitePi (fun _ : Fin 2 × ℕ => μ)) :=
    ⟨(MeasurableEquiv.piCongrLeft _ _).measurable,
      Measure.infinitePi_map_piCongrLeft (fun _ : Fin 2 × ℕ => μ) (swapIndex I)⟩
  exact ((measurePreserving_flatten μ).trans hr).trans
    (MeasurePreserving.symm flatten (measurePreserving_flatten μ))

theorem swapEquiv_fst (I : Finset ℕ) (xz : (ℕ → X) × (ℕ → X)) (i : ℕ) :
    (swapEquiv I xz).1 i = if i ∈ I then xz.2 i else xz.1 i := by
  by_cases hi : i ∈ I <;>
    simp [swapEquiv, flatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      swapIndex, hi, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo,
      MeasurableEquiv.curry]

theorem swapEquiv_snd (I : Finset ℕ) (xz : (ℕ → X) × (ℕ → X)) (i : ℕ) :
    (swapEquiv I xz).2 i = if i ∈ I then xz.1 i else xz.2 i := by
  by_cases hi : i ∈ I <;>
    simp [swapEquiv, flatten, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      swapIndex, hi, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo,
      MeasurableEquiv.curry]

end Invariant233.CoordinateSwap

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSampling
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingCylinderWeak.quotient_cutCoordinates _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

theorem triangularEvent_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  unfold triangularEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_lt
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem ordered_measurable : MeasurableSet {xy : EndpointPair | Ordered xy.1 xy.2} := by
  unfold Ordered
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem triangularLaw_finite (I : Finset ℕ) : IsFiniteMeasure (triangularLaw I) := by
  unfold triangularLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem triangularLaw_ordered (I : Finset ℕ) :
    ∀ᵐ xy ∂triangularLaw I, Ordered xy.1 xy.2 := by
  unfold triangularLaw
  rw [ae_map_iff (endpointMap_measurable I).aemeasurable ordered_measurable]
  filter_upwards [ae_restrict_mem (triangularEvent_measurable I)] with xz hxz
  intro i
  by_cases hi : i ∈ I
  · simpa [selectedEndpoint, hi] using (hxz i hi).le
  · simp [selectedEndpoint, hi]

theorem triangularLaw_first_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) := by
  exact Invariant233.ProductModel.triangularLaw_first_marginal I

theorem reversedRestriction_first_marginal (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict (Prod.swap ⁻¹' triangularEvent I)).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularSecondDensity I x)) := by
  exact Invariant233.ProductModel.reversedTriangularEvent_first_marginal I

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TriangularSecondMarginal
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel.Sampling

theorem reverseTriangularEvent_measurable (I : Finset ℕ) :
    MeasurableSet (reverseTriangularEvent I) :=
  (triangularEvent_measurable I).preimage measurable_swap

theorem swap_preimage_reverseTriangularEvent (I : Finset ℕ) :
    CoordinateSwap.swapEquiv I ⁻¹' reverseTriangularEvent I = triangularEvent I := by
  ext xz
  change (∀ i ∈ I, circleRepresentative ((CoordinateSwap.swapEquiv I xz).2 i) <
    circleRepresentative ((CoordinateSwap.swapEquiv I xz).1 i)) ↔ _
  constructor
  · intro h i hi
    simpa only [CoordinateSwap.swapEquiv_snd, CoordinateSwap.swapEquiv_fst, ite_eq_left hi]
      using h i hi
  · intro h i hi
    simpa only [CoordinateSwap.swapEquiv_snd, CoordinateSwap.swapEquiv_fst, ite_eq_left hi]
      using h i hi

theorem triangularLaw_second_marginal_swap (I : Finset ℕ) :
    (triangularLaw I).map Prod.snd =
      ((baseMeasure.prod baseMeasure).restrict (reverseTriangularEvent I)).map Prod.fst := by
  have hp : MeasurePreserving (CoordinateSwap.swapEquiv (X := Circle) I)
      (baseMeasure.prod baseMeasure) (baseMeasure.prod baseMeasure) :=
    CoordinateSwap.measurePreserving_swap circleMeasure I
  have hm := hp.restrict_preimage (reverseTriangularEvent_measurable I)
  rw [swap_preimage_reverseTriangularEvent] at hm
  have heq : (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) =
      Prod.fst ∘ CoordinateSwap.swapEquiv I := by
    funext xz i
    exact (CoordinateSwap.swapEquiv_fst I xz i).symm
  unfold triangularLaw
  rw [Measure.map_map measurable_snd (endpointMap_measurable I)]
  change ((baseMeasure.prod baseMeasure).restrict (triangularEvent I)).map
    (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) = _
  rw [heq, ← Measure.map_map measurable_fst (CoordinateSwap.swapEquiv I).measurable,
    hm.map_eq]

theorem triangularLaw_second_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.snd =
      baseMeasure.withDensity (fun y => ENNReal.ofReal (triangularSecondDensity I y)) := by
  rw [triangularLaw_second_marginal_swap]
  exact reversedRestriction_first_marginal I

end Invariant233.ProductModel.Sampling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

theorem exp_tsum_floor_zero {I : Type*} (x c : I → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑' i, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hf (i : I) : ⌊x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hx i)
  simp [hf]

theorem exp_tsum_floor_ratio_le_one {I : Type*} (x y θ c : I → ℝ) (k : ℤ)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, x i ≤ y i)
    (hx : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport (fun i ↦ ⌊y i + (k : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ))) /
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) ≤ 1 := by
  rw [← Real.exp_sub, Real.exp_le_one_iff]
  have hsum : (∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ)) ≤
      ∑' i, c i * (⌊y i + (k : ℝ) * θ i⌋ : ℝ) := by
    apply Summable.tsum_le_tsum _ (summable_weighted_int c hx) (summable_weighted_int c hy)
    intro i
    apply mul_le_mul_of_nonneg_left _ (hc i)
    exact Int.cast_le.mpr (Int.floor_mono (add_le_add_left (hxy i) ((k : ℝ) * θ i)))
  linarith

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem representative_rotate {I : Type*} (θ : I → ℝ) (k : ℤ)
    (x : Space I) (i : I) :
    representative (rotate θ k x i) =
      Int.fract (representative (x i) + (k : ℝ) * θ i) :=
  representative_add (x i) ((k : ℝ) * θ i)

theorem measurable_cocycleVersion {I : Type*} [Countable I]
    (θ c : I → ℝ) (k : ℤ) : Measurable (cocycleVersion θ c k) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Space I ↦ representative (x i)) :=
    measurable_representative.comp (measurable_pi_apply i)
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const ((k : ℝ) * θ i)).floor))

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

theorem cocycleVersion_add_of_finite_support {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hk : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊representative (rotate θ k x i) + (n : ℝ) * θ i⌋)) :
    cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := by
  simp only [cocycleVersion, representative_rotate] at hn ⊢
  exact FiniteSupportCocycle.exp_tsum_floor_cocycle _ θ c k n hk hn

theorem cocycleVersion_ratio_le_one {I : Type*}
    (θ c : I → ℝ) (k : ℤ) (x y : Space I)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, representative (x i) ≤ representative (y i))
    (hx : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport
      (fun i ↦ ⌊representative (y i) + (k : ℝ) * θ i⌋)) :
    cocycleVersion θ c k y / cocycleVersion θ c k x ≤ 1 :=
  FiniteSupportCocycle.exp_tsum_floor_ratio_le_one _ _ θ c k hc hxy hx hy

theorem exists_invariant_cocycle_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋)) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c (k + n) x =
          cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x) := by
  have hall : ∀ᵐ x ∂haar I, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  obtain ⟨s, hs, hfull, hprop, hinv⟩ :=
    Invariant233.exists_invariant_conull_forall (rotate θ) (rotate_zero θ)
      (rotate_add θ) (measurePreserving_rotate θ)
      (fun (k : ℤ) (x : Space I) ↦ HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
      (ae_all_iff.mp hall)
  have hsupport (x : Space I) (hx : x ∈ s) (k : ℤ) :
      HasFiniteSupport (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) := by
    simpa only [rotate_zero] using hprop x hx 0 k
  refine ⟨s, hs, hfull, hinv, hsupport, ?_⟩
  intro x hx c k n
  exact cocycleVersion_add_of_finite_support θ c k n x
    (hsupport x hx k) (hprop x hx k n)

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycleInterchange
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem cocycleVersion_ratio_interchange_of_add {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hkn : cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x)
    (hnk : cocycleVersion θ c (n + k) x =
      cocycleVersion θ c k (rotate θ n x) * cocycleVersion θ c n x) :
    cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
      cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x := by
  apply (div_eq_div_iff (cocycleVersion_pos θ c k x).ne'
    (cocycleVersion_pos θ c n x).ne').mpr
  calc
    cocycleVersion θ c k (rotate θ n x) * cocycleVersion θ c n x =
        cocycleVersion θ c (n + k) x := hnk.symm
    _ = cocycleVersion θ c (k + n) x := by rw [add_comm n k]
    _ = cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := hkn

theorem exists_invariant_ratio_interchange_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
          cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x) := by
  obtain ⟨s, hs, hfull, hinv, _hsupport, hlaw⟩ :=
    exists_invariant_cocycle_core θ hθ0 hθ
  refine ⟨s, hs, hfull, hinv, ?_⟩
  intro x hx c k n
  exact cocycleVersion_ratio_interchange_of_add θ c k n x
    (hlaw x hx c k n) (hlaw x hx c n k)

theorem ae_cocycleVersion_ratio_interchange {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂haar I, ∀ (c : I → ℝ) (k n : ℤ),
      cocycleVersion θ c k (rotate θ n x) / cocycleVersion θ c k x =
        cocycleVersion θ c n (rotate θ k x) / cocycleVersion θ c n x := by
  obtain ⟨s, _hs, hfull, _hinv, hlaw⟩ :=
    exists_invariant_ratio_interchange_core θ hθ0 hθ
  filter_upwards [hfull] with x hx
  exact hlaw x hx

end Invariant233.ProductCocycle

namespace Invariant233.ProductModel

theorem ae_cocycle_ratio_interchange (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∀ (c : ℕ → ℝ) (k n : ℤ),
      ProductCocycle.cocycleVersion θ c k (rotationIterate θ n x) /
          ProductCocycle.cocycleVersion θ c k x =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x :=
  ProductCocycle.ae_cocycleVersion_ratio_interchange θ hθ0 hθ

theorem ae_cocycleRatio_rotation (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, ∀ (c : ℕ → ℝ) (k n : ℤ),
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x :=
  ae_cocycle_ratio_interchange θ hθ0 hθ

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

theorem operator_pow_apply_add (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) (k + n) =
      (∏ j ∈ Finset.range n, w (k + j)) * ξ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, operator_apply]
    have hk : k + (↑(n + 1) : ℤ) - 1 = k + n := by omega
    rw [hk, ih, Finset.prod_range_succ]
    ring

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem operator_pow_eq_shift_diagonal (w : Weight) (n : ℕ) :
    (operator w)^n =
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.comp
        (diagonal (orbitProduct w n)) := by
  ext ξ k
  exact operator_pow_apply w n ξ k

end Invariant233.WeightedShift

end

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

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCovariance
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
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

theorem field_conjugacy {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F (rotationIterate θ m x) =
        (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap := by
  filter_upwards [field_covariance hT F hF] with x hx m
  have hinv : (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap *
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap = 1 := by
    rw [← WeightedShift.shift_add]
    simp [WeightedShift.shift_zero]
  have heq := congrArg
    (fun A : Fiber →L[ℂ] Fiber =>
      (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * A) (hx m)
  simpa only [← mul_assoc, hinv, one_mul] using heq.symm

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductProjectionFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem field_isStarProjection {θ : ℕ → ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hP : P ∈ factor θ) (hp : IsStarProjection P)
    (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, IsStarProjection (F x) := by
  obtain ⟨G, _, _, hG, huniq, _, _, hproj⟩ :=
    L2Multiplication.scalar_multiplier_fields_complete
      (default : HilbertBasis ℤ ℂ Fiber) P (factor_commutes_scalarMultiplier θ hP)
  filter_upwards [huniq F hF, hproj hp] with x hGF hx
  rwa [← hGF]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFieldRepresentation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

theorem exists_covariantProjectionField {θ : ℕ → ℝ}
    {P : Hilbert →L[ℂ] Hilbert} (hPm : P ∈ factor θ) (hP : IsStarProjection P) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ P F 1 ∧ ∀ x, IsStarProjection (F x) := by
  classical
  obtain ⟨F, hbound, hm, hrep, _⟩ := exists_unique_field hPm
  have hproj := field_isStarProjection hPm hP F hrep
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hproj)
  let G : Base → Fiber →L[ℂ] Fiber := fun x => if x ∈ N then 0 else F x
  have hgood : ∀ᵐ x ∂baseMeasure, x ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hGF : G =ᵐ[baseMeasure] F := by
    filter_upwards [hgood] with x hx
    simp only [G, ite_eq_right hx]
  have hGrep : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => G x (ξ x) := by
    intro ξ
    filter_upwards [hrep ξ, hGF] with x hξ hx
    rw [hx]
    exact hξ
  have hGproj : ∀ x, IsStarProjection (G x) := by
    intro x
    by_cases hx : x ∈ N
    · simp only [G, ite_eq_left hx]
      exact IsStarProjection.zero _
    · simp only [G, ite_eq_right hx]
      by_contra hn
      exact hx (hsub hn)
  refine ⟨G, ⟨by norm_num, ?_, ?_, hGrep, ?_⟩, hGproj⟩
  · intro x
    exact IsStarProjection.norm_le _ (hGproj x)
  · intro v
    have heq : (fun x => G x v) = N.piecewise (fun _ => (0 : Fiber)) (fun x => F x v) := by
      funext x
      by_cases hx : x ∈ N <;> simp [G, Set.piecewise, hx]
    rw [heq]
    exact (stronglyMeasurable_const : StronglyMeasurable (fun _ : Base => (0 : Fiber))).piecewise
      hN (hm v)
  · filter_upwards [field_conjugacy hPm G hGrep] with x hx
    have hrot : rotationIterate θ 1 x = rotation θ x := by
      funext i
      change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
      simp only [Int.cast_one, one_mul]
    rw [← hrot]
    exact hx 1

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

theorem norm_diagonal_le (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : ‖diagonal a C hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

theorem strong_continuous_diagonal [TopologicalSpace X]
    (a : X → I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x i, ‖a x i‖ ≤ C)
    (hc : ∀ i, Continuous (fun x => a x i)) (v : SequenceHilbert I) :
    Continuous (fun x => diagonal (a x) C hC (ha x) v) := by
  classical
  let b : HilbertBasis I ℂ (SequenceHilbert I) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun _ => rfl
  apply InvariantProjection.strong_continuous_of_dense_span_of_bounded
    (b := b) (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    (fun x => norm_diagonal_le (a x) C hC (ha x)) v
  intro i
  simpa only [hb, diagonal_single, mul_one, Function.comp_def,
    lp.singleContinuousLinearMap_apply] using
    (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.comp (hc i)

end Invariant233.SequenceHilbert

namespace Invariant233

variable {I X : Type*} [TopologicalSpace X]

theorem isClosed_diagonal_relation
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsClosed {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  apply InvariantProjection.isClosed_zero_set_of_strong_continuous
  intro v
  have hleft : ∀ w, Continuous (fun t : X × X => (1 - p t.2) w) := by
    intro w
    have h : Continuous (fun t : X × X => w - p t.2 w) :=
      continuous_const.sub ((hp w).comp continuous_snd)
    simpa using h
  have hleftn : ∀ t : X × X,
      ‖1 - p t.2‖ ≤ ‖(1 : SequenceHilbert I →L[ℂ] SequenceHilbert I)‖ + C := by
    intro t
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hpn t.2))
  have hright : ∀ w, Continuous (fun t : X × X =>
      ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) w) := by
    intro w
    apply InvariantProjection.strong_continuous_comp_of_bounded
      (fun z => SequenceHilbert.strong_continuous_diagonal d B hB hd hdc z)
      (fun z => (hp z).comp continuous_fst)
      (fun t => SequenceHilbert.norm_diagonal_le (d t) B hB (hd t)) w
  exact InvariantProjection.strong_continuous_comp_of_bounded hleft hright hleftn v

theorem isCompact_diagonal_relation [CompactSpace X]
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} :=
  (isClosed_diagonal_relation p d B C hB hd hp hdc hpn).isCompact

theorem isCompact_diagonal_relation_on
    (Q : Set X) (hQ : IsCompact Q)
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, ContinuousOn (fun x => p x v) Q)
    (hdc : ∀ i, ContinuousOn (fun t => d t i) (Q ×ˢ Q))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X | t ∈ Q ×ˢ Q ∧
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let f : Q × Q → X × X := fun t => ((t.1 : X), (t.2 : X))
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let pQ : Q → SequenceHilbert I →L[ℂ] SequenceHilbert I := fun x => p x
  let dQ : (Q × Q) → I → ℂ := fun t => d (f t)
  have hpQ : ∀ v, Continuous (fun x : Q => pQ x v) := fun v => (hp v).domRestrict
  have hdQ : ∀ i, Continuous (fun t : Q × Q => dQ t i) := by
    intro i
    exact (hdc i).comp_continuous hf (fun t => ⟨t.1.property, t.2.property⟩)
  have hS := isCompact_diagonal_relation pQ dQ B C hB
    (fun t i => hd (f t) i) hpQ hdQ (fun x => hpn x)
  have himage := hS.image hf
  convert himage using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨ht, hzero⟩
    refine ⟨(⟨t.1, ht.1⟩, ⟨t.2, ht.2⟩), ?_, rfl⟩
    exact hzero
  · rintro ⟨q, hzero, rfl⟩
    exact ⟨⟨q.1.property, q.2.property⟩, hzero⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UnrestrictedDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SequenceHilbert

variable {I : Type*}

theorem boundedDiagonal_eq (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : boundedDiagonal a = diagonal a C hC ha := by
  unfold boundedDiagonal
  split
  · rename_i h
    exact diagonal_congr a a h.choose C h.choose_spec.1 hC h.choose_spec.2 ha (fun _ => rfl)
  · rename_i h
    exact False.elim (h ⟨C, hC, ha⟩)

@[simp]
theorem boundedDiagonal_apply_of_bound (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    boundedDiagonal a v i = a i * v i := by
  rw [boundedDiagonal_eq a C hC ha, diagonal_apply]

theorem boundedDiagonal_congr {a b : I → ℂ} (h : ∀ i, a i = b i) :
    boundedDiagonal a = boundedDiagonal b := by
  exact congrArg boundedDiagonal (funext h)

end Invariant233.SequenceHilbert

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem HasUniformL2Marginals.uniformlyAbsolutelyContinuous
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η) :
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous baseMeasure (fun l => (η l).map Prod.snd) := by
  rcases hη with ⟨H, _hH, hη⟩
  constructor
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, hf, _hg, hmf, _hmg, hbf, _hbg⟩
    exact ⟨f, hf, hmf, hbf⟩
  · apply EndpointLoss.uniformlyAbsolutelyContinuous_of_Lp_densities baseMeasure _ H
    intro l
    rcases hη l with ⟨f, g, _hf, hg, _hmf, hmg, _hbf, hbg⟩
    exact ⟨g, hg, hmg, hbg⟩

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPairRatios
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cocycleRatio_pos (θ c : ℕ → ℝ) (x y : Base) (k : ℤ) :
    0 < cocycleRatio θ c x y k :=
  div_pos (ProductCocycle.cocycleVersion_pos θ c k y)
    (ProductCocycle.cocycleVersion_pos θ c k x)

theorem ae_all_cocycleRatio_bounds_of_ordered
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (horder : ∀ᵐ xy ∂ν, Ordered xy.1 xy.2) :
    ∀ᵐ xy ∂ν, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  have hcore := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  have hfirst := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hcore)
  have hsecond := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hcore)
  filter_upwards [hfirst, hsecond, horder] with xy hx hy hxy
  intro k
  refine ⟨cocycleRatio_pos θ c xy.1 xy.2 k, ?_⟩
  exact ProductCocycle.cocycleVersion_ratio_le_one θ c k xy.1 xy.2
    hc hxy (hx k) (hy k)

theorem triangularLaw_ae_all_cocycleRatio_bounds
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (I : Finset ℕ) :
    ∀ᵐ xy ∂triangularLaw I, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  apply ae_all_cocycleRatio_bounds_of_ordered θ c hθ0 hθ hc (triangularLaw I)
  · rw [Sampling.triangularLaw_first_marginal]
    exact withDensity_absolutelyContinuous _ _
  · rw [Sampling.triangularLaw_second_marginal]
    exact withDensity_absolutelyContinuous _ _
  · exact Sampling.triangularLaw_ordered I

theorem HasUniformL2Marginals.ae_all_cocycleRatio_bounds
    {η : ℕ → Measure EndpointPair} (hη : HasUniformL2Marginals η)
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i)
    (horder : ∀ l, ∀ᵐ xy ∂η l, Ordered xy.1 xy.2) :
    ∀ l, ∀ᵐ xy ∂η l, ∀ k : ℤ,
      0 < cocycleRatio θ c xy.1 xy.2 k ∧
        cocycleRatio θ c xy.1 xy.2 k ≤ 1 := by
  intro l
  obtain ⟨H, hH, hdens⟩ := hη
  obtain ⟨f, g, hf, hg, hmf, hmg, hbf, hbg⟩ := hdens l
  apply ae_all_cocycleRatio_bounds_of_ordered θ c hθ0 hθ hc (η l)
  · rw [hmf]
    exact withDensity_absolutelyContinuous _ _
  · rw [hmg]
    exact withDensity_absolutelyContinuous _ _
  · exact horder l

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldWeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)

theorem fieldOperator_ae (f : Lp Hilbert 2 μ) :
    fieldOperator a C hC ha hm f =ᵐ[μ] fun x => operator (a x) (f x) := by
  filter_upwards [fieldShift_ae 1 (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_ae a C hC ha hm f] with x hs hd
  change ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
    (fieldDiagonal a C hC ha hm f)) x = operator (a x) (f x)
  rw [hs, hd]
  rfl

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (s : Set Base) (hinv : ∀ k : ℤ, ProductCocycle.rotate θ k ⁻¹' s = s)
    (hs : ∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊ProductCocycle.representative (x i) + (k : ℝ) * θ i⌋))
    (hlaw : ∀ x ∈ s, ∀ k n : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) x =
        ProductCocycle.cocycleVersion θ c n (ProductCocycle.rotate θ k x) *
          ProductCocycle.cocycleVersion θ c k x)
    (x : Base) (hx : x ∈ s) (n : ℕ) :
    (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ j x)) =
      ProductCocycle.cocycleVersion θ c n x := by
  have hweight (k : ℤ) : weight θ c (rotationIterate θ k x) =
      ProductCocycle.cocycleVersion θ c 1 (ProductCocycle.rotate θ k x) := by
    apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc
    have hxk : ProductCocycle.rotate θ k x ∈ s := by
      change x ∈ ProductCocycle.rotate θ k ⁻¹' s
      rw [hinv k]
      exact hx
    simpa only [ProductCocycle.representative, circleRepresentative,
      Int.cast_one, one_mul, rotationIterate, ProductCocycle.rotate] using hs _ hxk 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, hweight]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (hlaw x hx n 1).symm

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPowerIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem ae_weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) := by
  obtain ⟨s, _hsm, hfull, hinv, hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx k
  have hxk : ProductCocycle.rotate θ k x ∈ s := by
    change x ∈ ProductCocycle.rotate θ k ⁻¹' s
    rw [hinv k]
    exact hx
  have hprod := weight_orbit_product_eq_cocycleVersion θ c hθ0 hc s hinv hs
    (fun y hy => hlaw y hy c) (ProductCocycle.rotate θ k x) hxk n
  have hrot (j : ℕ) : rotationIterate θ (k + j) x =
      rotationIterate θ j (ProductCocycle.rotate θ k x) :=
    ProductCocycle.rotate_add θ k j x
  simp_rw [hrot]
  exact hprod

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedOrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

theorem weighted_shift_orbit_inclusion (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0) (n : ℕ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (orbitProduct w n) * p = 0 := by
  exact orbit_inclusion_pow hp hT n (shiftUnit n) (diagonal (orbitProduct w n))
    (operator_pow_eq_shift_diagonal w n)

theorem diagonal_smul (c : ℂ) (w : Weight) :
    diagonal (c • w) = c • diagonal w := by
  ext ξ k
  simp [diagonal_apply, mul_assoc]

theorem weighted_shift_orbit_normalized (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0)
    (n : ℕ) (c : ℂ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (c⁻¹ • orbitProduct w n) * p = 0 := by
  rw [diagonal_smul, mul_smul_comm, smul_mul_assoc,
    weighted_shift_orbit_inclusion w hp hT n, smul_zero]

end Invariant233.OrbitInvariance

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductOrbitPair
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem weightedOperator_ae_actualWeightField (θ c : ℕ → ℝ) (f : Hilbert) :
    weightedOperator θ c f =ᵐ[baseMeasure] fun x =>
      WeightedShift.operator (actualWeightField θ c x) (f x) := by
  have ha (x : Base) : ‖actualWeightField θ c x‖ ≤ 1 :=
    lp.norm_le_of_forall_le (by norm_num) (fun k => by
      simpa only [actualWeightField_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_mem_Icc θ c _).1] using (weight_mem_Icc θ c _).2)
  have hm (k : ℤ) : AEStronglyMeasurable
      (fun x => actualWeightField θ c x k) baseMeasure :=
    ((measurable_weight θ c).complex_ofReal.comp
      (rotationIterate_measurePreserving θ k).measurable).aestronglyMeasurable
  exact WeightedShift.fieldOperator_ae (actualWeightField θ c) 1 (by norm_num) ha hm f

theorem ae_actualWeightField_invariant (θ c : ℕ → ℝ)
    (p : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F x) * WeightedShift.operator (actualWeightField θ c x) * F x = 0 :=
  L2Multiplication.ae_invariance_of_represented
    (default : HilbertBasis ℤ ℂ Fiber) p (weightedOperator θ c) F
    (fun x => WeightedShift.operator (actualWeightField θ c x))
    hrep (weightedOperator_ae_actualWeightField θ c) hinv

theorem boundedDiagonal_weight (w : WeightedShift.Weight) :
    SequenceHilbert.boundedDiagonal (fun k : ℤ => w k) = WeightedShift.diagonal w := by
  ext v k
  rw [SequenceHilbert.boundedDiagonal_apply_of_bound _ ‖w‖ (norm_nonneg w)
    (fun i => lp.norm_apply_le_norm (by simp) w i)]
  rfl

theorem ratioDiagonal_eq_normalized_orbit (θ c : ℕ → ℝ)
    (x : Base) (n : ℕ)
    (hprod : ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x))
    (hratio : ∀ k : ℤ,
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x) :
    ratioDiagonal θ c x (rotationIterate θ n x) =
      WeightedShift.diagonal ((ProductCocycle.cocycleVersion θ c n x : ℂ)⁻¹ •
        WeightedShift.orbitProduct (actualWeightField θ c x) n) := by
  rw [← boundedDiagonal_weight]
  apply SequenceHilbert.boundedDiagonal_congr
  intro k
  change (cocycleRatio θ c x (rotationIterate θ n x) k : ℂ) =
    (ProductCocycle.cocycleVersion θ c n x : ℂ)⁻¹ *
      (∏ j ∈ Finset.range n, (weight θ c (rotationIterate θ (k + j) x) : ℂ))
  rw [hratio k, Complex.ofReal_div, ← Complex.ofReal_prod, hprod k]
  exact div_eq_mul_inv _ _ |>.trans (mul_comm _ _)

theorem ae_orbit_pair_identity_of_ratio (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ)
    (F : Base → Fiber →L[ℂ] Fiber) (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0)
    (n : ℕ)
    (hratio : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F (rotationIterate θ n x)) *
        ratioDiagonal θ c x (rotationIterate θ n x) * F x = 0 := by
  filter_upwards [ae_actualWeightField_invariant θ c p F hrep hinv,
    field_conjugacy hpM F hrep,
    ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n,
    hratio] with x hInv hCov hProd hRatio
  rw [ratioDiagonal_eq_normalized_orbit θ c x n hProd hRatio, hCov n]
  exact OrbitInvariance.weighted_shift_orbit_normalized
    (actualWeightField θ c x) (hproj x).isIdempotentElem hInv n
    (ProductCocycle.cocycleVersion θ c n x : ℂ)

theorem ae_orbit_pair_identity (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ)
    (F : Base → Fiber →L[ℂ] Fiber) (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F (rotationIterate θ n x)) *
        ratioDiagonal θ c x (rotationIterate θ n x) * F x = 0 :=
  ae_orbit_pair_identity_of_ratio θ c hθ0 hc hθ p hpM F hproj hrep hinv n
    ((ae_cocycleRatio_rotation θ hθ0 hθ).mono (fun _ hx k => hx c k n))

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_OperatorCompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal lp

noncomputable section
namespace Invariant233.CompactTransfer

local instance operatorCompactTransferSecondCountableTopology :
    SecondCountableTopology (SequenceHilbert ℤ) := by
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ) |>.closure
  have : TopologicalSpace.SeparableSpace (SequenceHilbert ℤ) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      simpa only [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] using hs)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem uniform_marginal_budget {X ι : Type*}
    [MeasurableSpace X] (μ : Measure X) (νs : ι → Measure (X × X))
    (hfirst : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.snd)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hfirst⟩ := hfirst (ε / 2) hhalf
  obtain ⟨δ₂, hδ₂, hsecond⟩ := hsecond (ε / 2) hhalf
  refine ⟨(min δ₁ δ₂ : ℝ≥0), ?_, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_min hδ₁ hδ₂))
  intro A hA hμ i
  have hμ₁ : μ A < (δ₁ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_left δ₁ δ₂)
  have hμ₂ : μ A < (δ₂ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_right δ₁ δ₂)
  have h₁ := hfirst A hA hμ₁ i
  have h₂ := hsecond A hA hμ₂ i
  rw [Measure.map_apply measurable_fst hA] at h₁
  rw [Measure.map_apply measurable_snd hA] at h₂
  have heq₁ : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set X) := by ext t; simp
  have heq₂ : Prod.snd ⁻¹' A = (Set.univ : Set X) ×ˢ A := by ext t; simp
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  calc
    νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤
        ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add h₁.le h₂.le
    _ = ε := by rw [← ENNReal.coe_add, add_halves]

theorem capped_operator_relation_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (C : ℝ) (hC : 0 ≤ C) (hpn : ∀ x, ‖p x‖ ≤ C)
    (B : ℝ) (hB : 0 ≤ B)
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        (νs i : Measure (X × X)) (A ×ˢ Set.univ) +
        (νs i : Measure (X × X)) (Set.univ ×ˢ A) ≤ ε)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0 := by
  classical
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun i => (b.repr_symm_single i).symm
  apply ae_mem_of_closed_approximation hν
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
  obtain ⟨Q, hQ, hμQ, hpQ, hFQ⟩ :=
    StrongLusin.exists_compact_strong_and_continuousOn μ p hC hpn b
      (fun i => by simpa only [hb] using hpm i) F hFm hδ
  let S : Set (X × X) := {t | t ∈ Q ×ˢ Q ∧
    (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0}
  have hScompact : IsCompact S := by
    apply isCompact_diagonal_relation_on Q hQ p
      (fun t i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B C hB
      (fun t i => ?_) hpQ (fun i => ?_) hpn
    · have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
        le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
        (min_le_left B (F i t.2 / F i t.1))
    · exact continuousOn_capped_ratio (F i) Q (hFQ i)
        (fun x _ => (hF i x).ne') B
  refine ⟨S, hScompact.isClosed, fun _ ht => ht.2,
    Filter.Eventually.of_forall ?_⟩
  intro i
  have hsub : ∀ᵐ t ∂(νs i : Measure (X × X)), t ∈ Sᶜ → t ∈ (Q ×ˢ Q)ᶜ := by
    filter_upwards [hzero i] with t ht
    intro hbad hQpair
    exact hbad ⟨hQpair, ht⟩
  apply (measure_mono_ae hsub).trans
  rw [Set.compl_prod_eq_union]
  exact (measure_union_le _ _).trans
    (hδsmall Qᶜ hQ.isClosed.measurableSet.compl hμQ i)

theorem cappedDiagonal_eq_ratioDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X)
    (hcap : ∀ i, F i t.2 / F i t.1 ≤ B) :
    cappedDiagonal F hF B hB t = ratioDiagonal F t := by
  have hnorm : ∀ i, ‖((F i t.2 / F i t.1 : ℝ) : ℂ)‖ ≤ B := by
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hF i t.2).le (hF i t.1).le)] using hcap i
  unfold ratioDiagonal
  rw [SequenceHilbert.boundedDiagonal_eq _ B hB hnorm]
  apply SequenceHilbert.diagonal_congr
  intro i
  simp only [min_eq_right (hcap i)]

theorem compact_operator_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hfirst : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.snd))
    (B : ℝ) (hB : 0 < B)
    (hcapn : ∀ i k, ∀ᵐ t ∂(νs i : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hcap : ∀ k, ∀ᵐ t ∂(ν : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0 := by
  have hsmall := uniform_marginal_budget μ
    (fun i => (νs i : Measure (X × X))) hfirst hsecond
  have hbounded : ∀ x, ‖p x‖ ≤ (1 : ℝ) :=
    fun x => IsStarProjection.norm_le (p x) (hp x)
  have hzerocap : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB.le t).comp (p t.1)) = 0 := by
    intro i
    filter_upwards [ae_all_iff.mpr (hcapn i), hzero i] with t ht hz
    rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht]
  have hresult := capped_operator_relation_transfer μ p F hF hFm hpm
    1 zero_le_one hbounded B hB.le hν hsmall hzerocap
  filter_upwards [ae_all_iff.mpr hcap, hresult] with t ht hz
  rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht] at hz

end Invariant233.CompactTransfer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductSamplingTrimming
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Invariant233.ProductModel

attribute [local instance] OAI.Invariant233.ProductModel.productSamplingTrimmingOpensMeasurableSpace
theorem weaklyConverges_iff_tendsto (η : ℕ → FiniteMeasure EndpointPair)
    (ν : FiniteMeasure EndpointPair) :
    WeaklyConverges (fun l => (η l : Measure EndpointPair)) (ν : Measure EndpointPair) ↔
      Tendsto η atTop (𝓝 ν) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  constructor
  · intro h φ
    exact h φ.toContinuousMap
  · intro h φ
    exact h (BoundedContinuousFunction.mkOfCompact φ)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPairTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel

attribute [local instance] OAI.Invariant233.ProductModel.instOpensMeasurableSpaceEndpointPair
theorem ae_ratio_identity_of_positive_ordered_orbit_support
    (θ c : ℕ → ℝ) (F : Base → Fiber →L[ℂ] Fiber)
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂baseMeasure,
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0)
    (ν : Measure EndpointPair) (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsupp : SupportedOnPositiveOrderedOrbitPairs θ ν) :
    ∀ᵐ xy ∂ν, (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0 := by
  have hall : ∀ᵐ x ∂baseMeasure, ∀ n : ℕ, 0 < n →
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0 := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0 < n
    · exact (horbit n hn).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hn h).elim)
  have hpull := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hall)
  obtain ⟨N, hN, hsupp⟩ := hsupp
  filter_upwards [hpull, hsupp] with xy hx hxy
  obtain ⟨horder, n, hn, heq⟩ := hxy
  rw [heq] at horder ⊢
  exact hx n (hN n hn) horder

theorem pairIdentity_of_orderedOrbitSampling
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (F : Base → Fiber →L[ℂ] Fiber)
    (hproj : ∀ x, IsStarProjection (F x))
    (hFm : ∀ v : Fiber, StronglyMeasurable (fun x => F x v))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂baseMeasure,
      Ordered x (rotationIterate θ (n : ℤ) x) →
        (1 - F (rotationIterate θ (n : ℤ) x)) *
          ratioDiagonal θ c x (rotationIterate θ (n : ℤ) x) * F x = 0)
    (I : Finset ℕ) (hsampling : OrderedOrbitSampling θ I) :
    ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy := by
  obtain ⟨η, hfinite, hsupp, hL2, hweak⟩ := hsampling
  let ηf : ℕ → FiniteMeasure EndpointPair := fun l => ⟨η l, hfinite l⟩
  let ν : FiniteMeasure EndpointPair := ⟨triangularLaw I, Sampling.triangularLaw_finite I⟩
  have hconv : Tendsto ηf atTop (𝓝 ν) :=
    (weaklyConverges_iff_tendsto ηf ν).mp hweak
  have horder : ∀ l, ∀ᵐ xy ∂η l, Ordered xy.1 xy.2 := by
    intro l
    obtain ⟨N, hN, hs⟩ := hsupp l
    exact hs.mono (fun _ h => h.1)
  have hratio := hL2.ae_all_cocycleRatio_bounds θ c hθ0 hθ hc horder
  have hlimit := triangularLaw_ae_all_cocycleRatio_bounds θ c hθ0 hθ hc I
  have hac := hL2.uniformlyAbsolutelyContinuous
  have hzero : ∀ l, ∀ᵐ xy ∂η l,
      (1 - F xy.2) * ratioDiagonal θ c xy.1 xy.2 * F xy.1 = 0 := by
    intro l
    obtain ⟨H, hH, hdens⟩ := hL2
    obtain ⟨f, g, hf, hg, hmf, hmg, hbf, hbg⟩ := hdens l
    apply ae_ratio_identity_of_positive_ordered_orbit_support θ c F horbit (η l)
    · rw [hmf]
      exact withDensity_absolutelyContinuous _ _
    · exact hsupp l
  have htransfer := CompactTransfer.compact_operator_transfer baseMeasure F hproj
    (fun k => ProductCocycle.cocycleVersion θ c k)
    (fun k x => ProductCocycle.cocycleVersion_pos θ c k x)
    (fun k => ProductCocycle.measurable_cocycleVersion θ c k)
    (fun k => (hFm (lp.single 2 k 1)).measurable)
    hconv hac.1 hac.2 1 zero_lt_one
    (fun l k => (hratio l).mono (fun xy h => (h k).2))
    (fun k => hlimit.mono (fun xy h => (h k).2))
    (fun l => (hzero l).mono (fun xy h => by
      simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
        ProductModel.ratioDiagonal, Invariant233.ratioDiagonal, cocycleRatio] using h))
  filter_upwards [hlimit, htransfer] with xy hr hz
  refine ⟨hr, ?_⟩
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
    ProductModel.ratioDiagonal, Invariant233.ratioDiagonal, cocycleRatio] using hz

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductPairIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem exists_covariantProjectionField_pairIdentity_oai
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : HasAllFiniteCoordinateSampling θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ I : Finset ℕ, ∀ᵐ xy ∂triangularLaw I, PairIdentity θ c F xy := by
  obtain ⟨F, hF, hproj⟩ := exists_covariantProjectionField hpM hp
  refine ⟨F, hF, hproj, ?_⟩
  intro I
  apply pairIdentity_of_orderedOrbitSampling θ c hθ0 hθ hc F hproj hF.2.2.1
    _ I (hsampling I)
  intro n _hn
  exact (ae_orbit_pair_identity θ c hθ0 hc hθ p hpM F hproj hF.2.2.2.1 hinv n).mono
    (fun _ hx _ => hx)

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity_oai := @OAI.Invariant233.ProductModel.exists_covariantProjectionField_pairIdentity_oai
