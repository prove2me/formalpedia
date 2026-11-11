-- Prove2me | solution 1 for OAI.Invariant233.Rotation.exponentialTransfer_projection_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:13.363134+00:00
-- url     : https://prove2.me/submissions/2784ec1c-2e76-4839-bce0-d831fc7c5958

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.TietzeExtension
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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_IndividualLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Invariant233.Lusin

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [T2Space X] [CompactSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]

theorem exists_compact_clopen_restrictions (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧
      ∀ n, ∃ U : Set X, IsOpen U ∧ A n ∩ K = U ∩ K := by
  classical
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε (ℕ × Bool)
  let E : ℕ × Bool → Set X := fun p => if p.2 then A p.1 else (A p.1)ᶜ
  have hE : ∀ p, MeasurableSet (E p) := by
    rintro ⟨n, b⟩
    cases b <;> simp only [E, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hA n | exact (hA n).compl
  have happrox : ∀ p : ℕ × Bool, ∃ C : Set X,
      C ⊆ E p ∧ IsCompact C ∧ μ (E p \ C) < δ p := by
    intro p
    exact (hE p).exists_isCompact_sdiff_lt (measure_ne_top μ (E p)) (hδpos p).ne'
  choose C hCsub hCcompact hCmeasure using happrox
  let K : Set X := ⋂ n : ℕ, C (n, true) ∪ C (n, false)
  have hKclosed : IsClosed K :=
    isClosed_iInter fun n => (hCcompact (n, true)).isClosed.union (hCcompact (n, false)).isClosed
  have hKmem : ∀ {x : X}, x ∈ K → ∀ n, x ∈ C (n, true) ∪ C (n, false) := by
    intro x hx n
    exact mem_iInter.mp hx n
  have hbad : Kᶜ ⊆ ⋃ p : ℕ × Bool, E p \ C p := by
    intro x hx
    have hn : ∃ n : ℕ, x ∉ C (n, true) ∪ C (n, false) := by
      simpa only [K, mem_compl_iff, mem_iInter, not_forall] using hx
    obtain ⟨n, hn⟩ := hn
    by_cases ha : x ∈ A n
    · apply mem_iUnion.mpr
      refine ⟨(n, true), ?_, ?_⟩
      · simpa [E] using ha
      · exact fun hc => hn (Or.inl hc)
    · apply mem_iUnion.mpr
      refine ⟨(n, false), ?_, ?_⟩
      · simpa [E] using ha
      · exact fun hc => hn (Or.inr hc)
  refine ⟨K, hKclosed.isCompact, ?_, ?_⟩
  · calc
      μ Kᶜ ≤ μ (⋃ p : ℕ × Bool, E p \ C p) := measure_mono hbad
      _ ≤ ∑' p : ℕ × Bool, μ (E p \ C p) := measure_iUnion_le _
      _ ≤ ∑' p : ℕ × Bool, δ p := ENNReal.tsum_le_tsum fun p => (hCmeasure p).le
      _ < ε := hδsum
  · intro n
    refine ⟨(C (n, false))ᶜ, (hCcompact (n, false)).isClosed.isOpen_compl, ?_⟩
    ext x
    constructor
    · rintro ⟨ha, hk⟩
      refine ⟨?_, hk⟩
      intro hc
      have : x ∈ (A n)ᶜ := by simpa [E] using hCsub (n, false) hc
      exact this ha
    · rintro ⟨hc, hk⟩
      refine ⟨?_, hk⟩
      rcases hKmem hk n with ht | hf
      · simpa [E] using hCsub (n, true) ht
      · exact False.elim (hc hf)

theorem exists_compact_continuousOn {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨B, hB⟩ := TopologicalSpace.exists_seq_basis Y
  have hA : ∀ n : ℕ, MeasurableSet (f ⁻¹' B n) := by
    intro n
    exact hf (hB.isOpen (mem_range_self n)).measurableSet
  obtain ⟨K, hK, hμK, hrestr⟩ :=
    exists_compact_clopen_restrictions μ (fun n => f ⁻¹' B n) hA hε
  refine ⟨K, hK, hμK, hB.continuousOn_iff.mpr ?_⟩
  intro U hU
  obtain ⟨n, rfl⟩ := hU
  exact hrestr n

end Invariant233.Lusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_BoundedLusinApproximation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Lusin

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [CompactSpace X] [NormalSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] [Measure.InnerRegularCompactLTTop μ]

theorem exists_bounded_continuous_eq_on_large_compact
    {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖g x‖ ≤ C) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (a : C(X, ℂ)) (K : Set X), IsCompact K ∧ μ Kᶜ < ε ∧
      (∀ x, ‖a x‖ ≤ 2 * C) ∧ Set.EqOn a g K := by
  obtain ⟨K, hK, hμK, hgK⟩ := exists_compact_continuousOn μ hg hε
  let gre : C(K, ℝ) := ⟨fun x => (g x).re, Complex.continuous_re.comp hgK.domRestrict⟩
  let gim : C(K, ℝ) := ⟨fun x => (g x).im, Complex.continuous_im.comp hgK.domRestrict⟩
  have hre : ∀ x : K, gre x ∈ Icc (-C) C := by
    intro x
    exact abs_le.mp ((Complex.abs_re_le_norm (g x)).trans (hb x))
  have him : ∀ x : K, gim x ∈ Icc (-C) C := by
    intro x
    exact abs_le.mp ((Complex.abs_im_le_norm (g x)).trans (hb x))
  have hne : (Icc (-C) C).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨are, hare, heqre⟩ := gre.exists_restrict_eq_forall_mem_of_closed hre hne hK.isClosed
  obtain ⟨aim, haim, heqim⟩ := gim.exists_restrict_eq_forall_mem_of_closed him hne hK.isClosed
  let a : C(X, ℂ) := ⟨fun x => (are x : ℂ) + (aim x : ℂ) * Complex.I, by fun_prop⟩
  refine ⟨a, K, hK, hμK, ?_, ?_⟩
  · intro x
    change ‖(are x : ℂ) + (aim x : ℂ) * Complex.I‖ ≤ 2 * C
    calc
      _ ≤ ‖(are x : ℂ)‖ + ‖(aim x : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |are x| + |aim x| := by simp
      _ ≤ C + C := add_le_add (abs_le.mpr (hare x)) (abs_le.mpr (haim x))
      _ = 2 * C := by ring
  · intro x hx
    have hr := DFunLike.congr_fun heqre ⟨x, hx⟩
    have hi := DFunLike.congr_fun heqim ⟨x, hx⟩
    change are x = (g x).re at hr
    change aim x = (g x).im at hi
    change (are x : ℂ) + (aim x : ℂ) * Complex.I = g x
    rw [hr, hi, Complex.re_add_im]

theorem exists_bounded_continuous_eventuallyEq
    {g : X → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖g x‖ ≤ C) :
    ∃ a : ℕ → C(X, ℂ), (∀ n x, ‖a n x‖ ≤ 2 * C) ∧
      ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a n x = g x := by
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' (by simp : (1 : ℝ≥0∞) ≠ 0) ℕ
  choose a K hK hμK hbA heq using
    (fun n => exists_bounded_continuous_eq_on_large_compact μ hg hC hb (hδpos n).ne')
  have hsum : (∑' n, μ (K n)ᶜ) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum fun n => (hμK n).le
      _ < 1 := hδsum
      _ < ∞ := by simp
  refine ⟨a, hbA, ?_⟩
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with n hn
  exact heq n (by simpa using hn)

end Invariant233.Lusin

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ClosedRangeTransport
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace InvariantRotation.ClosedRangeTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (p : Submodule 𝕜 E) [CompleteSpace p]
variable (f : p →L[𝕜] E) (hinj : Function.Injective f)
variable (hclosed : IsClosed (Set.range f))

theorem partialInverse_comp_forward :
    (partialInverse p f hinj hclosed).comp (forward p f) = p.starProjection := by
  ext x
  exact partialInverse_apply_image p f hinj hclosed (p.orthogonalProjectionOnto x)

theorem forward_comp_partialInverse :
    letI := range_hasOrthogonalProjection p f hclosed
    (forward p f).comp (partialInverse p f hinj hclosed) = f.range.starProjection := by
  let := range_hasOrthogonalProjection p f hclosed
  ext x
  change f (p.orthogonalProjectionOnto
    (((f.equivRange hinj hclosed).symm (f.range.orthogonalProjectionOnto x) : p) : E)) = _
  rw [p.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h := (f.equivRange hinj hclosed).apply_symm_apply
    (f.range.orthogonalProjectionOnto x)
  exact congrArg (fun z : f.range => (z : E)) h

theorem functional_eq_of_cyclic (τ : (E →L[𝕜] E) → 𝕜)
    (hτ : τ ((partialInverse p f hinj hclosed).comp (forward p f)) =
      τ ((forward p f).comp (partialInverse p f hinj hclosed))) :
    letI := range_hasOrthogonalProjection p f hclosed
    τ p.starProjection = τ f.range.starProjection := by
  let := range_hasOrthogonalProjection p f hclosed
  rw [partialInverse_comp_forward, forward_comp_partialInverse] at hτ
  exact hτ

omit [CompleteSpace E] in

theorem range_forward : (forward p f).range = f.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨p.orthogonalProjectionOnto x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    change f (p.orthogonalProjectionOnto x) = f x
    rw [p.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem partialInverse_mem (x : E) : partialInverse p f hinj hclosed x ∈ p := by
  let := range_hasOrthogonalProjection p f hclosed
  exact ((f.equivRange hinj hclosed).symm (f.range.orthogonalProjectionOnto x)).property

theorem projection_comp_partialInverse :
    p.starProjection.comp (partialInverse p f hinj hclosed) =
      partialInverse p f hinj hclosed := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (partialInverse_mem p f hinj hclosed x)

section Algebra

variable {R : Type*} [Monoid R]

theorem commute_partialInverse {a b p q w : R}
    (hba : b * a = p) (hab : a * b = q) (hpb : p * b = b)
    (hwa : Commute w a) (hwp : Commute w p) (hwq : Commute w q) :
    Commute w b := by
  have hbq : b * q = b := by rw [← hab, ← mul_assoc, hba, hpb]
  change w * b = b * w
  calc
    w * b = w * (p * b) := by rw [hpb]
    _ = (w * p) * b := (mul_assoc _ _ _).symm
    _ = (p * w) * b := by rw [hwp.eq]
    _ = ((b * a) * w) * b := by rw [hba]
    _ = (b * (a * w)) * b := by rw [mul_assoc b a w]
    _ = (b * (w * a)) * b := by rw [hwa.eq]
    _ = (b * w) * (a * b) := by simp only [mul_assoc]
    _ = (b * w) * q := by rw [hab]
    _ = b * (w * q) := mul_assoc _ _ _
    _ = b * (q * w) := by rw [hwq.eq]
    _ = (b * q) * w := (mul_assoc _ _ _).symm
    _ = b * w := by rw [hbq]

end Algebra

section VonNeumann

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem range_projection_mem (M : VonNeumannAlgebra F) (a : F →L[ℂ] F)
    (ha : a ∈ M) (hc : IsClosed (Set.range a)) :
    letI : IsClosed (a.range : Set F) := hc
    a.range.starProjection ∈ M := by
  let : IsClosed (a.range : Set F) := hc
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro w hw
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  rintro y ⟨x, rfl⟩
  refine ⟨w x, ?_⟩
  exact congrArg (fun v : F →L[ℂ] F => v x)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) a ha)

theorem partialInverse_mem_algebra
    (M : VonNeumannAlgebra F) (p : Submodule ℂ F) [CompleteSpace p]
    (f : p →L[ℂ] F) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M) (hf : forward p f ∈ M) :
    partialInverse p f hinj hc ∈ M := by
  let := range_hasOrthogonalProjection p f hc
  have hfc : IsClosed (Set.range (forward p f)) := by
    change IsClosed ((forward p f).range : Set F)
    rw [range_forward]
    exact hc
  have hr : f.range.starProjection ∈ M := by
    have hr' := range_projection_mem M (forward p f) hf hfc
    simpa only [range_forward] using hr'
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro w hw
  exact (commute_partialInverse
    (a := forward p f) (b := partialInverse p f hinj hc)
    (p := p.starProjection) (q := f.range.starProjection)
    (partialInverse_comp_forward p f hinj hc)
    (forward_comp_partialInverse p f hinj hc)
    (projection_comp_partialInverse p f hinj hc)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hf).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hp).symm
    ((VonNeumannAlgebra.mem_commutant_iff.mp hw) _ hr).symm).eq

theorem trace_range_eq
    (M : VonNeumannAlgebra F) (p : Submodule ℂ F) [CompleteSpace p]
    (f : p →L[ℂ] F) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M) (hf : forward p f ∈ M)
    (τ : (F →L[ℂ] F) → ℂ)
    (hτ : ∀ a ∈ M, ∀ b ∈ M, τ (a * b) = τ (b * a)) :
    letI := range_hasOrthogonalProjection p f hc
    τ p.starProjection = τ f.range.starProjection := by
  apply functional_eq_of_cyclic p f hinj hc τ
  exact hτ _ (partialInverse_mem_algebra M p f hinj hc hp hf) _ hf

end VonNeumann

omit [CompleteSpace E] in

theorem injective_closedRange_of_bound (K : ℝ≥0)
    (hbound : ∀ x : p, ‖x‖ ≤ K * ‖f x‖) :
    Function.Injective f ∧ IsClosed (Set.range f) := by
  have hanti := f.antilipschitz_of_bound hbound
  exact ⟨hanti.injective, hanti.isClosed_range f.uniformContinuous⟩

end InvariantRotation.ClosedRangeTransport

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

omit [IsFiniteMeasure μ] in

theorem commute_shiftedPullback_of_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (DirectIntegral.shiftedPullback S σ hσ) := by
  change T * DirectIntegral.shiftedPullback S σ hσ =
    DirectIntegral.shiftedPullback S σ hσ * T
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (DirectIntegral.shiftedPullback S σ hσ ξ),
    shiftedPullback_ae S σ hσ ξ, shiftedPullback_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ), hcov] with x hTx hJx hJTx hTσx hcovx
  change (T (DirectIntegral.shiftedPullback S σ hσ ξ)) x =
    (DirectIntegral.shiftedPullback S σ hσ (T ξ)) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun R : E →L[ℂ] E => R (ξ (σ x))) hcovx

end Invariant233.FieldTraceCyclic

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldUnboundedMultiplier
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldUnboundedMultiplier_injective (h : X → ℤ → ℂ)
    (hh : ∀ᵐ x ∂μ, ∀ k, h x k ≠ 0) :
    Function.Injective (fieldUnboundedMultiplier μ h) := by
  intro ξ η heq
  apply Subtype.ext
  apply fieldHilbert_ext
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ,
    fieldUnboundedMultiplier_apply_ae h η, hh] with x hξ hη hh
  intro k
  apply mul_left_cancel₀ (hh k)
  rw [← hξ, ← hη, heq]

theorem fieldUnboundedMultiplier_formalAdjoint (h : X → ℤ → ℂ) :
    (fieldUnboundedMultiplier μ h).IsFormalAdjoint
      (fieldUnboundedMultiplier μ (fun x k => star (h x k))) := by
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldUnboundedMultiplier_apply_ae h ξ,
    fieldUnboundedMultiplier_apply_ae (fun x k => star (h x k)) η] with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply]
  ring

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

theorem norm_fieldDiagonal_le : ‖fieldDiagonal a C hC ha hm‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable {a C hC ha hm}

theorem fieldDiagonal_congr
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    (hab : a =ᵐ[μ] b) :
    fieldDiagonal a C hC ha hm = fieldDiagonal b D hD hb hn := by
  ext f
  filter_upwards [fieldDiagonal_ae a C hC ha hm f,
    fieldDiagonal_ae b D hD hb hn f, hab] with x hx hy hxy
  rw [hx, hy, hxy]

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

theorem fieldDiagonal_norm_map
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) (f : Lp Hilbert 2 μ) :
    ‖fieldDiagonal a C hC ha hm f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ, ‖fieldDiagonal a C hC ha hm f x‖ = ‖f x‖ := by
    filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm f, hunit] with x hx hu
    have hcoord : ∀ k, ‖fieldDiagonal a C hC ha hm f x k‖ = ‖f x k‖ := by
      intro k
      rw [hx, norm_mul, hu, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) fun k => (hcoord k).le)
      (lp.norm_mono (by norm_num) fun k => (hcoord k).symm.le)
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldDiagonal_mem_unitary
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) :
    fieldDiagonal a C hC ha hm ∈ unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  have hb : ∀ x, ‖star (a x)‖ ≤ C := by simpa using ha
  have hn : ∀ k, AEStronglyMeasurable (fun x => star (a x) k) μ := by
    intro k
    simpa only [lp.coeFn_star, Pi.star_apply] using
      continuous_star.comp_aestronglyMeasurable (hm k)
  have hstar : fieldDiagonal (fun x => star (a x)) C hC hb hn =
      star (fieldDiagonal a C hC ha hm) :=
    fieldDiagonal_star_of_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hunitstar : ∀ᵐ x ∂μ, ∀ k, ‖star (a x) k‖ = 1 := by
    simpa only [lp.coeFn_star, Pi.star_apply, norm_star] using hunit
  apply Unitary.mem_iff.mpr
  constructor
  · change ContinuousLinearMap.adjoint (fieldDiagonal a C hC ha hm) ∘L
      fieldDiagonal a C hC ha hm = 1
    exact ContinuousLinearMap.norm_map_iff_adjoint_comp_self _ |>.mp
      (fieldDiagonal_norm_map hunit)
  · have hh := ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (star (fieldDiagonal a C hC ha hm)) |>.mp (fun f => by
        rw [← hstar]
        exact fieldDiagonal_norm_map hunitstar f)
    change star (star (fieldDiagonal a C hC ha hm)) *
      star (fieldDiagonal a C hC ha hm) = 1 at hh
    simpa only [star_star] using hh

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldMultiplierAdjoint
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem normalizer_ne_zero (z : ℂ) : normalizer z ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact inv_ne_zero (by positivity)

private theorem normalizer_star (z : ℂ) : star (normalizer z) = normalizer z := by
  simp [normalizer]

private theorem normalizerOperator_selfAdjoint (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    IsSelfAdjoint (normalizerOperator h hm) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizerOperator_ae h hm ξ, normalizerOperator_ae h hm η]
    with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, normalizer_star]
  ring

private theorem normalizerOperator_injective (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    Function.Injective (normalizerOperator h hm) := by
  intro ξ η heq
  apply fieldHilbert_ext
  filter_upwards [normalizerOperator_ae h hm ξ, normalizerOperator_ae h hm η]
    with x hξ hη
  intro k
  apply mul_left_cancel₀ (normalizer_ne_zero (h x k))
  rw [← hξ, ← hη, heq]

private theorem multiplier_normalizer (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ h
      ⟨normalizerOperator h hm ξ, normalizer_mem_domain h hm ξ⟩ =
        normalizedOperator h hm ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [normalizerOperator_ae h hm ξ, normalizedOperator_ae h hm ξ]
    with x hR hS
  intro k
  rw [hR, hS, mul_assoc]

theorem dense_fieldUnboundedMultiplier_domain (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    Dense ((fieldUnboundedMultiplier μ h).domain : Set (FieldHilbert μ)) := by
  let R := normalizerOperator h hm
  have hs : R.adjoint = R := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (normalizerOperator_selfAdjoint h hm).star_eq
  have hk : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr (normalizerOperator_injective h hm)
  have hc : R.range.topologicalClosure = ⊤ := by
    have heq := R.orthogonal_ker
    rw [hs, hk, Submodule.bot_orthogonal_eq_top] at heq
    exact heq.symm
  have hd : Dense (R.range : Set (FieldHilbert μ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hc
  apply hd.mono
  rintro ξ ⟨η, rfl⟩
  exact normalizer_mem_domain h hm η

private theorem normalizedStarOperator_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    ∀ᵐ x ∂μ, ∀ k, normalizedStarOperator h hm ξ x k =
      (star (h x k) * normalizer (h x k)) * ξ x k := by
  filter_upwards [boundedField_ae
    (fun x k => star (h x k * normalizer (h x k)))
    (fun x k => by simpa only [norm_star] using normalized_bound (h x k))
    (fun k => ((hm k).mul (normalizer_measurable h hm k)).star) ξ] with x hx
  intro k
  simpa only [normalizedStarOperator, star_mul, normalizer_star, mul_comm] using hx k

private theorem normalizedOperator_adjoint (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (normalizedOperator h hm).adjoint = normalizedStarOperator h hm := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizedStarOperator_ae h hm ξ, normalizedOperator_ae h hm η]
    with x hξ hη
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [hξ, hη]
  simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, star_star, normalizer_star]
  ring

theorem adjoint_fieldUnboundedMultiplier_apply_ae (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (ξ : (fieldUnboundedMultiplier μ h).adjoint.domain) :
    ∀ᵐ x ∂μ, ∀ k, (fieldUnboundedMultiplier μ h).adjoint ξ x k =
      star (h x k) * ξ.val x k := by
  let R := normalizerOperator h hm
  let S := normalizedOperator h hm
  have hs : R.adjoint = R := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (normalizerOperator_selfAdjoint h hm).star_eq
  have heq : R ((fieldUnboundedMultiplier μ h).adjoint ξ) = S.adjoint ξ.val := by
    apply ext_inner_right ℂ
    intro η
    calc
      inner ℂ (R ((fieldUnboundedMultiplier μ h).adjoint ξ)) η =
          inner ℂ ((fieldUnboundedMultiplier μ h).adjoint ξ) (R η) := by
        simpa only [hs] using
          R.adjoint_inner_left η ((fieldUnboundedMultiplier μ h).adjoint ξ)
      _ = inner ℂ ξ.val (S η) := by
        have hf := LinearPMap.adjoint_isFormalAdjoint
          (dense_fieldUnboundedMultiplier_domain h hm) ξ
          ⟨R η, normalizer_mem_domain h hm η⟩
        simpa only [R, S, multiplier_normalizer] using hf
      _ = inner ℂ (S.adjoint ξ.val) η := (S.adjoint_inner_left η ξ.val).symm
  have heq' : normalizerOperator h hm ((fieldUnboundedMultiplier μ h).adjoint ξ) =
      normalizedStarOperator h hm ξ.val := by
    simpa only [R, S, normalizedOperator_adjoint] using heq
  filter_upwards [normalizerOperator_ae h hm ((fieldUnboundedMultiplier μ h).adjoint ξ),
    normalizedStarOperator_ae h hm ξ.val] with x hR hS
  intro k
  apply mul_left_cancel₀ (normalizer_ne_zero (h x k))
  calc
    normalizer (h x k) * (fieldUnboundedMultiplier μ h).adjoint ξ x k =
        normalizerOperator h hm ((fieldUnboundedMultiplier μ h).adjoint ξ) x k :=
      (hR k).symm
    _ = normalizedStarOperator h hm ξ.val x k := by rw [heq']
    _ = (star (h x k) * normalizer (h x k)) * ξ.val x k := hS k
    _ = normalizer (h x k) * (star (h x k) * ξ.val x k) := by ring

theorem adjoint_fieldUnboundedMultiplier (h : X → ℤ → ℂ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    (fieldUnboundedMultiplier μ h).adjoint =
      fieldUnboundedMultiplier μ (fun x k => star (h x k)) := by
  apply le_antisymm
  · constructor
    · intro ξ hξ
      apply (mem_fieldUnboundedMultiplier_domain_iff _ _).mpr
      exact ⟨(fieldUnboundedMultiplier μ h).adjoint ⟨ξ, hξ⟩,
        adjoint_fieldUnboundedMultiplier_apply_ae h hm ⟨ξ, hξ⟩⟩
    · intro ξ η hξη
      symm
      apply fieldUnboundedMultiplier_eq_of_ae
      filter_upwards [adjoint_fieldUnboundedMultiplier_apply_ae h hm ξ] with x hx
      intro k
      rw [hx, hξη]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint
      (dense_fieldUnboundedMultiplier_domain h hm)
      (fieldUnboundedMultiplier_formalAdjoint h)

theorem isSelfAdjoint_fieldUnboundedMultiplier_real (h : X → ℤ → ℝ)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) :
    IsSelfAdjoint (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) := by
  rw [LinearPMap.isSelfAdjoint_def,
    adjoint_fieldUnboundedMultiplier _
      (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k))]
  congr 1
  funext x k
  simp

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldMultiplierCutoff
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.WeightedShift.SpectralCutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem symbol_mul_self (n : ℕ) (r : ℝ) : symbol n r * symbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n <;> simp [symbol, hr]

theorem star_symbol (n : ℕ) (r : ℝ) : star (symbol n r) = symbol n r := by
  classical
  by_cases hr : r ∈ window n <;> simp [symbol, hr]

theorem projection_isStarProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    IsStarProjection (projection (μ := μ) h hm n) := by
  constructor
  · change projection h hm n * projection h hm n = projection h hm n
    apply ContinuousLinearMap.ext
    intro ξ
    apply fieldHilbert_ext
    filter_upwards [projection_ae h hm n ξ,
      projection_ae h hm n (projection h hm n ξ)] with x hξ hE
    intro k
    change projection h hm n (projection h hm n ξ) x k = projection h hm n ξ x k
    rw [hE, hξ, ← mul_assoc, symbol_mul_self]
  · rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro ξ η
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [projection_ae h hm n ξ, projection_ae h hm n η] with x hξ hη
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro k
    rw [hξ, hη]
    simp only [RCLike.inner_apply', map_mul, starRingEnd_apply, star_symbol]
    ring

theorem symbol_eventually_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, symbol n r = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max r r⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hrn : r ≤ n + 1 := by have := le_max_left r r⁻¹; linarith
  have hirn : r⁻¹ ≤ n + 1 := by have := le_max_right r r⁻¹; linarith
  have hin : r ∈ window n :=
    ⟨(inv_le_comm₀ (by positivity) hr).mpr hirn, hrn⟩
  simp [symbol, hin]

theorem fiber_error_norm_le (h : ℤ → ℝ) (n : ℕ) (ξ : Hilbert) :
    ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
      (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ≤ ‖ξ‖ := by
  apply lp.norm_mono (by norm_num)
  intro k
  change ‖symbol n (h k) * ξ k - ξ k‖ ≤ ‖ξ k‖
  classical
  by_cases hk : h k ∈ window n <;> simp [symbol, hk]

theorem fiber_error_sq_tendsto (h : ℤ → ℝ) (hh : ∀ k, 0 < h k) (ξ : Hilbert) :
    Tendsto (fun n => ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
      (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ^ 2) atTop (𝓝 0) := by
  have hsum : Summable (fun k => ‖ξ k‖ ^ 2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun n k => ‖symbol n (h k) * ξ k - ξ k‖ ^ 2)
    (g := fun _ : ℤ => (0 : ℝ)) hsum
    (fun k => tendsto_const_nhds.congr' ((symbol_eventually_one (hh k)).mono
      (fun n hn => by simp [hn])))
    (Filter.Eventually.of_forall fun n k => by
      classical
      by_cases hk : h k ∈ window n <;> simp [symbol, hk])
  have heq (n : ℕ) :
      ‖diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
        (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ‖ ^ 2 =
          ∑' k, ‖symbol n (h k) * ξ k - ξ k‖ ^ 2 := by
    simpa [boundedWeight] using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h k)) 1
        (fun _ k => norm_symbol_le n (h k)) ()) ξ - ξ)
  simpa only [← heq, tsum_zero] using ht

theorem norm_sq_eq_integral (ξ : FieldHilbert μ) :
    ‖ξ‖ ^ 2 = ∫ x, ‖ξ x‖ ^ 2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def]
  have hr := integral_re (L2.integrable_inner (𝕜 := ℂ) ξ ξ)
  simp only [RCLike.re_eq_complex_re] at hr ⊢
  rw [← hr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => inner_self_eq_norm_sq (𝕜 := ℂ) (ξ x)

theorem projection_tendsto (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (ξ : FieldHilbert μ) :
    Tendsto (fun n => projection h hm n ξ) atTop (𝓝 ξ) := by
  let D : ℕ → FieldHilbert μ := fun n => projection h hm n ξ - ξ
  have hD (n : ℕ) : ∀ᵐ x ∂μ, D n x =
      diagonal (boundedWeight (fun (_ : Unit) k => symbol n (h x k)) 1
        (fun _ k => norm_symbol_le n (h x k)) ()) (ξ x) - ξ x := by
    filter_upwards [projection_ae h hm n ξ, Lp.coeFn_sub (projection h hm n ξ) ξ]
      with x hE hsub
    change (projection h hm n ξ - ξ) x = _
    rw [hsub]
    apply lp.ext
    funext k
    change projection h hm n ξ x k - ξ x k = symbol n (h x k) * ξ x k - ξ x k
    rw [hE]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖D n x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_all_iff.mpr hD, hh] with x hx hh
    simp only [hx]
    exact fiber_error_sq_tendsto (h x) hh (ξ x)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖‖D n x‖ ^ 2‖ ≤ ‖ξ x‖ ^ 2 := by
    filter_upwards [hD n] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _), hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (fiber_error_norm_le (h x) n (ξ x)) 2
  have hi : Integrable (fun x => ‖ξ x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp (Lp.memLp ξ)
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖ξ x‖ ^ 2)
    (fun n => ((Lp.aestronglyMeasurable (D n)).norm).pow 2) hi hb hlim
  have hs : Tendsto (fun n => ‖D n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.pow_apply, ← norm_sq_eq_integral, integral_zero] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

theorem norm_boundedOperator_le (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    ‖boundedOperator a C hC ha hm‖ ≤ C :=
  norm_fieldDiagonal_le _ _ _ _ _

theorem norm_productOperator_le (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    ‖productOperator (μ := μ) h hm n‖ ≤ n + 1 := norm_boundedOperator_le _ _ _ _ _

theorem norm_inverseOperator_le (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    ‖inverseOperator (μ := μ) h hm n‖ ≤ n + 1 := norm_boundedOperator_le _ _ _ _ _

theorem multiplier_projection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨projection h hm n ξ, projection_mem_domain h hm n ξ⟩ = productOperator h hm n ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ] with x hP hT
  intro k
  rw [hP, hT]
  exact mul_assoc _ _ _

theorem inverseSymbol_mul_productSymbol (n : ℕ) (r : ℝ) :
    inverseSymbol n r * productSymbol n r = symbol n r := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hr.1)
    simp [inverseSymbol, productSymbol, symbol, hr, hr0]
  · simp [inverseSymbol, productSymbol, symbol, hr]

theorem inverseOperator_mul_productOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    inverseOperator (μ := μ) h hm n * productOperator h hm n = projection h hm n := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply fieldHilbert_ext
  filter_upwards [projection_ae h hm n ξ, productOperator_ae h hm n ξ,
    inverseOperator_ae h hm n (productOperator h hm n ξ)] with x hP hT hI
  intro k
  change inverseOperator h hm n (productOperator h hm n ξ) x k = projection h hm n ξ x k
  rw [hI, hT, hP, ← mul_assoc, inverseSymbol_mul_productSymbol]

theorem projection_apply_of_mem_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    {ξ : FieldHilbert μ} (hξ : ξ ∈ (projection h hm n).range) : projection h hm n ξ = ξ := by
  obtain ⟨η, rfl⟩ := hξ
  exact congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A η)
    (projection_isStarProjection h hm n).isIdempotentElem.eq

theorem multiplier_on_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨ξ.val, projection_range_le_domain h hm n ξ.property⟩ = productOperator h hm n ξ.val := by
  have hmP := multiplier_projection h hm n ξ.val
  have heq := projection_apply_of_mem_range h hm n ξ.property
  simpa only [heq] using hmP

theorem multiplier_range_bounds (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    let η := fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨ξ.val, projection_range_le_domain h hm n ξ.property⟩
    ‖η‖ ≤ (n + 1 : ℝ) * ‖ξ.val‖ ∧ ‖ξ.val‖ ≤ (n + 1 : ℝ) * ‖η‖ := by
  dsimp only
  rw [multiplier_on_range]
  constructor
  · exact (productOperator h hm n).le_of_opNorm_le (norm_productOperator_le h hm n) ξ.val
  · have heq : inverseOperator h hm n (productOperator h hm n ξ.val) = ξ.val := by
      have he := congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A ξ.val)
        (inverseOperator_mul_productOperator (μ := μ) h hm n)
      exact he.trans (projection_apply_of_mem_range h hm n ξ.property)
    have hb := (inverseOperator h hm n).le_of_opNorm_le (norm_inverseOperator_le h hm n)
      (productOperator h hm n ξ.val)
    rwa [heq] at hb

theorem inverse_multiplier_projection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ) (ξ : FieldHilbert μ) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨projection h hm n ξ, projection_mem_inverse_domain h hm n ξ⟩ = inverseOperator h hm n ξ := by
  have hker : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).toFun.ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    apply fieldUnboundedMultiplier_injective
    filter_upwards [hh] with x hx k
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (hx k))
  exact LinearPMap.inverse_apply_eq
    (y := ⟨projection h hm n ξ, projection_mem_inverse_domain h hm n ξ⟩)
    (x := ⟨inverseOperator h hm n ξ, inverseOperator_mem_domain h hm n ξ⟩)
    hker (multiplier_inverseOperator h hm n ξ)

theorem inverse_multiplier_on_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨ξ.val, projection_range_le_inverse_domain h hm n ξ.property⟩ = inverseOperator h hm n ξ.val := by
  have hmP := inverse_multiplier_projection h hm hh n ξ.val
  have heq := projection_apply_of_mem_range h hm n ξ.property
  simpa only [heq] using hmP

theorem productOperator_mul_inverseOperator (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    productOperator (μ := μ) h hm n * inverseOperator h hm n = projection h hm n := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply fieldHilbert_ext
  filter_upwards [projection_ae h hm n ξ, inverseOperator_ae h hm n ξ,
    productOperator_ae h hm n (inverseOperator h hm n ξ)] with x hP hI hT
  intro k
  change productOperator h hm n (inverseOperator h hm n ξ) x k = projection h hm n ξ x k
  rw [hT, hI, hP, ← mul_assoc, mul_comm (productSymbol n _) (inverseSymbol n _),
    inverseSymbol_mul_productSymbol]

theorem inverse_multiplier_range_bounds (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (n : ℕ)
    (ξ : (projection (μ := μ) h hm n).range) :
    let η := (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse
      ⟨ξ.val, projection_range_le_inverse_domain h hm n ξ.property⟩
    ‖η‖ ≤ (n + 1 : ℝ) * ‖ξ.val‖ ∧ ‖ξ.val‖ ≤ (n + 1 : ℝ) * ‖η‖ := by
  dsimp only
  rw [inverse_multiplier_on_range h hm hh]
  constructor
  · exact (inverseOperator h hm n).le_of_opNorm_le (norm_inverseOperator_le h hm n) ξ.val
  · have heq : productOperator h hm n (inverseOperator h hm n ξ.val) = ξ.val := by
      have he := congrArg (fun A : FieldHilbert μ →L[ℂ] FieldHilbert μ => A ξ.val)
        (productOperator_mul_inverseOperator (μ := μ) h hm n)
      exact he.trans (projection_apply_of_mem_range h hm n ξ.property)
    have hb := (productOperator h hm n).le_of_opNorm_le (norm_productOperator_le h hm n)
      (inverseOperator h hm n ξ.val)
    rwa [heq] at hb

theorem cutoffSpace_eq_range (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    cutoffSpace (μ := μ) h hm n = (projection h hm n).range := by
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (projection_isStarProjection h hm n).isIdempotentElem).submodule_topologicalClosure_eq

theorem cutoffSpace_starProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (cutoffSpace (μ := μ) h hm n).starProjection = projection h hm n := by
  obtain ⟨hi, he⟩ := isStarProjection_iff_eq_starProjection_range.mp
    (projection_isStarProjection (μ := μ) h hm n)
  let := hi
  simpa only [cutoffSpace_eq_range] using he.symm

theorem cutoffSpace_tendsto (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k))
    (hh : ∀ᵐ x ∂μ, ∀ k, 0 < h x k) (ξ : FieldHilbert μ) :
    Tendsto (fun n => (cutoffSpace h hm n).starProjection ξ) atTop (𝓝 ξ) := by
  simpa only [cutoffSpace_starProjection] using projection_tendsto h hm hh ξ

theorem cutoffSpace_le_domains (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    cutoffSpace (μ := μ) h hm n ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain ∧
    cutoffSpace (μ := μ) h hm n ≤
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).inverse.domain := by
  rw [cutoffSpace_eq_range]
  exact ⟨projection_range_le_domain h hm n, projection_range_le_inverse_domain h hm n⟩

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_AffiliatedTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantRotation.AffiliatedTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem domainImage_invariant
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) (A B : E →L[𝕜] E)
    (hAp : ∀ x ∈ p, A x ∈ p)
    (hAD : ∀ x ∈ H.domain, A x ∈ H.domain)
    (hAB : ∀ x : H.domain, H ⟨A x, hAD x x.property⟩ = B (H x)) :
    ∀ y ∈ domainImage H p, B y ∈ domainImage H p := by
  intro y hy
  obtain ⟨x, hxp, rfl⟩ := mem_domainImage.mp hy
  exact mem_domainImage.mpr
    ⟨⟨A x, hAD x x.property⟩, hAp x hxp, hAB x⟩

theorem transported_invariant
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) (A B : E →L[𝕜] E)
    (hAp : ∀ x ∈ p, A x ∈ p)
    (hAD : ∀ x ∈ H.domain, A x ∈ H.domain)
    (hAB : ∀ x : H.domain, H ⟨A x, hAD x x.property⟩ = B (H x)) :
    ∀ y ∈ transported H p, B y ∈ transported H p := by
  have hi : domainImage H p ∈ Module.End.invtSubmodule B.toLinearMap :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (domainImage_invariant H p A B hAp hAD hAB)
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
    (Submodule.topologicalClosure_mem_invtSubmodule hi)

theorem mem_transported_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (x : H.domain) (hx : H x ∈ pᗮ) :
    (x : E) ∈ (transported H p)ᗮ := by
  rw [transported, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨z, hzp, rfl⟩ := mem_domainImage.mp hy
  rw [hH z x]
  exact p.inner_right_of_mem_orthogonal hzp hx

theorem inverse_domainImage_le_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥) :
    domainImage H.inverse pᗮ ≤ (transported H p)ᗮ := by
  intro y hy
  obtain ⟨z, hzp, rfl⟩ := mem_domainImage.mp hy
  have hz : (z : E) ∈ LinearMap.range H.toFun := by
    simpa only [LinearPMap.inverse_domain] using z.property
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hz
  have hpartialker : H.toFun.ker = ⊥ := hker
  rw [LinearPMap.inverse_apply_eq hpartialker hx]
  apply mem_transported_orthogonal H p hH x
  change H.toFun x ∈ pᗮ
  rw [hx]
  exact hzp

theorem inverse_transported_le_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥) :
    transported H.inverse pᗮ ≤ (transported H p)ᗮ :=
  Submodule.topologicalClosure_minimal _
    (inverse_domainImage_le_orthogonal H p hH hker)
    (Submodule.isClosed_orthogonal _)


end InvariantRotation.AffiliatedTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialProjectionTransport
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem vectorTrace_le_of_cutoff_estimates
    (ξ : H) (p q : Submodule ℂ H)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (E : ℕ → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hE : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hbound : ∀ n, (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ q.starProjection).re) :
    (vectorTrace ξ p.starProjection).re ≤ (vectorTrace ξ q.starProjection).re := by
  have ht : Tendsto (fun n => inner ℂ ξ ((E n).starProjection ξ))
      atTop (𝓝 (inner ℂ ξ ξ)) := tendsto_const_nhds.inner hE
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  have he : Tendsto (fun n => (vectorTrace ξ (E n).starProjection).re)
      atTop (𝓝 (‖ξ‖ ^ 2)) := by
    have hnorm : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
    rw [hnorm] at hr
    exact hr
  have hlim : Tendsto (fun n => (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2) atTop
      (𝓝 ((vectorTrace ξ p.starProjection).re + ‖ξ‖ ^ 2 - ‖ξ‖ ^ 2)) :=
    (tendsto_const_nhds.add he).sub_const (‖ξ‖ ^ 2)
  have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa only [add_sub_cancel_right] using hle

theorem vectorTrace_eq_of_cutoff_estimates
    (ξ : H) (p q : Submodule ℂ H)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (E : ℕ → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hE : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hforward : ∀ n, (vectorTrace ξ p.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ q.starProjection).re)
    (hbackward : ∀ n, (vectorTrace ξ pᗮ.starProjection).re +
      (vectorTrace ξ (E n).starProjection).re - ‖ξ‖ ^ 2 ≤
        (vectorTrace ξ qᗮ.starProjection).re) :
    vectorTrace ξ p.starProjection = vectorTrace ξ q.starProjection := by
  have hle := vectorTrace_le_of_cutoff_estimates ξ p q E hE hforward
  have hge := vectorTrace_le_of_cutoff_estimates ξ pᗮ qᗮ E hE hbackward
  rw [vectorTrace_projection_orthogonal, vectorTrace_projection_orthogonal] at hge
  have hre : (vectorTrace ξ p.starProjection).re =
      (vectorTrace ξ q.starProjection).re := by
    simp only [Complex.sub_re] at hge
    linarith
  rw [vectorTrace_projection_re, vectorTrace_projection_re] at hre
  rw [vectorTrace_projection, vectorTrace_projection]
  exact_mod_cast hre

theorem vectorTrace_closedRange_eq
    [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (p : Submodule ℂ H) [CompleteSpace p]
    (f : p →L[ℂ] H) (hinj : Function.Injective f)
    (hc : IsClosed (Set.range f))
    (hp : p.starProjection ∈ M)
    (hf : InvariantRotation.ClosedRangeTransport.forward p f ∈ M) :
    letI : IsClosed (f.range : Set H) := hc
    vectorTrace ξ p.starProjection = vectorTrace ξ f.range.starProjection := by
  exact InvariantRotation.ClosedRangeTransport.trace_range_eq M p f hinj hc hp hf
    (vectorTrace ξ) (fun a ha b hb => hξ.2.1 a b ha hb)


variable [CompleteSpace H]

omit [CompleteSpace H] in

theorem cutoffMap_range_le_transported
    (T : H →ₗ.[ℂ] H) (p r : Submodule ℂ H) (hrp : r ≤ p) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖) :
    (cutoffMap T r hrD K hupper).range ≤
      InvariantRotation.AffiliatedTransport.transported T p := by
  rintro y ⟨x, rfl⟩
  apply (InvariantRotation.AffiliatedTransport.domainImage T p).le_topologicalClosure
  apply InvariantRotation.AffiliatedTransport.mem_domainImage.mpr
  exact ⟨⟨x, hrD x.property⟩, hrp x.property, rfl⟩

theorem cutoff_trace_le_transported
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (p r : Submodule ℂ H) [CompleteSpace r]
    (hrp : r ≤ p) (hrD : r ≤ T.domain)
    (K : ℝ) (hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ K * ‖x‖)
    (L : ℝ≥0) (hlower : ∀ x : r, ‖x‖ ≤ L * ‖T ⟨x, hrD x.property⟩‖)
    (hr : r.starProjection ∈ M)
    (hf : InvariantRotation.ClosedRangeTransport.forward r
      (cutoffMap T r hrD K hupper) ∈ M) :
    (vectorTrace ξ r.starProjection).re ≤
      (vectorTrace ξ (InvariantRotation.AffiliatedTransport.transported T p).starProjection).re := by
  let f := cutoffMap T r hrD K hupper
  have hbounds := InvariantRotation.ClosedRangeTransport.injective_closedRange_of_bound
    r f L hlower
  let : IsClosed (f.range : Set H) := hbounds.2
  have htrace := vectorTrace_closedRange_eq M ξ hξ r f hbounds.1 hbounds.2 hr hf
  apply (congrArg Complex.re htrace).trans_le
  exact vectorTrace_projection_mono ξ
    (cutoffMap_range_le_transported T p r hrp hrD K hupper)


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

theorem faithful_vectorTrace_meet_lower_bound
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (p q : Submodule ℂ H) [CompleteSpace p] [CompleteSpace q]
    (hp : p.starProjection ∈ M) (hq : q.starProjection ∈ M) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ q.starProjection).re - 1 ≤
      (vectorTrace ξ (p ⊓ q).starProjection).re := by
  simpa only [hξ.1, one_pow] using vectorTrace_meet_lower_bound M ξ hξ.2.1 p q hp hq

end Invariant233.ProjectionMeetTrace

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_AffiliatedTraceCutoffs
attribute [-instance] _root_.OAI.Invariant233.AffiliatedTransport.instCompleteSpaceSubtypeMemSubmoduleComplexClosedImageOn _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal
namespace Invariant233.AffiliatedTraceCutoffs
open InvariantRotation.AffiliatedTransport
open InvariantRotation.ClosedRangeTransport
open TracialProjectionTransport ProjectionMeetTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem trace_lower_of_cutoff
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (p E : Submodule ℂ H)
    [CompleteSpace p] [CompleteSpace E]
    (hp : p.starProjection ∈ M) (hE : E.starProjection ∈ M)
    (hED : E ≤ T.domain) (F : H →L[ℂ] H) (hF : F ∈ M)
    (hTF : ∀ x : E, T ⟨x, hED x.property⟩ = F x)
    (L : ℝ≥0) (hlower : ∀ x : E, ‖x‖ ≤ L * ‖F x‖) :
    (vectorTrace ξ p.starProjection).re + (vectorTrace ξ E.starProjection).re - 1 ≤
      (vectorTrace ξ (transported T p).starProjection).re := by
  let r := p ⊓ E
  have hrD : r ≤ T.domain := inf_le_right.trans hED
  have hupper : ∀ x : r, ‖T ⟨x, hrD x.property⟩‖ ≤ ‖F‖ * ‖x‖ := by
    intro x
    rw [hTF ⟨x, x.property.2⟩]
    exact F.le_opNorm x
  have hlower' : ∀ x : r, ‖x‖ ≤ L * ‖T ⟨x, hrD x.property⟩‖ := by
    intro x
    rw [hTF ⟨x, x.property.2⟩]
    exact hlower ⟨x, x.property.2⟩
  have hrmem : r.starProjection ∈ M := meet_projection_mem M p E hp hE
  have hforward : forward r (cutoffMap T r hrD ‖F‖ hupper) = F * r.starProjection := by
    ext x
    exact hTF ⟨r.starProjection x, (r.starProjection_apply_mem x).2⟩
  have hforwardmem : forward r (cutoffMap T r hrD ‖F‖ hupper) ∈ M := by
    rw [hforward]
    exact mul_mem hF hrmem
  exact (faithful_vectorTrace_meet_lower_bound M ξ hξ p E hp hE).trans
    (cutoff_trace_le_transported M ξ hξ T p r inf_le_left hrD ‖F‖ hupper L
      hlower' hrmem hforwardmem)

theorem vectorTrace_transported_eq_of_cutoffs
    (M : VonNeumannAlgebra H) (ξ : H) (hξ : IsFaithfulTracialVector M ξ)
    (T : H →ₗ.[ℂ] H) (hT : T.IsFormalAdjoint T) (hinj : T.toFun.ker = ⊥)
    (p : Submodule ℂ H) [CompleteSpace p] (hp : p.starProjection ∈ M)
    (E : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (E n)]
    (hE : ∀ n, (E n).starProjection ∈ M)
    (hlim : Tendsto (fun n => (E n).starProjection ξ) atTop (𝓝 ξ))
    (hED : ∀ n, E n ≤ T.domain) (hEinvD : ∀ n, E n ≤ T.inverse.domain)
    (F G : ℕ → H →L[ℂ] H) (hF : ∀ n, F n ∈ M) (hG : ∀ n, G n ∈ M)
    (hTF : ∀ n, ∀ x : E n, T ⟨x, hED n x.property⟩ = F n x)
    (hTG : ∀ n, ∀ x : E n, T.inverse ⟨x, hEinvD n x.property⟩ = G n x)
    (L R : ℕ → ℝ≥0)
    (hlower : ∀ n, ∀ x : E n, ‖x‖ ≤ L n * ‖F n x‖)
    (hinvlower : ∀ n, ∀ x : E n, ‖x‖ ≤ R n * ‖G n x‖) :
    vectorTrace ξ (transported T p).starProjection = vectorTrace ξ p.starProjection := by
  have hpperp : pᗮ.starProjection ∈ M := by
    simpa only [Submodule.starProjection_orthogonal, ← ContinuousLinearMap.one_def] using
      (sub_mem (one_mem M) hp : (1 : H →L[ℂ] H) - p.starProjection ∈ M)
  have hortho := inverse_transported_le_orthogonal T p hT hinj
  apply Eq.symm
  apply vectorTrace_eq_of_cutoff_estimates ξ p (transported T p) E hlim
  · intro n
    simpa only [hξ.1, one_pow] using
      trace_lower_of_cutoff M ξ hξ T p (E n) hp (hE n) (hED n)
        (F n) (hF n) (hTF n) (L n) (hlower n)
  · intro n
    have hcut := trace_lower_of_cutoff M ξ hξ T.inverse pᗮ (E n)
      hpperp (hE n) (hEinvD n) (G n) (hG n) (hTG n) (R n) (hinvlower n)
    have hmono := vectorTrace_projection_mono ξ hortho
    simpa only [hξ.1, one_pow] using hcut.trans hmono

end Invariant233.AffiliatedTraceCutoffs

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_AffiliatedTransportSupplement
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.AffiliatedTransport

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem imageOn_invariant (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (A B : E →L[ℂ] E)
    (hD : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hD x⟩ = B (H x))
    (hp : ∀ x ∈ p, A x ∈ p) :
    ∀ y ∈ imageOn H p, B y ∈ imageOn H p := by
  rintro y ⟨x, hx, rfl⟩
  exact (mem_imageOn).2 ⟨⟨A (x : E), hD x⟩, hp x hx, hI x⟩

theorem closedImageOn_invariant (H : E →ₗ.[ℂ] E) (p : Submodule ℂ E)
    (A B : E →L[ℂ] E)
    (hD : ∀ x : H.domain, A (x : E) ∈ H.domain)
    (hI : ∀ x : H.domain, H ⟨A (x : E), hD x⟩ = B (H x))
    (hp : ∀ x ∈ p, A x ∈ p) :
    ∀ y ∈ closedImageOn H p, B y ∈ closedImageOn H p := by
  have hmap : (imageOn H p).map B.toLinearMap ≤ imageOn H p := by
    rintro y ⟨x, hx, rfl⟩
    exact imageOn_invariant H p A B hD hI hp x hx
  intro y hy
  change B y ∈ (imageOn H p).topologicalClosure
  apply Submodule.topologicalClosure_mono hmap
  apply Submodule.topologicalClosure_map B (imageOn H p)
  exact ⟨y, hy, rfl⟩

theorem closedImageOn_invariant_of_commuting (H : E →ₗ.[ℂ] E)
    (p : Submodule ℂ E) (W : E →L[ℂ] E)
    (hD : ∀ x : H.domain, W (x : E) ∈ H.domain)
    (hC : ∀ x : H.domain, H ⟨W (x : E), hD x⟩ = W (H x))
    (hp : ∀ x ∈ p, W x ∈ p) :
    ∀ y ∈ closedImageOn H p, W y ∈ closedImageOn H p :=
  closedImageOn_invariant H p W W hD hC hp

end Invariant233.AffiliatedTransport

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ContinuousCircleImage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set

namespace Invariant233.ContinuousCircleImage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_natCast (n : ℕ) :
    (fourier (n : ℤ) : C(AddCircle (1 : ℝ), ℂ)) = fourier 1 ^ n := by
  induction n with
  | zero =>
    ext x
    simp only [Nat.cast_zero, pow_zero, ContinuousMap.one_apply]
    exact fourier_zero
  | succ n ih =>
    ext x
    rw [Nat.cast_succ]
    change fourier ((n : ℤ) + 1) x = (fourier 1 ^ (n + 1)) x
    rw [fourier_add, pow_succ, ContinuousMap.mul_apply, ← ih]

theorem isClosed_vonNeumannAlgebra (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

theorem image_mem
    (Φ : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (hΦ : Continuous Φ)
    (M : VonNeumannAlgebra H) (hV : Φ (fourier 1) ∈ M)
    (f : C(AddCircle (1 : ℝ), ℂ)) : Φ f ∈ M := by
  have hNat : ∀ n : ℕ, Φ (fourier (n : ℤ)) ∈ M := by
    intro n
    rw [fourier_natCast, map_pow]
    exact pow_mem hV n
  have hFourier : ∀ n : ℤ, Φ (fourier n) ∈ M := by
    intro n
    cases n with
    | ofNat n => exact hNat n
    | negSucc n =>
      have heq : (fourier (Int.negSucc n) : C(AddCircle (1 : ℝ), ℂ)) =
          star (fourier ((n + 1 : ℕ) : ℤ)) := by
        ext x
        change fourier (-((n + 1 : ℕ) : ℤ)) x = star (fourier ((n + 1 : ℕ) : ℤ) x)
        exact fourier_neg
      rw [heq, map_star]
      exact star_mem (hNat (n + 1))
  let K : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    M.toStarSubalgebra.toSubalgebra.toSubmodule.comap Φ.toAlgHom.toLinearMap
  have hK : IsClosed (K : Set C(AddCircle (1 : ℝ), ℂ)) :=
    (isClosed_vonNeumannAlgebra M).preimage hΦ
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hFourier n
  have hclosure := (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure_minimal hspan hK
  rw [span_fourier_closure_eq_top] at hclosure
  exact hclosure (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(AddCircle (1 : ℝ), ℂ)))

end Invariant233.ContinuousCircleImage

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonalConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem fieldDiagonal_tendsto_apply
    (a : ℕ → X → Weight) (b : X → Weight)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n x, ‖a n x‖ ≤ C) (hb : ∀ x, ‖b x‖ ≤ D)
    (hma : ∀ n k, AEStronglyMeasurable (fun x => a n x k) μ)
    (hmb : ∀ k, AEStronglyMeasurable (fun x => b x k) μ)
    (hab : ∀ᵐ x ∂μ, ∀ k, Tendsto (fun n => a n x k) atTop (𝓝 (b x k)))
    (v : Lp Hilbert 2 μ) :
    Tendsto (fun n => fieldDiagonal (a n) C hC (ha n) (hma n) v)
      atTop (𝓝 (fieldDiagonal b D hD hb hmb v)) := by
  apply lp_tendsto_of_ae_of_dominated ((Lp.memLp v).norm.const_mul C)
  · intro n
    filter_upwards [fieldDiagonal_ae (a n) C hC (ha n) (hma n) v] with x hx
    rw [hx]
    exact (diagonal (a n x)).le_of_opNorm_le
      ((lp.norm_mapCLM_le 2 _ (norm_nonneg (a n x)) _).trans (ha n x)) (v x)
  · have hall : ∀ᵐ x ∂μ, ∀ n,
        fieldDiagonal (a n) C hC (ha n) (hma n) v x = diagonal (a n x) (v x) := by
      rw [ae_all_iff]
      intro n
      exact fieldDiagonal_ae (a n) C hC (ha n) (hma n) v
    filter_upwards [hall, fieldDiagonal_ae b D hD hb hmb v, hab] with x hx hy hxy
    simp_rw [hx, hy]
    exact diagonal_tendsto_apply (Eventually.of_forall fun n => ha n x) hxy (v x)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_Rotation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

theorem representation_norm_le (θ : ℝ) (a : C(Circle, ℂ)) :
    ‖representation θ a‖ ≤ ‖a‖ := by
  unfold representation
  exact WeightedShift.norm_fieldDiagonal_le _ _ _ _ _

theorem representation_continuous (θ : ℝ) : Continuous (representation θ) := by
  let L := (representationStarAlgHom θ).toAlgHom.toLinearMap
  have hL : ∀ a : C(Circle, ℂ), ‖L a‖ ≤ (1 : ℝ) * ‖a‖ := by
    intro a
    change ‖representation θ a‖ ≤ (1 : ℝ) * ‖a‖
    simpa only [one_mul] using representation_norm_le θ a
  exact (L.mkContinuous 1 hL).continuous

theorem U_mem_unitary : U ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem V_mem_unitary (θ : ℝ) : V θ ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  unfold V representation
  apply WeightedShift.fieldDiagonal_mem_unitary
  exact Filter.Eventually.of_forall fun x k => character_norm (action θ k x)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationAlgebra
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem V_mem_algebra (θ : ℝ) : V θ ∈ algebra θ :=
  subset_vonNeumannGenerated _ (Set.mem_insert_of_mem U (Set.mem_singleton _))

theorem representation_mem_algebra (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a ∈ algebra θ :=
  ContinuousCircleImage.image_mem (representationStarAlgHom θ) (representation_continuous θ)
    (algebra θ) (V_mem_algebra θ) a

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem commute_star_left_of_mem_unitary {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ unitary (Hilbert →L[ℂ] Hilbert)) (hAB : Commute A B) :
    Commute (star A) B := by
  obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp hA
  show star A * B = B * star A
  calc
    star A * B = star A * (B * (A * star A)) := by rw [h₂, mul_one]
    _ = star A * ((A * B) * star A) := by rw [← mul_assoc B A, ← hAB.eq]
    _ = (star A * A) * (B * star A) := by simp only [mul_assoc]
    _ = B * star A := by rw [h₁, one_mul]

theorem U_commutes_multiplier (g : Lp ℂ ∞ circleMeasure) :
    Commute U (L2Multiplication.multiplier (E := Fiber) g) := by
  show U * L2Multiplication.multiplier g = L2Multiplication.multiplier g * U
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [U_coordinates_ae (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ, L2Multiplication.multiplier_coe g (U ξ),
    U_coordinates_ae ξ] with x hU hM hMU hUξ
  intro k
  change U (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (U ξ) x k
  rw [hU k, hM, hMU]
  change g x * ξ x (k - 1) = g x * U ξ x k
  rw [hUξ k]

theorem representation_commutes_multiplier (θ : ℝ) (a : C(Circle, ℂ))
    (g : Lp ℂ ∞ circleMeasure) :
    Commute (representation θ a) (L2Multiplication.multiplier (E := Fiber) g) := by
  show representation θ a * L2Multiplication.multiplier g =
    L2Multiplication.multiplier g * representation θ a
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ a (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ,
    L2Multiplication.multiplier_coe g (representation θ a ξ),
    representation_coordinates_ae θ a ξ] with x ha hM hMa haξ
  intro k
  change representation θ a (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (representation θ a ξ) x k
  rw [ha k, hM, hMa]
  change a (action θ k x) * (g x * ξ x k) =
    g x * representation θ a ξ x k
  rw [haξ k]
  ring

theorem multiplier_mem_commutant (θ : ℝ) (g : Lp ℂ ∞ circleMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (algebra θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact ⟨(U_commutes_multiplier g).eq,
      (commute_star_left_of_mem_unitary U_mem_unitary (U_commutes_multiplier g)).eq⟩
  · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
    subst A
    have hcomm := representation_commutes_multiplier θ character g
    exact ⟨hcomm.eq,
      (commute_star_left_of_mem_unitary (V_mem_unitary θ) hcomm).eq⟩

theorem algebra_commutes_multiplier (θ : ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) (g : Lp ℂ ∞ circleMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) := by
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (multiplier_mem_commutant θ g)) T hT

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFieldRepresentation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem exists_unique_field {θ : ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Circle → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => G x (ξ x)) →
          F =ᵐ[circleMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (algebra_commutes_multiplier θ hT)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationMeasurable
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem vonNeumannAlgebra_mem_of_strong_tendsto
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) {l : Filter ι} [l.NeBot]
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hA : ∀ i, A i ∈ M) (hAB : ∀ v, Tendsto (fun i => A i v) l (𝓝 (B v))) :
    B ∈ M := by
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  apply ContinuousLinearMap.ext
  intro v
  have ht := T.continuous.continuousAt.tendsto.comp (hAB v)
  have ha := hAB (T v)
  have heq : (fun i => T (A i v)) = (fun i => A i (T v)) := by
    funext i
    exact (DFunLike.congr_fun ((VonNeumannAlgebra.mem_commutant_iff.mp hT) (A i) (hA i)) v).symm
  change T (B v) = B (T v)
  change Tendsto (fun i => T (A i v)) l (𝓝 (T (B v))) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht ha

namespace Rotation

theorem measurableRepresentation_continuous
    (θ : ℝ) (a : C(Circle, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖a x‖ ≤ C) :
    measurableRepresentation θ a C hC a.continuous.measurable hb = representation θ a := by
  apply WeightedShift.fieldDiagonal_congr
  exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

theorem measurableRepresentation_tendsto_apply
    (θ : ℝ) (g : ℕ → Circle → ℂ) (h : Circle → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (hgb : ∀ n x, ‖g n x‖ ≤ C) (hhb : ∀ x, ‖h x‖ ≤ D)
    (hgh : ∀ᵐ x ∂circleMeasure, Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (v : Hilbert) :
    Tendsto (fun n => measurableRepresentation θ (g n) C hC (hg n) (hgb n) v)
      atTop (𝓝 (measurableRepresentation θ h D hD hh hhb v)) := by
  apply WeightedShift.fieldDiagonal_tendsto_apply
  have hall : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      Tendsto (fun n => g n (action θ k x)) atTop (𝓝 (h (action θ k x))) := by
    rw [ae_all_iff]
    intro k
    exact (action_measurePreserving θ k).quasiMeasurePreserving.ae
      (p := fun x => Tendsto (fun n => g n x) atTop (𝓝 (h x))) hgh
  exact hall

theorem measurableRepresentation_mem_algebra
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    measurableRepresentation θ g C hC hg hb ∈ algebra θ := by
  obtain ⟨a, ha, hae⟩ := Lusin.exists_bounded_continuous_eventuallyEq circleMeasure hg hC hb
  have hconv : ∀ᵐ x ∂circleMeasure, Tendsto (fun n => a n x) atTop (𝓝 (g x)) := by
    filter_upwards [hae] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun _ hn => hn.symm)
  apply vonNeumannAlgebra_mem_of_strong_tendsto (algebra θ) (l := (atTop : Filter ℕ))
    (A := fun n => measurableRepresentation θ (a n) (2 * C) (by positivity)
      (a n).continuous.measurable (ha n))
  · intro n
    rw [measurableRepresentation_continuous]
    exact representation_mem_algebra θ (a n)
  · intro v
    exact measurableRepresentation_tendsto_apply θ (fun n => a n) g (2 * C) C
      (by positivity) hC (fun n => (a n).continuous.measurable) hg ha hb hconv v

end Rotation
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTrace
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem algebra_commutes_shiftedPullback_int (θ : ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
      (action θ r) (action_measurePreserving θ r)) := by
  let S := (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
  let S₁ := (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap
  let J := DirectIntegral.shiftedPullback S (action θ r) (action_measurePreserving θ r)
  have hUJ : Commute U J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance U (fun _ => S₁)
      S (action θ r) (action_measurePreserving θ r) U_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp [S, S₁]
    rw [← WeightedShift.shift_add, ← WeightedShift.shift_add, add_comm (1 : ℤ) r]
  have hVJ : Commute (V θ) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance (V θ)
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      S (action θ r) (action_measurePreserving θ r) (representation_ae θ character)
    apply Filter.Eventually.of_forall
    intro x
    ext v k
    change character (action θ k x) * v (k - r) =
      character (action θ (k - r) (action θ r x)) * v (k - r)
    simp only [action_add, sub_add_cancel]
  have hJ : J ∈ (algebra θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨hUJ.eq, (commute_star_left_of_mem_unitary U_mem_unitary hUJ).eq⟩
    · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨hVJ.eq, (commute_star_left_of_mem_unitary (V_mem_unitary θ) hVJ).eq⟩
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem vacuum_faithfulTracial (θ : ℝ) :
    IsFaithfulTracialVector (algebra θ) vacuum := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hb (k : ℤ) : b k = lp.single 2 k 1 := by
    rw [← HilbertBasis.repr_symm_single]
    rfl
  have hshift (r k : ℤ) :
      (WeightedShift.shift r).toLinearIsometry (b k) = b (k + r) := by
    rw [hb, hb]
    ext j
    change (lp.single 2 k (1 : ℂ) : Fiber) (j-r) = (lp.single 2 (k+r) (1 : ℂ) : Fiber) j
    simp only [lp.single_apply]
    simp only [Pi.single_apply]
    by_cases h : j - r = k
    · have h' : j = k + r := by omega
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : j ≠ k + r := by omega
      rw [ite_eq_right h, ite_eq_right h']
  have h := FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    b (algebra θ) (action θ) (action_measurePreserving θ)
    (fun r => (WeightedShift.shift r).toLinearIsometry) hshift
    (fun T hT r => algebra_commutes_shiftedPullback_int θ r T hT) ?_
  · simpa only [hb, vacuum] using h
  · intro T hT
    obtain ⟨A, hbound, hm, hrep, _⟩ := exists_unique_field hT
    exact ⟨A, hrep, fun r => (hm (b r)).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace Invariant233.Rotation

theorem exponentialTransfer_injective (θ : ℝ) (b : Circle → ℝ) :
    Function.Injective (exponentialTransfer θ b) := by
  apply WeightedShift.fieldUnboundedMultiplier_injective
  exact Eventually.of_forall fun x k => Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)

theorem exponentialTransfer_selfAdjoint (θ : ℝ) {b : Circle → ℝ}
    (hb : Measurable b) : IsSelfAdjoint (exponentialTransfer θ b) := by
  apply WeightedShift.isSelfAdjoint_fieldUnboundedMultiplier_real
  intro k
  exact (exponentialTransfer_coefficient_measurable θ hb k).aestronglyMeasurable

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTransferTrace
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology NNReal

namespace Invariant233.Rotation

open WeightedShift.SpectralCutoff

theorem boundedOperator_orbit_mem_algebra
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => g (action θ k x)) circleMeasure) :
    boundedOperator (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm ∈ algebra θ := by
  have heq : boundedOperator (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm =
      measurableRepresentation θ g C hC hg hb := by
    apply operator_ext_of_coordinates
    intro ξ
    filter_upwards [boundedOperator_ae (fun x k => g (action θ k x)) C hC
      (fun x k => hb (action θ k x)) hm ξ,
      measurableRepresentation_coordinates_ae θ g C hC hg hb ξ] with x hx hy
    intro k
    exact (hx k).trans (hy k).symm
  rw [heq]
  exact measurableRepresentation_mem_algebra θ g C hC hg hb

theorem exponentialTransfer_cutoff_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    projection (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => symbol n (Real.exp (b x)))
  · exact ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_symbol_le n _

theorem exponentialTransfer_cutoffProduct_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    productOperator (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => productSymbol n (Real.exp (b x)))
  · exact (Complex.measurable_ofReal.comp hb.exp).mul
      ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_productSymbol_le n _

theorem exponentialTransfer_inverseCutoffProduct_mem_algebra
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b) (n : ℕ) :
    inverseOperator (fun x k => Real.exp (b (action θ k x)))
      (exponentialTransfer_coefficient_measurable θ hb) n ∈ algebra θ := by
  apply boundedOperator_orbit_mem_algebra θ (fun x => inverseSymbol n (Real.exp (b x)))
  · exact (Complex.measurable_ofReal.comp hb.exp.inv).mul
      ((measurable_const.indicator measurableSet_Icc).comp hb.exp)
  · exact fun x => norm_inverseSymbol_le n _

theorem exponentialTransfer_transported_vectorTrace
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (p : Submodule ℂ Hilbert) [CompleteSpace p]
    (hp : p.starProjection ∈ algebra θ) :
    vectorTrace vacuum
      (InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p).starProjection =
      vectorTrace vacuum p.starProjection := by
  let h : Circle → ℤ → ℝ := fun x k => Real.exp (b (action θ k x))
  let hm : ∀ k, Measurable (fun x => h x k) := exponentialTransfer_coefficient_measurable θ hb
  let E : ℕ → Submodule ℂ Hilbert := fun n => cutoffSpace (μ := circleMeasure) h hm n
  let (n : ℕ) : CompleteSpace ↥(E n) := by
    exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hpos : ∀ᵐ x ∂circleMeasure, ∀ k, 0 < h x k :=
    Eventually.of_forall fun _ _ => Real.exp_pos _
  have hEM (n : ℕ) : (E n).starProjection ∈ algebra θ := by
    rw [show (E n).starProjection = projection h hm n from cutoffSpace_starProjection h hm n]
    exact exponentialTransfer_cutoff_mem_algebra θ hb n
  have hED (n : ℕ) : E n ≤ (exponentialTransfer θ b).domain :=
    (cutoffSpace_le_domains h hm n).1
  have hiED (n : ℕ) : E n ≤ (exponentialTransfer θ b).inverse.domain :=
    (cutoffSpace_le_domains h hm n).2
  have hξ := vacuum_faithfulTracial θ
  have hsym : (exponentialTransfer θ b).IsFormalAdjoint (exponentialTransfer θ b) := by
    have hs := LinearPMap.adjoint_isFormalAdjoint (exponentialTransfer_selfAdjoint θ hb).dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp (exponentialTransfer_selfAdjoint θ hb)] at hs
    exact hs
  have hker : (exponentialTransfer θ b).toFun.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (exponentialTransfer_injective θ b)
  have hr (n : ℕ) (x : E n) :
      (x : Hilbert) ∈ (projection (μ := circleMeasure) h hm n).range := by
    have hx : (x : Hilbert) ∈ cutoffSpace (μ := circleMeasure) h hm n := x.property
    rw [cutoffSpace_eq_range] at hx
    exact hx
  have hF (n : ℕ) (x : E n) :
      exponentialTransfer θ b ⟨x, hED n x.property⟩ =
        productOperator (μ := circleMeasure) h hm n x := by
    exact multiplier_on_range (μ := circleMeasure) h hm n ⟨x, hr n x⟩
  have hG (n : ℕ) (x : E n) :
      (exponentialTransfer θ b).inverse ⟨x, hiED n x.property⟩ =
        inverseOperator (μ := circleMeasure) h hm n x := by
    exact inverse_multiplier_on_range (μ := circleMeasure) h hm hpos n ⟨x, hr n x⟩
  have hLower (n : ℕ) (x : E n) :
      ‖x‖ ≤ (n + 1 : ℝ≥0) * ‖productOperator (μ := circleMeasure) h hm n x‖ := by
    have hx := (multiplier_range_bounds (μ := circleMeasure) h hm n ⟨x, hr n x⟩).2
    rw [multiplier_on_range] at hx
    exact hx
  have hInvLower (n : ℕ) (x : E n) :
      ‖x‖ ≤ (n + 1 : ℝ≥0) * ‖inverseOperator (μ := circleMeasure) h hm n x‖ := by
    have hx := (inverse_multiplier_range_bounds (μ := circleMeasure) h hm hpos n ⟨x, hr n x⟩).2
    rw [inverse_multiplier_on_range h hm hpos] at hx
    exact hx
  exact AffiliatedTraceCutoffs.vectorTrace_transported_eq_of_cutoffs
    (algebra θ) vacuum hξ (exponentialTransfer θ b) hsym hker p hp E hEM
    (cutoffSpace_tendsto h hm hpos vacuum) hED hiED
    (productOperator h hm) (inverseOperator h hm)
    (exponentialTransfer_cutoffProduct_mem_algebra θ hb)
    (exponentialTransfer_inverseCutoffProduct_mem_algebra θ hb)
    hF hG (fun n => n + 1) (fun n => n + 1) hLower hInvLower

theorem exponentialTransfer_projection_trace
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p) :
    vectorTrace vacuum
      (InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p.range).starProjection =
      vectorTrace vacuum p := by
  let : CompleteSpace p.range := (ContinuousLinearMap.IsIdempotentElem.isClosed_range hpP.isIdempotentElem).completeSpace_coe
  obtain ⟨hi, he⟩ := isStarProjection_iff_eq_starProjection_range.mp hpP
  have hpm : p.range.starProjection ∈ algebra θ := by
    rw [← he]
    exact hp
  simpa only [← he] using exponentialTransfer_transported_vectorTrace θ hb p.range hpm

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldResolvent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldUnboundedMultiplier_positiveFieldResolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ) (ξ : FieldHilbert μ) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨positiveFieldResolvent h hpos hm ξ,
        positiveFieldResolvent_mem_domain h hpos hm ξ⟩ =
      ξ - positiveFieldResolvent h hpos hm ξ := by
  apply fieldUnboundedMultiplier_eq_of_ae
  filter_upwards [positiveFieldResolvent_ae h hpos hm ξ,
    Lp.coeFn_sub ξ (positiveFieldResolvent h hpos hm ξ)] with x hR hsub
  intro k
  rw [hsub]
  change ξ x k - positiveFieldResolvent h hpos hm ξ x k = _
  rw [hR]
  exact resolvent_scalar_identity (h x k) (hpos x k) (ξ x k)

theorem fieldUnboundedMultiplier_commutes_of_commute_resolvent
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (A : FieldHilbert μ →L[ℂ] FieldHilbert μ)
    (hA : Commute A (positiveFieldResolvent h hpos hm))
    (ξ : (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) :
    fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))
      ⟨A ξ.val,
        fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hA ξ⟩ =
      A (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ) := by
  let η := ξ.val + fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ)) ξ
  have hRη : positiveFieldResolvent h hpos hm η = ξ.val :=
    positiveFieldResolvent_apply_add_multiplier h hpos hm ξ
  have hRA : positiveFieldResolvent h hpos hm (A η) = A ξ.val := by
    have heq := congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ => B η) hA.eq
    change A (positiveFieldResolvent h hpos hm η) =
      positiveFieldResolvent h hpos hm (A η) at heq
    exact heq.symm.trans (congrArg A hRη)
  have hξ : (⟨A ξ.val,
      fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hA ξ⟩ :
        (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))).domain) =
      ⟨positiveFieldResolvent h hpos hm (A η),
        positiveFieldResolvent_mem_domain h hpos hm (A η)⟩ :=
    Subtype.ext hRA.symm
  rw [hξ, fieldUnboundedMultiplier_positiveFieldResolvent, hRA]
  dsimp [η]
  rw [map_add, add_sub_cancel_left]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_FieldResolventTransport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.WeightedShift

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem closedImageOn_projection_mem_of_resolvent_mem
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (M : VonNeumannAlgebra (FieldHilbert μ))
    (hR : positiveFieldResolvent h hpos hm ∈ M)
    (p : FieldHilbert μ →L[ℂ] FieldHilbert μ) (hp : p ∈ M) :
    (AffiliatedTransport.closedImageOn
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro A hA
  rw [Submodule.range_starProjection]
  have hAR : Commute A (positiveFieldResolvent h hpos hm) :=
    ((VonNeumannAlgebra.mem_commutant_iff.mp hA) _ hR).symm
  apply AffiliatedTransport.closedImageOn_invariant_of_commuting
    (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range A
    (fieldUnboundedMultiplier_domain_invariant_of_commute_resolvent h hpos hm A hAR)
    (fieldUnboundedMultiplier_commutes_of_commute_resolvent h hpos hm A hAR)
  rintro y ⟨z, rfl⟩
  refine ⟨A z, ?_⟩
  exact congrArg (fun B : FieldHilbert μ →L[ℂ] FieldHilbert μ => B z)
    ((VonNeumannAlgebra.mem_commutant_iff.mp hA) p hp)

theorem transported_projection_mem_of_resolvent_mem
    (h : X → ℤ → ℝ) (hpos : ∀ x k, 0 ≤ h x k)
    (hm : ∀ k, AEStronglyMeasurable (fun x => h x k) μ)
    (M : VonNeumannAlgebra (FieldHilbert μ))
    (hR : positiveFieldResolvent h hpos hm ∈ M)
    (p : FieldHilbert μ →L[ℂ] FieldHilbert μ) (hp : p ∈ M) :
    (InvariantRotation.AffiliatedTransport.transported
      (fieldUnboundedMultiplier μ (fun x k => (h x k : ℂ))) p.range).starProjection ∈ M :=
  closedImageOn_projection_mem_of_resolvent_mem h hpos hm M hR p hp

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationResolvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem positiveFieldResolvent_mem_algebra
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h) :
    WeightedShift.positiveFieldResolvent (fun x k => h (action θ k x))
      (fun x k => hpos (action θ k x)) (measurable_positive_orbit θ h hm) ∈ algebra θ := by
  let g : Circle → ℂ := fun x => (((1 + h x)⁻¹ : ℝ) : ℂ)
  have hg : Measurable g := by
    exact ((measurable_const.add hm).inv).complex_ofReal
  have hb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    have ht : 0 < 1 + h x := by linarith [hpos x]
    change ‖(((1 + h x)⁻¹ : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (inv_le_one₀ ht).mpr (by linarith [hpos x])
  have hR : WeightedShift.positiveFieldResolvent (fun x k => h (action θ k x))
      (fun x k => hpos (action θ k x)) (measurable_positive_orbit θ h hm) =
      measurableRepresentation θ g 1 (by norm_num) hg hb := by
    apply WeightedShift.fieldDiagonal_congr
    exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)
  rw [hR]
  exact measurableRepresentation_mem_algebra θ g 1 (by norm_num) hg hb

theorem positive_orbit_transported_projection_mem
    (θ : ℝ) (h : Circle → ℝ) (hpos : ∀ x, 0 ≤ h x) (hm : Measurable h)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) :
    (InvariantRotation.AffiliatedTransport.transported
      (WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => (h (action θ k x) : ℂ))) p.range).starProjection ∈ algebra θ :=
  WeightedShift.transported_projection_mem_of_resolvent_mem
    (fun x k => h (action θ k x)) (fun x k => hpos (action θ k x))
    (measurable_positive_orbit θ h hm) (algebra θ)
    (positiveFieldResolvent_mem_algebra θ h hpos hm) p hp

theorem exponential_orbit_transported_projection_mem
    (θ : ℝ) (b : Circle → ℝ) (hb : Measurable b)
    (p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) :
    (InvariantRotation.AffiliatedTransport.transported
      (WeightedShift.fieldUnboundedMultiplier circleMeasure
        (fun x k => (Real.exp (b (action θ k x)) : ℂ))) p.range).starProjection ∈ algebra θ :=
  positive_orbit_transported_projection_mem θ (fun x => Real.exp (b x))
    (fun x => (Real.exp_pos (b x)).le) hb.exp p hp

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationProjectionTransport
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233

namespace Rotation

theorem exponentialTransfer_projection_transport_oai
    (θ : ℝ) {b : Circle → ℝ} (hb : Measurable b)
    (A B p : Hilbert →L[ℂ] Hilbert) (hp : p ∈ algebra θ) (hpP : IsStarProjection p)
    (hAp : (1 - p) * A * p = 0)
    (hD : ∀ ξ : (exponentialTransfer θ b).domain,
      A ξ.val ∈ (exponentialTransfer θ b).domain)
    (hI : ∀ ξ : (exponentialTransfer θ b).domain,
      exponentialTransfer θ b ⟨A ξ.val, hD ξ⟩ = B (exponentialTransfer θ b ξ)) :
    let P := (InvariantRotation.AffiliatedTransport.transported
      (exponentialTransfer θ b) p.range).starProjection
    P ∈ algebra θ ∧ IsStarProjection P ∧ (1 - P) * B * P = 0 ∧
      vectorTrace vacuum P = vectorTrace vacuum p := by
  dsimp only
  refine ⟨exponential_orbit_transported_projection_mem θ b hb p hp,
    isStarProjection_starProjection, ?_, exponentialTransfer_projection_trace θ hb p hp hpP⟩
  have hAp' : p * A * p = A * p := by
    rw [sub_mul, one_mul, sub_mul] at hAp
    exact (sub_eq_zero.mp hAp).symm
  have hrange : ∀ y ∈ p.range, A y ∈ p.range := by
    rintro y ⟨z, rfl⟩
    refine ⟨A (p z), ?_⟩
    exact congrArg (fun C : Hilbert →L[ℂ] Hilbert => C z) hAp'
  have hinv := InvariantRotation.AffiliatedTransport.transported_invariant
    (exponentialTransfer θ b) p.range A B hrange
    (fun x hx => hD ⟨x, hx⟩) hI
  let S := InvariantRotation.AffiliatedTransport.transported (exponentialTransfer θ b) p.range
  have hr : S.starProjection.range ∈ Module.End.invtSubmodule B := by
    rw [Submodule.range_starProjection]
    exact hinv
  have heq := (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    (isStarProjection_starProjection (U := S)).isIdempotentElem).mp hr
  change S.starProjection * B * S.starProjection = B * S.starProjection at heq
  change (1 - S.starProjection) * B * S.starProjection = 0
  rw [sub_mul, one_mul, sub_mul, heq, sub_self]

end Rotation
end Invariant233

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.Rotation.exponentialTransfer_projection_transport_oai := @OAI.Invariant233.Rotation.exponentialTransfer_projection_transport_oai
