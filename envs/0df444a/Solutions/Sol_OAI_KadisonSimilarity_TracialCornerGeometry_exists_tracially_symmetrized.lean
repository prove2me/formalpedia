-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:48:45.767873+00:00
-- url     : https://prove2.me/submissions/3ce78ef6-c545-441f-8b95-bedc2638ff5b

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Pairing
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Option
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A028
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorCompactness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-operator compactness of a norm ball, obtained from compact scalar
matrix-coefficient discs and the Hilbert-space representation of bounded forms. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open ContinuousLinearMapWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem norm_operatorOfForm_le (f : H → H → ℂ) (hf : IsOperatorForm f) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖) :
    ‖operatorOfForm f hf R hb‖ ≤ R := by
  apply norm_le_of_matrix_coefficients _ hR
  intro x y
  rw [← norm_inner_symm, operatorOfForm_inner]
  convert hb x y using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompleteSpace H] in
private theorem isClosed_operatorForms : IsClosed {f : H → H → ℂ | IsOperatorForm f} := by
  have hc (x y : H) : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  unfold IsOperatorForm
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc (x + y) z) ((hc x z).add (hc y z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc (c • x) y) (continuous_const.mul (hc x y))
  · refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z => ?_
    exact isClosed_eq (hc x (y + z)) ((hc x y).add (hc x z))
  · refine isClosed_iInter fun c => isClosed_iInter fun x => isClosed_iInter fun y => ?_
    exact isClosed_eq (hc x (c • y)) (continuous_const.mul (hc x y))

omit [CompleteSpace H] in
private theorem isCompact_boundedOperatorForms (R : ℝ) :
    IsCompact (boundedOperatorForms (H := H) R) := by
  have hd : IsCompact {f : H → H → ℂ | ∀ x y, f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} :=
    isCompact_pi_infinite fun x => isCompact_pi_infinite fun y => isCompact_closedBall _ _
  have he : boundedOperatorForms (H := H) R =
      {f | IsOperatorForm f} ∩ {f : H → H → ℂ | ∀ x y,
        f x y ∈ Metric.closedBall 0 (R * ‖x‖ * ‖y‖)} := by
    ext f
    simp [boundedOperatorForms, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact hd.inter_left isClosed_operatorForms

private theorem continuous_boundedFormOperator (R : ℝ) :
    Continuous (boundedFormOperator (H := H) R) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  have he : (fun f : boundedOperatorForms (H := H) R =>
      inner ℂ y (boundedFormOperator R f x)) =
      fun f => star (f.val x y) := by
    funext f
    change inner ℂ y (operatorOfForm f.val f.property.1 R f.property.2 x) = _
    rw [← inner_conj_symm, operatorOfForm_inner]
    rfl
  rw [he]
  have hc : Continuous (fun f : H → H → ℂ => f x y) :=
    (continuous_apply y).comp (continuous_apply x)
  exact (hc.comp continuous_subtype_val).star

/-- The closed norm ball in bounded operators on a Hilbert space is compact
in the weak-operator topology. -/
theorem isCompact_weakOperator_ball (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
  let : CompactSpace (boundedOperatorForms (H := H) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedOperatorForms R)
  have himage : Set.range (boundedFormOperator (H := H) R) =
      {T : H →WOT[ℂ] H | ‖toCLM T‖ ≤ R} := by
    ext T
    constructor
    · rintro ⟨f, rfl⟩
      exact norm_operatorOfForm_le f.val f.property.1 R hR f.property.2
    · intro hT
      let f : H → H → ℂ := fun x y => inner ℂ (T x) y
      have hf : IsOperatorForm f := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x y z; simp [f, inner_add_left]
        · intro c x y; simp [f, inner_smul_left, mul_comm]
        · intro x y z; simp [f, inner_add_right]
        · intro c x y; simp [f, inner_smul_right]
      have hb : ∀ x y, ‖f x y‖ ≤ R * ‖x‖ * ‖y‖ := by
        intro x y
        calc
          ‖f x y‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
          _ ≤ (‖toCLM T‖ * ‖x‖) * ‖y‖ :=
            mul_le_mul_of_nonneg_right ((toCLM T).le_opNorm x) (norm_nonneg y)
          _ ≤ R * ‖x‖ * ‖y‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hT (norm_nonneg x)) (norm_nonneg y)
      refine ⟨⟨f, hf, hb⟩, ?_⟩
      apply ContinuousLinearMapWOT.ext_inner
      intro x y
      change inner ℂ y (operatorOfForm f hf R hb x) = inner ℂ y (T x)
      rw [← inner_conj_symm, operatorOfForm_inner]
      exact inner_conj_symm _ _
  rw [← himage]
  exact isCompact_range (continuous_boundedFormOperator R)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_FiniteSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite unitary averaging and weak-operator cluster points. These are the
analytic and algebraic symmetrization steps, before identifying the matrix
unitaries of the free-product model. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology
open Filter ContinuousLinearMapWOT

variable {Γ V H : Type*} [Fintype Γ] [Nonempty Γ]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [Group Γ]

variable [CompleteSpace H]

/-- Every bounded sequence of operators has a weak-operator cluster point,
without a separability assumption on the Hilbert space. -/
theorem exists_weakOperator_cluster (T : ℕ → H →L[ℂ] H) {R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ n, ‖T n‖ ≤ R) :
    ∃ S : H →L[ℂ] H, ‖S‖ ≤ R ∧ MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)) := by
  have hev : ∀ᶠ n : ℕ in atTop, ofCLM (T n) ∈
      {B : H →WOT[ℂ] H | ‖toCLM B‖ ≤ R} := Eventually.of_forall hbound
  obtain ⟨S, hS, hcluster⟩ :=
    (isCompact_weakOperator_ball (H := H) R hR).exists_mapClusterPt_of_frequently hev.frequently
  exact ⟨toCLM S, hS, hcluster⟩

/-- Eventual commutator bounds pass to weak cluster points. -/
theorem norm_commutator_le_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S A : H →L[ℂ] H)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    {c : ℝ} (hc : 0 ≤ c) (hbound : ∀ᶠ n in atTop, ‖commutator (T n) A‖ ≤ c) :
    ‖commutator S A‖ ≤ c := by
  have hclosed : IsClosed {B : H →WOT[ℂ] H | ‖commutator (toCLM B) A‖ ≤ c} :=
    (isCompact_weakOperator_ball (H := H) c hc).isClosed.preimage
      ((continuous_id.mul_const (ofCLM A)).sub (continuous_id.const_mul (ofCLM A)))
  exact hclosed.mem_of_mapClusterPt hcluster hbound

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_WeakOperatorIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak operator integrals built from scalar integrals. In particular this
permits averaging a strongly continuous unitary action without assuming
continuity in the operator norm. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem norm_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ g, ‖A g‖ ≤ R) :
    ‖weakOperatorIntegral μ A hA R hbound‖ ≤ R :=
  norm_operatorOfForm_le _ _ R hR _

/-- Left and right multiplication may be passed through the weak integral. -/
theorem weakOperatorIntegral_sandwich_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B C : H →L[ℂ] H) (x y : H) :
    inner ℂ ((B * weakOperatorIntegral μ A hA R hbound * C) x) y =
      ∫ g, inner ℂ ((B * A g * C) x) y ∂μ := by
  change inner ℂ (B (weakOperatorIntegral μ A hA R hbound (C x))) y = _
  rw [← adjoint_inner_right, weakOperatorIntegral_inner]
  apply integral_congr_ae
  filter_upwards with g
  exact adjoint_inner_right B (A g (C x)) y

/-- A commutator with a fixed operator may be passed through the weak integral. -/
theorem weakOperatorIntegral_commutator_inner (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) (x y : H) :
    inner ℂ (commutator (weakOperatorIntegral μ A hA R hbound) B x) y =
      ∫ g, inner ℂ (commutator (A g) B x) y ∂μ := by
  simp only [commutator, sub_apply, ContinuousLinearMap.mul_def, comp_apply, inner_sub_left]
  rw [weakOperatorIntegral_inner, ← adjoint_inner_right, weakOperatorIntegral_inner,
    ← integral_sub (hA (B x) y) (hA x (B.adjoint y))]
  apply integral_congr_ae
  filter_upwards with g
  rw [adjoint_inner_right]

/-- Uniform commutator bounds are preserved by weak integration. -/
theorem norm_commutator_weakOperatorIntegral_le (A : X → H →L[ℂ] H)
    (hA : WeaklyIntegrable μ A) (R : ℝ) (hbound : ∀ g, ‖A g‖ ≤ R)
    (B : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ g, ‖commutator (A g) B‖ ≤ c) :
    ‖commutator (weakOperatorIntegral μ A hA R hbound) B‖ ≤ c := by
  apply norm_le_of_matrix_coefficients _ hc
  intro x y
  rw [← norm_inner_symm, weakOperatorIntegral_commutator_inner]
  have hb : ∀ᵐ g ∂μ, ‖inner ℂ (commutator (A g) B x) y‖ ≤ c * ‖x‖ * ‖y‖ :=
    Filter.Eventually.of_forall fun g => calc
      _ ≤ ‖commutator (A g) B x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (‖commutator (A g) B‖ * ‖x‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right ((commutator (A g) B).le_opNorm x) (norm_nonneg y)
      _ ≤ c * ‖x‖ * ‖y‖ := by gcongr; exact hcomm g
  have hi := norm_integral_le_of_norm_le_const hb
  simp only [probReal_univ, mul_one] at hi
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ring

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_HaarSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Haar averaging is contractive in operator norm. -/
theorem norm_haarTwirl_le (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) :
    ‖haarTwirl μ U hU T hI‖ ≤ ‖T‖ :=
  norm_weakOperatorIntegral_le μ _ _ _ (norm_nonneg _) _

/-- Left invariance of Haar measure gives invariance of the operator average. -/
theorem haarTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    U g * haarTwirl μ U hU T hI * U g⁻¹ = haarTwirl μ U hU T hI := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [haarTwirl, weakOperatorIntegral_sandwich_inner, weakOperatorIntegral_inner]
  calc
    _ = ∫ h, inner ℂ (unitaryConjugate U T (g * h) x) y ∂μ := by
      apply integral_congr_ae
      filter_upwards with h
      congr 2
      simp only [unitaryConjugate, mul_inv_rev, map_mul, mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => inner ℂ (unitaryConjugate U T h x) y) g

/-- Thus the Haar average commutes with the whole compact group. -/
theorem haarTwirl_commute (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    commutator (haarTwirl μ U hU T hI) (U g) = 0 := by
  have hc := congrArg (fun B : H →L[ℂ] H => B * U g) (haarTwirl_conjugate μ U hU T hI g)
  have hi : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc, hi, mul_one] at hc
  exact sub_eq_zero.mpr hc.symm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Every common commutator estimate for the orbit survives Haar averaging. -/
theorem norm_commutator_haarTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H)
    (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (B : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcomm : ∀ g, ‖commutator (unitaryConjugate U T g) B‖ ≤ c) :
    ‖commutator (haarTwirl μ U hU T hI) B‖ ≤ c :=
  norm_commutator_weakOperatorIntegral_le μ _ _ _ _ B hc hcomm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- On a subspace fixed pointwise by the group, compression is exactly
preserved by averaging. -/
theorem haarTwirl_compression (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T))
    (J : K →L[ℂ] H) (hfix : ∀ g, (U g).comp J = J) :
    J.adjoint.comp ((haarTwirl μ U hU T hI).comp J) = J.adjoint.comp (T.comp J) := by
  have happly (g : Γ) (x : K) : U g (J x) = J x :=
    congrArg (fun B : K →L[ℂ] H => B x) (hfix g)
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (J.adjoint (haarTwirl μ U hU T hI (J x))) y =
    inner ℂ (J.adjoint (T (J x))) y
  rw [adjoint_inner_left, adjoint_inner_left, haarTwirl, weakOperatorIntegral_inner]
  apply integral_eq_const
  filter_upwards with g
  change inner ℂ (U g (T (U g⁻¹ (J x)))) (J y) = _
  rw [happly, ← adjoint_inner_right, hstar, happly]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SimultaneousSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous symmetry for an increasing family of compact groups, using
actual Haar averages and a weak-operator cluster point. -/

noncomputable section
namespace KadisonSimilarity

open Filter ContinuousLinearMapWOT MeasureTheory
open scoped Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A fixed rectangular compression is weak-operator continuous, so an exact
compression identity survives a weak-operator cluster point. -/
theorem compression_eq_of_weakOperator_cluster (T : ℕ → H →L[ℂ] H)
    (S : H →L[ℂ] H) (A : K →L[ℂ] H) (B : H →L[ℂ] K) (C : K →L[ℂ] K)
    (hcluster : MapClusterPt (ofCLM S) atTop (fun n => ofCLM (T n)))
    (heq : ∀ᶠ n in atTop, B.comp ((T n).comp A) = C) : B.comp (S.comp A) = C := by
  have hcont : Continuous (fun R : H →WOT[ℂ] H =>
      (ofCLM B).comp (R.comp (ofCLM A))) :=
    (continuous_postcomp (ofCLM B)).comp (continuous_precomp (ofCLM A))
  have hclosed : IsClosed {R : H →WOT[ℂ] H |
      (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} :=
    isClosed_eq hcont continuous_const
  have heq' : ∀ᶠ n in atTop, ofCLM (T n) ∈
      {R : H →WOT[ℂ] H | (ofCLM B).comp (R.comp (ofCLM A)) = ofCLM C} := by
    filter_upwards [heq] with n hn
    exact congrArg ofCLM hn
  have he := hclosed.mem_of_mapClusterPt hcluster heq'
  exact congrArg toCLM he

variable {Γ : ℕ → Type*} [∀ n, Group (Γ n)] [∀ n, MeasurableSpace (Γ n)]
  [∀ n, MeasurableMul (Γ n)]
  (μ : ∀ n, Measure (Γ n)) [∀ n, IsProbabilityMeasure (μ n)]
  [∀ n, (μ n).IsMulLeftInvariant]

/-- A single cluster point has every finite-stage symmetry, all common
commutator bounds, and the original compression to the fixed subspace.
The stage maps are ordinary group-element inclusions; no limiting invariant
operator is assumed among the data. -/
theorem exists_simultaneously_symmetrized
    (U : ∀ n, Γ n →* (H →L[ℂ] H)) (hU : ∀ n g, ‖U n g‖ ≤ 1)
    (hstar : ∀ n g, (U n g).adjoint = U n g⁻¹)
    (embedding : ∀ n m, n ≤ m → Γ n → Γ m)
    (hcompat : ∀ n m h g, U m (embedding n m h g) = U n g)
    (T : H →L[ℂ] H)
    (hI : ∀ n, WeaklyIntegrable (μ n) (unitaryConjugate (U n) T))
    (J : K →L[ℂ] H) (hfix : ∀ n g, (U n g).comp J = J)
    {ι : Type*} (test : ι → H →L[ℂ] H) (bound : ι → ℝ) (hbound : ∀ i, 0 ≤ bound i)
    (htest : ∀ n g i, ‖commutator (unitaryConjugate (U n) T g) (test i)‖ ≤ bound i) :
    ∃ S : H →L[ℂ] H,
      ‖S‖ ≤ ‖T‖ ∧
      (∀ n g, commutator S (U n g) = 0) ∧
      (∀ i, ‖commutator S (test i)‖ ≤ bound i) ∧
      J.adjoint.comp (S.comp J) = J.adjoint.comp (T.comp J) := by
  let averages : ℕ → H →L[ℂ] H := fun n => haarTwirl (μ n) (U n) (hU n) T (hI n)
  obtain ⟨S, hS, hcluster⟩ := exists_weakOperator_cluster averages (norm_nonneg T)
    (fun n => norm_haarTwirl_le (μ n) (U n) (hU n) T (hI n))
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro n g
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    apply norm_commutator_le_of_weakOperator_cluster averages S (U n g) hcluster (le_refl 0)
    filter_upwards [eventually_ge_atTop n] with m hm
    have he := haarTwirl_commute (μ m) (U m) (hU m) T (hI m) (embedding n m hm g)
    rw [hcompat] at he
    simp only [averages, he, norm_zero, le_refl]
  · intro i
    apply norm_commutator_le_of_weakOperator_cluster averages S (test i) hcluster (hbound i)
    exact Eventually.of_forall fun n =>
      norm_commutator_haarTwirl_le (μ n) (U n) (hU n) T (hI n) (test i)
        (hbound i) (fun g => htest n g i)
  · apply compression_eq_of_weakOperator_cluster averages S J J.adjoint
      (J.adjoint.comp (T.comp J)) hcluster
    exact Eventually.of_forall fun n =>
      haarTwirl_compression (μ n) (U n) (hU n) (hstar n) T (hI n) J (hfix n)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_CompactHaarIntegrability
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of a unitary action gives every weak Haar integral
used in symmetrization. No continuity in operator norm is required. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
/-- Moving the left unitary to the second inner-product slot makes matrix
coefficients of its conjugation action continuous in the strong topology. -/
theorem continuous_unitaryConjugate_coefficient
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) (x y : H) :
    Continuous (fun g => inner ℂ (unitaryConjugate U T g x) y) := by
  have he : (fun g => inner ℂ (unitaryConjugate U T g x) y) =
      fun g => inner ℂ (T (U g⁻¹ x)) (U g⁻¹ y) := by
    funext g
    change inner ℂ (U g (T (U g⁻¹ x))) y = _
    rw [← adjoint_inner_right, hstar]
  rw [he]
  exact (T.continuous.comp ((hcont x).comp continuous_inv)).inner
    ((hcont y).comp continuous_inv)

/-- On a compact group these continuous scalar coefficients are integrable
against Haar probability measure. -/
theorem weaklyIntegrable_unitaryConjugate (μ : Measure Γ) [IsFiniteMeasure μ]
    (U : Γ →* (H →L[ℂ] H)) (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (hcont : ∀ x, Continuous (fun g => U g x)) (T : H →L[ℂ] H) :
    WeaklyIntegrable μ (unitaryConjugate U T) := by
  intro x y
  exact (continuous_unitaryConjugate_coefficient U hstar hcont T x y).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space implementation of trace-preserving automorphisms. The
implementation and its covariance are constructed from dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (θ : P ≃⋆ₐ[ℂ] P)
  (hθ : ∀ a, G.trace (θ a) = G.trace a)

/-- Multiplication covariance extends from the algebra to the whole Hilbert space. -/
theorem automorphismUnitary_left (a : P) (x : H) :
    G.automorphismUnitary θ hθ (G.left a x) =
      G.left (θ a) (G.automorphismUnitary θ hθ x) := by
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [G.left_vector, automorphismUnitary_vector, map_mul]

theorem automorphismUnitary_fixes_base (A : StarSubalgebra ℂ P)
    (hA : ∀ a : A, θ (a : P) = (a : P)) (x : G.baseSpace A) :
    G.automorphismUnitary θ hθ (x : H) = (x : H) := by
  refine (G.baseVector_dense A).induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change G.automorphismUnitary θ hθ (G.vector (a : P)) = G.vector (a : P)
  rw [G.automorphismUnitary_vector, hA]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D)
  (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- The constructed matrix action fixes the whole completed base space,
by the algebraic fixation of its dense bounded vectors. -/
theorem matrixExtensionUnitaryRepresentation_base
    (u : Matrix.unitaryGroup α ℂ) (x : G.baseSpace A) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (x : H) = (x : H) := by
  exact G.automorphismUnitary_fixes_base
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a)
    A (fun a => G.matrixExtensionAutomorphism_base A D ι hgen hfaithful hext u a) x

/-- The represented ambient left action transforms under the actual
matrix-conjugation automorphism on all Hilbert vectors. -/
theorem matrixExtensionUnitaryRepresentation_left
    (u : Matrix.unitaryGroup α ℂ) (a : P) (x : H) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (G.left a x) =
    G.left (G.chosenMatrixExtension A D ι hext u a)
      ((G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H) x) := by
  exact G.automorphismUnitary_left
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun a => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u a) a x

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong continuity of the constructed finite matrix action follows from
ordinary factor-algebra density and the isometry bound; it is not an extra
free-product or Haar-averaging hypothesis. -/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology CStarAlgebra

section ContinuousOrbits
variable {Γ H : Type*} [TopologicalSpace Γ]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  (U : Γ → H →L[ℂ] H)

/-- A common contraction bound makes the continuous-orbit subspace closed. -/
theorem continuousOrbitSubmodule_isClosed (hU : ∀ g, ‖U g‖ ≤ 1) :
    IsClosed (continuousOrbitSubmodule U : Set H) := by
  apply isSeqClosed_iff_isClosed.mp
  intro x y hx hy
  have hu : TendstoUniformly (fun n g => U g (x n)) (fun g => U g y) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hy ε hε] with n hn
    intro g
    have hbound : dist (U g y) (U g (x n)) ≤ dist (x n) y := by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm, norm_sub_rev]
      calc
        ‖U g (y - x n)‖ ≤ ‖U g‖ * ‖y - x n‖ := (U g).le_opNorm _
        _ ≤ 1 * ‖y - x n‖ := mul_le_mul_of_nonneg_right (hU g) (norm_nonneg _)
        _ = ‖y - x n‖ := one_mul _
    exact hbound.trans_lt hn
  exact hu.continuous (Filter.Eventually.of_forall hx).frequently

end ContinuousOrbits

namespace TracialCornerGeometry
variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- The tracial vector map is continuous because it is left multiplication
on its fixed vacuum vector. -/
theorem continuous_vector : Continuous G.vector := by
  have he : (G.vector : P → H) = fun a => G.left a (G.vector 1) := by
    funext a
    simpa only [mul_one] using (G.left_vector a 1).symm
  rw [he]
  exact (map_continuous G.left).clm_apply continuous_const

variable (A D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : G.MatrixConjugationExtensionInput D ι A)

/-- Conjugation of a fixed factor element depends continuously on the matrix
unitary, directly from finite-dimensional continuity and multiplication. -/
theorem continuous_matrixConjugateLetter (d : D) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => (matrixConjugateLetter D ι u d : P)) := by
  have hι : Continuous (D.subtype.comp ι : Matrix α α ℂ →⋆ₐ[ℂ] P) :=
    (D.subtype.comp ι).toAlgHom.toLinearMap.continuous_of_finiteDimensional
  have hc : Continuous (fun u : Matrix.unitaryGroup α ℂ => (ι (u : Matrix α α ℂ) : P)) :=
    hι.comp continuous_subtype_val
  simpa only [matrixConjugateLetter, MulMemClass.coe_mul, StarMemClass.coe_star] using
    (hc.fun_mul continuous_const).fun_mul hc.star

/-- Every element of the algebra generated by the two factors has a
continuous orbit in the original operator norm. -/
theorem continuous_chosenMatrixExtension (a : factorAlgebra A D) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ => G.chosenMatrixExtension A D ι hext u (a : P)) := by
  let S : StarSubalgebra ℂ P :=
    { carrier := {a | Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u a)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => (0 : P)))
      one_mem' := by simpa only [Set.mem_ofPred_eq, map_one] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => (1 : P)))
      add_mem' := by intro a b ha hb; simpa only [Set.mem_ofPred_eq, map_add] using ha.fun_add hb
      mul_mem' := by intro a b ha hb; simpa only [Set.mem_ofPred_eq, map_mul] using ha.fun_mul hb
      algebraMap_mem' := by
        intro c
        have he : (fun u : Matrix.unitaryGroup α ℂ =>
            G.chosenMatrixExtension A D ι hext u (algebraMap ℂ P c)) =
            fun _ => algebraMap ℂ P c :=
          funext (fun u => (G.chosenMatrixExtension A D ι hext u).commutes c)
        change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
          G.chosenMatrixExtension A D ι hext u (algebraMap ℂ P c))
        rw [he]
        exact continuous_const
      star_mem' := by intro a ha; simpa only [Set.mem_ofPred_eq, map_star] using ha.star }
  have hs : factorAlgebra A D ≤ S := by
    apply StarAlgebra.adjoin_le
    intro x hx
    rcases hx with hx | hx
    · change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u x)
      simpa only [G.chosenMatrixExtension_base A D ι hext _ (⟨x, hx⟩ : A)] using
        (continuous_const : Continuous (fun _ : Matrix.unitaryGroup α ℂ => x))
    · change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
        G.chosenMatrixExtension A D ι hext u x)
      simpa only [G.chosenMatrixExtension_other A D ι hext _ (⟨x, hx⟩ : D)] using
        continuous_matrixConjugateLetter D ι (⟨x, hx⟩ : D)
  exact hs a.property

/-- The actual free-product matrix representation is strongly continuous;
only the ordinary tracial generation and published factor extension are used. -/
theorem matrixExtensionUnitaryRepresentation_stronglyContinuous (x : H) :
    Continuous (fun u : Matrix.unitaryGroup α ℂ =>
      (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H) x) := by
  let U : Matrix.unitaryGroup α ℂ → H →L[ℂ] H := fun u =>
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
  have hclosed : IsClosed (continuousOrbitSubmodule U : Set H) :=
    continuousOrbitSubmodule_isClosed U (fun u =>
      (Unitary.linearIsometryEquiv
        (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u)).toLinearIsometry.norm_toContinuousLinearMap_le)
  refine hgen.induction_on x hclosed ?_
  intro a
  change Continuous (fun u : Matrix.unitaryGroup α ℂ =>
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H)
      (G.vector (a : P)))
  simpa only [G.matrixExtensionUnitaryRepresentation_vector, Function.comp_def] using
    G.continuous_vector.comp (G.continuous_chosenMatrixExtension A D ι hext a)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixSymmetrization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_base _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_column _root_.OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily_corner _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerToRightColumn_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightColumnRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.right_zero _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialSmallColumn_vector _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact groups in free-product symmetrization are the actual matrix
unitary groups. Their compatibility follows from the nested matrix embeddings
and uniqueness of the trace-preserving extension on the two factors. -/

noncomputable section
namespace KadisonSimilarity

section Conjugation

variable {H Γ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Group Γ]

omit [CompleteSpace H] in
/-- Conjugation transports a commutator through its actual covariance. -/
theorem commutator_unitaryConjugate_of_covariance
    (U : Γ →* (H →L[ℂ] H)) (T B C : H →L[ℂ] H) (g : Γ)
    (hcov : U g⁻¹ * B = C * U g⁻¹) :
    commutator (unitaryConjugate U T g) B =
      unitaryConjugate U (commutator T C) g := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hi' : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcov' : B * U g = U g * C := by
    calc
      B * U g = (U g * U g⁻¹) * B * U g := by rw [hi, one_mul]
      _ = U g * (U g⁻¹ * B) * U g := by simp only [mul_assoc]
      _ = U g * (C * U g⁻¹) * U g := by rw [hcov]
      _ = U g * C := by simp only [mul_assoc, hi', mul_one]
  change U g * T * U g⁻¹ * B - B * (U g * T * U g⁻¹) =
    U g * (T * C - C * T) * U g⁻¹
  rw [mul_sub, sub_mul]
  congr 1
  · calc
      U g * T * U g⁻¹ * B = U g * T * (U g⁻¹ * B) := mul_assoc _ _ _
      _ = U g * T * (C * U g⁻¹) := by rw [hcov]
      _ = U g * (T * C) * U g⁻¹ := by simp only [mul_assoc]
  · calc
      B * (U g * T * U g⁻¹) = (B * U g) * (T * U g⁻¹) := by simp only [mul_assoc]
      _ = (U g * C) * (T * U g⁻¹) := by rw [hcov']
      _ = U g * (C * T) * U g⁻¹ := by simp only [mul_assoc]

end Conjugation

namespace TracialCornerGeometry

open MeasureTheory TopologicalSpace
open scoped Topology CStarAlgebra ComplexOrder

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)

omit [∀ j, Nonempty (I j)] in
theorem matrixStageUnitaryInclusion_embedding (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    M.embedding j (G.matrixStageUnitaryInclusion D M i j h u : Matrix (I j) (I j) ℂ) =
      M.embedding i (u : Matrix (I i) (I i) ℂ) :=
  M.compatible i j h u

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- The ambient extension does not depend on the matrix stage used to
represent the same unitary in the factor. -/
theorem chosenMatrixExtension_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.chosenMatrixExtension A D (M.embedding j) (hext j)
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.chosenMatrixExtension A D (M.embedding i) (hext i) u := by
  apply G.hom_eq_of_factor_eq A D hgen hfaithful
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · exact G.chosenMatrixExtension_trace A D _ _ _
  · intro a
    rw [G.chosenMatrixExtension_base, G.chosenMatrixExtension_base]
  · intro d
    rw [G.chosenMatrixExtension_other, G.chosenMatrixExtension_other]
    congr 1
    simp only [matrixConjugateLetter, G.matrixStageUnitaryInclusion_embedding]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
/-- Compatibility of the actual Hilbert-space representations is proved
on dense algebra vectors. -/
theorem tracialMatrixUnitaryRepresentation_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext i u := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp only [tracialMatrixUnitaryRepresentation, G.matrixExtensionUnitaryRepresentation_vector]
  rw [G.chosenMatrixExtension_compatible A D M hgen hfaithful hext i j h u]

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_star (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).adjoint =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u⁻¹ := by
  change (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u :
    H →L[ℂ] H).adjoint =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ : H →L[ℂ] H)
  rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star]
  have hs : star (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u) =
      G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j u⁻¹ := by
    rw [Unitary.star_eq_inv, map_inv]
  exact congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H)) hs

omit [∀ j, Nonempty (I j)] in
theorem norm_tracialMatrixUnitaryOperator_le (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    ‖G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖G.automorphismUnitary
    (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u)
    (fun a => G.matrixExtensionAutomorphism_trace A D (M.embedding j) hgen hfaithful
      (hext j) u a) x‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, one_mul]

include hgen hfaithful in
omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_compatible (i j : ℕ) (h : i ≤ j)
    (u : Matrix.unitaryGroup (I i) ℂ) :
    G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j
        (G.matrixStageUnitaryInclusion D M i j h u) =
      G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext i u := by
  exact congrArg (fun v : unitary (H →L[ℂ] H) => (v : H →L[ℂ] H))
    (G.tracialMatrixUnitaryRepresentation_compatible A D M hgen hfaithful hext i j h u)

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_fixes_base (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u).comp
        (G.baseInclusion A).toContinuousLinearMap = (G.baseInclusion A).toContinuousLinearMap := by
  ext x
  exact G.matrixExtensionUnitaryRepresentation_base A D (M.embedding j) hgen hfaithful
    (hext j) u x

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryOperator_stronglyContinuous (j : ℕ) (x : H) :
    Continuous (fun u => G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j u x) :=
  G.matrixExtensionUnitaryRepresentation_stronglyContinuous A D (M.embedding j)
    hgen hfaithful (hext j) x

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryCompactSpace
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryMeasurableSpace
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.matrixUnitaryBorelSpace
/-- The weak integrability needed for the actual Haar average is a
consequence of the proved strong continuity. -/
theorem weaklyIntegrable_tracialMatrixUnitaryConjugate (j : ℕ)
    (μ : Measure (Matrix.unitaryGroup (I j) ℂ)) [IsFiniteMeasure μ] (T : H →L[ℂ] H) :
    WeaklyIntegrable μ
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T) :=
  weaklyIntegrable_unitaryConjugate μ _
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext j)
    (G.tracialMatrixUnitaryOperator_stronglyContinuous A D M hgen hfaithful hext j) T

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutator (T : H →L[ℂ] H)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (x : P) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left x) =
    unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      (commutator T (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ x)))
      u := by
  apply commutator_unitaryConjugate_of_covariance
  ext v
  exact G.matrixExtensionUnitaryRepresentation_left A D (M.embedding j) hgen hfaithful
    (hext j) u⁻¹ x v

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_commutes_factor (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) (d : D) :
    commutator (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j)
      T u) (G.left (d : P)) = 0 := by
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  have hd : G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P) ∈ D := by
    rw [G.chosenMatrixExtension_other]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ d).property
  have hz : commutator T
      (G.left (G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹ (d : P))) = 0 :=
    sub_eq_zero.mpr (hTD ⟨_, hd⟩)
  rw [hz]
  simp only [unitaryConjugate, mul_zero, zero_mul]

omit [∀ j, Nonempty (I j)] in
theorem tracialMatrixUnitaryConjugate_cornerBound (T : H →L[ℂ] H) {t ε : ℝ}
    (hT : G.TraceCornerBound D T t ε) (j : ℕ) (u : Matrix.unitaryGroup (I j) ℂ) :
    G.TraceCornerBound D
      (unitaryConjugate (G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext j) T u) t ε := by
  intro e he heD het x
  let Φ := G.chosenMatrixExtension A D (M.embedding j) (hext j) u⁻¹
  have he' : IsStarProjection (Φ e) := by
    constructor
    · change Φ e * Φ e = Φ e
      rw [← map_mul, he.isIdempotentElem.eq]
    · change star (Φ e) = Φ e
      rw [← map_star, he.isSelfAdjoint.star_eq]
  have heD' : Φ e ∈ D := by
    dsimp only [Φ]
    rw [G.chosenMatrixExtension_other A D (M.embedding j) (hext j) u⁻¹ ⟨e, heD⟩]
    exact (matrixConjugateLetter D (M.embedding j) u⁻¹ ⟨e, heD⟩).property
  have het' : G.trace (Φ e) = (t : ℂ) :=
    (G.chosenMatrixExtension_trace A D (M.embedding j) (hext j) u⁻¹ e).trans het
  let x' : CStarCorner (Φ e) he' := ⟨Φ (x : P), by
    constructor
    · rw [← map_mul, x.property.1]
    · rw [← map_mul, x.property.2]⟩
  have hn : ‖x'‖ = ‖x‖ :=
    StarAlgEquiv.norm_map
      (G.matrixExtensionAutomorphism A D (M.embedding j) hgen hfaithful (hext j) u⁻¹) (x : P)
  rw [G.tracialMatrixUnitaryConjugate_commutator A D M hgen hfaithful hext]
  apply (norm_unitaryConjugate_le _
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext j) _ u).trans
  simpa only [hn] using hT (Φ e) he' heD' het' x'

include hgen hfaithful in
/-- Simultaneous compact averaging produces the exact additional symmetries
used by word classification. It preserves the original base compression and
the uniform corner bound. No invariant limiting operator is an input. -/
theorem exists_tracially_symmetrized_oai (T : H →L[ℂ] H)
    (hTD : ∀ d : D, T.comp (G.left (d : P)) = (G.left (d : P)).comp T)
    {t ε : ℝ} (hε : 0 ≤ ε) (hcorner : G.TraceCornerBound D T t ε) :
    ∃ Y : H →L[ℂ] H,
      ‖Y‖ ≤ ‖T‖ ∧
      (∀ d : D, Y.comp (G.left (d : P)) = (G.left (d : P)).comp Y) ∧
      (∀ j w, Y.comp
          (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y) ∧
      G.TraceCornerBound D Y t ε ∧ G.baseOperator A Y = G.baseOperator A T := by
  let U := G.tracialMatrixUnitaryOperator A D M hgen hfaithful hext
  let Test := D ⊕ G.traceCornerElements D t
  let test : Test → H →L[ℂ] H := Sum.elim (fun d => G.left (d : P)) (fun x => G.left (x : P))
  let bound : Test → ℝ := Sum.elim (fun _ => 0) (fun x => ε * ‖(x : P)‖)
  have hbound : ∀ x, 0 ≤ bound x := by
    intro x
    cases x with
    | inl d => exact le_refl 0
    | inr x => exact mul_nonneg hε (norm_nonneg _)
  have htest : ∀ j w x, ‖commutator (unitaryConjugate (U j) T w) (test x)‖ ≤ bound x := by
    intro j w x
    cases x with
    | inl d =>
      change ‖commutator (unitaryConjugate (U j) T w) (G.left (d : P))‖ ≤ 0
      rw [G.tracialMatrixUnitaryConjugate_commutes_factor A D M hgen hfaithful hext T hTD]
      simp only [norm_zero, le_refl]
    | inr x =>
      obtain ⟨e, he, heD, het, hxleft, hxright⟩ := x.property
      exact G.tracialMatrixUnitaryConjugate_cornerBound A D M hgen hfaithful hext T hcorner
        j w e he heD het ⟨x, hxleft, hxright⟩
  obtain ⟨Y, hYnorm, hYW, hYtest, hbase⟩ := exists_simultaneously_symmetrized
    (tracialMatrixHaarProbability (I := I)) U
    (G.norm_tracialMatrixUnitaryOperator_le A D M hgen hfaithful hext)
    (G.tracialMatrixUnitaryOperator_star A D M hgen hfaithful hext)
    (fun i j h u => G.matrixStageUnitaryInclusion D M i j h u)
    (G.tracialMatrixUnitaryOperator_compatible A D M hgen hfaithful hext) T
    (fun j => G.weaklyIntegrable_tracialMatrixUnitaryConjugate A D M hgen hfaithful hext j _ T)
    (G.baseInclusion A).toContinuousLinearMap
    (G.tracialMatrixUnitaryOperator_fixes_base A D M hgen hfaithful hext)
    test bound hbound htest
  refine ⟨Y, hYnorm, ?_, ?_, ?_, ?_⟩
  · intro d
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (hYtest (.inl d)) (norm_nonneg _)
  · intro j w
    exact sub_eq_zero.mp (hYW j w)
  · intro e he heD het x
    exact hYtest (.inr ⟨(x : P), e, he, heD, het, x.property.1, x.property.2⟩)
  · exact hbase

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.TracialCornerGeometry.exists_tracially_symmetrized_oai.{u_1, u_2, u_3}
