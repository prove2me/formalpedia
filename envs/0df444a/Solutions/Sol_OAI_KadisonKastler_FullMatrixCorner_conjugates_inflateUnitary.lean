-- Prove2me | solution 1 for OAI.KadisonKastler.FullMatrixCorner.conjugates_inflateUnitary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:53:27.699735+00:00
-- url     : https://prove2.me/submissions/1e4e726a-0cb1-4845-ab2d-f64817a6ecfd

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K014
import Definitions.Def_Q260K017

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

theorem column_adjoint_apply (i : ℕ) (x : H) :
    (F.column i).toContinuousLinearMap.adjoint x =
      E.orthogonalProjectionOnto (F.entry 0 i x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (F.entry i 0 y) x =
    inner ℂ y (E.orthogonalProjectionOnto (F.entry 0 i x))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← F.star_entry i 0, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem matrixEntry_apply (T : H →L[ℂ] H) (i j : ℕ) (x : E) :
    F.matrixEntry T i j x =
      E.orthogonalProjectionOnto (F.entry 0 i (T (F.entry j 0 x))) := by
  exact F.column_adjoint_apply i _

/-- Matrix coefficients of the inflated unitary conjugation are the original
corner conjugation, with no change of representation or norm. -/
theorem matrixEntry_unitaryConj (v : unitary (E →L[ℂ] E))
    (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (unitaryConj (F.inflateUnitary v) T) i j =
      unitaryConj v (F.matrixEntry T i j) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have hs (k : ℕ) (z : E) :
      star (F.inflateUnitary v : H →L[ℂ] H) (F.column k z) =
        F.column k (star (v : E →L[ℂ] E) z) := by
    rw [coe_inflateUnitary, ← map_star]
    exact F.inflateHom_column _ k z
  change inner ℂ y ((F.column i).toContinuousLinearMap.adjoint
      ((F.inflateUnitary v : H →L[ℂ] H)
        (T (star (F.inflateUnitary v : H →L[ℂ] H) (F.column j x))))) =
    inner ℂ y ((v : E →L[ℂ] E)
      ((F.column i).toContinuousLinearMap.adjoint
        (T (F.column j (star (v : E →L[ℂ] E) x)))))
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateUnitary v : H →L[ℂ] H) (F.column i y))
      (T (star (F.inflateUnitary v : H →L[ℂ] H) (F.column j x))) = _
  rw [hs, hs]
  rw [← ContinuousLinearMap.adjoint_inner_left (v : E →L[ℂ] E)
    ((F.column i).toContinuousLinearMap.adjoint
      (T (F.column j (star (v : E →L[ℂ] E) x)))) y]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem extension_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    cornerExtension E (F.matrixEntry T i j) = F.entry 0 i * T * F.entry j 0 := by
  have he : F.matrixEntry T i j =
      cornerCompression E (F.entry 0 i * T * F.entry j 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact F.matrixEntry_apply T i j x
  rw [he, cornerExtension_compression, ← F.zero_zero]
  calc
    F.entry 0 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 0 =
        (F.entry 0 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 0) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

/-- Membership of every transported matrix entry determines membership of
the whole operator. The proof uses actual finite compressions and WOT closure. -/
theorem mem_of_matrixEntries (N : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ N) (T : H →L[ℂ] H)
    (hT : ∀ i j, cornerExtension E (F.matrixEntry T i j) ∈ N) : T ∈ N := by
  have hterm (i j : ℕ) : F.entry i i * T * F.entry j j ∈ N := by
    have h := N.mul_mem (N.mul_mem (hF i 0) (hT i j)) (hF 0 j)
    rw [F.extension_matrixEntry] at h
    have he : F.entry i 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 j =
        F.entry i i * T * F.entry j j := by
      calc
        _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
          noncomm_ring
        _ = _ := by rw [F.mul_entry, F.mul_entry]; simp
    rwa [he] at h
  have hmem (s : Finset ℕ) : F.partialDiagonal s * T * F.partialDiagonal s ∈ N := by
    simp only [partialDiagonal, Finset.sum_mul, Finset.mul_sum]
    exact N.sum_mem (fun i _ => N.sum_mem (fun j _ => hterm j i))
  let a (s : Finset ℕ) : Algebra N :=
    ⟨F.partialDiagonal s * T * F.partialDiagonal s, hmem s⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N a T
  intro x y
  have ht := (F.partialDiagonal_tendsto y).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))
  have he (s : Finset ℕ) :
      inner ℂ (F.partialDiagonal s y) (T (F.partialDiagonal s x)) =
        inner ℂ y ((F.partialDiagonal s * T * F.partialDiagonal s) x) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal s)
      (T (F.partialDiagonal s x)) y]
    simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  exact ht.congr he

/-- A conjugacy of the common initial corners inflates to a conjugacy of
the original algebras, retaining the corner displacement bound. -/
theorem conjugates_inflateUnitary_oai (M N : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N)
    (v : unitary (E →L[ℂ] E))
    (hv : Conjugates v
      (representedCorner E M (F.zero_zero ▸ hM 0 0))
      (representedCorner E N (F.zero_zero ▸ hN 0 0))) :
    Conjugates (F.inflateUnitary v) M N := by
  have hdir (P Q : VonNeumannAlgebra H)
      (hP : ∀ i j, F.entry i j ∈ P) (hQ : ∀ i j, F.entry i j ∈ Q)
      (w : unitary (E →L[ℂ] E))
      (hw : Conjugates w
        (representedCorner E P (F.zero_zero ▸ hP 0 0))
        (representedCorner E Q (F.zero_zero ▸ hQ 0 0)))
      (T : H →L[ℂ] H) (hT : T ∈ P) :
      unitaryConj (F.inflateUnitary w) T ∈ Q := by
    apply F.mem_of_matrixEntries Q hQ
    intro i j
    rw [F.matrixEntry_unitaryConj]
    have he : F.matrixEntry T i j ∈ representedCorner E P (F.zero_zero ▸ hP 0 0) := by
      rw [mem_representedCorner, F.extension_matrixEntry]
      exact P.mul_mem (P.mul_mem (hP 0 i) hT) (hP j 0)
    have hq : unitaryConj w (F.matrixEntry T i j) ∈
        representedCorner E Q (F.zero_zero ▸ hQ 0 0) := by
      change unitaryConj w (F.matrixEntry T i j) ∈
        (representedCorner E Q (F.zero_zero ▸ hQ 0 0) : Set (E →L[ℂ] E))
      rw [← hw]
      exact ⟨F.matrixEntry T i j, he, rfl⟩
    exact hq
  apply Set.Subset.antisymm
  · rintro _ ⟨T, hT, rfl⟩
    exact hdir M N hM hN v hv T hT
  · intro T hT
    have hs : F.inflateUnitary (star v) = star (F.inflateUnitary v) := by
      apply Subtype.ext
      exact map_star F.inflateHom (v : E →L[ℂ] E)
    refine ⟨unitaryConj (star (F.inflateUnitary v)) T, ?_, ?_⟩
    · change unitaryConj (star (F.inflateUnitary v)) T ∈ M
      simpa only [hs] using hdir N M hN hM (star v) hv.symm T hT
    · simpa only [star_star] using unitaryConj_star_unitaryConj
        (star (F.inflateUnitary v)) T

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.FullMatrixCorner.conjugates_inflateUnitary_oai.{u_1} := @OAI.KadisonKastler.FullMatrixCorner.conjugates_inflateUnitary_oai.{u_1}
