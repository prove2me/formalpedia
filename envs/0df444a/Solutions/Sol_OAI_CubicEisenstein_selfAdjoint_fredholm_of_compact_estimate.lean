-- Prove2me | solution 1 for OAI.CubicEisenstein.selfAdjoint_fredholm_of_compact_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:10:37.075792+00:00
-- url     : https://prove2.me/submissions/8f8c2d54-8d92-456b-bd8f-4a9dacaf201a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Theorems.Thm_OAI_CubicEisenstein_ker_orthogonal_restriction_range
import Theorems.Thm_OAI_CubicEisenstein_ker_orthogonal_restriction_antilipschitz
import Theorems.Thm_OAI_CubicEisenstein_closed_range_of_compact_estimate
import Theorems.Thm_OAI_CubicEisenstein_selfAdjoint_range_eq_ker_orthogonal
import Theorems.Thm_OAI_CubicEisenstein_finiteDimensional_ker_of_compact_estimate


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
namespace OAI.CubicEisenstein
theorem _root_.solution (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  have he : (T.domRestrict T.kerᗮ).range=T.range := by
    apply SetLike.coe_injective
    exact ker_orthogonal_restriction_range T
  have hi := hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous
  have hs : Topology.IsStrictMap T :=
    ((T.isStrictMap_isClosed_range_iff_restrict T.kerᗮ T.ker.isClosed_orthogonal).mpr
      ⟨hi.isEmbedding.isStrictMap, by rw [he]; exact hrange⟩).1
  exact ⟨hs, hrange, inferInstance, inferInstance,
    (Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional T.ker.isCompl_orthogonal.symm
      T.ker.isClosed_orthogonal).symm.closedComplemented⟩
end OAI.CubicEisenstein
