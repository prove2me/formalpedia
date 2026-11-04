-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:31:38.021918+00:00
-- url     : https://prove2.me/submissions/e443acc8-7830-47fe-88ee-0d9e3562ddea

import Mathlib
import Definitions.Def_KadisonSimilarity
import Definitions.Def_OAIQ075A033
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_actual_dihedral_column_eq_repeated
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_adjoint_commutes_with_base
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_adjoint_corner_commutator_bound
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_baseMatrixWordAction_endpoint
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_baseRepresentation_baseVector
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_centeredBaseAlgebraVector_dense
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_haarRepeatedWordInclusion_factor
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_norm_tracialSmallColumn
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracialSmallColumn_level_zero
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracialSmallColumn_support
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracial_baseWordInclusion_eq
import Theorems.Thm_OAI_KadisonSimilarity_TracialCornerGeometry_tracial_baseWordInclusion_vector
import Theorems.Thm_OAI_KadisonSimilarity_TracialHeadCoordinates_vacuum_hasOrthogonalProjection
import Theorems.Thm_OAI_KadisonSimilarity_TracialRepeatedWordRealization_propagation_on_base_of_published_inputs
import Theorems.Thm_OAI_KadisonSimilarity_adjoint_commutes_of_adjoint_commutes
import Theorems.Thm_OAI_KadisonSimilarity_automorphism_alternatingProduct
import Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_compression
import Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_eq_baseInclusion
import Theorems.Thm_OAI_KadisonSimilarity_baseWordInclusion_intertwines
import Theorems.Thm_OAI_KadisonSimilarity_cyclicConstant_pos
import Theorems.Thm_OAI_KadisonSimilarity_embedded_actions_adjoint_repeated_word
import Theorems.Thm_OAI_KadisonSimilarity_embedded_actions_repeated_word
import Theorems.Thm_OAI_KadisonSimilarity_embedded_actions_word_levels_preserved
import Theorems.Thm_OAI_KadisonSimilarity_free_corner_from_multiplicity_propagation
import Theorems.Thm_OAI_KadisonSimilarity_repeatedMultiplicityInclusion_zero

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ConcreteRepeatedPropagation
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated-word propagation with all small-vector and prefix estimates
constructed from the actual scalar-free tracial model. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {P : Type u} {H : Type v} {F : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (W : TracialHeadCoordinates (G.baseGeometry D) G D.subtype F)
  [W.vacuum.HasOrthogonalProjection]
  (s : A) (hzero : G.trace (s : P) = 0)
  (hself : star s = s) (hsquare : s * s = 1)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
  {ALead : Submodule ℂ H}
  (C : TracialCreationFormulas G A D W s hzero z ha htrace hhaar ALead)

include C ha htrace hhaar in
/-- The propagation conclusion for a positive degree. Only elementary word
formulas remain as geometric inputs: small-vector normalization, prefix
isometry, the exceptional coefficient limit, and the full-column estimate
are proved in the construction. -/
theorem concrete_repeated_propagation
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (m : ℕ) (Y : H →L[ℂ] H)
    (hbase : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (Bₖ : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (word : ℕ → WordMultiplicity (G.baseVector A 1) (m + 1) →ₗᵢ[ℂ] H)
    (hlevel : ∀ n v, Y (word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)) =
      word n (Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v)))
    (hword : ∀ n (v : A), word n
      (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseVector A v)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P)
          (G.vector ((q : P) * (v : P)))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (hfaithful : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison τ)
    {n : ℕ} (hn : 0 < n) (frame : Fin n → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hY : ∀ x : CStarCorner e he,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖Bₖ (G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1) v) -
      G.baseSymmetryRepeatedInclusion A s hzero hself hsquare hτ (m + 1)
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  let R := C.repeatedWordRealization hself hsquare hτ m Y (G.baseOperator A Y) Bₖ word
    (G.tracialSmallColumn A (q : P))
    (G.norm_tracialSmallColumn A D hf hτ (q : P) (hq.map D.subtype) q.property ha.le htrace)
    (G.tracialSmallColumn_level_zero A (q : P) Y hbase (hYD q)) hlevel
    (fun v => congrArg (fun T : G.baseSpace A →L[ℂ] H => T v)
      (G.tracialSmallColumn_support A (q : P) (hq.map D.subtype)))
    (by simpa only [G.tracialSmallColumn_vector] using hword)
  exact R.propagation_on_base_of_published_inputs
    (G.baseGeometry_trace_one D hτ) ha htrace hhaar τ support
    (G.tracialSmallColumn_vector A (q : P)) e he hqe
    hfaithful comparison hn (fun i => (frame i : P)) hframe hsum
    (hYD ⟨e, heD⟩) (fun i => hYD (frame i)) hε hY published commutation v

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordBaseCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the degree-zero multiplicity operator with the actual compression
to the base algebra's tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

section TracialBase
variable {P : Type*} [CStarAlgebra P]
  (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) E F) H)

/-- The degree-zero operator is the actual tracial compression, rather than
an unrelated multiplicity coefficient. -/
theorem baseOperator_eq_zeroMultiplicityOperator (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ] WordMultiplicity (G.baseVector A 1) 0)
    (hword : ∀ a : A,
      baseWordInclusion (G.baseVector A 1) U ΩD hΩD (G.baseVector A a) = G.vector (a : P))
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v (emptyEndpoint (F := F) ΩD))) =
      U.inclusion 0 (hilbertTensorInsert (T v) (emptyEndpoint (F := F) ΩD))) :
    G.baseOperator A Y = zeroMultiplicityOperator (G.baseVector A 1) T := by
  have h := baseWordInclusion_compression (G.baseVector A 1) U ΩD hΩD Y T hY
  rw [baseWordInclusion_eq_baseInclusion ΩD hΩD G A U hword] at h
  exact h

end TracialBase
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordDensity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of bounded word maps can be tested on actual bounded algebra
letters. This bridges the published product formula to completed word actions. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

attribute [local irreducible] tensorWordSpace TracialCornerGeometry.baseSpace

variable {P H K : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseANormed
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseAInner
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseDNormed
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseDInner
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.centeredANormed
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.centeredAInner
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.centeredDNormed
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.centeredDInner
/-- Bounded algebra vectors determine every continuous map on a word level. -/
theorem continuousLinearMap_ext_tracialWordTensors (hτ : G.trace 1 = 1) (n : ℕ)
    (f g : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K)
    (h : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      f (tracialWordTensor G A D n d b a c ha hc) =
        g (tracialWordTensor G A D n d b a c ha hc)) : f = g := by
  refine continuousLinearMap_ext_denseTensorPackets
    (X := centeredSubspace (G.baseVector A 1)) (B := G.baseSpace A)
    (E := G.baseSpace D) (F := centeredSubspace (G.baseVector D 1)) (n := n) (K := K)
    (G.centeredBaseAlgebraVector A) (G.baseVector A) (G.baseVector D)
    (G.centeredBaseAlgebraVector D) ?_ ?_ ?_ ?_ _ _ ?_
  · exact G.centeredBaseAlgebraVector_dense A hτ
  · exact G.baseVector_dense A
  · exact G.baseVector_dense D
  · exact G.centeredBaseAlgebraVector_dense D hτ
  · intro a b d c
    exact h d b (fun i => (a i).val) (fun i => (c i).val)
      (fun i => (a i).property) (fun i => (c i).property)

/-- Equality on bounded algebra words determines a continuous map on the
completed word space. -/
theorem function_ext_tracialWordTensors (hτ : G.trace 1 = 1) (n : ℕ)
    (p q : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) → K)
    (hp : Continuous p) (hq : Continuous q)
    (hpadd : ∀ x y, p (x + y) = p x + p y) (hqadd : ∀ x y, q (x + y) = q x + q y)
    (hpsmul : ∀ (c : ℂ) x, p (c • x) = c • p x)
    (hqsmul : ∀ (c : ℂ) x, q (c • x) = c • q x)
    (h : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      p (tracialWordTensor G A D n d b a c ha hc) =
        q (tracialWordTensor G A D n d b a c ha hc)) : p = q := by
  let fp : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K :=
    { toFun := p, map_add' := hpadd, map_smul' := hpsmul, cont := hp }
  let fq : HilbertTensor
      (HilbertTensor (CompletedTensorWord (centeredSubspace (G.baseVector A 1)) n)
        (G.baseSpace A))
      (EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n) →L[ℂ] K :=
    { toFun := q, map_add' := hqadd, map_smul' := hqsmul, cont := hq }
  exact congrArg DFunLike.coe
    (G.continuousLinearMap_ext_tracialWordTensors A D hτ n fp fq h)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialAutomorphismWords
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unitary word formula is derived from the algebraic product
formula and the actual implementation of a trace-preserving automorphism. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

variable (A : StarSubalgebra ℂ P) [IsClosed (A : Set P)]

/-- The multiplicity letters are fixed, and the endpoint letters are
conjugated by the represented matrix unitary. -/
theorem baseMatrixWordAction_tensor (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
      (tracialWordTensor G A D n d b a c ha hc) =
    tracialWordTensor G A D n (matrixConjugateLetter D ι u d) b a
      (fun i => matrixConjugateLetter D ι u (c i)) ha
      (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i)) := by
  simp only [tracialWordTensor, hilbertTensorLift_insert,
    LinearIsometry.coe_toContinuousLinearMap, G.baseMatrixWordAction_endpoint]

end TracialCornerGeometry

namespace TracialWordFormula

open TracialCornerGeometry

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (θ : P ≃⋆ₐ[ℂ] P) (hθ : ∀ x, G.trace (θ x) = G.trace x)
  (hA : ∀ a : A, θ (a : P) = (a : P))
  (hD : ∀ d : D, θ (d : P) = (matrixConjugateLetter D ι u d : P))

attribute [local instance] OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialWordFormula.automorphismMultiplicityInnerFamily
variable
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}

include hA hD in
/-- On bounded tracial words, automorphism covariance is a consequence of
multiplicativity, factor fixation, and the reduced-word product formula. -/
theorem automorphism_word (hU : TracialWordFormula G A D U)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.automorphismUnitary θ hθ
      (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
    U.inclusion n (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
      (tracialWordTensor G A D n d b a c ha hc)) := by
  rw [G.baseMatrixWordAction_tensor, hU, hU, G.automorphismUnitary_vector]
  congr 1
  simp only [map_mul, automorphism_alternatingProduct, hA, hD]

/-- A bounded word intertwining identity extends from the actual algebra
letters to the entire completed word level. -/
theorem intertwining_of_bounded_words (hτ : G.trace 1 = 1) (n : ℕ)
    (W : H →L[ℂ] H)
    (T : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →L[ℂ]
      MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n)
    (hword : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      W (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
        U.inclusion n (T (tracialWordTensor G A D n d b a c ha hc))) :
    W.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp T := by
  apply DFunLike.coe_injective
  refine G.function_ext_tracialWordTensors (K := H) A D hτ n
    (fun z => W (U.inclusion n z)) (fun z => U.inclusion n (T z))
    (by fun_prop) (by fun_prop)
    (by intros; simp only [map_add]) (by intros; simp only [map_add])
    (by intros; simp only [map_smul]) (by intros; simp only [map_smul]) hword

include hA hD in
/-- Equality on the bounded algebra words extends the automorphism action to
its genuine completed-word intertwining identity. -/
theorem automorphism_level (hU : TracialWordFormula G A D U)
    (hτ : G.trace 1 = 1) (n : ℕ) :
    (G.automorphismUnitary θ hθ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) := by
  refine intertwining_of_bounded_words hτ n
    (G.automorphismUnitary θ hθ).toContinuousLinearEquiv.toContinuousLinearMap
    (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) ?_
  intro d b a c ha hc
  exact automorphism_word ι u θ hθ hA hD hU n d b a c ha hc

/-- The matrix action needed for finite-stage word classification is obtained
from the published factor extension, rather than supplied as tensor covariance. -/
theorem matrix_extension_level
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (hext : G.MatrixConjugationExtensionInput D ι A)
    (hU : TracialWordFormula G A D U) (hτ : G.trace 1 = 1) (n : ℕ) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H).comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) := by
  exact automorphism_level ι u
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun x => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u x)
    (fun a => G.matrixExtensionAutomorphism_base A D ι hgen hfaithful hext u a)
    (fun d => G.matrixExtensionAutomorphism_other A D ι hgen hfaithful hext u d)
    hU hτ n

end TracialWordFormula
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralEndgame
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Fourier matrix computed on the actual dihedral columns is the same
matrix tested by the repeated-word propagation estimate. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

/-- The exact Fourier compression of the actual normalized columns, together
with the derived multiplicity propagation bounds, controls the base symmetry. -/
theorem commutator_bound_of_actual_dihedral_compression
    (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (U : OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H)
    (hU : TracialWordFormula G A D U)
    (Y T : H →L[ℂ] H)
    (B : ∀ n, WordMultiplicity (G.baseVector A 1) n →L[ℂ]
      WordMultiplicity (G.baseVector A 1) n)
    (hY : ∀ n v d' r, Y (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (B n v) (endpointWord d' (fun _ : Fin n => r))))
    (hYstar : ∀ n v d' r, Y.adjoint (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((B n).adjoint v)
        (endpointWord d' (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n v,
      ‖B n (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          (G.baseOperator A Y v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hpropstar : ∀ n v,
      ‖(B n).adjoint (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          ((G.baseOperator A Y).adjoint v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  apply free_corner_from_multiplicity_propagation U hN
    (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ)
    (G.projectionEndpoint D e t) (G.baseSymmetryLetter D d hd0)
    (G.norm_projectionEndpoint D e he ht hte)
    (G.norm_baseSymmetryLetter D d hd0 hdstar hdsq hτ)
    Y T (G.baseOperator A Y) (G.baseRepresentation A s) B
    (fun n v => hY n v _ _) (fun n v => hYstar n v _ _)
    hlevel hlevelstar toeplitz hu hε hc₀ hT hcomm hprop hpropstar
  have hV : G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N = fun i =>
        (G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
          he ht hte U i.val).toContinuousLinearMap := by
    funext i
    ext v
    exact G.actual_dihedral_column_eq_repeated D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte U hf hU i.val v
  dsimp only at hfourier
  rw [hV] at hfourier
  exact hfourier

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The represented left head action follows from the ordinary product
formula in the reduced-word model. It is not extra covariance data. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityInnerFamily
theorem tracialWordHeadAction_tensor (n : ℕ) (x d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.tracialWordHeadAction A D n x (tracialWordTensor G A D n d b a c ha hc) =
      tracialWordTensor G A D n (x * d) b a c ha hc := by
  simp only [tracialWordHeadAction, tracialWordTensor, tracialEndpointWord,
    hilbertTensorLift_insert, endpointWord, endpointHeadAction_insert,
    G.baseRepresentation_baseVector D]

end TracialCornerGeometry

namespace TracialWordFormula

attribute [local instance] TracialCornerGeometry.actionMultiplicityNormedFamily
  TracialCornerGeometry.actionMultiplicityInnerFamily

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}

/-- The actual represented left action intertwines with the completed head
action, by equality on the dense bounded word vectors. -/
theorem left_head (hU : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
    (n : ℕ) (x : D) :
    (G.left (x : P)).comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (G.tracialWordHeadAction A D n x) := by
  apply DFunLike.coe_injective
  refine G.function_ext_tracialWordTensors (K := H) A D hτ n
    (fun z => G.left (x : P) (U.inclusion n z))
    (fun z => U.inclusion n (G.tracialWordHeadAction A D n x z))
    (by fun_prop) (by fun_prop)
    (by intros; simp only [map_add]) (by intros; simp only [map_add])
    (by intros; simp only [map_smul]) (by intros; simp only [map_smul]) ?_
  intro d b a c ha hc
  rw [G.tracialWordHeadAction_tensor, hU, hU, G.left_vector]
  congr 1
  simp only [MulMemClass.coe_mul, mul_assoc]

end TracialWordFormula
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialEmbeddedWordStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial free-product actions instantiate finite-stage word
classification. Both head covariance and matrix-unitary covariance follow
from the ordinary reduced-word formula. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ s, Fintype (I s)] [∀ s, DecidableEq (I s)]
  [∀ s, Nonempty (I s)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

variable (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ s, G.MatrixConjugationExtensionInput D (M.embedding s) A)

variable (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (I s) : ℝ)) Filter.atTop Filter.atTop)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.tracialEmbeddedMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)

include hword hτ in
/-- The left matrix covariance is the derived tracial head formula. -/
theorem tracialMatrixLeftRepresentation_inclusion (s : ℕ) (a : Matrix (I s) (I s) ℂ)
    (n : ℕ) :
    (G.tracialMatrixLeftRepresentation D M s a).comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (endpointHeadAction (n := n)
          (((G.baseTracialMatrixTower D M S hsize).stage s).left a))) := by
  exact hword.left_head hτ n (M.embedding s a)

include hword hτ in
omit [∀ s, Nonempty (I s)] in
/-- The unitary covariance is derived from the published algebraic extension
and the completed bounded-word identity. -/
theorem tracialMatrixUnitaryRepresentation_inclusion (s : ℕ)
    (u : Matrix.unitaryGroup (I s) ℂ) (n : ℕ) :
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (tracialMatrixWordAction (G.baseGeometry D).trace
          (G.baseGeometry D).vector (G.baseGeometry D).left (M.embedding s)
          (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
          (G.baseGeometry D).tracial
          (NestedTracialMatrices.denseRange_vector (G.baseGeometry D).trace
            (G.baseGeometry D).vector M) u n).toContinuousLinearMap) := by
  exact hword.matrix_extension_level (M.embedding s) u hgen hfaithful (hext s) hτ n

variable (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (G.tracialMatrixLeftRepresentation D M s a) =
    (G.tracialMatrixLeftRepresentation D M s a).comp Y)
  (hYU : ∀ s u, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext s u : H →L[ℂ] H).comp Y)

include S hsize hword hτ hYL hYU in
/-- Actual free-product symmetries force preservation of every word level. -/
theorem tracial_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) :=
  embedded_actions_word_levels_preserved (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n

include hword hτ hYL hYU in
/-- Every repeated-letter word transforms by the canonical bounded
multiplicity operator; its action is independent of the repeated letter. -/
theorem tracial_repeated_word (n : ℕ) (a : WordMultiplicity (G.baseVector A 1) n)
    (d : G.baseSpace D) (r : centeredSubspace (G.baseVector D 1)) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        (G.tracialWordRepeatedOperator A D M S hsize U Y n a)
        (endpointWord d (fun _ : Fin n => r))) :=
  embedded_actions_repeated_word (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n a d r

include hword hτ hYL hYU in
/-- The adjoint transforms by the adjoint of the same canonical coefficient. -/
theorem tracial_adjoint_repeated_word (n : ℕ) (a : WordMultiplicity (G.baseVector A 1) n)
    (d : G.baseSpace D) (r : centeredSubspace (G.baseVector D 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        ((G.tracialWordRepeatedOperator A D M S hsize U Y n).adjoint a)
        (endpointWord d (fun _ : Fin n => r))) :=
  embedded_actions_adjoint_repeated_word (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector M (G.baseGeometry D).tracial S hsize U
    (G.tracialMatrixLeftRepresentation D M)
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext)
    (G.tracialMatrixLeftRepresentation_inclusion A D M S hsize U hword hτ)
    (G.tracialMatrixUnitaryRepresentation_inclusion A D M hgen hfaithful hext U hword hτ)
    Y hYL hYU n a d r

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordBase
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The vacuum endpoint in degree zero is the actual base Hilbert space.
Consequently the repeated-word action implies base-space invariance; this
is not an additional assumption on the symmetrized operator. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.baseMultiplicityInnerFamily
variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hU : TracialWordFormula G A D U)

include hτ hU

/-- A degree-zero repeated action gives invariance of the actual base space. -/
theorem baseSpace_invariant_of_word_action (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ]
      WordMultiplicity (G.baseVector A 1) 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (T v)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) :
    ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A := by
  have hi := baseWordInclusion_intertwines (G.baseVector A 1) U (G.baseVector D 1)
    (G.norm_baseVector_one D hτ) Y T hY
  rw [G.tracial_baseWordInclusion_eq A D hτ U hU] at hi
  intro x hx
  have he := congrArg (fun f : G.baseSpace A →L[ℂ] H => f ⟨x, hx⟩) hi
  exact he.symm ▸ (zeroMultiplicityOperator (G.baseVector A 1) T ⟨x, hx⟩).property

/-- The same word action identifies its multiplicity-zero coefficient with
the actual compression used in the commutator estimate. -/
theorem baseOperator_of_word_action (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ]
      WordMultiplicity (G.baseVector A 1) 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (T v)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) :
    G.baseOperator A Y = zeroMultiplicityOperator (G.baseVector A 1) T :=
  baseOperator_eq_zeroMultiplicityOperator (G.baseVector D 1) (G.norm_baseVector_one D hτ)
    G A U Y T (G.tracial_baseWordInclusion_vector A D hτ U hU) hY

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHaarWordColumns
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_family _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixConjugationIsometry_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.freeMatrixExtensionUnitary_one _root_.OAI.KadisonSimilarity.TracialCornerGeometry.homIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_base _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_other _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionAutomorphism_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.matrixExtensionUnitaryRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.mem_l2ClosureAlgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.oppositeGeometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.positiveTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.rightRepresentation_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.coe_realTracialHilbertSequence _root_.OAI.KadisonSimilarity.completedTensorWordIsometry_apply _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralWordIsometry_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.embeddedMatrixStage_center _root_.OAI.KadisonSimilarity.embeddedMatrixStage_full _root_.OAI.KadisonSimilarity.endpointTensorIsometry_apply _root_.OAI.KadisonSimilarity.freeCreationIsometry_tensor _root_.OAI.KadisonSimilarity.freeHeadIsometry_tensor _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.globalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.gnsTracialGeometry_left _root_.OAI.KadisonSimilarity.gnsTracialGeometry_trace _root_.OAI.KadisonSimilarity.gnsTracialGeometry_vector _root_.OAI.KadisonSimilarity.hilbertTensorMapIsometry_insert _root_.OAI.KadisonSimilarity.invariantStarRepresentation_apply _root_.OAI.KadisonSimilarity.leadingIntoCentered_coe _root_.OAI.KadisonSimilarity.nonunitalRangeRepresentation_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.nonunitalRestrictionFiberEquiv_symm_coe _root_.OAI.KadisonSimilarity.projectionFiberAction_coe _root_.OAI.KadisonSimilarity.projectionFiberCompression_coe _root_.OAI.KadisonSimilarity.projectionFiberEquivOfEq_coe _root_.OAI.KadisonSimilarity.projectionFiberRepresentation_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_coe _root_.OAI.KadisonSimilarity.projectionFiberRetraction_inclusion _root_.OAI.KadisonSimilarity.restrictBoundedHom_apply _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.KadisonSimilarity.tracialWordInclusion_family _root_.OAI.KadisonSimilarity.unitizationRangeRepresentation_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_coe _root_.OAI.KadisonSimilarity.unitizationRestrictionFiberEquiv_symm_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Haar test columns used in propagation are actual reduced-word
inclusions. Their isometry and product formula follow from the word model
and the normalized corner Haar letters. -/

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.haarMultiplicityInnerFamily
variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
  {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

include hτ z ha htrace hhaar

/-- The published elementary creation maps and the ordinary product formula
give the manuscript's propagation estimate. The test word columns and their
prefix identities are constructed here. -/
theorem repeated_propagation_of_published_words
    (hU : TracialWordFormula G A D U)
    (creation : RicardXuCreationInput G A D)
    (hf : ScalarFree G.trace D A) (hfaithful : Function.Injective G.vector)
    (hdense : ReducedWordGenerated G A D)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (m : ℕ) (Y : H →L[ℂ] H)
    (hbase : ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (B : WordMultiplicity (G.baseVector A 1) (m + 1) →L[ℂ]
      WordMultiplicity (G.baseVector A 1) (m + 1))
    (hY : ∀ v d r, Y (U.inclusion (m + 1)
        (hilbertTensorInsert v (endpointWord d (fun _ : Fin (m + 1) => r)))) =
      U.inclusion (m + 1) (hilbertTensorInsert (B v)
        (endpointWord d (fun _ : Fin (m + 1) => r))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (comparison : FiniteFactorProjectionComparison τ)
    {N : ℕ} (hN : 0 < N) (frame : Fin N → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (v : G.baseSpace A) :
    ‖B (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1) v) -
      G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  obtain ⟨W⟩ := creation hτ hfaithful hf hdense
  let := W.head.vacuum_hasOrthogonalProjection (G.baseGeometry_trace_one D hτ)
  let C := W.tracialCreationFormulas s hs0 z ha htrace hhaar
  apply concrete_repeated_propagation G A D W.head s hs0 hsstar hssq z ha htrace hhaar C
    hf hτ m Y hbase hYD B
    (G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1))
    ?_ ?_ τ support e he heD hqe hfaithful comparison hN frame hframe hsum hε hcomm
    published commutation v
  · intro n w
    simpa only [haarRepeatedWordInclusion, repeatedWordInclusion_apply,
      LinearIsometry.id_apply] using
      hY (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1) w)
        (G.baseVector D 1) (G.baseHaarLetter D z ha htrace hhaar n)
  · exact G.haarRepeatedWordInclusion_factor A D hτ U z ha htrace hhaar hU
      s hs0 hsstar hssq m

/-- The degree-zero case is exact, and every positive degree follows from
the constructed Haar test columns. Base-space invariance is derived from
the same ordinary word action. -/
theorem all_degrees_propagation_of_published_words
    (hU : TracialWordFormula G A D U)
    (creation : RicardXuCreationInput G A D)
    (hf : ScalarFree G.trace D A) (hfaithful : Function.Injective G.vector)
    (hdense : ReducedWordGenerated G A D)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (Y : H →L[ℂ] H)
    (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
    (B : ∀ k, WordMultiplicity (G.baseVector A 1) k →L[ℂ]
      WordMultiplicity (G.baseVector A 1) k)
    (hY : ∀ k v d r, Y (U.inclusion k
        (hilbertTensorInsert v (endpointWord d (fun _ : Fin k => r)))) =
      U.inclusion k (hilbertTensorInsert (B k v) (endpointWord d (fun _ : Fin k => r))))
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e : P) (he : IsStarProjection e) (heD : e ∈ D) (hqe : τ (q : P) ≤ τ e)
    (comparison : FiniteFactorProjectionComparison τ)
    {N : ℕ} (hN : 0 < N) (frame : Fin N → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcomm : ∀ x : CStarCorner e he, ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e he))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (k : ℕ) (v : G.baseSpace A) :
    ‖B k (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v) -
      G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k
        (G.baseOperator A Y v)‖ ≤ 2 * cyclicConstant * ε * ‖v‖ := by
  have hzero : ∀ w, Y (U.inclusion 0 (hilbertTensorInsert w
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (B 0 w)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1))) := by
    intro w
    have hz : (fun _ : Fin 0 => (0 : centeredSubspace (G.baseVector D 1))) = Fin.elim0 :=
      Subsingleton.elim _ _
    simpa only [emptyEndpoint, hz] using hY 0 w (G.baseVector D 1) 0
  have hbase := G.baseSpace_invariant_of_word_action A D hτ U hU Y (B 0) hzero
  cases k with
  | zero =>
    have hb := G.baseOperator_of_word_action A D hτ U hU Y (B 0) hzero
    simp only [baseSymmetryRepeatedInclusion, repeatedMultiplicityInclusion_zero, hb,
      LinearIsometryEquiv.coe_toLinearIsometry, zeroMultiplicityOperator_intertwines,
      sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) cyclicConstant_pos.le) hε)
      (norm_nonneg v)
  | succ k =>
    exact G.repeated_propagation_of_published_words A D hτ U z ha htrace hhaar hU
      creation hf hfaithful hdense s hs0 hsstar hssq k Y hbase hYD (B (k + 1)) (hY (k + 1))
      τ support e he heD hqe comparison hN frame hframe hsum hε hcomm published commutation v

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialFreeCornerEstimate
attribute [-instance] _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedTestAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual tracial word model supplies both errors in the Fourier
compression argument. The only remaining Fourier hypotheses below concern
the spectral test operator itself; level preservation and propagation are
derived from the matrix symmetries and the cited published inputs. -/

noncomputable section
namespace KadisonSimilarity

universe u v

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

namespace TracialCornerGeometry

variable {P : Type u} {H : Type v} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
  (hext : ∀ j, G.MatrixConjugationExtensionInput D (M.embedding j) A)
  (S : RealTracialSequence (G.baseGeometry D).trace)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.freeCornerMultiplicityInnerFamily
variable (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hword : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
  (Y : H →L[ℂ] H)
  (hYD : ∀ x : D, Y.comp (G.left (x : P)) = (G.left (x : P)).comp Y)
  (hYU : ∀ j w, Y.comp
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
    (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp Y)

include S hsize hword hτ hYD hYU in
/-- Both the operator and its adjoint preserve the actual word levels.
Star closure supplies the second conclusion; it is not additional data. -/
theorem tracial_word_level_ranges :
    (∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) ∧
    (∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range) := by
  have hYL j a : Y.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y := hYD (M.embedding j a)
  have hYLstar j a : Y.adjoint.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y.adjoint :=
    G.adjoint_commutes_with_base D Y hYD (M.embedding j a)
  have hYUstar j w : Y.adjoint.comp
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H) =
      (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w : H →L[ℂ] H).comp
        Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    have hs :
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w :
          H →L[ℂ] H).adjoint =
        (G.tracialMatrixUnitaryRepresentation A D M hgen hfaithful hext j w⁻¹ :
          H →L[ℂ] H) := by
      rw [← ContinuousLinearMap.star_eq_adjoint, ← Unitary.coe_star,
        Unitary.star_eq_inv, map_inv]
    rw [hs]
    exact hYU j w⁻¹
  constructor
  · intro n x
    refine ⟨U.block Y n n x, ?_⟩
    exact (congrArg (fun T => T x)
      (G.tracial_word_levels_preserved A D M hgen hfaithful hext S hsize U hword hτ
        Y hYL hYU n)).symm
  · intro n x
    refine ⟨U.block Y.adjoint n n x, ?_⟩
    exact (congrArg (fun T => T x)
      (G.tracial_word_levels_preserved A D M hgen hfaithful hext S hsize U hword hτ
        Y.adjoint hYLstar hYUstar n)).symm

include S hsize hword hτ hYD hYU in
/-- The free-corner estimate with all word-structure and propagation
prerequisites derived. The published derivation inputs, the
elementary reduced creation model, and the standard support/comparison data
are explicit. The spectral test is used only through its norm and exact
finite Fourier compression. -/
theorem free_corner_estimate_of_published_words_oai
    (creation : RicardXuCreationInput G A D) (hf : ScalarFree G.trace D A)
    (hdense : ReducedWordGenerated G A D)
    {q : D} {hq : IsStarProjection q} (z : unitary (CStarCorner q hq))
    {a : ℝ} (ha : 0 < a) (htrace : G.trace (q : P) = (a : ℂ))
    (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)
    (τ : P → ℝ) (support : TracialRightSupportInput τ (q : P) A)
    (e₀ : P) (he₀ : IsStarProjection e₀) (he₀D : e₀ ∈ D)
    (hqe : τ (q : P) ≤ τ e₀) (comparison : FiniteFactorProjectionComparison τ)
    {N₀ : ℕ} (hN₀ : 0 < N₀) (frame : Fin N₀ → D)
    (hframe : ∀ i j, star (frame i : P) * (frame j : P) = if i = j then e₀ else 0)
    (hsum : ∑ i, (frame i : P) * star (frame i : P) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcorner : ∀ x : CStarCorner e₀ he₀,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖)
    (published : PublishedDerivationInputs.{u,v} (CStarCorner e₀ he₀))
    (commutation : TracialCommutationInput G.left (G.faithfulRightAction hfaithful))
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (T : H →L[ℂ] H) {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {b : ℝ} (hb : 0 < b) (hT : ‖T‖ ≤ 3 * b)
    (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (b : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * cyclicConstant) * ε := by
  let B := G.tracialWordRepeatedOperator A D M S hsize U Y
  have hYL j a : Y.comp (G.tracialMatrixLeftRepresentation D M j a) =
      (G.tracialMatrixLeftRepresentation D M j a).comp Y := hYD (M.embedding j a)
  have hY := G.tracial_repeated_word A D M hgen hfaithful hext S hsize U hword hτ
    Y hYL hYU
  have hYstar := G.tracial_adjoint_repeated_word A D M hgen hfaithful hext S hsize U hword hτ
    Y hYL hYU
  have hlevels := G.tracial_word_level_ranges A D M hgen hfaithful hext S hsize U hword hτ
    Y hYD hYU
  have hprop := G.all_degrees_propagation_of_published_words A D hτ U z ha htrace hhaar
    hword creation hf hfaithful hdense s hs0 hsstar hssq Y hYD B hY
    τ support e₀ he₀ he₀D hqe comparison hN₀ frame hframe hsum hε hcorner published commutation
  have hpropstar := G.all_degrees_propagation_of_published_words A D hτ U z ha htrace hhaar
    hword creation hf hfaithful hdense s hs0 hsstar hssq Y.adjoint
    (G.adjoint_commutes_with_base D Y hYD) (fun n => (B n).adjoint) hYstar
    τ support e₀ he₀ he₀D hqe comparison hN₀ frame hframe hsum hε
    (G.adjoint_corner_commutator_bound e₀ he₀ Y hcorner) published commutation
  apply G.commutator_bound_of_actual_dihedral_compression A D hτ hf d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte U hword Y T B hY hYstar hlevels.1 hlevels.2 hN toeplitz
    hb hε cyclicConstant_pos.le hT hcomm hprop
  · simpa only [G.baseOperator_adjoint] using hpropstar
  · exact hfourier

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words_oai.{u, v, u_1} := @OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words_oai.{u, v, u_1}
