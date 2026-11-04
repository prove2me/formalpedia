-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:25:35.316483+00:00
-- url     : https://prove2.me/submissions/2d9b661e-792a-4e48-9c62-c9d86d91354c

import Mathlib
import Definitions.Def_OAIQ075A024

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reduced-word part of the published free-product construction.

Ricard–Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2–3 of
arXiv:math/0505302, constructs the reduced free-product Hilbert space as the
orthogonal sum of alternating centered tensor words. Regrouping the first
and last factors gives the coordinates below. The input is only this word
construction, without any operator invariance or commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem alternatingProduct_constant (a b : P) (n : ℕ) :
    alternatingProduct (fun _ : Fin n => a) (fun _ => b) = (a * b) ^ n := by
  simp [alternatingProduct, List.ofFn_const]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

namespace TracialWordFormula

variable {G A D}
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}
  (hU : TracialWordFormula G A D U)

include hU

/-- Constant centered letters recover the exact repeated-word formula. -/
theorem repeated_word_formula (n : ℕ) (d₀ d : D) (a b : A)
    (ha : G.trace (a : P) = 0) (hd : G.trace (d : P) = 0) :
    U.inclusion n (tracialWordTensor G A D n d₀ b
      (fun _ => a) (fun _ => d) (fun _ => ha) (fun _ => hd)) =
      G.vector ((d₀ : P) * ((a : P) * (d : P)) ^ n * (b : P)) := by
  simpa only [alternatingProduct_constant] using
    hU n d₀ b (fun _ => a) (fun _ => d) (fun _ => ha) (fun _ => hd)

end TracialWordFormula
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct



section TensorScaling
variable {J E F H : Type*}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Endpoint normalization commutes with every continuous word inclusion. -/
theorem include_scaled_endpoint {n : ℕ}
    (L : HilbertTensor J (EndpointTensor E F n) →L[ℂ] H)
    (v : J) (e : E) (x : Fin n → F) (c : ℂ) :
    L (hilbertTensorInsert v (endpointWord (c • e) x)) =
      c • L (hilbertTensorInsert v (endpointWord e x)) := by
  rw [endpointWord_smul_endpoint, map_smul, map_smul]

end TensorScaling

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized dihedral columns agree with the repeated tensor
words on the dense bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityNormedFamily
attribute [local instance] OAI.KadisonSimilarity.TracialCornerGeometry.dihedralMultiplicityInnerFamily
variable
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)

/-- A constant-letter word has exactly the tensor coordinates of the
repeated base insertion and the unnormalized endpoint. -/
theorem repeated_dihedral_word_formula (hU : TracialWordFormula G A D U)
    (k : ℕ) (b : A) :
    U.inclusion k
      (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b))
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) =
      G.vector ((e : P) * ((s : P) * (d : P)) ^ k * (b : P)) := by
  exact hU.repeated_word_formula k e d s b hs0 hd0

attribute [local irreducible] tracialDihedralInclusion

/-- The two column realizations agree on all bounded algebra vectors. -/
theorem actual_dihedral_column_baseVector (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (b : A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k (G.baseVector A b) =
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b))
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) := by
  exact (G.tracialDihedralInclusion_apply D A hf hτ d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte k b).trans
      (congrArg (fun x : H => dihedralNormalization t • x)
        (G.repeated_dihedral_word_formula D A hτ d s e hd0 hsstar hssq hs0 U hU k b)).symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralColumnIdentification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the normalized actual dihedral columns with completed word maps. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

variable
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)

attribute [local irreducible] tracialDihedralInclusion

/-- On every completed base vector, the actual normalized dihedral column
is the normalized repeated word supplied by the reduced-word model. -/
theorem actual_dihedral_column_apply (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k v =
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v)
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) := by
  have hword : Continuous (fun x : G.baseSpace A =>
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k x)
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0)))) := by
    change Continuous (fun x : G.baseSpace A =>
      dihedralNormalization t • U.inclusion k
        (hilbertTensorRightInsert
          (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))
          (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k x)))
    exact continuous_const.smul ((U.inclusion k).continuous.comp
      ((hilbertTensorRightInsert
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))).continuous.comp
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k).continuous))
  refine (G.baseVector_dense A).induction_on v
    (isClosed_eq
      (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte k).continuous hword) ?_
  intro b
  exact G.actual_dihedral_column_baseVector D A hτ d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte U hf hU k b

/-- The Fourier columns are exactly the normalized repeated-letter columns
used by propagation, with normalization derived from the projection trace. -/
theorem actual_dihedral_column_eq_repeated_oai (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k v =
    G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte U k v := by
  rw [G.actual_dihedral_column_apply D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
    he ht hte U hf hU k v]
  symm
  simp only [repeatedDihedralInclusion, repeatedWordInclusion_apply, projectionEndpoint]
  exact include_scaled_endpoint (U.inclusion k).toContinuousLinearMap
    (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v)
    (G.baseVector D e) (fun _ : Fin k => G.baseSymmetryLetter D d hd0)
    (dihedralNormalization t)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.actual_dihedral_column_eq_repeated_oai.{u_1, u_2}
