-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:31:36.457194+00:00
-- url     : https://prove2.me/submissions/3aaa606a-a3b9-41f6-bab6-a7af4c29ea68

import Mathlib
import Definitions.Def_OAIQ075A029

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialHaarWordColumns
attribute [-instance] _root_.OAI.KadisonSimilarity.CStarCorner.isClosed_subalgebra _root_.OAI.KadisonSimilarity.TracialCornerGeometry.generatedDihedralAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
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

/-- On bounded base vectors this column is precisely the ordinary repeated
product, with no independently assumed prefix formula. -/
theorem haarRepeatedWordInclusion_baseVector
    (hU : TracialWordFormula G A D U)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (k n : ℕ) (b : A) :
    G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar k n
      (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b)) =
      G.vector (((s : P) * (haarCornerLetter z a n : D)) ^ k * (b : P)) := by
  have hx0 : G.trace (haarCornerLetter z a n : D) = 0 :=
    haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htrace hhaar n
  simpa only [haarRepeatedWordInclusion, repeatedWordInclusion_apply,
    LinearIsometry.id_apply, baseSymmetryRepeatedInclusion,
    repeatedMultiplicityInclusion_apply, tracialWordTensor, tracialMultiplicityWord,
    tracialEndpointWord, baseHaarLetter, baseSymmetryLetter,
    OneMemClass.coe_one, one_mul] using
      hU.repeated_word_formula k (1 : D) (haarCornerLetter z a n) s b hs0 hx0

/-- The final Haar letter is supported on q, so the product formula is the
exact small-column factorization consumed by propagation. -/
theorem haarRepeatedWordInclusion_factor_oai
    (hU : TracialWordFormula G A D U)
    (s : A) (hs0 : G.trace (s : P) = 0) (hsstar : star s = s) (hssq : s * s = 1)
    (m n : ℕ) (b : A) :
    G.haarRepeatedWordInclusion A D hτ U z ha htrace hhaar (m + 1) n
      (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ (m + 1)
        (G.baseVector A b)) =
      G.left (tracialWordPrefix (ι := D.subtype) z a (s : P) m n)
        (G.left ((haarCornerLetter z a n : D) : P)
          (G.vector ((q : P) * (b : P)))) := by
  rw [G.haarRepeatedWordInclusion_baseVector A D hτ U z ha htrace hhaar hU,
    G.left_vector, G.left_vector]
  have hxq : ((haarCornerLetter z a n : D) : P) * (q : P) =
      ((haarCornerLetter z a n : D) : P) :=
    congrArg (fun x : D => (x : P)) (haarCornerLetter_mul_support z a n)
  congr 1
  simp only [tracialWordPrefix, StarSubalgebra.subtype_apply, pow_succ, mul_assoc]
  rw [← mul_assoc ((haarCornerLetter z a n : D) : P) (q : P), hxq]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor_oai.{u, v} := @OAI.KadisonSimilarity.TracialCornerGeometry.haarRepeatedWordInclusion_factor_oai.{u, v}
