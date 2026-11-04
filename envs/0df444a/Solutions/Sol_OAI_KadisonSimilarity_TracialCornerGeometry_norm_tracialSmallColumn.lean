-- Prove2me | solution 1 for OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:27:04.677505+00:00
-- url     : https://prove2.me/submissions/b0dcf572-d992-4ff8-9339-3f340b7ab23b

import Mathlib
import Definitions.Def_OAIQ075A023
import Theorems.Thm_OAI_KadisonSimilarity_trace_centered_mul_of_free

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSmallColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2ClosureAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2FactorAlgebra_isClosed _root_.OAI.KadisonSimilarity.TracialCornerGeometry.l2GeneratedAlgebra_isClosed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small vectors in propagation are actual left compressions of the
completed base space. Scalar freeness gives their exact norm, first on
algebra vectors and then throughout the completion by density. -/

noncomputable section
namespace KadisonSimilarity

namespace ScalarFree

variable {P : Type*} [Ring P] [Algebra ℂ P] [StarRing P] [StarModule ℂ P]
  {τ : P →ₗ[ℂ] ℂ} {D A : StarSubalgebra ℂ P}

/-- Centered freeness gives the product trace formula for arbitrary letters
from the two algebras. -/
theorem trace_product (hf : ScalarFree τ D A) (hτ : τ 1 = 1)
    {x y : P} (hx : x ∈ D) (hy : y ∈ A) : τ (x * y) = τ x * τ y := by
  have h := trace_centered_mul_of_free τ hτ hf
    (traceCentered_mem τ D hx) (traceCentered_trace τ hτ x) hy
  simpa only [traceCentered, sub_mul, smul_mul_assoc, one_mul,
    map_sub, map_smul, smul_eq_mul, sub_eq_zero] using h

end ScalarFree

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The exact inner-product scaling on bounded base-algebra vectors follows
from the projection identity, traciality, and scalar freeness. -/
theorem tracialSmallColumn_inner_base (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D) (b c : A) :
    inner ℂ (G.tracialSmallColumn A q (G.baseVector A b))
      (G.tracialSmallColumn A q (G.baseVector A c)) =
        G.trace q * inner ℂ (G.baseVector A b) (G.baseVector A c) := by
  rw [G.tracialSmallColumn_vector, G.tracialSmallColumn_vector, G.inner_vector]
  have hprod : star (q * (b : P)) * (q * (c : P)) = star (b : P) * (q * (c : P)) := by
    rw [star_mul, hq.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc q q (c : P), hq.isIdempotentElem.eq]
  have hbstar : star (b : P) ∈ A := star_mem b.property
  have hcb : (c : P) * star (b : P) ∈ A := A.mul_mem c.property hbstar
  rw [hprod, G.tracial (star (b : P)) (q * (c : P)), mul_assoc,
    hf.trace_product hτ hqD hcb,
    G.tracial (c : P) (star (b : P)), G.baseVector_inner]

/-- The inner-product formula extends from bounded algebra vectors to the
entire completed base space. -/
theorem tracialSmallColumn_inner (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D) (v w : G.baseSpace A) :
    inner ℂ (G.tracialSmallColumn A q v) (G.tracialSmallColumn A q w) =
      G.trace q * inner ℂ v w := by
  refine (G.baseVector_dense A).induction_on v
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  exact (G.baseVector_dense A).induction_on w
    (isClosed_eq (by fun_prop) (by fun_prop))
    (G.tracialSmallColumn_inner_base A D hf hτ q hq hqD b)

/-- The small vectors have the exact square-root trace scaling. This is a
consequence of freeness and density, not an additional word-model field. -/
theorem norm_tracialSmallColumn_oai (D : StarSubalgebra ℂ P)
    (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
    (q : P) (hq : IsStarProjection q) (hqD : q ∈ D)
    {a : ℝ} (ha : 0 ≤ a) (htrace : G.trace q = (a : ℂ)) (v : G.baseSpace A) :
    ‖G.tracialSmallColumn A q v‖ = Real.sqrt a * ‖v‖ := by
  have hsq : ‖G.tracialSmallColumn A q v‖ ^ 2 = a * ‖v‖ ^ 2 := by
    calc
      _ = Complex.re (inner ℂ (G.tracialSmallColumn A q v)
          (G.tracialSmallColumn A q v)) := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = a * Complex.re (inner ℂ v v) := by
        rw [G.tracialSmallColumn_inner A D hf hτ q hq hqD, htrace]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
        rfl
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg v))).mp
  rw [mul_pow, Real.sq_sqrt ha]
  exact hsq

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn_oai.{u_1, u_2} := @OAI.KadisonSimilarity.TracialCornerGeometry.norm_tracialSmallColumn_oai.{u_1, u_2}
