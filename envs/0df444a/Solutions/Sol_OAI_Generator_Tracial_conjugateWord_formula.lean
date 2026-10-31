-- Prove2me | solution 1 for OAI.Generator.Tracial.conjugateWord_formula
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:28:56.719617+00:00
-- url     : https://prove2.me/submissions/993a81ce-d207-4036-bae1-095da8183d39

import Mathlib
import Definitions.Def_OAIQ11Fg022
import Definitions.Def_OAIQ11Fg023

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeGroupMoments
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Every nonempty reduced word in successive Haar variables has zero trace.
The induction eliminates the largest label, retaining centered lower-label gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem unitaryWord_nil {A : Type*} (v : A → unitary (Q τ ω)) :
    unitaryWord τ ω v []=1 := rfl

theorem unitaryWord_cons {A : Type*} (v : A → unitary (Q τ ω))
    (x : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω v (x::w)=algebraSignedLetter (v x.1 : Q τ ω) (!x.2)*unitaryWord τ ω v w := rfl

end

/-! The actual free-group representation furnished by successive Haar variables. -/

/-! Reduced-word moments for p*y*(star p). Distinct labels have centered ratios;
reducedness requires distinct labels precisely at opposite-sign gaps. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {A : Type*}

theorem signed_conjugate (p y : unitary (Q τ ω)) (s : Bool) :
    algebraSignedLetter (↑(p*y*(star p)) : Q τ ω) s=
      (p : Q τ ω)*algebraSignedLetter (y : Q τ ω) s*↑(star p) := by
  cases s with
  | false => rfl
  | true =>
    change star ((p : Q τ ω)*(y : Q τ ω)*star (p : Q τ ω))=
      (p : Q τ ω)*star (y : Q τ ω)*star (p : Q τ ω)
    rw [star_mul,star_mul,star_star,mul_assoc]

theorem conjugateWord_formula_oai (p : A → unitary (Q τ ω)) (y : unitary (Q τ ω))
    (a : A × Bool) (w : List (A × Bool)) :
    unitaryWord τ ω (conjugateVariables τ ω p y) (a::w)=
      (p a.1 : Q τ ω)*betweenWord (y : Q τ ω) (!a.2)
        (conjugateGaps τ ω p a w) (conjugateEnd τ ω p a w) := by
  induction w generalizing a with
  | nil =>
    rw [unitaryWord_cons,unitaryWord_nil,mul_one]
    change algebraSignedLetter (↑(p a.1*y*star (p a.1)) : Q τ ω) (!a.2)=_
    rw [signed_conjugate]
    exact mul_assoc _ _ _
  | cons b w ih =>
    rw [unitaryWord_cons,ih]
    change algebraSignedLetter (↑(p a.1*y*star (p a.1)) : Q τ ω) (!a.2)*_= _
    rw [signed_conjugate]
    simp only [conjugateGaps,conjugateEnd,betweenWord,Submonoid.coe_mul,mul_assoc]

end

/-! Positive and negative conjugate terms in first-order correlation. Same-sign gaps require no centering hypothesis. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Generator.Tracial.conjugateWord_formula_oai.{u_1, u_2} := @OAI.Generator.Tracial.conjugateWord_formula_oai.{u_1, u_2}
