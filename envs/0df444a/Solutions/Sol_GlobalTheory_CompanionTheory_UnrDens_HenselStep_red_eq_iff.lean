-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.red_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:32.423498+00:00
-- url     : https://prove2.me/submissions/23273849-3492-45f2-863d-39676f9a7e53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
variable {R : Type} [CommRing R] {a b c : ℕ}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution (ϖ : R) (k : ℕ) (M N : Matrix (Fin a) (Fin b) R) :
    red ϖ k M = red ϖ k N ↔ ∃ D : Matrix (Fin a) (Fin b) R, M = N + ϖ ^ k • D := by
  constructor
  · intro h
    have h1 : ∀ i j, ∃ d, M i j = N i j + ϖ ^ k * d := by
      intro i j
      have h2 : Ideal.Quotient.mk (lev ϖ k) (M i j) = Ideal.Quotient.mk (lev ϖ k) (N i j) :=
        congrFun (congrFun h i) j
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
      exact ⟨d, by linear_combination -hd⟩
    choose D hD using h1
    exact ⟨Matrix.of D, by ext i j; simp [hD i j]⟩
  · rintro ⟨D, rfl⟩
    ext i j
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨D i j, ?_⟩)
    simp [mul_comm]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
