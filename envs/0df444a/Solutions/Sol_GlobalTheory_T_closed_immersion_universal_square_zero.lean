-- Prove2me | solution 1 for GlobalTheory.T.closed_immersion_universal_square_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:15.847152+00:00
-- url     : https://prove2.me/submissions/7a362db9-edc1-4c25-a7c9-7c0e5308657f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZero
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedImmersionUniversalSquareZeroStatement
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLift_isCot_of_lifting


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  first | exact @GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting | exact GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting | (intros; apply GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting <;> assumption)
end _root_.GlobalTheory.T
