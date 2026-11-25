-- Prove2me | solution 1 for GlobalTheory.T.cotangent_local_open_chart_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:22.280808+00:00
-- url     : https://prove2.me/submissions/9fec7066-3da8-48ea-a4d2-be5379f14368

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_cotangent_away


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∀ (W : Type) [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ → ∀ (r : R) (A C : Type) [CommRing A] [CommRing C] [Algebra C A] [Algebra A (Localization.Away r)] (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R) [IsOpenImmersion j] [Mono k], j ≫ s = spMap (algebraMap C A) ≫ k → spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e → Nonempty ((Localization.Away r ⊗[R] W) ≃ₗ[Localization.Away r] (Localization.Away r ⊗[A] KaehlerDifferential C A)) := by
  first | exact @GlobalTheory.CompanionTheory.CotLoc.cotangent_away | exact GlobalTheory.CompanionTheory.CotLoc.cotangent_away | (intros; apply GlobalTheory.CompanionTheory.CotLoc.cotangent_away <;> assumption)
end _root_.GlobalTheory.T
