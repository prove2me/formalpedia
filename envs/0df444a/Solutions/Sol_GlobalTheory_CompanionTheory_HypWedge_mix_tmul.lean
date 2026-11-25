-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.mix_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:58:55.311085+00:00
-- url     : https://prove2.me/submissions/d4d3cef0-349a-4c90-a759-42a6d23be1d3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (σ : V →ₗ[R] M) (k : W →ₗ[R] M) (v : V) (w : W) :
    mix σ k (v ⊗ₜ w) = wB R M (σ v) (k w) := rfl
end GlobalTheory.CompanionTheory.HypWedge
