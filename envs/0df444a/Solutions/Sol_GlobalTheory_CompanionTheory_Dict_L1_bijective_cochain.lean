-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.L1_bijective_cochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:26:57.716211+00:00
-- url     : https://prove2.me/submissions/2615f48e-ab6c-4e8a-b1f2-be749d34cfe3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero

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
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.Dict
theorem _root_.solution : Function.Bijective (L1 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj (Fin.last 1))
    (c.map (homOfLE (Fin.zero_le _))), rfl⟩⟩
  obtain ⟨X₀, X₁, φ, rfl⟩ := ComposableArrows.mk₁_surjective c
  exact congr_fun (congr_fun (congr_fun h X₀) X₁) φ
end GlobalTheory.CompanionTheory.Dict
