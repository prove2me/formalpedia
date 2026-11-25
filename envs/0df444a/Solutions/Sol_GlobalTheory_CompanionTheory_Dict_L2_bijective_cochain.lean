-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.L2_bijective_cochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:26:59.676426+00:00
-- url     : https://prove2.me/submissions/ca8e9c2a-9ffd-438a-a272-a169bcd029b4

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
theorem _root_.solution : Function.Bijective (L2 F) := by
  refine ⟨fun f g h => funext fun c => ?_, fun e => ⟨fun c => e (c.obj 0) (c.obj 1) (c.obj (Fin.last 2))
    (c.map (homOfLE (show (0 : Fin 3) ≤ 1 by decide)))
    (c.map (homOfLE (show (1 : Fin 3) ≤ Fin.last 2 by decide))), rfl⟩⟩
  obtain ⟨X₀, X₁, X₂, φ, ψ, rfl⟩ := ComposableArrows.mk₂_surjective c
  exact congr_fun (congr_fun (congr_fun (congr_fun (congr_fun h X₀) X₁) X₂) φ) ψ
end GlobalTheory.CompanionTheory.Dict
