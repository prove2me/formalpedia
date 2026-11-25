-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeCx.act_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:34:26.491985+00:00
-- url     : https://prove2.me/submissions/f9f49b6a-508f-466c-b0d9-813067ec0dca

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DnCompDn

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
open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeCx
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
variable (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.HodgeCx
theorem _root_.solution {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : Cn F m) (c : Fin (n + 1) ⥤ C) :
    act F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) :=
  rfl
end GlobalTheory.CompanionTheory.HodgeCx
