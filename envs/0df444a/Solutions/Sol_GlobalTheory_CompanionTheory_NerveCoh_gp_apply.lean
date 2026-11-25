-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.NerveCoh.gp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:54:34.216108+00:00
-- url     : https://prove2.me/submissions/16e44a6b-72a5-4bed-9140-bb4818a2264e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic

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
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.NerveCoh
theorem _root_.solution (F : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : MCn F m)
    (c : Fin (n + 1) ⥤ C) : gp F θ f c =
      F.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) := rfl
end GlobalTheory.CompanionTheory.NerveCoh
