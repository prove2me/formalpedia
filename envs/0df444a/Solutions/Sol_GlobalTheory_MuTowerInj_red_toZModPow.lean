-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.red_toZModPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:24.268423+00:00
-- url     : https://prove2.me/submissions/c8992e71-05ea-42b0-95c7-cf1334a7ac6d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable (l : ℕ) [Fact l.Prime] (n : ℕ)
namespace GlobalTheory.MuTowerInj
theorem _root_.solution (u : ℤ_[l]) :
    red l n (PadicInt.toZModPow (n + 1) u) = PadicInt.toZModPow n u := by
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) u
end GlobalTheory.MuTowerInj
