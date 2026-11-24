-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.iota_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:42.268796+00:00
-- url     : https://prove2.me/submissions/298a3909-3200-4bf2-b012-ef975fa2f2e0

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_natCast

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
theorem _root_.solution (u : ℤ_[l]) (b : ZMod (l ^ 1)) :
    iota l n (PadicInt.toZModPow 1 u * b) = PadicInt.toZModPow (n + 1) u * iota l n b := by
  obtain ⟨y, rfl⟩ := ZMod.natCast_zmod_surjective b
  set w := PadicInt.toZModPow (n + 1) u with hw

  have h1 : PadicInt.toZModPow 1 u = ((w.val : ℕ) : ZMod (l ^ 1)) := by
    rw [← PadicInt.zmod_cast_comp_toZModPow 1 (n + 1) (by omega), RingHom.comp_apply,
      ZMod.castHom_apply, ZMod.cast_eq_val]
  have h2 : ((w.val : ℕ) : ZMod (l ^ (n + 1))) = w := ZMod.natCast_zmod_val w
  rw [h1, ← Nat.cast_mul, iota_natCast, iota_natCast]
  conv_rhs => rw [← h2]
  push_cast
  ring
end GlobalTheory.MuTowerInj
