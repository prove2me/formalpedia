-- Prove2me | solution 1 for GlobalTheory.FlatDescent.existsUnique_appTop_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:48.940802+00:00
-- url     : https://prove2.me/submissions/b970a3b5-033b-4391-9904-81101ffca0c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_injective_appTop_of_epi
import Theorems.Thm_GlobalTheory_FlatDescent_exists_appTop_eq_of_effectiveEpi
import Theorems.Thm_GlobalTheory_FlatDescent_appTop_appTop_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}
namespace GlobalTheory.FlatDescent
theorem _root_.solution (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) :
    (∃! a : Γ(X, ⊤), p.appTop a = s) ↔ f.appTop s = g.appTop s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact appTop_appTop_eq h.w a
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s hs
    exact ⟨a, ha, fun b hb => injective_appTop_of_epi p (hb.trans ha.symm)⟩
end GlobalTheory.FlatDescent
