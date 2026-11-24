-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.exists_iota_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:39.701581+00:00
-- url     : https://prove2.me/submissions/3aeddcd1-a975-460b-8de7-a9fd3fd622eb

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
theorem _root_.solution (m : ZMod (l ^ (n + 1))) (hm : red l n m = 0) :
    ∃ k, iota l n k = m := by
  have h0 : ((m.val : ℕ) : ZMod (l ^ n)) = 0 := by
    rw [← ZMod.cast_eq_val]
    exact hm
  rw [CharP.cast_eq_zero_iff (ZMod (l ^ n)) (l ^ n)] at h0
  obtain ⟨t, ht⟩ := h0
  exact ⟨t, by rw [iota_natCast, ← ht, ZMod.natCast_zmod_val]⟩
end GlobalTheory.MuTowerInj
