-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.iota_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:41.515969+00:00
-- url     : https://prove2.me/submissions/6e681240-5f70-4cff-8e74-776c6c6398e0

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable (l : ℕ) [Fact l.Prime] (n : ℕ)
namespace GlobalTheory.MuTowerInj
theorem _root_.solution : Function.Injective (iota l n) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [iota_apply, CharP.cast_eq_zero_iff (ZMod (l ^ (n + 1))) (l ^ (n + 1)), pow_succ,
    Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : l.Prime).pos n)] at hb
  have hlt : b.val < l := by simpa using ZMod.val_lt b
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hb hlt
end GlobalTheory.MuTowerInj
