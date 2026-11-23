-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.iota_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:40.807614+00:00
-- url     : https://prove2.me/submissions/72fdaa35-7586-44d8-92b7-97bc0da284ae

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift
import Theorems.Thm_GlobalTheory_MuTowerInj_iota_apply

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
theorem _root_.solution (x : ℕ) : iota l n x = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
  rw [iota_apply, pow_mul_val]
end GlobalTheory.MuTowerInj
