-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.iota_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:46.957807+00:00
-- url     : https://prove2.me/submissions/5d576082-09c2-483a-aebd-3701008332e9

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
theorem _root_.solution (b : ZMod (l ^ 1)) :
    iota l n b = ((l ^ n * b.val : ℕ) : ZMod (l ^ (n + 1))) := rfl
end GlobalTheory.MuTowerInj
