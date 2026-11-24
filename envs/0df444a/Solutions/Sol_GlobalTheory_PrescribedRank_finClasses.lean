-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.finClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:25.16075+00:00
-- url     : https://prove2.me/submissions/2e97f69e-81d7-4ea9-9276-153cda4b103c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_GlobalTheory_PrescribedRank_tup_eq
import Theorems.Thm_GlobalTheory_PrescribedRank_isLatTup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution : (trivLevel p O Kf).FinClasses :=
  ⟨{fun v => isEmptyElim v}, fun L _ => isLatTup p O Kf L, fun L _ =>
    ⟨_, Finset.mem_singleton_self _, (1 : (trivLevel p O Kf).Γ), tup_eq p O Kf _ _⟩⟩
end GlobalTheory.PrescribedRank
