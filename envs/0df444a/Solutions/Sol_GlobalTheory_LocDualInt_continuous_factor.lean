-- Prove2me | solution 1 for GlobalTheory.LocDualInt.continuous_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:51.909801+00:00
-- url     : https://prove2.me/submissions/466dfb99-ea0b-4291-b7b3-dca1b8aa5da4

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)
noncomputable section
open GlobalTheory GlobalTheory.LocDualInt
variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul O M]
namespace GlobalTheory.LocDualInt
theorem _root_.solution (a : O) {m n : ℕ} (h : m ≤ n) :
    Continuous (Submodule.factor (powSub_anti (M := M) a h)) := by
  rw [(Submodule.isOpenQuotientMap_mkQ _).isQuotientMap.continuous_iff]
  exact continuous_quot_mk
end GlobalTheory.LocDualInt
