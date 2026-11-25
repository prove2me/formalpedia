-- Prove2me | solution 1 for GlobalTheory.LocDualInt.smul_mem_powSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:03:40.347074+00:00
-- url     : https://prove2.me/submissions/48f5e464-d2b6-4882-a144-2defa96706f1

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
variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]
namespace GlobalTheory.LocDualInt
theorem _root_.solution (a : O) (n : ℕ) (y : M) : a ^ n • y ∈ powSub (M := M) a n :=
  mem_powSub.2 ⟨y, rfl⟩
end GlobalTheory.LocDualInt
