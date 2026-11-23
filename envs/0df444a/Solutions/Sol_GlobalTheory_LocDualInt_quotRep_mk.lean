-- Prove2me | solution 1 for GlobalTheory.LocDualInt.quotRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:30.91384+00:00
-- url     : https://prove2.me/submissions/2241bb8c-1add-4db3-a22f-caf001da8d60

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
theorem _root_.solution (ρ : Representation O G M) (a : O) (n : ℕ) (g : G) (x : M) :
    quotRep ρ a n g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := rfl
end GlobalTheory.LocDualInt
