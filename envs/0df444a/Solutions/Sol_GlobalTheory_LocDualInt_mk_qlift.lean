-- Prove2me | solution 1 for GlobalTheory.LocDualInt.mk_qlift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:07.130555+00:00
-- url     : https://prove2.me/submissions/1740ca5b-6959-4767-ba09-6e5f7d71c01a

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
theorem _root_.solution {N : Submodule O M} (z : M ⧸ N) : Submodule.Quotient.mk (qlift z) = z :=
  (Submodule.Quotient.mk_surjective N z).choose_spec
end GlobalTheory.LocDualInt
