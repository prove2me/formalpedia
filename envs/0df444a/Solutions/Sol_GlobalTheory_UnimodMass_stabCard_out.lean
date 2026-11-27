-- Prove2me | solution 1 for GlobalTheory.UnimodMass.stabCard_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:39:14.919554+00:00
-- url     : https://prove2.me/submissions/25d2239c-d87d-4a98-af5b-25a18f76de5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
namespace GlobalTheory.UnimodMass
theorem _root_.solution (Γ K : Subgroup G) (x : G) :
    stabCard Γ K (Quotient.mk (dcSetoid Γ K) x).out = stabCard Γ K x :=
  (stabCard_eq (Quotient.mk_out (s := dcSetoid Γ K) x)).symm
end GlobalTheory.UnimodMass
