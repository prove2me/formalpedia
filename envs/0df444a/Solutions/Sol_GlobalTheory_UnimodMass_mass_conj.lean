-- Prove2me | solution 1 for GlobalTheory.UnimodMass.mass_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:40:51.417806+00:00
-- url     : https://prove2.me/submissions/dcab94a9-c227-4994-9b7f-cc098e8ee898

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_out
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_conj

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
theorem _root_.solution (Γ K : Subgroup G) (h : G) :
    mass Γ (K.map (MulAut.conj h).toMonoidHom) = mass Γ K := by
  unfold mass
  rw [← finsum_comp_equiv (dcConj Γ K h)]
  refine finsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h x =>
    have e1 : dcConj Γ K h (Quotient.mk _ x) = Quotient.mk (dcSetoid Γ K) (x * h) := rfl
    rw [e1, stabCard_out, stabCard_out, stabCard_conj]
end GlobalTheory.UnimodMass
