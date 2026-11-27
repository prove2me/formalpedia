-- Prove2me | solution 1 for GlobalTheory.UnimodMass.stabCard_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:31:06.310548+00:00
-- url     : https://prove2.me/submissions/09eb6c53-c50e-46c1-ab83-ffa037eee0d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover

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
theorem _root_.solution (Γ K : Subgroup G) (h g : G) :
    stabCard Γ (K.map (MulAut.conj h).toMonoidHom) g = stabCard Γ K (g * h) := by
  unfold stabCard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]
end GlobalTheory.UnimodMass
