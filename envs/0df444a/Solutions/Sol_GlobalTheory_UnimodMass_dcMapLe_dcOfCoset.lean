-- Prove2me | solution 1 for GlobalTheory.UnimodMass.dcMapLe_dcOfCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:38:46.028864+00:00
-- url     : https://prove2.me/submissions/6aef6be6-73ab-46c2-a39d-970db11f1571

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DoubleCosetMassEqRelIndexMulMass
import Theorems.Thm_GlobalTheory_UnimodMass_dcOfCoset_mk

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
open scoped BigOperators
namespace GlobalTheory.UnimodMass
theorem _root_.solution {G : Type} [Group G] {Γ W K : Subgroup G} (hWK : W ≤ K) (t : G)
    (x : K ⧸ W.subgroupOf K) : dcMapLe hWK (dcOfCoset Γ W K t x) = Quotient.mk (dcSetoid Γ K) t := by
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [dcOfCoset_mk]
    apply Quotient.sound
    exact ⟨1, Γ.one_mem, (k : G)⁻¹, K.inv_mem k.2, by simp⟩
end GlobalTheory.UnimodMass
