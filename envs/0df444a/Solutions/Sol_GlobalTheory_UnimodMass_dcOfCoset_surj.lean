-- Prove2me | solution 1 for GlobalTheory.UnimodMass.dcOfCoset_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:38:50.400095+00:00
-- url     : https://prove2.me/submissions/0f06851e-9ec6-4b8b-ae67-aeff6a0d6cb0

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
    (d : DC Γ W) (hd : dcMapLe hWK d = Quotient.mk (dcSetoid Γ K) t) :
    ∃ k : K, d = dcOfCoset Γ W K t (k : K ⧸ W.subgroupOf K) := by
  induction d using Quotient.inductionOn with
  | h g =>
    have h2 : (dcSetoid Γ K) g t := Quotient.exact hd
    obtain ⟨γ, hγ, κ, hκ, e⟩ := (dcSetoid Γ K).iseqv.symm h2
    refine ⟨⟨κ, hκ⟩, ?_⟩
    rw [dcOfCoset_mk]
    apply Quotient.sound
    refine ⟨γ⁻¹, Γ.inv_mem hγ, 1, W.one_mem, ?_⟩
    simp [e, mul_assoc]
end GlobalTheory.UnimodMass
