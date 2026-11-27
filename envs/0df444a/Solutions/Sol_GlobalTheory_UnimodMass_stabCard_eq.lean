-- Prove2me | solution 1 for GlobalTheory.UnimodMass.stabCard_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:18.712324+00:00
-- url     : https://prove2.me/submissions/420d051f-5679-4898-a469-6d5b295d2470

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
theorem _root_.solution {Γ K : Subgroup G} {t t' : G} (hr : (dcSetoid Γ K) t t') :
    stabCard Γ K t' = stabCard Γ K t := by
  obtain ⟨γ, hγ, κ, hκ, rfl⟩ := hr
  unfold stabCard
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨γ⁻¹ * (x.1 : G) * γ, Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) x.1.2) hγ⟩, ?_⟩
      invFun := fun x => ⟨⟨γ * (x.1 : G) * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ x.1.2) (Γ.inv_mem hγ)⟩, ?_⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc] }
  · have := K.mul_mem (K.mul_mem hκ x.2) (K.inv_mem hκ)
    convert this using 1
    simp [mul_assoc]
  · have := K.mul_mem (K.mul_mem (K.inv_mem hκ) x.2) hκ
    convert this using 1
    simp [mul_assoc]
end GlobalTheory.UnimodMass
