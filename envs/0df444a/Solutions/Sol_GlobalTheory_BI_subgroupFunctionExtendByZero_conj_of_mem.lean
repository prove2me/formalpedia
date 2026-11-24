-- Prove2me | solution 1 for GlobalTheory.BI.subgroupFunctionExtendByZero_conj_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:24.435871+00:00
-- url     : https://prove2.me/submissions/d4da0ff3-9374-4757-985b-62e86307fa5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InducedClassFunctionFromSubgroupEqFinsumCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by
  unfold ext0
  by_cases ha : a ∈ H
  · have h1 : (y : G)⁻¹ * a * y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2
    rw [dif_pos ha, dif_pos h1]
    exact hψ ⟨a, ha⟩ y
  · have h1 : ¬ (y : G)⁻¹ * a * y ∈ H := by
      intro h
      apply ha
      have h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)
      have h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a := by group
      rwa [h3] at h2
    rw [dif_neg ha, dif_neg h1]
end GlobalTheory.BI
