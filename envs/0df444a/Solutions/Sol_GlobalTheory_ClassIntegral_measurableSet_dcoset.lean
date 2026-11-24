-- Prove2me | solution 1 for GlobalTheory.ClassIntegral.measurableSet_dcoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:44.181687+00:00
-- url     : https://prove2.me/submissions/6189c3ae-ace3-4abe-8ef7-23f48e119b9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralFundamentalDomainEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.ClassIntegral
variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace GlobalTheory.ClassIntegral
theorem _root_.solution (Γ K : Subgroup G) [Countable Γ] (hK : MeasurableSet (K : Set G)) (g : G) :
    MeasurableSet (dcoset Γ K g) := by
  have : dcoset Γ K g = ⋃ γ : Γ, (fun y => ((γ : G) * g)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext x
    simp only [dcoset, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, by simpa [mul_assoc] using hk⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ, γ.2, _, h, by group⟩
  rw [this]
  exact MeasurableSet.iUnion fun γ => (measurable_const_mul _) hK
end GlobalTheory.ClassIntegral
