-- Prove2me | solution 1 for GroundTheory.LocalField.sum_conj_eq_card_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:03.581801+00:00
-- url     : https://prove2.me/submissions/d22eedbc-4391-43cb-82ec-3b18e4187bed

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit [Fintype G] hp
namespace GroundTheory.LocalField
theorem _root_.solution [Fintype G] {g : G} (hc : IsConj x g) :
    (∑ t : G, if t⁻¹ * g * t = x then (1 : ℂ) else 0) = Nat.card (Subgroup.centralizer {x}) := by
  obtain ⟨u, hu⟩ := isConj_iff.mp hc
  rw [← hu]
  rw [Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ (fun t ↦ if t ∈ Subgroup.centralizer {x} then (1 : ℂ) else 0)
    (fun t ↦ ?_)]
  · rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · simp only [Equiv.coe_mulLeft, Subgroup.mem_centralizer_singleton_iff]
    congr 1
    apply propext
    constructor
    · intro h
      calc u⁻¹ * t * x = u⁻¹ * (t * (t⁻¹ * (u * x * u⁻¹) * t)) := by rw [h]; group
        _ = x * (u⁻¹ * t) := by group
    · intro h
      calc t⁻¹ * (u * x * u⁻¹) * t = t⁻¹ * u * (x * (u⁻¹ * t)) := by group
        _ = t⁻¹ * u * (u⁻¹ * t * x) := by rw [h]
        _ = x := by group
end GroundTheory.LocalField
