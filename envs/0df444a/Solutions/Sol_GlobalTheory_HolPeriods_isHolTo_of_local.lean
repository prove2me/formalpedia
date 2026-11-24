-- Prove2me | solution 1 for GlobalTheory.HolPeriods.isHolTo_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:19.46821+00:00
-- url     : https://prove2.me/submissions/d281289d-04ae-466f-aa41-ec7108d8a389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}
namespace GlobalTheory.HolPeriods
theorem _root_.solution {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : ∀ b ∈ B, ∃ B' : Set V, b ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y) : IsHolTo B y := by
  intro U f
  have key : ∀ b ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ nhds b ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) b := by
    intro b hb
    obtain ⟨B', hb', hsub, hB'⟩ := h b hb.1
    have hn := (hB' U f).1.mem_nhds (⟨hb', hb.2⟩ : b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U})
    exact ⟨Filter.mem_of_superset hn fun c hc => ⟨hsub hc.1, hc.2⟩, (hB' U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb).1,
    fun b hb => (key b hb).2.differentiableWithinAt⟩
end GlobalTheory.HolPeriods
