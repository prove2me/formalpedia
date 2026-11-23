-- Prove2me | solution 1 for GlobalTheory.isFundamentalDomain_of_orbitSection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:18.286904+00:00
-- url     : https://prove2.me/submissions/304609bc-d82b-4a7c-a299-57465800a1d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
namespace GlobalTheory
theorem _root_.solution {D : Set X} (hD : NullMeasurableSet D μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D) (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ where
  nullMeasurableSet := hD
  ae_covers := hc
  aedisjoint g h hgh := by
    refine measure_mono_null (fun y hy => ?_) (hfree (g * h⁻¹) fun e => hgh (mul_inv_eq_one.1 e))
    obtain ⟨hg, hh⟩ := hy
    rw [mem_smul_set_iff_inv_smul_mem] at hg hh
    have := hu _ hg (h⁻¹ * g) (by simpa [mul_smul] using hh)
    rw [mul_smul, smul_inv_smul] at this
    rw [mem_setOf_eq, mul_smul, this, smul_inv_smul]
end GlobalTheory
