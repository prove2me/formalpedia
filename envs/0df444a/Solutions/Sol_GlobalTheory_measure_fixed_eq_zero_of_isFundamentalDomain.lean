-- Prove2me | solution 1 for GlobalTheory.measure_fixed_eq_zero_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:34.71614+00:00
-- url     : https://prove2.me/submissions/e64f14fc-00be-45b5-9fa7-dcf345590775

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_isFundamentalDomain

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
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
namespace GlobalTheory
theorem _root_.solution {D : Set X} (hD : IsFundamentalDomain G D μ)
    {g : G} (hg : g ≠ 1) : μ {x | g • x = x} = 0 := by
  have h1 : ∀ᵐ x ∂μ, ∀ k : G, k • x ∈ D → ¬ g • x = x := by
    refine ae_all_iff.2 fun k => ?_
    have hne : k⁻¹ ≠ (k * g)⁻¹ := fun e => hg (by simpa using inv_injective e)
    refine measure_mono_null (fun x hx => ?_) (hD.aedisjoint hne)
    simp only [mem_compl_iff, mem_setOf_eq, Classical.not_imp, not_not] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hx.1
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv, mul_smul, hx.2]; exact hx.1
  refine measure_mono_null (fun x hx => ?_) (h1.and hD.ae_covers)
  rintro ⟨h2, k, hk⟩
  exact h2 k hk hx
end GlobalTheory
