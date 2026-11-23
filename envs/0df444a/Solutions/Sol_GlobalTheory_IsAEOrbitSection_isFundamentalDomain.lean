-- Prove2me | solution 1 for GlobalTheory.IsAEOrbitSection.isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:03.957202+00:00
-- url     : https://prove2.me/submissions/986d7902-f051-4098-b8a6-308e508a4966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection

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
namespace IsAEOrbitSection
theorem _root_.solution {D : Set X} (hD : IsAEOrbitSection G D μ)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ := by
  refine IsFundamentalDomain.mk'' hD.nullMeasurableSet hD.ae_covers (fun g hg => ?_)
    fun g => (measurePreserving_smul g μ).quasiMeasurePreserving
  have h1 : ∀ᵐ x ∂μ, ¬ g⁻¹ • x = x := by
    rw [ae_iff]; simpa using hfree g⁻¹ (inv_ne_one.2 hg)
  refine measure_mono_null (fun y hy => ?_) (h1.and hD.ae_unique)
  rintro ⟨h2, h3⟩
  exact h2 (h3 hy.2 g⁻¹ (mem_smul_set_iff_inv_smul_mem.1 hy.1))
end IsAEOrbitSection
end GlobalTheory
