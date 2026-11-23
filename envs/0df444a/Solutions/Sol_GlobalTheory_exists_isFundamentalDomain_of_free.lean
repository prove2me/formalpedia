-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:24.61183+00:00
-- url     : https://prove2.me/submissions/a2b7aa98-c3db-44e9-b1ee-c8cdddf86880

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_isFundamentalDomain
import Theorems.Thm_GlobalTheory_measure_fixed_eq_zero_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_quotMeasure_univ_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_map_restrict_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measurePreserving_mk
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_univ
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_measure_eq
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_lintegral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integral_quotMeasure
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_integrable_quotMeasure_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_apply_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_eq_zero_iff
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_quotMeasure_image_le
import Theorems.Thm_GlobalTheory_IsAEOrbitSection_sigmaFinite_quotMeasure
import Theorems.Thm_GlobalTheory_quotMeasure_univ_eq_covolume
import Theorems.Thm_GlobalTheory_lintegral_eq_lintegral_quotMeasure_tsum
import Theorems.Thm_GlobalTheory_exists_measurableSet_orbitSection

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
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
namespace GlobalTheory
theorem _root_.solution [ProperlyDiscontinuousSMul G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃! g : G, g • x ∈ D) ∧
      ∀ μ : Measure X, IsFundamentalDomain G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  have h : ∀ x, ∃! g : G, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by simpa [mul_smul] using hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩
end GlobalTheory
