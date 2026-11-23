-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_subgroup_op
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:17.701545+00:00
-- url     : https://prove2.me/submissions/3b59cf88-9e54-4300-887a-6e357019a22c

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
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_free
import Theorems.Thm_GlobalTheory_exists_isAEOrbitSection
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_ae_free
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_of_surjective
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_and_quotMeasure_eq
import Theorems.Thm_GlobalTheory_quotMeasure_eq_zero_iff
import Theorems.Thm_GlobalTheory_countable_of_discrete_subgroup
import Theorems.Thm_GlobalTheory_exists_nhds_one_inter_subgroup
import Theorems.Thm_GlobalTheory_exists_isFundamentalDomain_subgroup

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
variable [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory
theorem _root_.solution :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ.op, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by
  obtain ⟨D, hD, h, -⟩ := exists_isFundamentalDomain_subgroup Γ
  have h' : ∀ x, ∃! g : Γ.op, g • x ∈ D⁻¹ := fun x => by
    obtain ⟨g, hg, hu⟩ := h x⁻¹
    refine ⟨⟨MulOpposite.op (g : G)⁻¹, inv_mem g.2⟩, ?_, fun k hk => ?_⟩
    · have : (g : G) * x⁻¹ ∈ D := hg
      change (x * (g : G)⁻¹)⁻¹ ∈ D
      rwa [mul_inv_rev, inv_inv]
    · have hk' : (x * MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹ ∈ D := hk
      rw [mul_inv_rev] at hk'
      have := hu ⟨(MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹, inv_mem k.2⟩ hk'
      subst this
      ext
      simp
  exact ⟨D⁻¹, hD.inv, h', fun μ => IsFundamentalDomain.mk' hD.inv.nullMeasurableSet h'⟩
end GlobalTheory
