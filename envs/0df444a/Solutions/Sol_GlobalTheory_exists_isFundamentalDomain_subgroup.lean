-- Prove2me | solution 1 for GlobalTheory.exists_isFundamentalDomain_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:16.213176+00:00
-- url     : https://prove2.me/submissions/d95f6379-8341-4488-b002-008405f8bec3

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
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ D μ := by
  have := countable_of_discrete_subgroup Γ
  have hfree : ∀ (g : Γ) (x : G), g • x = x → g = 1 := fun g x h =>
    Subtype.ext (mul_eq_right.1 h)
  obtain ⟨V, hV, hV1⟩ := exists_nhds_one_inter_subgroup Γ
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Γ) (X := G)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {x : G | g • x = x} = ∅ := eq_empty_of_forall_notMem fun x hx => hg (hfree g x hx)
        simp [this])
    (fun x => by
      refine ⟨(· * x⁻¹) ⁻¹' V, (continuous_mul_const _).continuousAt.preimage_mem_nhds
        (by simpa using hV), fun g hg => ?_⟩
      have h1 : (g : G) ∈ V := by
        have : (g : G) * x * x⁻¹ ∈ V := hg
        simpa using this
      have : g = 1 := Subtype.ext (hV1 g g.2 h1)
      rw [this, one_smul])
  have h : ∀ x, ∃! g : Γ, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by rwa [mul_smul, inv_smul_smul])
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩
end GlobalTheory
