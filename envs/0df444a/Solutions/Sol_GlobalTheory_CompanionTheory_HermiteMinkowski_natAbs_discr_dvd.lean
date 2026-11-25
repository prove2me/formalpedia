-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermiteMinkowski.natAbs_discr_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:44.474666+00:00
-- url     : https://prove2.me/submissions/3b6166ec-9e27-4a7d-ad87-caac9578476c

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePowerStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminantStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
import Theorems.Thm_GlobalTheory_CompanionTheory_HermiteMinkowski_bound_ne_zero
import Theorems.Thm_GlobalTheory_T_different_dvd_ramified_prime_power
import Theorems.Thm_GlobalTheory_T_ramified_prime_contains_discriminant
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermiteMinkowski
namespace GlobalTheory.CompanionTheory.HermiteMinkowski
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) :
    (discr E).natAbs ∣ bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) := by
  have hdvd := GlobalTheory.T.different_dvd_ramified_prime_power E (bound S) (bound_ne_zero S) fun P hP hP0 hPd => by
    haveI := hP
    exact GlobalTheory.T.ramified_prime_contains_discriminant F E S hE P hP0 hPd
  have h := map_dvd Ideal.absNorm hdvd
  rw [absNorm_differentIdeal E (𝓞 E)] at h
  have hr : ((bound S : 𝓞 E)) ^ (Module.finrank ℚ E) =
      algebraMap ℤ (𝓞 E) (((bound S : ℕ) : ℤ) ^ (Module.finrank ℚ E)) := by
    simp
  rw [Ideal.absNorm_span_singleton, hr, Algebra.norm_algebraMap, RingOfIntegers.rank,
    Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_natCast, ← pow_mul] at h
  exact h
end GlobalTheory.CompanionTheory.HermiteMinkowski
