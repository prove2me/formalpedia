-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:14:34.799447+00:00
-- url     : https://prove2.me/submissions/6b9f945f-9c5e-4db8-ab74-c507206e11c8

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePowerStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminantStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
import Theorems.Thm_GlobalTheory_CompanionTheory_HermiteMinkowski_bound_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_HermiteMinkowski_natAbs_discr_dvd
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
open GlobalTheory.CompanionTheory.HermiteMinkowski
namespace GlobalTheory.CompanionTheory.HermiteMinkowski
theorem _root_.solution :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ),
      {E : IntermediateField F Ω | FiniteDimensional F E ∧
        IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧
        Module.finrank F E ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S N
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  set n := Module.finrank ℚ F * N with hn
  set M : ℕ := bound S ^ (n * n) with hM
  have hfin := (NumberField.finite_of_discr_bdd Ω M).image Subtype.val
  have hinj : Function.Injective (fun E : IntermediateField F Ω => E.restrictScalars ℚ) :=
    IntermediateField.restrictScalars_injective ℚ
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro E ⟨hfd, hun, hdeg⟩
  haveI := hfd
  haveI : NumberField E := NumberField.of_module_finite F E
  let e : (E.restrictScalars ℚ) ≃ₐ[ℚ] E := (RingEquiv.refl E : E ≃+* E).toRatAlgEquiv
  haveI hfd' : FiniteDimensional ℚ (E.restrictScalars ℚ) :=
    e.toLinearEquiv.symm.finiteDimensional
  refine ⟨⟨E.restrictScalars ℚ, hfd'⟩, ?_, rfl⟩
  haveI : NumberField (E.restrictScalars ℚ) := @NumberField.mk _ _ inferInstance hfd'
  show |discr (E.restrictScalars ℚ)| ≤ (M : ℤ)
  rw [discr_eq_discr_of_algEquiv _ e]
  have hdvd := natAbs_discr_dvd (E := E) S fun v hv => hun v (by simpa using hv)
  have hd : Module.finrank ℚ E ≤ n := by
    rw [← Module.finrank_mul_finrank ℚ F E]
    exact Nat.mul_le_mul_left _ hdeg
  have hb : 0 < bound S := Nat.pos_of_ne_zero (bound_ne_zero S)
  have hle := Nat.le_of_dvd (pow_pos hb _) hdvd
  have hle2 : bound S ^ (Module.finrank ℚ E * Module.finrank ℚ E) ≤ bound S ^ (n * n) :=
    Nat.pow_le_pow_right hb (Nat.mul_le_mul hd hd)
  rw [hM, Int.abs_eq_natAbs]
  exact_mod_cast hle.trans hle2
end GlobalTheory.CompanionTheory.HermiteMinkowski
