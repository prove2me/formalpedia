-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.InertiaLift.fixingSubgroup_le_NS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:51.610292+00:00
-- url     : https://prove2.me/submissions/7b778b83-ace6-49bd-bace-2d353d0201d1

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Theorems.Thm_GlobalTheory_CompanionTheory_Glob_InertiaLift_exists_inertia_lift
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_exists_finiteGalois_mem
import Theorems.Thm_GroundTheory_ProfCoh_finiteDimensional_of_le
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_iff_inertia
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_NS
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
open scoped Pointwise IntermediateField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.InertiaLift
namespace GlobalTheory.CompanionTheory.Glob.InertiaLift
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  intro F Ω _ _ _ _ _ S
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois F Ω := {}
  have key : IntermediateField.fixedField (NS Ω S) ≤ maxUnramifiedOutside F Ω S := by
    intro x hx
    obtain ⟨M, hxM⟩ := exists_finiteGalois_mem (K := F) x
    have hE : F⟮x⟯ ≤ M.toIntermediateField := IntermediateField.adjoin_simple_le_iff.2 hxM
    have : FiniteDimensional F F⟮x⟯ := finiteDimensional_of_le hE
    have hEK : F⟮x⟯ ≤ IntermediateField.fixedField (NS Ω S) :=
      IntermediateField.adjoin_simple_le_iff.2 hx
    refine le_maxUnramifiedOutside S (E := F⟮x⟯) (fun v hv => ?_)
      (IntermediateField.mem_adjoin_simple_self F x)
    rw [isUnramifiedIn_iff_inertia hE v]
    intro Q hQ hQv τ hτ y hy
    have : NumberField M.toIntermediateField := NumberField.of_module_finite F _
    have : IsAlgClosure M.toIntermediateField Ω :=
      ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) _⟩
    let w : HeightOneSpectrum (𝓞 M.toIntermediateField) :=
      ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    obtain ⟨A, σ, hA, hσ, hres⟩ := exists_inertia_lift (Ω := Ω) w hτ
    have hAv : IsPlaceOver A v := by
      intro a
      have h1 := hA (algebraMap (𝓞 F) (𝓞 M.toIntermediateField) a)
      refine Iff.trans (by exact h1) ?_
      exact (Ideal.mem_of_liesOver Q v.asIdeal a).symm
    have hNS : σ ∈ NS Ω S := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hσ⟩
    have hfix : σ y = y :=
      (IntermediateField.mem_fixedField_iff (NS Ω S) y).1 (hEK hy) σ hNS
    apply Subtype.ext
    have := hres ⟨y, hE hy⟩
    exact (this.symm.trans hfix)
  have hc := InfiniteGalois.fixingSubgroup_fixedField (⟨NS Ω S, isClosed_NS Ω S⟩ : ClosedSubgroup (Ω ≃ₐ[F] Ω))
  have := IntermediateField.fixingSubgroup_antitone key
  rw [show (IntermediateField.fixedField (NS Ω S)).fixingSubgroup = NS Ω S from hc] at this
  exact this
end GlobalTheory.CompanionTheory.Glob.InertiaLift
