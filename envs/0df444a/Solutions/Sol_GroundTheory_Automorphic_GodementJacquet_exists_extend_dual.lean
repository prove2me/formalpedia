-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_extend_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:08.913285+00:00
-- url     : https://prove2.me/submissions/9562f331-e502-4164-91aa-180ddd21adb6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_fixedMap_injective
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_map
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_sub_fixedProj_mem
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (ι : Representation.IntertwiningMap ρ τ) (hι : Function.Injective ι) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {ℓ : Module.Dual ℂ V}
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    ∃ lam : Module.Dual ℂ U, (∀ k ∈ K, ∀ x, lam (τ k x) = lam x) ∧ ∀ v, lam (ι v) = ℓ v := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (fixedMap ρ ι K)
    (LinearMap.ker_eq_bot.2 (fixedMap_injective ρ hι))
  refine ⟨ℓ ∘ₗ (fixedVectors ρ K).subtype ∘ₗ r ∘ₗ fixedProj τ hτ hKc hKo, fun k hk x => ?_,
    fun v => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [fixedProj_apply_act hτ hKc hKo hk]
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [fixedProj_map hKc hKo hρ hτ ι v]
    have h1 : r (fixedMap ρ ι K (fixedProj ρ hρ hKc hKo v)) = fixedProj ρ hρ hKc hKo v := by
      rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
    rw [h1]

    have hker : ∀ y ∈ coinvariantsKer ρ K, ℓ y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hy
      rintro _ ⟨k, rfl⟩
      simp [hℓ k.1.1 k.1.2 k.2]
    have := hker _ (sub_fixedProj_mem hρ hKc hKo v)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
end GroundTheory.Automorphic.GodementJacquet
