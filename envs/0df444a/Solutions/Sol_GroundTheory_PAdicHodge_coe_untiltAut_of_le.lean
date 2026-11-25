-- Prove2me | solution 1 for GroundTheory.PAdicHodge.coe_untiltAut_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:45.582219+00:00
-- url     : https://prove2.me/submissions/c76e55e4-cf23-4b48-971d-4c477aa55f52

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural
import Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_inclusion
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_untiltAut_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_untiltField_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution {N N' : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    [FiniteDimensional K♭ N'] (h : N ≤ N') (σ : N ≃ₐ[K♭] N) (σ' : N' ≃ₐ[K♭] N')
    (hσ : ∀ y : N, ((σ' ⟨y, h y.2⟩ : N') : C♭) = ((σ y : N) : C♭)) (x : untiltField K C p N) :
    ((untiltAut N' σ' ⟨x, untiltField_mono h x.2⟩ : untiltField K C p N') : C) =
      ((untiltAut N σ x : untiltField K C p N) : C) := by
  set f : untiltField K C p N →ₐ[K] C := (untiltField K C p N').val.comp
    ((untiltAut N' σ').toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p N →ₐ[K] C := (untiltField K C p N).val.comp (untiltAut N σ).toAlgHom
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N' σ' (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N') : C) =
      ((untiltAut N σ ⟨y, IntermediateField.subset_adjoin _ _ hy⟩ : untiltField K C p N) : C)
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p N).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hcoeff : ∀ n, integerTiltHom N' σ'.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N' σ')
        (u'.coeff n) = Subring.inclusion (integerTilt_mono h)
          (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n)) := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      change _ = algebraMap 𝒪C♭ C♭ (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ) (u.coeff n) : 𝒪C♭)
      rw [algebraMap_integerTiltHom]
      exact hσ ⟨algebraMap 𝒪C♭ C♭ (u.coeff n : 𝒪C♭), (u.coeff n).2⟩
    have hmap : WittVector.map (integerTiltHom N' σ'.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N' σ')) u' =
        WittVector.map (Subring.inclusion (integerTilt_mono h))
          (WittVector.map (integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u) :=
      WittVector.ext fun n => by
        simp only [WittVector.map_coeff]; exact hcoeff n
    have hmemN : ((θ (WittVector.map (integerTilt K C p N).subtype u) : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u, rfl⟩
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N').subtype u') : normInteger C) : C) ∈
        untiltField K C p N' := coe_mem_untiltField ⟨u', rfl⟩
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N') := Subtype.ext hz
    have e2 : (⟨_, hy0⟩ : untiltField K C p N) = ⟨_, hmemN⟩ := rfl
    rw [e1, e2, coe_untiltAut_fontaineTheta, coe_untiltAut_fontaineTheta, hmap,
      fontaineTheta_map_inclusion h]
  exact congrArg (fun φ : untiltField K C p N →ₐ[K] C => φ x) hfg
end GroundTheory.PAdicHodge
