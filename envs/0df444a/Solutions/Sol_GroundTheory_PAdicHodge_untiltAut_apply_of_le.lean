-- Prove2me | solution 1 for GroundTheory.PAdicHodge.untiltAut_apply_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:00:47.549332+00:00
-- url     : https://prove2.me/submissions/aab318c1-88a2-450e-8366-1c3ce7f9ff8a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural
import Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_inclusion
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_untiltAut_fontaineTheta
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono
import Theorems.Thm_GroundTheory_PAdicHodge_untiltField_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {M N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] (h : M ≤ N)
    (σ : N ≃ₐ[K♭] N) (hσ : ∀ y : N, (y : C♭) ∈ M → σ y = y) (x : untiltField K C p M) :
    untiltAut N σ ⟨x, untiltField_mono h x.2⟩ = ⟨x, untiltField_mono h x.2⟩ := by
  set f : untiltField K C p M →ₐ[K] C := (untiltField K C p N).val.comp
    ((untiltAut N σ).toAlgHom.comp (IntermediateField.inclusion (untiltField_mono h)))
  set g : untiltField K C p M →ₐ[K] C := (untiltField K C p M).val
  have hfg : f = g := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    show ((untiltAut N σ (IntermediateField.inclusion (untiltField_mono h)
        ⟨y, IntermediateField.subset_adjoin _ _ hy⟩) : untiltField K C p N) : C) = y
    generalize IntermediateField.subset_adjoin K _ hy = hy0
    obtain ⟨z, ⟨u, rfl⟩, rfl⟩ := hy
    set u' := WittVector.map (Subring.inclusion (integerTilt_mono h)) u
    have hz : ((RingHom.comp θ (WittVector.map (integerTilt K C p M).subtype) u : normInteger C) : C) =
        ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) := by
      rw [fontaineTheta_map_inclusion h]; rfl
    have hmemN' : ((θ (WittVector.map (integerTilt K C p N).subtype u') : normInteger C) : C) ∈
        untiltField K C p N := coe_mem_untiltField ⟨u', rfl⟩
    have hcoeff : ∀ n, integerTiltHom N σ.toAlgHom (norm_tiltAlgEquiv_toAlgHom_apply N σ)
        (u'.coeff n) = u'.coeff n := by
      intro n
      apply Subtype.ext
      apply IsFractionRing.injective 𝒪C♭ C♭
      rw [algebraMap_integerTiltHom]
      exact congrArg Subtype.val (hσ ⟨algebraMap 𝒪C♭ C♭ (u'.coeff n : 𝒪C♭), (u'.coeff n).2⟩
        (u.coeff n).2)
    have hmap : WittVector.map (integerTiltHom N σ.toAlgHom
        (norm_tiltAlgEquiv_toAlgHom_apply N σ)) u' = u' :=
      WittVector.ext fun n => by rw [WittVector.map_coeff, hcoeff n]
    have e1 : IntermediateField.inclusion (untiltField_mono h) ⟨_, hy0⟩ =
        (⟨_, hmemN'⟩ : untiltField K C p N) := Subtype.ext hz
    rw [e1, coe_untiltAut_fontaineTheta, hmap]
    exact hz.symm
  exact Subtype.ext (congrArg (fun φ : untiltField K C p M →ₐ[K] C => φ x) hfg)
end GroundTheory.PAdicHodge
