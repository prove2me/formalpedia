-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isOrthoCompl_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:43.397109+00:00
-- url     : https://prove2.me/submissions/06679484-7110-494a-90f5-97422a9ef1a1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_bijective_of_injective_sesq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V)
    (U : Submodule E V) (hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0) :
    h.IsOrthoCompl U (h.orthogonal U) := by
  have hinj : Function.Injective (h.toSesq.domRestrict₁₂ U U) := by
    intro a b hab
    have hab' : a - b = 0 := by
      apply Subtype.ext
      apply hU _ (a - b).2
      intro u' hu'
      have h1 := LinearMap.congr_fun hab ⟨u', hu'⟩
      simp only [LinearMap.domRestrict₁₂_apply] at h1
      rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, h1, sub_self]
    exact sub_eq_zero.1 hab'
  have hbij := bijective_of_injective_sesq _ hinj
  refine ⟨?_, fun x hx y hy => hy x hx⟩
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot E).2
      (hU x hx1 fun u' hu' => h.toSesq_eq_zero_comm.1 (hx2 u' hu'))
  · rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu⟩ := hbij.2 ((h.toSesq v).domRestrict U)
    rw [Submodule.mem_sup]
    refine ⟨u, u.2, v - u, fun x hx => ?_, by abel⟩
    have h1 := LinearMap.congr_fun hu ⟨x, hx⟩
    simp only [LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict_apply] at h1
    rw [h.toSesq_eq_zero_comm, map_sub, LinearMap.sub_apply, h1, sub_self]
end GroundTheory.Automorphic.HermitianForm
