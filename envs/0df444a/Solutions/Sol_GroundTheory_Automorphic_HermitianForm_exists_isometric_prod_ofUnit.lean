-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_isometric_prod_ofUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:50.805033+00:00
-- url     : https://prove2.me/submissions/09f7644b-e7f2-4d33-8dfe-0a218cb866fe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_ne_zero_of_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_finrank_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isOrthoCompl_span_singleton
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_restrict
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
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



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) {v : V} {a : Fˣ}
    (hv : h.toSesq v v = algebraMap F E a) :
    ∃ (W : Submodule E V) (h₀ : HermitianForm F E W),
      Isometric ((ofUnit (E := E) a).prod h₀) h ∧
        (FiniteDimensional E V → finrank E W + 1 = finrank E V) := by
  have hv0 := h.toSesq_self_ne_zero_of_eq hv
  have hne : v ≠ 0 := by rintro rfl; simp at hv0
  have hW := h.isOrthoCompl_span_singleton hv0
  set L := Submodule.span E {v}
  set K := LinearMap.ker (h.toSesq v)
  have iso1 : Isometric (ofUnit (E := E) a) (h.restrict L K hW) := by
    refine ⟨LinearEquiv.toSpanNonzeroSingleton E V v hne, fun x y => ?_⟩
    show h.toSesq (x • v) (y • v) = conj F E x * algebraMap F E a * y
    rw [h.toSesq_smul_left, h.toSesq_smul_right, hv]
    ring
  refine ⟨K, h.restrict K L hW.symm, (iso1.prod (Isometric.refl _)).trans
    (h.isometric_prod_restrict L K hW), fun hfin => ?_⟩
  have := ((iso1.prod (Isometric.refl (h.restrict K L hW.symm))).trans
    (h.isometric_prod_restrict L K hW)).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega
end GroundTheory.Automorphic.HermitianForm
