-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.length_ext_zero_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:44.861891+00:00
-- url     : https://prove2.me/submissions/2a85a439-f304-45ac-9966-5695ad3eba51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Theorems.Thm_GlobalTheory_FiniteLengthComplex_isIso_pOpcycles_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution :
    Module.length R (Abelian.Ext.{0} (C.opcycles 0) (ModuleCat.of R R) 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0))) =
      Module.length R (Module.Dual R (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) := by
  have := isIso_pOpcycles_zero C
  let e (X : ModuleCat.{0} R) : Abelian.Ext.{0} X (ModuleCat.of R R) 0 ≃ₗ[R] Module.Dual R X :=
    (Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv
  have he (X : ModuleCat.{0} R) (f : X ⟶ ModuleCat.of R R) : e X (Ext.mk₀ f) = f.hom := by
    rw [← LinearEquiv.eq_symm_apply]
    rfl
  let φ := (extCongrLeft (asIso (C.pOpcycles 0)) (ModuleCat.of R R) 0).trans (e (C.X 0))
  have hφ (f : C.X 1 ⟶ ModuleCat.of R R) :
      φ ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0)
        (Ext.mk₀ f)) = (C.d 0 1).hom.dualMap f.hom := by
    change e _ ((Ext.mk₀ (C.pOpcycles 0)).comp
      ((Ext.mk₀ _).comp (Ext.mk₀ f) (zero_add 0)) (zero_add 0)) = _
    rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, he, HomologicalComplex.p_fromOpcycles_assoc]
    rfl
  refine (Submodule.Quotient.equiv _ _ φ ?_).length_eq
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    exact ⟨f.hom, (hφ f).symm⟩
  · rintro _ ⟨f, rfl⟩
    exact ⟨_, ⟨Ext.mk₀ (ModuleCat.ofHom f), rfl⟩, hφ (ModuleCat.ofHom f)⟩
end GlobalTheory.FiniteLengthComplex
