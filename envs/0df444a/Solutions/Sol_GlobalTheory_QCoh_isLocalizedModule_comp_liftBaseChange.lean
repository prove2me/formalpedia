-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizedModule_comp_liftBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:34.542641+00:00
-- url     : https://prove2.me/submissions/f188e21a-8290-4811-b9c3-d0b2ec9d0ca9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution {A B M N P : Type*} (C : Type*) [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] [AddCommGroup P] [Module A P] [Module B P] [Module C P]
    [IsScalarTower A B P] [IsScalarTower A C P] [IsScalarTower B C P]
    (l : M →ₗ[A] N) (g : N →ₗ[B] P) (S : Submonoid B) [IsLocalization S C]
    (h : IsBaseChange C (g.restrictScalars A ∘ₗ l)) :
    IsLocalizedModule S (g ∘ₗ l.liftBaseChange B) := by
  rw [isLocalizedModule_iff_isBaseChange S C]
  refine (TensorProduct.isBaseChange A M B).of_comp ?_
  convert h using 1
  ext m
  simp
end GlobalTheory.QCoh
