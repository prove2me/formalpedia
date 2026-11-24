-- Prove2me | solution 1 for GlobalTheory.QCoh.isBaseChange_resLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:18:29.152482+00:00
-- url     : https://prove2.me/submissions/a3dd8704-a02b-4c1e-ad92-b3011726714e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_res_res
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resBasicOpen
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resLinear
import Theorems.Thm_GlobalTheory_QCoh_bijective_of_isLocalizedModule_comp
import Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_comp_liftBaseChange
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
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule F h
    haveI := res_isScalarTower F h
    IsBaseChange Γ(X, V) (resLinear F h) := by
  letI := resAlgebra h
  letI := resModule F h
  haveI := res_isScalarTower F h
  let s : Set Γ(X, V) := {b | ∃ f : Γ(X, U), X.basicOpen b = X.basicOpen f}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hV x ⟨h hx, hx⟩
    exact Opens.mem_iSup.mpr ⟨⟨g, f, e.symm⟩, e ▸ hxf⟩
  have H₁ (b : s) : IsLocalizedModule.Away b.1 (resBasicOpen F b.1) :=
    isLocalizedModule_resBasicOpen F hV b.1
  have H₂ (b : s) : IsLocalizedModule.Away b.1
      (resBasicOpen F b.1 ∘ₗ (resLinear F h).liftBaseChange Γ(X, V)) := by
    obtain ⟨b, f, e⟩ := b
    have hb : X.basicOpen b ≤ U := (X.basicOpen_le b).trans h
    letI := resAlgebra hb
    letI := resModule F hb
    haveI := res_isScalarTower F hb
    haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(X, X.basicOpen b) :=
      .of_algebraMap_eq fun r ↦ (res_res_ring h (X.basicOpen_le b) r).symm
    haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(F, X.basicOpen b) :=
      .of_algebraMap_smul fun r t ↦ by
        change X.presheaf.map (homOfLE (X.basicOpen_le b)).op
          (X.presheaf.map (homOfLE h).op r) • t = X.presheaf.map (homOfLE hb).op r • t
        rw [res_res_ring]
    haveI := hV.isLocalization_basicOpen b
    haveI : IsLocalization.Away f Γ(X, X.basicOpen b) :=
      hU.isLocalization_of_eq_basicOpen f (homOfLE hb) e
    refine isLocalizedModule_comp_liftBaseChange Γ(X, X.basicOpen b) _ _ _ ?_
    rw [← isLocalizedModule_iff_isBaseChange (.powers f)]
    convert isLocalizedModule_resLinear F hU f hb e using 1
    ext t
    exact res_res F h (X.basicOpen_le b) t
  have hbij := bijective_of_isLocalizedModule_comp ((resLinear F h).liftBaseChange Γ(X, V)) s hs
    (fun b ↦ Γ(F, X.basicOpen b.1)) (fun b ↦ resBasicOpen F b.1)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hbij) fun t ↦ by simp
end GlobalTheory.QCoh
