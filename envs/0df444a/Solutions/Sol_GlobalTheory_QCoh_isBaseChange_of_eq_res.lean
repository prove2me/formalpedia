-- Prove2me | solution 1 for GlobalTheory.QCoh.isBaseChange_of_eq_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:09:41.086896+00:00
-- url     : https://prove2.me/submissions/e1089945-3731-4a94-8a30-8b13b08505bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resModule_smul
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_isBaseChange_resLinear
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
    (h : V ≤ U) [alg : Algebra Γ(X, U) Γ(X, V)] [mod : Module Γ(X, U) Γ(F, V)]
    [IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V)]
    (halg : ∀ r, algebraMap Γ(X, U) Γ(X, V) r = X.presheaf.map (homOfLE h).op r)
    (l : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V)) (hl : ∀ s, l s = F.presheaf.map (homOfLE h).op s) :
    IsBaseChange Γ(X, V) l := by
  obtain rfl : mod = resModule F h := Module.ext' _ _ fun r s ↦ by
    rw [resModule_smul, ← halg, algebraMap_smul]
  obtain rfl : alg = resAlgebra h := Algebra.algebra_ext _ _ halg
  letI := resModule F h
  obtain rfl : l = resLinear F h := LinearMap.ext hl
  exact isBaseChange_resLinear F hU hV h
end GlobalTheory.QCoh
