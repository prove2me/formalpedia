-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.subsingleton_sections_of_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:15.813495+00:00
-- url     : https://prove2.me/submissions/528d0fc6-03c4-4246-b158-cd2c69202674

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution (h : W = ⊥) : Subsingleton Γ(F, W) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{u + 1} ↦ i.elim) W (fun i ↦ i.elim) (by simp [h]) s t (fun i ↦ i.elim)
end GlobalTheory.QCoh.Qcqs
