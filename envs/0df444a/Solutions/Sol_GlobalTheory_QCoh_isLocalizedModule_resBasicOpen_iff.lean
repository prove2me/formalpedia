-- Prove2me | solution 1 for GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:34.674642+00:00
-- url     : https://prove2.me/submissions/30305abd-a1f5-4a84-bbb9-e4e1efdc9b85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_isUnit_res_of_le_basicOpen
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
theorem _root_.solution (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) ↔
      (∀ s : Γ(F, X.basicOpen f), ∃ (n : ℕ) (t : Γ(F, U)),
        X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
          F.presheaf.map (homOfLE (X.basicOpen_le f)).op t) ∧
      (∀ t : Γ(F, U), F.presheaf.map (homOfLE (X.basicOpen_le f)).op t = 0 →
        ∃ n : ℕ, f ^ n • t = 0) := by
  constructor
  · intro h
    refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj (resBasicOpen F f) f s
      exact ⟨n, t, by rw [← map_pow]; exact ht⟩
    · obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := resBasicOpen F f) f
        (x := t) (y := 0) (by rw [map_zero]; exact ht)
      exact ⟨n, by simpa using hn⟩
  · rintro ⟨h₁, h₂⟩
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun s ↦ ?_) h₂
    · have := (isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).map
        (algebraMap Γ(X, X.basicOpen f) (Module.End Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)))
      rw [Module.End.isUnit_iff] at this ⊢
      exact this
    · obtain ⟨n, t, ht⟩ := h₁ s
      exact ⟨n, t, by rw [← map_pow] at ht; exact ht⟩
end GlobalTheory.QCoh
