-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.finite_fib
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:20.208901+00:00
-- url     : https://prove2.me/submissions/14af858c-d0b0-418f-921c-a7572686e254

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x y : X) :
    Finite {γ : Γ // γ • x = y} := by
  by_cases hne : Nonempty {γ : Γ // γ • x = y}
  · obtain ⟨γ0, h0⟩ := hne
    refine Finite.of_injective (β := MulAction.stabilizer Γ x) (fun γ => ⟨γ0⁻¹ * γ.1, ?_⟩) ?_
    · rw [MulAction.mem_stabilizer_iff, mul_smul, γ.2, ← h0, inv_smul_smul]
    · intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
  · haveI := not_nonempty_iff.1 hne
    infer_instance
end GlobalTheory.CompanionTheory.HeckeCoinv
