-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:55.93223+00:00
-- url     : https://prove2.me/submissions/61a7cb47-fa72-412c-a44d-ecfa7662d23b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_finite_fib
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
theorem _root_.solution [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    (Function.support fun γ : Γ => f (γ • x)).Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion f.support.finite_toSet
    (t := fun z => {γ : Γ | γ • x = z}) ?_) ?_
  · intro z _
    exact Set.finite_coe_iff.1 (finite_fib (Γ := Γ) x z)
  · intro γ hγ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨γ • x, by simpa using hγ, rfl⟩
end GlobalTheory.CompanionTheory.HeckeCoinv
