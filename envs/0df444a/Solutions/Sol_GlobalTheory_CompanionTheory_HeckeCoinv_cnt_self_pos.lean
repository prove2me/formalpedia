-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.cnt_self_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:55.738938+00:00
-- url     : https://prove2.me/submissions/b4e4902b-7138-40b8-b37b-8099472f7fb7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_finite_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x : X) : 0 < cnt Γ x x := by
  haveI := finite_fib (Γ := Γ) x x
  haveI : Nonempty {γ : Γ // γ • x = x} := ⟨⟨1, one_smul _ _⟩⟩
  exact Nat.card_pos
end GlobalTheory.CompanionTheory.HeckeCoinv
