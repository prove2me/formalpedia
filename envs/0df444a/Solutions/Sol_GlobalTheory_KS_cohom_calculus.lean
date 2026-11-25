-- Prove2me | solution 1 for GlobalTheory.KS.cohom_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:45.706425+00:00
-- url     : https://prove2.me/submissions/cd623fd4-685c-4e2d-b099-9c4460b86d48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_IsCob_add
import Theorems.Thm_GlobalTheory_KS_IsCob_sub
import Theorems.Thm_GlobalTheory_KS_isCob_lc
import Theorems.Thm_GlobalTheory_KS_cohom_lc
import Theorems.Thm_GlobalTheory_KS_Cohom_isCob_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (f : Y ⟶ Y) (I : Type) (U : I → Y.Opens), f ≫ q = q → ⨆ i, U i = ⊤ → (∀ c c₁ c' c₁' : C1 U, Cohom f U c c' → Cohom f U c₁ c₁' → IsCob U (c' - c₁') → IsCob U (c - c₁)) ∧ (∀ (g : ℕ) (a : Fin g → K) (c c' : Fin g → C1 U), (∀ x, Cohom f U (c x) (c' x)) → Cohom f U (lc q a c) (lc q a c')) ∧ (∀ (g : ℕ) (a : Fin g → K) (c : Fin g → C1 U), (∀ x, IsCob U (c x)) → IsCob U (lc q a c)) ∧ ∀ c c' : C1 U, IsCob U c → IsCob U c' → IsCob U (c + c') ∧ IsCob U (c - c') :=
  fun _ _ _ q f _ _ hf hU =>
    ⟨fun _ _ _ _ h h₁ hc => Cohom.isCob_sub f hU h h₁ hc, fun _ a c c' h => cohom_lc q f hf a c c' h,
      fun _ a c h => isCob_lc q a c h, fun _ _ h h' => ⟨h.add h', h.sub h'⟩⟩
end GlobalTheory.KS
