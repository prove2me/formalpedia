-- Prove2me | solution 1 for GlobalTheory.T.exists_spec_vectorField_of_dualNumber_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:17.903995+00:00
-- url     : https://prove2.me/submissions/ddde5001-51bd-4ffc-82ad-39025c57cfa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSection
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSectionStatement
import Theorems.Thm_GlobalTheory_SpecField_exists_isField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] (σ : A →+* DualNumber A), (∀ a, (σ a).fst = a) → ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧ ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by
  first | exact @GlobalTheory.SpecField.exists_isField | exact GlobalTheory.SpecField.exists_isField | (intros; apply GlobalTheory.SpecField.exists_isField <;> assumption)
end _root_.GlobalTheory.T
