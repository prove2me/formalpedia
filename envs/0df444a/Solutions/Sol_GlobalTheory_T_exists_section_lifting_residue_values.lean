-- Prove2me | solution 1 for GlobalTheory.T.exists_section_lifting_residue_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:58.462106+00:00
-- url     : https://prove2.me/submissions/d7d28457-3341-4eaa-910f-3753dbaa0eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValues
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSectionLiftingResidueValuesStatement
import Theorems.Thm_GlobalTheory_DenseSec_hensel_etChart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R → ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) → ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  first | exact @GlobalTheory.DenseSec.hensel_etChart | exact GlobalTheory.DenseSec.hensel_etChart | (intros; apply GlobalTheory.DenseSec.hensel_etChart <;> assumption)
end _root_.GlobalTheory.T
