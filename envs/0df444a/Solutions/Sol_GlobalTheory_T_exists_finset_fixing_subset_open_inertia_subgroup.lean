-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:20.9838+00:00
-- url     : https://prove2.me/submissions/f674795b-1207-43b8-b367-03e05571f43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingSubsetOpenInertiaSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_finset_fix_subset_of_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  first | exact @GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | exact GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | (intros; apply GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen <;> assumption)
end _root_.GlobalTheory.T
