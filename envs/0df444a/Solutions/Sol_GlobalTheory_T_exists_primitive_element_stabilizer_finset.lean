-- Prove2me | solution 1 for GlobalTheory.T.exists_primitive_element_stabilizer_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:34.595881+00:00
-- url     : https://prove2.me/submissions/76c67698-c304-4d38-a462-dd0b7bb9d09a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimitiveElementStabilizerFinset
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimitiveElementStabilizerFinsetStatement
import Theorems.Thm_GlobalTheory_stab_finset_eq_stab_primitive


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
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  first | exact @GlobalTheory.stab_finset_eq_stab_primitive | exact GlobalTheory.stab_finset_eq_stab_primitive | (intros; apply GlobalTheory.stab_finset_eq_stab_primitive <;> assumption)
end _root_.GlobalTheory.T
