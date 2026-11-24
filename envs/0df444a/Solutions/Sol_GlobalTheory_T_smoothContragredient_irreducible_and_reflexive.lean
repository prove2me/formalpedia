-- Prove2me | solution 1 for GlobalTheory.T.smoothContragredient_irreducible_and_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:59.962309+00:00
-- url     : https://prove2.me/submissions/60f53b51-7082-4732-98ad-479e3218d5d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexiveStatement
import Theorems.Thm_GlobalTheory_ContraRefl_contra_irreducible_reflexive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → (π.IsIrreducible → (contra π).IsIrreducible) ∧ Nonempty (π.Equiv (contra (contra π))) ∧ (Nonempty ((contra π).Equiv (contra π')) → Nonempty (π.Equiv π')) := by
  first | exact @GlobalTheory.ContraRefl.contra_irreducible_reflexive | exact GlobalTheory.ContraRefl.contra_irreducible_reflexive | (intros; apply GlobalTheory.ContraRefl.contra_irreducible_reflexive <;> assumption)
end _root_.GlobalTheory.T
