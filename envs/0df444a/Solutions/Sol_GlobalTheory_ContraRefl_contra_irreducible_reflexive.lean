-- Prove2me | solution 1 for GlobalTheory.ContraRefl.contra_irreducible_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:45.949053+00:00
-- url     : https://prove2.me/submissions/75d2aa53-589d-410e-ab43-2f7fe556209c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexive
import Theorems.Thm_GlobalTheory_ContraRefl_contra_isIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.ContraRefl
variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.ContraRefl
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → (π.IsIrreducible → (contra π).IsIrreducible) ∧ Nonempty (π.Equiv (contra (contra π))) ∧ (Nonempty ((contra π).Equiv (contra π')) → Nonempty (π.Equiv π')) := by
  intro G _ _ _ hG V _ _ W _ _ π π' hπ hπ'
  refine ⟨contra_isIrreducible hG hπ, ⟨evEquiv hG hπ⟩, fun ⟨e⟩ => ⟨?_⟩⟩
  exact ((evEquiv hG hπ).trans (contraEquiv e.symm)).trans (evEquiv hG hπ').symm
end GlobalTheory.ContraRefl
