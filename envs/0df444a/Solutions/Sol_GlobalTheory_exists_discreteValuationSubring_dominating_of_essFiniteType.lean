-- Prove2me | solution 1 for GlobalTheory.exists_discreteValuationSubring_dominating_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:48:04.228492+00:00
-- url     : https://prove2.me/submissions/144c929a-b853-4243-8e1a-8a3864ae60aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]
namespace GlobalTheory
theorem _root_.solution [Algebra.EssFiniteType R L]
    [FaithfulSMul R L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  obtain ⟨W, hW⟩ := (LocalSubring.range (algebraMap R L)).exists_le_valuationSubring
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (isField_iff_maximalIdeal_eq.not.mp hR)
  obtain ⟨V, h1, h2, -⟩ := exists_discreteValuationSubring_dominating_of_le W hW
    Set.finite_empty Set.finite_empty (by simp) (by simp) (Or.inl ⟨r, hr, by simpa using hr0⟩)
  exact ⟨V, h1, h2⟩
end GlobalTheory
