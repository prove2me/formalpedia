-- Prove2me | solution 1 for GlobalTheory.UnimodOver.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:49:49.278893+00:00
-- url     : https://prove2.me/submissions/b431e8ea-5f49-48c2-8a52-6599b230b6c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_discrete_of_le
import Theorems.Thm_GlobalTheory_UnimodOver_span_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.UnimodOver
theorem _root_.solution {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by
  haveI := discrete_of_le h
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ M := ⟨span_of_le hs h⟩
  have hr : finrank ℤ (L.comap M.subtype) = finrank ℤ M := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, ZLattice.rank ℝ L, ZLattice.rank ℝ M]
  haveI hfin : Finite (M ⧸ L.comap M.subtype) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  refine ⟨Nat.card (M ⧸ L.comap M.subtype), Nat.card_pos, fun x hx => ?_⟩
  have h1 := (L.comap M.subtype).toAddSubgroup.nsmul_index_mem ⟨x, hx⟩
  exact h1
end GlobalTheory.UnimodOver
