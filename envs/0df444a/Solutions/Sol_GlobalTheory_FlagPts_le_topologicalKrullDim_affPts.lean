-- Prove2me | solution 1 for GlobalTheory.FlagPts.le_topologicalKrullDim_affPts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:08.124564+00:00
-- url     : https://prove2.me/submissions/6286d037-d3b1-4e1e-bcaf-0dd128fb11cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts
open MvPolynomial
variable {k : Type} [Field k] {J : Type}
namespace GlobalTheory.FlagPts
theorem _root_.solution [Infinite k] [Fintype J] :
    ((Fintype.card J : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (AffPts k J) := by
  classical
  set e := Fintype.equivFin J
  set n := Fintype.card J
  let f : Fin (n + 1) → IrreducibleCloseds (AffPts k J) :=
    fun m ↦ coordSubspace {j | (e j : ℕ) < m}
  have hf : StrictMono f := by
    intro a b hab
    rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun x hx j hj ↦ hx j fun h ↦ hj ?_, ?_⟩
    · exact lt_trans (Set.mem_setOf.1 h) hab
    have ha : (a : ℕ) < n := lt_of_lt_of_le hab (Nat.lt_succ_iff.1 b.2)
    refine ⟨fun j ↦ if (e j : ℕ) = a then 1 else 0, ?_, ?_⟩
    · intro j hj
      have : (e j : ℕ) ≠ a := fun h ↦ hj (by simp only [Set.mem_setOf_eq, h]; exact hab)
      simp [this]
    · intro hx
      have := hx (e.symm ⟨a, ha⟩) (by simp)
      simp at this
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk n f hf)
end GlobalTheory.FlagPts
