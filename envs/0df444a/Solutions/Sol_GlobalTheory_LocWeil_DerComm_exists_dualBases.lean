-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.exists_dualBases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:51.075711+00:00
-- url     : https://prove2.me/submissions/090e1587-1edb-4ea7-a933-90109ec22ba0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) :
    ∃ (n : ℕ) (b b' : Fin n → U), DualBases β b b' := by
  have hn : LinearMap.BilinForm.Nondegenerate β := ⟨hβ, fun y hy => hβ y fun x => by rw [hs, hy, neg_zero]⟩
  let b := Module.finBasis ℝ U
  let b' := LinearMap.BilinForm.dualBasis β hn b
  refine ⟨_, b, b', fun x => ?_, fun x => ?_⟩
  · conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]
    simp only [b', map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left]
    simp
  · conv_rhs => rw [← b'.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
end GlobalTheory.LocWeil.DerComm
