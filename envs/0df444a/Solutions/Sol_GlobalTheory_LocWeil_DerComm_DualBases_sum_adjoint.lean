-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.DualBases.sum_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:13.741941+00:00
-- url     : https://prove2.me/submissions/24d99231-d242-453f-8236-485c43a0670e

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
variable {β b b'}
namespace GlobalTheory.LocWeil.DerComm
namespace DualBases
theorem _root_.solution (h : DualBases β b b') {M : Type} [AddCommGroup M] [Module ℝ M] (B : U →ₗ[ℝ] U →ₗ[ℝ] M)
    (g g' : U → U) (hg : ∀ x y, β (g' x) y = β x (g y)) : ∑ i, B (g (b i)) (b' i) = ∑ i, B (b i) (g' (b' i)) := by
  have e1 : ∀ i, B (g (b i)) (b' i) = ∑ j, β (b' j) (g (b i)) • B (b j) (b' i) := fun i => by
    conv_lhs => rw [← h.1 (g (b i))]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  have e2 : ∀ j, B (b j) (g' (b' j)) = ∑ i, β (b' j) (g (b i)) • B (b j) (b' i) := fun j => by
    conv_lhs => rw [← h.2 (g' (b' j))]
    simp only [map_sum, map_smul, hg]
  simp only [e1, e2]
  exact Finset.sum_comm
end DualBases
end GlobalTheory.LocWeil.DerComm
