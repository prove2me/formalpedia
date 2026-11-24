-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.quad_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:55.425329+00:00
-- url     : https://prove2.me/submissions/dae2783c-5820-4096-889d-6860e0749314

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
variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution (b b' : ι → U) (Y : U →ₗ[ℝ] U) : quad d b b' Y ∈ Algebra.adjoin ℂ (Set.range d) :=
  sum_mem fun _ _ => mul_mem (Algebra.subset_adjoin ⟨_, rfl⟩) (Algebra.subset_adjoin ⟨_, rfl⟩)
end GlobalTheory.LocWeil.DerComm
