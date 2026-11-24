-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.DualBases.quad_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:09.823444+00:00
-- url     : https://prove2.me/submissions/cd5e2a44-a580-4c71-bc8d-8e15aedcebd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_sum_adjoint

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
namespace DualBases
theorem _root_.solution (h : DualBases β b b') (P : Module.End ℂ S) (g g' : U →ₗ[ℝ] U)
    (hP : ∀ u, P * d u = d (g u) * P) (hg : ∀ x y, β (g x) (g y) = β x y) (hg' : ∀ x, g (g' x) = x)
    (hc : ∀ x, g (Y x) = Y (g x)) : P * quad d b b' Y = quad d b b' Y * P := by
  have := h.sum_adjoint ((LinearMap.mul ℝ (Module.End ℂ S)).compl₁₂ (d ∘ₗ Y) (d ∘ₗ g)) g g'
    (fun x y => by rw [← hg, hg'])
  simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.mul_apply', hg'] at this
  rw [quad, Finset.mul_sum]
  conv_rhs => rw [← this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, hP, mul_assoc, hP, hc, mul_assoc]
end DualBases
end GlobalTheory.LocWeil.DerComm
