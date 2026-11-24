-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.DualBases.quad_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:10.606796+00:00
-- url     : https://prove2.me/submissions/c1080d13-4aec-4b52-81dc-18153308b340

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
theorem _root_.solution (h : DualBases β b b') {N : Submodule ℂ S} (hN : ∀ u, ∀ Φ ∈ N, d u Φ ∈ N)
    (A : Module.End ℂ S) (Z : U →ₗ[ℝ] U) (hA : ∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Z u) Φ + d u (A Φ))
    (hZ : ∀ x y, β (Z x) y = -β x (Z y)) (hc : ∀ x, Z (Y x) = Y (Z x)) :
    ∀ Φ ∈ N, A (quad d b b' Y Φ) = quad d b b' Y (A Φ) := by
  intro Φ hΦ
  have := h.sum_adjoint ((LinearMap.mul ℝ (Module.End ℂ S)).compl₁₂ (d ∘ₗ Y) d) Z (fun x => -Z x)
    (fun x y => by rw [map_neg, LinearMap.neg_apply, hZ, neg_neg])
  simp only [LinearMap.compl₁₂_apply, LinearMap.comp_apply, LinearMap.mul_apply', map_neg, Finset.sum_neg_distrib] at this
  have h2 := LinearMap.congr_fun this Φ
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, Module.End.mul_apply] at h2
  simp only [quad, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hA _ _ (hN _ _ hΦ), hA _ _ hΦ, map_add, hc,
    Finset.sum_add_distrib, h2]
  abel
end DualBases
end GlobalTheory.LocWeil.DerComm
