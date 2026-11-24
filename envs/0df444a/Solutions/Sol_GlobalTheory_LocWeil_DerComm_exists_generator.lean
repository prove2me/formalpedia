-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:30.678707+00:00
-- url     : https://prove2.me/submissions/dcf4c731-4960-4286-996a-3ac1b5c6490d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_differentiableAt_oneParameter
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_deriv_swap
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_hasDerivAt_move
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_quad_mem
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_quad_comm
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_apply_mem
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_scalar_of_comm

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
variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)
include hs hκ hd hω hG hN hvac hev hline
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution (hb : DualBases β b b') (p : ℝ → Γ) (h0 : p 0 = 1) (hm : ∀ s t, p (s + t) = p s * p t)
    (hc : Continuous fun t => G (p t)) {A : Module.End ℂ S} (hA : A ∈ Algebra.adjoin ℂ (Set.range d))
    (hder : ∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p t) Φ)) (ev w (A Φ)) 0) :
    ∃ Y : U →L[ℝ] U, HasDerivAt (fun t => G (p t)) Y 0 ∧ (∀ x y, β (Y x) y = -β x (Y y)) ∧
      (∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Y u) Φ + d u (A Φ)) ∧
      ∃ c : ℂ, ∀ Φ ∈ N, A Φ = (2 * κ)⁻¹ • quad d b b' Y.toLinearMap Φ + c • Φ := by
  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  have hY := (differentiableAt_oneParameter (fun t => G (p t)) hc (by rw [h0, map_one])
    (fun s t => by rw [hm, map_mul])).hasDerivAt
  set Y := deriv (fun t => G (p t)) 0
  have hYu : ∀ u, HasDerivAt (fun t => G (p t) u) (Y u) 0 := fun u => by
    simpa using hY.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have hdN : ∀ u, ∀ Φ ∈ N, d u Φ ∈ N := fun u => apply_mem hN (Algebra.subset_adjoin ⟨u, rfl⟩)
  have h1 : ∀ x y, β (Y x) y = -β x (Y y) := fun x y => by
    let β' : U →L[ℝ] U →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (U →ₗ[ℝ] ℝ) ≃ₗ[ℝ] U →L[ℝ] ℝ).toLinearMap ∘ₗ β)
    have h2 := (β'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hYu x)).clm_apply (hYu y)
    have h3 := h2.unique ((hasDerivAt_const (0 : ℝ) (β x y)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => hG (p t) x y))
    simp only [Function.comp_apply, h0, map_one, ContinuousLinearMap.one_apply] at h3
    exact eq_neg_of_add_eq_zero_left h3
  have h2 : ∀ u, ∀ Φ ∈ N, A (d u Φ) = d (Y u) Φ + d u (A Φ) := fun u Φ hΦ => by
    have h3 : HasDerivAt (fun t => G (p (-t)) u) (-Y u) 0 := by
      have := HasDerivAt.scomp (0 : ℝ) (by rw [neg_zero]; exact hYu u) (hasDerivAt_neg (0 : ℝ))
      rw [neg_one_smul] at this
      exact this
    have h4 : ∀ t, ω (p t) (d (G (p (-t)) u) Φ) = d u (ω (p t) Φ) := fun t => by
      rw [← Module.End.mul_apply, hω, ← ContinuousLinearMap.mul_apply, ← map_mul, ← hm, add_neg_cancel, h0, map_one]
      rfl
    have h5 : d (-Y u) Φ + A (d u Φ) = d u (A Φ) := hev _ _ fun w => by
      obtain ⟨ℓ, hl0, hl1, hl2⟩ := hline w u
      have h6 : ∀ s, ∀ Ψ ∈ N, HasDerivAt (fun t => ℓ s (ω (p t) Ψ)) (ℓ s (A Ψ)) 0 := fun s Ψ hΨ => by
        obtain ⟨c, w', e⟩ := hl2 s
        simp only [e]
        exact (hder Ψ hΨ w').const_mul c
      rw [← hl0]
      refine deriv_swap ℓ (d u) hl1 (fun t => ω (p t) Φ) _ _ (fun s => h6 s Φ hΦ) fun s => ?_
      have := hasDerivAt_move (ℓ s) d (fun t => ω (p t)) (by rw [h0, map_one]) A Φ
        (fun v => h6 s _ (hdN v Φ hΦ)) h3
      simp only [h4, neg_zero, h0, map_one, ContinuousLinearMap.one_apply] at this
      exact this
    rw [← h5, map_neg, LinearMap.neg_apply, add_neg_cancel_left]
  refine ⟨Y, hY, h1, h2, ?_⟩
  obtain ⟨c, hc⟩ := scalar_of_comm hN hvac (sub_mem hA (Subalgebra.smul_mem _ (quad_mem b b' Y.toLinearMap) (2 * κ)⁻¹))
    (fun u Φ hΦ => by
      have := LinearMap.congr_fun (hb.quad_comm hs hd (Y := Y.toLinearMap) h1 u) Φ
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, sub_eq_iff_eq_add] at this
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, h2 u Φ hΦ, this, smul_add, smul_smul,
        inv_mul_cancel₀ (mul_ne_zero two_ne_zero hκ), one_smul, ContinuousLinearMap.coe_coe]
      abel)
  exact ⟨c, fun Φ hΦ => by rw [← hc Φ hΦ, LinearMap.sub_apply, LinearMap.smul_apply, add_sub_cancel]⟩
end GlobalTheory.LocWeil.DerComm
