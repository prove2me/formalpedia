-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.der_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:36.724712+00:00
-- url     : https://prove2.me/submissions/24fea721-82ae-4a6c-8595-4e5f22cb8e61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_exists_dualBases
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_quad_group
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_DualBases_quad_lie
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_commute_deriv
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_apply_mem
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_exists_generator

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
include hβ hs hκ hd hω hG hN hvac hev hline
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution (p : ℝ → Γ) (h0 : p 0 = 1) (hm : ∀ s t, p (s + t) = p s * p t)
    (hc : Continuous fun t => G (p t)) {A : Module.End ℂ S} (hA : A ∈ Algebra.adjoin ℂ (Set.range d))
    (hder : ∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p t) Φ)) (ev w (A Φ)) 0) :
    (∀ k, (∀ t, Commute k (p t)) → (∀ Φ ∈ N, ω k Φ ∈ N) → ∀ Φ ∈ N, A (ω k Φ) = ω k (A Φ)) ∧
    ∀ p' : ℝ → Γ, p' 0 = 1 → (∀ s t, p' (s + t) = p' s * p' t) → (Continuous fun t => G (p' t)) →
      ∀ A' ∈ Algebra.adjoin ℂ (Set.range d),
      (∀ Φ ∈ N, ∀ w, HasDerivAt (fun t => ev w (ω (p' t) Φ)) (ev w (A' Φ)) 0) → (∀ s t, Commute (p s) (p' t)) →
      ∀ Φ ∈ N, A (A' Φ) = A' (A Φ) := by
  obtain ⟨n, b, b', hb⟩ := exists_dualBases β hβ hs
  obtain ⟨Y, hY, -, -, c, hc⟩ := exists_generator ω G ev hs hκ hd hω hG hN hvac hev hline hb p h0 hm hc hA hder
  refine ⟨fun k hk hkN Φ hΦ => ?_, fun p' h0' hm' hc' A' hA' hder' hcc Φ hΦ => ?_⟩
  · have h1 := commute_deriv hY fun t => (hk t).map G
    have h2 := hb.quad_group (Y := Y.toLinearMap) (ω k) (G k).toLinearMap (G k⁻¹).toLinearMap (hω k) (hG k)
      (fun x => by
        change (G k * G k⁻¹) x = x
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl) fun x => ContinuousLinearMap.ext_iff.1 h1 x
    rw [hc _ (hkN Φ hΦ), hc Φ hΦ, map_add, map_smul, map_smul, ← Module.End.mul_apply, ← h2, Module.End.mul_apply]
  · obtain ⟨Z, hZ, h1, h2, -⟩ := exists_generator ω G ev hs hκ hd hω hG hN hvac hev hline hb p' h0' hm' hc' hA' hder'
    have h3 := commute_deriv hY fun s => (commute_deriv hZ fun t => (hcc s t).map G).symm
    have h4 := hb.quad_lie (Y := Y.toLinearMap) (fun u => apply_mem hN (Algebra.subset_adjoin ⟨u, rfl⟩)) A'
      Z.toLinearMap h2 h1 (fun x => ContinuousLinearMap.ext_iff.1 h3 x) Φ hΦ
    rw [hc _ (apply_mem hN hA' Φ hΦ), hc Φ hΦ, map_add, map_smul, map_smul, h4]
end GlobalTheory.LocWeil.DerComm
