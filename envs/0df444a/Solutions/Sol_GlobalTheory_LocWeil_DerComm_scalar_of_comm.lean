-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.scalar_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:57.580611+00:00
-- url     : https://prove2.me/submissions/b280a1ac-6d22-4b0d-be4c-fa86672d2ea2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter
import Theorems.Thm_GlobalTheory_LocWeil_DerComm_apply_mem

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
include hN hvac
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution {B : Module.End ℂ S} (hB : B ∈ Algebra.adjoin ℂ (Set.range d))
    (hc : ∀ u, ∀ Φ ∈ N, B (d u Φ) = d u (B Φ)) : ∃ c : ℂ, ∀ Φ ∈ N, B Φ = c • Φ := by
  have hf : f ∈ N := (hN f).2 ⟨1, one_mem _, rfl⟩
  obtain ⟨c, h⟩ := hvac B hB fun u => hc u f hf
  have key : ∀ a ∈ Algebra.adjoin ℂ (Set.range d), ∀ Φ ∈ N, B (a Φ) = a (B Φ) := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact hc u
    | algebraMap r => exact fun Φ _ => map_smul B r Φ
    | add x y _ _ hx hy => exact fun Φ hΦ => by rw [LinearMap.add_apply, map_add, hx Φ hΦ, hy Φ hΦ, LinearMap.add_apply]
    | mul x y _ hy' hx hy =>
      exact fun Φ hΦ => by rw [Module.End.mul_apply, hx _ (apply_mem hN hy' Φ hΦ), hy Φ hΦ, Module.End.mul_apply]
  refine ⟨c, fun Φ hΦ => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (hN Φ).1 hΦ
  rw [key a ha f hf, h, map_smul]
end GlobalTheory.LocWeil.DerComm
