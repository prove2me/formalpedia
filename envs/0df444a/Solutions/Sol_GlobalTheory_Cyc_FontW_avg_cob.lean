-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.avg_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:40:48.496129+00:00
-- url     : https://prove2.me/submissions/2c429063-d65d-42bc-89a3-9ba1082c99ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
import Theorems.Thm_GlobalTheory_Cyc_FontW_mem_Dv
import Theorems.Thm_GlobalTheory_Cyc_FontW_Dv_map
import Theorems.Thm_GlobalTheory_Cyc_FontW_avg_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution (hM : Cpl l M) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) : ∃ b, ∀ g, c g = ρ g b - b := by
  let P : ℕ → M → Prop := fun k b => (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l k M
  have h0 : P 0 0 := ⟨by simpa using hcont, fun g => mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
  have hstep : ∀ k b, P k b → ∃ b', P (k + 1) b' ∧ b' - b ∈ Dv l k M := by
    intro k b hb
    obtain ⟨d, hd, h1, h2⟩ := avg_step l 𝓕 a ρ amul ρmul semi htr (fun g => c g - (ρ g b - b))
      (fun g h => by simp only [hc, ρmul, map_sub]; abel) hb.1 k hb.2
    have e : ∀ g, c g - (ρ g (b + d) - (b + d)) = c g - (ρ g b - b) - (ρ g d - d) := fun g => by
      rw [map_add]; abel
    refine ⟨b + d, ⟨?_, ?_⟩, by simpa using hd⟩
    · simpa only [e] using h1
    · simpa only [e] using h2
  choose nx hnx using hstep
  let f : (k : ℕ) → {b // P k b} := fun k =>
    Nat.rec ⟨0, h0⟩ (fun k b => ⟨nx k b.1 b.2, (hnx k b.1 b.2).1⟩) k
  obtain ⟨L, hL⟩ := hM.2 (fun k => (f k).1) fun k => (hnx k (f k).1 (f k).2).2
  refine ⟨L, fun g => sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : c g - (ρ g L - L) = (c g - (ρ g (f r).1 - (f r).1)) - (ρ g (L - (f r).1) - (L - (f r).1)) := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem ((f r).2.2 g) (sub_mem (Dv_map _ (hL r)) (hL r))
end GlobalTheory.Cyc.FontW
