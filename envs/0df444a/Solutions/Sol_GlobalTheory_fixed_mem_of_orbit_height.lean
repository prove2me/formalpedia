-- Prove2me | solution 1 for GlobalTheory.fixed_mem_of_orbit_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:36.262678+00:00
-- url     : https://prove2.me/submissions/1f7a686e-0e6f-41fb-9e53-a4c9052ea9a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
import Theorems.Thm_GlobalTheory_GradedFixed_WA_mono
import Theorems.Thm_GlobalTheory_GradedFixed_iSup_orbit
import Theorems.Thm_GlobalTheory_GradedFixed_orbit_stable
import Theorems.Thm_GlobalTheory_GradedFixed_fixed_part
import Theorems.Thm_GlobalTheory_GradedFixed_exists_comp
import Theorems.Thm_GlobalTheory_GradedFixed_comp_outside
import Theorems.Thm_GlobalTheory_GradedFixed_mem_WA_of_sum
import Theorems.Thm_GlobalTheory_GradedFixed_mem_span_of_fixed
import Theorems.Thm_GlobalTheory_GradedFixed_mem_of_orbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory
open GlobalTheory.GradedFixed
namespace GlobalTheory
theorem _root_.solution : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  intro G ι M _ _ _ _ π V hV htop hline hπ μ hμ S hS hstep
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_comp V hV htop
  have hsum : ∀ (p : ι → Prop) (u : M), (∀ l, ¬ p l → c l u = 0) →
      (∀ i, p i → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
      (∀ g, π g u = u) → u ∈ S := by
    classical
    intro p u hp hgood hu
    obtain ⟨F, hF⟩ := hc4 u
    have hF' : u = ∑ j ∈ F.filter p, c j u := by
      rw [Finset.sum_filter_of_ne (fun j _ h => by_contra fun hpj => h (hp j hpj))]
      exact hF
    refine mem_of_orbits π V hV hπ S (F.filter p)
      (fun j hj => hgood j (Finset.mem_filter.mp hj).2) u hu ?_
    exact mem_WA_of_sum V c hc1 hc3
      (fun j hj => Set.mem_iUnion₂.mpr ⟨j, hj, (mem_orbit_self j : j ∈ orbit G j)⟩) u hF'
  have key : ∀ m i, μ i = m → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi x hx hxO
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem S
    obtain ⟨v, hvS, u, hu, hvu, hvu0⟩ := hstep i ⟨x, hx0, hx, by rw [iSup_orbit]; exact hxO⟩
    rw [iSup_orbit] at hvu
    have huW : u ∈ WA V {j | μ j < μ i} := hu
    have hsub : {j | μ j < μ i} ⊆ (orbit G i)ᶜ := by
      intro j hj hjO
      obtain ⟨g, rfl⟩ := hjO
      simp [hμ] at hj
    have hcompl : ∀ (g : G), ∀ j ∈ (orbit G i)ᶜ, g • j ∈ (orbit G i)ᶜ :=
      fun g j hj hgj => hj (by simpa using orbit_stable i g⁻¹ hgj)
    have hfa : ∀ g, π g (v - u) = v - u :=
      fixed_part π V hV hπ (fun g j hj => orbit_stable i g hj) hcompl disjoint_compl_right hvu
        (WA_mono V hsub huW) (fun g => by rw [sub_add_cancel]; exact hS v hvS g)
    have hufix : ∀ g, π g u = u := fun g => by
      have h1 := hfa g
      rw [map_sub, hS v hvS g] at h1
      exact sub_right_injective h1
    have huS : u ∈ S := hsum (fun j => μ j < μ i) u (fun l hl => comp_outside V c hc3 huW hl)
      (fun j hj => ih (μ j) (hi ▸ hj) j rfl) hufix
    have hvuS : v - u ∈ S := sub_mem hvS huS
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (mem_span_of_fixed π V c hc1 hc2 hc3 hc4 hπ hline i hx hfa hxO hvu hvu0)
    rw [← hr]
    exact S.smul_mem r hvuS
  intro w hw
  exact hsum (fun _ => True) w (fun l hl => absurd trivial hl) (fun i _ => key (μ i) i rfl) hw
end GlobalTheory
