-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.sum_twist_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:42:48.028677+00:00
-- url     : https://prove2.me/submissions/aaca10f9-391d-45aa-ba76-9bd75e80c620

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_lam_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {G : Type*} [Group G] [Fintype G]
open Classical
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution (H : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hm : ∀ a ∈ H, ∀ b ∈ H, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ H, lam a ≠ 0)
    (y h : G) (hh : h ∈ H) (hc : h * y * h⁻¹ * y⁻¹ ∈ H) (hl : lam (h * y * h⁻¹ * y⁻¹) ≠ 1) :
    (∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0) = 0 := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = h * y * h⁻¹ * y⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc hl
  let e : G ≃ G := (MulAut.conj h).toEquiv.trans (Equiv.mulRight c)
  have he : ∀ u, e u = h * u * h⁻¹ * c := fun u => rfl
  have hmem : ∀ u, e u ∈ H ↔ u ∈ H := by
    intro u
    rw [he]
    constructor
    · intro hu
      have h1 : h⁻¹ * (h * u * h⁻¹ * c * c⁻¹) * h = u := by group
      rw [← h1]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) (H.mul_mem hu (H.inv_mem hc))) hh
    · intro hu
      exact H.mul_mem (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) hc
  have hcne := hne c hc
  have key : (∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0) =
      (lam c)⁻¹ * ∑ u, if u ∈ H then (lam u)⁻¹ * χ (u * y) else 0 := by
    conv_lhs => rw [← Equiv.sum_comp e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ H
    · rw [if_pos ((hmem u).2 hu), if_pos hu]
      have h1 : e u * y = h * (u * y) * h⁻¹ := by
        rw [he, hcdef]; group
      have h2 : lam (e u) = lam u * lam c := by
        rw [he, hm _ (H.mul_mem (H.mul_mem hh hu) (H.inv_mem hh)) _ hc,
          hm _ (H.mul_mem hh hu) _ (H.inv_mem hh), hm _ hh _ hu, lam_inv H lam hm hne h hh]
        have := hne h hh
        field_simp
      rw [h1, hχ, h2, mul_inv]
      ring
    · rw [if_neg (fun h' => hu ((hmem u).1 h')), if_neg hu, mul_zero]
  by_contra hD
  apply hl
  have h3 : (lam c)⁻¹ = 1 := mul_right_cancel₀ hD (by rw [one_mul]; exact key.symm)
  exact inv_eq_one.1 h3
end GlobalTheory.CompanionTheory.RootExch
