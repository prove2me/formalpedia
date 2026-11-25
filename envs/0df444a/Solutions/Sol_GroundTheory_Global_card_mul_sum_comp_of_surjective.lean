-- Prove2me | solution 1 for GroundTheory.Global.card_mul_sum_comp_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:02.177458+00:00
-- url     : https://prove2.me/submissions/1eaf6200-3ebf-4b0a-b410-105d0d080cfb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G H : Type*} [Group G] [Group H]
namespace GroundTheory.Global
theorem _root_.solution {A B : Type*} [Group A] [Group B] [Fintype A]
    [Fintype B] (ψ : A →* B) (hψ : Function.Surjective ψ) (F : B → ℂ) :
    (Fintype.card B : ℂ) * ∑ a, F (ψ a) = (Fintype.card A : ℂ) * ∑ b, F b := by
  have h1 : ∀ b : B, ∑ a, F (b * ψ a) = ∑ a, F (ψ a) := by
    intro b
    obtain ⟨a₀, rfl⟩ := hψ b
    calc ∑ a, F (ψ a₀ * ψ a) = ∑ a, F (ψ (a₀ * a)) := by simp only [map_mul]
      _ = ∑ a, F (ψ a) := Equiv.sum_comp (Equiv.mulLeft a₀) (fun a => F (ψ a))
  have h2 : ∀ a : A, ∑ b, F (b * ψ a) = ∑ b, F b := fun a =>
    Equiv.sum_comp (Equiv.mulRight (ψ a)) F
  calc (Fintype.card B : ℂ) * ∑ a, F (ψ a) = ∑ _b : B, ∑ a, F (ψ a) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ b : B, ∑ a, F (b * ψ a) := Finset.sum_congr rfl fun b _ => (h1 b).symm
    _ = ∑ a : A, ∑ b, F (b * ψ a) := Finset.sum_comm
    _ = ∑ _a : A, ∑ b, F b := Finset.sum_congr rfl fun a _ => h2 a
    _ = (Fintype.card A : ℂ) * ∑ b, F b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end GroundTheory.Global
