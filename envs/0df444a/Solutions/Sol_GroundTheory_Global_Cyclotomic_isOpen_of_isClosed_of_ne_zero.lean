-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isOpen_of_isClosed_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:49.497232+00:00
-- url     : https://prove2.me/submissions/04ea35ba-7894-4acb-ba5a-8e725ea626de

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Theorems.Thm_GroundTheory_Global_Cyclotomic_mul_mem_of_isClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ]))
    {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) : IsOpen (H : Set ℤ_[ℓ]) := by
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, x = u * (ℓ : ℤ_[ℓ]) ^ x.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hx0⟩
  set v := x.valuation
  rw [Metric.isOpen_iff]
  intro y hy
  refine ⟨(ℓ : ℝ) ^ (-(v : ℤ)), zpow_pos (by exact_mod_cast hℓ.out.pos) _, fun w hw => ?_⟩
  have h1 : w - y ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ v} :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 (by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hw).le)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : x * (↑u⁻¹ * t) = w - y := by
    rw [← ht, hu, show (u : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ v * (↑u⁻¹ * t) =
      ((u : ℤ_[ℓ]) * ↑u⁻¹) * t * (ℓ : ℤ_[ℓ]) ^ v by ring, Units.mul_inv, one_mul]
  have h3 : w - y ∈ H := h2 ▸ mul_mem_of_isClosed H hH hx _
  have := H.add_mem h3 hy
  rwa [sub_add_cancel] at this
end GroundTheory.Global.Cyclotomic
