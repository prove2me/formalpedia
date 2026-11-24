-- Prove2me | solution 1 for GlobalTheory.PadicUnitBall.padic_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:10:15.188971+00:00
-- url     : https://prove2.me/submissions/195324d0-0748-4886-a840-b727fc94f303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicMemRangeCompleteDvrPadicAlgCl
import Theorems.Thm_GlobalTheory_PadicUnitBall_padicInt_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicUnitBall
namespace GlobalTheory.PadicUnitBall
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (κ : FractionRing V →+* PadicAlgCl p),
    (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
    ∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range := by
  intro p _ V _ _ _ _ hc κ hV q
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hp
  have hz : ‖q * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact hk.le
  obtain ⟨L, hL⟩ := padicInt_mem_range hc hV (⟨q * (p : ℚ_[p]) ^ k, hz⟩ : ℤ_[p])
  have hpne : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨algebraMap V (FractionRing V) L * (((p : ℕ) : FractionRing V) ^ k)⁻¹, ?_⟩
  rw [map_mul, hL, map_inv₀, map_pow, map_natCast]
  show algebraMap ℚ_[p] (PadicAlgCl p) (q * (p : ℚ_[p]) ^ k) * _ = _
  simp only [map_mul, map_pow, map_natCast]
  field_simp
end GlobalTheory.PadicUnitBall
