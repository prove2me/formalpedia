-- Prove2me | solution 1 for GlobalTheory.SympTower.exists_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:02:46.432712+00:00
-- url     : https://prove2.me/submissions/bd8b3339-2749-4c01-b35e-2be88b1ec968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompatibleSymplectic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SympTower
namespace GlobalTheory.SympTower
theorem _root_.solution {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    (f : V →ₗ[ZMod n] ZMod n) (h : ∀ c : ZMod n, (∀ y, c * f y = 0) → c = 0) : ∃ y, f y = 1 := by
  haveI : IsPrincipalIdealRing (ZMod n) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range f)).principal
  have hreg : d ∈ nonZeroDivisors (ZMod n) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    apply h
    intro y
    have : f y ∈ Submodule.span (ZMod n) {d} := hd ▸ LinearMap.mem_range_self f y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← ha, smul_eq_mul, mul_left_comm, hc, mul_zero]
  have hu : IsUnit d := IsArtinianRing.isUnit_of_mem_nonZeroDivisors hreg
  have : (1 : ZMod n) ∈ LinearMap.range f := by
    rw [hd]
    obtain ⟨u, rfl⟩ := hu
    exact Submodule.mem_span_singleton.2 ⟨↑u⁻¹, by simp⟩
  exact this
end GlobalTheory.SympTower
