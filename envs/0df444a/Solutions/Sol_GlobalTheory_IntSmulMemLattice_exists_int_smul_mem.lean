-- Prove2me | solution 1 for GlobalTheory.IntSmulMemLattice.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:03.908079+00:00
-- url     : https://prove2.me/submissions/60899e99-2841-4a8c-90fd-299b52e651a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulMemLattice
open NumberField
namespace GlobalTheory.IntSmulMemLattice
theorem _root_.solution {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) (hL : Submodule.span E (L : Set V) = ⊤) (v : V) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  have hden : ∀ a : E, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • a) := fun a =>
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
      (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
  have hv : v ∈ Submodule.span E (L : Set V) := by rw [hL]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    have e1 : (m * k) • x = k • (m • x) := by rw [mul_comm, mul_smul]
    have e2 : (m * k) • y = m • (k • y) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact L.add_mem (zsmul_mem hmx k) (zsmul_mem hky m)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := hden a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩

    let b : RingOfIntegers E := ⟨d • a, hint⟩
    have hb : algebraMap (RingOfIntegers E) E b = (d : E) * a := by
      change d • a = (d : E) * a
      rw [zsmul_eq_mul]
    have e : (d * m) • (a • x) = b • (m • x) := by
      rw [← algebraMap_smul E b (m • x), hb, ← Int.cast_smul_eq_zsmul E (d * m),
        ← Int.cast_smul_eq_zsmul E m, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [e]
    exact L.smul_mem b hmx
end GlobalTheory.IntSmulMemLattice
