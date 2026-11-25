-- Prove2me | solution 1 for GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:56:03.175749+00:00
-- url     : https://prove2.me/submissions/6cab0f10-c7be-47c4-aeee-976f93bf0d63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntSmulMemSubmodule
namespace GlobalTheory.IntSmulMemSubmodule
theorem _root_.solution {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hdc⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hdc⟩
    have h : (d * a) • (c • x) = r • (a • x) := by
      have h1 : r • (a • x) = (d • c) • (a • x) := rfl
      rw [h1, smul_assoc, mul_smul, smul_comm a c x]
    rw [h]
    exact L.smul_mem r hax
end GlobalTheory.IntSmulMemSubmodule
