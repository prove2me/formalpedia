-- Prove2me | solution 1 for GlobalTheory.SaturatedSublattice.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:54:29.383714+00:00
-- url     : https://prove2.me/submissions/47f7b457-f6b4-4074-b799-01af416fbd4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsSide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SaturatedSublattice
open NumberField
namespace GlobalTheory.SaturatedSublattice
theorem _root_.solution : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤ → ∀ (v : Fin n → E), ∃ (D : NumberField.RingOfIntegers E), D ≠ (0 : NumberField.RingOfIntegers E) ∧ D • v ∈ Λ := by
  intro E _ _ n Λ hspan v
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨D1, hD1, h1⟩ := hx
    obtain ⟨D2, hD2, h2⟩ := hy
    refine ⟨D1 * D2, mul_ne_zero hD1 hD2, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem D2 h1
    · rw [mul_smul]; exact Λ.smul_mem D1 h2
  | smul a x _ hx =>
    obtain ⟨D, hD, h⟩ := hx
    obtain ⟨⟨b, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hd
    refine ⟨(d : RingOfIntegers E) * D, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hD, ?_⟩
    have key : ((d : RingOfIntegers E) * D) • (a • x) = b • (D • x) := by
      rw [← algebraMap_smul E ((d : RingOfIntegers E) * D) (a • x), ← algebraMap_smul E b (D • x),
        ← algebraMap_smul E D x, smul_smul, smul_smul, map_mul, ← hd]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem b h
end GlobalTheory.SaturatedSublattice
