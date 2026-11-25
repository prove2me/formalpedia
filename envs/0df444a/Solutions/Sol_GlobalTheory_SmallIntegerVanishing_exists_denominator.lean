-- Prove2me | solution 1 for GlobalTheory.SmallIntegerVanishing.exists_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:59.399794+00:00
-- url     : https://prove2.me/submissions/aa1b5985-5e58-4dad-ac35-a78c690cff6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SmallIntegerVanishing
namespace GlobalTheory.SmallIntegerVanishing
theorem _root_.solution (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun g => Finset.univ.image fun a => g a)
  refine ⟨(y : RingOfIntegers E), by exact_mod_cast hy0, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    have hint := hy (g a) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨y • g a, hint⟩, ?_⟩
    simp [zsmul_eq_mul]
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    obtain ⟨x2, h2⟩ := hw a
    refine ⟨x1 + x2, ?_⟩
    calc ((x1 + x2 : RingOfIntegers E) : E) = (x1 : E) + (x2 : E) := rfl
      _ = _ := by rw [h1, h2, Pi.add_apply, mul_add]
  | smul r u _ hu =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    refine ⟨r * x1, ?_⟩
    calc ((r * x1 : RingOfIntegers E) : E) = (r : E) * (x1 : E) := rfl
      _ = (r : E) * (((y : RingOfIntegers E) : E) * u a) := by rw [h1]
      _ = ((y : RingOfIntegers E) : E) * (r • u) a := by
        rw [Pi.smul_apply, Algebra.smul_def]
        show _ = _ * ((r : E) * u a)
        ring
end GlobalTheory.SmallIntegerVanishing
