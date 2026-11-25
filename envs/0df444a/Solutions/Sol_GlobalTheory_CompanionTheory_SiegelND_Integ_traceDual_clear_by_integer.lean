-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.traceDual_clear_by_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:57.219843+00:00
-- url     : https://prove2.me/submissions/f1ea505b-f348-424c-ad61-5834634d4da2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TraceDualDenominatorBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ
namespace GlobalTheory.CompanionTheory.SiegelND.Integ
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  intro F _ _
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · intro f hf
    have hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]
      intro x hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      obtain ⟨m, hm⟩ := hf r
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, eq_intCast]
      exact hm.symm
    obtain ⟨o, ho⟩ := hint f hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨c * o, ?_⟩
    rw [Algebra.smul_def] at ho
    show algebraMap (𝓞 F) F (c * o) = _
    rw [map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]
end GlobalTheory.CompanionTheory.SiegelND.Integ
