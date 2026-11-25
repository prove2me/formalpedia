-- Prove2me | solution 1 for GlobalTheory.SplitEmbSep.one_le_norm_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:39.478809+00:00
-- url     : https://prove2.me/submissions/ef3c7a8d-ce36-45c6-8f24-5bbb5a13ff10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField
namespace GlobalTheory.SplitEmbSep
namespace _root_.GlobalTheory.SplitEmbSep
theorem _root_.solution {C : Type*} [NormedField C] [IsUltrametricDist C] {g : ℕ}
    (hg : g.Prime) (hgC : ‖(g : C)‖ < 1) {d : ℤ} (hd : ¬ (g : ℤ) ∣ d) : 1 ≤ ‖(d : C)‖ := by
  obtain ⟨a, b, hab⟩ :=
    ((Nat.prime_iff_prime_int.mp hg).irreducible.coprime_iff_not_dvd).mpr hd
  have hC : (a : C) * (g : C) + (b : C) * (d : C) = 1 := by exact_mod_cast congrArg (Int.cast (R := C)) hab
  have h1 : ‖(a : C) * (g : C)‖ < 1 := by
    rw [norm_mul]
    calc ‖(a : C)‖ * ‖(g : C)‖ ≤ 1 * ‖(g : C)‖ := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one C a
      _ < 1 := by rwa [one_mul]
  have h2 : 1 ≤ max ‖(a : C) * (g : C)‖ ‖(b : C) * (d : C)‖ := by
    rw [← norm_one (α := C), ← hC]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h3 : 1 ≤ ‖(b : C) * (d : C)‖ := by
    rcases le_max_iff.mp h2 with h | h
    · exact absurd h (not_le.mpr h1)
    · exact h
  calc 1 ≤ ‖(b : C)‖ * ‖(d : C)‖ := by rwa [← norm_mul]
    _ ≤ 1 * ‖(d : C)‖ := by
      gcongr
      exact IsUltrametricDist.norm_intCast_le_one C b
    _ = ‖(d : C)‖ := one_mul _
end _root_.GlobalTheory.SplitEmbSep
end GlobalTheory.SplitEmbSep
