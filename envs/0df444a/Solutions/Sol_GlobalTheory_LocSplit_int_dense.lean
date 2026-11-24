-- Prove2me | solution 1 for GlobalTheory.LocSplit.int_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:08.088929+00:00
-- url     : https://prove2.me/submissions/4dd7e438-66f5-4c95-bc66-d1e1fb1376e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_GlobalTheory_LocSplit_val_eq_of
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
namespace GlobalTheory.LocSplit
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] (w : HeightOneSpectrum R) (g : ℕ)
    (h1 : (g : R) ∈ w.asIdeal) (h2 : (g : R) ∉ w.asIdeal ^ 2)
    (h3 : ∀ x : R, ∃ m : ℤ, x - m ∈ w.asIdeal) (x : R) (n : ℕ) :
    ∃ m : ℤ, x - m ∈ w.asIdeal ^ n := by
  have hv := val_eq_of w _ h1 h2
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    have hn : (g : R) ^ n ∉ w.asIdeal ^ (n + 1) := by
      rw [← w.intValuation_le_pow_iff_mem, map_pow, hv, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
      simp
    haveI := w.isPrime
    obtain ⟨d, e, he, hde⟩ := Ideal.exists_mul_add_mem_pow_succ w.ne_bot ((g : R) ^ n) (x - m)
      (Ideal.pow_mem_pow h1 n) hn hm
    obtain ⟨c, hc⟩ := h3 d
    refine ⟨m + g ^ n * c, ?_⟩
    have : x - ((m + g ^ n * c : ℤ) : R) = (g : R) ^ n * (d - c) + e := by
      push_cast; linear_combination -hde
    rw [this]
    refine Ideal.add_mem _ ?_ he
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow h1 n) hc
end GlobalTheory.LocSplit
