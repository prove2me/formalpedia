-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.claim_6_2_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:44.094861+00:00
-- url     : https://prove2.me/submissions/34da348e-dbb0-4abc-8d10-82a669ff26f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency
import Definitions.Def_ITPIRPreproc_MatchVec_OfflineEfficiency
import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4_offline
import Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4_streaming

open scoped ENNReal

open ITPIRPreproc.MatchVec
open ITPIRPreproc.MatchVec.WordRAM
open ITPIRPreproc.MatchVec.OCHPImpl

theorem solution :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ (C : ℝ) (c : ℕ),
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        ∃ (I : OCHPImpl (actFamily dim u v)) (hintProg : Program),
          Deterministic hintProg ∧
          ∀ h : ℕ, 3 ≤ h →
            (Function.Injective (I.encKey (2 ^ h)) ∧
              ∀ K, (I.encKey (2 ^ h) K).length = (h + 1) * dim h) ∧
            (Function.Injective (I.encHint (2 ^ h)) ∧
              ∀ z, (I.encHint (2 ^ h) z).length = 2 * dim h) ∧
            (Function.Injective (I.encAns (2 ^ h)) ∧
              ∀ a, (I.encAns (2 ^ h) a).length = 2 * dim h) ∧
            I.Efficient (2 ^ h) (C * h * dim h) (C * dim h * (h : ℝ) ^ c) (C * h * dim h)
              (C * h * dim h) (C * 2 ^ h * dim h * (h : ℝ) ^ c) ((h + 1) * dim h) (2 * dim h) ∧
            ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (K : (actFamily dim u v (2 ^ h)).Key),
              let inp := encNat (2 ^ h) ++ encBits (I.encKey (2 ^ h) K) ++ List.ofFn D
              Halts hintProg inp zeroTape ∧
              output hintProg inp zeroTape =
                I.encHint (2 ^ h) ((actFamily dim u v (2 ^ h)).hint D K) ∧
              (cost hintProg inp zeroTape : ℝ) ≤ C * 2 ^ h * dim h * (h : ℝ) ^ c := by
  intro C₀ c₀
  obtain ⟨C, c, hC, hc, hoff⟩ := claim_6_2_4_offline C₀ c₀
  refine ⟨C, c, ?_⟩
  intro dim u v vecProg tableProg hmv hcomp
  obtain ⟨I, hintProg, hdet, ho⟩ := hoff dim u v vecProg tableProg hmv hcomp
  obtain ⟨si, sc, hsi, hsc, hs⟩ := claim_6_2_4_streaming C₀ c₀ C c hC hc
    dim u v vecProg tableProg I hmv hcomp (fun h hh => (ho h hh).2.2.2.1)
  refine ⟨I.withStreams si sc, hintProg, hdet, fun h hh => ?_⟩
  refine ⟨(ho h hh).1, (ho h hh).2.1, (ho h hh).2.2.1, hs h hh, ?_⟩
  exact (ho h hh).2.2.2.2
