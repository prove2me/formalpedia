-- Prove2me | solution 1 for LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded_det
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T08:56:18.432365+00:00
-- url     : https://prove2.me/submissions/8189889b-09ae-48ba-8a01-020c17dbbc0f

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122

/-!
# Proposition 2.1's decoder at the combined weakening

`pinsketch_decoding_at_bounded`'s conclusion (bounded `hzeroB` / `hβ2`, `decoderPost`, and the frame
`∀ a ≥ decoderAllocEnd t, s'.mem a = s.mem a`) with `pinsketch_decoding_at_det`'s weakened `det`
hypothesis (agreement with `detStd t N b ι` on `{0,1,2,4,5,6,8,9,10,12} ∪ [detMulBase w, ∞)`).

The proof is the published Definition node
`Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122`, which combines the two
published weakenings at the level of all four stage contracts:

* `P21DetBnd.pinsketch_decoder_readB` — the bounded read stage (published bounded tail + frame),
  re-pointed to `DetAgrees`;
* `P21Bnd.pinsketch_decoder_key_solverB` — the bounded key solver (bounded `hTail` + solver frame),
  re-pointed to `DetAgrees`;
* `pinsketch_decoder_root_search` from `Def_..._P21DetBack20261121` — already at `DetAgrees`;
* `verifierFrameDet` — the verifier *with* its frame at `DetAgrees`, reconstructed from the Back
  bundle's `verifierProcedure_spec` + `finishOutput_spec` (the published
  `pinsketch_decoder_verifier_frame` is stated at `E.det = detStd` only).

The bundle is proved outright: `#print axioms` on `pinsketch_decoding_at_bounded_det` reports
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`); no `sorry`/`admit` occurs in this file, and
the only imports are `Mathlib` and `Definitions.Def_*`.
-/

set_option autoImplicit false

open LinearSetReconciliation327.Main in
/-- Proposition 2.1's decoder at the combined weakening -- submission wrapper. -/
theorem solution {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (s : RAMState) (dt : ℕ → ℕ)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = 0)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < LinearSetReconciliation327.Main.decoderAllocEnd t →
        s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤
      LinearSetReconciliation327.Main.decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w))
    (hdt : (∀ a, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
        a = 12) → dt a = LinearSetReconciliation327.Main.detStd t N b ι a) ∧
      (∀ a, LinearSetReconciliation327.Main.detMulBase w ≤ a →
        dt a = LinearSetReconciliation327.Main.detStd t N b ι a)) :
    ∃ s', LinearSetReconciliation327.Main.HaltsWithin
        (LinearSetReconciliation327.Main.programOfStatement
          (LinearSetReconciliation327.Main.pinsketchRunStmt t w β))
        (LinearSetReconciliation327.Main.detEnv (8 * w) dt)
        (((LinearSetReconciliation327.Main.positiveDecoderBudget t w
          + (24 * LinearSetReconciliation327.Main.wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ)) s s' ∧
      LinearSetReconciliation327.Main.decoderPost (N := N) b ι y s' ∧
      (∀ a, LinearSetReconciliation327.Main.decoderAllocEnd t ≤ a → s'.mem a = s.mem a) :=
  LinearSetReconciliation327.Main.P21DetBndComp.pinsketch_decoding_at_bounded_det b ι y β s dt
    hN ht htN h0 hinj hpc hpayload hpayloadWord hzeroB hβL hβ2 hβfit hdt
