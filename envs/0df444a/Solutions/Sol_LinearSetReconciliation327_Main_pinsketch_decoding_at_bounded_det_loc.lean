-- Prove2me | solution 1 for LinearSetReconciliation327.Main.pinsketch_decoding_at_bounded_det_loc
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T09:07:45.146794+00:00
-- url     : https://prove2.me/submissions/494b2e56-95c1-4e4b-9479-7d7aafda2ce3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122

/-!
# Residual B for Theorem 6.5's row stage: where the decoder's output list lives

`decoderPost` bounds nothing about the *location* of the output list: it only says that
`outList s'` (the `s'.regs 1` words starting at `s'.regs 0`) is a duplicate-free enumeration of the
support of the decoded `x`.  `RepackPre`'s `listBase + len ≤ rowSlot j` therefore cannot be
discharged from it.

The decoder's own construction gives the missing bound.  The 9-instruction finish block
(`finishOutputCode = metaReadCode r0 85 ++ metaReadCode r1 101 ++ metaReadCode r2 100`) loads
`r0 := decoderOutputBase t`, `r1 := (root count) ≤ t`, `r2 := flag`, and does not touch memory; the
verifier has already established `output base = decoderOutputBase t`, `count ≤ t` and
`decoderOutputBase t + t ≤ decoderAllocEnd t`.  Hence `s'.regs r0 + s'.regs r1 ≤ decoderAllocEnd t`.

The proof is the published Definition node
`Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122`
(theorem `pinsketch_decoding_at_bounded_det_loc`), which carries the bound as a fourth conjunct of
the combined decoder contract; its verifier stage is the `DetAgrees` reconstruction
`verifierFrameDet` in the same node.
-/

set_option autoImplicit false

open LinearSetReconciliation327.Main in
/-- Residual B: the decoder's output list lives inside the decoder's scratch -- submission wrapper. -/
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
      (∀ a, LinearSetReconciliation327.Main.decoderAllocEnd t ≤ a → s'.mem a = s.mem a) ∧
      s'.regs r0 + s'.regs r1 ≤ LinearSetReconciliation327.Main.decoderAllocEnd t :=
  LinearSetReconciliation327.Main.P21DetBndComp.pinsketch_decoding_at_bounded_det_loc b ι y β s dt
    hN ht htN h0 hinj hpc hpayload hpayloadWord hzeroB hβL hβ2 hβfit hdt
