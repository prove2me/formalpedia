-- Prove2me | solution 1 for LexPat.scalar_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:48.424582+00:00
-- url     : https://prove2.me/submissions/7985b41b-9182-4d57-9bf1-74aa9eff075e

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs

set_option autoImplicit true
open LexPat
open LexPat
namespace LexPat
theorem _root_.solution {t s : Scalar} (h : t.n = s.n) : t = s := by
  cases t
  cases s
  simp only [Scalar.mk.injEq] at h ⊢
  exact h
end LexPat
