-- Prove2me | solution 1 for LexPat.decodeUtf8One_rejects_overlong_two_byte
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:49.311643+00:00
-- url     : https://prove2.me/submissions/40fd5a98-e914-4a4c-a96d-2ad6e71be56c

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs

set_option autoImplicit true
open LexPat
open LexPat
namespace LexPat
theorem _root_.solution (data : ByteArray) (i : Nat) (b : UInt8)
    (hb : data[i]? = some b) (hlead : b = 0xC0 ∨ b = 0xC1) :
    ∃ off, decodeUtf8One data i = .error { reason := .overlong, offset := off } := by
  rcases hlead with rfl | rfl
  · exact ⟨i, by unfold decodeUtf8One; rw [hb]; rfl⟩
  · exact ⟨i, by unfold decodeUtf8One; rw [hb]; rfl⟩
end LexPat
