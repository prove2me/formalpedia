-- Prove2me | solution 1 for LexPat.decodeUtf8One_ascii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:48.901491+00:00
-- url     : https://prove2.me/submissions/a10e2f6b-2987-4397-99ca-b4d904863600

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs

set_option autoImplicit true
open LexPat
open LexPat
namespace LexPat
theorem _root_.solution (data : ByteArray) (b : UInt8) (hb : data[0]? = some b)
    (h : b.toNat < 0x80) :
    ∃ (t : Scalar) (next : Nat),
      decodeUtf8One data 0 = .ok (t, next) ∧ t.n = b.toNat ∧ next = 1 := by
  simp only [decodeUtf8One, hb]
  rw [dif_pos h]
  exact ⟨⟨b.toNat, Or.inl (by omega)⟩, 1, by congr 1, rfl, rfl⟩
end LexPat
