-- Prove2me | solution 1 for LexPat.decodeUtf8One_ascii_roundtrip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:12.763846+00:00
-- url     : https://prove2.me/submissions/b41b007b-3475-4c25-8cc9-b7f5f1d70786

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs
import Theorems.Thm_LexPat_scalar_ext
import Theorems.Thm_LexPat_decodeUtf8One_ascii

set_option autoImplicit true
open LexPat
open LexPat
namespace LexPat
theorem _root_.solution (s : Scalar) (h : s.n < 0x80) :
    decodeUtf8One (encodeAscii s) 0 = .ok (s, 1) := by
  have h0 : (encodeAscii s)[0]? = some (UInt8.ofNat s.n) := rfl
  have hn : (UInt8.ofNat s.n).toNat = s.n := by
    rw [UInt8.toNat_ofNat']
    omega
  have hlt : (UInt8.ofNat s.n).toNat < 0x80 := by rw [hn]; exact h
  obtain ⟨t, next, hdec, ht, hnext⟩ :=
    decodeUtf8One_ascii (encodeAscii s) (UInt8.ofNat s.n) h0 hlt
  have hts : t.n = s.n := by rw [ht, hn]
  rw [hdec, scalar_ext hts, hnext]
end LexPat
