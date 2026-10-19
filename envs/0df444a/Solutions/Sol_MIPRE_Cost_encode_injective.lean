-- Prove2me | solution 1 for MIPRE.Cost.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:28.776729+00:00
-- url     : https://prove2.me/submissions/b1c90c64-0ce3-4c81-8a27-af3bf47c49a0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Encoding.lean (solution of MIPRE.Cost.encode_injective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
theorem _root_.solution {α : Type*} [SizedEncoding α] : Function.Injective (encode : α → Data) := by
  intro a b h
  have := SizedEncoding.decode_encode a
  rw [h, SizedEncoding.decode_encode] at this
  exact (Option.some.inj this).symm
end MIPRE.Cost
