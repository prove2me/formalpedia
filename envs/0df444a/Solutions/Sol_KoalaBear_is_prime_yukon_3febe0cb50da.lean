-- Prove2me | solution 1 for KoalaBear.is_prime_yukon_3febe0cb50da
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T05:09:03.113187+00:00
-- url     : https://prove2.me/submissions/40f656df-5039-4848-b51b-de766b0a9975

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module



public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Basic


public import Mathlib
public import Definitions.Def_Yukon_b0cfdbaf70ca87129aa06e66
public import Definitions.Def_Yukon_92052b9f6262f4f17145e198
public import Definitions.Def_Yukon_8b59f57debbd0f7955ae4947
public import Definitions.Def_Yukon_5a1c8f8f8be9100f7eedfb21
public import Theorems.Thm_Tactic_Nat_Prime_of_isNat_yukon_7be3e9103c5e
public import Theorems.Thm_Tactic_ZMod_bla_yukon_0a381eac01d1
public import Theorems.Thm_Tactic_ZMod_blub_yukon_274e400d41f5
public import Definitions.Def_Yukon_20fdbb063a4c0f803b6a5b04
public import Definitions.Def_Yukon_adcae76b85f03179c58a98cf
public import Definitions.Def_Yukon_12578fdadf11b5bb40ff7e00
@[expose] public section
/-!
  # KoalaBear Field `2^{31} - 2^{24} + 1`

  This is the field used for lean Ethereum spec.
-/

@[expose] public section

namespace KoalaBear
-- 2130706433
-- #eval fieldSize
/-- The KoalaBear modulus is prime. -/
theorem _root_.solution : Nat.Prime fieldSize  := (
by
  unfold fieldSize
  refine PrattCertificate.out ⟨3, by reduce_mod_char, ?_⟩
  refine .split (2 ^ 24) 127 ?_ ?_ (by norm_num)
  · exact .prime 2 24 _ prime_2 (by reduce_mod_char; decide) (by norm_num)
  · exact .prime 127 1 _ (by norm_num) (by reduce_mod_char; decide) (by norm_num)
)
end KoalaBear
end
end
