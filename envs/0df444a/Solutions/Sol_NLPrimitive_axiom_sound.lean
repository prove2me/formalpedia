-- Prove2me | solution 1 for NLPrimitive.axiom_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:23.337629+00:00
-- url     : https://prove2.me/submissions/2a22ff79-d8e6-4277-8326-d97eb2889d0d

import Std
import Definitions.Def_NLPrimitive

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution {α : Type} (M : Matrix α) (v : Nat → α)
    {a : Formula} (h : Axiom a) : M.D (eval M.op v a) := by
  cases h with
  | a1 a => exact M.a1 (eval M.op v a)
  | a2 a b => exact M.a2 (eval M.op v a) (eval M.op v b)
  | a3 a => exact M.a3 (eval M.op v a)
  | a4 a b => exact M.a4 (eval M.op v a) (eval M.op v b)
  | a5 a b c => exact M.a5 (eval M.op v a) (eval M.op v b) (eval M.op v c)
  | a6 a b => exact M.a6 (eval M.op v a) (eval M.op v b)
  | a7 a b c => exact M.a7 (eval M.op v a) (eval M.op v b) (eval M.op v c)
end NLPrimitive
