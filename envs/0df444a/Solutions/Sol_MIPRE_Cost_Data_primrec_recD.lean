-- Prove2me | solution 1 for MIPRE.Cost.Data.primrec_recD
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:37:18.821228+00:00
-- url     : https://prove2.me/submissions/e4a3f4ab-3800-4a09-930f-beeced20796a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Codable.lean (solution of MIPRE.Cost.Data.primrec_recD);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Codable

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem encode_eq (d : Data) : Encodable.encode d = encodeNat d := rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem ofNat_eq (n : ℕ) : Denumerable.ofNat Data n = decodeNat n := by
  have h := Denumerable.decode_eq_ofNat Data n
  rw [show (Encodable.decode n : Option Data) = some (decodeNat n) from rfl] at h
  exact (Option.some.inj h).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_decodeNat : Primrec decodeNat := (Primrec.ofNat Data).of_eq ofNat_eq
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
private theorem getD_range_map {σ : Type*} [Inhabited σ] (F : ℕ → σ) {n i : ℕ} (hi : i < n) :
    ((List.range n).map F).getD i default = F i := by
  simp [List.getD_eq_getElem?_getD, hi]
end MIPRE.Cost.Data

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Data
theorem solution {σ : Type*} [Primcodable σ] [Inhabited σ] (base : σ)
    (step : Data → Data → σ → σ → σ)
    (hstep : Primrec fun p : (Data × Data) × σ × σ => step p.1.1 p.1.2 p.2.1 p.2.2) :
    Primrec (recD base step) := by
  have hlen : Primrec fun p : Unit × List σ => p.2.length := Primrec.list_length.comp Primrec.snd
  have hidx : Primrec fun p : Unit × List σ => Nat.unpair (Nat.pred p.2.length) :=
    Primrec.unpair.comp (Primrec.pred.comp hlen)
  have h1 : Primrec fun p : Unit × List σ => decodeNat (Nat.unpair (Nat.pred p.2.length)).1 :=
    primrec_decodeNat.comp (Primrec.fst.comp hidx)
  have h2 : Primrec fun p : Unit × List σ => decodeNat (Nat.unpair (Nat.pred p.2.length)).2 :=
    primrec_decodeNat.comp (Primrec.snd.comp hidx)
  have h3 : Primrec fun p : Unit × List σ =>
      p.2.getD (Nat.unpair (Nat.pred p.2.length)).1 default :=
    (Primrec.list_getD default).comp Primrec.snd (Primrec.fst.comp hidx)
  have h4 : Primrec fun p : Unit × List σ =>
      p.2.getD (Nat.unpair (Nat.pred p.2.length)).2 default :=
    (Primrec.list_getD default).comp Primrec.snd (Primrec.snd.comp hidx)
  have hg' : Primrec₂ fun (_ : Unit) (l : List σ) =>
      if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default) :=
    Primrec.ite (PrimrecRel.comp Primrec.eq hlen (Primrec.const 0)) (Primrec.const base)
      (hstep.comp (Primrec.pair (Primrec.pair h1 h2) (Primrec.pair h3 h4)))
  have hg : Primrec₂ fun (_ : Unit) (l : List σ) =>
      some (if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default)) :=
    Primrec₂.option_some_iff.2 hg'
  have H : ∀ (_ : Unit) (n : ℕ),
      (fun (_ : Unit) (l : List σ) => some (if l.length = 0 then base else
        step (decodeNat (Nat.unpair (Nat.pred l.length)).1)
          (decodeNat (Nat.unpair (Nat.pred l.length)).2)
          (l.getD (Nat.unpair (Nat.pred l.length)).1 default)
          (l.getD (Nat.unpair (Nat.pred l.length)).2 default))) ()
        ((List.range n).map fun m => recD base step (decodeNat m)) =
      some (recD base step (decodeNat n)) := by
    intro _ n
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.length_map, List.length_range, Nat.pred_succ, Nat.succ_ne_zero,
        if_false, decodeNat_succ, recD_cons]
      rw [getD_range_map _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
        getD_range_map _ (Nat.lt_succ_of_le (Nat.unpair_right_le n))]
  have := Primrec.nat_strong_rec (fun (_ : Unit) n => recD base step (decodeNat n)) hg H
  refine (this.comp (Primrec.const ()) Primrec.encode).of_eq fun d => ?_
  rw [encode_eq, decodeNat_encodeNat]
