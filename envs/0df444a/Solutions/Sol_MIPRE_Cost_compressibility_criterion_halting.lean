-- Prove2me | solution 1 for MIPRE.Cost.compressibility_criterion_halting
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:43:35.929325+00:00
-- url     : https://prove2.me/submissions/f87e23a2-87e0-45e3-aee5-24260cbbd402

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.compressibility_criterion_halting);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression
import Theorems.Thm_MIPRE_Cost_Data_primrec_recD
import Theorems.Thm_MIPRE_Cost_Machine_mem_evalData_iff
import Theorems.Thm_MIPRE_Cost_compressibility_criterion
import Theorems.Thm_MIPRE_Cost_exists_compile

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem primrec_cons : Primrec₂ Data.cons := by
  refine Primrec₂.encode_iff.1 ?_
  refine (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.encode.comp Primrec.snd))).of_eq ?_
  rintro ⟨a, b⟩
  rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem encodeNat_left (d : Data) : encodeNat (left d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).1 := by
  cases d <;> simp [Nat.unpair_pair]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem encodeNat_right (d : Data) : encodeNat (right d) =
    if encodeNat d = 0 then 0 else (Nat.unpair (Nat.pred (encodeNat d))).2 := by
  cases d <;> simp [Nat.unpair_pair]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_left : Primrec left := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_left d).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_right : Primrec right := by
  refine Primrec.encode_iff.1 ?_
  refine (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.encode (Primrec.const 0))
    (Primrec.const 0)
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.pred.comp Primrec.encode)))).of_eq ?_
  intro d
  exact (encodeNat_right d).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_unaryToNat : Primrec unaryToNat :=
  primrec_recD 0 _ (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_getList : Primrec₂ getList :=
  primrec_left.comp (Primrec.nat_iterate Primrec.snd Primrec.fst
    (primrec_right.comp Primrec.snd).to₂)
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem toBool?_eq (d : Data) : toBool? d =
    if d = nil then some false else if d = cons nil nil then some true else none := by
  rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩ <;> simp [toBool?]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_toBool? : Primrec toBool? :=
  (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const nil))
    (Primrec.const (some false))
    (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const (cons nil nil)))
      (Primrec.const (some true)) (Primrec.const none))).of_eq fun d => (toBool?_eq d).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem toList?_eq_recD {α : Type*} (g : Data → Option α) (d : Data) :
    toList? g d = recD (some []) (fun a _ _ rb => (g a).bind fun x => rb.map (x :: ·)) d := by
  induction d with
  | nil => rfl
  | cons a d _ ihd =>
    rw [recD_cons, ← ihd]
    simp only [toList?]
    cases g a <;> cases toList? g d <;> rfl
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
theorem primrec_toList? {α : Type*} [Primcodable α] {g : Data → Option α} (hg : Primrec g) :
    Primrec (toList? g) := by
  have hstep : Primrec fun p : (Data × Data) × Option (List α) × Option (List α) =>
      (g p.1.1).bind fun x => p.2.2.map (x :: ·) :=
    Primrec.option_bind (hg.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  exact (primrec_recD (some []) _ hstep).of_eq fun d => (toList?_eq_recD g d).symm
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
/-- Decoding bit strings from `Data` is primitive recursive. -/
theorem primrec_decode_bitStr :
    Primrec fun d : Data => (SizedEncoding.decode d : Option BitStr) :=
  primrec_toList? primrec_toBool?
end MIPRE.Cost.Data

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_evD : Primrec evD := Data.primrec_cons.comp (const Data.nil) Primrec.id
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_retD : Primrec retD := Data.primrec_cons.comp (const (Data.cons .nil .nil)) Primrec.id
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
/-- `p ↦ unaryToNat p.left`, the tag of an encoded program or frame. -/
theorem primrec_tag : Primrec fun d : Data => Data.unaryToNat d.left :=
  Data.primrec_unaryToNat.comp Data.primrec_left
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_stepEv : Primrec fun q : Data × Data × Data => stepEv q.1 q.2.1 q.2.2 := by
  have hp : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have htag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.1.left := primrec_tag.comp hp
  have hbody : Primrec fun q : Data × Data × Data => q.1.right := Data.primrec_right.comp hp
  have hget0 : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp hbody)
  have hgetE : Primrec fun q : Data × Data × Data =>
      Data.getList q.2.1 (Data.unaryToNat q.1.right.left) :=
    Data.primrec_getList.comp henv (Data.primrec_unaryToNat.comp (Data.primrec_left.comp hbody))
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data => Data.unaryToNat q.1.left = n :=
    fun n => PrimrecRel.comp Primrec.eq htag (const n)
  refine Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
    (Primrec.ite (heq 3) ?_ (Primrec.ite (heq 4) ?_ (Primrec.ite (heq 5) ?_ ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hget0) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 0))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · refine Primrec.ite (PrimrecRel.comp Primrec.eq hgetE (const Data.nil)) ?_ ?_
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_left.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp henv hk)
    · exact Data.primrec_cons.comp
        (primrec_evD.comp (Data.primrec_right.comp (Data.primrec_right.comp hbody)))
        (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_left.comp hgetE)
          (Data.primrec_cons.comp (Data.primrec_right.comp hgetE) henv)) hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp (Data.primrec_left.comp hbody))
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 2))
          (Data.primrec_cons.comp (Data.primrec_right.comp hbody) henv)) hk))
  · exact Data.primrec_cons.comp (primrec_evD.comp hbody)
      (Data.primrec_cons.comp henv (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 3)) (Data.primrec_cons.comp hbody henv)) hk))
  · exact Data.primrec_cons.comp (primrec_retD.comp hbody) (Data.primrec_cons.comp henv hk)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_stepRet : Primrec fun q : Data × Data × Data => stepRet q.1 q.2.1 q.2.2 := by
  have hv : Primrec fun q : Data × Data × Data => q.1 := fst
  have henv : Primrec fun q : Data × Data × Data => q.2.1 := fst.comp snd
  have hk : Primrec fun q : Data × Data × Data => q.2.2 := snd.comp snd
  have hfr : Primrec fun q : Data × Data × Data => q.2.2.left := Data.primrec_left.comp hk
  have hk' : Primrec fun q : Data × Data × Data => q.2.2.right := Data.primrec_right.comp hk
  have hftag : Primrec fun q : Data × Data × Data => Data.unaryToNat q.2.2.left.left :=
    primrec_tag.comp hfr
  have hfb : Primrec fun q : Data × Data × Data => q.2.2.left.right := Data.primrec_right.comp hfr
  have hfb1 : Primrec fun q : Data × Data × Data => q.2.2.left.right.left :=
    Data.primrec_left.comp hfb
  have hfb2 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right :=
    Data.primrec_right.comp hfb
  have hfb22 : Primrec fun q : Data × Data × Data => q.2.2.left.right.right.right :=
    Data.primrec_right.comp hfb2
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data × Data =>
      Data.unaryToNat q.2.2.left.left = n :=
    fun n => PrimrecRel.comp Primrec.eq hftag (const n)
  refine Primrec.ite (PrimrecRel.comp Primrec.eq hk (const Data.nil)) ?_
    (Primrec.ite (heq 0) ?_ (Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_
      (Primrec.ite (PrimrecRel.comp Primrec.eq hv (const Data.nil)) ?_
        (Primrec.ite (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp hv) (const Data.nil)) ?_
          ?_)))))
  · exact Data.primrec_cons.comp (primrec_retD.comp hv) (Data.primrec_cons.comp henv hk)
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp hfb2 (Data.primrec_cons.comp
        (Data.primrec_cons.comp (const (Data.ofNat 1)) hv) hk'))
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_cons.comp hfb hv))
      (Data.primrec_cons.comp henv hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp hv hfb2) hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (const Data.nil)) (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_retD.comp (Data.primrec_right.comp hv))
      (Data.primrec_cons.comp hfb2 hk')
  · exact Data.primrec_cons.comp (primrec_evD.comp hfb1)
      (Data.primrec_cons.comp (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22)
        (Data.primrec_cons.comp (Data.primrec_cons.comp (const (Data.ofNat 3))
          (Data.primrec_cons.comp hfb1
            (Data.primrec_cons.comp (Data.primrec_right.comp hv) hfb22))) hk'))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_stepData : Primrec stepData := by
  have hq : Primrec fun d : Data => (d.left.right, d.right.left, d.right.right) :=
    Primrec.pair (Data.primrec_right.comp Data.primrec_left)
      (Primrec.pair (Data.primrec_left.comp Data.primrec_right)
        (Data.primrec_right.comp Data.primrec_right))
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil))
    (primrec_stepEv.comp hq) (primrec_stepRet.comp hq)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_isFinalD : PrimrecPred IsFinalD := by
  have h1 : PrimrecPred fun d : Data => d.left.left ≠ .nil :=
    (PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil)).not
  have h2 : PrimrecPred fun d : Data => d.right.right = .nil :=
    PrimrecRel.comp Primrec.eq (Data.primrec_right.comp Data.primrec_right) (const Data.nil)
  exact h1.and h2
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_resultD : Primrec resultD := Data.primrec_right.comp Data.primrec_left
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem primrec_initData : Primrec₂ initData :=
  Data.primrec_cons.comp (primrec_evD.comp fst)
    (Data.primrec_cons.comp (Data.primrec_cons.comp snd (const Data.nil)) (const Data.nil))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem computable_evalStep : Computable evalStep :=
  (Primrec.ite primrec_isFinalD (Primrec.sumInl.comp primrec_resultD)
    (Primrec.sumInr.comp primrec_stepData)).to_comp
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem partrec_evalData : Partrec₂ evalData :=
  (Partrec.fix computable_evalStep).comp
    (primrec_initData.to_comp.comp Computable.fst Computable.snd)
end MIPRE.Cost.Machine

namespace MIPRE.Cost
theorem evalData_encode {α β : Type*} [SizedEncoding α] [SizedEncoding β] (F : PolyTimeFun α β)
    (a : α) : Machine.evalData (encode F.code) (encode a) = Part.some (encode (F a)) := by
  refine Part.eq_some_iff.2 ?_
  rw [show (encode F.code : Data) = F.code.toData from rfl, Machine.mem_evalData_iff]
  obtain ⟨t, -, h⟩ := F.computes a
  exact ⟨t, h⟩
end MIPRE.Cost

namespace MIPRE.Cost
/-- **The `Data`-level form**: a polynomial-time function of the ambient model, precomposed
with a computable encoding of its input, has a computable *encoded* output. No `Primcodable`
on the output type is needed, which matters — `Prog` deliberately has none (see the module
docstring of `Cost/Codable.lean`), so this is the only way a `PolyTimeFun _ Prog` such as
`GapCompression.samplerProg` can reach a computability proof at all. -/
theorem PolyTimeFun.computable_encode_comp {α β γ : Type*} [SizedEncoding α] [SizedEncoding β]
    [Primcodable γ] (F : PolyTimeFun α β) (h : γ → α)
    (hh : Computable fun c => (encode (h c) : Data)) :
    Computable fun c => (encode (F (h c)) : Data) :=
  Partrec.of_eq_tot (Machine.partrec_evalData.comp (Computable.const (encode F.code)) hh)
    fun c => by rw [evalData_encode]; exact Part.mem_some _
end MIPRE.Cost

namespace MIPRE.Cost
/-- A polynomial-time function of the ambient model, precomposed with a computable
encoding of its input and followed by a computable decoding of its output, is
Mathlib-computable. -/
theorem PolyTimeFun.computable_comp {α β γ : Type*} [SizedEncoding α] [SizedEncoding β]
    [Primcodable γ] [Primcodable β] [Inhabited β] (F : PolyTimeFun α β) (h : γ → α)
    (hh : Computable fun c => (encode (h c) : Data))
    (hβ : Computable fun d : Data => (SizedEncoding.decode d : Option β)) :
    Computable fun c => F (h c) := by
  have h2 : Computable fun c => (SizedEncoding.decode (encode (F (h c)) : Data) : Option β) :=
    hβ.comp (F.computable_encode_comp h hh)
  refine (Primrec.option_getD_default.to_comp.comp h2).of_eq fun c => ?_
  simp [SizedEncoding.decode_encode]
end MIPRE.Cost

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → g pc ∈ B) := by
  obtain ⟨g, hg⟩ := compressibility_criterion A B yYes hyes yNo hno S hSws hS Compr hCompr
  obtain ⟨compile, hc, hspec⟩ := exists_compile
  refine ⟨fun pc => g (compile pc),
    PolyTimeFun.computable_comp g compile hc Data.primrec_decode_bitStr.to_comp, fun pc => ?_⟩
  exact ⟨fun h => (hg _).1 ((hspec pc).2 h), fun h => (hg _).2 fun h' => h ((hspec pc).1 h')⟩
