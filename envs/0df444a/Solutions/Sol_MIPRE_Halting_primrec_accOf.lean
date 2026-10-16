-- Prove2me | solution 1 for MIPRE.Halting.primrec_accOf
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:56:05.093615+00:00
-- url     : https://prove2.me/submissions/5fd0d30d-51a0-4f87-82e8-e8384a890fa1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Tabulate.lean (solution of MIPRE.Halting.primrec_accOf);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
set_option maxHeartbeats 1000000 in
theorem _root_.solution {α : Type*} [Primcodable α] {pd : α → Data} {lvl : α → ℕ}
    (hpd : Primrec pd) (hlvl : Primrec lvl) :
    Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      accOf (pd q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hpd' : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => pd q.1 :=
    hpd.comp Primrec.fst
  have hn : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => lvl q.1 :=
    hlvl.comp Primrec.fst
  have hx : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have htup : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr => (encode q.2 : Data) :=
    Data.primrec_cons.comp (hebs.comp hx)
      (Data.primrec_cons.comp (hebs.comp hy)
        (Data.primrec_cons.comp (hebs.comp ha) (hebs.comp hb)))
  have hinput : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      (encode (lvl q.1, q.2) : Data) :=
    Data.primrec_cons.comp (Data.primrec_encode_nat.comp hn) htup
  have hbudget : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Decider.acceptBudget (lvl q.1 ^ lvl q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 :=
    Primrec.nat_mul.comp (primrec_nat_pow.comp hn hn)
      (primrec_nat_pow.comp (Primrec.succ.comp (Data.primrec_size.comp htup)) hn)
  have hfin : PrimrecPred fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD (pd q.1) (encode (lvl q.1, q.2))
        (Decider.acceptBudget (lvl q.1 ^ lvl q.1) (lvl q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp ((hpd'.pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accOf]; split <;> simp_all
end MIPRE.Halting
