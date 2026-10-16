-- Prove2me | solution 1 for MIPRE.Verifier.rePred_not_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:46:11.494175+00:00
-- url     : https://prove2.me/submissions/a51acc80-4cf3-4ad0-9e27-395843f75a81

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Semidecider.lean (solution of MIPRE.Verifier.rePred_not_isBounded);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
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
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
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
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Theorems.Thm_MIPRE_Cost_Data_encode_natOf
import Theorems.Thm_MIPRE_REPred_of_computable_exists
import Theorems.Thm_MIPRE_Verifier_not_isBounded_iff_exists

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_stepCostEv : Primrec fun q : Data × Data => stepCostEvD q.1 q.2 := by
  have htag : Primrec fun q : Data × Data => Data.unaryToNat q.1.left := primrec_tag.comp fst
  have heq : ∀ n : ℕ, PrimrecPred fun q : Data × Data => Data.unaryToNat q.1.left = n :=
    fun n => PrimrecRel.comp Primrec.eq htag (const n)
  have hle : PrimrecPred fun q : Data × Data => Data.unaryToNat q.1.left ≤ 5 :=
    PrimrecRel.comp Primrec.nat_le htag (const 5)
  have hvar : Primrec fun q : Data × Data =>
      (Data.getList q.2 (Data.unaryToNat q.1.right)).size + 1 :=
    Primrec.succ.comp (Data.primrec_size.comp
      (Data.primrec_getList.comp snd (Data.primrec_unaryToNat.comp (Data.primrec_right.comp fst))))
  exact Primrec.ite (heq 0) hvar (Primrec.ite (heq 5) (const 0) (Primrec.ite hle (const 1)
    (Data.primrec_size.comp (Data.primrec_right.comp fst))))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_stepCostRet : Primrec stepCostRetD := by
  have hnil : PrimrecPred fun d : Data => d = Data.nil :=
    PrimrecRel.comp Primrec.eq Primrec.id (const Data.nil)
  have htag : Primrec fun d : Data => Data.unaryToNat d.left.left :=
    Data.primrec_unaryToNat.comp (Data.primrec_left.comp Data.primrec_left)
  have heq : PrimrecPred fun d : Data => Data.unaryToNat d.left.left = 3 :=
    PrimrecRel.comp Primrec.eq htag (const 3)
  exact Primrec.ite hnil (const 0) (Primrec.ite heq (const 1) (const 0))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_stepCostD : Primrec stepCostD := by
  have hnil : PrimrecPred fun d : Data => d.left.left = Data.nil :=
    PrimrecRel.comp Primrec.eq (Data.primrec_left.comp Data.primrec_left) (const Data.nil)
  exact Primrec.ite hnil
    (primrec_stepCostEv.comp ((Data.primrec_right.comp Data.primrec_left).pair
      (Data.primrec_left.comp Data.primrec_right)))
    (primrec_stepCostRet.comp (Data.primrec_right.comp Data.primrec_right))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_costStep : Primrec costStep :=
  (primrec_stepData.comp fst).pair (Primrec.nat_add.comp snd (primrec_stepCostD.comp fst))
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_costRun : Primrec fun q : (Data × Data) × ℕ => costRun q.1.1 q.1.2 q.2 := by
  have hinit : Primrec fun q : (Data × Data) × ℕ => ((initData q.1.1 q.1.2 : Data), (0 : ℕ)) :=
    (primrec_initData.comp (fst.comp fst) (snd.comp fst)).pair (const 0)
  exact Primrec.nat_iterate (Primrec.succ.comp (Primrec.nat_mul.comp (const 3) snd)) hinit
    (primrec_costStep.comp snd).to₂
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec in
theorem primrec_evalForCostD :
    Primrec fun q : (Data × Data) × ℕ => evalForCostD q.1.1 q.1.2 q.2 := by
  have hcfg : Primrec fun q : (Data × Data) × ℕ => (costRun q.1.1 q.1.2 q.2).1 :=
    fst.comp primrec_costRun
  have hcost : Primrec fun q : (Data × Data) × ℕ => (costRun q.1.1 q.1.2 q.2).2 :=
    snd.comp primrec_costRun
  have hcond : PrimrecPred fun q : (Data × Data) × ℕ =>
      isFinalB (costRun q.1.1 q.1.2 q.2).1 = true ∧ (costRun q.1.1 q.1.2 q.2).2 ≤ q.2 :=
    PrimrecPred.and
      ⟨inferInstance, (primrec_isFinalB.comp hcfg).of_eq fun q => Bool.eq_iff_iff.2 (by simp)⟩
      (PrimrecRel.comp Primrec.nat_le hcost snd)
  exact Primrec.ite hcond (Primrec.option_some.comp (primrec_resultD.comp hcfg)) (const none)
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem primrec_haltsWithinB :
    Primrec fun q : (Data × Data) × ℕ => haltsWithinB q.1.1 q.1.2 q.2 :=
  Primrec.option_isSome.comp primrec_evalForCostD
end MIPRE.Cost.Machine

namespace MIPRE
open Cost
open HaltingGameValue (GameData)
/-- `≤` on naturals as a primitive recursive `Bool`-valued function. `Primrec.nat_le` is a
`PrimrecRel`, which hides the `Decidable` instance behind an existential and so does not
compose with `Computable` arguments; this is the same fact in usable form. -/
theorem Cost.primrec_natLeB : Primrec fun p : ℕ × ℕ => decide (p.1 ≤ p.2) := by
  obtain ⟨_, h⟩ := Primrec.nat_le
  exact h.of_eq fun p => by rw [Bool.eq_iff_iff]; simp
end MIPRE

namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem boundViolationB_iff (lam : ℕ) (w : Data × Data) :
    V.boundViolationB lam w = true ↔ V.BoundViolation lam w := by
  have key : ∀ (p : Prog) (x : Data) (k : ℕ),
      (Machine.haltsWithinB (encode p) x k = false) ↔ ¬ HaltsWithin p x k := fun p x k => by
    rw [← Machine.haltsWithinB_iff, Bool.not_eq_true]
  simp only [boundViolationB, BoundViolation, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, key, or_assoc]
end MIPRE.Verifier

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
theorem _root_.solution {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}
    (hV : ComputablyPresented V) :
    REPred fun q : α × ℕ => ¬ (V q.1).IsBounded q.2 := by
  -- the pieces of the test, as functions of `((a, lam), w)`
  have ha : Computable fun z : (α × ℕ) × (Data × Data) => z.1.1 :=
    Computable.fst.comp Computable.fst
  have hlam : Computable fun z : (α × ℕ) × (Data × Data) => z.1.2 :=
    Computable.snd.comp Computable.fst
  have hidx : Computable fun z : (α × ℕ) × (Data × Data) => Data.natOf z.2.1 :=
    (Data.primrec_natOf.comp Primrec.fst).to_comp.comp Computable.snd
  have hinp : Computable fun z : (α × ℕ) × (Data × Data) => z.2.2 :=
    (Primrec.snd.to_comp).comp Computable.snd
  have hsize : Computable fun z : (α × ℕ) × (Data × Data) => (V z.1.1).size :=
    Primrec.nat_max.to_comp.comp (Data.primrec_size.to_comp.comp (hV.samplerProg.comp ha))
      (Data.primrec_size.to_comp.comp (hV.deciderProg.comp ha))
  have hdim : Computable fun z : (α × ℕ) × (Data × Data) =>
      (V z.1.1).sampler.dim (Data.natOf z.2.1) := hV.dim.comp (ha.pair hidx)
  have hpow : Computable fun z : (α × ℕ) × (Data × Data) => Data.natOf z.2.1 ^ z.1.2 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp hidx hlam
  have hbudget : Computable fun z : (α × ℕ) × (Data × Data) =>
      boundBudget z.1.2 (Data.natOf z.2.1) z.2.2 :=
    Primrec.nat_mul.to_comp.comp hpow
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp.comp
        (Primrec.succ.to_comp.comp ((Data.primrec_size.to_comp).comp hinp)) hlam)
  have hcfg : Computable fun z : (α × ℕ) × (Data × Data) =>
      (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data) := by
    refine (Data.primrec_cons.to_comp.comp
      (((Data.primrec_normBin.comp Primrec.fst).to_comp).comp Computable.snd) hinp).of_eq
      fun z => ?_
    rw [Data.encode_natOf]
  have htest : Computable fun z : (α × ℕ) × (Data × Data) =>
      (V z.1.1).boundViolationB z.1.2 z.2 := by
    have hS : Computable fun z : (α × ℕ) × (Data × Data) =>
        Machine.haltsWithinB (encode (V z.1.1).sampler.prog)
          (Data.cons (encode (Data.natOf z.2.1)) z.2.2)
          (boundBudget z.1.2 (Data.natOf z.2.1) z.2.2) :=
      Computable.comp (f := fun q : (Data × Data) × ℕ => Machine.haltsWithinB q.1.1 q.1.2 q.2)
        (g := fun z : (α × ℕ) × (Data × Data) =>
          (((encode (V z.1.1).sampler.prog : Data),
            (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data)),
            boundBudget z.1.2 (Data.natOf z.2.1) z.2.2))
        Machine.primrec_haltsWithinB.to_comp
        (((hV.samplerProg.comp ha).pair hcfg).pair hbudget)
    have hD : Computable fun z : (α × ℕ) × (Data × Data) =>
        Machine.haltsWithinB (encode (V z.1.1).decider.prog)
          (Data.cons (encode (Data.natOf z.2.1)) z.2.2)
          (boundBudget z.1.2 (Data.natOf z.2.1) z.2.2) :=
      Computable.comp (f := fun q : (Data × Data) × ℕ => Machine.haltsWithinB q.1.1 q.1.2 q.2)
        (g := fun z : (α × ℕ) × (Data × Data) =>
          (((encode (V z.1.1).decider.prog : Data),
            (Data.cons (encode (Data.natOf z.2.1)) z.2.2 : Data)),
            boundBudget z.1.2 (Data.natOf z.2.1) z.2.2))
        Machine.primrec_haltsWithinB.to_comp
        (((hV.deciderProg.comp ha).pair hcfg).pair hbudget)
    have hle1 : Computable fun z : (α × ℕ) × (Data × Data) => decide ((V z.1.1).size ≤ z.1.2) :=
      Cost.primrec_natLeB.to_comp.comp (hsize.pair hlam)
    have hle2 : Computable fun z : (α × ℕ) × (Data × Data) =>
        decide (2 ≤ Data.natOf z.2.1) :=
      (Cost.primrec_natLeB.comp ((Primrec.const 2).pair
        (Data.primrec_natOf.comp Primrec.fst))).to_comp.comp Computable.snd
    have hle3 : Computable fun z : (α × ℕ) × (Data × Data) =>
        decide ((V z.1.1).sampler.dim (Data.natOf z.2.1) ≤ Data.natOf z.2.1 ^ z.1.2) :=
      Cost.primrec_natLeB.to_comp.comp (hdim.pair hpow)
    unfold boundViolationB
    exact Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hle1)
      (Primrec.and.to_comp.comp hle2
        (Primrec.or.to_comp.comp
          (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hle3)
            (Primrec.not.to_comp.comp hS))
          (Primrec.not.to_comp.comp hD)))
  refine (REPred.of_computable_exists (β := Data × Data)
    (test := fun (q : α × ℕ) (w : Data × Data) => (V q.1).boundViolationB q.2 w)
    htest).of_eq fun q => ?_
  rw [not_isBounded_iff_exists]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, ((V q.1).boundViolationB_iff q.2 w).1 hw⟩,
    fun ⟨w, hw⟩ => ⟨w, ((V q.1).boundViolationB_iff q.2 w).2 hw⟩⟩
end MIPRE.Verifier
