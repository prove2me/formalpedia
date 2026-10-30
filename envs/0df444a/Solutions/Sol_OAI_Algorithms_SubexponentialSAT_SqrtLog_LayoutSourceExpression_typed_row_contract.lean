-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:50:13.093392+00:00
-- url     : https://prove2.me/submissions/57524962-3002-4bbe-a7b3-b4dd1b0cb2d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceTyped_row_meaning
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PolynomialExecutorProgram_evaluate_full

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Algorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable separated arithmetic kernels

The arithmetic expressions and their postfix compiler in this file are data.
The evaluator contains no choice, no decision of a semantic proposition, and no
enumeration of the Cartesian product of the two inner lists.  Its instruction
counts are proved by actual transition traces.  An arithmetic instruction is
not a primitive bit-machine instruction: refining the supplied coefficient
operations to the latter remains a separate obligation.
-/

namespace SubexponentialSAT.Algorithm

open scoped BigOperators

universe u

/-! ## Constructive output-sensitive monomial enumeration -/

/-! ## Concrete dense coefficients and the arithmetic-machine backend -/

/-! ## Finite coefficient extraction after moment execution -/

namespace Expr

theorem map_sum {R S : Type*} [Zero R] [Zero S]
    (f : R → S) (hf : f 0 = 0) (es : List (Expr R)) :
    (Expr.sum es).map f = Expr.sum (es.map fun e => e.map f) := by
  induction es with
  | nil => simp [Expr.sum, Expr.map, hf]
  | cons e es ih => simp [Expr.sum, Expr.map, ih]

end Expr

end SubexponentialSAT.Algorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row-source emitter's bytes are exactly the input accepted by
the generic coefficient-array interpreter. Scalar literals are single cells;
the formal variable has the two-cell representation [zero, one]. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram

private theorem map_product {A B : Type*} [One A] [One B]
    (f : A → B) (h1 : f 1 = 1) (es : List (Algorithm.Expr A)) :
    (Algorithm.Expr.product es).map f = Algorithm.Expr.product (es.map (Algorithm.Expr.map f)) := by
  induction es with
  | nil => simp [Algorithm.Expr.product,Algorithm.Expr.map,h1]
  | cons e es ih => simp [Algorithm.Expr.product,Algorithm.Expr.map,ih]

theorem map_rowExpression {A B : Type*} [Zero A] [One A] [Zero B] [One B]
    (f : A → B) (h0 : f 0 = 0) (h1 : f 1 = 1) (x : A) (r : Row A) :
    (rowExpression x r).map f = rowExpression (f x) (mapRow f r) := by
  simp [rowExpression,Algorithm.Expr.map,Algorithm.Expr.map_sum f h0,
    map_product f h1,List.map_map,Function.comp_def,termExpression,factorExpression,
    mapRow,mapTerm,mapFactor]

theorem sourceExpr_meaning {C R : Type*} [CommRing R] (ops : RepresentedRing C R)
    (r : Row C) :
    (sourceExpr ops.program r).map (meaning ops) =
      rowExpression Polynomial.X (mapRow (fun c => Polynomial.C (ops.decode c)) r) := by
  let _ : Zero (List C) := ⟨[ops.zeroRun.1]⟩
  let _ : One (List C) := ⟨[ops.oneRun.1]⟩
  have h0 : meaning ops (0 : List C) = 0 := by
    change meaning ops [ops.zeroRun.1] = 0
    simp [meaning,PolynomialAlgorithm.denote,ops.zero_correct]
  have h1 : meaning ops (1 : List C) = 1 := by
    change meaning ops [ops.oneRun.1] = 1
    simp [meaning,PolynomialAlgorithm.denote,ops.one_correct]
  have h := map_rowExpression (meaning ops) h0 h1 [ops.zeroRun.1,ops.oneRun.1]
    (mapRow (fun c => [c]) r)
  have hc (c : C) : meaning ops [c] = Polynomial.C (ops.decode c) := by
    simp [meaning, PolynomialAlgorithm.denote]
  have hmap : mapRow (meaning ops) (mapRow (fun c => [c]) r) =
      mapRow (fun c => Polynomial.C (ops.decode c)) r := by
    cases r
    simp [mapRow, mapTerm, mapFactor, List.map_map, Function.comp_def, hc]
  rw [hmap] at h
  have hx : meaning ops [ops.zeroRun.1, ops.oneRun.1] = Polynomial.X := by
    simp [meaning, PolynomialAlgorithm.denote, ops.zero_correct, ops.one_correct]
  rw [hx] at h
  simpa [sourceExpr] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceExpression
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Degree certificates for the actual typed literal and interpolation-row
sources. These remove the full-polynomial cutoff premise at R+1. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

/-- Any exact source-row witness inherits the audited full source degree. -/
theorem source_row_degree {C O : Type*} [CommRing O] {r Q Δ : ℕ}
    (ops : RepresentedRing C O) (row : Row C)
    (N : LayoutScaledMatrices.Numerators r Q Δ) (denom : Oˣ)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) {node : Fin Q → O}
    (units : NodeUnits node) (y : UniversalType r Q Δ)
    (hm : (rowExpression Polynomial.X
      (mapRow (fun c => Polynomial.C (ops.decode c)) row)).eval =
        LayoutScaledMatrices.sourceRow N denom u i R units y) :
    (((sourceExpr ops.program row).map (meaning ops)).eval).natDegree ≤ R := by
  rw [sourceExpr_meaning,hm]
  exact LayoutScaledMatrices.sourceRow_degree N denom u i R units y

/-- No separate degree assumption remains at the source's R+1 cutoff. -/
theorem source_row_evaluate_full {C O : Type*} [CommRing O] {r Q Δ : ℕ}
    (ops : RepresentedRing C O) (row : Row C)
    (N : LayoutScaledMatrices.Numerators r Q Δ) (denom : Oˣ)
    (u : UniversalType r Q Δ) (i : Fin Δ) (R : ℕ) {node : Fin Q → O}
    (units : NodeUnits node) (y : UniversalType r Q Δ)
    (hm : (rowExpression Polynomial.X
      (mapRow (fun c => Polynomial.C (ops.decode c)) row)).eval =
        LayoutScaledMatrices.sourceRow N denom u i R units y) :
    meaning ops (evaluate ops.program (R+1) (sourceExpr ops.program row)) =
      LayoutScaledMatrices.sourceRow N denom u i R units y := by
  rw [evaluate_full ops (R+1) _ (Nat.lt_succ_of_le
    (source_row_degree ops row N denom u i R units y hm)),sourceExpr_meaning,hm]

section TypedRows

variable {C O : Type*} [Nonempty C] [CommRing O] {r Q : ℕ}
    (encode : C → List Bool) (tables : SubexponentialSAT.Subexp.UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (hvalues : ∀ i, tables.values.getD i.val []=encode (values i))
    (hinverse : ∀ i, tables.inverses.getD i.val []=encode (inverse i))
    (hnegative : ∀ i, tables.negatives.getD i.val []=encode (negative i))
    (hdifference : ∀ i j, (tables.differences.getD i.val []).getD j.val []=encode (difference i j))
    (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

include hvalues hinverse hnegative hdifference hinteger hinvDenom hnode hnodeInverse hdiffInverse in
/-- Concrete native table values give a typed expression of degree at most R,
and evaluation at R+1 recovers the complete source polynomial. The degree
conclusion is derived here, not supplied by the caller. -/
theorem typed_row_contract_oai (hi : Function.Injective encode)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
    (hlimit : limit.length=R)
    (hv : ∀ i,ops.decode (values i)=ops.decode
      (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
    let row := LayoutProgram.SourceTyped.row values inverse negative difference
      (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
    let e := sourceExpr ops.program row
    ((e.map (meaning ops)).eval =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) ∧
    (((e.map (meaning ops)).eval).natDegree ≤ R) ∧
    (meaning ops (evaluate ops.program (R+1) e) =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) := by
  intro row e
  have hm := LayoutProgram.SourceTyped.row_meaning
    (encode := encode) (tables := tables) (values := values) (inverse := inverse)
    (negative := negative) (difference := difference)
    (hvalues := hvalues) (hinverse := hinverse) (hnegative := hnegative) (hdifference := hdifference)
    (ops := ops) (cache := cache) (integerWord := integerWord) (hinteger := hinteger)
    (denom := denom) (invDenom := invDenom) (hinvDenom := hinvDenom)
    (units := units) (hnode := hnode) (hnodeInverse := hnodeInverse) (hdiffInverse := hdiffInverse)
    hi A R u y delta limit hlimit hv hiv hnv hdv hdelta
  refine ⟨?_,source_row_degree ops row _ denom u 0 R units y hm,
    source_row_evaluate_full ops row _ denom u 0 R units y hm⟩
  rw [sourceExpr_meaning]
  exact hm

end TypedRows
end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract_oai.{u_1, u_2}
