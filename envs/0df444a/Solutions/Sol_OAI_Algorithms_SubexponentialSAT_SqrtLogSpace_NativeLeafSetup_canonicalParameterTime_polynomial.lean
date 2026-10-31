-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:14:49.624864+00:00
-- url     : https://prove2.me/submissions/09aef37c-5afa-42a6-87bc-a619368dff41

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

theorem le_majorant (B : ℕ) : B ≤ majorant B := by
  have hp : B+2 ≤ (B+2)^6 := Nat.le_self_pow (by decide) _
  dsimp [majorant]
  omega

private theorem power_bounds (B : ℕ) :
    1 ≤ (B+2)^6 ∧ B ≤ (B+2)^6 ∧ B^2 ≤ (B+2)^6 ∧
      B^3 ≤ (B+2)^6 ∧ B^4 ≤ (B+2)^6 := by
  have h1 : 1 ≤ B+2 := by omega
  have hp (k : ℕ) (hk : k ≤ 6) : B^k ≤ (B+2)^6 :=
    (Nat.pow_le_pow_left (show B ≤ B+2 by omega) k).trans (Nat.pow_le_pow_right h1 hk)
  exact ⟨one_le_pow₀ h1,(by simpa using hp 1 (by decide)),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide)⟩

theorem length_cost_majorant (m : Model) (i : Instr) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : scale m i ≤ B) :
    lengthBound m.val m.len i ≤ majorant B ∧ cost m.val m.len i ≤ majorant B := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := power_bounds B
  have hM := le_majorant B
  cases i with
  | clear a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  0 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B+3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | load o bits =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  2*B := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | copy a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  7*B+5 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | add a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | mul a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pow a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  1+B*B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  B*(50*(B+1)*(2+(B+1)*B))+(B+1)*(16*B+16)+3+9*B+8 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | quot a b o ha hb =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  150*(B+B+1)^2 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr <;> first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | sqrt a o h =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  200001*(B+B+2)^3 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | logSucc a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+1 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  32*(B+1)^2+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | addConst a k =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  8*B*(B+B+1)+4 := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | pred a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  20*(B+1) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
  | maxTwo a =>
    simp only [scale] at hs
    constructor
    · calc
        _  ≤  B+2 := by
          simp only [lengthBound]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]
    · calc
        _  ≤  100*(B+3) := by
          simp only [cost]
          all_goals first | exact hs | apply hl | omega | (gcongr ; first | exact hs | apply hl)
        _  ≤  majorant B := by dsimp [majorant]; nlinarith only [h0,h1,h2,h3,h4]

theorem le_iterMajorant (n B : ℕ) : B ≤ iterMajorant n B := by
  induction n generalizing B with
  | zero => exact le_rfl
  | succ n ih => exact (le_majorant B).trans (ih (majorant B))

theorem scaleBound_mono (B C : ℕ) (hBC : B ≤ C) (is : List Instr) (m : Model)
    (h : ScaleBound B is m) : ScaleBound C is m := by
  induction is generalizing m with
  | nil => trivial
  | cons i is ih => exact ⟨h.1.trans hBC,ih (next m i) h.2⟩

/-- A single global bound on numeric loop parameters yields a polynomial
bound for every fixed instruction table, regardless of large output values. -/
theorem budget_majorant (is : List Instr) (m : Model) (B : ℕ)
    (hl : ∀ a, m.len a ≤ B) (hs : ScaleBound B is m) :
    (∀ a, (result is m).len a ≤ iterMajorant is.length B) ∧
      budget is m ≤ is.length*iterMajorant is.length B := by
  induction is generalizing m B with
  | nil => exact ⟨hl,by simp [budget]⟩
  | cons i is ih =>
    have hi := length_cost_majorant m i B hl hs.1
    have hn : ∀ a, (next m i).len a ≤ majorant B := by
      intro a
      by_cases ha : a=output i
      · simpa [next,ha] using hi.1
      · simpa [next,ha] using (hl a).trans (le_majorant B)
    have ht := ih (next m i) (majorant B) hn
      (scaleBound_mono B (majorant B) (le_majorant B) is (next m i) hs.2)
    refine ⟨ht.1,?_⟩
    have hm := le_iterMajorant is.length (majorant B)
    simp only [budget,List.length_cons,iterMajorant]
    nlinarith [hi.2,ht.2]

/-- The deliberately loose degree is a fixed constant once the finite table
is fixed. It establishes a genuine ordinary-polynomial setup bound. -/
theorem iterMajorant_polynomial (n B : ℕ) (hB : 1 ≤ B) :
    iterMajorant n B ≤ polynomialCoefficient n * B^(6^n) := by
  induction n generalizing B with
  | zero => simp [iterMajorant,polynomialCoefficient]
  | succ n ih =>
    have hF : 1 ≤ majorant B := hB.trans (le_majorant B)
    have hb : B+2 ≤ 3*B := by omega
    have hm : majorant B ≤ (10000000*3^6)*B^6 := by
      dsimp [majorant]
      calc
        _  ≤  10000000*(3*B)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
        _ = _ := by rw [mul_pow]; ring_nf
    calc
      iterMajorant (n+1) B = iterMajorant n (majorant B) := rfl
      _  ≤  polynomialCoefficient n * (majorant B)^(6^n) := ih (majorant B) hF
      _  ≤  polynomialCoefficient n * ((10000000*3^6)*B^6)^(6^n) := by gcongr
      _ = polynomialCoefficient (n+1)*B^(6^(n+1)) := by
        rw [polynomialCoefficient,mul_pow,← pow_mul,pow_succ 6 n]
        simp only [Nat.mul_comm,Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le (m B : ℕ) : degree m B ≤ m := min_le_left _ _

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_min (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : r < dimensionFor m D) : D * 2 ^ r < m := by
  simp only [dimensionFor, dite_eq_left hD] at hr
  exact Nat.lt_of_not_ge (Nat.find_min (exists_dimension m hD) hr)

theorem dimensionFor_edge_upper {m D : ℕ} (hm : 0 < m) (hD : 0 < D) (hDm : D ≤ m) :
    D * 2 ^ dimensionFor m D < 2 * m := by
  cases hr : dimensionFor m D with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ r =>
    have hprev : D * 2 ^ r < m := dimensionFor_min m hD (by omega)
    simp only [pow_succ]
    nlinarith

theorem graph_edge_upper {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    2 ^ dimension m B * degree m B < 2 * m := by
  simpa [dimension, Nat.mul_comm] using
    dimensionFor_edge_upper hm (degree_pos hm hB) (degree_le m B)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

/-- The minimal graph dimension is computed by one division and a binary size,
including the one-vertex case. No unbounded semantic search is needed by the
physical parameter program. -/
theorem dimensionFor_eq_size {m D : ℕ} (hm : 0 < m) (hD : 0 < D) :
    SparseCode.dimensionFor m D = Nat.size ((m-1)/D) := by
  apply Nat.le_antisymm
  · apply SparseCode.dimensionFor_le m hD
    have h := Nat.lt_size_self ((m-1)/D)
    have hh := (Nat.div_lt_iff_lt_mul hD).mp h
    rw [Nat.mul_comm] at hh
    omega
  · apply Nat.size_le.mpr
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    have h := SparseCode.dimensionFor_spec m hD
    rw [Nat.mul_comm]
    omega

theorem dimension_eq_size {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    SparseCode.dimension m B = Nat.size ((m-1)/SparseCode.degree m B) :=
  dimensionFor_eq_size hm (SparseCode.degree_pos hm hB)

/-- A branch-free implementation of binary size using the existing positive
logarithm primitive. -/
theorem size_eq_log2_odd (z : ℕ) : Nat.size z = Nat.log2 (2*z+1) := by
  have ha := LeafParametersProgram.size_eq_log2_add_one (n := 2*z+1) (by omega)
  have hb : Nat.size (2*z+1) = Nat.size z+1 := by
    simpa [Nat.bit, Nat.two_mul] using
      (Nat.size_bit (b := true) (n := z) (by simp [Nat.bit]))
  omega

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank
open LeafParametersProgram.Circuit


theorem final_values {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    (finalModel m B ml Bl).val 5=SparseCode.gapDenom m B  ∧
    (finalModel m B ml Bl).val 9=SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 11=SparseCode.localRows m B  ∧
    (finalModel m B ml Bl).val 12=SparseCode.localRows m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 15=SparseCode.degree m B/(100*B*SparseCode.logSize m)+1  ∧
    (finalModel m B ml Bl).val 18=SparseCode.dimension m B  ∧
    (finalModel m B ml Bl).val 19=SparseCode.dimension m B*SparseCode.degree m B  ∧
    (finalModel m B ml Bl).val 21=2^SparseCode.dimension m B := by
  have hr := dimension_eq_size hm hB
  rw [size_eq_log2_odd] at hr
  have hr' : Nat.log 2 (((m-1)/SparseCode.degree m B)+((m-1)/SparseCode.degree m B)+1) =
      SparseCode.dimension m B := by
    simpa [Nat.two_mul,Nat.log2_eq_log_two] using hr.symm
  simp [finalModel,suffixCode,middleModel,prefixModel,prefixCode,result,next,output,
    value,initialModel,BinaryArithmetic.toNat,bitVal,SparseCode.gapDenom,SparseCode.localRows,
    SparseCode.logSize,Nat.log2_eq_log_two,Nat.mul_assoc,hr']

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

/-- Unary materialization is paid by numeric value. All seven values are
polynomial in the original number of violation coordinates, even when B is
large. In particular the vertex count is not charged merely by bit length. -/
theorem parameterValues_le {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (j : Fin 7) :
    parameterValues m B j  ≤  2*(m+1)^2 := by
  have hD := SparseCode.degree_le m B
  have hDpos := SparseCode.degree_pos hm hB
  have ht : SparseCode.localRows m B ≤ m+1 := by
    unfold SparseCode.localRows
    have := Nat.div_le_self (SparseCode.degree m B) (8*B)
    omega
  have hd : SparseCode.degree m B/(100*B*SparseCode.logSize m)+1 ≤ m+1 := by
    have := Nat.div_le_self (SparseCode.degree m B) (100*B*SparseCode.logSize m)
    omega
  have hr : SparseCode.dimension m B ≤ m := by
    rw [dimension_eq_size hm hB]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans
      ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
  have hN : 2^SparseCode.dimension m B ≤ 2*m := by
    calc
      _ = 2^SparseCode.dimension m B*1 := by simp
      _  ≤  2^SparseCode.dimension m B*SparseCode.degree m B :=
        Nat.mul_le_mul_left _ hDpos
      _  ≤  _ := (SparseCode.graph_edge_upper hm hB).le
  have htD := Nat.mul_le_mul ht hD
  have hrD := Nat.mul_le_mul hr hD
  fin_cases j <;> simp +decide [parameterValues,Fin.reduceFinMk] <;> nlinarith

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramBudget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary-polynomial cost of the actual sparse-code metadata producer.
The two exhaustive code searches have separate costs; this file accounts
for the fixed arithmetic table and all seven unary materializations. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open LeafParametersProgram.Circuit


private theorem prefix_scale (m B ml Bl : ℕ) :
    ScaleBound (setupInput m ml Bl) prefixCode (initialModel m B ml Bl) := by
  simp [prefixCode,ScaleBound,scale,setupInput]

private theorem prefix_envelope (m B ml Bl : ℕ) :
    (∀ a, (prefixModel m B ml Bl).len a ≤ prefixEnvelope m ml Bl) ∧
    budget prefixCode (initialModel m B ml Bl) ≤ prefixCode.length*prefixEnvelope m ml Bl := by
  apply budget_majorant prefixCode (initialModel m B ml Bl) (setupInput m ml Bl)
  · intro a
    simp only [initialModel]
    split_ifs <;> dsimp [setupInput] <;> omega
  · exact prefix_scale m B ml Bl

private theorem dimension_le_m {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    SparseCode.dimension m B ≤ m := by
  rw [dimension_eq_size hm hB]
  exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans
    ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))

private theorem suffix_scale {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    ScaleBound (setupInput m ml Bl) suffixCode (middleModel m B ml Bl) := by
  have hr := dimension_eq_size hm hB
  rw [size_eq_log2_odd] at hr
  have hr' : Nat.log 2 (((m-1)/SparseCode.degree m B)+((m-1)/SparseCode.degree m B)+1) =
      SparseCode.dimension m B := by
    simpa [Nat.two_mul,Nat.log2_eq_log_two] using hr.symm
  have hd := dimension_le_m hm hB
  simp [suffixCode,ScaleBound,scale,next,output,value,middleModel,prefixModel,
    prefixCode,result,initialModel,BinaryArithmetic.toNat,BinaryArithmetic.bitVal,
    Nat.log2_eq_log_two,hr',setupInput] ; omega

private theorem envelopes_order (m ml Bl : ℕ) :
    setupInput m ml Bl ≤ prefixEnvelope m ml Bl ∧
    2*prefixEnvelope m ml Bl ≤ setupEnvelope m ml Bl :=
  ⟨le_iterMajorant _ _,le_iterMajorant _ _⟩

private theorem suffix_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    (∀ a, (finalModel m B ml Bl).len a ≤ setupEnvelope m ml Bl) ∧
    budget suffixCode (middleModel m B ml Bl) ≤ suffixCode.length*setupEnvelope m ml Bl := by
  have hp := prefix_envelope m B ml Bl
  have ho := envelopes_order m ml Bl
  apply budget_majorant suffixCode (middleModel m B ml Bl) (2*prefixEnvelope m ml Bl)
  · intro a
    by_cases ha : a=9
    · subst a
      simpa only [middleModel,Function.update_self,two_mul] using Nat.add_le_add (hp.1 0) (hp.1 8)
    · have h := hp.1 a
      simpa only [middleModel,Function.update_of_ne ha] using
        h.trans (show prefixEnvelope m ml Bl ≤ 2*prefixEnvelope m ml Bl by omega)
  · apply scaleBound_mono (setupInput m ml Bl) (2*prefixEnvelope m ml Bl)
      (by omega) _ _ (suffix_scale hm hB ml Bl)

private theorem final_values_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ)
    (j : Fin 7) :
    (finalModel m B ml Bl).val (binaryPorts j) ≤ 2*(setupEnvelope m ml Bl)^2 := by
  have hv := final_values hm hB ml Bl
  have he : (finalModel m B ml Bl).val (binaryPorts j)=parameterValues m B j := by
    fin_cases j
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2.1
    · exact hv.2.2.2.2.1
    · exact hv.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.1
    · exact hv.2.2.2.2.2.2.2
  rw [he]
  apply (parameterValues_le hm hB j).trans
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  have ho := envelopes_order m ml Bl
  dsimp [setupInput] at ho
  omega

private theorem unary_row_budget {v l Z : ℕ} (hZ : 1 ≤ Z) (hl : l ≤ Z) (hv : v ≤ 2*Z^2) :
    7*l+6+(2*v+(v+1)*(16*l+16)+2*l+6) ≤ 128*Z^3 := by
  have h1 : Z ≤ Z^3 := Nat.le_self_pow (by decide) _
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^3 := one_le_pow₀ hZ
  calc
    _ ≤ 7*Z+6+(2*(2*Z^2)+(2*Z^2+1)*(16*Z+16)+2*Z+6) := by gcongr
    _ ≤ _ := by nlinarith only [h1,h2,h0]

private theorem unary_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    unaryModelBudget (finalModel m B ml Bl) ≤ 896*(setupEnvelope m ml Bl)^3 := by
  let z := finalModel m B ml Bl
  let Z := setupEnvelope m ml Bl
  have hZ : 1 ≤ Z := by
    have ho := envelopes_order m ml Bl
    dsimp [Z,setupInput] at *
    omega
  have hl := (suffix_envelope hm hB ml Bl).1
  have hb (j : Fin 7) :
      7*z.len (binaryPorts j)+6+(2*z.val (binaryPorts j)+
        (z.val (binaryPorts j)+1)*(16*z.len (binaryPorts j)+16)+2*z.len (binaryPorts j)+6) ≤ 128*Z^3 :=
    unary_row_budget hZ (hl _) (final_values_bound hm hB ml Bl j)
  have h9 := hb 0
  have h11 := hb 1
  have h12 := hb 2
  have h15 := hb 3
  have h18 := hb 4
  have h19 := hb 5
  have h21 := hb 6
  simp +decide [binaryPorts] at h9 h11 h12 h15 h18 h19 h21
  change unaryModelBudget z ≤ 896*Z^3
  simp only [unaryModelBudget,unaryPairs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- This bound includes the halt after the actual native metadata command. -/
theorem fullBudget_envelope {m B : ℕ} (hm : 0 < m) (hB : 0 < B) (ml Bl : ℕ) :
    fullBudget m B ml Bl+1 ≤
      (prefixCode.length+suffixCode.length+1017)*(setupEnvelope m ml Bl)^3 := by
  let Y := prefixEnvelope m ml Bl
  let Z := setupEnvelope m ml Bl
  have hp := prefix_envelope m B ml Bl
  have hs := suffix_envelope hm hB ml Bl
  have hu := unary_envelope hm hB ml Bl
  have ho := envelopes_order m ml Bl
  have hYZ : Y ≤ Z := by dsimp [Y,Z]; omega
  have hZ : 1 ≤ Z := by dsimp [Y,Z,setupInput] at *; omega
  have hmin : 40*((prefixModel m B ml Bl).len 0+(prefixModel m B ml Bl).len 8+1) ≤ 120*Z := by
    have h0 : (prefixModel m B ml Bl).len 0 ≤ Y := hp.1 0
    have h8 : (prefixModel m B ml Bl).len 8 ≤ Y := hp.1 8
    omega
  have h1 : Z ≤ Z^3 := Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ Z^3 := one_le_pow₀ hZ
  have hpre : budget prefixCode (initialModel m B ml Bl) ≤ prefixCode.length*Z^3 :=
    hp.2.trans (Nat.mul_le_mul_left _ (hYZ.trans h1))
  have hsuf : budget suffixCode (middleModel m B ml Bl) ≤ suffixCode.length*Z^3 :=
    hs.2.trans (Nat.mul_le_mul_left _ h1)
  have hm3 := hmin.trans (Nat.mul_le_mul_left 120 h1)
  change fullBudget m B ml Bl+1 ≤ (prefixCode.length+suffixCode.length+1017)*Z^3
  dsimp only [fullBudget,runtimeBound]
  change unaryModelBudget (finalModel m B ml Bl) ≤ 896*Z^3 at hu
  nlinarith only [hpre,hsuf,hm3,hu,h0]

/-- A fixed ordinary polynomial bounds every arithmetic operation, copy,
comparison and unary output in the metadata producer. Input padding is
charged through ml and Bl. Numeric B does not enter this input measure. -/
theorem runtime_ordinary :
    ∃ C d : ℕ, ∀ m B ml Bl, 0 < m → 0 < B →
      fullBudget m B ml Bl+1 ≤ C*(setupInput m ml Bl)^d := by
  have hepExists : ∃ e : ℕ, e = 6^prefixCode.length := ⟨_, rfl⟩
  have hesExists : ∃ e : ℕ, e = 6^suffixCode.length := ⟨_, rfl⟩
  have hcpExists : ∃ c : ℕ, c = polynomialCoefficient prefixCode.length := ⟨_, rfl⟩
  have hcsExists : ∃ c : ℕ, c = polynomialCoefficient suffixCode.length := ⟨_, rfl⟩
  let ep := Classical.choose hepExists
  let es := Classical.choose hesExists
  let cp := Classical.choose hcpExists
  let cs := Classical.choose hcsExists
  have hep : ep = 6^prefixCode.length := Classical.choose_spec hepExists
  have hes : es = 6^suffixCode.length := Classical.choose_spec hesExists
  have hcp : cp = polynomialCoefficient prefixCode.length := Classical.choose_spec hcpExists
  have hcs : cs = polynomialCoefficient suffixCode.length := Classical.choose_spec hcsExists
  let A := cs*(2*cp)^es
  let E := ep*es
  refine ⟨(prefixCode.length+suffixCode.length+1017)*A^3,E*3,?_⟩
  intro m B ml Bl hm hB
  let X := setupInput m ml Bl
  have hX : 1 ≤ X := by dsimp [X,setupInput]; omega
  have hY : 1 ≤ 2*prefixEnvelope m ml Bl := by
    have h := (envelopes_order m ml Bl).1
    change X ≤ prefixEnvelope m ml Bl at h
    omega
  have hp : prefixEnvelope m ml Bl ≤ cp*X^ep := by
    rw [hcp, hep]
    exact iterMajorant_polynomial _ _ hX
  have hs : setupEnvelope m ml Bl ≤ cs*(2*prefixEnvelope m ml Bl)^es :=
    by
      rw [hcs, hes]
      exact iterMajorant_polynomial _ _ hY
  have hZ : setupEnvelope m ml Bl ≤ A*X^E := by
    calc
      _ ≤ cs*(2*(cp*X^ep))^es := hs.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hp) _))
      _ = _ := by
        dsimp [A,E]
        rw [show 2*(cp*X^ep)=(2*cp)*X^ep by ring,mul_pow,← pow_mul]
        ring
  calc
    _ ≤ (prefixCode.length+suffixCode.length+1017)*(setupEnvelope m ml Bl)^3 :=
      fullBudget_envelope hm hB ml Bl
    _ ≤ (prefixCode.length+suffixCode.length+1017)*(A*X^E)^3 := by gcongr
    _ = _ := by rw [mul_pow,← pow_mul]; ring

end SubexponentialSAT.SqrtLog.CodeParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual sparse-code metadata production, with paid polynomial time and every-prefix word bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- One fixed ordinary polynomial bounds the metadata stage and every
temporary word. Its coefficients and degree precede all input values;
the numerical occurrence bound is not substituted for its word length. -/
theorem parameterTime_polynomial :
    ∃ C d : ℕ, ∀ m B W ml Bl, 0 < m → 0 < B → ml ≤ W → Bl ≤ W →
      W + parameterTime m B W ml Bl + 1 ≤ C * (m + W + 16) ^ d := by
  obtain ⟨C, e, hC⟩ := CodeParametersProgram.runtime_ordinary
  refine ⟨10000 * (C * 2 ^ e + 1) + 1, e + 1, ?_⟩
  intro m B W ml Bl hm hB hml hBl
  let X := m + W + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hinput : CodeParametersProgram.setupInput m ml Bl ≤ 2 * X := by
    dsimp [CodeParametersProgram.setupInput, X]
    omega
  have hbudget : CodeParametersProgram.fullBudget m B ml Bl + 1 ≤
      (C * 2 ^ e) * X ^ e := by
    calc
      _ ≤ C * (CodeParametersProgram.setupInput m ml Bl) ^ e := hC m B ml Bl hm hB
      _ ≤ C * (2 * X) ^ e := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput e)
      _ = _ := by rw [mul_pow]; ring
  have hp : X ^ e ≤ X ^ (e + 1) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ e + 1)
  have hW : W + 1 ≤ X ^ (e + 1) := by
    apply (show W + 1 ≤ X by dsimp [X]; omega).trans hlinear
  have hb := hbudget.trans (Nat.mul_le_mul_left (C * 2 ^ e) hp)
  unfold parameterTime
  change W + 10000 * (W + CodeParametersProgram.fullBudget m B ml Bl + 2) + 1 ≤
    (10000 * (C * 2 ^ e + 1) + 1) * X ^ (e + 1)
  nlinarith only [hb, hW]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- A fixed fifth-degree bound covers the entire canonical startup and
all of its temporary words. The numerical ambient dimension is explicit. -/
theorem canonicalStartTime_polynomial (n m W : ℕ) :
    W + canonicalStartTime n m W + 1 ≤
      6000 * (CodeSetupOuterCost.startupConstant + 1) * (n + m + W + 1) ^ 5 := by
  let C := CodeSetupOuterCost.startupConstant
  let X := n + m + W + 1
  let S := C * (W + 1) ^ 4
  let L := W + S
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hsize : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hK : HashSelect.loopCap n m + 1 ≤ 3 * X := by
    dsimp [HashSelect.loopCap, X]
    omega
  have hS : S ≤ C * X ^ 4 := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (by dsimp [X]; omega) 4)
  have hlinear : W + 1 ≤ X ^ 4 :=
    (show W + 1 ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by decide) X)
  have hL : L + 1 ≤ (C + 1) * X ^ 4 := by dsimp [L]; nlinarith only [hS, hlinear]
  have hI : I ≤ 300 * (C + 1) * X ^ 5 := by
    calc
      I ≤ 100 * (3 * X) * ((C + 1) * X ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 100 hK) hL
      _ = _ := by rw [pow_succ]; ring
  have hL5 : L + 1 ≤ (C + 1) * X ^ 5 := hL.trans
    (Nat.mul_le_mul_left (C + 1) (Nat.pow_le_pow_right hX (by decide : 4 ≤ 5)))
  change W + (S + (I + 18 * (L + I) + 16)) + 1 ≤ 6000 * (C + 1) * X ^ 5
  have hLdef : L = W + S := rfl
  nlinarith only [hI, hL5, hLdef]

/-- Fixed ordinary-polynomial transport across actual canonical startup and
metadata production. The incoming binary lengths are bounded by the proved
startup boundary, rather than by any exponential search duration. -/
theorem canonicalParameterTime_polynomial_oai :
    ∃ C d : ℕ, ∀ n m B W ml Bl, 0 < m → 0 < B →
      ml ≤ W + canonicalStartTime n m W → Bl ≤ W + canonicalStartTime n m W →
      W + canonicalStartTime n m W +
        parameterTime m B (W + canonicalStartTime n m W) ml Bl + 1 ≤
          C * (n + m + W + 16) ^ d := by
  obtain ⟨C, d, hC⟩ := parameterTime_polynomial
  let A := 6000 * (CodeSetupOuterCost.startupConstant + 1)
  refine ⟨C * (A + 1) ^ d, 5 * d, ?_⟩
  intro n m B W ml Bl hm hB hml hBl
  let U := W + canonicalStartTime n m W
  let X := n + m + W + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hU : U + 1 ≤ A * X ^ 5 :=
    (canonicalStartTime_polynomial n m W).trans
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by dsimp [X]; omega) 5))
  have hmX : m + 15 ≤ X ^ 5 :=
    (show m + 15 ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by decide) X)
  have hinput : m + U + 16 ≤ (A + 1) * X ^ 5 := by nlinarith only [hU, hmX]
  calc
    _ ≤ C * (m + U + 16) ^ d := hC m B U ml Bl hm hB hml hBl
    _ ≤ C * ((A + 1) * X ^ 5) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput d)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial_oai
