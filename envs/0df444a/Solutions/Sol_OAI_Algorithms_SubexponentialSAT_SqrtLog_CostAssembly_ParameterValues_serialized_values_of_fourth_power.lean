-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:04:37.804315+00:00
-- url     : https://prove2.me/submissions/04df9a7f-c429-4023-aaba-55508b2c26b7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S158

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layout_grid_square (n : ℕ) :
    (layoutR n ^ (4 * layoutQ n)) ^ 2 ≤ n + 16 := by
  have hbudget : 64 * (Nat.log2 (layoutR n) + 1) * layoutQ n ≤ L n := by
    exact Nat.mul_div_le (L n) (layoutDen n)
  have hlog : 1 ≤ Nat.log2 (n + 16) :=
    (Nat.le_log2 (by omega)).2 (by norm_num)
  have hexp : (Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2) ≤ Nat.log2 (n + 16) := by
    unfold L at hbudget
    nlinarith
  calc
    (layoutR n ^ (4 * layoutQ n)) ^ 2 = layoutR n ^ (4 * layoutQ n * 2) :=
      (pow_mul _ _ _).symm
    _ ≤ (2 ^ (Nat.log2 (layoutR n) + 1)) ^ (4 * layoutQ n * 2) :=
      Nat.pow_le_pow_left (Nat.lt_log2_self.le) _
    _ = 2 ^ ((Nat.log2 (layoutR n) + 1) * (4 * layoutQ n * 2)) :=
      (pow_mul _ _ _).symm
    _ ≤ 2 ^ Nat.log2 (n + 16) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ n + 16 := Nat.log2_self_le (by omega)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCrudeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

open Asymptotic

theorem L_le_magnitude (x : Input) : L x.freeCount ≤ 2*magnitude x := by
  have h := Nat.log2_le_self (x.freeCount+16)
  dsimp [L, magnitude]
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


theorem grow_ge (B : ℕ) : B ≤ grow B := by dsimp [grow]; nlinarith

theorem value_le {B K : ℕ} (hK : K ≤ B) (m : Model) (hm : ∀ j, m.val j ≤ B)
    (i : Instr) (hc : Constants i) (hp : PowerBound K m i) :
    value m.val i ≤ grow B := by
  have hg := grow_ge B
  have hb : 128 ≤ grow B := by dsimp [grow]; nlinarith
  cases i with
  | clear a => exact Nat.zero_le _
  | load a bs => exact hc.trans hb
  | copy a o h => exact (hm a).trans hg
  | add a b o ha hb => dsimp [value,grow]; have := hm a; have := hm b; nlinarith
  | mul a b o ha hb =>
      dsimp [value]
      exact (Nat.mul_le_mul (hm a) (hm b)).trans (by dsimp [grow]; nlinarith)
  | pow a b o ha hb => exact hp.trans (hK.trans hg)
  | quot a b o ha hb => exact (Nat.div_le_self _ _).trans ((hm a).trans hg)
  | sqrt a o h => exact (Nat.sqrt_le_self _).trans ((hm a).trans hg)
  | logSucc a =>
      have := Nat.log2_le_self (m.val a)
      have := hm a
      dsimp [value,grow]
      nlinarith
  | addConst a k => have := hm a; dsimp [Constants] at hc; dsimp [value,grow]; nlinarith
  | pred a => exact (Nat.sub_le _ _).trans ((hm a).trans hg)
  | maxTwo a => exact max_le (by dsimp [grow]; nlinarith) ((hm a).trans hg)

theorem result_le {B K : ℕ} (hK : K ≤ B) (is : List Instr) (m : Model)
    (hm : ∀ j, m.val j ≤ B) (hc : ∀ i ∈ is,Constants i) (hp : PowerBounds K is m) :
    ∀ j, (result is m).val j ≤ iter is.length B := by
  induction is generalizing B m with
  | nil => exact hm
  | cons i is ih =>
      apply ih (hK.trans (grow_ge B)) (next m i)
      · intro j
        by_cases hj : j=output i
        · subst j; simpa [next] using value_le hK m hm i (hc i (by simp)) hp.1
        · simpa [next,hj] using (hm j).trans (grow_ge B)
      · intro a ha; exact hc a (by simp [ha])
      · exact hp.2

theorem iter_ordinary (n : ℕ) {f : ℕ → ℕ} (hf : Polynomial.Ordinary f) :
    Polynomial.Ordinary (fun S => iter n (f S)) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
      exact ih (Polynomial.ordinary_pow (Polynomial.ordinary_add hf
        (Polynomial.ordinary_const 129)) 2)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValuesLayout
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


theorem initial_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Layout.initialModel x l).val j ≤ base x := by
  intro j
  dsimp [Layout.initialModel,Layout.initialValues,base,magnitude]
  split <;> omega

theorem grid_le (x : Input) (l : Fin 8 → ℕ) :
    (Layout.model x l).val 31 ≤ base x := by
  rw [(Layout.model_core_values x l).2.2.2.2.2.2.2]
  have hg := Asymptotic.layout_grid_square x.freeCount
  have hr : 1 ≤ Asymptotic.layoutR x.freeCount := by
    dsimp [Asymptotic.layoutR]; omega
  have hp : Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) ≤
      (Asymptotic.layoutR x.freeCount^(4*Asymptotic.layoutQ x.freeCount))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hr (by omega)
  change Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) ≤ base x
  have hb : x.freeCount+16 ≤ base x := by dsimp [base,magnitude]; omega
  exact hp.trans (hg.trans hb)

theorem log_field_le (Q : ℕ) : 3^(Nat.log2 Q+2) ≤ 16*(Q+1)^2 := by
  have hlog : 2^Nat.log2 Q ≤ Q+1 := by
    by_cases hQ : Q=0
    · subst Q; norm_num
    · exact (Nat.log2_self_le hQ).trans (by omega)
  have hp : 2^(Nat.log2 Q+2) ≤ 4*(Q+1) := by
    rw [pow_add]
    norm_num
    omega
  calc
    _  ≤  4^(Nat.log2 Q+2) := Nat.pow_le_pow_left (by decide) _
    _ = (2^(Nat.log2 Q+2))^2 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    _  ≤  (4*(Q+1))^2 := Nat.pow_le_pow_left hp _
    _ = _ := by ring

theorem field_le (x : Input) (l : Fin 8 → ℕ) :
    (Layout.model x l).val 35 ≤ base x := by
  have he : (Layout.model x l).val 35=
      3^(Nat.log2 ((Layout.model x l).val 21)+2) := by
    simp [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output,
      Layout.initialModel, Layout.initialValues, BinaryArithmetic.toNat,
      BinaryArithmetic.bitVal]
  rw [he,(Layout.model_core_values x l).2.2.2.2.1]
  have hQ : (produce x).Q ≤ 2*magnitude x :=
    (Nat.div_le_self _ _).trans (L_le_magnitude x)
  have hh : 16*((produce x).Q+1)^2 ≤ 16*(2*magnitude x+1)^2 := by
    gcongr
  exact (log_field_le _).trans (hh.trans (by dsimp [base]; omega))

theorem layout_powers (x : Input) (l : Fin 8 → ℕ) :
    PowerBounds (base x) Layout.code (Layout.initialModel x l) := by
  simp [Layout.code, Layout.coreCode, Layout.prefixCode, Layout.earlyCode,
    Layout.quotientCode, Layout.finishCode, Layout.heavyCode, Layout.powerCode,
    Layout.tailCode, PowerBounds, PowerBound, next, value, output]
  constructor
  · simpa [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output] using grid_le x l
  · simpa [Layout.model, Layout.code, Layout.coreCode, Layout.prefixCode,
      Layout.earlyCode, Layout.quotientCode, Layout.finishCode, Layout.heavyCode,
      Layout.powerCode, Layout.tailCode, result, next, value, output] using field_le x l

theorem layout_constants : ∀ i ∈ Layout.code,Constants i := by
  simp [Layout.code, Layout.coreCode, Layout.prefixCode, Layout.earlyCode,
    Layout.quotientCode, Layout.finishCode, Layout.heavyCode, Layout.powerCode,
    Layout.tailCode, Constants, BinaryArithmetic.bitVal]

theorem guard_constants : ∀ i ∈ GuardSetup.code,Constants i := by
  simp [GuardSetup.code, GuardSetup.preparation, GuardSetup.emissions,
    Constants, BinaryArithmetic.bitVal]

theorem guard_powers (B : ℕ) (m : Model) : PowerBounds B GuardSetup.code m := by
  simp [GuardSetup.code, GuardSetup.preparation, GuardSetup.emissions,
    PowerBounds, PowerBound]

theorem layout_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Layout.model x l).val j ≤ iter Layout.code.length (base x) :=
  result_le le_rfl _ _ (initial_le x l) layout_constants (layout_powers x l)

theorem prepared_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Prepared.finalModel x l).val j ≤
      iter GuardSetup.code.length (iter Layout.code.length (base x)) :=
  result_le le_rfl _ _ (layout_le x l) guard_constants (guard_powers _ _)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyParameterValues
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


theorem guarded_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Execute.guardedModel x l).val j ≤
      iter GuardSetup.code.length (iter Layout.code.length (base x)) := by
  intro j
  dsimp [Execute.guardedModel]
  split
  · exact prepared_le x l j
  · exact Nat.zero_le _

theorem serialization_constants : ∀ i ∈ Serialization.code,Constants i := by
  simp [Serialization.code,Constants]

theorem serialization_powers (B : ℕ) (m : Model) : PowerBounds B Serialization.code m := by
  simp [Serialization.code,PowerBounds,PowerBound]

/-- No positivity, guard, or padding-length premise is needed. -/
theorem serialized_values_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (result Serialization.code (Execute.guardedModel x l)).val j ≤ envelope (magnitude x) :=
  result_le le_rfl _ _ (guarded_le x l) serialization_constants (serialization_powers _ _)

theorem envelope_ordinary : Polynomial.Ordinary envelope := by
  apply iter_ordinary
  apply iter_ordinary
  apply iter_ordinary
  exact Polynomial.ordinary_add
    (Polynomial.ordinary_add Polynomial.ordinary_id
      (Polynomial.ordinary_mul (Polynomial.ordinary_const 16)
        (Polynomial.ordinary_pow
          (Polynomial.ordinary_add
            (Polynomial.ordinary_mul (Polynomial.ordinary_const 2) Polynomial.ordinary_id)
            (Polynomial.ordinary_const 1)) 2)))
    (Polynomial.ordinary_const 128)

/-- Fixed constants are chosen before the input, its padding, and the port. -/
theorem serialized_values_polynomial : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
    (S : ℕ), magnitude x ≤ S → ∀ j,
    (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := envelope_ordinary
  refine ⟨C,d,?_⟩
  intro x l S hS j
  exact (serialized_values_le x l j).trans ((h _).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)))

/-- The actual-query scalar theorem supplies magnitude ≤ n^4. This consequence
keeps all constants uniform over every query and every physical padding. -/
theorem serialized_values_of_fourth_power_oai : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
    (n : ℕ), magnitude x ≤ n^4 → ∀ j,
    (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(n+1)^d := by
  obtain ⟨C,d,h⟩ := serialized_values_polynomial
  refine ⟨C,4*d,?_⟩
  intro x l n hn j
  have hn4 : n^4+1 ≤ (n+1)^4 := by
    have he : (n+1)^4=n^4+4*n^3+6*n^2+4*n+1 := by ring
    rw [he]
    omega
  calc
    _  ≤  C*(n^4+1)^d := h x l (n^4) hn j
    _  ≤  C*((n+1)^4)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hn4 d)
    _ = _ := by rw [pow_mul]

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power_oai
