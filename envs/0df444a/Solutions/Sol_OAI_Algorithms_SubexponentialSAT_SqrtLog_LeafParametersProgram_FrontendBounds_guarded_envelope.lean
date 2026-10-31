-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:50:27.521869+00:00
-- url     : https://prove2.me/submissions/ac854cf2-84a1-47e9-8b03-2590e0558229

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact, computable square-root-log scheduling. No algorithmic assertion is
hidden in these numerical lemmas. Small inputs may have schedule zero. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem s_le_L (n : ℕ) : s n ≤ L n :=
  (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)

theorem four_le_logSize (n : ℕ) : 4 ≤ logSize n := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (n : ℝ) + 16)).mpr
  norm_num

theorem logSize_lt_L (n : ℕ) : logSize n < (L n : ℝ) := by
  simpa [logSize, L, Nat.cast_add, Nat.cast_ofNat] using
    SubexpExponentArithmetic.logb_lt_natLog2_add_one (n + 16)

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

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

theorem layoutR_le_L (n : ℕ) : layoutR n ≤ L n := by
  have h : (4 : ℝ) < L n := (four_le_logSize n).trans_lt (logSize_lt_L n)
  have hnat : 4 < L n := by exact_mod_cast h
  exact max_le (by omega) (s_le_L n)

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

theorem magnitude_ge (x : Input) :
    16 ≤ magnitude x ∧ x.freeCount ≤ magnitude x ∧ x.occurrence ≤ magnitude x := by
  dsimp [magnitude]
  omega

theorem L_le_magnitude (x : Input) : L x.freeCount ≤ 2*magnitude x := by
  have h := Nat.log2_le_self (x.freeCount+16)
  dsimp [L, magnitude]
  omega

theorem energy_le_magnitude (x : Input) :
    layoutEnergy x.freeCount x.occurrence ≤ 513*(magnitude x)^4 := by
  let H := magnitude x
  have hH : 1 ≤ H := by dsimp [H]; have := magnitude_ge x; omega
  have hL := L_le_magnitude x
  have hr := (layoutR_le_L x.freeCount).trans hL
  have hb := (magnitude_ge x).2.2
  have hlog := Nat.log2_le_self (64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2)
  have hprod : 64*x.occurrence*layoutR x.freeCount*(L x.freeCount)^2 ≤ 512*H^4 := by
    calc
      _ ≤ 64*H*(2*H)*(2*H)^2 := by gcongr
      _ = _ := by ring
  have hpow : 1 ≤ H^4 := one_le_pow₀ hH
  dsimp [layoutEnergy]
  change Nat.log2 _+1 ≤ 513*H^4
  omega

theorem loop_operands_le_cap (x : Input) :
    16 ≤ loopCap x ∧ L x.freeCount ≤ loopCap x ∧
    2*layoutQ x.freeCount ≤ loopCap x ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ loopCap x ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ loopCap x := by
  let H := magnitude x
  have hH : 16 ≤ H := (magnitude_ge x).1
  have hL := L_le_magnitude x
  have hQ : layoutQ x.freeCount ≤ 2*H := (Nat.div_le_self _ _).trans hL
  have hE := energy_le_magnitude x
  have hlog := Nat.log2_le_self (layoutQ x.freeCount)
  have hp1 : H ≤ H^6 := Nat.le_self_pow (by decide) _
  have hp5 : H^5 ≤ H^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hp0 : 1 ≤ H^6 := one_le_pow₀ (by omega)
  have hroot : 128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 131328*H^5 := by
    calc
      _ ≤ 128*(2*H)*(513*H^4) := by gcongr
      _ = _ := by ring
  change 16 ≤ 1000000*H^6 ∧ _ ∧ _ ∧ _ ∧ _
  dsimp [loopCap]
  change 16 ≤ 1000000*H^6 ∧ L x.freeCount ≤ 1000000*H^6 ∧
    2*layoutQ x.freeCount ≤ 1000000*H^6 ∧
    128*layoutQ x.freeCount*layoutEnergy x.freeCount x.occurrence ≤ 1000000*H^6 ∧
    Nat.log2 (layoutQ x.freeCount)+2 ≤ 1000000*H^6
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutCost -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic Asymptotic

/-- The only input values entering loop costs are precisely the four small
operands bounded in CrudeBounds. All power outputs affect later work through
binary word lengths alone. -/
theorem scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (loopCap x) code (initialModel x l) := by
  obtain ⟨h16,hL,hQ,hR,hd⟩ := loop_operands_le_cap x
  have hL' : (x.freeCount + 16).log2 + 1 ≤ loopCap x := by
    simpa [L] using hL
  have hR' : 128 * (layoutQ x.freeCount *
      layoutEnergy x.freeCount x.occurrence) ≤ loopCap x := by
    simpa only [Nat.mul_assoc] using hR
  have henergy :
      Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1 =
        layoutEnergy x.freeCount x.occurrence := by
    simp [layoutEnergy,pow_two,Nat.mul_assoc]
  have hRcomputed : 128 * (layoutQ x.freeCount *
      (Nat.log2 (64 * (x.occurrence *
        (layoutR x.freeCount * (L x.freeCount * L x.freeCount)))) + 1)) ≤ loopCap x := by
    rw [henergy]
    exact hR'
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hRcomputed
  have hQcomputed := hQ
  simp only [layoutQ,layoutDen,layoutR,s,w,L,pow_two] at hQcomputed
  rw [code,scaleBound_append]
  constructor
  · simp [coreCode,ScaleBound,scale,next,output,value,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal,Nat.mul_assoc]
    omega
  · have hQ' : (result coreCode (initialModel x l)).val 21 = layoutQ x.freeCount := by
      rw [coreCode,result_append]
      rw [result_value_frame finishCode _ 21]
      · exact (prefix_values x l).2.2
      · decide
    simp [tailCode,ScaleBound,scale,next,output,value,hQ']
    omega

theorem guard_scaleBound (m : Model) (B : ℕ) (hB : 16 ≤ B) :
    ScaleBound B GuardSetup.code m := by
  rw [GuardSetup.code, scaleBound_append]
  constructor
  · simp [GuardSetup.preparation, ScaleBound, scale]
    omega
  · simp [GuardSetup.emissions, ScaleBound, scale]
    omega

theorem initial_lengths_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ a, (initialModel x l).len a ≤ setupScale x l := by
  intro a
  dsimp [initialModel]
  split_ifs with h
  · have hs : l ⟨a.val,h⟩ ≤ ∑ i, l i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    dsimp [setupScale]
    omega
  · exact Nat.zero_le _

theorem guarded_scaleBound (x : Input) (l : Fin 8 → ℕ) :
    ScaleBound (setupScale x l) guardedCode (initialModel x l) := by
  rw [guardedCode,scaleBound_append]
  constructor
  · exact scaleBound_mono _ _ (by dsimp [setupScale]; omega) _ _ (scaleBound x l)
  · exact guard_scaleBound _ _ (by have := (loop_operands_le_cap x).1; dsimp [setupScale]; omega)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem final_lengths_le (x : Input) (l : Fin 8 → ℕ) (a : Fin 64) :
    (Prepared.finalModel x l).len a ≤ bitBound x l := by
  have h := (budget_majorant Layout.guardedCode (Layout.initialModel x l)
    (Layout.setupScale x l) (Layout.initial_lengths_le x l) (Layout.guarded_scaleBound x l)).1 a
  simpa only [Layout.guardedCode,result_append,Layout.model,Prepared.finalModel,bitBound] using h

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem bitBound_le_runtime (x : Input) (l : Fin 8 → ℕ) :
    Execute.bitBound x l ≤ Execute.runtimeBound x l := by
  dsimp [Execute.runtimeBound]
  omega

theorem guarded_length_le (a : Args) (j : Fin 64) : (guarded a).len j ≤ nativeCost a := by
  by_cases hj : j.val < 44
  · change (if j.val < 44 then _ else _) ≤ _
    rw [ite_eq_left hj]
    exact (Execute.final_lengths_le a.1 a.2 j).trans (bitBound_le_runtime a.1 a.2)
  · simp [guarded,Execute.guardedModel,hj]

theorem guarded_core (a : Args) :
    (guarded a).val 0=a.1.ambient ∧ (guarded a).val 5=a.1.factors ∧
    (guarded a).val 18=(produce a.1).r ∧ (guarded a).val 21=(produce a.1).Q ∧
    (guarded a).val 29=(produce a.1).R := by
  have h0 := Execute.guardedModel_input a.1 a.2 0
  have h5 := Execute.guardedModel_input a.1 a.2 5
  have h18 := Execute.guardedModel_radius a.1 a.2
  have h21 := Execute.guardedModel_public a.1 a.2 4
  have h29 := Execute.guardedModel_public a.1 a.2 6
  obtain ⟨_,_,_,_,hQ,_,hR,_⟩ := Layout.model_core_values a.1 a.2
  refine ⟨?_,?_,h18,?_,?_⟩
  · simpa [guarded,Layout.initialValues] using h0
  · simpa [guarded,Layout.initialValues] using h5
  · exact h21.trans hQ
  · exact h29.trans hR

theorem small_parameters_le (x : Input) :
    (produce x).r ≤ loopCap x ∧ (produce x).Q ≤ loopCap x ∧
      (produce x).R ≤ loopCap x+4 := by
  obtain ⟨_,hL,_,hoperand,_⟩ := loop_operands_le_cap x
  refine ⟨(layoutR_le_L x.freeCount).trans hL,?_,?_⟩
  · exact (Nat.div_le_self _ _).trans hL
  · exact Nat.add_le_add_right ((Nat.sqrt_le_self _).trans hoperand) 4

theorem guarded_envelope_oai (a : Args) :
    (∀ j,(guarded a).len j ≤ inputEnvelope a) ∧
    (∀ j∈smallPorts,(guarded a).val j ≤ inputEnvelope a) ∧ 0 < (guarded a).val 18 := by
  obtain ⟨h0,h5,hr,hQ,hR⟩ := guarded_core a
  obtain ⟨hrB,hQB,hRB⟩ := small_parameters_le a.1
  have hbase : a.1.ambient ≤ inputMeasure a ∧ a.1.factors ≤ inputMeasure a := by
    dsimp [inputMeasure,Layout.inputMeasure,magnitude]
    omega
  have hrad := produce_r_ge_two a.1
  refine ⟨fun j => (guarded_length_le a j).trans (by dsimp [inputEnvelope]; omega),?_,?_⟩
  · intro j hj
    simp only [smallPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl
    · rw [h0]; dsimp [inputEnvelope]; omega
    · rw [h5]; dsimp [inputEnvelope]; omega
    · rw [hr]; dsimp [inputEnvelope]; omega
    · rw [hQ]; dsimp [inputEnvelope]; omega
    · rw [hR]; dsimp [inputEnvelope]; omega
  · omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded_envelope_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.guarded_envelope_oai
