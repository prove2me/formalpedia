-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:52:24.971002+00:00
-- url     : https://prove2.me/submissions/e5053460-bc8e-448e-914f-0888fba6ffc5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_FrontendBounds_exportCost_poly
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_FrontendBounds_guarded_envelope
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_FrontendBounds_inputEnvelope_poly

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

theorem setupScale_pos (x : Input) (l : Fin 8 → ℕ) : 1 ≤ setupScale x l := by
  have := (loop_operands_le_cap x).1
  dsimp [setupScale]
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

theorem guarded_budget_bound (x : Input) (l : Fin 8 → ℕ) :
    guardedBudget x l ≤ guardedCode.length*polynomialCoefficient guardedCode.length*
      (setupScale x l)^(6^guardedCode.length) := by
  have hb := (budget_majorant guardedCode (initialModel x l) (setupScale x l)
    (initial_lengths_le x l) (guarded_scaleBound x l)).2
  have hp := iterMajorant_polynomial guardedCode.length (setupScale x l) (setupScale_pos x l)
  calc
    _  ≤  guardedCode.length*iterMajorant guardedCode.length (setupScale x l) := hb
    _  ≤  guardedCode.length*(polynomialCoefficient guardedCode.length*(setupScale x l)^(6^guardedCode.length)) :=
      Nat.mul_le_mul_left _ hp
    _ = _ := (Nat.mul_assoc _ _ _).symm

theorem setupScale_le (x : Input) (l : Fin 8 → ℕ) :
    setupScale x l ≤ 1000001*(inputMeasure x l)^6 := by
  have hm : magnitude x ≤ inputMeasure x l := by dsimp [inputMeasure]; omega
  have hl : (∑ i, l i) ≤ inputMeasure x l := by dsimp [inputMeasure]; omega
  have hp : inputMeasure x l ≤ (inputMeasure x l)^6 := Nat.le_self_pow (by decide) _
  calc
    setupScale x l = 1000000*(magnitude x)^6+∑ i, l i := rfl
    _  ≤  1000000*(inputMeasure x l)^6+(inputMeasure x l)^6 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 6)) (hl.trans hp)
    _ = _ := by ring_nf

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatchCost -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem final_lengths_le (x : Input) (l : Fin 8 → ℕ) (a : Fin 64) :
    (Prepared.finalModel x l).len a ≤ bitBound x l := by
  have h := (budget_majorant Layout.guardedCode (Layout.initialModel x l)
    (Layout.setupScale x l) (Layout.initial_lengths_le x l) (Layout.guarded_scaleBound x l)).1 a
  simpa only [Layout.guardedCode,result_append,Layout.model,Prepared.finalModel,bitBound] using h

theorem prepared_runtime_eq (x : Input) (l : Fin 8 → ℕ) :
    Prepared.runtimeBound x l=Layout.guardedBudget x l := by
  simp only [Prepared.runtimeBound,Layout.guardedBudget,Layout.guardedCode,budget_append,
    Layout.runtimeBound,Layout.model]

private theorem scaled_power (U V X d : ℕ) :
    U*(V*X^6)^d=(U*V^d)*X^(6*d) := by
  rw [mul_pow,← pow_mul]
  exact (Nat.mul_assoc U (V^d) (X^(6*d))).symm

private theorem assemble_cost (X Y N A P : ℕ)
    (hX : X ≤ N*A*P) (hY : Y ≤ A*P) (hP : 1 ≤ P) :
    X+100*Y+83+1 ≤ ((N+100)*A+84)*P := by
  nlinarith

/-- The complete physical parameter setup, including all guards and halt,
has a fixed ordinary-polynomial bound in input counts and padded bit lengths. -/
theorem runtime_ordinary :
    ∃ C d : ℕ, ∀ x l, runtimeBound x l+1 ≤ C*(Layout.inputMeasure x l)^d := by
  let N := Layout.guardedCode.length
  let D := 6^N
  let A := polynomialCoefficient N*1000001^D
  refine ⟨(N+100)*A+84,6*D,?_⟩
  intro x l
  let M := Layout.inputMeasure x l
  have hM : 1 ≤ M := by
    have hm := (magnitude_ge x).1
    dsimp [M,Layout.inputMeasure]
    omega
  have hpow : 1 ≤ M^(6*D) := one_le_pow₀ hM
  have hs := Layout.setupScale_le x l
  have hb : bitBound x l ≤ A*M^(6*D) := by
    calc
      bitBound x l  ≤  polynomialCoefficient N*(Layout.setupScale x l)^D :=
        iterMajorant_polynomial N (Layout.setupScale x l) (Layout.setupScale_pos x l)
      _  ≤  polynomialCoefficient N*(1000001*M^6)^D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs D)
      _ = A*M^(6*D) := scaled_power _ _ _ _
  have hn : Prepared.runtimeBound x l ≤ N*A*M^(6*D) := by
    rw [prepared_runtime_eq]
    calc
      Layout.guardedBudget x l  ≤  N*polynomialCoefficient N*(Layout.setupScale x l)^D :=
        Layout.guarded_budget_bound x l
      _  ≤  N*polynomialCoefficient N*(1000001*M^6)^D :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs D)
      _ = N*A*M^(6*D) := by
        rw [scaled_power]
        exact congrArg (fun z => z*M^(6*D)) (Nat.mul_assoc N (polynomialCoefficient N) (1000001^D))
  dsimp [runtimeBound]
  change Prepared.runtimeBound x l+100*bitBound x l+83+1 ≤ ((N+100)*A+84)*M^(6*D)
  exact assemble_cost _ _ _ _ _ hn hb hpow

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramPublic -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendPoly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open Circuit
noncomputable section

namespace Poly
variable {α : Type*} {measure f g : α → ℕ}

theorem mono (hf : Poly measure f) (h : ∀ a, g a ≤ f a) : Poly measure g := by
  obtain ⟨C,d,hf⟩ := hf
  exact ⟨C,d,fun a => (h a).trans (hf a)⟩

theorem const (measure : α → ℕ) (C : ℕ) : Poly measure (fun _ => C) :=
  ⟨C,0,by intro a; simp⟩

theorem add (hmeasure : ∀ a,1 ≤ measure a) (hf : Poly measure f) (hg : Poly measure g) :
    Poly measure (fun a => f a+g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C+D,d+e,?_⟩
  intro a
  have hd := Nat.pow_le_pow_right (hmeasure a) (show d ≤ d+e by omega)
  have he := Nat.pow_le_pow_right (hmeasure a) (show e ≤ d+e by omega)
  calc
    f a+g a ≤ C*(measure a)^d+D*(measure a)^e := Nat.add_le_add (hf a) (hg a)
    _ ≤ C*(measure a)^(d+e)+D*(measure a)^(d+e) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left D he)
    _ = (C+D)*(measure a)^(d+e) := (Nat.add_mul _ _ _).symm

theorem mul (hf : Poly measure f) (hg : Poly measure g) :
    Poly measure (fun a => f a*g a) := by
  obtain ⟨C,d,hf⟩ := hf
  obtain ⟨D,e,hg⟩ := hg
  refine ⟨C*D,d+e,?_⟩
  intro a
  calc
    f a*g a ≤ (C*(measure a)^d)*(D*(measure a)^e) := Nat.mul_le_mul (hf a) (hg a)
    _ = (C*D)*(measure a)^(d+e) := by rw [pow_add]; ac_rfl

theorem pow (hf : Poly measure f) (k : ℕ) : Poly measure (fun a => f a^k) := by
  obtain ⟨C,d,hf⟩ := hf
  refine ⟨C^k,d*k,?_⟩
  intro a
  calc
    f a^k ≤ (C*(measure a)^d)^k := Nat.pow_le_pow_left (hf a) k
    _ = C^k*(measure a)^(d*k) := by rw [mul_pow,pow_mul]

end Poly

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem inputMeasure_pos (a : Args) : 1 ≤ inputMeasure a := by
  have := (magnitude_ge a.1).1
  dsimp [inputMeasure,Layout.inputMeasure]
  omega

theorem nativeCost_poly : Poly inputMeasure nativeCost := by
  obtain ⟨C,d,h⟩ := Execute.runtime_ordinary
  refine ⟨C,d,fun a => ?_⟩
  exact (Nat.le_add_right (nativeCost a) 1).trans (h a.1 a.2)

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

theorem guarded_length_poly (j : Fin 64) : Poly inputMeasure (fun a => (guarded a).len j) :=
  nativeCost_poly.mono (fun a => guarded_length_le a j)

theorem guarded_cutoff_poly : Poly inputMeasure (fun a => (guarded a).val 29) :=
  inputEnvelope_poly.mono (fun a => (guarded_envelope a).2.1 29 (by simp [smallPorts]))

theorem offsetCost_poly : Poly inputMeasure offsetCost := by
  have hR := Poly.add inputMeasure_pos
    (Poly.mul (Poly.const inputMeasure 2) guarded_cutoff_poly) (Poly.const _ 1)
  have hL := Poly.add inputMeasure_pos
    (Poly.add inputMeasure_pos
      (Poly.add inputMeasure_pos (guarded_length_poly 3) (guarded_length_poly 21))
      (guarded_length_poly 29)) (Poly.const _ 11)
  exact Poly.mul (Poly.mul (Poly.const inputMeasure 5000) (Poly.pow hR 2)) (Poly.pow hL 2)

theorem bundle_poly : Poly inputMeasure bundle :=
  Poly.add inputMeasure_pos (Poly.add inputMeasure_pos
    (Poly.add inputMeasure_pos
      (Poly.add inputMeasure_pos
        (Poly.add inputMeasure_pos
          (Poly.add inputMeasure_pos (Poly.add inputMeasure_pos nativeCost_poly exportCost_poly)
            (guarded_length_poly 3)) (guarded_length_poly 21)) (guarded_length_poly 29))
      guarded_cutoff_poly) (Poly.const _ 1)) offsetCost_poly

theorem inputMeasure_le (x : Input) (l : Fin 8 → ℕ) (S : ℕ)
    (hv : CountsBound x S) (hl : ∀ i,l i ≤ S) : inputMeasure (x,l) ≤ 16*(S+1) := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  have h5 := hv 5
  have h6 := hv 6
  have h7 := hv 7
  change x.ambient ≤ S at h0
  change x.freeCount ≤ S at h1
  change x.clauses ≤ S at h2
  change x.occurrence ≤ S at h3
  change x.arity ≤ S at h4
  change x.factors ≤ S at h5
  change x.width ≤ S at h6
  change x.incidences ≤ S at h7
  have hsum : (∑ i,l i) ≤ 8*S := by
    calc
      _ ≤ ∑ i : Fin 8,S := Finset.sum_le_sum (fun i _ => hl i)
      _ = _ := by simp
  dsimp [inputMeasure,Layout.inputMeasure,magnitude]
  omega

/-- One pair of constants works for every measured query and every padding
of its eight binary inputs. No produced-value or produced-length premise. -/
theorem uniform_bundle_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      CountsBound x S → (∀ i,l i ≤ S) → bundle (x,l) ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := bundle_poly
  refine ⟨C*16^d,d,?_⟩
  intro x l S hv hl
  calc
    bundle (x,l) ≤ C*(inputMeasure (x,l))^d := h (x,l)
    _ ≤ C*(16*(S+1))^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (inputMeasure_le x l S hv hl) d)
    _ = (C*16^d)*(S+1)^d := by rw [mul_pow,Nat.mul_assoc]

/-- Solver-facing uniform bound: source instruction costs plus the three
actual offset-input word-length caps and its numeric exponent. -/
theorem uniform_polynomial :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      CountsBound x S → (∀ i,l i ≤ S) →
      Execute.runtimeBound x l+Exports.prepareBudget (Execute.guardedModel x l) ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 3 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 21 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).len 29 ≤ C*(S+1)^d ∧
      (Execute.guardedModel x l).val 29 ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := uniform_bundle_polynomial
  refine ⟨C,d,?_⟩
  intro x l S hv hl
  have hb := h x l S hv hl
  dsimp [bundle,nativeCost,exportCost,guarded] at hb
  omega

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical length bounds for the six paid serialization operations. The
input length vector remains explicit; no arbitrary padding bound is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open Circuit
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lengths (m : Model) (j : Fin 64) :
    (result code m).len j =
      if j=44 then m.len 35 else if j=45 then m.len 33+m.len 33+1 else m.len j := by
  by_cases h44 : j=44
  · subst j
    simp [code,result,next,output,lengthBound]
  · by_cases h45 : j=45
    · subst j
      simp [code,result,next,output,lengthBound]
    · simp [code,result,next,output,lengthBound,h44,h45]

theorem lengths_le (m : Model) (B : ℕ) (hm : ∀ j,m.len j ≤ B) (j : Fin 64) :
    (result code m).len j ≤ 2*B+1 := by
  rw [lengths]
  split_ifs <;> have h33 := hm 33 <;> have h35 := hm 35 <;> have hj := hm j <;> omega

/-- Applies in particular at the frontend's actual canonical input-length
vector. The bound changes with that vector, rather than quantifying it away. -/
theorem guarded_lengths_le (x : Input) (l : Fin 8 → ℕ) (j : Fin 64) :
    (result code (Execute.guardedModel x l)).len j ≤ 2*Execute.runtimeBound x l+1 :=
  lengths_le _ _ (FrontendBounds.guarded_length_le (x,l)) j

/-- One fixed polynomial bounds every serialized port whenever the eight
actual source values and their chosen physical length caps are bounded. -/
theorem uniform_guarded_lengths_polynomial_oai :
    ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ) (S : ℕ),
      FrontendBounds.CountsBound x S → (∀ i,l i ≤ S) →
      ∀ j, (result code (Execute.guardedModel x l)).len j ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := FrontendBounds.uniform_polynomial
  refine ⟨2*C+1,d,?_⟩
  intro x l S hv hl j
  have hb := (h x l S hv hl).1
  have hj := guarded_lengths_le x l j
  have hp : 1 ≤ (S+1)^d := one_le_pow₀ (by omega)
  nlinarith

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial_oai
