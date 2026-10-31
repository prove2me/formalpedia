-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost_poly
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:49:40.324239+00:00
-- url     : https://prove2.me/submissions/97e77bb8-d4d5-4eb0-a320-b1e5afc0e130

import Mathlib
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_FrontendBounds_guarded_envelope
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafParametersProgram_FrontendBounds_inputEnvelope_poly

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

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCacheWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid binary metadata for the integer entry cache. The centered interval
start on port46 is produced by `SubexpIntervalStartProgram.program`; its
semantic identification is `SubexpIntervalStart.value_eq_intervalStart`.
This stage preserves that word and the parameter table while forming Qr and
the sufficient scalar width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem values (m : Model) :
    (result code m).val 47=m.val 21*m.val 18 ∧
    (result code m).val 50=1+2*m.val 46*m.val 29+m.val 21 := by
  simp [code,result,next,value,output]
  ring

theorem frame (m : Model) (a : Fin 64)
    (h47 : a≠47) (h48 : a≠48) (h49 : a≠49) (h50 : a≠50) :
    (result code m).val a=m.val a := by
  simp [code,result,next,value,output,h47,h48,h49,h50]

theorem scaleBound (m : Model) : ScaleBound 2 code m := by
  simp [ScaleBound,code,scale]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem prepare_frame (m : Model) (a : Fin 64) (ha : a.val < 46) :
    (result prepare m).val a=m.val a ∧ (result prepare m).len a=m.len a := by
  have hne (k : Fin 64) (hk : 46 ≤ k.val) : a≠k := by
    intro he; subst k; omega
  simp [prepare,result,next,output,lengthBound,hne _ (by decide : 46 ≤ (46 : Fin 64).val),
    hne _ (by decide : 46 ≤ (47 : Fin 64).val),hne _ (by decide : 46 ≤ (48 : Fin 64).val),
    hne _ (by decide : 46 ≤ (49 : Fin 64).val),hne _ (by decide : 46 ≤ (50 : Fin 64).val),
    hne _ (by decide : 46 ≤ (51 : Fin 64).val),hne _ (by decide : 46 ≤ (52 : Fin 64).val),
    hne _ (by decide : 46 ≤ (53 : Fin 64).val),hne _ (by decide : 46 ≤ (54 : Fin 64).val),
    hne _ (by decide : 46 ≤ (55 : Fin 64).val),hne _ (by decide : 46 ≤ (56 : Fin 64).val),
    hne _ (by decide : 46 ≤ (57 : Fin 64).val),hne _ (by decide : 46 ≤ (58 : Fin 64).val),
    hne _ (by decide : 46 ≤ (59 : Fin 64).val),hne _ (by decide : 46 ≤ (60 : Fin 64).val),
    hne _ (by decide : 46 ≤ (61 : Fin 64).val),hne _ (by decide : 46 ≤ (62 : Fin 64).val),
    hne _ (by decide : 46 ≤ (63 : Fin 64).val)]

theorem intervalModel_input (m : Model) (a : Fin 64) (ha : a.val < 46) :
    (intervalModel m).val a=m.val a := by
  have hne : a≠46 := by intro h; subst a; contradiction
  simpa [intervalModel,hne] using (prepare_frame m a ha).1

theorem final_values (m : Model) :
    (finalModel m).val 29=m.val 29 ∧
    (finalModel m).val 46=Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29) ∧
    (finalModel m).val 47=m.val 21*m.val 18 ∧
    (finalModel m).val 50=1+2*
      Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21 := by
  have hi (a : Fin 64) (ha : a.val < 46) := intervalModel_input m a ha
  have hA : (intervalModel m).val 46=
      Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29) := by
    simp [intervalModel]
  have hv := CacheWidth.values (intervalModel m)
  refine ⟨?_,?_,?_,?_⟩
  · exact (CacheWidth.frame (intervalModel m) 29 (by decide) (by decide)
      (by decide) (by decide)).trans (hi 29 (by decide))
  · exact (CacheWidth.frame (intervalModel m) 46 (by decide) (by decide)
      (by decide) (by decide)).trans hA
  · simpa only [finalModel,hi 21 (by decide),hi 18 (by decide)] using hv.1
  · simpa only [finalModel,hA,hi 29 (by decide),hi 21 (by decide)] using hv.2

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem intervalModel_frame (m : Model) (j : Fin 64) (hj : j.val < 46) :
    (Interval.finalModel m).val j=m.val j ∧ (Interval.finalModel m).len j=m.len j := by
  have h46 : j≠46 := by intro h; subst j; norm_num at hj
  have h47 : j≠47 := by intro h; subst j; norm_num at hj
  have h48 : j≠48 := by intro h; subst j; norm_num at hj
  have h49 : j≠49 := by intro h; subst j; norm_num at hj
  have h50 : j≠50 := by intro h; subst j; norm_num at hj
  simpa [Interval.finalModel,CacheWidth.code,Interval.intervalModel,result,next,output,
    lengthBound,h46,h47,h48,h49,h50] using Interval.prepare_frame m j hj

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

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

theorem self (measure : α → ℕ) : Poly measure measure :=
  ⟨1,1,by intro a; simp⟩

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

theorem iter (hf : Poly measure f) (hpos : ∀ a,1 ≤ f a) (k : ℕ) :
    Poly measure (fun a => iterMajorant k (f a)) := by
  apply (mul (const measure (polynomialCoefficient k)) (pow hf (6^k))).mono
  intro a
  exact iterMajorant_polynomial k (f a) (hpos a)

theorem compose (hmeasure : ∀ a,1 ≤ measure a) (hf : Poly measure f)
    {g : ℕ → ℕ} (hg : Poly (fun B => B+1) g) : Poly measure (fun a => g (f a)) := by
  obtain ⟨C,d,hg⟩ := hg
  apply (mul (const measure C) (pow (add hmeasure hf (const measure 1)) d)).mono
  exact fun a => hg (f a)
end Poly

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual parameter/export prefix. Only
input counts and input word lengths enter the final bound. In particular the
large grid value never becomes a unary counter in this prefix. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod



theorem height_ge (B : ℕ) :
    1 ≤ height B ∧ B ≤ height B ∧ preHeight B ≤ height B ∧
    widthHeight B ≤ height B ∧ valueHeight B ≤ height B := by dsimp [height]; omega

theorem prepare_scale (B : ℕ) (m : Model) : ScaleBound (B+2) Interval.prepare m := by
  simp [Interval.prepare,ScaleBound,scale]

theorem interval_bounds (m : Model) (B : ℕ) (hl : ∀ j,m.len j ≤ B) :
    (∀ j,(Interval.finalModel m).len j ≤ widthHeight B) ∧
    Interval.runtimeBound m ≤ Interval.prepare.length*preHeight B+
      10000*(3*B+1)^2+1+CacheWidth.code.length*widthHeight B := by
  have hpre := budget_majorant Interval.prepare m (B+2)
    (fun j => (hl j).trans (by omega)) (prepare_scale B m)
  have hint : ∀ j,(Interval.intervalModel m).len j ≤ widthInput B := by
    intro j
    by_cases hj : j=46
    · subst j
      simp only [Interval.intervalModel,Function.update_self]
      have h1 := hl 18
      have h2 := hl 21
      have h3 := hl 29
      dsimp [widthInput]
      omega
    · simp only [Interval.intervalModel,Function.update_of_ne hj]
      exact (hpre.1 j).trans (by dsimp [preHeight,widthInput]; omega)
  have hwidth : 2 ≤ widthInput B := by dsimp [widthInput]; omega
  have hw := budget_majorant CacheWidth.code (Interval.intervalModel m) (widthInput B) hint
    (scaleBound_mono 2 _ hwidth _ _ (CacheWidth.scaleBound _))
  refine ⟨hw.1,?_⟩
  have hsum : m.len 18+m.len 21+m.len 29+1 ≤ 3*B+1 := by
    have := hl 18; have := hl 21; have := hl 29; omega
  unfold Interval.runtimeBound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpre.2
    (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hsum 2))) le_rfl) hw.2

theorem interval_values (m : Model) (B : ℕ)
    (hv : ∀ j∈smallPorts,m.val j ≤ B) (hr : 0 < m.val 18) :
    ∀ j∈resultPorts,(Interval.finalModel m).val j ≤ valueHeight B := by
  have h0 := hv 0 (by simp [smallPorts])
  have h5 := hv 5 (by simp [smallPorts])
  have hrB := hv 18 (by simp [smallPorts])
  have hQB := hv 21 (by simp [smallPorts])
  have hRB := hv 29 (by simp [smallPorts])
  have hA := (Interval.intervalStart_le_Q (m.val 18) (m.val 21) (m.val 29) hr).trans hQB
  have hvals := Interval.final_values m
  have hB : B ≤ valueHeight B := by dsimp [valueHeight]; nlinarith
  have hQr : m.val 21*m.val 18 ≤ valueHeight B := by
    have hh := Nat.mul_le_mul hQB hrB
    dsimp [valueHeight]
    nlinarith
  have hW : 1+2*Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21 ≤ valueHeight B := by
    have hh := Nat.mul_le_mul hA hRB
    dsimp [valueHeight]
    nlinarith
  intro j hj
  simp only [resultPorts,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [(Exports.intervalModel_frame m 0 (by decide)).1]; exact h0.trans hB
  · rw [(Exports.intervalModel_frame m 5 (by decide)).1]; exact h5.trans hB
  · rw [(Exports.intervalModel_frame m 18 (by decide)).1]; exact hrB.trans hB
  · rw [(Exports.intervalModel_frame m 21 (by decide)).1]; exact hQB.trans hB
  · rw [hvals.1]; exact hRB.trans hB
  · rw [hvals.2.1]; exact hA.trans hB
  · rw [hvals.2.2.1]; exact hQr
  · rw [hvals.2.2.2]; exact hW

theorem unaryBound_mono (v l H : ℕ) (hv : v ≤ H) (hl : l ≤ H) :
    Cache.unaryBound v l ≤ Cache.unaryBound H H := by unfold Cache.unaryBound; gcongr

theorem unaryBound_square (H : ℕ) (hH : 1 ≤ H) : Cache.unaryBound H H ≤ 141*H^2 := by
  have hsq : H ≤ H^2 := by nlinarith
  dsimp [Cache.unaryBound]
  nlinarith

theorem cacheLength_bound (m : Model) (H : ℕ) (hl : ∀ j,m.len j ≤ H)
    (hv : ∀ j∈resultPorts,m.val j ≤ H) (j : Fin 64) : Exports.cacheLength m j ≤ H := by
  unfold Exports.cacheLength
  split_ifs
  · exact hv 50 (by simp [resultPorts])
  · exact hv 46 (by simp [resultPorts])
  · exact hv 29 (by simp [resultPorts])
  · exact hl j

set_option maxHeartbeats 3200000 in
theorem tail_bounds (m : Model) (H : ℕ) (hl : ∀ j,m.len j ≤ H)
    (hv : ∀ j∈resultPorts,m.val j ≤ H) :
    Cache.unaryRuntime m ≤ 3*Cache.unaryBound H H ∧
    Exports.exportModelBudget m ≤ 16*Cache.unaryBound H H ∧
    Exports.clearModelBudget m ≤ 36*H+57 := by
  have hu (j : Fin 64) (hj : j∈resultPorts) :
      Cache.unaryBound (m.val j) (m.len j) ≤ Cache.unaryBound H H :=
    unaryBound_mono _ _ _ (hv j hj) (hl j)
  constructor
  · have h29 := hu 29 (by simp [resultPorts])
    have h46 := hu 46 (by simp [resultPorts])
    have h50 := hu 50 (by simp [resultPorts])
    dsimp [Cache.unaryRuntime]
    omega
  constructor
  · have hf : ∀ i : Fin 16,Exports.exportFieldBound m i ≤ Cache.unaryBound H H := by
      intro i
      unfold Exports.exportFieldBound
      split_ifs with hi
      · apply hu
        fin_cases i <;> simp_all [Exports.localSource,resultPorts]
      · have hc := cacheLength_bound m H hl hv (Exports.localSource i)
        dsimp [Cache.unaryBound]
        omega
    have hh := List.sum_le_sum (l := List.finRange 16)
      (f := Exports.exportFieldBound m) (g := fun _ => Cache.unaryBound H H) (fun i _ => hf i)
    change (List.finRange 16 |>.map (Exports.exportFieldBound m)).sum ≤
      16 * Cache.unaryBound H H
    exact hh.trans_eq (by simp; omega)
  · have hh := List.sum_le_sum (l := List.finRange 18)
      (f := fun i => Exports.cacheLength m ⟨46+i.val,by omega⟩) (g := fun _ => H)
      (fun i _ => cacheLength_bound m H hl hv _)
    have hs : ((List.finRange 18).map (fun i => Exports.cacheLength m ⟨46+i.val,by omega⟩)).sum ≤ 18*H := by
      exact hh.trans_eq (by simp; omega)
    dsimp [Exports.clearModelBudget]
    omega

theorem prepareBudget_bound (m : Model) (B : ℕ) (hl : ∀ j,m.len j ≤ B)
    (hv : ∀ j∈smallPorts,m.val j ≤ B) (hr : 0 < m.val 18) :
    Exports.prepareBudget m ≤ postMajorant B := by
  obtain ⟨hH,hBH,hpreH,hwH,hvH⟩ := height_ge B
  obtain ⟨hlf,hint⟩ := interval_bounds m B hl
  have hvf := interval_values m B hv hr
  obtain ⟨hu,he,hc⟩ := tail_bounds (Interval.finalModel m) (height B)
    (fun j => (hlf j).trans hwH) (fun j hj => (hvf j hj).trans hvH)
  have hsquare := unaryBound_square (height B) hH
  have hsq : height B ≤ (height B)^2 := by nlinarith
  have hroot : (3*B+1)^2 ≤ 16*(height B)^2 := by
    calc
      _ ≤ (4*height B)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hint' : Interval.runtimeBound m ≤ 160028*(height B)^2 := by
    have hpre : Interval.prepare.length=18 := by rfl
    have hw : CacheWidth.code.length=9 := by rfl
    rw [hpre,hw] at hint
    nlinarith
  unfold Exports.prepareBudget Cache.runtimeBound postMajorant
  nlinarith

theorem postMajorant_poly : Poly (fun B => B+1) postMajorant := by
  have hmeasure : ∀ B : ℕ,1 ≤ B+1 := by omega
  have hp0 : Poly (fun B => B+1) preHeight :=
    Poly.iter (Poly.add hmeasure (Poly.self _) (Poly.const _ 1))
      (by intro B; omega) Interval.prepare.length
  have hp1 : Poly (fun B => B+1) widthInput :=
    Poly.add hmeasure hp0 (Poly.mul (Poly.const _ 16) (Poly.self _))
  have hp2 : Poly (fun B => B+1) widthHeight :=
    Poly.iter hp1 (by intro B; dsimp [widthInput]; omega) CacheWidth.code.length
  have hpv : Poly (fun B => B+1) valueHeight :=
    Poly.mul (Poly.const _ 4) (Poly.pow (Poly.self _) 2)
  have hpid : Poly (fun B => B+1) (fun B => B) := (Poly.self _).mono (by intro B; omega)
  have hh : Poly (fun B => B+1) height :=
    Poly.add hmeasure (Poly.add hmeasure (Poly.add hmeasure (Poly.add hmeasure hp0 hp2) hpv) hpid)
      (Poly.const _ 1)
  exact Poly.mul (Poly.const _ 200000) (Poly.pow hh 2)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

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

theorem inputMeasure_pos (a : Args) : 1 ≤ inputMeasure a := by
  have := (magnitude_ge a.1).1
  dsimp [inputMeasure,Layout.inputMeasure]
  omega

theorem exportCost_poly_oai : Poly inputMeasure exportCost := by
  apply (Poly.compose inputMeasure_pos inputEnvelope_poly postMajorant_poly).mono
  intro a
  obtain ⟨hl,hv,hr⟩ := guarded_envelope a
  exact prepareBudget_bound (guarded a) (inputEnvelope a) hl hv hr

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost_poly_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.exportCost_poly_oai
