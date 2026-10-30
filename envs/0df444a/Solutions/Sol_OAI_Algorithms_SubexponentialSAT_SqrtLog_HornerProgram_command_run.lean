-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:47:21.684191+00:00
-- url     : https://prove2.me/submissions/172e7649-8bc5-417c-bf21-ce4999695d84

import Mathlib
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S119

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native streaming Horner control for arbitrary-width coefficient
representations. Arithmetic callbacks are finite commands with exact framed
traces. No loop bound or ring dimension occurs in the control table. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update binaryStep binaryStep_run)

theorem takeCoefficient_run (s : Store) (bits rest : List Bool)
    (hs : s 246 = bits.reverse ++ rest) (hw : (s 250).length = bits.length)
    (h241 : s 241 = []) (h251 : s 251 = []) (h252 : s 252 = []) :
    ExecutesIn takeCoefficient (23 * bits.length + 18) s
      (Function.update (Function.update s 246 rest) 241 bits) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  have h1 := takeWord_eval d 250 251 252 246 241 0 1
    (by decide) (by decide) bits.reverse rest hs h251 h252 (by simpa using hw)
  let mid := afterTake d 246 241 0 1 bits.reverse rest
  have h2 := reverse_eval mid 241 251 252 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [mid, afterTake, d, h251]) (by simp [mid, afterTake, d, h252])
  have he : afterReverse mid 241 0 1 =
      (⟨readRegs regs 0 1 none,
        Function.update (Function.update s 246 rest) 241 bits⟩ : Data) := by
    apply state_ext
    · simp [afterReverse, mid, afterTake, d, StackRoutines.readRegs_reset]
    · simp [afterReverse, mid, afterTake, d, StackRoutines.reverseStacks, h241]
  rw [he] at h2
  have h := h1.seq h2
  refine ⟨14 * bits.reverse.length + 11 + (9 * (mid.stacks 241).length + 7),
    readRegs regs 0 1 none, ?_, ?_⟩
  · simp [mid, afterTake, d, h241]
    omega
  · simpa only [takeCoefficient] using h

theorem iteration_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (s : Store) (a x c : C) (rest : List Bool) (hf : LowFrame base s)
    (hacc : s 240 = encode a) (hx : s 247 = encode x)
    (hs : s 246 = (encode c).reverse ++ rest) (hw : (s 250).length = W)
    (h120 : s 120 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (h245 : s 245 = []) (h251 : s 251 = []) (h252 : s 252 = []) :
    ExecutesIn (iteration multiply add) (Km + Ka + 50 * W + 47) s
      (Function.update (Function.update s 246 rest) 240
        (encode (stepValue mulOp addOp x a c))) := by
  let p := mulOp a x
  let v := stepValue mulOp addOp x a c
  let s1 := Function.update s 241 (encode x)
  let s2 := Function.update s1 240 (encode p)
  let s3 := Function.update s2 241 []
  let s4 := Function.update (Function.update s3 246 rest) 241 (encode c)
  let s5 := Function.update s4 240 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 241 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 240 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 241 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update
    (lowFrame_update hf3 246 (by decide) _) 241 (by decide) _
  have h1 : ExecutesIn (copy 247 241) (7 * W + 5) s s1 := by
    simpa [s1, hx, h241, hwidth] using copy_run 247 241 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (binaryStep multiply) (Km + 8 * W + 9) s1 s2 :=
    binaryStep_run base encode multiply mulOp Km W hm (fun a => (hwidth a).le)
      s1 a x hf1 (by simp [s1, hacc]) (by simp [s1])
      (by simp [s1, h244]) (by simp [s1, h245])
  have h3 : ExecutesIn (clear 241) (2 * W + 3) s2 s3 := by
    simpa [s3, s2, s1, hwidth] using clear_run 241 s2
  have h4 : ExecutesIn takeCoefficient (23 * W + 18) s3 s4 := by
    simpa only [hwidth] using takeCoefficient_run s3 (encode c) rest
      (by simp [s3, s2, s1, hs]) (by simp [s3, s2, s1, hw, hwidth])
      (by simp [s3]) (by simp [s3, s2, s1, h251])
      (by simp [s3, s2, s1, h252])
  have h5 : ExecutesIn (binaryStep add) (Ka + 8 * W + 9) s4 s5 :=
    binaryStep_run base encode add addOp Ka W ha (fun a => (hwidth a).le)
      s4 p c hf4 (by simp [s4, s3, s2]) (by simp [s4])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
  have he : Function.update s5 241 [] =
      Function.update (Function.update s 246 rest) 240 (encode v) := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h241' : i = 241 <;>
      by_cases h246 : i = 246 <;>
      simp [s5, s4, s3, s2, s1, h240, h241', h246, h241]
  have h6 : ExecutesIn (clear 241) (2 * W + 3) s5
      (Function.update (Function.update s 246 rest) 240 (encode v)) := by
    have h := clear_run 241 s5
    rw [he] at h
    simpa [s5, s4, hwidth] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert h using 1 <;> first | omega | rfl

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl)

theorem popped_ready {C : Type*} (base : Store) (encode : C → List Bool)
    (cs : List C) (a : C) (count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped counterPorts (⟨regs, ready base encode cs a count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?, ready base encode cs a count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped, counterPorts, ready]
  · simp [UnaryForPrograms.popped, counterPorts, ready]

theorem traversal_visits {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : C → C → C) (K : ℕ)
    (hstep : ∀ c cs a count, ExecutesIn body K
      (ready base encode (c :: cs) a count)
      (ready base encode cs (step a c) count))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length)
    (regs : Fin 16 → Bool) :
    ∃ costs n regs',
      UnaryForPrograms.Visits counterPorts body costs n
        (⟨regs, ready base encode cs a count⟩ : Data)
        (⟨regs', ready base encode [] (fold step cs a) []⟩ : Data) ∧
      n ≤ cs.length * (K + 2) + 2 := by
  induction cs generalizing count a regs with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa only [popped_ready, List.head?_nil, List.tail_nil, fold,
        SubexpHornerControl.fold] using
        UnaryForPrograms.Visits.done (p := counterPorts) (body := body)
          (⟨regs, ready base encode [] a []⟩ : Data) (by simp [ready, counterPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hl : count.length = cs.length := by simpa using hlen
          obtain ⟨nb, rb, hnb, hb⟩ := hstep c cs a count (readRegs regs 0 1 (some bit))
          obtain ⟨costs, nt, rt, ht, hnt⟩ := ih (step a c) count hl rb
          refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
          · have h := UnaryForPrograms.Visits.step
              (p := counterPorts) (body := body)
              (d := (⟨regs, ready base encode (c :: cs) a (bit :: count)⟩ : Data))
              (by simp [ready, counterPorts])
              (by simpa only [popped_ready, List.head?_cons, List.tail_cons] using hb)
              (by simp [ready, counterPorts, UnaryForPrograms.popped]) ht
            simpa only [fold, SubexpHornerControl.fold] using h
          · simp only [List.length_cons]
            nlinarith

theorem traversal_run {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : C → C → C) (K : ℕ)
    (hstep : ∀ c cs a count, ExecutesIn body K
      (ready base encode (c :: cs) a count)
      (ready base encode cs (step a c) count))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length) :
    ExecutesIn (traversal body) (cs.length * (K + 2) + 2)
      (ready base encode cs a count)
      (ready base encode [] (fold step cs a) []) := by
  intro regs
  obtain ⟨costs, n, rf, ht, hn⟩ := traversal_visits base encode body step K
    hstep cs a count hlen regs
  exact ⟨n, rf, hn, ht.eval⟩

theorem streaming_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (x : C) (hx : base 247 = encode x) (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = [])
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length) :
    ExecutesIn (traversal (iteration multiply add))
      (cs.length * (Km + Ka + 50 * W + 49) + 2)
      (ready base encode cs a count)
      (ready base encode [] (fold (stepValue mulOp addOp x) cs a) []) := by
  apply traversal_run base encode (iteration multiply add) (stepValue mulOp addOp x)
    (Km + Ka + 50 * W + 47) _ cs a count hlen
  intro c cs a count
  let s := ready base encode (c :: cs) a count
  have hf : LowFrame base s := lowFrame_update
    (lowFrame_update (lowFrame_update (lowFrame_refl base) 246 (by decide) _)
      240 (by decide) _) 248 (by decide) _
  have h := iteration_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
    s a x c (backward encode cs) hf
    (by simp [s, ready]) (by simp [s, ready, hx])
    (by simp [s, ready, backward, SubexpHornerControl.backward])
    (by simp [s, ready, hw])
    (by simp [s, ready, h120]) (by simp [s, ready, h241])
    (by simp [s, ready, h244]) (by simp [s, ready, h245])
    (by simp [s, ready, h251]) (by simp [s, ready, h252])
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;>
    by_cases h248 : i = 248 <;>
    simp [s, ready, h240, h246, h248]

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

theorem encodePolynomial_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hw : ∀ a, (encode a).length = W) (P : List C) :
    (encodePolynomial encode P).length = P.length * W := by
  induction P with
  | nil => simp [encodePolynomial]
  | cons c P ih => simp [encodePolynomial, hw, Nat.add_mul, Nat.add_comm]

theorem reverse_encodePolynomial {C : Type*} (encode : C → List Bool) (P : List C) :
    (encodePolynomial encode P).reverse = backward encode P.reverse := by
  simpa only [encodePolynomial, backward, SubexpHornerControl.backward, Function.comp_def]
    using (List.reverse_flatMap (l := P) (f := encode))

/-- This is a concrete finite-command execution statement, not an arithmetic
oracle. Its only component premises are exact execution contracts for the two
fixed native binary services. -/
theorem command_run_oai {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (P : List C) (x seed : C)
    (hP : base 246 = encodePolynomial encode P) (hx : base 247 = encode x)
    (hseed : base 240 = encode seed) (hcount : (base 248).length = P.length)
    (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = []) :
    ExecutesIn (command multiply add) (budget P.length W Km Ka) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 []) := by
  let s := Function.update base 246 (backward encode P.reverse)
  have hr : ExecutesIn reverseStream (9 * (P.length * W) + 7) base s := by
    intro regs
    have h := reverse_eval (⟨regs, base⟩ : Data) 246 251 252 0 1
      (by decide) (by decide) (by decide) (by decide) h251 h252
    refine ⟨9 * (base 246).length + 7, readRegs regs 0 1 none, ?_, ?_⟩
    · rw [hP, encodePolynomial_length encode W hwidth]
    · simpa [reverseStream, afterReverse, StackRoutines.reverseStacks, s, hP,
        reverse_encodePolynomial] using h
  have hs := lowFrame_update (lowFrame_refl base) 246 (by decide) (backward encode P.reverse)
  have hloop := streaming_run s encode multiply add mulOp addOp Km Ka W
    (serviceSpec_frame hm hs) (serviceSpec_frame ha hs) hwidth x
    (by simp [s, hx]) (by simp [s, hw]) (by simp [s, h120])
    (by simp [s, h241]) (by simp [s, h244]) (by simp [s, h245])
    (by simp [s, h251]) (by simp [s, h252]) P.reverse seed (base 248)
    (by simpa using hcount)
  have hin : ready s encode P.reverse seed (base 248) = s := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;> by_cases h248 : i = 248 <;>
      simp [ready, s, h240, h246, h248, hseed]
  have hout : ready s encode [] (fold (stepValue mulOp addOp x) P.reverse seed) [] =
      Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 [] := by
    simp [ready, s, backward, SubexpHornerControl.backward]
  rw [hin, hout] at hloop
  have h := hr.seq hloop
  have hcost : (9 * (P.length * W) + 7) +
      (P.reverse.length * (Km + Ka + 50 * W + 49) + 2) =
      budget P.length W Km Ka := by
    simp only [List.length_reverse, budget]
    ring
  simpa only [command, hcost] using h

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run_oai.{u_1}
