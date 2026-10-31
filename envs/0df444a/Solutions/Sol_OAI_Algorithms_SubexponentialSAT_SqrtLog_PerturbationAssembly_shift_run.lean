-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:27:35.33537+00:00
-- url     : https://prove2.me/submissions/b8bce00d-0c8a-4e54-8817-50d012b7ba69

import Mathlib
import Definitions.Def_OAIQ081S150
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HornerProgram_command_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationProgram_Padding_streaming_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
namespace Counter
open SubexponentialSAT.SubexpLinearFactorProgram
theorem paddedBits_length (D W : ℕ) (low high : List Bool)
    (hlow : low.length = W) (hhigh : high.length = W) :
    (paddedBits W low high D).length = D * W := by
  cases D with
  | zero => simp [paddedBits]
  | succ D =>
      cases D with
      | zero => simpa [paddedBits] using hlow
      | succ n => simp [paddedBits, hlow, hhigh]; ring

end Counter
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpPolynomialConstructor

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

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

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite scalar-to-polynomial padding. The runtime degree and
coefficient width are tapes, so this command is independent of all dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open DensePolynomialProgram.Constructor

theorem cell_length (D W : ℕ) (bits : List Bool) (h : bits.length=W) :
    (cell D W bits).length = D*W :=
  Counter.paddedBits_length D W bits _ h (by simp)

/-- Starting with highest degree first makes the final stream coefficient-zero first. -/
theorem fold_output {C : Type*} (encode : C → List Bool) (D W : ℕ) (cs : List C) :
    cs.reverse.foldl (step encode D W) [] = cs.flatMap (fun c => cell D W (encode c)) := by
  rw [List.foldl_reverse]
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [step,List.flatMap_def]

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem output_length {C : Type*} (encode : C → List Bool) (D W : ℕ)
    (hwidth : ∀ c, (encode c).length=W) (cs : List C) :
    (output encode D W cs).length=cs.length*D*W := by
  induction cs with
  | nil => simp [output]
  | cons c cs ih =>
      change (cell D W (encode c)++output encode D W cs).length=_
      rw [List.length_append,cell_length D W _ (hwidth c),ih]
      simp only [List.length_cons]
      ring

/-- Full native construction of the homogeneous stream required by polynomial
Horner, from the actual serialized scalar coefficient array. No padded-input
oracle is assumed: both all zero bits and every copied coefficient are paid. -/
theorem command_run {C : Type*} (base : Store) (encode : C → List Bool)
    (D W : ℕ) (hwidth : ∀ c, (encode c).length=W)
    (cs : List C) (hcs : base 246=HornerProgram.encodePolynomial encode cs)
    (hacc : base 240=[]) (hcount : (base 248).length=cs.length)
    (hw : (base 250).length=W) (hD : base 243=List.replicate D true)
    (hzero : base 104=List.replicate W false) (hz : base 254=List.replicate W false)
    (h100 : base 100=[]) (h101 : base 101=[]) (h102 : base 102=[])
    (h107 : base 107=[]) (h108 : base 108=[]) (h120 : base 120=[])
    (h241 : base 241=[]) (h245 : base 245=[]) (h251 : base 251=[])
    (h252 : base 252=[]) (h253 : base 253=[]) :
    ExecutesIn command (budget cs.length D W) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (output encode D W cs)) 248 []) := by
  let s := Function.update base 246 (HornerProgram.backward encode cs.reverse)
  have hr : ExecutesIn HornerProgram.reverseStream (9*(cs.length*W)+7) base s := by
    intro regs
    have h := reverse_eval (⟨regs,base⟩ : Data) 246 251 252 0 1
      (by decide) (by decide) (by decide) (by decide) h251 h252
    refine ⟨9*(base 246).length+7,readRegs regs 0 1 none,?_,?_⟩
    · rw [hcs,HornerProgram.encodePolynomial_length encode W hwidth]
    · simpa [HornerProgram.reverseStream,afterReverse,StackRoutines.reverseStacks,s,hcs,
        HornerProgram.reverse_encodePolynomial] using h
  have hl := streaming_run s encode D W hwidth
    (by simp [s,hw]) (by simp [s,hD]) (by simp [s,hzero]) (by simp [s,hz])
    (by simp [s,h100]) (by simp [s,h101]) (by simp [s,h102])
    (by simp [s,h107]) (by simp [s,h108]) (by simp [s,h120])
    (by simp [s,h241]) (by simp [s,h245]) (by simp [s,h251])
    (by simp [s,h252]) (by simp [s,h253]) cs.reverse [] (base 248)
    (by simpa using hcount)
  have hin : Traversal.ready s encode cs.reverse [] (base 248)=s := by
    funext i
    by_cases h240 : i=240 <;> by_cases h246 : i=246 <;> by_cases h248 : i=248 <;>
      simp [Traversal.ready,s,h240,h246,h248,hacc]
  have hout : Traversal.ready s encode [] (cs.reverse.foldl (step encode D W) []) [] =
      Function.update (Function.update (Function.update base 246 [])
        240 (output encode D W cs)) 248 [] := by
    rw [fold_output]
    simp [Traversal.ready,s,output,HornerProgram.backward,SubexpHornerControl.backward]
  rw [hin,hout,List.length_reverse] at hl
  exact hr.seq hl

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native staging for the complete per-coordinate perturbation worker.
All dimensions and values are runtime tapes. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

theorem loadRow_run (s : Store) (h120 : s 120=[]) (h245 : s 245=[])
    (h246 : s 246=[]) (h248 : s 248=[]) (h250 : s 250=[]) :
    ExecutesIn loadRow (6*(s 219).length+7*(s 210).length+7*(s 211).length+16)
      s (loaded s) := by
  let s1 := Function.update (Function.update s 219 []) 246 (s 219)
  let s2 := Function.update s1 248 (s 210)
  have h1 : ExecutesIn (move 219 246) (6*(s 219).length+6) s s1 :=
    move_run s 219 246 (by decide) (by decide) (by decide) h245 h246
  have h2 : ExecutesIn (copy 210 248) (7*(s 210).length+5) s1 s2 := by
    simpa [s1,s2,h248] using copy_run 210 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
  have h3 : ExecutesIn (copy 211 250) (7*(s 211).length+5) s2 (loaded s) := by
    simpa [s1,s2,loaded,h250] using copy_run 211 250 s2 (by decide) (by decide) (by decide)
      (by simp [s2,s1,h120])
  convert h1.seq (h2.seq h3) using 1 <;> first | rfl | omega

theorem enterHorner_run (s : Store) (h120 : s 120=[]) (h245 : s 245=[])
    (h246 : s 246=[]) (h248 : s 248=[]) :
    ExecutesIn enterHorner
      (6*(s 240).length+7*(s 210).length+2*(s 250).length+14*(s 192).length+24)
      s (hornerInput s) := by
  let s1 := Function.update (Function.update s 240 []) 246 (s 240)
  let s2 := Function.update s1 248 (s 210)
  let s3 := Function.update s2 250 []
  let s4 := Function.update s3 250 (s 192)
  have h1 : ExecutesIn (move 240 246) (6*(s 240).length+6) s s1 :=
    move_run s 240 246 (by decide) (by decide) (by decide) h245 h246
  have h2 : ExecutesIn (copy 210 248) (7*(s 210).length+5) s1 s2 := by
    simpa [s1,s2,h248] using copy_run 210 248 s1 (by decide) (by decide) (by decide)
      (by simp [s1,h120])
  have h3 : ExecutesIn (clear 250) (2*(s 250).length+3) s2 s3 := by
    simpa [s1,s2,s3] using clear_run 250 s2
  have h4 : ExecutesIn (copy 192 250) (7*(s 192).length+5) s3 s4 := by
    simpa [s1,s2,s3,s4] using copy_run 192 250 s3 (by decide) (by decide) (by decide)
      (by simp [s3,s2,s1,h120])
  have he : Function.update s4 240 ((s4 192)++s4 240)=hornerInput s := by
    funext i
    by_cases h240 : i=240 <;> by_cases h246 : i=246 <;>
      by_cases h248 : i=248 <;> by_cases h250 : i=250 <;>
      simp [s4,s3,s2,s1,hornerInput,h240,h246,h248,h250]
  have h5 : ExecutesIn (copy 192 240) (7*(s 192).length+5) s4 (hornerInput s) := by
    have h := copy_run 192 240 s4 (by decide) (by decide) (by decide)
      (by simp [s4,s3,s2,s1,h120])
    rw [he] at h
    simpa [s4,s3,s2,s1] using h
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native composition from a complete scalar coefficient row to its shifted
jet. Padding and both runtime counters are executed, rather than supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open PerturbationProgram
open CRTLocalProgram (ServiceSpec LowFrame serviceSpec_frame)

/-- The two services are fixed finite commands. The input is a full scalar
row at219; no pre-padded stream or evaluated/shifted row is a premise. -/
theorem shift_run_oai {C A : Type*} (s : Store) (encC : C → List Bool)
    (encA : A → List Bool) (lift : C → A) (multiply add : Code)
    (mulOp addOp : A → A → A) (Km Ka J W : ℕ)
    (hm : ServiceSpec s encA multiply mulOp Km)
    (ha : ServiceSpec s encA add addOp Ka)
    (hc : ∀ c, (encC c).length=W) (hw : ∀ a, (encA a).length=J*W)
    (hlift : ∀ c, Padding.cell J W (encC c)=encA (lift c))
    (P : List C) (x zero : A)
    (hrow : s 219=HornerProgram.encodePolynomial encC P)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=W)
    (hx : s 247=encA x) (hz : s 192=encA zero)
    (hJ : s 243=List.replicate J true)
    (hzero : s 104=List.replicate W false)
    (h254 : s 254=List.replicate W false)
    (he : ∀ i ∈ shiftScratch, s i=[]) :
    ExecutesIn (shift multiply add) (shiftBudget P.length J W Km Ka) s
      (Function.update (Function.update s 219 []) 240
        (encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
          (P.map lift).reverse zero))) := by
  have e100 := he 100 (by simp [shiftScratch])
  have e101 := he 101 (by simp [shiftScratch])
  have e102 := he 102 (by simp [shiftScratch])
  have e107 := he 107 (by simp [shiftScratch])
  have e108 := he 108 (by simp [shiftScratch])
  have e120 := he 120 (by simp [shiftScratch])
  have e240 := he 240 (by simp [shiftScratch])
  have e241 := he 241 (by simp [shiftScratch])
  have e244 := he 244 (by simp [shiftScratch])
  have e245 := he 245 (by simp [shiftScratch])
  have e246 := he 246 (by simp [shiftScratch])
  have e248 := he 248 (by simp [shiftScratch])
  have e250 := he 250 (by simp [shiftScratch])
  have e251 := he 251 (by simp [shiftScratch])
  have e252 := he 252 (by simp [shiftScratch])
  have e253 := he 253 (by simp [shiftScratch])
  let s1 := loaded s
  let s2 := Function.update (Function.update (Function.update s1 246 [])
    240 (Padding.output encC J W P)) 248 []
  let s3 := hornerInput s2
  let answer := encA (HornerProgram.fold (HornerProgram.stepValue mulOp addOp x)
    (P.map lift).reverse zero)
  let s4 := Function.update (Function.update (Function.update s3 246 []) 240 answer) 248 []
  have h1 : ExecutesIn loadRow (6*(P.length*W)+7*P.length+7*W+16) s s1 := by
    simpa [s1,hrow,HornerProgram.encodePolynomial_length encC W hc,hcount,hwidth] using
      loadRow_run s e120 e245 e246 e248 e250
  have h2 : ExecutesIn Padding.command (Padding.budget P.length J W) s1 s2 := by
    apply Padding.command_run s1 encC J W hc P
    all_goals simp_all [s1,loaded]
  have hpad : Padding.output encC J W P =
      HornerProgram.encodePolynomial encA (P.map lift) := by
    simp [Padding.output,HornerProgram.encodePolynomial,List.flatMap_map,hlift]
  have h3 : ExecutesIn enterHorner
      (6*(P.length*J*W)+7*P.length+2*W+14*(J*W)+24) s2 s3 := by
    have h := enterHorner_run s2
      (by simp [s2,s1,loaded,e120]) (by simp [s2,s1,loaded,e245])
      (by simp [s2]) (by simp [s2])
    simpa [s3,s2,s1,loaded,Padding.output_length encC J W hc,hcount,hwidth,hz,hw] using h
  have hf : LowFrame s s3 := by
    intro i hi
    have h219 : i≠219 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h240 : i≠240 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h246 : i≠246 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h248 : i≠248 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h250 : i≠250 := by intro hh; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    simp [s3,hornerInput,s2,s1,loaded,h219,h240,h246,h248,h250]
  have h4 : ExecutesIn (HornerProgram.command multiply add)
      (HornerProgram.budget P.length (J*W) Km Ka) s3 s4 := by
    have h := HornerProgram.command_run s3 encA multiply add mulOp addOp Km Ka (J*W)
      (serviceSpec_frame hm hf) (serviceSpec_frame ha hf) hw (P.map lift) x zero
      (by simp [s3,hornerInput,s2,hpad]) (by simp [s3,hornerInput,s2,s1,loaded,hx])
      (by simp [s3,hornerInput,s2,s1,loaded,hz])
      (by simp [s3,hornerInput,s2,s1,loaded,hcount])
      (by simp [s3,hornerInput,s2,s1,loaded,hz,hw])
      (by simp [s3,hornerInput,s2,s1,loaded,e120])
      (by simp [s3,hornerInput,s2,s1,loaded,e241])
      (by simp [s3,hornerInput,s2,s1,loaded,e244])
      (by simp [s3,hornerInput,s2,s1,loaded,e245])
      (by simp [s3,hornerInput,s2,s1,loaded,e251])
      (by simp [s3,hornerInput,s2,s1,loaded,e252])
    simpa [s4,answer] using h
  have hout : Function.update s4 250 [] =
      Function.update (Function.update s 219 []) 240 answer := by
    funext i
    by_cases h219 : i=219 <;> by_cases h240 : i=240 <;>
      by_cases h246 : i=246 <;> by_cases h248 : i=248 <;> by_cases h250 : i=250 <;>
      simp [s4,s3,hornerInput,s2,s1,loaded,
        h219,h240,h246,h248,h250,e246,e248,e250]
  have h5 : ExecutesIn (clear 250) (2*(J*W)+3) s4
      (Function.update (Function.update s 219 []) 240 answer) := by
    have h := clear_run 250 s4
    rw [hout] at h
    simpa [s4,s3,hornerInput,s2,s1,loaded,hz,hw] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert h using 1 <;> first
    | rfl
    | omega
    | (simp only [shiftBudget] ; omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.shift_run_oai.{u_1, u_2}
