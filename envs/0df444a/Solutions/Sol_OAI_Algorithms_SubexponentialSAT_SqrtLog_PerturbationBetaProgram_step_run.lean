-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:18:26.401096+00:00
-- url     : https://prove2.me/submissions/c9575e33-3bec-41d4-8f13-069899800106

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S163
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HornerProgram_command_run

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

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- All arithmetic service hypotheses are discharged by the actual native
programs. Remaining assumptions describe supplied bytes and clean scratch. -/
theorem modelCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : Services.NativeReady 3 t M cache (modelTable t a M cache) base)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hP : base 246 = encodePolynomial RingProgram.flat P)
    (hx : base 247 = RingProgram.flat x)
    (hseed : base 240 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hcount : (base 248).length = P.length) (hw : (base 250).length = d * baseWidth 3 t)
    (h241 : base 241 = []) (h244 : base 244 = []) (h245 : base 245 = [])
    (h251 : base 251 = []) (h252 : base 252 = []) :
    ExecutesIn modelCommand (modelBudget P.length t d) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (RingProgram.flat (modelValue t a M cache P x))) 248 []) := by
  exact command_run base RingProgram.flat Services.multiply Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (Services.mulBudget (baseWidth 3 t) d) (Services.addBudget (baseWidth 3 t) d)
    (d * baseWidth 3 t)
    (Services.multiply_spec 3 t M cache hz (modelTable t a M cache) base hready)
    (Services.add_spec 3 t M cache (modelTable t a M cache) base hready)
    RingProgram.flat_length P x (RingProgram.modelProgram t a M cache).zeroRun.1
    hP hx hseed hcount hw hready.workspace.1 h241 h244 h245 h251 h252

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed16/256 frame primitives for beta evaluation. These use the immutable
reader and transfer programs and are independent of the larger moment driver. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaFrames
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem transfer_eval (d : Data) (src dst : Fin 256) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

theorem readFrame_eval (d : Data) (src dst : Fin 256) (hsd : src ≠ dst)
    (bits tail : List Bool) (hs : d.stacks src = Encoding.frame bits ++ tail) :
    Eval (readFrame src dst hsd) (6*bits.length+4) d (afterFrame d src dst bits tail) := by
  let ports := framePorts src dst hsd
  have h := RecordPrograms.reader_eval ports d bits tail (d.stacks dst)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have hi : RecordPrograms.state ports d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) (d.stacks dst) = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl hs rfl
  rw [hi] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ ports, framePorts, readRegs]
  · funext i
    simp [ ports, framePorts ]

end SubexponentialSAT.SqrtLog.PerturbationBetaFrames

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

theorem popRow_run (s : Store) (b : Bool) (rest : List Bool)
    (hs : s 230=b::rest) :
    ExecutesIn popRow 1 s (Function.update s 230 rest) := by
  intro regs
  refine ⟨1,readRegs regs 0 1 (some b),by omega,?_⟩
  simpa [popRow,hs,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
    (Eval.base (StructuredProgram.Eval.atom (.pop (230 : Fin 256) (0 : Fin 16) 1)
      (⟨regs,s⟩ : Data)))

theorem readRow_run (s : Store) (bits rest : List Bool)
    (hs : s 230=true::(Encoding.frame bits++rest))
    (h232 : s 232=[]) (h246 : s 246=[]) :
    ExecutesIn readRow (9*bits.length+8) s
      (Function.update (Function.update s 230 rest) 246 bits) := by
  have hp := popRow_run s true (Encoding.frame bits++rest) hs
  intro regs
  obtain ⟨np,rp,hnp,hep⟩ := hp regs
  let a : Data := ⟨rp,Function.update s 230 (Encoding.frame bits++rest)⟩
  have hr := PerturbationBetaFrames.readFrame_eval a 230 232 (by decide) bits rest (by simp [a])
  have ht := PerturbationBetaFrames.transfer_eval
    (PerturbationBetaFrames.afterFrame a 230 232 bits rest) 232 246 (by decide)
  have he : PerturbationBetaFrames.afterTransfer
      (PerturbationBetaFrames.afterFrame a 230 232 bits rest) 232 246 =
      (⟨readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,
        Function.update (Function.update s 230 rest) 246 bits⟩ : Data) := by
    apply state_ext
    · rfl
    · funext i
      by_cases h0 : i=230 <;> by_cases h1 : i=232 <;> by_cases h2 : i=246 <;>
        simp [a,
          StackRoutines.transferStacks,h0,h1,h2,h232,h246]
  rw [he] at ht
  refine ⟨np+((6*bits.length+4)+(3*bits.length+3)),
    readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,by omega,?_⟩
  have ht' : Eval (PerturbationBetaFrames.transfer 232 246) (3*bits.length+3)
      (PerturbationBetaFrames.afterFrame a 230 232 bits rest)
      (⟨readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,
        Function.update (Function.update s 230 rest) 246 bits⟩ : Data) := by
    simpa [PerturbationBetaFrames.afterFrame,a,h232] using ht
  exact hep.seq (hr.seq ht')

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One selected coefficient row is evaluated by the actual Horner command
and accumulated by the actual extension-ring addition service. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

theorem selected_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) s)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (theta acc : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hP : s 246=HornerProgram.encodePolynomial RingProgram.flat P)
    (hx : s 247=RingProgram.flat theta) (ha : s 220=RingProgram.flat acc)
    (hz0 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (s 210).length=P.length) (hw : (s 250).length=d*baseWidth 3 t)
    (h240 : s 240=[]) (h248 : s 248=[]) (h241 : s 241=[])
    (h244 : s 244=[]) (h245 : s 245=[]) (h251 : s 251=[]) (h252 : s 252=[]) :
    ExecutesIn selected (selectedBudget P.length t d) s
      (Function.update (Function.update s 246 []) 220
        (RingProgram.flat (nextValue t a M cache P theta acc))) := by
  let W := d*baseWidth 3 t
  let v := HornerProgram.modelValue t a M cache P theta
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  let out := nextValue t a M cache P theta acc
  let s1 := Function.update s 240 (RingProgram.flat z)
  let s2 := Function.update s1 248 (s 210)
  let s3 := Function.update (Function.update (Function.update s2 246 []) 240 (RingProgram.flat v)) 248 []
  let s4 := Function.update s3 241 (RingProgram.flat acc)
  let s5 := Function.update s4 240 (RingProgram.flat out)
  let s6 := Function.update s5 241 []
  let s7 := Function.update s6 220 []
  have hf1 : LowFrame s s1 := lowFrame_update (lowFrame_refl s) 240 (by decide) _
  have hf2 : LowFrame s s2 := lowFrame_update hf1 248 (by decide) _
  have hf3 : LowFrame s s3 := lowFrame_update (lowFrame_update
    (lowFrame_update hf2 246 (by decide) _) 240 (by decide) _) 248 (by decide) _
  have hf4 : LowFrame s s4 := lowFrame_update hf3 241 (by decide) _
  have h1 : ExecutesIn (copy 207 240) (7*W+5) s s1 := by
    simpa [s1,z,hz0,h240,RingProgram.flat_length,W] using
      copy_run 207 240 s (by decide) (by decide) (by decide) hready.workspace.1
  have h2 : ExecutesIn (copy 210 248) (7*P.length+5) s1 s2 := by
    simpa [s2,s1,h248,hc] using copy_run 210 248 s1
      (by decide) (by decide) (by decide) (by simp [s1,hready.workspace.1])
  have h3 : ExecutesIn HornerProgram.modelCommand (HornerProgram.modelBudget P.length t d) s2 s3 := by
    exact HornerProgram.modelCommand_run t a M cache hz s2 (hready.frame hf2) P theta
      (by simp [s2,s1,hP]) (by simp [s2,s1,hx]) (by simp [s2,s1,z])
      (by simp [s2,hc]) (by simp [s2,s1,hw]) (by simp [s2,s1,h241])
      (by simp [s2,s1,h244]) (by simp [s2,s1,h245])
      (by simp [s2,s1,h251]) (by simp [s2,s1,h252])
  have h4 : ExecutesIn (copy 220 241) (7*W+5) s3 s4 := by
    simpa [s4,s3,s2,s1,ha,h241,RingProgram.flat_length,W] using
      copy_run 220 241 s3 (by decide) (by decide) (by decide)
        (by simp [s3,s2,s1,hready.workspace.1])
  have h5 : ExecutesIn (CRTLocalProgram.binaryStep HornerProgram.Services.add)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d+8*W+9) s4 s5 := by
    exact CRTLocalProgram.binaryStep_run s RingProgram.flat HornerProgram.Services.add
      (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d) W
      (HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hready)
      (fun x => (RingProgram.flat_length x).le) s4 v acc hf4
      (by simp [s4,s3]) (by simp [s4]) (by simp [s4,s3,s2,s1,h244])
      (by simp [s4,s3,s2,s1,h245])
  have h6 : ExecutesIn (clear 241) (2*W+3) s5 s6 := by
    simpa [s6,s5,s4,RingProgram.flat_length,W] using clear_run 241 s5
  have h7 : ExecutesIn (clear 220) (2*W+3) s6 s7 := by
    simpa [s7,s6,s5,s4,s3,s2,s1,ha,RingProgram.flat_length,W] using clear_run 220 s6
  have he : Function.update (Function.update s7 240 []) 220 (RingProgram.flat out) =
      Function.update (Function.update s 246 []) 220 (RingProgram.flat out) := by
    funext i
    by_cases h0 : i=240 <;> by_cases h1 : i=248 <;> by_cases h2 : i=246 <;>
      by_cases h3 : i=241 <;> by_cases h4 : i=220 <;>
      simp [s7,s6,s5,s4,s3,s2,s1,h0,h1,h2,h3,h4,h240,h248,h241]
  have h8 : ExecutesIn (SubexpPolynomialConstructor.move 240 220) (6*W+6) s7
      (Function.update (Function.update s 246 []) 220 (RingProgram.flat out)) := by
    have h := SubexpPolynomialConstructor.move_run s7 240 220
      (by decide) (by decide) (by decide) (by simp [s7,s6,s5,s4,s3,s2,s1,h245])
      (by simp [s7])
    have hv : s7 240=RingProgram.flat out := by simp [s7,s6,s5]
    rw [hv,he] at h
    simpa only [RingProgram.flat_length] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  convert h using 1 <;> first | (simp only [selectedBudget]; dsimp [W]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

theorem ready_lowFrame {t d : ℕ} (base : Store) (rows : List (List (Coeff t d) × Bool))
    (acc : Coeff t d) : LowFrame base (ready base rows acc) :=
  lowFrame_update (lowFrame_update (lowFrame_update (lowFrame_refl base)
    230 (by decide) _) 231 (by decide) _) 220 (by decide) _

theorem step_run_oai (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta acc : Coeff t d) (P : List (Coeff t d)) (b : Bool)
    (rows : List (List (Coeff t d) × Bool))
    (hx : base 247=RingProgram.flat theta)
    (hz0 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (base 210).length=P.length) (hw : (base 250).length=d*baseWidth 3 t)
    (h232 : base 232=[]) (h240 : base 240=[]) (h246 : base 246=[])
    (h248 : base 248=[]) (h241 : base 241=[]) (h244 : base 244=[])
    (h245 : base 245=[]) (h251 : base 251=[]) (h252 : base 252=[]) :
    ExecutesIn step (stepBudget P.length t d) (ready base ((P,b)::rows) acc)
      (ready base rows (stepValue t a M cache theta acc (P,b))) := by
  let s := ready base ((P,b)::rows) acc
  let sr := Function.update (Function.update s 230 (rowsBits rows)) 246
    (HornerProgram.encodePolynomial RingProgram.flat P)
  let sp := Function.update sr 231 (rows.map Prod.snd)
  have hr : ExecutesIn readRow (9*(P.length*(d*baseWidth 3 t))+8) s sr := by
    simpa only [HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length] using
      readRow_run s (HornerProgram.encodePolynomial RingProgram.flat P) (rowsBits rows)
        (by simp [s,ready,rowsBits,Encoding.encodeList])
        (by simp [s,ready,h232]) (by simp [s,ready,h246])
  have hf : LowFrame base sp := lowFrame_update (lowFrame_update
    (lowFrame_update (ready_lowFrame base ((P,b)::rows) acc) 230 (by decide) _)
      246 (by decide) _) 231 (by decide) _
  have hbranch : ExecutesIn (if b then selected else skip)
      (selectedBudget P.length t d+2*(P.length*(d*baseWidth 3 t))+3) sp
      (ready base rows (stepValue t a M cache theta acc (P,b))) := by
    cases b with
    | false =>
      have he : Function.update sp 246 []=ready base rows acc := by
        funext i
        by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=246 <;>
          by_cases h3 : i=220 <;>
          simp [sp,sr,s,ready,h0,h1,h2,h3,h246]
      have h := clear_run 246 sp
      rw [he] at h
      have hp : (sp 246).length=P.length*(d*baseWidth 3 t) := by
        simp [sp,sr,HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length]
      simpa only [Bool.false_eq_true,ite_false,stepValue,skip,hp] using
        h.mono (by omega)
    | true =>
      have h := selected_run t a M cache hz sp (hready.frame hf) P theta acc
        (by simp [sp,sr]) (by simp [sp,sr,s,ready,hx]) (by simp [sp,sr,s,ready])
        (by simp [sp,sr,s,ready,hz0]) (by simp [sp,sr,s,ready,hc])
        (by simp [sp,sr,s,ready,hw]) (by simp [sp,sr,s,ready,h240])
        (by simp [sp,sr,s,ready,h248]) (by simp [sp,sr,s,ready,h241])
        (by simp [sp,sr,s,ready,h244]) (by simp [sp,sr,s,ready,h245])
        (by simp [sp,sr,s,ready,h251]) (by simp [sp,sr,s,ready,h252])
      have he : Function.update (Function.update sp 246 []) 220
          (RingProgram.flat (nextValue t a M cache P theta acc)) =
          ready base rows (nextValue t a M cache P theta acc) := by
        funext i
        by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=246 <;>
          by_cases h3 : i=220 <;>
          simp [sp,sr,s,ready,h0,h1,h2,h3,h246]
      rw [he] at h
      simpa [stepValue] using h.mono (by omega)
  intro regs
  obtain ⟨nr,rr,hnr,her⟩ := hr regs
  let rp := readRegs rr 0 1 (some b)
  have hep : Eval popChoice 1 (⟨rr,sr⟩ : Data) (⟨rp,sp⟩ : Data) := by
    have hb : sr 231=b::rows.map Prod.snd := by simp [sr,s,ready]
    simpa [popChoice,rp,sp,hb,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      (Eval.base (StructuredProgram.Eval.atom (.pop (231 : Fin 256) (0 : Fin 16) 1)
        (⟨rr,sr⟩ : Data)))
  obtain ⟨nb,rb,hnb,heb⟩ := hbranch rp
  have heif : Eval (.ite 0 selected skip) (nb+1) (⟨rp,sp⟩ : Data)
      (⟨rb,ready base rows (stepValue t a M cache theta acc (P,b))⟩ : Data) := by
    cases b
    · exact Eval.ite_false (by simp [rp,readRegs]) heb
    · exact Eval.ite_true (by simp [rp,readRegs]) heb
  refine ⟨nr+(1+(nb+1)),rb,?_,her.seq (hep.seq heif)⟩
  dsimp [stepBudget]
  omega

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.step_run_oai
