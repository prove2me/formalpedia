-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:03:39.63883+00:00
-- url     : https://prove2.me/submissions/c15a9d15-1653-49e3-ae99-9fddf1d6b8e7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S135

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem popToken_run (counter : Fin 256) (s : Store) (bit : Bool) (rest : List Bool)
    (hcounter : s counter = bit :: rest) :
    ExecutesIn (popToken counter) 1 s (Function.update s counter rest) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (some bit), le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop counter 0 1)
    (⟨regs, s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, hcounter] using Eval.base h

end SubexponentialSAT.SubexpConvolutionControl

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

theorem pushBit_run (s : Store) (b : Bool) : ExecutesIn (pushBit b) 2 s
    (Function.update s 214 (b::s 214)) := by
  intro regs
  refine ⟨2,Function.update regs 0 b,le_rfl,?_⟩
  simpa [pushBit,Subexp.TupleProgram.pushedState] using
    Subexp.TupleProgram.pushConst_eval (214 : Fin 256) (0 : Fin 16) b (⟨regs,s⟩ : Data)

private theorem zero_visits (s : Store) (count out : List Bool) (regs : Fin 16 → Bool) :
    ∃ rr, UnaryForPrograms.Visits zeroPorts (pushBit false)
      (List.replicate count.length 2) (4*count.length+2)
      (⟨regs,fill s count out⟩ : Data)
      (⟨rr,fill s [] (List.replicate count.length false++out)⟩ : Data) := by
  induction count generalizing out regs with
  | nil =>
      refine ⟨readRegs regs 0 1 none,?_⟩
      simpa [zeroPorts,UnaryForPrograms.popped] using
        (UnaryForPrograms.Visits.done (p := zeroPorts) (body := pushBit false)
          (⟨regs,fill s [] out⟩ : Data) (by simp [zeroPorts,fill]))
  | cons bit count ih =>
      let rp := readRegs regs 0 1 (some bit)
      let rb := Function.update rp 0 false
      have hb : Eval (pushBit false) 2
          (UnaryForPrograms.popped zeroPorts (⟨regs,fill s (bit::count) out⟩ : Data))
          (⟨rb,fill s count (false::out)⟩ : Data) := by
        simpa [pushBit,Subexp.TupleProgram.pushedState,UnaryForPrograms.popped,
          zeroPorts,rp,rb] using
          Subexp.TupleProgram.pushConst_eval (214 : Fin 256) (0 : Fin 16) false
            (⟨rp,fill s count out⟩ : Data)
      obtain ⟨rr,ht⟩ := ih (false::out) rb
      have he := UnaryForPrograms.Visits.step
        (p := zeroPorts) (body := pushBit false)
        (by simp [zeroPorts,fill] : (fill s (bit::count) out) zeroPorts.counter ≠ [])
        hb (by simp [zeroPorts,fill,UnaryForPrograms.popped]) ht
      have hout : List.replicate count.length false ++ (false::out) =
          List.replicate (count.length+1) false ++ out := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      rw [hout] at he
      refine ⟨rr,?_⟩
      convert he using 1 <;> simp [List.replicate_succ] ; omega

theorem zeroLoop_run (s : Store) (count out : List Bool)
    (hc : s 221=count) (ho : s 214=out) :
    ExecutesIn zeroLoop (4*count.length+2) s
      (Function.update (Function.update s 221 []) 214
        (List.replicate count.length false++out)) := by
  intro regs
  obtain ⟨rr,hv⟩ := zero_visits s count out regs
  have hs : fill s count out=s := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [fill]
  refine ⟨4*count.length+2,rr,le_rfl,?_⟩
  have he := hv.eval
  rw [hs] at he
  exact he

/-- Zero-mask construction retains the count master and all unrelated stacks. -/
theorem zero_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (h120 : s 120=[]) (h221 : s 221=[]) (h214 : s 214=[]) :
    ExecutesIn zeroCommand (11*n+7) s
      (Function.update s 214 (List.replicate n false)) := by
  let mid := Function.update s 221 (s 212)
  have h1 : ExecutesIn (copy 212 221) (7*n+5) s mid := by
    simpa [mid,hn,h221] using copy_run 212 221 s (by decide) (by decide) (by decide) h120
  have h2 := zeroLoop_run mid (s 212) [] (by simp [mid]) (by simp [mid,h214])
  have he : Function.update (Function.update mid 221 []) 214
      (List.replicate (s 212).length false++[]) =
      Function.update s 214 (List.replicate n false) := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [mid]
  rw [he] at h2
  have h := h1.seq h2
  convert h using 1 ; simp only [hn] ; omega

private theorem zero_split (n j : ℕ) (hj : j < n) :
    List.replicate n false =
      List.replicate j false ++ false :: List.replicate (n-j-1) false := by
  have hn : n=j+((n-j-1)+1) := by omega
  conv_lhs => rw [hn,List.replicate_add,List.replicate_succ]

theorem select_run (s : Store) (n j : ℕ) (hj : j < n)
    (hindex : (s 218).length=j) (hmask : s 214=List.replicate n false)
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn selectCommand (17*j+17) s (Function.update s 214 (bits n j)) := by
  let zeroPrefix := List.replicate j false
  let suffix := List.replicate (n-j-1) false
  let s1 := Function.update (Function.update s 214 (false::suffix)) 223 zeroPrefix
  let s2 := Function.update (Function.update s 214 suffix) 223 zeroPrefix
  let s3 := Function.update (Function.update s 214 (true::suffix)) 223 zeroPrefix
  have h1 : ExecutesIn (takeWord 218 221 222 214 223 0 1) (14*j+11) s s1 := by
    intro regs
    refine ⟨14*j+11,readRegs regs 0 1 none,le_rfl,?_⟩
    simpa [afterTake,zeroPrefix,suffix,s1,h223] using
      takeWord_eval (⟨regs,s⟩ : Data) 218 221 222 214 223 0 1
        (by decide) (by decide) zeroPrefix (false::suffix)
        (by simpa [zeroPrefix,suffix,hmask] using zero_split n j hj) h221 h222
        (by simpa [zeroPrefix] using hindex)
  have h2 : ExecutesIn (popToken 214) 1 s1 s2 := by
    have h := popToken_run 214 s1 false suffix (by simp [s1])
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
      simp [s1,s2,h0,h1]
  have h3 : ExecutesIn (pushBit true) 2 s2 s3 := by
    have h := pushBit_run s2 true
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
      simp [s2,s3,h0,h1]
  have h4 : ExecutesIn (.call (StackRoutines.transferProgram 223 214 (0 : Fin 16) 1))
      (3*j+3) s3 (Function.update s 214 (bits n j)) := by
    intro regs
    have h := transfer_eval (⟨regs,s3⟩ : Data) 223 214 0 1 (by decide) (by decide)
    have he : afterTransfer (⟨regs,s3⟩ : Data) 223 214 0 1 =
        (⟨readRegs regs 0 1 none,Function.update s 214 (bits n j)⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · ext i
        by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
          simp_all [afterTransfer,StackRoutines.transferStacks,s3,zeroPrefix,suffix,bits,
          Function.update_apply]
    rw [he] at h
    exact ⟨3*j+3,readRegs regs 0 1 none,le_rfl,by simpa [s3,zeroPrefix] using h⟩
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 ; omega

theorem command_run (s : Store) (n j : ℕ) (hj : j < n)
    (hn : (s 212).length=n) (hindex : (s 218).length=j)
    (h120 : s 120=[]) (h214 : s 214=[])
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn command (11*n+17*j+24) s (Function.update s 214 (bits n j)) := by
  have h1 := zero_run s n hn h120 h221 h214
  have h2 := select_run (Function.update s 214 (List.replicate n false)) n j hj
    (by simpa using hindex) (by simp) (by simpa using h221)
    (by simpa using h222) (by simpa using h223)
  have h := h1.seq h2
  simpa only [Function.update_idem,show 11*n+7+(17*j+17)=11*n+17*j+24 by omega] using h

theorem bits_eq_ofFn (n j : ℕ) (hj : j < n) :
    bits n j=List.ofFn (fun v : Fin n => decide (v.val=j)) := by
  apply List.ext_getElem
  · simp [hj]
  · intro i hi h'
    have hin : i < n := by simpa only [bits_length n j hj] using hi
    by_cases hij : i < j
    · simp [bits,List.getElem_append_left,hij,show i≠j by omega]
    · have hle : j ≤ i := by omega
      by_cases heq : i=j
      · subst i
        simp [bits,List.getElem_append_right]
      · have hlt : j < i := by omega
        simp [bits,List.getElem_append_right,hle,List.getElem_cons,
          show i-j≠0 by omega,heq]

theorem bits_eq_encodeMask {n : ℕ} (v : Fin n) :
    bits n v.val=Squarefree.encodeMask {v} := by
  rw [bits_eq_ofFn n v.val v.isLt]
  congr 1
  funext w
  simp [Fin.ext_iff]

theorem singleton_run {n : ℕ} (s : Store) (v : Fin n)
    (hn : (s 212).length=n) (hindex : (s 218).length=v.val)
    (h120 : s 120=[]) (h214 : s 214=[])
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn command (11*n+17*v.val+24) s
      (Function.update s 214 (Squarefree.encodeMask {v})) := by
  simpa only [bits_eq_encodeMask] using
    command_run s n v.val v.isLt hn hindex h120 h214 h221 h222 h223

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

theorem loadCoordinate_run_oai {n : ℕ} (s : Store) (v : Fin n) (bits rest : List Bool)
    (hrow : s 230=true::(Encoding.frame bits++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (he : ∀ i ∈ coordinateLoadScratch, s i=[]) :
    ExecutesIn loadCoordinate (15*bits.length+11*n+17*v.val+38) s
      (coordinateLoaded s bits rest (Squarefree.encodeMask {v})) := by
  let s1 := Function.update (Function.update s 230 rest) 246 bits
  let s2 := Function.update (Function.update s 230 rest) 219 bits
  have h1 : ExecutesIn PerturbationBetaProgram.readRow (9*bits.length+8) s s1 :=
    PerturbationBetaProgram.readRow_run s bits rest hrow
      (he 232 (by simp [coordinateLoadScratch])) (he 246 (by simp [coordinateLoadScratch]))
  have hout : Function.update (Function.update s1 246 []) 219 (s1 246)=s2 := by
    funext i
    by_cases h219 : i=219 <;> by_cases h230 : i=230 <;> by_cases h246 : i=246 <;>
      simp [s1,s2,h219,h230,h246,he 246 (by simp [coordinateLoadScratch])]
  have h2 : ExecutesIn (move 246 219) (6*bits.length+6) s1 s2 := by
    have h := move_run s1 246 219 (by decide) (by decide) (by decide)
      (by simpa [s1] using he 245 (by simp [coordinateLoadScratch]))
      (by simpa [s1] using he 219 (by simp [coordinateLoadScratch]))
    rw [hout] at h
    simpa [s1] using h
  have h3 : ExecutesIn PerturbationMaskProgram.command (11*n+17*v.val+24) s2
      (coordinateLoaded s bits rest (Squarefree.encodeMask {v})) := by
    apply PerturbationMaskProgram.singleton_run s2 v
    all_goals first | simpa [s2] using hn | simpa [s2] using hv |
      simpa [s2] using he _ (by simp [coordinateLoadScratch])
  have hcost : 9 * bits.length + 8 +
      (6 * bits.length + 6 + (11 * n + 17 * v.val + 24)) =
      15 * bits.length + 11 * n + 17 * v.val + 38 := by omega
  rw [← hcost]
  exact h1.seq (h2.seq h3)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.loadCoordinate_run_oai
