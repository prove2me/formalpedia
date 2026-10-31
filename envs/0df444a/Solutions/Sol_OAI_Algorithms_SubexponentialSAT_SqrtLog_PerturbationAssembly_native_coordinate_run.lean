-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:24:30.956562+00:00
-- url     : https://prove2.me/submissions/f3b9b864-7ca3-430a-a94b-63e0ee78cac3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S150
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_PairSpec_BaseReady_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_loadCoordinate_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_native_shift_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationEmitProgram_command_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem advance_run (s : Store) : ExecutesIn advance 2 s
    (Function.update s 218 (true::s 218)) := by
  intro regs
  exact ⟨2,Function.update regs 0 true,le_rfl,
    Subexp.TupleProgram.pushConst_eval (218 : Fin 256) (0 : Fin 16) true (⟨regs,s⟩ : Data)⟩

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

/-- Sequential composition exposes the exact output bytes, including their
prepend order. The supplied trace is discharged by native_shift_run. -/
theorem finishCoordinate_run (s : Store) (mask : List Bool) (W K : ℕ)
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (hs : ExecutesIn (shift DensePolynomialProgram.Fixed.mulCommand
      DensePolynomialProgram.AddService.command) K s
      (Function.update (Function.update s 219 []) 240 (PerturbationEmitProgram.array cs)))
    (hJ : s 213=List.replicate cs.length true) (hw : (s 211).length=W)
    (hm : s 214=mask) (he : ∀ i ∈ coordinateEmitScratch,s i=[])
    (h240 : s 240=[]) :
    ExecutesIn finishCoordinate
      (K+PerturbationEmitProgram.budget cs.length mask.length W+2*mask.length+5) s
      (Function.update (Function.update (Function.update (Function.update s 219 [])
        217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s 217))) 214 [])
        218 (true::s 218)) := by
  let s1 := Function.update (Function.update s 219 []) 240 (PerturbationEmitProgram.array cs)
  let s2 := Function.update (Function.update s 219 [])
    217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s 217))
  let s3 := Function.update s2 214 []
  have hout : Function.update (Function.update s1 240 []) 217
      (PerturbationEmitProgram.emitted mask 1 cs.tail (s1 217))=s2 := by
    funext i
    by_cases h219 : i=219 <;> by_cases h217 : i=217 <;> by_cases h240' : i=240 <;>
      simp [s1,s2,h219,h217,h240',h240]
  have h2 : ExecutesIn PerturbationEmitProgram.command
      (PerturbationEmitProgram.budget cs.length mask.length W) s1 s2 := by
    have h := PerturbationEmitProgram.command_run s1 mask W cs hc
      (by simp [s1]) (by simpa [s1] using hJ) (by simpa [s1] using hw)
      (by simpa [s1] using hm)
      (by simpa [s1] using he 120 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 221 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 222 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 223 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 224 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 225 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 226 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 227 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 228 (by simp [coordinateEmitScratch]))
    rw [hout] at h
    exact h
  have h3 : ExecutesIn (clear 214) (2*mask.length+3) s2 s3 := by
    simpa [s3,s2,hm] using clear_run 214 s2
  have h4 := PerturbationMaskProgram.advance_run s3
  have h := hs.seq (h2.seq (h3.seq h4))
  have hcost : K + (PerturbationEmitProgram.budget cs.length mask.length W +
      (2 * mask.length + 3 + 2)) =
      K + PerturbationEmitProgram.budget cs.length mask.length W +
        2 * mask.length + 5 := by omega
  rw [← hcost]
  simpa [finishCoordinate, s3, s2] using h

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeCoordinate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem loaded_lowFrame (s : Store) (bits rest mask : List Bool) :
    CRTLocalProgram.LowFrame s (coordinateLoaded s bits rest mask) := by
  intro i hi
  have h214 : i≠214 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h219 : i≠219 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h230 : i≠230 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [coordinateLoaded,h214,h219,h230]

private theorem shiftScratch_ne_loadPorts :
    ∀ i : Fin 256, i ∈ shiftScratch → i ≠ 214 ∧ i ≠ 219 ∧ i ≠ 230 := by
  intro i hi
  simp [shiftScratch] at hi
  omega

private theorem coordinateEmitScratch_ne_loadPorts :
    ∀ i : Fin 256, i ∈ coordinateEmitScratch → i ≠ 214 ∧ i ≠ 219 ∧ i ≠ 230 := by
  intro i hi
  simp [coordinateEmitScratch] at hi
  omega

/-- This is the complete native coordinate worker: frame decode, physical mask
construction, padding, native polynomial Horner, sparse emission, and cleanup.
There is no shifted-row, padded-input, mask, or coefficient-emission oracle. -/
theorem native_coordinate_run_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d n : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (P : List (Coeff (baseWidth p t) d)) (theta : Coeff (baseWidth p t) d)
    (v : Fin n) (rest : List Bool)
    (hrow : s 230=true::(Encoding.frame (HornerProgram.encodePolynomial RingProgram.flat P)++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (hcount : (s 210).length=P.length) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
    (heShift : ∀ i ∈ shiftScratch,s i=[])
    (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[]) :
    ExecutesIn coordinate
      (15*(P.length*(d*baseWidth p t))+11*n+17*v.val+38+
        shiftBudget P.length J (d*baseWidth p t)
          (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+
        PerturbationEmitProgram.budget J n (d*baseWidth p t)+2*n+5) s
      (Function.update (Function.update (Function.update s 230 rest)
        217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218)) := by
  let bits := HornerProgram.encodePolynomial RingProgram.flat P
  let mask := Squarefree.encodeMask {v}
  let s1 := coordinateLoaded s bits rest mask
  let cs := (shiftedValue ops J theta P).val.map RingProgram.flat
  let K := shiftBudget P.length J (d*baseWidth p t)
    (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)
  have hlow := loaded_lowFrame s bits rest mask
  have hsLoad := loadCoordinate_run s v bits rest hrow hn hv heLoad
  have hss : ∀ i ∈ shiftScratch,s1 i=[] := by
    intro i hi
    have hne := shiftScratch_ne_loadPorts i hi
    change Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask i = []
    rw [Function.update_noteq hne.1, Function.update_noteq hne.2.1,
      Function.update_noteq hne.2.2]
    exact heShift i hi
  have hse : ∀ i ∈ coordinateEmitScratch,s1 i=[] := by
    intro i hi
    have hne := coordinateEmitScratch_ne_loadPorts i hi
    change Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask i = []
    rw [Function.update_noteq hne.1, Function.update_noteq hne.2.1,
      Function.update_noteq hne.2.2]
    exact heEmit i hi
  have hs : ExecutesIn (shift Fixed.mulCommand AddService.command) K s1
      (Function.update (Function.update s1 219 []) 240 (PerturbationEmitProgram.array cs)) := by
    have h := native_shift_run p t M cache ops table hB hz hadd hmul s1 J scalarWidth frame
      (PairSpec.BaseReady.frame p t M cache table H hlow)
      (fun i => (hlow (bufferPorts i) (by fin_cases i <;> decide)).trans (hempty i))
      (by simpa [s1,coordinateLoaded] using h121) (by simpa [s1,coordinateLoaded] using h122)
      (by simpa [s1,coordinateLoaded] using hcache) (by simpa [s1,coordinateLoaded] using hJcount)
      hzero P theta (by simp [s1,coordinateLoaded,bits])
      (by simpa [s1,coordinateLoaded] using hcount) (by simpa [s1,coordinateLoaded] using hwidth)
      (by simpa [s1,coordinateLoaded] using hx) (by simpa [s1,coordinateLoaded] using hJ)
      (by simpa [s1,coordinateLoaded] using h104) (by simpa [s1,coordinateLoaded] using h254) hss
    simpa [K,cs,Fixed.encode,DensePolynomialProgram.encode,PerturbationEmitProgram.array] using h
  have hlen : cs.length=J := by
    simp only [cs, List.length_map, (shiftedValue ops J theta P).property]
  have hm : mask.length=n := by simp [mask,Squarefree.encodeMask]
  have hf := finishCoordinate_run s1 mask (d*baseWidth p t) K cs
    (by intro c hc; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc; exact RingProgram.flat_length a)
    hs (by simpa [s1,coordinateLoaded,hlen] using h213)
    (by simpa [s1,coordinateLoaded] using hwidth) (by simp [s1,coordinateLoaded]) hse
    (hss 240 (by simp [shiftScratch]))
  have hout : Function.update (Function.update (Function.update (Function.update s1 219 [])
      217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s1 217))) 214 []) 218 (true::s1 218) =
      Function.update (Function.update (Function.update s 230 rest)
        217 (coordinateResult ops J theta v P (s 217))) 218 (true::s 218) := by
    funext i
    by_cases h214 : i=214 <;> by_cases h217 : i=217 <;> by_cases h218 : i=218 <;>
      by_cases h219 : i=219 <;> by_cases h230 : i=230 <;>
      first | rfl | simp [s1,coordinateLoaded,coordinateResult,cs,mask,Function.update_apply,
        h214,h217,h218,h219,h230,heLoad 214 (by simp [coordinateLoadScratch]),
        heLoad 219 (by simp [coordinateLoadScratch])]
  rw [hout] at hf
  have h := hsLoad.seq hf
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals
    first
    | rfl
    | simp only [bits,HornerProgram.encodePolynomial_length RingProgram.flat
        (d*baseWidth p t) RingProgram.flat_length,hlen,hm,K]
      omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_coordinate_run_oai
