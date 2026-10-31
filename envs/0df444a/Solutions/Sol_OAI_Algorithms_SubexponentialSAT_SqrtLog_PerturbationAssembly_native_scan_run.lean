-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:25:48.997211+00:00
-- url     : https://prove2.me/submissions/ba863299-aab8-4984-a27c-9585b577e9a3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S150
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_DensePolynomialProgram_PairSpec_BaseReady_frame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_native_coordinate_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

theorem rowPopped {C : Type*} (base : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped rowPorts (⟨regs,rowsReady base encode j cs acc count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?,rowsReady base encode j cs acc count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,rowPorts,rowsReady]
  · funext i
    by_cases h231 : i=231 <;> by_cases h218 : i=218 <;> by_cases h217 : i=217 <;>
      simp [UnaryForPrograms.popped,rowPorts,rowsReady,Function.update_apply,h231,h218,h217]

/-- The callback premise is an execution trace for a fixed command. It is
instantiated by the fully composed load/shift/emission worker. -/
theorem rowLoop_run {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : ℕ → C → List Bool → List Bool) (K n : ℕ)
    (hbody : ∀ j, j < n → ∀ c cs acc count,
      ExecutesIn body K (rowsReady base encode j (c::cs) acc count)
        (rowsReady base encode (j+1) cs (step j c acc) count))
    (j : ℕ) (cs : List C) (acc count : List Bool)
    (hbound : j+cs.length ≤ n) (hlen : count.length=cs.length) :
    ExecutesIn (rowLoop body) (cs.length*(K+2)+2)
      (rowsReady base encode j cs acc count)
      (rowsReady base encode (j+cs.length) [] (rowsResult step j cs acc) []) := by
  intro regs
  suffices h : ∃ costs k rf, UnaryForPrograms.Visits rowPorts body costs k
      (⟨regs,rowsReady base encode j cs acc count⟩ : Data)
      (⟨rf,rowsReady base encode (j+cs.length) [] (rowsResult step j cs acc) []⟩ : Data) ∧
      k ≤ cs.length*(K+2)+2 by
    obtain ⟨costs,k,rf,hv,hk⟩ := h
    exact ⟨k,rf,hk,hv.eval⟩
  induction cs generalizing j acc count regs with
  | nil =>
      have hh : count=[] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[],2,readRegs regs 0 1 none,?_,by simp⟩
      simpa [rowsResult,rowPopped] using
        UnaryForPrograms.Visits.done (p:=rowPorts) (body:=body)
          (⟨regs,rowsReady base encode j [] acc []⟩ : Data) (by simp [rowsReady,rowPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hcount : count.length=cs.length := by simpa using hlen
          have hj : j < n := by simp only [List.length_cons] at hbound; omega
          have hb := hbody j hj c cs acc count
          obtain ⟨nb,rb,hnb,heb⟩ := hb (readRegs regs 0 1 (some bit))
          obtain ⟨costs,nt,rt,ht,hnt⟩ := ih (j:=j+1) (acc:=step j c acc) (count:=count) (regs:=rb)
            (by simp only [List.length_cons] at hbound; omega) hcount
          refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
          · have hv := UnaryForPrograms.Visits.step
              (p:=rowPorts) (body:=body)
              (d:=(⟨regs,rowsReady base encode j (c::cs) acc (bit::count)⟩ : Data))
              (by simp [rowsReady,rowPorts])
              (by simpa only [rowPopped,List.head?_cons,List.tail_cons] using heb)
              (by simp [rowsReady,rowPorts,UnaryForPrograms.popped]) ht
            simpa [rowsResult,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv
          · simp only [List.length_cons]
            nlinarith


theorem scanRows_run {C : Type*} (s : Store) (encode : C → List Bool)
    (body : Code) (step : ℕ → C → List Bool → List Bool) (K : ℕ)
    (cs : List C) (hcs : s 205=Encoding.encodeList encode cs)
    (hn : (s 212).length=cs.length)
    (h120 : s 120=[]) (h230 : s 230=[]) (h231 : s 231=[]) (h218 : s 218=[])
    (hbody : ∀ j, j < cs.length → ∀ c rest acc count,
      ExecutesIn body K (rowsReady s encode j (c::rest) acc count)
        (rowsReady s encode (j+1) rest (step j c acc) count)) :
    ExecutesIn (scanRows body)
      (7*(s 205).length+9*cs.length+cs.length*(K+2)+20) s
      (Function.update s 217 (rowsResult step 0 cs (s 217))) := by
  let s1 := Function.update s 230 (s 205)
  let s2 := Function.update s1 231 (s 212)
  let s3 := rowsReady s encode cs.length [] (rowsResult step 0 cs (s 217)) []
  let s4 := Function.update s3 230 []
  have h1 : ExecutesIn (copy 205 230) (7*(s 205).length+5) s s1 := by
    simpa [s1,h230] using copy_run 205 230 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 212 231) (7*cs.length+5) s1 s2 := by
    simpa [s2,s1,h231,hn] using copy_run 212 231 s1
      (by decide) (by decide) (by decide) (by simp [s1,h120])
  have hin : rowsReady s encode 0 cs (s 217) (s 212)=s2 := by
    funext i
    by_cases h217' : i=217 <;> by_cases h218' : i=218 <;>
      by_cases h230' : i=230 <;> by_cases h231' : i=231 <;>
      simp [s2,s1,rowsReady,hcs,h218,h217',h218',h230',h231']
  have h3 : ExecutesIn (rowLoop body) (cs.length*(K+2)+2) s2 s3 := by
    have h := rowLoop_run s encode body step K cs.length hbody 0 cs (s 217) (s 212)
      (by omega) hn
    rw [hin] at h
    simpa [s3] using h
  have h4 : ExecutesIn (clear 230) 5 s3 s4 := by
    simpa [s4,s3,rowsReady,Encoding.encodeList] using clear_run 230 s3
  have hout : Function.update s4 218 []=Function.update s 217 (rowsResult step 0 cs (s 217)) := by
    funext i
    by_cases h217' : i=217 <;> by_cases h218' : i=218 <;>
      by_cases h230' : i=230 <;> by_cases h231' : i=231 <;>
      simp [s4,s3,rowsReady,h217',h218',h230',h231',h218,h230,h231]
  have h5 : ExecutesIn (clear 218) (2*cs.length+3) s4
      (Function.update s 217 (rowsResult step 0 cs (s 217))) := by
    have h := clear_run 218 s4
    rw [hout] at h
    simpa [s4,s3,rowsReady] using h
  have hcost : (7*(s 205).length+5) + ((7*cs.length+5) +
      ((cs.length*(K+2)+2) + (5 + (2*cs.length+3)))) =
      7*(s 205).length+9*cs.length+cs.length*(K+2)+20 := by
    omega
  rw [← hcost]
  simpa only [scanRows] using h1.seq (h2.seq (h3.seq (h4.seq h5)))


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete native coordinate-row scan with arithmetic callbacks discharged. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem rowsReady_lowFrame {C : Type*} (s : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) :
    CRTLocalProgram.LowFrame s (rowsReady s encode j cs acc count) := by
  intro i hi
  have h217 : i≠217 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h218 : i≠218 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h230 : i≠230 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h231 : i≠231 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [rowsReady,h217,h218,h230,h231]

private theorem coordinateLoadScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈coordinateLoadScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [coordinateLoadScratch] at hi
  omega

private theorem shiftScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈shiftScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [shiftScratch] at hi
  omega

private theorem coordinateEmitScratch_ne_rowsPorts :
    ∀ i : Fin 256, i∈coordinateEmitScratch →
      i≠217 ∧ i≠218 ∧ i≠230 ∧ i≠231 := by
  intro i hi
  simp [coordinateEmitScratch] at hi
  omega

/-- Every row is actually decoded, shifted and emitted by the fixed coordinate
worker. Source lengthN and target lengthJ are independent parameters. -/
theorem native_scan_run_oai (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J N : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i)=[])
    (h121 : s 121=[]) (h122 : s 122=[])
    (hcache : s 192=Fixed.encode (CRTLocalProgram.Model.zero ops.zeroRun.1 J))
    (hJcount : (s 193).length=J)
    (hzero : RingProgram.flat ops.zeroRun.1=List.replicate (d*baseWidth p t) false)
    (rows : List (Fixed.Array (baseWidth p t) d N)) (theta : Coeff (baseWidth p t) d)
    (hrows : s 205=Encoding.encodeList Fixed.encode rows)
    (hn : (s 212).length=rows.length)
    (hcount : (s 210).length=N) (hwidth : (s 211).length=d*baseWidth p t)
    (hx : s 247=Fixed.encode (CRTLocalProgram.Model.linear ops.zeroRun.1 ops.oneRun.1 theta J))
    (hJ : s 243=List.replicate J true) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth p t) false)
    (h254 : s 254=List.replicate (d*baseWidth p t) false)
    (heLoad : ∀ i ∈ coordinateLoadScratch,s i=[])
    (heShift : ∀ i ∈ shiftScratch,s i=[])
    (heEmit : ∀ i ∈ coordinateEmitScratch,s i=[])
    (h230 : s 230=[]) (h231 : s 231=[]) (h218 : s 218=[]) :
    ExecutesIn (scanRows coordinate)
      (7*(s 205).length+9*rows.length+rows.length*
        (nativeRowBudget N J rows.length (d*baseWidth p t)
          (nativeMulBudget J d (baseWidth p t)) (AddService.budget d (baseWidth p t) J J)+2)+20) s
      (Function.update s 217 (rowsResult (scanStep ops J rows.length N theta) 0 rows (s 217))) := by
  apply scanRows_run s Fixed.encode coordinate (scanStep ops J rows.length N theta)
    _ rows hrows hn (heLoad 120 (by simp [coordinateLoadScratch])) h230 h231 h218
  intro j hj c rest acc count
  let a := rowsReady s (Fixed.encode (J:=N)) j (c::rest) acc count
  let v : Fin rows.length := ⟨j,hj⟩
  have hf := rowsReady_lowFrame s (Fixed.encode (J:=N)) j (c::rest) acc count
  have hl : ∀ i∈coordinateLoadScratch,a i=[] := by
    intro i hi
    have hne := coordinateLoadScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heLoad i hi
  have hs : ∀ i∈shiftScratch,a i=[] := by
    intro i hi
    have hne := shiftScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heShift i hi
  have he : ∀ i∈coordinateEmitScratch,a i=[] := by
    intro i hi
    have hne := coordinateEmitScratch_ne_rowsPorts i hi
    simpa [a,rowsReady,Function.update_apply,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2] using heEmit i hi
  have h := native_coordinate_run p t M cache ops table hB hz hadd hmul a J scalarWidth frame
    (PairSpec.BaseReady.frame p t M cache table H hf)
    (fun i => (hf (bufferPorts i) (by fin_cases i <;> decide)).trans (hempty i))
    (by simpa [a,rowsReady] using h121) (by simpa [a,rowsReady] using h122)
    (by simpa [a,rowsReady] using hcache) (by simpa [a,rowsReady] using hJcount)
    hzero c.val theta v (Encoding.encodeList Fixed.encode rest)
    (by simp [a,rowsReady,Encoding.encodeList,Fixed.encode,DensePolynomialProgram.encode,
      HornerProgram.encodePolynomial,List.flatMap_def])
    (by simpa [a,rowsReady] using hn) (by simp [a,rowsReady,v])
    (by simpa [a,rowsReady,c.property] using hcount) (by simpa [a,rowsReady] using hwidth)
    (by simpa [a,rowsReady] using hx) (by simpa [a,rowsReady] using hJ)
    (by simpa [a,rowsReady] using h213) (by simpa [a,rowsReady] using h104)
    (by simpa [a,rowsReady] using h254) hl hs he
  have hout : Function.update (Function.update (Function.update a 230
      (Encoding.encodeList Fixed.encode rest)) 217 (coordinateResult ops J theta v c.val (a 217)))
      218 (true::a 218) =
      rowsReady s Fixed.encode (j+1) rest (scanStep ops J rows.length N theta j c acc) count := by
    funext i
    by_cases h217 : i=217 <;> by_cases h218 : i=218 <;>
      by_cases h230 : i=230 <;> by_cases h231 : i=231 <;>
      simp [a,rowsReady,scanStep,hj,v,Function.update_apply,h217,h218,h230,h231,List.replicate_succ]
  rw [hout] at h
  apply h.mono
  simp only [c.property,nativeRowBudget,v]
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.native_scan_run_oai
