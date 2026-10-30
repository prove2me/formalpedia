-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:28:24.783888+00:00
-- url     : https://prove2.me/submissions/7016d2ad-2c42-4d62-9fea-8691c3e9bc4f

import Mathlib
import Definitions.Def_OAIQ081S138

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramGeometricAt
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem geometricAt_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (z zero one : C) (hf : LowFrame base s)
    (hzero : s 242 = encode zero) (hone : s 220 = encode one) (hz : s 222 = encode z)
    (h120 : s 120 = []) (h224 : s 224 = []) (h240 : s 240 = []) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (geometricAt multiply add) (((s 243).length+1)*(Km+Ka+80*W+100)) s
      (Function.update s 224 (encode ((hornerValue mulOp addOp z one)^[(s 243).length] zero))) := by
  let g := (hornerValue mulOp addOp z one)^[(s 243).length] zero
  let s1 := Function.update s 240 (encode zero)
  let s2 := Function.update s1 241 (encode z)
  let s3 := Function.update s2 246 (s 243)
  let s4 := Function.update s2 240 (encode g)
  let s5 := Function.update s4 224 (encode g)
  have hf1 : LowFrame base s1 := lowFrame_update hf 240 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 241 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 246 (by decide) _
  have h1 : ExecutesIn (replace 242 240) (9*W+8) s s1 := by
    simpa [s1, hzero] using replace_bounded s 242 240 W (by decide) (by decide) (by decide)
      h120 (by simpa [hzero] using hwidth zero) (by simp [h240])
  have h2 : ExecutesIn (replace 222 241) (9*W+8) s1 s2 := by
    simpa [s2, s1, hz] using replace_bounded s1 222 241 W (by decide) (by decide) (by decide)
      (by simp [s1, h120]) (by simpa [s1, hz] using hwidth z) (by simp [s1, h241])
  have h3 : ExecutesIn (replace 243 246) (7*(s 243).length+8) s2 s3 := by
    simpa [s3, s2, s1, h246] using replace_run s2 243 246 (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120])
  have h4 : ExecutesIn (hornerCommand multiply add)
      ((s 243).length*(Km+Ka+34*W+36)+2) s3 s4 := by
    have h := hornerCommand_state base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s3 z one zero hf3 (by simp [s3, s2, s1]) (by simp [s3, s2])
      (by simp [s3, s2, s1, hone]) (by simp [s3, s2, s1, hz])
      (by simp [s3, s2, s1, h120]) (by simp [s3, s2, s1, h244])
      (by simp [s3, s2, s1, h245])
    have hc : (s3 246).length = (s 243).length := by simp [s3]
    rw [hc] at h
    have he : Function.update (Function.update s3 240 (encode g)) 246 [] = s4 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s4, s3, s2, s1, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s3 (Function.update (Function.update s3 240 (encode g)) 246 []) at h
    rw [he] at h
    exact h
  have h5 : ExecutesIn (replace 240 224) (9*W+8) s4 s5 := by
    simpa [s5, s4] using replace_bounded s4 240 224 W (by decide) (by decide) (by decide)
      (by simp [s4, s2, s1, h120]) (by simpa [s4] using hwidth g)
      (by simp [s4, s2, s1, h224])
  have h6 : ExecutesIn (SubexpLocalCRTSetup.clearMany [240,241]) (2*(2*W+3)) s5
      (Function.update s 224 (encode g)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [240,241] s5 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s5, s4] using hwidth g
      · simpa [s5, s4, s2] using hwidth z)
    have he : SubexpLocalCRTSetup.cleared [240,241] s5 = Function.update s 224 (encode g) := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 241 <;> by_cases hk : i = 224 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s5, s4, s2, s1,
 hi, hj, hk, h240, h241]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native local Hermite correction once the truncated cofactor and its
constant inverse have been prepared. Only output244 changes. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem correctionCommand_run_oai {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one negInverse inverse factor jet : C) (hf : LowFrame base s)
    (hzero : s 242 = encode zero) (hone : s 220 = encode one)
    (hneg : s 228 = encode negInverse) (hinv : s 227 = encode inverse)
    (hfactor : s 223 = encode factor) (hjet : s 225 = encode jet)
    (h120 : s 120 = []) (h222 : s 222 = []) (h224 : s 224 = [])
    (h240 : s 240 = []) (h241 : s 241 = []) (h244 : s 244 = [])
    (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (correctionCommand multiply add)
      (correctionBudget (s 243).length Km Ka W) s
      (Function.update s 244 (encode (correctionValue mulOp addOp
        zero one negInverse inverse factor jet (s 243).length))) := by
  let p := mulOp factor negInverse
  let z := addOp p one
  let g := (hornerValue mulOp addOp z one)^[(s 243).length] zero
  let inv := mulOp g inverse
  let v := mulOp inv jet
  let s1 := Function.update s 222 (encode p)
  let s2 := Function.update s1 222 (encode z)
  let s3 := Function.update s2 224 (encode g)
  let s4 := Function.update s3 224 (encode inv)
  let s5 := Function.update s4 224 (encode v)
  let s6 := Function.update s5 244 (encode v)
  have hf1 : LowFrame base s1 := lowFrame_update hf 222 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 222 (by decide) _
  have hf3 : LowFrame base s3 := lowFrame_update hf2 224 (by decide) _
  have hf4 : LowFrame base s4 := lowFrame_update hf3 224 (by decide) _
  have h1 : ExecutesIn (callAt multiply 223 228 222) (Km+40*W+50) s s1 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s factor negInverse 223 228 222
      (by decide) (by decide) (by decide) hf hfactor hneg h120 h240 h241 h244 h245
      (by simp [h222])
  have h2 : ExecutesIn (callAt add 222 220 222) (Ka+40*W+50) s1 s2 :=
    callAt_run base encode add addOp Ka W ha hwidth s1 p one 222 220 222
      (by decide) (by decide) (by decide) hf1 (by simp [s1]) (by simp [s1, hone])
      (by simp [s1, h120]) (by simp [s1, h240]) (by simp [s1, h241])
      (by simp [s1, h244]) (by simp [s1, h245]) (by simpa [s1] using hwidth p)
  have h3 : ExecutesIn (geometricAt multiply add)
      (((s 243).length+1)*(Km+Ka+80*W+100)) s2 s3 := by
    have h := geometricAt_run base encode multiply add mulOp addOp Km Ka W hm ha hwidth
      s2 z zero one hf2 (by simp [s2, s1, hzero]) (by simp [s2, s1, hone])
      (by simp [s2]) (by simp [s2, s1, h120]) (by simp [s2, s1, h224])
      (by simp [s2, s1, h240]) (by simp [s2, s1, h241])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245]) (by simp [s2, s1, h246])
    simpa only [s3, s2, s1, Function.update_of_ne (show (243 : Fin 256) ≠ 222 by decide)] using h
  have h4 : ExecutesIn (callAt multiply 224 227 224) (Km+40*W+50) s3 s4 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s3 g inverse 224 227 224
      (by decide) (by decide) (by decide) hf3 (by simp [s3])
      (by simp [s3, s2, s1, hinv]) (by simp [s3, s2, s1, h120])
      (by simp [s3, s2, s1, h240]) (by simp [s3, s2, s1, h241])
      (by simp [s3, s2, s1, h244]) (by simp [s3, s2, s1, h245])
      (by simpa [s3] using hwidth g)
  have h5 : ExecutesIn (callAt multiply 224 225 224) (Km+40*W+50) s4 s5 :=
    callAt_run base encode multiply mulOp Km W hm hwidth s4 inv jet 224 225 224
      (by decide) (by decide) (by decide) hf4 (by simp [s4])
      (by simp [s4, s3, s2, s1, hjet]) (by simp [s4, s3, s2, s1, h120])
      (by simp [s4, s3, s2, s1, h240]) (by simp [s4, s3, s2, s1, h241])
      (by simp [s4, s3, s2, s1, h244]) (by simp [s4, s3, s2, s1, h245])
      (by simpa [s4] using hwidth inv)
  have h6 : ExecutesIn (replace 224 244) (9*W+8) s5 s6 := by
    simpa [s6, s5] using replace_bounded s5 224 244 W (by decide) (by decide) (by decide)
      (by simp [s5, s4, s3, s2, s1, h120]) (by simpa [s5] using hwidth v)
      (by simp [s5, s4, s3, s2, s1, h244])
  have h7 : ExecutesIn (SubexpLocalCRTSetup.clearMany [222,224]) (2*(2*W+3)) s6
      (Function.update s 244 (encode v)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [222,224] s6 W (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [s6, s5, s4, s3, s2] using hwidth z
      · simpa [s6, s5] using hwidth v)
    have he : SubexpLocalCRTSetup.cleared [222,224] s6 = Function.update s 244 (encode v) := by
      funext i
      by_cases hi : i = 222 <;> by_cases hj : i = 224 <;> by_cases hk : i = 244 <;>
        simp [SubexpLocalCRTSetup.cleared_apply, s6, s5, s4, s3, s2, s1,
 hi, hj, hk, h222, h224]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))).mono
  dsimp [correctionBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.correctionCommand_run_oai.{u_1}
