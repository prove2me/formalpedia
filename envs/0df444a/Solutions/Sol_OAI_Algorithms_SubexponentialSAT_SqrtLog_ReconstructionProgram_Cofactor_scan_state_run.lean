-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:09:12.929181+00:00
-- url     : https://prove2.me/submissions/9506ec4a-3f07-4dcc-9c2b-9dd7a88c8bb6

import Mathlib
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S138
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNodeScanControl_command_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

theorem work_update (base : Store) (w : Fin 6 → List Bool) (i : Fin 6) (v : List Bool) :
    work base (Function.update w i v) = Function.update (work base w) (ports i) v :=
  ProgramLinking.extend_update ports.injective w base i v

theorem work_frame (base : Store) (w : Fin 6 → List Bool) (j : Fin 256)
    (hj : ¬ ∃ i, ports i = j) : work base w j = base j :=
  Function.extend_apply' _ _ _ hj

@[simp] theorem work_104 (base : Store) (w : Fin 6 → List Bool) : work base w 104 = base 104 :=
  work_frame base w 104 (by decide)
@[simp] theorem work_121 (base : Store) (w : Fin 6 → List Bool) : work base w 121 = base 121 :=
  work_frame base w 121 (by decide)
@[simp] theorem work_122 (base : Store) (w : Fin 6 → List Bool) : work base w 122 = base 122 :=
  work_frame base w 122 (by decide)

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar cofactor construction for the Hermite value at zero. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec binaryStep nativeRepeat replace loopReady)

theorem reframe_service {C : Type*} {base s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store} (hf : LowFrame base s)
    (encode : C → List Bool) (code : Code) (op : C → C → C) (K : ℕ)
    (h : ServiceSpec base encode code op K) : ServiceSpec s encode code op K := by
  intro t a b ht ha hb ho htmp
  apply h t a b _ ha hb ho htmp
  intro i hi
  exact (ht i hi).trans (hf i hi)

/-- Repetition can start in any framed caller state. Its counter is consumed. -/
theorem repeat_at_state {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (code : Code) (op : C → C → C) (K W : ℕ)
    (hspec : ServiceSpec base encode code op K) (hw : ∀ a, (encode a).length ≤ W)
    (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (hf : LowFrame base s) (factor seed : C)
    (h240 : s 240 = encode seed) (h241 : s 241 = encode factor)
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) (counter : List Bool) :
    ExecutesIn (nativeRepeat (binaryStep code))
      (counter.length * (K + 8 * W + 11) + 2)
      (Function.update s 246 counter)
      (Function.update s 240 (encode ((fun a => op a factor)^[counter.length] seed))) := by
  have h := CRTLocalProgram.binary_repeat_run s encode code op K W
    (reframe_service hf encode code op K hspec) hw factor seed h241 h244 h245 counter
  have hin : loopReady s encode seed counter = Function.update s 246 counter := by
    simp [loopReady, SubexpPolynomialIterationControl.ready, ← h240]
  have hout : loopReady s encode ((fun a => op a factor)^[counter.length] seed) [] =
      Function.update s 240 (encode ((fun a => op a factor)^[counter.length] seed)) := by
    funext i
    by_cases hi : i = 246 <;> by_cases hj : i = 240 <;>
      simp [loopReady, SubexpPolynomialIterationControl.ready, hi, hj, h246]
  simpa only [hin, hout] using h


theorem replace_bound (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (src dst : Fin 256) (W : ℕ)
    (hsd : src ≠ dst) (hs : src ≠ 120) (hd : dst ≠ 120)
    (ht : s 120 = []) (hsrc : (s src).length ≤ W) (hdst : (s dst).length ≤ W) :
    ExecutesIn (replace src dst) (9 * W + 8) s (Function.update s dst (s src)) :=
  (CRTLocalProgram.replace_run s src dst hsd hs hd ht).mono (by omega)

theorem includeNode_run {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length ≤ W)
    (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (a c : C) (hf : LowFrame base s)
    (ha : s 240 = encode a) (hc : s 218 = encode c) (hm : s 211 = encode minusOne)
    (hj : s 243 = List.replicate J true)
    (h120 : s 120 = []) (h219 : s 219 = []) (h223 : s 223 = [])
    (h241 : s 241 = []) (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (includeNode multiply) (includeBudget K W J) s
      (Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c)))
        219 (encode (mul c minusOne))) := by
  let neg := mul c minusOne
  let s1 := Function.update s 223 (encode a)
  let s2 := Function.update s1 240 (encode c)
  let s3 := Function.update s2 241 (encode minusOne)
  let s4 := Function.update s3 240 (encode neg)
  let s5 := Function.update s4 219 (encode neg)
  let s6 := Function.update s5 240 (encode a)
  let s7 := Function.update s6 241 (encode neg)
  let s8 := Function.update (Function.update s 219 (encode neg)) 241 (encode neg)
  have h1 : ExecutesIn (replace 240 223) (9 * W + 8) s s1 := by
    simpa [s1, ha] using replace_bound s 240 223 W (by decide) (by decide) (by decide)
      h120 (by simpa [ha] using hw a) (by simp [h223])
  have h2 : ExecutesIn (replace 218 240) (9 * W + 8) s1 s2 := by
    simpa [s2, s1, hc] using replace_bound s1 218 240 W (by decide) (by decide) (by decide)
      (by simp [s1, h120]) (by simpa [s1, hc] using hw c) (by simpa [s1, ha] using hw a)
  have h3 : ExecutesIn (replace 211 241) (9 * W + 8) s2 s3 := by
    simpa [s3, s2, s1, hm] using replace_bound s2 211 241 W (by decide) (by decide) (by decide)
      (by simp [s2, s1, h120]) (by simpa [s2, s1, hm] using hw minusOne)
      (by simp [s2, s1, h241])
  have hf3 : LowFrame base s3 := by
    intro i hi
    have h1 : i ≠ 223 := by intro h; subst i; omega
    have h2 : i ≠ 240 := by intro h; subst i; omega
    have h3 : i ≠ 241 := by intro h; subst i; omega
    simpa [s3, s2, s1, h1, h2, h3] using hf i hi
  have h4 : ExecutesIn (binaryStep multiply) (K + 8 * W + 9) s3 s4 := by
    apply CRTLocalProgram.binaryStep_run base encode multiply mul K W hspec hw s3 c minusOne hf3
    all_goals simp [ s3, s2, s1, h244, h245]
  have h5 : ExecutesIn (replace 240 219) (9 * W + 8) s4 s5 := by
    simpa [s5, s4] using replace_bound s4 240 219 W (by decide) (by decide) (by decide)
      (by simp [s4, s3, s2, s1, h120]) (by simp [s4]; exact hw neg)
      (by simp [s4, s3, s2, s1, h219])
  have h6 : ExecutesIn (replace 223 240) (9 * W + 8) s5 s6 := by
    simpa [s6, s5, s4, s3, s2, s1] using
      replace_bound s5 223 240 W (by decide) (by decide) (by decide)
        (by simp [s5, s4, s3, s2, s1, h120])
        (by simpa [s5, s4, s3, s2, s1] using hw a)
        (by simpa [s5, s4] using hw neg)
  have h7 : ExecutesIn (replace 219 241) (9 * W + 8) s6 s7 := by
    simpa [s7, s6, s5] using replace_bound s6 219 241 W (by decide) (by decide) (by decide)
      (by simp [s6, s5, s4, s3, s2, s1, h120])
      (by simpa [s6, s5] using hw neg)
      (by simpa [s6, s5, s4, s3] using hw minusOne)
  have he8 : Function.update s7 223 [] = s8 := by
    funext i
    by_cases h1 : i = 223 <;> by_cases h2 : i = 240 <;>
      by_cases h3 : i = 241 <;> by_cases h4 : i = 219 <;>
      simp [s8, s7, s6, s5, s4, s3, s2, s1,
        h1, h2, h3, h4, h223, ha]
  have h8 : ExecutesIn (clear 223) (2 * W + 3) s7 s8 := by
    have h := clear_run 223 s7
    rw [he8] at h
    apply h.mono
    simpa [s7, s6, s5, s4, s3, s2, s1] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw a)) 3
  have h9 : ExecutesIn (copy 243 246) (7 * J + 5) s8
      (Function.update s8 246 (List.replicate J true)) := by
    simpa [s8, hj, h246] using copy_run 243 246 s8 (by decide) (by decide) (by decide)
      (by simp [s8, h120])
  have hf8 : LowFrame base s8 := by
    intro i hi
    have h1 : i ≠ 219 := by intro h; subst i; omega
    have h2 : i ≠ 241 := by intro h; subst i; omega
    simpa [s8, h1, h2] using hf i hi
  have h10 : ExecutesIn (nativeRepeat (binaryStep multiply))
      (J * (K + 8 * W + 11) + 2)
      (Function.update s8 246 (List.replicate J true))
      (Function.update s8 240 (encode (includeValue mul minusOne J a c))) := by
    simpa only [List.length_replicate, includeValue, neg] using repeat_at_state base encode multiply mul K W hspec hw
      s8 hf8 neg a (by simp [s8, ha]) (by simp [s8])
      (by simp [s8, h244]) (by simp [s8, h245]) (by simp [s8, h246]) (List.replicate J true)
  have h11 : ExecutesIn (clear 241) (2 * W + 3)
      (Function.update s8 240 (encode (includeValue mul minusOne J a c)))
      (Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c)))
        219 (encode neg)) := by
    have h := clear_run 241 (Function.update s8 240 (encode (includeValue mul minusOne J a c)))
    have he : Function.update (Function.update s8 240 (encode (includeValue mul minusOne J a c))) 241 [] =
        Function.update (Function.update s 240 (encode (includeValue mul minusOne J a c))) 219 (encode neg) := by
      funext i
      by_cases h1 : i = 219 <;> by_cases h2 : i = 241 <;> by_cases h3 : i = 240 <;>
        simp [s8, h1, h2, h3, h241]
    rw [he] at h
    apply h.mono
    simpa [s8] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw neg)) 3
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9.seq (h10.seq h11)))))))))
  apply h.mono
  unfold includeBudget
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

private theorem scan_ports_high (i : Fin 6) : 205 ≤ (SubexponentialSAT.SubexpNodeScanControl.ports i).val := by
  fin_cases i <;> decide

theorem ready_low {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (cs : List C) (x : SubexponentialSAT.SubexpNodeScanControl.Cursor C) (current negative : List Bool) :
    LowFrame base (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x current negative) := by
  intro i hi
  apply SubexpNodeScanControl.work_frame
  rintro ⟨j, hj⟩
  have hg := scan_ports_high j
  have hv := congrArg Fin.val hj
  omega

private theorem ready_outside {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (cs : List C) (x : SubexponentialSAT.SubexpNodeScanControl.Cursor C) (current negative : List Bool) (j : Fin 256)
    (hj : ¬ ∃ i, SubexponentialSAT.SubexpNodeScanControl.ports i = j) :
    SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x current negative j = base j :=
  SubexpNodeScanControl.work_frame base _ j hj

theorem include_spec {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length ≤ W)
    (hm : base 211 = encode minusOne) (hj : base 243 = List.replicate J true)
    (hclean : ∀ j ∈ ([120,223,241,244,245,246] : List (Fin 256)), base j = []) :
    SubexpNodeScanControl.IncludeSpec (includeNode multiply) base encode encode
      (fun c => encode (mul c minusOne)) (includeValue mul minusOne J) (includeBudget K W J) := by
  intro cs x c
  let s := SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs x (encode c) []
  have hout (j : Fin 256) (h : ¬ ∃ i, SubexponentialSAT.SubexpNodeScanControl.ports i = j) : s j = base j :=
    ready_outside base encode cs x (encode c) [] j h
  have hh := includeNode_run base encode multiply mul minusOne K W J hspec hw s x.value c
    (ready_low base encode cs x (encode c) [])
    (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words]) (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words])
    ((hout 211 (by decide)).trans hm) ((hout 243 (by decide)).trans hj)
    ((hout 120 (by decide)).trans (hclean 120 (by simp)))
    (by simp [s, SubexponentialSAT.SubexpNodeScanControl.ready, SubexponentialSAT.SubexpNodeScanControl.words])
    ((hout 223 (by decide)).trans (hclean 223 (by simp)))
    ((hout 241 (by decide)).trans (hclean 241 (by simp)))
    ((hout 244 (by decide)).trans (hclean 244 (by simp)))
    ((hout 245 (by decide)).trans (hclean 245 (by simp)))
    ((hout 246 (by decide)).trans (hclean 246 (by simp)))
  have he : Function.update (Function.update s 240
      (encode (includeValue mul minusOne J x.value c))) 219 (encode (mul c minusOne)) =
      SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs {x with value := includeValue mul minusOne J x.value c}
        (encode c) (encode (mul c minusOne)) := by
    change Function.update (Function.update (SubexponentialSAT.SubexpNodeScanControl.work base (SubexponentialSAT.SubexpNodeScanControl.words encode encode cs x (encode c) []))
      (SubexponentialSAT.SubexpNodeScanControl.ports 3) _) (SubexponentialSAT.SubexpNodeScanControl.ports 5) _ = _
    rw [← SubexpNodeScanControl.work_update, ← SubexpNodeScanControl.work_update]
    apply congrArg (SubexponentialSAT.SubexpNodeScanControl.work base)
    funext i
    fin_cases i <;> simp [SubexponentialSAT.SubexpNodeScanControl.words]
  simpa only [he] using hh

theorem scan_run {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hm : base 211 = encode minusOne) (hj : base 243 = List.replicate J true)
    (hwidth : (base 104).length = W)
    (hclean : ∀ j ∈ ([120,121,122,223,241,244,245,246] : List (Fin 256)), base j = [])
    (cs : List C) (unit : C) :
    ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2)
      (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode cs ⟨unit, [], false⟩ [] [])
      (SubexponentialSAT.SubexpNodeScanControl.ready base encode encode []
        (SubexpNodeScanControl.run (includeValue mul minusOne J) cs ⟨unit, [], false⟩) [] []) := by
  apply SubexpNodeScanControl.command_run (includeNode multiply) base encode encode
    (fun c => encode (mul c minusOne)) (includeValue mul minusOne J)
    (includeBudget K W J) W _ hw hW (fun c => (hw _).le) hwidth
    (hclean 121 (by simp)) (hclean 122 (by simp)) cs ⟨unit, [], false⟩
  apply include_spec base encode multiply mul minusOne K W J hspec (fun a => (hw a).le) hm hj
  intro j hj
  apply hclean j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
  tauto

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

private theorem run_false {C : Type*} (f : C → C → C) (cs : List C) (a : C) :
    SubexpNodeScanControl.run f cs ⟨a, [], false⟩ = ⟨cs.foldl f a, [], false⟩ := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simpa [SubexpNodeScanControl.run, SubexpNodeScanControl.next] using ih (f a c)

theorem ready_eq_of_ports {C : Type*} (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (cs : List C) (a : C)
    (h : ∀ i, s (SubexpNodeScanControl.ports i) =
      SubexpNodeScanControl.words encode encode cs ⟨a, [], false⟩ [] [] i) :
    SubexpNodeScanControl.ready s encode encode cs ⟨a, [], false⟩ [] [] = s := by
  funext j
  by_cases hj : ∃ i, SubexpNodeScanControl.ports i = j
  · obtain ⟨i, rfl⟩ := hj
    exact (SubexpNodeScanControl.work_port s _ i).trans (h i).symm
  · exact SubexpNodeScanControl.work_frame s _ j hj

theorem scan_state_run_oai {C : Type*} (base : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (encode : C → List Bool)
    (multiply : Code) (mul : C → C → C) (minusOne : C) (K W J : ℕ)
    (hspec : ServiceSpec base encode multiply mul K)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (s : _root_.OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store) (hf : LowFrame base s) (cs : List C) (unit : C)
    (hm : s 211 = encode minusOne) (hj : s 243 = List.replicate J true)
    (hwidth : (s 104).length = W)
    (hstream : s 215 = cs.flatMap encode) (hunit : s 240 = encode unit)
    (hclean : ∀ j ∈ ([120,121,122,217,218,219,223,229,241,244,245,246] : List (Fin 256)), s j = []) :
    ExecutesIn (scan multiply) (cs.length * (includeBudget K W J + 18 * W + 28) + 2) s
      (Function.update (Function.update s 215 [])
        240 (encode (cs.foldl (includeValue mul minusOne J) unit))) := by
  have hh := scan_run s encode multiply mul minusOne K W J
    (reframe_service hf encode multiply mul K hspec) hw hW hm hj hwidth
    (by
      intro j hj
      apply hclean j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
      tauto) cs unit
  have hin : SubexpNodeScanControl.ready s encode encode cs ⟨unit, [], false⟩ [] [] = s := by
    apply ready_eq_of_ports
    intro i
    fin_cases i <;> simp [SubexpNodeScanControl.ports, SubexpNodeScanControl.words,
      SubexpNodeScanControl.marker, hstream, hunit,
      hclean 217 (by simp), hclean 218 (by simp), hclean 219 (by simp), hclean 229 (by simp)]
  have hout : SubexpNodeScanControl.ready s encode encode []
      (SubexpNodeScanControl.run (includeValue mul minusOne J) cs ⟨unit, [], false⟩) [] [] =
      Function.update (Function.update s 215 [])
        240 (encode (cs.foldl (includeValue mul minusOne J) unit)) := by
    rw [run_false]
    conv_rhs => rw [← hin]
    change SubexpNodeScanControl.work s _ = Function.update (Function.update
      (SubexpNodeScanControl.work s _) (SubexpNodeScanControl.ports 0) [])
        (SubexpNodeScanControl.ports 3) _
    rw [← SubexpNodeScanControl.work_update, ← SubexpNodeScanControl.work_update]
    apply congrArg (SubexpNodeScanControl.work s)
    funext i
    fin_cases i <;> simp [SubexpNodeScanControl.words]
  simpa only [hin, hout] using hh

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor.scan_state_run_oai.{u_1}
