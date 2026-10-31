-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:47:41.453069+00:00
-- url     : https://prove2.me/submissions/1771150e-7063-4630-b449-92729d49e49d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_Numerator_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update callAt callAt_run)

theorem scaledValue_decode {C A : Type*} [CommRing A] (decode : C → A)
    (mul add : C → C → C)
    (hm : ∀ x y, decode (mul x y) = decode x * decode y)
    (ha : ∀ x y, decode (add x y) = decode x + decode y)
    (zero one minusOne invDenom : C) (hz : decode zero = 0) (ho : decode one = 1)
    (hn : decode minusOne = -1) (positive negative : List Bool) :
    decode (scaledValue mul add zero one minusOne invDenom positive negative) =
      -(decode invDenom) * (((BinaryArithmetic.toNat positive : ℤ) -
        (BinaryArithmetic.toNat negative : ℤ) : ℤ) : A) := by
  rw [scaledValue, hm, hm, signedValue_decode decode mul add hm ha zero one minusOne hz ho hn,
    hn]
  ring

theorem scaledCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hw : ∀ a, (encode a).length ≤ W)
    (s : Store) (zero one minusOne invDenom : C) (hf : LowFrame base s) (hc : Clean s)
    (hz : s 249 = encode zero) (ho : s 250 = encode one) (hn : s 251 = encode minusOne)
    (hinv : s 252 = encode invDenom)
    (h246 : s 246 = []) (h247 : s 247 = []) (h248 : s 248 = []) (h255 : s 255 = []) :
    ExecutesIn (scaledCommand multiply add)
      (scaledBudget ((s 253).length + (s 254).length) Km Ka W) s
      (Function.update s 255 (encode (scaledValue mulOp addOp zero one minusOne invDenom
        (s 253) (s 254)))) := by
  let x := signedValue mulOp addOp zero one minusOne (s 253) (s 254)
  let y := mulOp x invDenom
  let z := mulOp y minusOne
  let s1 := Function.update s 255 (encode x)
  let s2 := Function.update s 255 (encode y)
  have h1 := signedCommand_run base encode multiply add mulOp addOp Km Ka W hm ha hw
    s zero one minusOne hf hc hz ho hn h246 h247 h248 h255
  have hf1 : LowFrame base s1 := lowFrame_update hf 255 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf 255 (by decide) _
  have h2 : ExecutesIn (callAt multiply 255 252 255) (Km+40*W+50) s1 s2 := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s1 x invDenom
      255 252 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf1 (by simp [s1])
      (by simp [s1, hinv]) (by simp [s1, hc.1]) (by simp [s1, hc.2.1])
      (by simp [s1, hc.2.2.1]) (by simp [s1, hc.2.2.2.1])
      (by simp [s1, hc.2.2.2.2]) (by simpa [s1] using hw x)
    simpa [s1, s2, y] using h
  have h3 : ExecutesIn (callAt multiply 255 251 255) (Km+40*W+50) s2
      (Function.update s 255 (encode z)) := by
    have h := callAt_run base encode multiply mulOp Km W hm hw s2 y minusOne
      255 251 255 (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) (by unfold CRTLocalProgram.CachePort; decide) hf2 (by simp [s2])
      (by simp [s2, hn]) (by simp [s2, hc.1]) (by simp [s2, hc.2.1])
      (by simp [s2, hc.2.2.1]) (by simp [s2, hc.2.2.2.1])
      (by simp [s2, hc.2.2.2.2]) (by simpa [s2] using hw y)
    simpa [s2, z] using h
  exact (h1.seq (h2.seq h3)).mono (by unfold scaledBudget; omega)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramCached
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache-extensional interface for the same fixed integer-lift programs.
Setup may supply any represented zero, one and minus-one bytes whose decoded
values are correct. This avoids requiring its constant-vector construction
to equal a particular arithmetic expression byte for byte. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

theorem cachedScaledCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d) (s : Store)
    (h : CachedReady t a M cache zero one minusOne s) (hi : s 252 = RingProgram.flat invDenom) :
    ExecutesIn modelScaledCommand (modelScaledBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat
        (cachedScaledValue t a M cache zero one minusOne invDenom (s 253) (s 254)))) := by
  exact scaledCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s zero one minusOne invDenom (lowFrame_refl s)
    h.clean h.zero h.one h.minusOne hi h.bits h.accumulator h.place h.output

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control that constructs an ordered scalar table. The callback is an
actual finite command with a measured execution contract. Runtime unary node
indices and counters do not change the command. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem popped_loopState (base : Store) (j : ℕ) (remaining acc : List Bool)
    (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped ports (⟨regs,loopState base j remaining acc⟩ : Data) =
      (⟨readRegs regs 14 15 remaining.head?,
        loopState base j remaining.tail acc⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,ports,loopState]
  · funext i
    by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
      simp [UnaryForPrograms.popped,ports,loopState,h37,h64,h65]

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramRelation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relational refinement of the same table builder. Each scalar may have any
correct byte representation; all table entries are obtained from executions. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open _root_.OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl (transfer transfer_run)
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem append_scalar_run (base : Store) (j : ℕ) (remaining acc word : List Bool)
    (h255 : base 255 = []) :
    ExecutesIn (.seq (transfer 255 65) advance) (3*word.length+5)
      (Function.update (loopState base j remaining acc) 255 word)
      (loopState base (j+1) remaining (word.reverse ++ acc)) := by
  let s1 := Function.update (loopState base j remaining acc) 255 word
  let s2 := loopState base j remaining (word.reverse ++ acc)
  have he2 : Function.update (Function.update s1 255 []) 65
      ((s1 255).reverse ++ s1 65) = s2 := by
    funext i
    by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;>
      by_cases h65 : i = 65 <;> by_cases hi255 : i = 255 <;>
      simp [s2,s1,loopState,Function.update_apply,h37,h64,h65,hi255,h255]
  have h2 : ExecutesIn (transfer 255 65) (3*word.length+3) s1 s2 := by
    have h := transfer_run 255 65 s1 (by decide)
    rw [he2] at h
    simpa [s1] using h
  have h3 : ExecutesIn advance 2 s2
      (loopState base (j+1) remaining (word.reverse ++ acc)) := by
    intro regs
    refine ⟨2,Function.update regs 0 true,le_rfl,?_⟩
    have h := Subexp.TupleProgram.pushConst_eval (37 : Fin 256) (0 : Fin 16) true
      (⟨regs,s2⟩ : Data)
    have he : Function.update s2 37 (true :: s2 37) =
        loopState base (j+1) remaining (word.reverse ++ acc) := by
      funext i
      by_cases h37 : i = 37 <;> by_cases h64 : i = 64 <;> by_cases h65 : i = 65 <;>
        simp [s2,loopState,h37,h64,h65,List.replicate_succ]
    simpa only [advance,Subexp.TupleProgram.pushedState,he] using h
  exact (h2.seq h3).mono (by omega)

theorem loop_visits_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (h255 : base 255 = [])
    (remaining acc : List Bool) (j : ℕ) (hj : j + remaining.length ≤ Q)
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (costs : List ℕ) (n : ℕ) (rf : Fin 16 → Bool),
      words.length = remaining.length ∧
      (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' j remaining.length) words ∧
      n ≤ remaining.length*(K+3*W+7)+2 ∧
      UnaryForPrograms.Visits ports (body callback) costs n
        (⟨regs,loopState base j remaining acc⟩ : Data)
        (⟨rf,loopState base (j+remaining.length) []
          (words.flatten.reverse ++ acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,rfl,by simp,by simp,by simp,?_⟩
    simpa only [popped_loopState,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,List.flatten_nil,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := ports) (body := body callback)
        (⟨regs,loopState base j [] acc⟩ : Data) (by simp [loopState,ports])
  | cons bit remaining ih =>
    obtain ⟨nc,rc,word,hnc,hw,hv,hc⟩ := spec j
      (by simp only [List.length_cons] at hj; omega) remaining acc
      (readRegs regs 14 15 (some bit))
    obtain ⟨na,ra,hna,ha⟩ := append_scalar_run base j remaining acc word h255 rc
    have hb : Eval (body callback) (nc+na)
        (⟨readRegs regs 14 15 (some bit),loopState base j remaining acc⟩ : Data)
        (⟨ra,loopState base (j+1) remaining (word.reverse ++ acc)⟩ : Data) := hc.seq ha
    obtain ⟨words,costs,nt,rt,hl,hws,hvs,hnt,ht⟩ := ih (word.reverse ++ acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) ra
    refine ⟨word::words,(nc+na)::costs,nc+na+nt+2,rt,by simp [hl],?_,?_,?_,?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact hws x hx
    · simpa only [List.length_cons,List.range'_succ] using List.Forall₂.cons hv hvs
    · simp only [List.length_cons]
      rw [hw] at hna
      nlinarith
    · have h := UnaryForPrograms.Visits.step (p := ports) (body := body callback)
        (d := (⟨regs,loopState base j (bit::remaining) acc⟩ : Data))
        (by simp [loopState,ports])
        (by simpa only [popped_loopState,List.head?_cons,List.tail_cons] using hb)
        (by simp [loopState,ports,UnaryForPrograms.popped]) ht
      simpa only [List.length_cons,List.flatten_cons,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem command_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (n : ℕ) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' 0 Q) words ∧
      n ≤ Q*(K+6*W+16)+13 ∧
      Eval (command callback) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 67 words.flatten⟩ : Data) := by
  let s1 := loopState base 0 (base 22) []
  have he1 : Function.update base 64 (base 22 ++ base 64) = s1 := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;> by_cases hi65 : i = 65 <;>
      simp [s1,loopState,hi37,hi64,hi65,h37,h64,h65]
  obtain ⟨n1,r1,hn1,e1⟩ := copy_run 22 64 base (by decide) (by decide) (by decide) h120 regs
  rw [he1] at e1
  obtain ⟨words,costs,n2,r2,hl,hws,hvs,hn2,hv⟩ := loop_visits_relation callback base valid
    Q K W spec h255 (base 22) [] 0 (by omega) r1
  simp only [hQ,Nat.zero_add,List.append_nil] at hl hvs hn2 hv
  let s2 := loopState base Q [] words.flatten.reverse
  let s3 := Function.update s2 37 []
  have e2 : Eval (loop callback) n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := hv.eval
  obtain ⟨n3,r3,hn3,e3⟩ := clear_run 37 s2 r2
  have he4 : Function.update (Function.update s3 65 []) 67
      ((s3 65).reverse ++ s3 67) = Function.update base 67 words.flatten := by
    funext i
    by_cases hi37 : i = 37 <;> by_cases hi64 : i = 64 <;>
      by_cases hi65 : i = 65 <;> by_cases hi67 : i = 67 <;>
      simp [s3,s2,loopState,hi37,hi64,hi65,hi67,h37,h64,h65,h67]
  obtain ⟨n4,r4,hn4,e4⟩ := transfer_run 65 67 s3 (by decide) r3
  rw [he4] at e4
  have hflat : words.flatten.length = Q*W := by
    rw [List.length_flatten]
    have hm : words.map List.length = words.map (fun _ => W) := by
      apply List.map_congr_left
      exact hws
    rw [hm]
    simp [hl]
  refine ⟨words,n1+(n2+(n3+n4)),r4,hl,hws,hvs,?_,e1.seq (e2.seq (e3.seq e4))⟩
  simp only [hQ] at hn1
  have hs2 : (s2 37).length = Q := by simp [s2,loopState]
  have hs3 : (s3 65).length = Q*W := by simp [s3,s2,loopState,hflat]
  rw [hs2] at hn3
  rw [hs3] at hn4
  nlinarith

theorem program_relation (callback : Code) (base : Store)
    (valid : ℕ → List Bool → Prop) (Q K W : ℕ)
    (spec : CallbackRelation callback base valid Q K W) (hQ : (base 22).length = Q)
    (h37 : base 37 = []) (h64 : base 64 = []) (h65 : base 65 = [])
    (h67 : base 67 = []) (h120 : base 120 = []) (h255 : base 255 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = W) ∧
      List.Forall₂ valid (List.range' 0 Q) words ∧
      RunsIn (program callback) (Q*(K+6*W+16)+14)
        ((⟨regs,base⟩ : Data).withPC (some (program callback).entry))
        ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none) := by
  obtain ⟨words,n,rf,hl,hw,hv,hn,he⟩ := command_relation callback base valid Q K W spec hQ
    h37 h64 h65 h67 h120 h255 regs
  exact ⟨words,rf,hl,hw,hv,n+1,by omega,compiled_halt_trace he 22 67⟩

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port maps and the persistent ring-cache frame for source-table
callbacks. These lemmas are independent of the integer numerator evaluator. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem numeratorRegs_injective : Function.Injective numeratorRegs :=
  Fin.castAdd_injective _ _

theorem numeratorPorts_injective : Function.Injective numeratorPorts := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp only [numeratorPorts] at hv
  split_ifs at hv <;> simp_all <;> omega

/-- Ring service invariants depend only on their own high registers. -/
theorem cachedReady_frame (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (base s : Store)
    (h : CachedReady t a M cache zero one minusOne base)
    (hf : ∀ i : Fin 256, 120 ≤ i.val → i ≠ 253 → i ≠ 254 → s i = base i) :
    CachedReady t a M cache zero one minusOne s := by
  have he (i : Fin 256) (hi : 120 ≤ i.val) (h253 : i ≠ 253) (h254 : i ≠ 254) :=
    hf i hi h253 h254
  have h120 := he 120 (by decide) (by decide) (by decide)
  have h194 := he 194 (by decide) (by decide) (by decide)
  have h201 := he 201 (by decide) (by decide) (by decide)
  have h202 := he 202 (by decide) (by decide) (by decide)
  have h203 := he 203 (by decide) (by decide) (by decide)
  have h204 := he 204 (by decide) (by decide) (by decide)
  have hn : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s := by
    refine ⟨⟨h120.trans h.native.workspace.1,?_⟩,h194.trans h.native.modulus,
      ?_,h203.trans h.native.zero,h201.trans h.native.table,?_⟩
    · intro i
      have hp := hf (ReconstructionProgram.RingAdapter.ports i)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      rw [hp]
      simpa only [ReconstructionProgram.RingAdapter.finalNative,h194,h201,h202,h203]
        using h.native.workspace.2 i
    · simpa only [h202] using h.native.width
    · simpa only [h204] using h.native.degree
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases h.clean with ⟨h1,h2,h3,h4,h5⟩
    exact ⟨h120.trans h1,(he 240 (by decide) (by decide) (by decide)).trans h2,
      (he 241 (by decide) (by decide) (by decide)).trans h3,
      (he 244 (by decide) (by decide) (by decide)).trans h4,
      (he 245 (by decide) (by decide) (by decide)).trans h5⟩
  · exact (he 249 (by decide) (by decide) (by decide)).trans h.zero
  · exact (he 250 (by decide) (by decide) (by decide)).trans h.one
  · exact (he 251 (by decide) (by decide) (by decide)).trans h.minusOne
  · exact (he 246 (by decide) (by decide) (by decide)).trans h.bits
  · exact (he 247 (by decide) (by decide) (by decide)).trans h.accumulator
  · exact (he 248 (by decide) (by decide) (by decide)).trans h.place
  · exact (he 255 (by decide) (by decide) (by decide)).trans h.output

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Native

theorem numerator_eval {r Q : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (s : Store) (regs : Fin 16 → Bool)
    (hinput : ∀ i, s (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (regs ∘ numeratorRegs) t u y [] [] ([],[])).stacks i) :
    ∃ n rf result,
      n ≤ LayoutProgram.Numerator.budget as.length R width.length (pairLength power) t u y + 1 ∧
      Eval numerator n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (Function.update s 253 result.1) 254 result.2⟩ : Data) ∧
      pairValue result = LayoutProgram.Numerator.value as.length R t u y ∧
      pairLength result ≤ R * LayoutProgramScalar.termGrowth
        (2*width.length+pairLength power) := by
  let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as
  let start := LayoutProgram.Numerator.state c (regs ∘ numeratorRegs) t u y [] [] ([],[])
  obtain ⟨n,hn,rr,result,he,hval,hmass,hlength⟩ := LayoutProgram.Numerator.command_eval
    Hwords width power (regs ∘ numeratorRegs) as R t u y hlen hwords hvalues hp hpt hwidth hAQ hQ
  have hin : projectState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data) = start := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; exact hinput i
  have he' : Eval LayoutProgram.Numerator.command n
      (projectState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data))
      (LayoutProgram.Numerator.state c rr t u y [] [] result) := by
    rw [hin]; exact he
  have hr := eval_liftCommand_from_state LayoutProgram.Numerator.command 23 50
    numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
    numeratorRegs_injective numeratorPorts_injective he'
  have hout : (LayoutProgram.Numerator.state c rr t u y [] [] result).stacks =
      Function.update (Function.update start.stacks 50 result.1) 51 result.2 := by
    funext i
    by_cases h50 : i = 50 <;> by_cases h51 : i = 51 <;>
      simp [LayoutProgram.Numerator.state,start,Function.update_apply,h50,h51]
  have hbase : Function.extend numeratorPorts start.stacks s = s := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
        numeratorRegs_injective numeratorPorts_injective)
    rw [hin] at h
    exact h
  have hs : (embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
      (LayoutProgram.Numerator.state c rr t u y [] [] result)).stacks =
      Function.update (Function.update s 253 result.1) 254 result.2 := by
    change Function.extend numeratorPorts _ s = _
    rw [hout,ProgramLinking.extend_update numeratorPorts_injective,
      ProgramLinking.extend_update numeratorPorts_injective,hbase]
    rfl
  have heq : embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
      (LayoutProgram.Numerator.state c rr t u y [] [] result) =
      (⟨(embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
        (LayoutProgram.Numerator.state c rr t u y [] [] result)).regs,
        Function.update (Function.update s 253 result.1) 254 result.2⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hs
  rw [heq] at hr
  exact ⟨n+1,_,result,by omega,hr,hval,
    hlength.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))⟩



theorem callback_eval {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (node : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (ready : CachedReady t a M cache zero one minusOne s)
    (hinv : s 252 = RingProgram.flat invDenom) (regs : Fin 16 → Bool)
    (hinput : ∀ i, s (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (regs ∘ numeratorRegs) node u y [] [] ([],[])).stacks i) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool) (out : ModelCode t d),
      n ≤ callbackBudget
        (LayoutProgram.Numerator.budget as.length R width.length (pairLength power) node u y)
        (integerBits R width.length (pairLength power)) t d ∧
      Eval callback n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update s 255 (RingProgram.flat out)⟩ : Data) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value as.length R node u y : ℤ) : a.O t) := by
  have h253 : s 253 = [] := by
    simpa [numeratorPorts,LayoutProgram.Numerator.state] using hinput 50
  have h254 : s 254 = [] := by
    simpa [numeratorPorts,LayoutProgram.Numerator.state] using hinput 51
  obtain ⟨n1,r1,result,hn1,e1,hval,hlenResult⟩ := numerator_eval Hwords width power as R node
    u y hlen hwords hvalues hp hpt hwidth hAQ hQ s regs hinput
  let s1 := Function.update (Function.update s 253 result.1) 254 result.2
  let out := cachedScaledValue t a M cache zero one minusOne invDenom result.1 result.2
  let s2 := Function.update s1 255 (RingProgram.flat out)
  let s3 := Function.update s2 253 []
  have hr : CachedReady t a M cache zero one minusOne s1 := by
    apply cachedReady_frame t a M cache zero one minusOne s s1 ready
    intro i hi h1 h2
    simp [s1,h1,h2]
  have hri : s1 252 = RingProgram.flat invDenom := by simp [s1,hinv]
  obtain ⟨n2,r2,hn2,e2⟩ := cachedScaledCommand_run t a M cache hz
    zero one minusOne invDenom s1 hr hri r1
  have e2' : Eval modelScaledCommand n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := by
    simpa [s2,out,s1] using e2
  have hb : modelScaledBudget (result.1.length+result.2.length) t d ≤
      _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.polynomialBudget (integerBits R width.length (pairLength power)) t d := by
    apply (modelScaledBudget_polynomial _ _ _).trans
    unfold _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.polynomialBudget
    have hsize : result.1.length+result.2.length ≤ integerBits R width.length (pairLength power) :=
      hlenResult
    gcongr
  have hn2' : n2 ≤ _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.polynomialBudget (integerBits R width.length (pairLength power)) t d := by
    apply LE.le.trans hn2
    simpa [s1] using hb
  obtain ⟨n3,r3,hn3,e3⟩ := clear_run 253 s2 r2
  obtain ⟨n4,r4,hn4,e4⟩ := clear_run 254 s3 r3
  have hfinal : Function.update s3 254 [] = Function.update s 255 (RingProgram.flat out) := by
    funext i
    by_cases h1 : i = 253 <;> by_cases h2 : i = 254 <;> by_cases h3 : i = 255 <;>
      simp [s3,s2,s1,h1,h2,h3,h253,h254]
  rw [hfinal] at e4
  have hdecode : (RingProgram.modelRing t ht hd a M cache).decode out =
      -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        ((LayoutProgram.Numerator.value as.length R node u y : ℤ) : a.O t) := by
    let ops := RingProgram.modelRing t ht hd a M cache
    have hh := scaledValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
      zero one minusOne invDenom hzero hone hminus result.1 result.2
    change ops.decode out = _
    change ops.decode out = _ at hh
    rw [show ((BinaryArithmetic.toNat result.1 : ℤ) -
      (BinaryArithmetic.toNat result.2 : ℤ)) = LayoutProgram.Numerator.value as.length R node u y
        by exact hval] at hh
    exact hh
  refine ⟨n1+(n2+(n3+n4)),r4,out,?_,e1.seq (e2'.seq (e3.seq e4)),hdecode⟩
  have hn3' : n3 ≤ 2*result.1.length+3 := by simpa [s2,s1] using hn3
  have hn4' : n4 ≤ 2*result.2.length+3 := by simpa [s3,s2,s1] using hn4
  unfold callbackBudget
  change result.1.length+result.2.length ≤ integerBits R width.length (pairLength power) at hlenResult
  omega

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod


namespace Native

theorem state_node_update {r Q : ℕ} (c : LayoutProgram.Numerator.Saved)
    (regs : Fin 10 → Bool) (start node : Fin Q) (u y : UniversalType r Q 1) :
    (LayoutProgram.Numerator.state c regs node u y [] [] ([],[])).stacks =
      Function.update (LayoutProgram.Numerator.state c regs start u y [] [] ([],[])).stacks
        37 (List.replicate node.val true) := by
  first | done | (funext i; fin_cases i <;> rfl)

theorem port_range (i : Fin 64) :
    (numeratorPorts i).val < 64 ∨ numeratorPorts i = 253 ∨ numeratorPorts i = 254 := by
  by_cases h50 : i = 50
  · simp [numeratorPorts,h50]
  · by_cases h51 : i = 51
    · simp [numeratorPorts,h51]
    · simp [numeratorPorts,h50,h51]

theorem loop_input {r Q : ℕ} (c : LayoutProgram.Numerator.Saved)
    (start node : Fin Q) (u y : UniversalType r Q 1) (base : Store)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state c (fun _ => false) start u y [] [] ([],[])).stacks i)
    (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    ∀ i, (loopState base node.val remaining acc) (numeratorPorts i) =
      (LayoutProgram.Numerator.state c (regs ∘ numeratorRegs) node u y [] [] ([],[])).stacks i := by
  intro i
  have h64 : numeratorPorts i ≠ 64 := by
    have h := port_range i
    rcases h with h | h | h
    · intro he; rw [he] at h; norm_num at h
    · rw [h]; decide
    · rw [h]; decide
  have h65 : numeratorPorts i ≠ 65 := by
    have h := port_range i
    rcases h with h | h | h
    · intro he; rw [he] at h; norm_num at h
    · rw [h]; decide
    · rw [h]; decide
  by_cases hi : i = 37
  · subst i
    simp [loopState,numeratorPorts,LayoutProgram.Numerator.state,
      LayoutProgram.Numerator.baseStacks,LayoutProgram.Guard.guardInput]
  · have h37 : numeratorPorts i ≠ 37 := by
      intro he
      have hv := congrArg Fin.val he
      unfold numeratorPorts at hv
      split_ifs at hv <;> simp_all ; omega
    rw [loopState,Function.update_of_ne h65,Function.update_of_ne h64,
      Function.update_of_ne h37,hinput i]
    have he := congrFun (state_node_update c (regs ∘ numeratorRegs) start node u y) i
    simpa [Function.update_of_ne hi,LayoutProgram.Numerator.state] using he.symm

theorem callback_relation {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
    (hinv : base 252 = RingProgram.flat invDenom)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _ => false) start u y [] [] ([],[])).stacks i) :
    CallbackRelation callback base (ValidWord as.length R t ht hd a M cache invDenom u y)
      Q (callbackBudget (numeratorBudget as.length R width.length (pairLength power) u y)
        (integerBits R width.length (pairLength power)) t d) (d * SubexpLiftRing.baseWidth 3 t) := by
  intro j hj remaining acc regs
  let node : Fin Q := ⟨j,hj⟩
  let s := loopState base j remaining acc
  have hready : CachedReady t a M cache zero one minusOne s := by
    apply cachedReady_frame t a M cache zero one minusOne base s ready
    intro i hi h253 h254
    have h37 : i ≠ 37 := by intro h; subst i; norm_num at hi
    have h64 : i ≠ 64 := by intro h; subst i; norm_num at hi
    have h65 : i ≠ 65 := by intro h; subst i; norm_num at hi
    simp [s,loopState,h37,h64,h65]
  have hi : s 252 = RingProgram.flat invDenom := by simp [s,loopState,hinv]
  have hsource := loop_input
    (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
    start node u y base hinput remaining acc regs
  obtain ⟨n,rf,out,hn,he,hv⟩ := callback_eval Hwords width power as R node u y
    hlen hwords hvalues hp hpt hwidth hAQ hQ t ht hd a M cache hz
    zero one minusOne invDenom hzero hone hminus s hready hi regs hsource
  have hnum : LayoutProgram.Numerator.budget as.length R width.length (pairLength power) node u y ≤
      numeratorBudget as.length R width.length (pairLength power) u y := by
    unfold numeratorBudget
    exact Finset.single_le_sum
      (f := fun k : Fin Q => LayoutProgram.Numerator.budget as.length R width.length (pairLength power) k u y)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ node)
  refine ⟨n,rf,RingProgram.flat out,?_,RingProgram.flat_length out,?_,he⟩
  · unfold callbackBudget at *
    omega
  · exact ⟨hj,out,rfl,hv⟩

/-- The resulting table is produced by a fixed native program from metadata
and prepared arithmetic caches, with a decode witness at every node. -/
theorem tableProgram_runsIn_oai {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
    (hinv : base 252 = RingProgram.flat invDenom)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _ => false) start u y [] [] ([],[])).stacks i)
    (hq : (base 22).length = Q) (h37 : base 37 = [])
    (h64 : base 64 = []) (h65 : base 65 = []) (h67 : base 67 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = d * SubexpLiftRing.baseWidth 3 t) ∧
      List.Forall₂ (ValidWord as.length R t ht hd a M cache invDenom u y) (List.range' 0 Q) words ∧
      RunsIn tableProgram (tableBudget as.length R width.length (pairLength power) t d u y)
        ((⟨regs,base⟩ : Data).withPC (some tableProgram.entry))
        ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none) := by
  have hs := callback_relation Hwords width power as R start u y hlen hwords hvalues hp hpt
    hwidth hAQ hQ t ht hd a M cache hz zero one minusOne invDenom hzero hone hminus base ready hinv hinput
  exact program_relation callback base _ Q _ _ hs hq h37 h64 h65 h67 ready.clean.1 ready.output regs

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn_oai
