-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:25:53.827708+00:00
-- url     : https://prove2.me/submissions/3a3b99b6-e796-478f-800a-0e0b5e89c4f9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Source_native_command_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_SourceReady_Input_native
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableProgram_specializeCall_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem decodeBasePort_low (i : Fin 896) (hi : i.val < 768) :
    decodeBasePort i = i.val := by
  have h885 : i ≠ 885 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h886 : i ≠ 886 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h887 : i ≠ 887 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h888 : i ≠ 888 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h889 : i ≠ 889 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h890 : i ≠ 890 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h891 : i ≠ 891 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h892 : i ≠ 892 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp only [decodeBasePort, ite_eq_right h885, ite_eq_right h886, ite_eq_right h887,
    ite_eq_right h888, ite_eq_right h889, ite_eq_right h890, ite_eq_right h891,
    ite_eq_right h892]

private theorem decodeBasePort_basePort (i : Fin 768) : decodeBasePort (basePort i) = i.val := by
  unfold basePort
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · subst i; rfl
  · exact decodeBasePort_low _ i.isLt

theorem basePort_injective : Function.Injective basePort := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg decodeBasePort hij
  simpa only [decodeBasePort_basePort] using hv

theorem basePort_low (i : Fin 768) (hi : i.val < 640) : basePort i = i.castAdd 128 := by
  have hn (j : Fin 768) (hj : 640 ≤ j.val) : i ≠ j := by
    intro h
    subst j
    omega
  simp only [basePort, ite_eq_right (hn 640 (by decide)),
    ite_eq_right (hn 641 (by decide)), ite_eq_right (hn 642 (by decide)),
    ite_eq_right (hn 647 (by decide)), ite_eq_right (hn 650 (by decide)),
    ite_eq_right (hn 651 (by decide)), ite_eq_right (hn 670 (by decide)),
    ite_eq_right (hn 671 (by decide))]

theorem basePort_inner (i : Fin 256) :
    basePort (PerturbationAssembly.innerPort i) = innerPort i := by
  rw [basePort_low _ (by change 340+i.val<640; omega)]
  rfl

/-- The joined input uses the existing low256 words and exactly38 empty
private words; retained caller masters are outside this interval. -/
theorem joined_shape_of_high_empty (a : OuterData)
    (hempty : ∀ i : Fin 38,
      a.stacks (joinedPort (QueryProducerSpace.Native.producerPorts i)) = []) :
    ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs
        (fun j : Fin 256 => a.stacks (joinedPort (j.castAdd 38)))
        (QueryProducerSpace.Native.emptyHigh [])).stacks i := by
  intro i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · simp [QueryProducerSpace.Native.joinedState]
  · simp only [QueryProducerSpace.Native.joinedState, Fin.addCases_right]
    change a.stacks (joinedPort (QueryProducerSpace.Native.producerPorts j)) = _
    rw [hempty]
    fin_cases j <;> rfl

theorem projectInner_projectBase (s : OuterStore) :
    PerturbationAssembly.projectInner (projectBase s) = projectInner s := by
  funext i
  exact congrArg s (basePort_inner i)

theorem projectBase_update (s : OuterStore) (i : Fin 768) (word : List Bool) :
    projectBase (Function.update s (basePort i) word) = Function.update (projectBase s) i word := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [projectBase]
  · have hne : basePort j ≠ basePort i := fun h => hj (basePort_injective h)
    simp [projectBase, Function.comp_def, hj, hne]

theorem replaceBase_project (s : OuterStore) : replaceBase s (projectBase s) = s := by
  have h := embedState_project id basePort (⟨fun _ => false, s⟩ : OuterData)
    Function.injective_id basePort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceBase_update (s : OuterStore) (u : PerturbationAssembly.OuterStore)
    (i : Fin 768) (bits : List Bool) :
    replaceBase s (Function.update u i bits) = Function.update (replaceBase s u) (basePort i) bits :=
  ProgramLinking.extend_update basePort_injective _ _ _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Recover the native arithmetic invariants from the actual staged cache
words and an otherwise empty low workspace. No execution premise is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t} {s : Store}

theorem ArithmeticInput.pairReady (h : ArithmeticInput t a M cache s) :
    PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s (s 10) (fun _=>[]) := by
  constructor
  · intro j h8 h9
    fin_cases j <;>
      simp_all [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
        RingScan.serviceTapes,h.modulus,h.lowWidth,h.zero,h.table]
    all_goals exact h.clean _ (by decide) (by decide)
  · intro i
    fin_cases i <;>
      simp [SubexpConvolutionPair.lowPort,SubexpJetCellProgram.scalarPorts,
        DensePolynomialLoop.ready,DensePolynomialLoop.state,DensePolynomialLoop.stackArray,Fin.addCases,
        h.lowModulus,h.modulus,h.lowWidth]
    all_goals first
      | exact h.lowModulus.trans h.modulus
      | exact h.lowWidth
      | (apply h.clean <;> decide)

  · simp [h.fullZero]
  · simpa only [h.lowWidth] using h.width
  · exact h.degree
  · exact h.clean 120 (by decide) (by decide)
  · intro j hlo hhi
    apply h.clean j (by omega)
    intro hj
    simp only [arithmeticCachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with hj|hj|hj|hj|hj|hj|hj|hj|hj|hj <;> subst j <;> omega

theorem ArithmeticInput.scalarReady (h : ArithmeticInput t a M cache s) :
    HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s := by
  refine ⟨⟨h.clean 120 (by decide) (by decide),?_⟩,h.modulus,h.width,h.zero,h.table,h.degree⟩
  intro i
  fin_cases i <;>
    simp [ReconstructionProgram.RingAdapter.ports,ReconstructionProgram.RingAdapter.finalNative,
      ReconstructionProgram.RingAdapter.nativeStacks]
  all_goals exact h.clean _ (by decide) (by decide)

theorem ArithmeticInput.buffers (h : ArithmeticInput t a M cache s) :
    ∀ i,s (bufferPorts i)=[] := by
  intro i
  apply h.clean
  · fin_cases i <;> decide
  · fin_cases i <;> decide

private theorem lowScratch_not_arithmeticCachePorts :
    ∀ i : Fin 256, i∈lowScratch → i∉arithmeticCachePorts := by
  intro i hi ha
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  simp [arithmeticCachePorts] at ha
  omega

/-- The caller supplies the preserved masters and high-workspace emptiness;
the remaining native preconditions follow from the staged low cache words. -/
theorem LowInput.of_staged {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)}
    (h : ArithmeticInput t a M cache s)
    (hB : 0 < baseWidth 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzero : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
      List.replicate (d*baseWidth 3 t) false)
    (hrows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst))
    (hchoice : s 206=rows.map Prod.snd)
    (h207 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h208 : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (h209 : s 209=RingProgram.flat theta)
    (h210 : (s 210).length=N) (h211 : (s 211).length=d*baseWidth 3 t)
    (h212 : (s 212).length=rows.length) (h213 : s 213=List.replicate J true)
    (he : ∀ i∈lowScratch,205 ≤ i.val → s i=[]) :
    LowInput t a M cache J N theta rows s := by
  refine ⟨hB,hz,h.pairReady,h.scalarReady,h.buffers,
    h.clean 121 (by decide) (by decide),h.clean 122 (by decide) (by decide),hzero,
    hrows,hchoice,h207,h208,h209,h210,h211,h212,h213,h.fullZero,?_⟩
  intro i hi
  by_cases hl : i.val < 205
  · exact h.clean i hl (lowScratch_not_arithmeticCachePorts i hi)
  · exact he i hi (by omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One invariant of the physically staged masters yields every per-literal
low-worker precondition. No beta, shifted polynomial, or output table occurs
as an input hypothesis. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ArithmeticInput.frame_low {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {s u : Store} (h : ArithmeticInput t a M cache s)
    (hf : ∀ i:Fin 256,i.val < 205 → u i=s i) : ArithmeticInput t a M cache u := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf 194 (by decide)] using h.modulus
  · simpa only [hf 5 (by decide),hf 194 (by decide)] using h.lowModulus
  · simpa only [hf 202 (by decide)] using h.width
  · simpa only [hf 10 (by decide),hf 202 (by decide)] using h.lowWidth
  · simpa only [hf 203 (by decide)] using h.zero
  · simpa only [hf 201 (by decide)] using h.table
  · simpa only [hf 204 (by decide)] using h.degree
  · simpa only [hf 104 (by decide)] using h.fullZero
  · intro i hi hn
    exact (hf i hi).trans (h.clean i hi hn)

theorem FactorInput.lowInput {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : FactorRows t N (d:=d)} {s : OuterStore} {n : ℕ}
    (h : FactorInput t a M cache J N theta rows s n) (j : ℕ) (hj : j < n)
    (acc : List Bool) : LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (sourceWords (rows j)))) := by
  let u := literalSourceState (literalReady s (List.replicate j true) acc)
    j (sourceWords (rows j))
  have hf : ∀ i:Fin 256,i≠205 → i≠215 → i≠229 → i≠233 →
      projectInner u i=projectInner s i := by
    intro i h205 h215 h229 h233
    have hn : innerPort i≠545 ∧ innerPort i≠555 ∧ innerPort i≠569 ∧ innerPort i≠573 := by
      exact ⟨fun he=>h205 (innerPort_injective he),fun he=>h215 (innerPort_injective he),
        fun he=>h229 (innerPort_injective he),fun he=>h233 (innerPort_injective he)⟩
    simp [u,literalSourceState,literalReady,projectInner,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]
  have ha : ArithmeticInput t a M cache (projectInner u) := h.arithmetic.frame_low (by
    intro i hi
    apply hf i
    all_goals intro he; subst i; norm_num at hi)
  change LowInput t a M cache J N theta (rows j) (projectInner u)
  apply LowInput.of_staged ha h.widthPositive h.zeroCanonical h.zeroBits
  · simp [u,literalSourceState,projectInner,innerPort,sourceWords]
  · rw [hf 206 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.choices j hj
  · rw [hf 207 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.zeroWord
  · rw [hf 208 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.oneWord
  · rw [hf 209 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.thetaWord
  · rw [hf 210 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.sourceCount
  · rw [hf 211 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.wordWidth
  · rw [hf 212 (by decide) (by decide) (by decide) (by decide)]
    change (s 552).length=(rows j).length
    simp [h.ambientCount,h.rowsLength j hj]
  · rw [hf 213 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.targetCount
  · intro i hi hlarge
    have hn : i ≠ 205 ∧ i ≠ 215 ∧ i ≠ 229 ∧ i ≠ 233 := by
      simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
        coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
      omega
    exact (hf i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans (h.workEmpty i hi hlarge)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Common physical input invariant, independent of whichever exact source
arrays are returned by the next native source execution. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem pairChoice_rows {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).map Prod.fst=xs := by
  rw [←List.unzip_fst]
  exact congrArg Prod.fst (List.unzip_zip h)

theorem pairChoice_choices {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).map Prod.snd=choice := by
  rw [←List.unzip_snd]
  exact congrArg Prod.snd (List.unzip_zip h)

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J N : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterStore} {n : ℕ}

theorem StagedInput.factorInput (h : StagedInput t a M cache J N theta s n)
    (xs : List (Fixed.Array (baseWidth 3 t) d N)) (hx : xs.length=n) :
    FactorInput t a M cache J N theta (fun _=>pairChoice xs (s 546)) s n := by
  have hc : xs.length=(s 546).length := hx.trans h.choicesLength.symm
  refine ⟨h.arithmetic,h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,h.zeroWord,h.oneWord,
    h.thetaWord,h.sourceCount,h.wordWidth,h.ambientCount,h.targetCount,h.workEmpty⟩
  · intro j hj
    exact (pairChoice_length xs (s 546) hc).trans hx
  · intro j hj
    exact (pairChoice_choices xs (s 546) hc).symm

theorem StagedInput.rowInput (h : StagedInput t a M cache J N theta s n)
    (xs : List (Fixed.Array (baseWidth 3 t) d N)) (hx : xs.length=n)
    (j : ℕ) (hj : j < n) (acc : List Bool) :
    LowInput t a M cache J N theta (pairChoice xs (s 546))
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (Encoding.encodeList Fixed.encode xs))) := by
  have hh := (h.factorInput xs hx).lowInput j hj acc
  simpa only [sourceWords,pairChoice_rows xs (s 546) (hx.trans h.choicesLength.symm)] using hh

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem saved_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.saved a).stacks i = a.stacks i := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right hc]
  apply copyMany_frame
  intro p hp he
  have hm : p.2 ∈ SourceStaging.backupPorts := by
    simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> decide
  exact hb (he.symm ▸ hm)

theorem prepared_delta (a : Data) (he : a.stacks 365=[]) :
    (prepared a).stacks 365=[true] := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_same,
    copyMany_frame SourceControls.pairs _ 365 (by simp [SourceControls.pairs]),
    saved_frame a 365 (by decide) (by decide),he]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.controls_empty (h : Input p ps P a v N f S) :
    ∀ q ∈ SourceControls.pairs,a.stacks q.2=[] := by
  intro q hq
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.clean 21 (by decide)
  · exact h.clean 22 (by decide)
  · exact h.clean 26 (by decide)
  · exact h.clean 42 (by decide)
  · exact h.clean 43 (by decide)
  · exact h.clean 44 (by decide)
  · exact h.clean 45 (by decide)
  · exact h.clean 47 (by decide)
  · exact h.clean 48 (by decide)
  · exact h.clean 306 (by decide)
  · exact h.clean 308 (by decide)
  · exact h.clean 309 (by decide)
  · exact h.clean 310 (by decide)
  · exact h.clean 311 (by decide)
  · exact h.clean 312 (by decide)
  · exact h.clean 313 (by decide)
  · exact h.clean 314 (by decide)
  · exact h.clean 337 (by decide)
  · exact h.clean 249 (by decide)
  · exact h.clean 250 (by decide)
  · exact h.clean 251 (by decide)
  · exact h.clean 252 (by decide)

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeMaskDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed-length support-mask encoding and its executable inverse.
Words shorter than n are padded by false; longer words are truncated.
On length-n words these operations are mutually inverse. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_decodeMask (n : ℕ) (xs : List Bool) (h : xs.length = n) :
    encodeMask (decodeMask n xs) = xs := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [encodeMask, decodeMask, List.getElem?_eq_getElem hj]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadySize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Word bounds for the actual source preparation and full source initializer.
The bound explicitly includes the full (R+1)-coefficient zero array. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.prepared_bound (h : Input p ps P a v N f S) : WordBound S (prepared a) := by
  have hsave : WordBound S (SourceStaging.saved a) := by
    apply clearMany_wordBound
    exact copyMany_wordBound SourceStaging.savePairs a S (by decide)
      (by intro q hq
          simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
          rcases hq with rfl|rfl|rfl|rfl <;> exact h.backups _ (by decide))
      (by simp [SourceStaging.savePairs]) h.size
  have hs : ∀ q ∈ SourceControls.pairs,
      q.2 ∉ SourceStaging.cachePorts ∧ q.2 ∉ SourceStaging.backupPorts := by
    simp [SourceControls.pairs,SourceStaging.cachePorts,SourceStaging.backupPorts]
  have hcopy : WordBound S (copyManyState SourceControls.pairs (SourceStaging.saved a)) :=
    copyMany_wordBound SourceControls.pairs (SourceStaging.saved a) S (by decide)
      (by intro q hq
          rw [saved_frame a q.2 (hs q hq).1 (hs q hq).2]
          exact h.controls_empty q hq)
      (by simp [SourceControls.pairs]) hsave
  intro i
  by_cases hi : i=365
  · subst i
    rw [prepared_delta a (h.clean 25 (by decide))]
    simp only [List.length_cons,List.length_nil]
    have := h.countSize
    omega
  · simpa only [prepared,SourceControls.prepared,SourceControls.delta_stacks,
      Function.update_of_ne hi] using hcopy i

theorem Input.local_bound (h : Input p ps P a v N f S) (i : Fin 340) :
    (localStore a i).length ≤ S := h.prepared_bound (localPort i)

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical master words and ordinary scratch cleanliness imply every native
source precondition. The numerator uses the cleared 5/10 view; the executor
keeps the original arithmetic words. No source execution is a hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

/-- The two extra source-call word bounds used by the incidence assembly are
also consequences of the same actual byte-size bound. -/
theorem Input.call_bounds (h : Input p ps P a v N f S) :
    (Source.nativeStore a 21).length ≤ S ∧ (Source.nativeStore a 26).length ≤ S :=
  ⟨h.local_bound 21,h.local_bound 26⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

/-- The old source-row arithmetic input is exactly the low projection of
the relocated call state; its variable choices still have ambient length n. -/
theorem rowInput_at_call (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N n : ℕ) (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (s : FactorTableProgram.OuterStore)
    (h : StagedInput t model M cache J N theta (FactorTableProgram.projectBase s) n)
    (xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N))
    (hx : xs.length = n) (j : ℕ) (hj : j < n) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    LowInput t model M cache J N theta (pairChoice xs (s 546))
      (FactorTableProgram.projectInner
        (Function.update (sourceCallData s j acc regs).stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))) := by
  have hp : FactorTableProgram.projectBase
      (Function.update (sourceCallData s j acc regs).stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)) =
      literalSourceState
        (literalReady (FactorTableProgram.projectBase s) (List.replicate j true) acc)
        j (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs) := by
    change FactorTableProgram.projectBase
      (Function.update (Function.update
        (Function.update (Function.update s (FactorTableProgram.basePort 573)
          (List.replicate j true)) (FactorTableProgram.basePort 569) acc)
          (FactorTableProgram.basePort 555) (Encoding.encodeNat j))
          (FactorTableProgram.basePort 545) _) = _
    rw [FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update,
      FactorTableProgram.projectBase_update, FactorTableProgram.projectBase_update]
    rfl
  have hh := h.rowInput xs hx j hj acc
  rw [← hp, FactorTableProgram.projectInner_projectBase] at hh
  exact hh

/-- Actual SourceReady cleanliness supplies the immediate producer's high
scratch bank. The eight relocated source-local masters are outside this bank. -/
theorem source_high_empty {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S : ℕ)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (i : Fin 38) :
    a.stacks (FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i)) = [] := by
  let j : Fin 340 := ⟨256+i.val, by omega⟩
  have hj : j ∉ SourceReady.physicalLive := by
    intro hm
    simp only [SourceReady.physicalLive, List.mem_cons, List.mem_nil_iff, or_false,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hm
    dsimp only [j] at hm
    omega
  have he := h.clean j hj
  have hp : FactorTableProgram.basePort (SourceReady.localPort j) =
      FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i) := by
    rw [FactorTableProgram.basePort_low _ (by
      change 340+(256+i.val)<640
      have hi := i.isLt
      omega)]
    apply Fin.ext
    rfl
  change a.stacks (FactorTableProgram.basePort (SourceReady.localPort j)) = [] at he
  rwa [hp] at he

/-- The concrete native source program supplies its own row witness and full
source polynomial identity. No row oracle or execution is an input. -/
theorem native_source_run {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : FactorTableProgram.OuterData) (v n f S : ℕ)
    (h : SourceReady.Input p ps P (projectState id FactorTableProgram.basePort a) v n f S)
    (hv : v ≤ S) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rr : Fin 16 → Bool),
      rows.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f v
            (LayoutSourceRowsProgram.totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      k ≤ Source.nativeSourceWorkPolynomial p S + 1 ∧
      Eval (FactorTableProgram.liftBase Source.command) k a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : FactorTableProgram.OuterData) := by
  obtain ⟨rows,k,rr,hlen,hrows,hk,he⟩ := Source.native_command_bound p ps P
    (projectState id FactorTableProgram.basePort a) v n f S _ _ h.native h.size hv hn hf hplans
      h.call_bounds.1 h.call_bounds.2
  have hl := eval_liftCommand_from_state Source.command 0 0 id FactorTableProgram.basePort a
    Function.injective_id FactorTableProgram.basePort_injective he
  have ho : embedState id FactorTableProgram.basePort a
      (⟨rr, Function.update (projectState id FactorTableProgram.basePort a).stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : SourceReady.Data) =
      (⟨rr,Function.update a.stacks 545
        (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : FactorTableProgram.OuterData) := by
    apply SubexpScanPrimitives.state_ext
    · simp [embedState]
    · change FactorTableProgram.replaceBase a.stacks (Function.update (FactorTableProgram.projectBase a.stacks) 545 _) = _
      rw [FactorTableProgram.replaceBase_update, FactorTableProgram.replaceBase_project]
      rfl
  rw [ho] at hl
  exact ⟨rows,k+1,rr,hlen,hrows,Nat.add_le_add_right hk 1,hl⟩


/-- Source rows are generated on this invocation and immediately specialized
using the retained ambient mask. The only returned words are row serialization
545 and the already-specialized dictionary557 consumed by finishLiteral. -/
theorem lowPayload_native_run_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
    (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hmask : (s 857).length = n) (htmp : s 881 = []) :
    ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      let pairs := pairChoice xs (s 546)
      let source := QueryProducerSpace.emittedSource p.t p.model p.modulus p.cache
        J (p.R+1) theta pairs
      let result := MomentsProgram.Normalize.run 3 p.t p.modulus p.cache
        (HeadEvaluation.specializeEntries (Squarefree.decodeMask pairs.length (s 857)) source) []
      ∃ k rf, k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
          (7*n+5+FactorTableProgram.specializeBudget p.t d u J (p.R+1) pairs.length
            (1+pairs.length*(J-1)) (MomentsProgram.Product.bytes source).length
            (FactorTableProgram.projectInner
              (Function.update (sourceCallData s j acc regs).stacks 545
                (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs)))) ∧
        TruncatedRingProgram.Good ∅ u J result ∧
        Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
          (⟨rf,Function.update
            (Function.update (sourceCallData s j acc regs).stacks 545
              (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
            557 (MomentsProgram.Product.bytes result)⟩ : FactorTableProgram.OuterData) := by
  let a := sourceCallData s j acc regs
  obtain ⟨xs, ns, rs, hxs, hrows, hns, hes⟩ :=
    native_source_run p ps P a j n f S hsource (hj.le.trans hn) hn hf hplans
  let pairs := pairChoice xs (s 546)
  have hchoices : (s 546).length = n := hcommon.choicesLength
  have hpairs : pairs.length = n :=
    (pairChoice_length xs (s 546) (hxs.trans hchoices.symm)).trans hxs
  let words := Encoding.encodeList DensePolynomialProgram.Fixed.encode xs
  let b : FactorTableProgram.OuterData := ⟨rs, Function.update a.stacks 545 words⟩
  let low := FactorTableProgram.projectInner b.stacks
  have hin : LowInput p.t p.model p.modulus p.cache J (p.R+1) theta pairs low :=
    rowInput_at_call p.t p.model p.modulus p.cache J (p.R+1) n theta s hcommon xs hxs
      j hj acc regs
  have hz : low 217 = [] := by
    have he := hsource.clean 217 (by decide)
    change a.stacks (FactorTableProgram.basePort (SourceReady.localPort 217)) = [] at he
    have hport : FactorTableProgram.basePort (SourceReady.localPort (217 : Fin 340)) =
        FactorTableProgram.innerPort (217 : Fin 256) := by
      apply Fin.ext
      simp [FactorTableProgram.basePort, SourceReady.localPort, FactorTableProgram.innerPort]
    rw [hport] at he
    simpa only [low, b, FactorTableProgram.projectInner, Function.comp_apply,
      Function.update_of_ne (by decide : FactorTableProgram.innerPort (217 : Fin 256) ≠ 545)]
      using he
  have h857 : b.stacks 857 = s 857 := by
    simp [b, a, sourceCallData, FactorTableProgram.literalReady]
  have ht : b.stacks 881 = [] := by
    simp [b, a, sourceCallData, FactorTableProgram.literalReady, htmp]
  have hhigh (i : Fin 38) :
      b.stacks (FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i)) = [] := by
    have he := source_high_empty p ps P a j n f S hsource i
    have hne : FactorTableProgram.joinedPort (QueryProducerSpace.Native.producerPorts i) ≠ 545 := by
      intro hi
      have hv := congrArg Fin.val hi
      simp only [FactorTableProgram.joinedPort, QueryProducerSpace.Native.producerPorts,
        Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simpa only [b, Function.update_of_ne hne] using he
  have hshape := FactorTableProgram.joined_shape_of_high_empty b hhigh
  have hencode : b.stacks 857 =
      Squarefree.encodeMask (Squarefree.decodeMask pairs.length (s 857)) := by
    rw [h857, Squarefree.encodeMask_decodeMask pairs.length (s 857) (hmask.trans hpairs.symm)]
  obtain ⟨np, rp, hnp, hgood, hep⟩ :=
    FactorTableProgram.specializeCall_run p.t p.ht p.hd p.model p.modulus p.cache
      u J (p.R+1) hu hJ theta pairs b low hin hz
      (Squarefree.decodeMask pairs.length (s 857)) hencode ht hshape
  refine ⟨xs, hxs, hrows, ns+np, rp, ?_, hgood, hes.seq hep⟩
  rw [h857, hmask] at hnp
  exact Nat.add_le_add hns hnp


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.lowPayload_native_run_oai
