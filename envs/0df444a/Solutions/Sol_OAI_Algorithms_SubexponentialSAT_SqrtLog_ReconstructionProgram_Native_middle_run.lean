-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:20:33.037001+00:00
-- url     : https://prove2.me/submissions/21d012ad-bb2a-4e69-8a27-84aa52e64f6a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_Native_command_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_LocalValue_corrected_denote
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Middle_iteration_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static native arithmetic readiness, independent of the final service
composition. The two polynomial caches do not participate in readiness. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod
variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))


omit [Fact (Nat.Prime p)] in
/-- Readiness only inspects native arithmetic ports; the two protected
polynomial caches may vary while the native arithmetic frame is retained. -/
theorem BaseReady.frame_except_caches {base s : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (hf : ∀ i : Fin 256, i.val < 205 → i ≠ 192 → i ≠ 193 → s i = base i) :
    BaseReady p t M cache table s scalarWidth frame := by
  constructor
  · intro i h8 h9
    have hp : (RingCall.ports i).val < 205 ∧ RingCall.ports i ≠ 192 ∧ RingCall.ports i ≠ 193 := by
      exact (by decide : ∀ j : Fin 32, (RingCall.ports j).val < 205 ∧
        RingCall.ports j ≠ 192 ∧ RingCall.ports j ≠ 193) i
    rw [hf _ hp.1 hp.2.1 hp.2.2]
    exact H.high i h8 h9
  · intro i
    have hp : (SubexponentialSAT.SubexpConvolutionPair.lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)).val < 20 := i.isLt
    rw [hf _ (by omega) (by intro he; rw [he] at hp; norm_num at hp)
      (by intro he; rw [he] at hp; norm_num at hp)]
    exact H.low i
  · rw [hf 104 (by decide) (by decide) (by decide)]; exact H.width
  · exact H.scalarWidthLength
  · rw [hf 204 (by decide) (by decide) (by decide)]; exact H.degreeLength
  · rw [hf 120 (by decide) (by decide) (by decide)]; exact H.scratch
  · intro i hlo hhi
    rw [hf i (by omega) (by intro he; subst i; norm_num at hhi)
      (by intro he; subst i; norm_num at hhi)]
    exact H.work i hlo hhi

omit [Fact (Nat.Prime p)] in
theorem BaseReady.update_cache {base : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (i : Fin 256) (hi : i = 192 ∨ i = 193) (bits : List Bool) :
    BaseReady p t M cache table (Function.update base i bits) scalarWidth frame := by
  apply BaseReady.frame_except_caches p t M cache table H
  intro j _ h192 h193
  rcases hi with rfl | rfl
  · exact Function.update_of_ne h192 _ _
  · exact Function.update_of_ne h193 _ _


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fully discharged native binary services for arbitrary coefficient-vector
length. Shared by Horner, local CRT and dense polynomial services. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram.Services

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (ServiceSpec)

/-- The prepared polynomial zero and unary length caches are caller-owned. -/
theorem NativeReady.update_polynomial_caches {p t : ℕ} [Fact p.Prime]
    {M : SubexpPreparedQuartic.Modulus p t} {cache : RingProgram.ScalarCache p t}
    {d : ℕ} {table : Fin d → Fin d → Fin d → Word (baseWidth p t)}
    {base : Store} (h : NativeReady p t M cache table base) (zero count : List Bool) :
    NativeReady p t M cache table
      (Function.update (Function.update base 192 zero) 193 count) := by
  apply h.frame_except_low_caches
  intro i hi h192 h193
  simp [h192, h193]

end SubexponentialSAT.SqrtLog.HornerProgram.Services

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramModelMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual model-specific native Hermite iteration. Every arithmetic
service and every local correction trace is discharged here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

theorem middle_run_oai (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (_hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne acc : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (processed remaining : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (input.stacks ∘ localPorts) scalarWidth frame)
    (hbuffers : ∀ j, input.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [])
    (hclean : ∀ j ∈ Middle.cleanPorts, input.stacks j = [])
    (hlocalClean : ∀ j ∈ CRTLocalProgram.localWork, input.stacks (localPorts j) = [])
    (hzero : input.stacks 104 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hnode : input.stacks 213 = RingProgram.flat (nodes i))
    (hnodes : input.stacks 214 = (List.ofFn nodes).flatMap RingProgram.flat)
    (hindex : (input.stacks 216).length = i.val)
    (hjet : input.stacks 225 = Fixed.encode (jets i))
    (hJ : input.stacks 243 = List.replicate J true)
    (hr : input.stacks 257 = (remaining.map nodes).flatMap RingProgram.flat)
    (hp : input.stacks 258 = (processed.map nodes).flatMap RingProgram.flat)
    (hx : input.stacks 259 = RingProgram.flat (nodes i))
    (hacc : input.stacks 261 = RingProgram.flat acc)
    (h277 : input.stacks 277 = DensePolynomialProgram.encode
      (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    ∃ n ≤ Middle.budget Q J (d*baseWidth 3 t)
        (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
        (HornerProgram.Services.addBudget (baseWidth 3 t) d)
        (CRTLocalProgram.Native.budget Q i.val (3^d) t d J), ∃ rf b,
      Eval middle n input ⟨rf, Function.update input.stacks 261 (RingProgram.flat b)⟩ ∧
      (RingProgram.modelRing t ht hd a M cache).decode b =
        (RingProgram.modelRing t ht hd a M cache).decode acc + term t ht hd a M cache nodes J jets i := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let s := input.stacks ∘ localPorts
  let prepared := (Local.prepared input).stacks ∘ localPorts
  have hprep : prepared = Function.update (Function.update s 192 (input.stacks 277))
      193 (input.stacks 243) := by
    funext j
    have hj : localPorts j = (192 : Fin 320) ↔ j = 192 := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun k : Fin 320 => k.val) h
      · rintro rfl; rfl
    have hj' : localPorts j = (193 : Fin 320) ↔ j = 193 := by
      constructor
      · intro h; apply Fin.ext; exact congrArg (fun k : Fin 320 => k.val) h
      · rintro rfl; rfl
    simp [prepared, s, Local.prepared, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks,
      Function.comp_def, Function.update_apply, hj, hj',
      hclean 192 (by simp [Middle.cleanPorts]), hclean 193 (by simp [Middle.cleanPorts])]
  have hscalar' : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) prepared := by
    rw [hprep]
    exact hscalar.update_polynomial_caches _ _
  have hpoly' : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      prepared scalarWidth frame := by
    rw [hprep]
    exact PairSpec.BaseReady.update_cache 3 t M cache (HornerProgram.modelTable t a M cache)
      (PairSpec.BaseReady.update_cache 3 t M cache (HornerProgram.modelTable t a M cache)
        hpoly 192 (Or.inl rfl) _) 193 (Or.inr rfl) _
  have hlocal : ∀ j ∈ CRTLocalProgram.localWork, prepared j = [] := by
    intro j hj
    have h192 : j ≠ (192 : Fin 256) := by intro he; subst j; simp [CRTLocalProgram.localWork] at hj
    have h193 : j ≠ (193 : Fin 256) := by intro he; subst j; simp [CRTLocalProgram.localWork] at hj
    simpa [hprep, s, localPorts, h192, h193] using hlocalClean j hj
  have hb : ∀ j, prepared (SubexpConvolutionControl.bufferPorts j) = [] := by
    intro j
    have h192 : SubexpConvolutionControl.bufferPorts j ≠ (192 : Fin 256) := by fin_cases j <;> decide
    have h193 : SubexpConvolutionControl.bufferPorts j ≠ (193 : Fin 256) := by fin_cases j <;> decide
    simpa [hprep, s, localPorts, h192, h193] using hbuffers j
  obtain ⟨c, rest, hhead, hrun⟩ := CRTLocalProgram.Native.command_run t ht hd a M cache hcanon
    prepared J (3^d) hJpos hB hscalar' scalarWidth frame hpoly' hb minusOne (nodes i)
    (List.ofFn nodes) (jets i)
    (by simpa [hprep, s, localPorts] using hzero)
    (by simpa [hprep, s, localPorts] using hone)
    (by simpa [hprep, s, localPorts] using hneg)
    (by simpa [hprep, s, localPorts] using hnode)
    (by simpa [hprep, s, localPorts] using hnodes)
    (by simpa [hprep, s, localPorts] using hjet)
    (by simpa [hprep, s, localPorts] using hJ)
    (by simp [hprep, hJ]) (by simp [hprep, h277])
    (by simpa [hprep, s, localPorts] using hexponent)
    (by simpa [hprep, s, localPorts] using hprecision) hlocal
  have hidx : (prepared 216).length = i.val := by simpa [hprep, s, localPorts] using hindex
  simp only [List.length_ofFn, hidx] at hrun hhead
  change (LocalValue.factorCode ops minusOne nodes J i).1 = c :: rest at hhead
  let correction := CRTLocalProgram.Model.corrected ops minusOne c (3^d) t
    (LocalValue.factorCode ops minusOne nodes J i) (jets i)
  change SubexpConvolutionControl.ExecutesIn localCode
      (CRTLocalProgram.Native.budget Q i.val (3^d) t d J) prepared
      (Function.update prepared 244 (List.map RingProgram.flat
        (CRTLocalProgram.Model.corrected ops minusOne c (3^d) t
          (LocalValue.factorCode ops minusOne nodes J i) (jets i)).1).flatten) at hrun
  have hrun' : SubexpConvolutionControl.ExecutesIn localCode
      (CRTLocalProgram.Native.budget Q i.val (3^d) t d J) prepared
      (Function.update prepared 244 (HornerProgram.encodePolynomial RingProgram.flat correction.1)) := by
    dsimp only [correction]
    simpa only [localCode, CRTLocalProgram.Native.command, Fixed.encode,
      DensePolynomialProgram.encode, HornerProgram.encodePolynomial,
      List.flatMap_def] using hrun
  have hdenote := LocalValue.corrected_denote ops minusOne hminus nodes (3^d) t J jets i c rest hhead
  have hscalarMul := HornerProgram.Services.multiply_spec 3 t M cache hcanon
    (HornerProgram.modelTable t a M cache) s hscalar
  have hscalarAdd := HornerProgram.Services.add_spec 3 t M cache
    (HornerProgram.modelTable t a M cache) s hscalar
  apply Middle.iteration_run RingProgram.flat ops.decode localCode HornerProgram.Services.multiply
    HornerProgram.Services.add (CRTLocalProgram.Model.scalarMul ops) (CRTLocalProgram.Model.scalarAdd ops)
    _ _ _ _ J input nodes remaining processed i hfull ops.oneRun.1 minusOne ops.zeroRun.1 acc
    hscalarMul hscalarAdd ops.mul_correct ops.add_correct ops.one_correct hminus ops.zero_correct
    RingProgram.flat_length (Nat.mul_pos hd hB) hr hp hone hneg hzero hx hacc hJ
    (by simp [h277, DensePolynomialProgram.encode, RingProgram.flat_length]) hclean
    correction.1 correction.2 _ hdenote hrun'

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run_oai
