-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:39:11.825858+00:00
-- url     : https://prove2.me/submissions/6ea341a3-25de-48d9-bf49-135a8fcd1878

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Native_program_correct
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_reconstructionBudget_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- An explicit polynomial upper bound for the fully native trace. -/
theorem nativeMulBudget_polynomial (J degree B : ℕ) :
    nativeMulBudget J degree B ≤ 100000 * (J+1)^3 * (degree+1)^3 * (B+1)^2 := by
  unfold nativeMulBudget mulBudget convolutionBudget outerCost Pair.budget
    RingCall.budget RingScan.serviceMulBudget RingTriple.expandBudget Cell.eventBudget Cell.addBudget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.SubexpLiftRing

theorem localBudget_le_uniform (S nodes index e t J Km Ka Kp Kap W V : ℕ)
    (hn : nodes ≤ S) (hi : index ≤ S) (he : e ≤ S) (ht : t ≤ S) (hJ : J ≤ S)
    (hm : Km ≤ S) (ha : Ka ≤ S) (hp : Kp ≤ S) (hap : Kap ≤ S)
    (hw : W ≤ S) (hv : V ≤ S) :
    localBudget nodes index e t J Km Ka Kp Kap W V ≤ 10000*(S+1)^3 := by
  calc
    _ ≤ localBudget S S S S S S S S S S S := by
      unfold localBudget initializationBudget includeBudget preparationBudget
        inverseConstantsBudget inverseBudget correctionBudget
      gcongr
    _ ≤ _ := by
      unfold localBudget initializationBudget includeBudget preparationBudget
        inverseConstantsBudget inverseBudget correctionBudget
      ring_nf
      omega

namespace Native

/-- A deliberately coarse uniform polynomial bound in every runtime size. -/
theorem budget_polynomial (S nodes index q t d J : ℕ)
    (hn : nodes ≤ S) (hi : index ≤ S) (hq : q ≤ S)
    (ht : t ≤ S) (hd : d ≤ S) (hJ : J ≤ S) :
    budget nodes index q t d J ≤ 10000*1000001^3*(S+1)^24 := by
  let T := S+1
  let K := 1000000*T^8
  have hT : 0 < T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have h18 : T ≤ T^8 := by simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 8 by decide)
  have h28 : T^2 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h38 : T^3 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h48 : T^4 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h58 : T^5 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have h08 : 1 ≤ T^8 := by simpa only [pow_zero] using Nat.pow_le_pow_right hT (show 0 ≤ 8 by decide)
  have hlog : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hB : baseWidth 3 t ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hB1 : baseWidth 3 t+1 ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hd1 : d+1 ≤ T := by dsimp [T]; omega
  have hJ1 : J+1 ≤ T := by dsimp [T]; omega
  have hdT : d ≤ T := hd.trans hS
  have hJT : J ≤ T := hJ.trans hS
  have hKm : HornerProgram.Services.mulBudget (baseWidth 3 t) d ≤ K := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.mulBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKa : HornerProgram.Services.addBudget (baseWidth 3 t) d ≤ K := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.addBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKp : DensePolynomialProgram.nativeMulBudget J d (baseWidth 3 t) ≤ K := by
    calc
      _ ≤ 100000*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2 := DensePolynomialProgram.nativeMulBudget_polynomial _ _ _
      _ ≤ 100000*T^3*T^3*(2*T)^2 := by gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hKap : DensePolynomialProgram.AddService.budget d (baseWidth 3 t) J J ≤ K := by
    calc
      _ ≤ 7000*(T*(T+T)+1)*(2*T)^2+1+13*T*(2*T)*(T+T)+16 := by
        unfold DensePolynomialProgram.AddService.budget
        gcongr
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hW : d*baseWidth 3 t ≤ K := by
    calc
      _ ≤ T*(2*T) := Nat.mul_le_mul hdT hB
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hV : J*(d*baseWidth 3 t) ≤ K := by
    calc
      _ ≤ T*(T*(2*T)) := Nat.mul_le_mul hJT (Nat.mul_le_mul hdT hB)
      _ ≤ K := by dsimp [K]; ring_nf; omega
  have hSK : S ≤ K := by dsimp [K]; omega
  have hmain := localBudget_le_uniform K nodes index (q-2) t J
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (DensePolynomialProgram.nativeMulBudget J d (baseWidth 3 t))
    (DensePolynomialProgram.AddService.budget d (baseWidth 3 t) J J)
    (d*baseWidth 3 t) (J*(d*baseWidth 3 t))
    (hn.trans hSK) (hi.trans hSK) (by omega) (ht.trans hSK) (hJ.trans hSK)
    hKm hKa hKp hKap hW hV
  change budget nodes index q t d J ≤ _ at hmain
  calc
    _ ≤ 10000*(K+1)^3 := hmain
    _ ≤ 10000*(1000001*T^8)^3 := by gcongr; dsimp [K]; omega
    _ = _ := by dsimp [T]; ring

end Native
end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramPolynomialCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform polynomial bound on the complete primitive CRT program. The
residue-field cardinality is a runtime dimension, as are all tape widths. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native
open SubexponentialSAT.SubexpLiftRing

private theorem entry_le (S modulusBits widthTokens : ℕ)
    (hm : modulusBits ≤ S) (hw : widthTokens ≤ S) :
    Entry.budget modulusBits widthTokens ≤ 24*(S+1) := by
  unfold Entry.budget
  omega

private theorem controller_polynomial (S Q J t d : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S)
    (hq : 3^d ≤ S) :
    controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d) + 1 ≤
      2300*((costConstant+1)^4*(S+1)^96)+1 := by
  let T := S+1
  let U := costConstant*T^24
  have hT : 0 < T := by dsimp [T]; omega
  have hS : S ≤ T := by dsimp [T]; omega
  have h124 : T ≤ T^24 := by simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 24 by decide)
  have h224 : T^2 ≤ T^24 := Nat.pow_le_pow_right hT (by decide)
  have h524 : T^5 ≤ T^24 := Nat.pow_le_pow_right hT (by decide)
  have h024 : 1 ≤ T^24 := by simpa only [pow_zero] using Nat.pow_le_pow_right hT (show 0 ≤ 24 by decide)
  have hC : 200000 ≤ costConstant := by
    rw [costConstant]
    exact (show 200000 ≤ 1000000 by decide).trans
      (Nat.le_add_left 1000000 (10000*1000001^3))
  have hC1 : 1 ≤ costConstant := (show 1 ≤ 200000 by decide).trans hC
  have hSU : S ≤ U := by
    calc
      S ≤ T^24 := hS.trans h124
      _ = 1*T^24 := by simp
      _ ≤ U := Nat.mul_le_mul_right _ hC1
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  have hB : baseWidth 3 t ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hB1 : baseWidth 3 t+1 ≤ 2*T := by norm_num [baseWidth, hlog]; dsimp [T]; omega
  have hd1 : d+1 ≤ T := by dsimp [T]; omega
  have hW : d*baseWidth 3 t ≤ U := by
    calc
      _ ≤ T*(2*T) := Nat.mul_le_mul (hd.trans hS) hB
      _ = 2*T^2 := by ring
      _ ≤ U := Nat.mul_le_mul ((show 2 ≤ 200000 by decide).trans hC) h224
  have hmul : HornerProgram.Services.mulBudget (baseWidth 3 t) d ≤ U := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.mulBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ = 200000*T^5 := by ring
      _ ≤ U := Nat.mul_le_mul hC h524
  have hadd : HornerProgram.Services.addBudget (baseWidth 3 t) d ≤ U := by
    calc
      _ ≤ 50000*(d+1)^3*(baseWidth 3 t+1)^2 := HornerProgram.Services.addBudget_polynomial _ _
      _ ≤ 50000*T^3*(2*T)^2 := by gcongr
      _ = 200000*T^5 := by ring
      _ ≤ U := Nat.mul_le_mul hC h524
  have hlocal : CRTLocalProgram.Native.budget Q Q (3^d) t d J ≤ U := by
    calc
      _ ≤ 10000*1000001^3*(S+1)^24 := CRTLocalProgram.Native.budget_polynomial S Q Q (3^d) t d J
        hQ hQ hq ht hd hJ
      _ ≤ U := Nat.mul_le_mul_right _ (by
        rw [costConstant]
        exact Nat.le_add_right (10000*1000001^3) 1000000)
  have hmain := reconstructionBudget_le Q J (d*baseWidth 3 t)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (CRTLocalProgram.Native.budget Q Q (3^d) t d J) U
    (hQ.trans hSU) (hJ.trans hSU) hW hmul hadd hlocal
  have hU1 : U+1 ≤ (costConstant+1)*T^24 := by
    calc
      U+1 ≤ U+T^24 := Nat.add_le_add_left h024 U
      _ = _ := by dsimp [U]; ring
  have hpow : (U+1)^4 ≤ (costConstant+1)^4*T^96 := by
    calc
      _ ≤ ((costConstant+1)*T^24)^4 := Nat.pow_le_pow_left hU1 4
      _ = _ := by ring
  have hctrl := hmain.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2300 hpow) 1)
  simpa only [T, middleBudget] using hctrl

theorem budget_polynomial (S Q J t d modulusBits widthTokens : ℕ)
    (hQ : Q ≤ S) (hJ : J ≤ S) (ht : t ≤ S) (hd : d ≤ S)
    (hq : 3^d ≤ S) (hm : modulusBits ≤ S) (hw : widthTokens ≤ S) :
    budget Q J t d modulusBits widthTokens + 1 ≤
      2400*(costConstant+1)^4*(S+1)^96+1 := by
  let T := S+1
  have hT : 0 < T := by dsimp [T]; omega
  have h196 : T ≤ T^96 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hT (show 1 ≤ 96 by decide)
  have hCpow : 1 ≤ (costConstant+1)^4 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right
      (Nat.succ_pos costConstant) (show 0 ≤ 4 by decide)
  have hscale : 24 ≤ 100*(costConstant+1)^4 :=
    (show 24 ≤ 100 by decide).trans (Nat.mul_le_mul_left 100 hCpow)
  have hentry : Entry.budget modulusBits widthTokens ≤ 24*T :=
    entry_le S modulusBits widthTokens hm hw
  have hentry' : Entry.budget modulusBits widthTokens ≤
      100*(costConstant+1)^4*T^96 :=
    hentry.trans (Nat.mul_le_mul hscale h196)
  have hctrl := controller_polynomial S Q J t d hQ hJ ht hd hq
  calc
    budget Q J t d modulusBits widthTokens + 1 =
        Entry.budget modulusBits widthTokens +
          (controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d) + 1) := by
      unfold budget
      exact Nat.add_assoc _ _ _
    _ ≤ 100*(costConstant+1)^4*T^96 + (2300*((costConstant+1)^4*T^96)+1) :=
      Nat.add_le_add hentry' hctrl
    _ = 2400*(costConstant+1)^4*(S+1)^96+1 := by dsimp [T]; ring

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

/-- Correct Hasse jets give the actual residue output, with all-prefix local
workspace bounded by the fixed-degree polynomial native runtime. -/
theorem reconstruct_run_space_oai (t : ℕ) (ht : 0 < t) {d Q : ℕ} [NeZero Q] (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → ReconstructionProgram.Native.Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : ReconstructionProgram.Native.Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (ReconstructionProgram.NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ ReconstructionProgram.NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t)
    (hdistinct : Function.Injective (fun i => a.rho t ht
      ((RingProgram.modelRing t ht hd a M cache).decode (nodes i))))
    (target : Polynomial (a.O t)) (hdegree : target.natDegree < Q*J)
    (htargetJets : Reconstruction.HasJets (RingProgram.modelRing t ht hd a M cache)
      nodes J (fun i => (jets i).1) target)
    (S : ℕ) (hQsize : Q ≤ S) (hJsize : J ≤ S) (htsize : t ≤ S)
    (hdsize : d ≤ S) (hqsize : 3^d ≤ S)
    (hmodsize : (input.stacks 194).length ≤ S)
    (hwidthsize : (input.stacks 202).length ≤ S)
    (count m n : ℕ) (hcount : count ≤ m*2^n) (hlarge : m*2^n < 3^t)
    (htarget : target.eval 0 = (count : a.O t)) :
    ∃ (b : ReconstructionProgram.Native.Coeff t d) (rf : Fin 16 → Bool) (steps : ℕ),
      steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 ∧
      Trace ReconstructionProgram.Native.program steps (input.withPC (some ReconstructionProgram.Native.program.entry))
        ((⟨rf, Function.update (ReconstructionProgram.Entry.prepared input.stacks) 261
          (RingProgram.flat b)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode b = (count : a.O t) ∧
      a.decodeCount t ht ((RingProgram.modelRing t ht hd a M cache).decode b) = count ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace ReconstructionProgram.Native.program prefixSteps (input.withPC (some ReconstructionProgram.Native.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          stackBits input.stacks + (2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1) := by
  obtain ⟨b, rf, ⟨steps, hsteps, htrace⟩, hvalue, hdecode⟩ :=
    ReconstructionProgram.Native.program_correct t ht hd a M cache hcanon hzbits J hJpos hB nodes jets
      minusOne hminus input hscalar scalarWidth frame hpoly hclean hzero hone hneg
      hJ hnodes hjets hexponent hprecision hdistinct target hdegree htargetJets
      count m n hcount hlarge htarget
  have hbudget : steps ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1 :=
    hsteps.trans (ReconstructionProgram.Native.budget_polynomial S Q J t d (input.stacks 194).length
      (input.stacks 202).length hQsize hJsize htsize hdsize hqsize hmodsize hwidthsize)
  refine ⟨b, rf, steps, hbudget, htrace, hvalue, hdecode, ?_⟩
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _
    (steps := 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96+1) (by rfl)
    prefixSteps intermediate (hprefix.trans hbudget) hp


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space_oai
