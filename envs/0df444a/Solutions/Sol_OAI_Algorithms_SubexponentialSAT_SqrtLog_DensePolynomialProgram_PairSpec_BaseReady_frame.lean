-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady.frame
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:41:16.036394+00:00
-- url     : https://prove2.me/submissions/5c016181-a7a1-4864-9082-d8a831b8d263

import Mathlib
import Definitions.Def_OAIQ081S119

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
theorem BaseReady.frame_oai {base s : Store}
    {scalarWidth : List Bool} {frame : Fin 6 → List Bool}
    (H : BaseReady p t M cache table base scalarWidth frame)
    (hf : CRTLocalProgram.LowFrame base s) :
    BaseReady p t M cache table s scalarWidth frame :=
  BaseReady.frame_except_caches p t M cache table H (fun i hi _ _ => hf i hi)


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady.frame_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady.frame_oai
