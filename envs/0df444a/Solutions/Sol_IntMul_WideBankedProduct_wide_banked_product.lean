-- Prove2me | solution 1 for IntMul.WideBankedProduct.wide_banked_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T16:34:00.609401+00:00
-- url     : https://prove2.me/submissions/e89c6173-ccc0-450b-83ab-51c805ecf68b

import Definitions.Def_IntMul_WideBankedProduct
import Mathlib.Tactic
import Theorems.Thm_IntMul_WideNormalizedProduct_wide_normalized_product
import Theorems.Thm_IntMul_PreparedBankedCall_call_prepared

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.WideBankedProduct

private theorem native_markers (base : child.Cfg) (pre x y z l d : List Bool) :
    ∀ j, (WideNormalizedProduct.initialFrame base pre x y z l d).cells j 0=child.startSym := by
  intro j
  fin_cases j <;> simp [WideNormalizedProduct.initialFrame,FiniteCaller.embed,
    WideNormalizedProduct.productView,WideNormalizedProduct.productIncoming,FixedTapeExtension.embed,
    FixedTapeExtension.innerTape,WideNormalizedProduct.productBase,CarryProduct.initialFrame,
    CarryOutput.initialFrame,CarryOutput.batchView,CarryBatch.initialFrame,
    StreamCarryStep.initialFrame,StreamCarryStep.rootTape,StreamCarryStep.descriptorTape,
    MultitapeTM.tapeOf]
  all_goals rfl

private theorem native_output_head (base : child.Cfg) (pre x y z l d : List Bool) :
    (WideNormalizedProduct.finalFrame base pre x y z l d).head child.outTape=FixedOutputWidth.width d+1 := by
  simp [WideNormalizedProduct.finalFrame,MultitapeTM.outTape]

end IntMul.WideBankedProduct



namespace IntMul.WideBankedProduct

/-- Complete coefficient-based product recovery on writable banks, followed
by an actual physical return to global output, retaining the original caller
input and the exact terminal native bank frame. -/
private theorem wide_banked_product (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) := by
  obtain ⟨u,hu,heu,hhu,hpu⟩ := WideNormalizedProduct.wide_normalized_product nativeBase pre x y z l d hl hd
  have out : (child.step^[u] (WideNormalizedProduct.initialFrame nativeBase pre x y z l d)).cells child.outTape=
      child.tapeOf ((bin (FixedOutputWidth.width d) (val x*val y)).map child.bitSym) := by
    rw [hd]
    convert hpu using 1 <;> rfl
  obtain ⟨t,ht,het,hht,hout,hinput,hhead,hprefix⟩ := PreparedBankedCall.call_prepared child base
    (WideNormalizedProduct.initialFrame nativeBase pre x y z l d) u
    (native_markers nativeBase pre x y z l d) hhu
    (bin (FixedOutputWidth.width d) (val x*val y)) out
  rw [heu] at het ht
  have he : machine.step^[t] (initialFrame base nativeBase pre x y z l d)=
      finalFrame base nativeBase pre x y z l d := het
  refine ⟨t,?_,he,hht,?_,hinput,hhead,hprefix⟩
  · rw [native_output_head] at ht
    simp only [bin,List.length_ofFn] at ht
    omega
  · rw [hd] at hout
    convert hout using 1 <;> rfl

end IntMul.WideBankedProduct



open IntMul IntMul.WideBankedProduct

theorem solution (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : CarryProduct.coefficientWidth (CarryStep.blockSize z) x y≤ val l+1)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*(val l+1)+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) :=
  IntMul.WideBankedProduct.wide_banked_product base nativeBase pre x y z l d hl hd

#print axioms solution
