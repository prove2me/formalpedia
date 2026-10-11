-- Prove2me | solution 1 for IntMul.BankedProduct.banked_product
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T14:20:02.365608+00:00
-- url     : https://prove2.me/submissions/c257d3f2-6b46-4cac-aafc-00a6df73ee15

import Definitions.Def_IntMul_BankedProduct
import Mathlib.Tactic
import Theorems.Thm_IntMul_NormalizedProduct_normalized_product
import Theorems.Thm_IntMul_PreparedBankedCall_call_prepared

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.BankedProduct

private theorem native_markers (base : child.Cfg) (pre x y z l d : List Bool) :
    ∀ j, (NormalizedProduct.initialFrame base pre x y z l d).cells j 0=child.startSym := by
  intro j
  fin_cases j <;> simp [NormalizedProduct.initialFrame,FiniteCaller.embed,
    NormalizedProduct.productView,NormalizedProduct.productIncoming,FixedTapeExtension.embed,
    FixedTapeExtension.innerTape,NormalizedProduct.productBase,CarryProduct.initialFrame,
    CarryOutput.initialFrame,CarryOutput.batchView,CarryBatch.initialFrame,
    StreamCarryStep.initialFrame,StreamCarryStep.rootTape,StreamCarryStep.descriptorTape,
    MultitapeTM.tapeOf]
  all_goals rfl

private theorem native_output_head (base : child.Cfg) (pre x y z l d : List Bool) :
    (NormalizedProduct.finalFrame base pre x y z l d).head child.outTape=FixedOutputWidth.width d+1 := by
  simp [NormalizedProduct.finalFrame,MultitapeTM.outTape]

end IntMul.BankedProduct



namespace IntMul.BankedProduct

/-- Complete coefficient-based product recovery on writable banks, followed
by an actual physical return to global output, retaining the original caller
input and the exact terminal native bank frame. -/
private theorem banked_product (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : val l+1=CarryProduct.coefficientWidth (CarryStep.blockSize z) x y)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*CarryProduct.coefficientWidth (CarryStep.blockSize z) x y+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) := by
  obtain ⟨u,hu,heu,hhu,hpu⟩ := NormalizedProduct.normalized_product nativeBase pre x y z l d hl hd
  have out : (child.step^[u] (NormalizedProduct.initialFrame nativeBase pre x y z l d)).cells child.outTape=
      child.tapeOf ((bin (FixedOutputWidth.width d) (val x*val y)).map child.bitSym) := by
    rw [hd]
    convert hpu using 1 <;> rfl
  obtain ⟨t,ht,het,hht,hout,hinput,hhead,hprefix⟩ := PreparedBankedCall.call_prepared child base
    (NormalizedProduct.initialFrame nativeBase pre x y z l d) u
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

end IntMul.BankedProduct



open IntMul IntMul.BankedProduct

theorem solution (base : machine.Cfg) (nativeBase : child.Cfg)
    (pre x y z l d : List Bool)
    (hl : val l+1=CarryProduct.coefficientWidth (CarryStep.blockSize z) x y)
    (hd : FixedOutputWidth.width d=x.length+y.length) :
    ∃ t : ℕ,
      t ≤ (DigitConvolution.blockCount (CarryStep.blockSize z) x+
        DigitConvolution.blockCount (CarryStep.blockSize z) y)*
        (41*CarryProduct.coefficientWidth (CarryStep.blockSize z) x y+32*CarryStep.blockSize z+
          21*z.length+4*l.length+126)+12*FixedOutputWidth.width d+6*d.length+67 ∧
      machine.step^[t] (initialFrame base nativeBase pre x y z l d)=finalFrame base nativeBase pre x y z l d ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.outTape=
        machine.tapeOf ((bin (x.length+y.length) (val x*val y)).map machine.bitSym) ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells machine.inTape=base.cells machine.inTape ∧
      (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).head machine.inTape=base.head machine.inTape ∧
      (∀ j, (machine.step^[t] (initialFrame base nativeBase pre x y z l d)).cells (BankedSimulation.workTape child j) 0=
        base.cells (BankedSimulation.workTape child j) 0) :=
  IntMul.BankedProduct.banked_product base nativeBase pre x y z l d hl hd

#print axioms solution
