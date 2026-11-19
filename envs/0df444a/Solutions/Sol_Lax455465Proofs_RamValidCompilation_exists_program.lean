-- Prove2me | solution 1 for Lax455465Proofs.RamValidCompilation.exists_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:40.692205+00:00
-- url     : https://prove2.me/submissions/bc183325-a129-4554-b1bb-60e69a9d5c23

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax808846Proofs_Simulation_compileProgram_runsTo
import Theorems.Thm_Lax455465Proofs_RamValidFlowCut_exists_program_native

namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
namespace Lax109476Proofs.BinaryOptimization
end Lax109476Proofs.BinaryOptimization
namespace Lax109476Proofs.BinaryOptimizationBounds
end Lax109476Proofs.BinaryOptimizationBounds
namespace Lax109476Proofs.CertificateSystems
end Lax109476Proofs.CertificateSystems
namespace Lax109476Proofs.CoordinateOptimization
end Lax109476Proofs.CoordinateOptimization
namespace Lax109476Proofs.DeterminantBounds
end Lax109476Proofs.DeterminantBounds
namespace Lax109476Proofs.EllipsoidDeterminant
end Lax109476Proofs.EllipsoidDeterminant
namespace Lax109476Proofs.EllipsoidTermination
end Lax109476Proofs.EllipsoidTermination
namespace Lax109476Proofs.IterationBudget
end Lax109476Proofs.IterationBudget
namespace Lax109476Proofs.LexicographicBounds
end Lax109476Proofs.LexicographicBounds
namespace Lax109476Proofs.PointRecovery
end Lax109476Proofs.PointRecovery
namespace Lax109476Proofs.RamEllipsoidStoredBounds
end Lax109476Proofs.RamEllipsoidStoredBounds
namespace Lax109476Proofs.RamEllipsoidWordBounds
end Lax109476Proofs.RamEllipsoidWordBounds
namespace Lax109476Proofs.RamFrame
end Lax109476Proofs.RamFrame
namespace Lax109476Proofs.RamPadEntries
end Lax109476Proofs.RamPadEntries
namespace Lax109476Proofs.RamPrimitiveBounds
end Lax109476Proofs.RamPrimitiveBounds
namespace Lax109476Proofs.RamRecoveryData
end Lax109476Proofs.RamRecoveryData
namespace Lax109476Proofs.RamScalarFrame
end Lax109476Proofs.RamScalarFrame
namespace Lax109476Proofs.RationalFeasibility
end Lax109476Proofs.RationalFeasibility
namespace Lax109476Proofs.RationalMinima
end Lax109476Proofs.RationalMinima
namespace Lax109476Proofs.SmallFeasiblePoint
end Lax109476Proofs.SmallFeasiblePoint
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
namespace Lax263307Proofs.ConditioningDistribution
end Lax263307Proofs.ConditioningDistribution
namespace Lax263307Proofs.EntropyDecrease
end Lax263307Proofs.EntropyDecrease
namespace Lax263307Proofs.NativeDistanceEntries
end Lax263307Proofs.NativeDistanceEntries
namespace Lax263307Proofs.NativeMachineSegment
end Lax263307Proofs.NativeMachineSegment
namespace Lax263307Proofs.NativeUniformWordGuards
end Lax263307Proofs.NativeUniformWordGuards
namespace Lax455465.ShortPathFlow
end Lax455465.ShortPathFlow
namespace Lax455465Proofs.AcyclicFlowPath
end Lax455465Proofs.AcyclicFlowPath
namespace Lax455465Proofs.LargePotentialData
end Lax455465Proofs.LargePotentialData
namespace Lax455465Proofs.PathSubtraction
end Lax455465Proofs.PathSubtraction
namespace Lax455465Proofs.RamFlowData
end Lax455465Proofs.RamFlowData
namespace Lax455465Proofs.RationalParser
end Lax455465Proofs.RationalParser
namespace Lax455465Proofs.RegionHistory
end Lax455465Proofs.RegionHistory
namespace Lax455465Proofs.RegionInterval
end Lax455465Proofs.RegionInterval
namespace Lax455465Proofs.RegionRuntimeState
end Lax455465Proofs.RegionRuntimeState
namespace Lax455465Proofs.RoundingConstants
end Lax455465Proofs.RoundingConstants
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
namespace Lax759944Proofs.Legacy.RamPolytime
end Lax759944Proofs.Legacy.RamPolytime
namespace Lax808846.RamComputes
end Lax808846.RamComputes
namespace Lax808846Proofs.Machine
end Lax808846Proofs.Machine

namespace Lax455465Proofs.RamValidFlowCut
end Lax455465Proofs.RamValidFlowCut
theorem Lax455465Proofs.RamValidFlowCut.exists_program:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
  @Polynomial Nat Nat.instSemiring) (sourceTime:@Polynomial Nat Nat.instSemiring),
  ∀ {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
    (@Eq Lax455465.ProductNetwork.EdgeKind kind Lax455465.ProductNetwork.EdgeKind.undirected→
        @Lax455465.ProductNetwork.Network.IsUndirected n (@Lax455465.RationalEncoding.RationalInstance.network n I))→
      LE.le ((2:Nat))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I))→
        ∀ (W:Nat),
          LE.le
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) wordBound)
              W→
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) W)
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And
                  (@Eq (List Nat) σ.inp
                    (@List.cons Nat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@Lax455465.RationalEncoding.encodeInput n kind I)))
                  (And
                    (LE.le (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (@List.length Nat (σ.arrs "input.data")))
                    (And
                      (LT.lt
                        (HMul.hMul
                          ((2:Nat)) n)
                        (@List.length Nat (σ.arrs "flow.weights")))
                      (And
                        (LT.lt
                          (HMul.hMul
                            ((2:Nat))
                            (HMul.hMul n n))
                          (@List.length Nat (σ.arrs "flow.capacities")))
                        (And
                          (LT.lt (Lax455465Proofs.RamFlowLp.wordLength n)
                            (@List.length Nat (σ.arrs "lp.word")))
                          (And
                            (LT.lt
                              (@List.length Nat
                                (@Lax109476.RationalEncoding.encodeProgram
                                  (HAdd.hAdd
                                    (HMul.hMul n n)
                                    (HMul.hMul
                                      ((2:Nat))
                                      (HMul.hMul
                                        (HMul.hMul n n) n)))
                                  (HAdd.hAdd
                                    ((1:Nat))
                                    (HMul.hMul
                                      (HMul.hMul n n)
                                      (HMul.hMul n n)))
                                  (@Lax455465Proofs.DirectedFlowLP.program n I)))
                              (@List.length Nat (σ.arrs "vm.input")))
                            (And
                              (LT.lt
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (Lax759944.BinaryWordEncoding.bitSize
                                    (@Lax109476.RationalEncoding.encodeProgram
                                      (HAdd.hAdd
                                        (HMul.hMul n n)
                                        (HMul.hMul
                                          ((2:Nat))
                                          (HMul.hMul
                                            (HMul.hMul n n) n)))
                                      (HAdd.hAdd
                                        ((1:Nat))
                                        (HMul.hMul
                                          (HMul.hMul n n)
                                          (HMul.hMul n n)))
                                      (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                  sourceTime)
                                (@List.length Nat (σ.arrs "vm.addresses")))
                              (And
                                (LT.lt
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (Lax759944.BinaryWordEncoding.bitSize
                                      (@Lax109476.RationalEncoding.encodeProgram
                                        (HAdd.hAdd
                                          (HMul.hMul n n)
                                          (HMul.hMul
                                            ((2:Nat))
                                            (HMul.hMul
                                              (HMul.hMul n n) n)))
                                        (HAdd.hAdd
                                          ((1:Nat))
                                          (HMul.hMul
                                            (HMul.hMul n n)
                                            (HMul.hMul n n)))
                                        (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                    sourceTime)
                                  (@List.length Nat (σ.arrs "vm.values")))
                                (And
                                  (LT.lt
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (Lax759944.BinaryWordEncoding.bitSize
                                        (@Lax109476.RationalEncoding.encodeProgram
                                          (HAdd.hAdd
                                            (HMul.hMul n n)
                                            (HMul.hMul
                                              ((2:Nat))
                                              (HMul.hMul
                                                (HMul.hMul n n) n)))
                                          (HAdd.hAdd
                                            ((1:Nat))
                                            (HMul.hMul
                                              (HMul.hMul n n)
                                              (HMul.hMul n n)))
                                          (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                      sourceTime)
                                    (@List.length Nat (σ.arrs "vm.output")))
                                  (And
                                    (LT.lt
                                      (HMul.hMul
                                        ((2:Nat))
                                        (Lax455465Proofs.RamFlowData.columns n))
                                      (@List.length Nat (σ.arrs "flow.primal")))
                                    (And
                                      (LT.lt
                                        (HMul.hMul
                                          ((2:Nat))
                                          (Lax455465Proofs.RamFlowData.rows n))
                                        (@List.length Nat (σ.arrs "flow.dual")))
                                      (And
                                        (LT.lt
                                          (HMul.hMul
                                            ((2:Nat))
                                            (HMul.hMul n n))
                                          (@List.length Nat (σ.arrs "metric.old")))
                                        (And
                                          (LT.lt
                                            (HMul.hMul
                                              ((2:Nat))
                                              (HMul.hMul n n))
                                            (@List.length Nat (σ.arrs "metric.new")))
                                          (And
                                            (Lax455465Proofs.RamRegionInvariant.Room n
                                              (@Lax455465Proofs.RamRoundingInit.support n
                                                (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                              σ)
                                            (And (Lax455465Proofs.RamRegionCut.Room n σ)
                                              (And
                                                (LT.lt
                                                  (HMul.hMul
                                                    ((2:Nat))
                                                    (Lax455465Proofs.RamFlowData.columns n))
                                                  (@List.length Nat (σ.arrs "flow.converted")))
                                                (@Eq (List Nat) σ.out (@List.nil Nat))))))))))))))))))
              c
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                ∃ (certificate:Lax455465.FlowCutCertificate.Certificate n),
                  And
                    (@Lax455465.FlowCutCertificate.IsValid n kind I
                      (@OfNat.ofNat Real (nat_lit 512)
                        (@instOfNatAtLeastTwo Real (nat_lit 512) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat ((511:Nat))
                            (@Nat.instNeZeroSucc ((510:Nat))))))
                      certificate)
                    (@Eq (List Nat) τ.out (@Lax455465.FlowCutCertificate.encodeCertificate n certificate)))
              (@Polynomial.eval Nat Nat.instSemiring
                (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) timeBound):= @Lax455465Proofs.RamValidFlowCut.exists_program_native

section

namespace Lax808846Proofs.Imp

@[simp] theorem Bop.apply_add (m n:ℕ):Bop.add.apply m n=m + n:=rfl
@[simp] theorem Bop.apply_sub (m n:ℕ):Bop.sub.apply m n=m - n:=rfl
@[simp] theorem Bop.apply_mul (m n:ℕ):Bop.mul.apply m n=m * n:=rfl
@[simp] theorem Bop.apply_div (m n:ℕ):Bop.div.apply m n=m / n:=rfl
@[simp] theorem Bop.apply_and (m n:ℕ):Bop.and.apply m n=Nat.land m n:=rfl
@[simp] theorem Bop.apply_or (m n:ℕ):Bop.or.apply m n=Nat.lor m n:=rfl
@[simp] theorem Bop.apply_xor (m n:ℕ):Bop.xor.apply m n=Nat.xor m n:=rfl
@[simp] theorem Bop.apply_shiftl (m n:ℕ):Bop.shiftl.apply m n=m * 2 ^ n:=rfl
@[simp] theorem Bop.apply_shiftr (m n:ℕ):Bop.shiftr.apply m n=m / 2 ^ n:=rfl

@[simp] theorem Expr.add_def (e f:Expr):Expr.add e f=.bin .add e f:=rfl
@[simp] theorem Expr.sub_def (e f:Expr):Expr.sub e f=.bin .sub e f:=rfl
@[simp] theorem Expr.mul_def (e f:Expr):Expr.mul e f=.bin .mul e f:=rfl
@[simp] theorem Expr.div_def (e f:Expr):Expr.div e f=.bin .div e f:=rfl
@[simp] theorem Expr.and_def (e f:Expr):Expr.and e f=.bin .and e f:=rfl
@[simp] theorem Expr.or_def (e f:Expr):Expr.or e f=.bin .or e f:=rfl
@[simp] theorem Expr.xor_def (e f:Expr):Expr.xor e f=.bin .xor e f:=rfl
@[simp] theorem Expr.shiftl_def (e f:Expr):Expr.shiftl e f=.bin .shiftl e f:=rfl
@[simp] theorem Expr.shiftr_def (e f:Expr):Expr.shiftr e f=.bin .shiftr e f:=rfl

def Expr.eval:Expr→ Env→ Option ℕ
  | lit n,_ => some n
  | var x,σ => some (σ.vars x)
  | get a i,σ => (i.eval σ).bind fun k => (σ.arrs a)[k]?
  | bin op e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => op.apply m n

def Cond.eval:Cond→ Env→ Option Bool
  | eq e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n
  | lt e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n)

inductive BigStep:Com→ Env→ Env→ ℕ→ Prop

  | skip {σ:Env}:BigStep .skip σ σ 1

  | assign {σ:Env} {x:String} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.assign x e) σ (σ.setVar x v) (1 + e.size)

  | store {σ:Env} {a:String} {i e:Expr} {k v:ℕ}
      (hi:i.eval σ=some k) (he:e.eval σ=some v)
      (hk:k < (σ.arrs a).length):
      BigStep (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)

  | seq {c d:Com} {σ σ' σ'':Env} {k k':ℕ}:
      BigStep c σ σ' k→ BigStep d σ' σ'' k'→
      BigStep (.seq c d) σ σ'' (k + k')

  | ite_true {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | ite_false {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some false) (hd:BigStep d σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | while_true {b:Cond} {c:Com} {σ σ' σ'':Env} {k k':ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k)
      (hw:BigStep (.while b c) σ' σ'' k'):
      BigStep (.while b c) σ σ'' (1 + b.size + k + k')

  | while_false {b:Cond} {c:Com} {σ:Env} (hb:b.eval σ=some false):
      BigStep (.while b c) σ σ (1 + b.size)

  | read {σ:Env} {x:String} {v:ℕ} {rest:List ℕ} (h:σ.inp=v::rest):
      BigStep (.read x) σ { σ.setVar x v with inp:=rest } 1

  | write {σ:Env} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

@[simp] theorem vars_setVar (σ:Env) (x:String) (v:ℕ) (y:String):
    (σ.setVar x v).vars y=if y=x then v else σ.vars y:=rfl

@[simp] theorem arrs_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).arrs=σ.arrs:=rfl

@[simp] theorem inp_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).inp=σ.inp:=rfl

@[simp] theorem out_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).out=σ.out:=rfl

@[simp] theorem vars_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).vars=σ.vars:=rfl

@[simp] theorem arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    (σ.setArr a i v).arrs b=if b=a then (σ.arrs a).set i v else σ.arrs b:=rfl

@[simp] theorem inp_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).inp=σ.inp:=rfl

@[simp] theorem out_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).out=σ.out:=rfl

@[simp] theorem size_lit (n:ℕ):(Expr.lit n).size=1:=rfl
@[simp] theorem size_var (x:String):(Expr.var x).size=1:=rfl
@[simp] theorem size_get (a:String) (i:Expr):(Expr.get a i).size=i.size + 1:=rfl
@[simp] theorem size_bin (op:Bop) (e f:Expr):
    (Expr.bin op e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_add (e f:Expr):(Expr.add e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_sub (e f:Expr):(Expr.sub e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_mul (e f:Expr):(Expr.mul e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_div (e f:Expr):(Expr.div e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_and (e f:Expr):(Expr.and e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_or (e f:Expr):(Expr.or e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_xor (e f:Expr):(Expr.xor e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftl (e f:Expr):(Expr.shiftl e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftr (e f:Expr):(Expr.shiftr e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condEq (e f:Expr):(Cond.eq e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condLt (e f:Expr):(Cond.lt e f).size=e.size + f.size + 1:=rfl

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Transfer

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning

theorem fitsWords_of_max_le {L:Layout} {B w:ℕ} (h1:1 < B)
    (h:max B (L.span B)≤ 2 ^ w):L.FitsWords B w:=
  ⟨h1,le_trans (le_max_left _ _) h,le_trans (le_max_right _ _) h⟩

end Lax808846Proofs.Transfer

end

section

namespace Lax455465Proofs.RamTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

def layoutAllowance (L:Layout):ℕ:=
  L.temps + 2 + L.scalars.length + L.arrays.length + 1

theorem layout_fits {L:Layout} {v w:ℕ} (hv:0 < v)
    (hw:v + layoutAllowance L≤ w):L.FitsWords (2 ^ v) w:=by
  have hB:1 < 2 ^ v:=Nat.one_lt_pow (ne_of_gt hv) (by decide)
  have hc:layoutAllowance L≤ 2 ^ layoutAllowance L:=Nat.lt_two_pow_self.le
  have hs:max (2 ^ v) (L.span (2 ^ v))≤ 2 ^ (v + layoutAllowance L):=by
    rw [pow_add]
    apply max_le
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · unfold Layout.span
      have hp:1≤ 2 ^ v:=hB.le
      calc
        _≤ (L.temps + 2 + L.scalars.length) * 2 ^ v + L.arrays.length * 2 ^ v:=by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hp) _
        _≤ layoutAllowance L * 2 ^ v:=by unfold layoutAllowance; nlinarith
        _≤ _:=by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ v) hc
  exact fitsWords_of_max_le hB (hs.trans (Nat.pow_le_pow_right (by decide) hw))

end Lax455465Proofs.RamTransfer

end

section

namespace Lax455465Proofs.RamAutomaticLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile

def expressionNames:Expr→ List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old:=expressionNames i; (old.1,a::old.2)
  | .bin _ e f => let a:=expressionNames e; let b:=expressionNames f; (a.1 ++ b.1,a.2 ++ b.2)

def conditionNames (b:Cond):List String × List String:=expressionNames (condExpr b)

def commandNames:Com→ List String × List String
  | .skip => ([], [])
  | .assign x e => let a:=expressionNames e; (x::a.1,a.2)
  | .store x i e => let a:=expressionNames i; let b:=expressionNames e; (a.1 ++ b.1,x::(a.2 ++ b.2))
  | .seq c d => let a:=commandNames c; let b:=commandNames d; (a.1 ++ b.1,a.2 ++ b.2)
  | .ite b c d => let a:=conditionNames b; let x:=commandNames c; let y:=commandNames d;
      (a.1 ++ x.1 ++ y.1,a.2 ++ x.2 ++ y.2)
  | .while b c => let a:=conditionNames b; let x:=commandNames c; (a.1 ++ x.1,a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def commandDepth:Com→ ℕ
  | .skip | .read _ => 1
  | .assign _ e | .write e => e.size + 2
  | .store _ i e => max i.size e.size + 2
  | .seq c d => max (commandDepth c) (commandDepth d)
  | .ite b c d => max (condExpr b).size (max (commandDepth c) (commandDepth d)) + 2
  | .while b c => max (condExpr b).size (commandDepth c) + 2

def layout (c:Com):Layout:= ⟨(commandNames c).1, (commandNames c).2,commandDepth c + 2⟩

theorem expression_ok (e:Expr) (L:Layout) (d:ℕ)
    (hv:(expressionNames e).1 ⊆ L.scalars) (ha:(expressionNames e).2 ⊆ L.arrays)
    (hd:d + e.size < L.temps):Expr.Ok L e d:=by
  induction e generalizing d with
  | lit v => trivial
  | var x => exact hv (by simp [expressionNames])
  | get a i ih =>
    refine ⟨ha (by simp [expressionNames]),ih d
      (by simpa [expressionNames] using hv)
      (fun x hx => ha (by simp [expressionNames,hx])) ?_, ?_⟩
    all_goals simp only [Expr.size] at hd; omega
  | bin op e f ihe ihf =>
    have hve:(expressionNames e).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hvf:(expressionNames f).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hae:(expressionNames e).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    have haf:(expressionNames f).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    simp only [Expr.Ok]
    exact ⟨ihf d hvf haf (by simp only [Expr.size] at hd; omega),
      ihe (d + 1) hve hae (by simp only [Expr.size] at hd; omega),
      by simp only [Expr.size] at hd; omega⟩

theorem command_ok (c:Com) (L:Layout)
    (hv:(commandNames c).1 ⊆ L.scalars) (ha:(commandNames c).2 ⊆ L.arrays)
    (hd:commandDepth c < L.temps):Com.Ok L c:=by
  induction c with
  | skip => trivial
  | read x => exact hv (by simp [commandNames])
  | assign x e =>
    refine ⟨hv (by simp [commandNames]),expression_ok e L 0
      (fun x hx => hv (by simp [commandNames,hx])) (by simpa [commandNames] using ha) ?_⟩
    simp only [commandDepth] at hd; omega
  | store a i e =>
    refine ⟨ha (by simp [commandNames]),expression_ok i L 0
      (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      expression_ok e L 1 (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | write e =>
    refine ⟨expression_ok e L 0 hv ha ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | seq c d ihc ihd =>
    refine ⟨ihc (fun x hx => hv (by simp [commandNames,hx]))
      (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | ite b c d ihc ihd =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ihc (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | «while» b c ih =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ih (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega

theorem layout_ok (c:Com):Com.Ok (layout c) c:=
  command_ok c (layout c) (fun _ h => h) (fun _ h => h) (by simp [layout])

end Lax455465Proofs.RamAutomaticLayout

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

end Lax455465Proofs.WordSize

end

section

open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

abbrev PathFlow (n:ℕ):=List (Fin n)→₀ ℝ≥0

end Lax455465.ConcurrentFlow

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

noncomputable def FlowCertificate.flow {n:ℕ} (certificate:FlowCertificate n):
    PathFlow n:=
  certificate.paths.foldl
    (fun F record => F + Finsupp.single record.1 (record.2:ℝ≥0)) 0

end Lax455465.RationalEncoding

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamValidCompilation
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding RamFlowData

def extent {n:ℕ} (TB:Polynomial ℕ) (kind:EdgeKind) (I:RationalInstance n):ℕ:=
  (encodeInput kind I).length+RamFlowLp.wordLength n+
    (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)).length+
    TB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (DirectedFlowLP.program I)))+
    2*n+2*(n*n)+2*columns n+2*rows n+
    ((RamRegionInvariant.extents n (RamRoundingInit.support I.weight)).map Prod.snd).sum+1

theorem room {n:ℕ} (TB:Polynomial ℕ) (kind:EdgeKind) (I:RationalInstance n):
    RamRegionInvariant.Room n (RamRoundingInit.support I.weight)
      (initEnv (fun _ => extent TB kind I) ((encodeInput kind I).length::encodeInput kind I)):=by
  intro a count hc
  have hmem:count∈ (RamRegionInvariant.extents n (RamRoundingInit.support I.weight)).map Prod.snd:=
    List.mem_map.mpr ⟨(a,count),hc,rfl⟩
  have hs:=List.single_le_sum (fun x hx => Nat.zero_le x) count hmem
  simp only [initEnv,List.length_replicate]
  dsimp [extent]
  omega

theorem input_fits (xs:List ℕ) (v:ℕ) (hv:bitSize xs+1≤ v):
    ∀ a∈xs.length::xs,a < 2^v:=by
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · have hlen:=WordSize.length_le xs
    exact (show xs.length < 2^(bitSize xs+1) from lt_of_le_of_lt hlen
      (by have:=Nat.lt_two_pow_self (n:=bitSize xs+1); omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hv)
  · exact (WordSize.member_bound xs a ha).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

set_option maxHeartbeats 0 in

theorem exists_program:
    ∃ (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ),
      ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),
        (kind=.undirected→ I.network.IsUndirected)→ 2≤ supportCount I.weights→
        ∃ certificate:Lax455465.FlowCutCertificate.Certificate n,
          Lax455465.FlowCutCertificate.IsValid kind I 512 certificate∧
          ∀ W:ℕ,WB.eval (bitSize (encodeInput kind I))≤ W→
            ∃ t≤ TB.eval (bitSize (encodeInput kind I)),
              Lax808846.Ram.RunsTo W p ((encodeInput kind I).length::encodeInput kind I)
                (Lax455465.FlowCutCertificate.encodeCertificate certificate) t:=by
  obtain ⟨c,T,WB,sourceTime,hcorrect⟩:=RamValidFlowCut.exists_program
  let layout:=_root_.Lax455465Proofs.RamAutomaticLayout.layout c
  refine ⟨compileProgram layout c,WB+Polynomial.X+Polynomial.C (2+RamTransfer.layoutAllowance layout),
    Polynomial.C layout.const*T+1,?_⟩
  intro n kind I hsym hp
  let L:=bitSize (encodeInput kind I)
  let v:=WB.eval L+L+2
  let σ:=initEnv (fun _ => extent sourceTime kind I) ((encodeInput kind I).length::encodeInput kind I)
  have hE:=room sourceTime kind I
  have hcut:RamRegionCut.Room n σ:=by
    constructor
    · intro a ha
      simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
    · simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
    · simp only [σ,initEnv,List.length_replicate]
      dsimp [extent]
      omega
  have hrun:=hcorrect kind I hsym hp v (by dsimp [v,L]; omega)
  obtain ⟨τ,rr,cert,hvalid,hout⟩:=hrun σ (by
    refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hE,hcut,?_,rfl⟩
    all_goals simp only [σ,initEnv,List.length_replicate]; dsimp [extent]; omega)
  refine ⟨cert,hvalid,?_⟩
  intro W hW
  have hv:0 < v:=by dsimp [v]; omega
  have hfit:v+RamTransfer.layoutAllowance layout≤ W:=by
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,v,L,Nat.add_assoc] using hW
  obtain ⟨k,hk,hbs⟩:=rr
  obtain ⟨t,ht,hr⟩:=Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hfit) (RamAutomaticLayout.layout_ok c)
    (input_fits (encodeInput kind I) v (by dsimp [v,L]; omega)) hbs
  refine ⟨t,?_,by simpa only [hout] using hr⟩
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one] using
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left layout.const hk) 1)

end Lax455465Proofs.RamValidCompilation

end

theorem solution:∃ (p:Lax808846.Ram.Program) (WB:Polynomial ℕ) (TB:Polynomial ℕ),
  ∀ {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
    (kind=Lax455465.ProductNetwork.EdgeKind.undirected→ I.network.IsUndirected)→
      2≤ Lax455465.ProductNetwork.supportCount I.weights→
        ∃ (certificate:Lax455465.FlowCutCertificate.Certificate n),
          Lax455465.FlowCutCertificate.IsValid kind I 512 certificate∧
            ∀ (W:ℕ),
              Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                    WB≤
                  W→
                ∃
                  t≤
                    Polynomial.eval
                      (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I)) TB,
                  Lax808846.Ram.RunsTo W p
                    ((Lax455465.RationalEncoding.encodeInput kind I).length::
                      Lax455465.RationalEncoding.encodeInput kind I)
                    (Lax455465.FlowCutCertificate.encodeCertificate certificate) t:= @Lax455465Proofs.RamValidCompilation.exists_program
