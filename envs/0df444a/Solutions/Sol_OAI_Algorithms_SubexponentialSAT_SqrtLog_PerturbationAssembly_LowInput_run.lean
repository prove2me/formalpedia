-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:02:15.943173+00:00
-- url     : https://prove2.me/submissions/aff92b14-fc8a-44c3-8221-58d506471a6d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_initializeTarget_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_native_scan_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_origin_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationBetaProgram_betaCommand_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
namespace Counter
open SubexponentialSAT.SubexpLinearFactorProgram
theorem paddedBits_length (D W : ℕ) (low high : List Bool)
    (hlow : low.length = W) (hhigh : high.length = W) :
    (paddedBits W low high D).length = D * W := by
  cases D with
  | zero => simp [paddedBits]
  | succ D =>
      cases D with
      | zero => simpa [paddedBits] using hlow
      | succ n => simp [paddedBits, hlow, hhigh]; ring

end Counter
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpPolynomialConstructor

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The constructor's bit string is precisely a padded coefficient array. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

private theorem encode_replicate {B degree : ℕ} (z : Coeff B degree)
    (hz : RingProgram.flat z = List.replicate (degree*B) false) (n : ℕ) :
    encode (List.replicate n z) = List.replicate (n*(degree*B)) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,encode_cons,hz,ih,← List.replicate_add]
      congr 1
      ring

theorem encode_coefficients {B degree : ℕ} (zero low high : Coeff B degree)
    (hz : RingProgram.flat zero = List.replicate (degree*B) false) (J : ℕ) :
    encode (coefficients zero low high J) =
      Counter.paddedBits (degree*B) (RingProgram.flat low) (RingProgram.flat high) J := by
  cases J with
  | zero => rfl
  | succ J =>
      cases J with
      | zero => simp [coefficients,Counter.paddedBits]
      | succ n => simp [coefficients,Counter.paddedBits,encode_replicate zero hz n,List.append_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-length array instantiation of the local Hermite algebra. The
constructor and head split are exact identities of physical bit strings. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram.Model
open Polynomial
open SubexponentialSAT.SubexpSymbolicCost
open DensePolynomialProgram

theorem padded_encode {B d : ℕ} (z low high : Coeff B d)
    (hz : RingProgram.flat z = List.replicate (d*B) false) (J : ℕ) :
    Fixed.encode (padded z low high J) =
      Constructor.Counter.paddedBits (d*B) (RingProgram.flat low) (RingProgram.flat high) J :=
  Constructor.encode_coefficients z low high hz J

end SubexponentialSAT.SqrtLog.CRTLocalProgram.Model

end OAI.Algorithms
end

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


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor
open DensePolynomialProgram (Coeff)
open DensePolynomialProgram.Constructor

theorem restoreCache_run (s : Store) (dst backup : Fin 256)
    (hdb : backup≠dst) (hd : dst≠245) (hb : backup≠245)
    (h245 : s 245=[]) :
    ExecutesIn (restoreCache dst backup)
      (2*(s dst).length+6*(s backup).length+9) s
      (Function.update (Function.update s backup []) dst (s backup)) := by
  have h1 := clear_run dst s
  have h2 := move_run (Function.update s dst []) backup dst hb hd hdb
    (by simpa [Ne.symm hd] using h245) (by simp)
  have hout : Function.update (Function.update (Function.update s dst []) backup []) dst
      ((Function.update s dst []) backup) =
      Function.update (Function.update s backup []) dst (s backup) := by
    funext i
    by_cases hi : i=dst <;> by_cases hj : i=backup <;>
      simp [hi,hj,hdb]
  rw [hout] at h2
  have h := h1.seq h2
  have hbackup : (Function.update s dst [] backup).length = (s backup).length := by
    rw [Function.update_noteq hdb]
  have hcost : 2*(s dst).length+6*(s backup).length+9 =
      (2*(s dst).length+3)+(6*(Function.update s dst [] backup).length+6) := by
    rw [hbackup]
    omega
  rw [hcost]
  exact h

/-- Bit-level point construction agrees with the fixed-array model. -/
theorem point_bits {B d : ℕ} (z one theta : Coeff B d)
    (hz : RingProgram.flat z=List.replicate (d*B) false) (J : ℕ) :
    Counter.paddedBits (d*B) (RingProgram.flat theta) (RingProgram.flat one) J =
      DensePolynomialProgram.Fixed.encode (CRTLocalProgram.Model.linear z one theta J) :=
  (CRTLocalProgram.Model.padded_encode z theta one hz J).symm

theorem zero_coefficients {C : Type*} (z : C) (J : ℕ) :
    DensePolynomialProgram.Constructor.coefficients z z z J=List.replicate J z := by
  cases J with
  | zero => rfl
  | succ J => cases J <;> simp [DensePolynomialProgram.Constructor.coefficients,List.replicate_succ]

theorem zero_bits {B d : ℕ} (z : Coeff B d)
    (hz : RingProgram.flat z=List.replicate (d*B) false) (J : ℕ) :
    Counter.paddedBits (d*B) (RingProgram.flat z) (RingProgram.flat z) J =
      DensePolynomialProgram.Fixed.encode (CRTLocalProgram.Model.zero z J) := by
  rw [← DensePolynomialProgram.Constructor.encode_coefficients z z z hz J,zero_coefficients]
  rfl

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

theorem finishTarget_run (s : Store) (h245 : s 245=[]) :
    ExecutesIn finishTarget
      (2*((s 192).length+(s 193).length+(s 243).length+(s 247).length+(s 254).length)+
        6*((s 236).length+(s 237).length+(s 238).length)+33)
      s (finishedTarget s) := by
  let s1 := Function.update (Function.update s 236 []) 192 (s 236)
  let s2 := Function.update (Function.update s1 237 []) 193 (s 237)
  let s3 := Function.update (Function.update s2 238 []) 243 (s 238)
  let s4 := Function.update s3 247 []
  have h1 : ExecutesIn (restoreCache 192 236)
      (2*(s 192).length+6*(s 236).length+9) s s1 :=
    restoreCache_run s 192 236 (by decide) (by decide) (by decide) h245
  have h2 : ExecutesIn (restoreCache 193 237)
      (2*(s 193).length+6*(s 237).length+9) s1 s2 := by
    simpa [s2,s1] using restoreCache_run s1 193 237
      (by decide) (by decide) (by decide) (by simp [s1,h245])
  have h3 : ExecutesIn (restoreCache 243 238)
      (2*(s 243).length+6*(s 238).length+9) s2 s3 := by
    simpa [s3,s2,s1] using restoreCache_run s2 243 238
      (by decide) (by decide) (by decide) (by simp [s2,s1,h245])
  have h4 : ExecutesIn (clear 247) (2*(s 247).length+3) s3 s4 := by
    simpa [s4,s3,s2,s1] using clear_run 247 s3
  have h5 : ExecutesIn (clear 254) (2*(s 254).length+3) s4 (finishedTarget s) := by
    simpa [finishedTarget,s4,s3,s2,s1] using clear_run 254 s4
  have hcost : (2 * (s 192).length + 6 * (s 236).length + 9) +
      ((2 * (s 193).length + 6 * (s 237).length + 9) +
        ((2 * (s 243).length + 6 * (s 238).length + 9) +
          ((2 * (s 247).length + 3) + (2 * (s 254).length + 3)))) =
      2 * ((s 192).length + (s 193).length + (s 243).length +
        (s 247).length + (s 254).length) +
        6 * ((s 236).length + (s 237).length + (s 238).length) + 33 := by omega
  rw [← hcost]
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))



theorem targetState_frame (s : Store) (J W : ℕ) (i : Fin 256)
    (hi : i.val < 205) (h192 : i≠192) (h193 : i≠193) :
    targetState s J W i=s i := by
  have h236 : i≠236 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h237 : i≠237 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h238 : i≠238 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h243 : i≠243 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h247 : i≠247 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  have h254 : i≠254 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  simp [targetState,h192,h193,h236,h237,h238,h243,h247,h254]

/-- The dictionary may change while the temporary caches are live. Restoring
those caches preserves precisely that completed dictionary. -/
theorem target_restore_dictionary (s : Store) (J W : ℕ) (output : List Bool)
    (he : ∀ i∈targetScratch,s i=[]) :
    finishedTarget (Function.update (targetState s J W) 217 output)=
      Function.update s 217 output := by
  funext i
  by_cases h192 : i=192
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h193 : i=193
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h217 : i=217
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h236 : i=236
  · subst i
    simp [finishedTarget,targetState,he 236 (by simp [targetScratch])

]
  by_cases h237 : i=237
  · subst i
    simp [finishedTarget,targetState,
      he 237 (by simp [targetScratch])
]
  by_cases h238 : i=238
  · subst i
    simp [finishedTarget,targetState,
he 238 (by simp [targetScratch])
]
  by_cases h243 : i=243
  · subst i
    simp [finishedTarget,targetState

]
  by_cases h247 : i=247
  · subst i
    simp [finishedTarget,targetState,

      he 247 (by simp [targetScratch])]
  by_cases h254 : i=254
  · subst i
    simp [finishedTarget,targetState,

he 254 (by simp [targetScratch])]
  simp [finishedTarget,targetState,h192,h193,h217,h236,h237,h238,h243,h247,h254]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed low-variable incidence preparation from physical coefficient rows.
Beta evaluation, point construction, polynomial Horner, sparse emission, and
cache restoration are all performed by fixed finite commands. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem pairedRows_encode {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    Encoding.encodeList (HornerProgram.encodePolynomial RingProgram.flat)
      ((pairedRows rows).map Prod.fst) =
      Encoding.encodeList Fixed.encode (rows.map Prod.fst) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [pairedRows,List.map_cons,Encoding.encodeList] at ih ⊢
      rw [ih]
      simp only [Fixed.encode,DensePolynomialProgram.encode,
        HornerProgram.encodePolynomial,List.flatMap_def]

private theorem originScratch_ne_betaPort :
    ∀ i : Fin 256, i∈originScratch → i≠220 := by
  intro i hi
  simp [originScratch] at hi
  omega

private theorem targetScratch_ne_seedPorts :
    ∀ i : Fin 256, i∈targetScratch → i≠217 ∧ i≠220 := by
  intro i hi
  simp [targetScratch] at hi
  omega

private theorem scanScratch_ne_targetPorts :
    ∀ i : Fin 256,
      i∈coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231] →
      i≠192 ∧ i≠193 ∧ i≠217 ∧ i≠220 ∧ i≠236 ∧ i≠237 ∧ i≠238 ∧
        i≠243 ∧ i≠247 ∧ i≠254 := by
  intro i hi
  simp [coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  omega

theorem prepareLow_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hB : 0 < baseWidth 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J N : ℕ) (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s scalarWidth frame)
    (Hscalar : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) s)
    (hempty : ∀ i, s (bufferPorts i)=[]) (h121 : s 121=[]) (h122 : s 122=[])
    (hzero : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1 =
      List.replicate (d*baseWidth 3 t) false)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool))
    (hrows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst))
    (hchoice : s 206=rows.map Prod.snd)
    (h207 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h208 : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (h209 : s 209=RingProgram.flat theta)
    (h210 : (s 210).length=N) (h211 : (s 211).length=d*baseWidth 3 t)
    (h212 : (s 212).length=rows.length) (h213 : s 213=List.replicate J true)
    (h104 : s 104=List.replicate (d*baseWidth 3 t) false)
    (he : ∀ i∈lowScratch,s i=[]) :
    ExecutesIn prepareLow (lowBudget s rows.length N J t d) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) := by
  let ops := RingProgram.modelProgram t a M cache
  let W := d*baseWidth 3 t
  let beta := PerturbationBetaProgram.runValue t a M cache theta (pairedRows rows)
  let seed := Encoding.frame (originKey rows.length) ++ Encoding.frame (RingProgram.flat beta) ++ s 217
  let b := Function.update s 220 (RingProgram.flat beta)
  let o := Function.update b 217 seed
  let u := targetState o J W
  let out := lowOutput t a M cache J N theta rows (s 217)
  let f := Function.update u 217 out
  have hb : ExecutesIn PerturbationBetaProgram.betaCommand
      (PerturbationBetaProgram.runBudget s rows.length N t d) s b := by
    have h := PerturbationBetaProgram.betaCommand_run t a M cache hz s Hscalar theta
      (pairedRows rows) N
      (by intro row hr; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr; exact r.1.property)
      (by simpa only [PerturbationBetaProgram.rowsBits,pairedRows_encode] using hrows)
      (by simpa [pairedRows,List.map_map,Function.comp_def] using hchoice)
      h207 h209 h210 h211
      (by intro i hi; exact he i (by simp [lowScratch,hi]))
    simpa [b,beta,pairedRows] using h
  have ho : ExecutesIn origin (33*rows.length+20*W+83) b o := by
    have hoScratch : ∀ i∈originScratch,b i=[] := by
      intro i hi
      have hn := originScratch_ne_betaPort i hi
      simpa [b,hn] using he i (by simp [lowScratch,hi])
    simpa [o,b,seed,W] using origin_run b rows.length (by simpa [b] using h212) hoScratch
  have eo : ∀ i∈targetScratch,o i=[] := by
    intro i hi
    have hn := targetScratch_ne_seedPorts i hi
    simpa [o,b,hn.1,hn.2] using he i (by simp [lowScratch,hi])
  have hu : ExecutesIn initializeTarget (targetBudget s J W) o u := by
    have h := initializeTarget_run o J W
      (by simp [o,b,h207,W]) (by simp [o,b,h208,W]) (by simp [o,b,h209,W])
      (by simpa [o,b] using h213) (by simpa [o,b,W] using h104) eo
    simpa [u,targetBudget,o,b] using h
  have uf : ∀ i : Fin 256,i.val < 205 → i≠192 → i≠193 → u i=s i := by
    intro i hi h192 h193
    rw [show u i=o i from targetState_frame o J W i hi h192 h193]
    have h217 : i≠217 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    have h220 : i≠220 := by intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
    simp [o,b,h217,h220]
  have ue : ∀ i∈coordinateLoadScratch ++ shiftScratch ++ coordinateEmitScratch ++ [218,230,231],u i=[] := by
    intro i hi
    have hn := scanScratch_ne_targetPorts i hi
    simpa [u,targetState,o,b,Function.update_apply,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,
      hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,
      hn.2.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2.2] using
      he i (by simp only [List.mem_append] at hi ⊢; simp only [lowScratch,List.mem_append]; tauto)
  have hs : ExecutesIn (scanRows coordinate)
      (7*(s 205).length+9*rows.length+rows.length*(nativeRowBudget N J rows.length W
        (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)+2)+20) u f := by
    have h := native_scan_run 3 t M cache ops (HornerProgram.modelTable t a M cache) hB hz
      (fun _ _ => rfl) (fun _ _ => rfl) u J N scalarWidth frame
      (PairSpec.BaseReady.frame_except_caches 3 t M cache _ H uf)
      (by intro i; rw [uf _ (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide)]; exact hempty i)
      ((uf 121 (by decide) (by decide) (by decide)).trans h121)
      ((uf 122 (by decide) (by decide) (by decide)).trans h122)
      (by simpa [u,targetState,o,b,h207,ops,W] using zero_bits ops.zeroRun.1 hzero J)
      (by simp [u,targetState,o,b,h213]) hzero (rows.map Prod.fst) theta
      (by simpa [u,targetState,o,b] using hrows)
      (by simpa [u,targetState,o,b] using h212)
      (by simpa [u,targetState,o,b] using h210)
      (by simpa [u,targetState,o,b] using h211)
      (by simpa [u,targetState,o,b,h208,h209,ops,W] using point_bits ops.zeroRun.1 ops.oneRun.1 theta hzero J)
      (by simp [u,targetState,o,b,h213])
      (by simpa [u,targetState,o,b] using h213)
      (by simpa [u,targetState,o,b] using h104)
      (by simp [u,targetState,o,b,h207,hzero])
      (by intro i hi; exact ue i (by simp [hi]))
      (by intro i hi; exact ue i (by simp [hi]))
      (by intro i hi; exact ue i (by simp [hi]))
      (ue 230 (by simp)) (ue 231 (by simp)) (ue 218 (by simp))
    simpa [f,out,lowOutput,ops,seed,beta,u,targetState,o,b] using h
  have hf : ExecutesIn finishTarget
      (2*(2*(J*W)+2*J+W)+6*((s 192).length+(s 193).length+(s 243).length)+33)
      f (Function.update o 217 out) := by
    have h := finishTarget_run f (by simpa [f] using ue 245 (by simp [shiftScratch]))
    have hout : finishedTarget f=Function.update o 217 out :=
      target_restore_dictionary o J W out eo
    rw [hout] at h
    have hk : 2*((f 192).length+(f 193).length+(f 243).length+(f 247).length+(f 254).length)+
        6*((f 236).length+(f 237).length+(f 238).length)+33 =
        2*(2*(J*W)+2*J+W)+6*((s 192).length+(s 193).length+(s 243).length)+33 := by
      simp [f,u,targetState,o,b,h213,h207,h208,h209,W,
        DensePolynomialProgram.Constructor.Counter.paddedBits_length]
      ring
    simpa only [hk] using h
  have hc := clear_run 220 (Function.update o 217 out)
  have hout : Function.update (Function.update o 217 out) 220 []=Function.update s 217 out := by
    funext i
    by_cases h217 : i=217
    · subst i; simp
    by_cases h220 : i=220
    · subst i; simp [o,b,he 220 (by simp [lowScratch,PerturbationBetaProgram.workPorts])]
    simp [o,b,h217,h220]
  rw [hout] at hc
  have hc' : ExecutesIn (clear 220) (2*W+3) (Function.update o 217 out)
      (Function.update s 217 out) := by simpa [o,b,W] using hc
  have all := hb.seq (ho.seq (hu.seq (hs.seq (hf.seq hc'))))
  convert all using 1 <;> first | rfl | (simp only [lowBudget,W]; omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only contract for the closed native low-variable worker. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem LowInput.run_oai {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    ExecutesIn prepareLow (lowBudget s rows.length N J t d) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) :=
  prepareLow_run t a M cache h.widthPositive h.zeroCanonical s J N (s 10) (fun _=>[])
    h.pairReady h.scalarReady h.buffersEmpty h.empty121 h.empty122 h.zeroBits theta rows
    h.sourceRows h.choices h.zeroWord h.oneWord h.thetaWord h.sourceCount h.wordWidth
    h.ambientCount h.targetCount h.widthZeros h.workEmpty

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_oai
