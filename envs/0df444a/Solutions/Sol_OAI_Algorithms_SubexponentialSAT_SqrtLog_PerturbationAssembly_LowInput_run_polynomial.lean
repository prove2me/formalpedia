-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:03:49.066236+00:00
-- url     : https://prove2.me/submissions/916f9f43-97a4-45b0-bdeb-3f6da0ccbcf3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationAssembly_LowInput_run

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

theorem encodePolynomial_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hw : ∀ a, (encode a).length = W) (P : List C) :
    (encodePolynomial encode P).length = P.length * W := by
  induction P with
  | nil => simp [encodePolynomial]
  | cons c P ih => simp [encodePolynomial, hw, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Concrete polynomial native-step bound, before the fixed primitive-machine
simulation constant. -/
theorem modelBudget_polynomial (n t d : ℕ) :
    modelBudget n t d ≤ 200000 * (n+1) * (d+1)^3 * (baseWidth 3 t+1)^2 := by
  have hm := Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := Services.addBudget_polynomial (baseWidth 3 t) d
  have hs := Nat.mul_le_mul_left n (Nat.add_le_add hm ha)
  unfold modelBudget budget
  ring_nf at *
  omega

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationProgramPaddingRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram.Padding
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem budget_polynomial (N D W : ℕ) :
    budget N D W ≤ 280*(N+1)*(D+1)*(W+1) := by
  unfold budget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.PerturbationProgram.Padding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationEmitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native emission of the positive part of a shifted coefficient array.
The dimensions and the singleton support mask are runtime data. The constant
cell is consumed without emission; all later cells are framed, including zero
coefficients. No normalization or arithmetic oracle is used. -/


namespace SubexponentialSAT.SqrtLog.PerturbationEmitProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl

theorem budget_polynomial (J n W : ℕ) :
    budget J n W ≤ 150*(J+1)*(J+n+W+1) := by
  unfold budget loopBudget stepBudget
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.PerturbationEmitProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial work and storage bounds for native shifted rows. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

theorem shiftBudget_polynomial (N J W Km Ka : ℕ) :
    shiftBudget N J W Km Ka ≤
      1000*(N+1)*(J+1)*(W+1)+(N+1)*(Km+Ka) := by
  have hp := PerturbationProgram.Padding.budget_polynomial N J W
  unfold shiftBudget HornerProgram.budget
  ring_nf at hp ⊢
  omega

theorem shifted_row_work_bound (N J n d B : ℕ) :
    15*(N*(d*B))+30*n+43+
      shiftBudget N J (d*B) (DensePolynomialProgram.nativeMulBudget J d B)
        (DensePolynomialProgram.AddService.budget d B J J)+
      PerturbationEmitProgram.budget J n (d*B) ≤ rowWorkPolynomial N J n d B := by
  have hs := shiftBudget_polynomial N J (d*B) (DensePolynomialProgram.nativeMulBudget J d B)
    (DensePolynomialProgram.AddService.budget d B J J)
  have hm := DensePolynomialProgram.nativeMulBudget_polynomial J d B
  have he := PerturbationEmitProgram.budget_polynomial J n (d*B)
  have hm' := Nat.mul_le_mul_left (N+1) (Nat.add_le_add_right hm
    (DensePolynomialProgram.AddService.budget d B J J))
  unfold rowWorkPolynomial
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial native cost, including framing, all skipped rows, and cleanup.
The parser dependency has a fixed16/256 ABI owned by this helper. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

theorem rowsBits_length {t d : ℕ} (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L) :
    (rowsBits rows).length=rows.length*(2*(L*(d*baseWidth 3 t))+2)+1 := by
  induction rows with
  | nil => simp [rowsBits]
  | cons row rows ih =>
    have hl := hL row (by simp)
    have hi := ih (fun r hr => hL r (by simp [hr]))
    simp only [rowsBits,List.map_cons,Encoding.length_encodeList_cons,
      HornerProgram.encodePolynomial_length RingProgram.flat _ RingProgram.flat_length,hl] at *
    rw [hi]
    simp only [List.length_cons]
    ring

theorem runBudget_eq (t d L : ℕ) (base : Store) (rows : List (List (Coeff t d) × Bool))
    (theta zero : Coeff t d) (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat zero) (h209 : base 209=RingProgram.flat theta)
    (h211 : (base 211).length=d*baseWidth 3 t) :
    runBudget base rows.length L t d=nativeBudget rows.length L t d := by
  simp only [runBudget,initBudget,h205,h206,h207,h209,List.length_map,
    RingProgram.flat_length,h211,rowsBits_length rows L hL,nativeBudget]
  ring

theorem nativeBudget_polynomial (n L t d : ℕ) :
    nativeBudget n L t d ≤ 1000000*(n+1)*(L+1)*(d+1)^3*(baseWidth 3 t+1)^2 := by
  have hm := HornerProgram.modelBudget_polynomial L t d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  have hsum := Nat.mul_le_mul_left n (Nat.add_le_add hm ha)
  unfold nativeBudget stepBudget selectedBudget
  ring_nf at *
  omega

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLowBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial cost of the complete low-variable producer. Incoming
cache size is charged even when the source and target cutoffs differ. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem fixedRows_length {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    (Encoding.encodeList Fixed.encode (rows.map Prod.fst)).length=
      rows.length*(2*(N*(d*B))+2)+1 := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.map_cons,Encoding.length_encodeList_cons,Fixed.encode_length]
      rw [ih]
      simp only [List.length_cons]
      ring

theorem LowInput.budget_bound {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    lowBudget s rows.length N J t d ≤
      lowWorkPolynomial rows.length N J t d
        ((s 192).length+(s 193).length+(s 243).length) := by
  have hL : ∀ row∈pairedRows rows,row.1.length=N := by
    intro row hr
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hr
    exact r.1.property
  have hb := PerturbationBetaProgram.runBudget_eq t d N s (pairedRows rows) theta
    (RingProgram.modelProgram t a M cache).zeroRun.1 hL
    (by simpa only [PerturbationBetaProgram.rowsBits,pairedRows_encode] using h.sourceRows)
    (by simpa [pairedRows,List.map_map,Function.comp_def] using h.choices)
    h.zeroWord h.thetaWord h.wordWidth
  simp only [pairedRows,List.length_map] at hb
  have hb' : PerturbationBetaProgram.runBudget s rows.length N t d ≤
      1000000*(rows.length+1)*(N+1)*(d+1)^3*(baseWidth 3 t+1)^2 := by
    rw [hb]
    exact PerturbationBetaProgram.nativeBudget_polynomial rows.length N t d
  have hs : (s 205).length=rows.length*(2*(N*(d*baseWidth 3 t))+2)+1 := by
    rw [h.sourceRows]
    exact fixedRows_length rows
  have hr := shifted_row_work_bound N J rows.length d (baseWidth 3 t)
  change nativeRowBudget N J rows.length (d*baseWidth 3 t)
    (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J) ≤ _ at hr
  have hr' := Nat.mul_le_mul_left rows.length (Nat.add_le_add_right hr 2)
  unfold lowBudget targetBudget lowWorkPolynomial
  rw [hs]
  dsimp only
  omega

/-- Full native execution with the explicit polynomial bound. -/
theorem LowInput.run_polynomial_oai {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    ExecutesIn prepareLow
      (lowWorkPolynomial rows.length N J t d ((s 192).length+(s 193).length+(s 243).length)) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) :=
  h.run.mono h.budget_bound

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.LowInput.run_polynomial_oai
