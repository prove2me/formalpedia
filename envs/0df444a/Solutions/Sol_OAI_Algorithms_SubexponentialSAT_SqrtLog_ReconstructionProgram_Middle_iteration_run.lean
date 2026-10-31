-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:34:12.424649+00:00
-- url     : https://prove2.me/submissions/11e5258a-6a3a-41ab-97e6-f02283b57791

import Mathlib
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ReconstructionProgram_Middle_command_run

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

section Semantics
variable {C A : Type*} [CommRing A]

theorem fold_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (x : C) (cs : List C) (seed : C) :
    decode (fold (stepValue mulOp addOp x) cs seed) =
      cs.foldl (fun value b => value * decode x + decode b) (decode seed) := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih =>
      change decode (fold (stepValue mulOp addOp x) cs (stepValue mulOp addOp x seed c)) = _
      rw [ih, List.foldl_cons]
      simp only [stepValue, ha, hm]

theorem output_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (P : List C) (x zero : C) (hz : decode zero = 0) :
    decode (fold (stepValue mulOp addOp x) P.reverse zero) =
      (PolynomialAlgorithm.denote (P.map decode)).eval (decode x) := by
  rw [fold_decode decode mulOp addOp hm ha, List.foldl_reverse, hz]
  induction P with
  | nil => simp []
  | cons a P ih =>
      simp only [List.foldr_cons, List.map_cons, PolynomialAlgorithm.denote,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, ih]
      ring

end Semantics
end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final cleanup and complete tape-loop costs for scalar reconstruction.
The arithmetic-middle premise below is an actual execution of a fixed command;
its concrete implementation is assembled separately from the CRT services. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open scoped BigOperators

/-- The actual remaining ++ processed cofactor stream contains each other
node exactly once. No cancellation and no nonzero-node assumption is used. -/
theorem cofactor_stream_product {Q : ℕ} {R : Type*} [CommMonoid R]
    (processed remaining : List (Fin Q)) (current : Fin Q) (f : Fin Q → R)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining) :
    ((remaining ++ processed).map f).prod = ∏ i ∈ Finset.univ.erase current, f i := by
  have hn := List.nodup_finRange Q
  rw [hfull] at hn
  have hm := List.nodup_cons.mp (List.nodup_middle.mp hn)
  have hset : (processed.reverse ++ remaining).toFinset = Finset.univ.erase current := by
    ext j
    simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hj he
      subst j
      exact hm.1 hj
    · intro hne
      have hj : j ∈ processed.reverse ++ current :: remaining := by
        rw [← hfull]
        exact List.mem_finRange j
      rcases List.mem_append.mp hj with hp | hr
      · exact List.mem_append_left _ hp
      · rcases List.mem_cons.mp hr with he | hr
        · exact False.elim (hne he)
        · exact List.mem_append_right _ hr
  calc
    ((remaining ++ processed).map f).prod = ((processed.reverse ++ remaining).map f).prod := by
      simp [List.map_append, List.prod_append, List.map_reverse, List.prod_reverse, mul_comm]
    _ = (processed.reverse ++ remaining).toFinset.prod f := (List.prod_toFinset f hm.2).symm
    _ = ∏ i ∈ Finset.univ.erase current, f i := by rw [hset]

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramCofactorScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open CRTLocalProgram (LowFrame ServiceSpec)

section Semantics
variable {C A : Type*} [CommRing A]

theorem includeValue_decode (decode : C → A) (mul : C → C → C)
    (hmul : ∀ a b, decode (mul a b) = decode a * decode b)
    (minusOne : C) (hminus : decode minusOne = -1) (J : ℕ) (a c : C) :
    decode (includeValue mul minusOne J a c) = decode a * (-decode c)^J := by
  rw [includeValue, CRTLocalProgram.iterate_mul_decode decode mul hmul, hmul, hminus]
  simp

end Semantics

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Cofactor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial majorants for the physical middle and outer traversal. The
native service costs can be substituted directly in these inequalities. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT SubexpCRTOuterProgram

theorem middleBudget_mono {Q J W Km Ka Kl Q' J' W' Km' Ka' Kl' : ℕ}
    (hQ : Q ≤ Q') (hJ : J ≤ J') (hW : W ≤ W')
    (hm : Km ≤ Km') (ha : Ka ≤ Ka') (hl : Kl ≤ Kl') :
    Middle.budget Q J W Km Ka Kl ≤ Middle.budget Q' J' W' Km' Ka' Kl' := by
  unfold Middle.budget CofactorOuter.budget Cofactor.includeBudget Local.budget
    Horner.budget HornerProgram.budget
  gcongr

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTAtZero
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct evaluation of the explicit Hermite reconstruction at zero. The
algorithm needs only local corrections and scalar Horner evaluations; no
global shifted polynomial or final polynomial division is required. -/

namespace SubexponentialSAT.SubexpCRTAtZero

open Polynomial
open scoped BigOperators

noncomputable section

variable {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]

theorem cofactor_eval_zero (θ : I → A) (D : ℕ) (i : I) :
    (JetCRT.cofactor θ D i).eval 0 =
      ∏ j ∈ Finset.univ.erase i, (-θ j)^D := by
  simp [JetCRT.cofactor, JetCRT.nodePower, eval_prod]

end

end SubexponentialSAT.SubexpCRTAtZero

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic interpretation of the values produced by the physical outer
Hermite stages. This uses precisely the coefficient list evaluated by the
native Horner loop. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT Polynomial
open scoped BigOperators

variable {C A : Type*} [CommRing A]

theorem factor_decode (decode : C → A) (mul : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (minusOne unit : C) (hminus : decode minusOne = -1) (hu : decode unit = 1)
    (J : ℕ) (cs : List C) :
    decode (cs.foldl (Cofactor.includeValue mul minusOne J) unit) =
      (cs.map (fun c => (-decode c)^J)).prod := by
  have hf (a : C) : decode (cs.foldl (Cofactor.includeValue mul minusOne J) a) =
      decode a * (cs.map (fun c => (-decode c)^J)).prod := by
    induction cs generalizing a with
    | nil => simp
    | cons c cs ih =>
      rw [List.foldl_cons, ih, Cofactor.includeValue_decode decode mul hm minusOne hminus]
      simp [mul_assoc]
  rw [hf, hu, one_mul]

theorem nodeValue_decode (decode : C → A) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (minusOne zero unit node acc : C)
    (hminus : decode minusOne = -1) (hz : decode zero = 0) (hu : decode unit = 1)
    (J : ℕ) (remaining processed correction : List C) :
    decode (nodeValue mul add minusOne zero unit node acc J remaining processed correction) =
      decode acc + ((remaining ++ processed).map (fun c => (-decode c)^J)).prod *
        (PolynomialAlgorithm.denote (correction.map decode)).eval (-decode node) := by
  unfold nodeValue
  rw [ha, hm, factor_decode decode mul hm minusOne unit hminus hu,
    HornerProgram.output_decode decode mul add hm ha correction _ zero hz, hm, hminus]
  simp

theorem indexed_nodeValue_decode {Q : ℕ}
    (decode : C → A) (mul add : C → C → C)
    (hm : ∀ a b, decode (mul a b) = decode a * decode b)
    (ha : ∀ a b, decode (add a b) = decode a + decode b)
    (minusOne zero unit acc : C)
    (hminus : decode minusOne = -1) (hz : decode zero = 0) (hu : decode unit = 1)
    (nodes : Fin Q → C) (J : ℕ) (remaining processed : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (correction : List C) (H : A[X])
    (hc : PolynomialAlgorithm.denote (correction.map decode) = H) :
    decode (nodeValue mul add minusOne zero unit (nodes i) acc J
      (remaining.map nodes) (processed.map nodes) correction) =
      decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 * H.eval (-decode (nodes i)) := by
  rw [nodeValue_decode decode mul add hm ha _ _ _ _ _ hminus hz hu, hc,
    SubexpCRTAtZero.cofactor_eval_zero]
  congr 2
  simpa only [← List.map_append, List.map_map, Function.comp_def] using
    SubexpCRTOuterProgram.cofactor_stream_product processed remaining i
      (fun j => (-decode (nodes j))^J) hfull

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramIteration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact finite-command node iteration, interpreted in its represented
ring. The local producer premise is an actual trace, discharged by the native
local-correction theorem in the model specialization. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open Polynomial
open CRTLocalProgram (ServiceSpec)

theorem iteration_run_oai {C A : Type*} [CommRing A] {Q : ℕ}
    (encode : C → List Bool) (decode : C → A)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data)
    (nodes : Fin Q → C) (remaining processed : List (Fin Q)) (i : Fin Q)
    (hfull : List.finRange Q = processed.reverse ++ i :: remaining)
    (unit minusOne zero acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hmd : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (had : ∀ a b, decode (addOp a b) = decode a + decode b)
    (hunit : decode unit = 1) (hminus : decode minusOne = -1) (hzero : decode zero = 0)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = (remaining.map nodes).flatMap encode)
    (hp : d.stacks 258 = (processed.map nodes).flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode (nodes i))
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ j ∈ cleanPorts, d.stacks j = [])
    (correction : List C) (hcl : correction.length = J) (H : A[X])
    (hdenote : PolynomialAlgorithm.denote (correction.map decode) = H)
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget Q J W Km Ka Kl, ∃ rf b,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261 (encode b)⟩ ∧
      decode b = decode acc + (JetCRT.cofactor (decode ∘ nodes) J i).eval 0 *
        H.eval (-decode (nodes i)) := by
  obtain ⟨n, hn, rf, he⟩ := command_run encode localCode multiply add mulOp addOp
    Km Ka Kl W J d (remaining.map nodes) (processed.map nodes) correction
    unit minusOne zero (nodes i) acc hm ha hw hW hr hp hu hn hz hx hacc hJ hcl h277 hc hlocal
  refine ⟨n, ?_, rf, _, he, ?_⟩
  · apply hn.trans
    apply reconstructionProgramBudgetAux
  · exact indexed_nodeValue_decode decode mulOp addOp hmd had minusOne zero unit acc
      hminus hzero hunit nodes J remaining processed i hfull correction H hdenote
where
  reconstructionProgramBudgetAux :
      budget ((remaining.map nodes).length + (processed.map nodes).length) J W Km Ka Kl ≤
        budget Q J W Km Ka Kl := by
    apply middleBudget_mono _ le_rfl le_rfl le_rfl le_rfl le_rfl
    have hlen := congrArg List.length hfull
    simp only [List.length_finRange, List.length_append, List.length_reverse, List.length_cons] at hlen
    simp only [List.length_map]
    omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle.iteration_run_oai.{u_1, u_2}
