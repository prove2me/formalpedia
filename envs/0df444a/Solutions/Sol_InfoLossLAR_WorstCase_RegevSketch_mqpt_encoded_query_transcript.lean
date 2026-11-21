-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.mqpt_encoded_query_transcript
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T15:34:21.182122+00:00
-- url     : https://prove2.me/submissions/4401e99d-86f6-4084-b3a6-ae608780bd3d

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Vector.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.DecisionSearch
end InfoLossLAR.WorstCase.DecisionSearch

namespace InfoLossLAR.WorstCase.NativeIndependence
end InfoLossLAR.WorstCase.NativeIndependence

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.StaticBatch
end InfoLossLAR.WorstCase.StaticBatch

namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN

namespace Integration9_9
end Integration9_9

namespace Integration9_9.DyadicReadout
end Integration9_9.DyadicReadout

namespace Integration9_9.LARCoinLayout
end Integration9_9.LARCoinLayout

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.LoadedBatch
end Integration9_9.LoadedBatch

namespace Integration9_9.LoadedBatch.PostComposition
end Integration9_9.LoadedBatch.PostComposition

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace Integration9_9.TM2PolynomialBudget
end Integration9_9.TM2PolynomialBudget

namespace Integration9_9.TM2StockLists
end Integration9_9.TM2StockLists

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QMCNumericRuntime
end QMCNumericRuntime

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule0

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

private theorem phase_composition {N : ℕ} (f g : QState N → QState N)
    (a b : Bits N → ℂ)
    (hf : ∀ φ x, f φ x = a x * φ x) (hg : ∀ φ x, g φ x = b x * φ x)
    (φ : QState N) (x : Bits N) : g (f φ) x = b x * a x * φ x := by
  rw [hg, hf, mul_assoc]

private theorem cnot_conj_phase_map {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N)
    (F : QState N → QState N) (a : Bits N → ℂ)
    (hF : ∀ φ x, F φ x = a x * φ x) :
    cnotState i j hij (F (cnotState i j hij ψ)) =
      fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  funext x
  simp only [cnotState, hF, Function.update_self, Function.update_of_ne hij, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Function.update_idem, Function.update_eq_self]

private theorem apply1_tMat_eq_phase {N : ℕ} (i : Fin N) (ψ : QState N) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  funext x
  simp [apply1, tMat]

private theorem inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- `shiTof_Ph F a`: `F` acts as multiplication by the diagonal phase `a`. -/
private abbrev shiTof_Ph {N : ℕ} (F : QState N → QState N) (a : Bits N → ℂ) : Prop :=
  ∀ (φ : QState N) (x : Bits N), F φ x = a x * φ x

private lemma shiTof_Ph_comp {N : ℕ} {f g : QState N → QState N} {a b : Bits N → ℂ}
    (hf : shiTof_Ph f a) (hg : shiTof_Ph g b) :
    shiTof_Ph (fun ψ => g (f ψ)) (fun x => b x * a x) := by
  intro ψ x
  exact phase_composition f g a b hf hg ψ x

private lemma shiTof_Ph_conj {N : ℕ} {F : QState N → QState N} {a : Bits N → ℂ}
    (i j : Fin N) (hij : i ≠ j) (hF : shiTof_Ph F a) :
    shiTof_Ph (fun ψ => cnotState i j hij (F (cnotState i j hij ψ)))
      (fun x => a (Function.update x j (xor (x j) (x i)))) := by
  intro ψ x
  exact congrFun (cnot_conj_phase_map i j hij ψ F a hF) x

private lemma shiTof_Ph_t {N : ℕ} (i : Fin N) :
    shiTof_Ph (apply1 tMat i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  simp only [apply1_tMat_eq_phase]

/-- `T ^ 7` on one wire, as seven `T` gates. -/
private noncomputable def shiTof_T7 {N : ℕ} (i : Fin N) (ψ : QState N) : QState N :=
  apply1 tMat i (apply1 tMat i (apply1 tMat i (apply1 tMat i
    (apply1 tMat i (apply1 tMat i (apply1 tMat i ψ))))))

private lemma shiTof_Ph_T7 {N : ℕ} (i : Fin N) :
    shiTof_Ph (shiTof_T7 i)
      (fun x => if x i then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  simp only [shiTof_T7, apply1_tMat_eq_phase]
  cases hx : x i with
  | false => simp [hx]
  | true =>
      simp only [hx, if_true]
      ring

/-- A `T^7` block conjugated by a CNOT: control `i`, target `j`. -/
private noncomputable def shiTof_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) (ψ : QState N) :
    QState N :=
  cnotState i j hij (shiTof_T7 j (cnotState i j hij ψ))

private lemma shiTof_Ph_cB {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    shiTof_Ph (shiTof_cB i j hij)
      (fun x => if xor (x j) (x i) then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) := by
  intro φ x
  have h := shiTof_Ph_conj i j hij (shiTof_Ph_T7 j) φ x
  simp only [Function.update_self] at h
  exact h

/-- The three-parity `T` block: `CNOT(p,r) CNOT(q,r) T_r CNOT(q,r) CNOT(p,r)`. -/
private noncomputable def shiTof_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) : QState N :=
  cnotState p r hpr (cnotState q r hqr (apply1 tMat r
    (cnotState q r hqr (cnotState p r hpr ψ))))

private lemma shiTof_Ph_cB7 {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cB7 p q r hpr hqr)
      (fun x => if xor (xor (x r) (x p)) (x q) then
        Complex.exp (Complex.I * Real.pi / 4) else 1) := by
  intro φ x
  have h := shiTof_Ph_conj p r hpr (shiTof_Ph_conj q r hqr (shiTof_Ph_t r)) φ x
  simp only [Function.update_self, Function.update_of_ne hqr] at h
  exact h

/-- The seven block phases multiply to the CCZ sign. -/
private lemma shiTof_phase_prod (a b c : Bool) :
    (if xor (xor c a) b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
      ((if xor c a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
        ((if xor c b then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
          ((if xor b a then Complex.exp (Complex.I * Real.pi / 4) ^ 7 else 1) *
            ((if c then Complex.exp (Complex.I * Real.pi / 4) else 1) *
              ((if b then Complex.exp (Complex.I * Real.pi / 4) else 1) *
                (if a then Complex.exp (Complex.I * Real.pi / 4) else 1))))))
      = if a && b && c then (-1 : ℂ) else 1 := by
  let w : ℂ := Complex.exp (Complex.I * Real.pi / 4)
  have h4 : w ^ 4 = -1 := by
    rw [show w ^ 4 = Complex.exp (4 * (Complex.I * Real.pi / 4)) from
      (Complex.exp_nat_mul _ 4).symm]
    convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> ring
  have h16 : w ^ 16 = 1 := by
    rw [show 16 = 4 * 4 from rfl, pow_mul, h4]
    norm_num
  change (if xor (xor c a) b then w else 1) *
      ((if xor c a then w ^ 7 else 1) *
        ((if xor c b then w ^ 7 else 1) *
          ((if xor b a then w ^ 7 else 1) *
            ((if c then w else 1) * ((if b then w else 1) * (if a then w else 1)))))) = _
  cases a <;> cases b <;> cases c <;> norm_num <;> ring_nf <;> first | exact h16 | exact h4

/-- The CCZ part of the circuit, as a composition of the seven diagonal blocks. -/
private noncomputable def shiTof_cczOp {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) : QState N :=
  shiTof_cB7 p q r hpr hqr (shiTof_cB p r hpr (shiTof_cB q r hqr (shiTof_cB p q hpq
    (apply1 tMat r (apply1 tMat q (apply1 tMat p ψ))))))

private lemma shiTof_Ph_ccz {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    shiTof_Ph (shiTof_cczOp p q r hpq hpr hqr)
      (fun x => if x p && x q && x r then (-1 : ℂ) else 1) := by
  have c7 := shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_comp
      (shiTof_Ph_comp (shiTof_Ph_comp (shiTof_Ph_t p) (shiTof_Ph_t q)) (shiTof_Ph_t r))
      (shiTof_Ph_cB p q hpq)) (shiTof_Ph_cB q r hqr)) (shiTof_Ph_cB p r hpr))
      (shiTof_Ph_cB7 p q r hpr hqr)
  intro φ x
  first
    | exact (c7 φ x).trans
        (congrArg (fun z : ℂ => z * φ x) (shiTof_phase_prod (x p) (x q) (x r)))
    | (refine (c7 φ x).trans ?_
       rw [← shiTof_phase_prod (x p) (x q) (x r)])
    | (refine (c7 φ x).trans ?_
       beta_reduce
       rw [shiTof_phase_prod (x p) (x q) (x r)])

private lemma shiTof_hconj {N : ℕ} (p q r : Fin N) (hpr : p ≠ r) (hqr : q ≠ r)
    (F : QState N → QState N)
    (hF : ∀ (φ : QState N) (y : Bits N),
      F φ y = (if y p && y q && y r then (-1 : ℂ) else 1) * φ y)
    (ψ : QState N) :
    apply1 hMat r (F (apply1 hMat r ψ))
      = fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
    inv_sqrt_two_mul_self
  funext x
  have hup : ∀ b : Bool, F (apply1 hMat r ψ) (Function.update x r b)
      = (if x p && x q && b then (-1 : ℂ) else 1)
        * ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
    intro b
    have e1 : Function.update x r b p = x p := Function.update_of_ne hpr b x
    have e2 : Function.update x r b q = x q := Function.update_of_ne hqr b x
    have e3 : Function.update x r b r = b := Function.update_self r b x
    have e4 : apply1 hMat r ψ (Function.update x r b)
        = ∑ c : Bool, hMat b c * ψ (Function.update x r c) := by
      simp only [apply1, Function.update_self, Function.update_idem]
    simp only [hF, e1, e2, e3, e4]
  have main : apply1 hMat r (F (apply1 hMat r ψ)) x
      = ∑ b : Bool, hMat (x r) b * F (apply1 hMat r ψ) (Function.update x r b) := rfl
  rw [main]
  -- PHASE 1: split the outer Bool sum, `hMat` still FOLDED.
  simp only [Fintype.sum_bool]
  -- PHASE 2: expand `F` while `hMat` is still folded, so `hup`'s LHS still matches.
  -- Listing `hup` and `hMat` in one `simp only` unfolded `hMat` inside `F (apply1 hMat r ψ)`
  -- first, `hup` then matched nothing and was silently dropped ("unused simp argument"),
  -- leaving `ring` with two opaque `F …` atoms.
  first
    | rw [hup true, hup false]
    | simp only [hup]
  -- PHASE 3: only now unfold the matrix and split the two inner Bool sums.
  simp only [hMat, Matrix.of_apply, Fintype.sum_bool, Complex.ofReal_inv]
  -- PHASE 4: abstract the irrational AFTER all unfolding, so no `(↑√2)⁻¹` survives
  -- alongside `s` and `hs` applies to every quadratic term.
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ with hsdef
  -- `cases h : e` already substitutes the value, so `simp only [hr, hm]` has nothing to do,
  -- and a no-progress `simp only` is an ERROR in Lean 4 (it killed all four branches).
  cases hr : x r <;> cases hm : (x p && x q) <;> (try simp only [hr, hm]) <;> norm_num <;>
    first
      | linear_combination (2 * ψ (Function.update x r false)) * hs
      | linear_combination (2 * ψ (Function.update x r true)) * hs
      | linear_combination (-2 * ψ (Function.update x r false)) * hs
      | linear_combination (-2 * ψ (Function.update x r true)) * hs

private lemma shiTof_layerOk_map {N : ℕ} (gs : List (Instr N)) :
    ∀ l ∈ gs.map (fun g => [g]), LayerOk l := by
  intro l hl
  simp only [List.mem_map] at hl
  obtain ⟨g, _, hg⟩ := hl
  subst hg
  exact List.pairwise_singleton _ g

private lemma shiTof_run_map {N : ℕ} (gs : List (Instr N)) (ψ : QState N) :
    runLayered (gs.map (fun g => [g])) ψ = gs.foldl (fun st g => Instr.apply g st) ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      have hstep : runLayered ((g :: gs).map (fun z => [z])) ψ
          = runLayered (gs.map (fun z => [z])) (Instr.apply g ψ) := rfl
      rw [hstep, ih, List.foldl_cons]

private lemma shiTof_fold_eq {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (ψ : QState N) :
    (toffoliGates p q r hpq hpr hqr).foldl (fun st g => Instr.apply g st) ψ
      = apply1 hMat r (shiTof_cczOp p q r hpq hpr hqr (apply1 hMat r ψ)) := by
  first
    | rfl
    | simp only [toffoliGates, shiTof_cczOp, shiTof_cB, shiTof_cB7, shiTof_T7,
        List.foldl_cons, List.foldl_nil, Instr.apply]

theorem toffoliCircuit_apply {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (ψ : QState N) :
    runLayered (toffoliCircuit p q r hpq hpr hqr) ψ =
      fun x => ψ (Function.update x r (xor (x r) (x p && x q))) := by
  rw [toffoliCircuit, shiTof_run_map, shiTof_fold_eq]
  exact shiTof_hconj p q r hpr hqr _ (fun φ y => shiTof_Ph_ccz p q r hpq hpr hqr φ y) ψ

theorem toffoliCircuit_wellFormed {N : ℕ} (p q r : Fin N)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ layer ∈ toffoliCircuit p q r hpq hpr hqr, LayerOk layer := shiTof_layerOk_map _

end InfoLossLAR.WorstCase

end P2MDyadicModule0

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule1

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2PlatformSerialization

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open QAlgorithms.Complexity

open Polynomial

theorem readUnary_rest_length (xs : Str) : (readUnary xs).2.length ≤ xs.length := by
  simp only [readUnary, List.length_drop]
  omega

@[fun_prop] theorem lengthToken_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (lengthToken : List α → Str) := by
  unfold lengthToken
  fun_prop

@[fun_prop] theorem serializeWords_poly : Poly serializeWords := by
  unfold serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair lengthToken_poly hf)

section RepeatedParser

variable {α : Type} [Coding α] [Inhabited α]

variable (read : Str → Str × α)

lemma readList_rest_length (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) (xs : Str) :
    (readList read xs).1.length ≤ xs.length := by
  exact (parser_fold_bounds read hr hrest (unarySlots xs) (readUnary xs).2 []).1.trans
    (readUnary_rest_length xs)

end RepeatedParser

end Integration9_9.TM2PlatformSerialization

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule2

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readCircuitInstruction_poly : Poly readCircuitInstruction := by
  unfold readCircuitInstruction
  fun_prop

theorem readCircuitInstruction_rest_length (xs : Str) :
    (readCircuitInstruction xs).1.length ≤ xs.length := by
  unfold readCircuitInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)

@[fun_prop] theorem readCircuitLayer_poly : Poly readCircuitLayer :=
  readList_poly readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length

theorem readCircuitLayer_rest_length (xs : Str) :
    (readCircuitLayer xs).1.length ≤ xs.length :=
  readList_rest_length readCircuitInstruction readCircuitInstruction_poly readCircuitInstruction_rest_length xs

@[fun_prop] theorem readCircuitLayers_poly : Poly readCircuitLayers :=
  readList_poly readCircuitLayer readCircuitLayer_poly readCircuitLayer_rest_length

end InfoLossLAR.WorstCase

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

namespace ReversibleGate

theorem compile_apply {n : ℕ} (g : ReversibleGate n) (ψ : QState n) :
    runLayered g.compile ψ = fun x => ψ (g.act x) := by
  cases g with
  | flip i =>
    funext x
    simp only [compile, runLayered, runLayer, List.foldl_cons, List.foldl_nil, Instr.apply, apply1]
    cases hx : x i <;> simp [xMat, act, hx]
  | controlled i j hij => rfl
  | toffoli i j k hij hik hjk => exact toffoliCircuit_apply i j k hij hik hjk ψ

theorem compile_wellFormed {n : ℕ} (g : ReversibleGate n) :
    ∀ layer ∈ g.compile, LayerOk layer := by
  cases g with
  | flip i => simp [compile, LayerOk]
  | controlled i j hij => simp [compile, LayerOk]
  | toffoli i j k hij hik hjk => exact toffoliCircuit_wellFormed i j k hij hik hjk

theorem compile_depth {n : ℕ} (g : ReversibleGate n) : depth g.compile ≤ 37 := by
  cases g <;> simp [compile, depth, toffoliCircuit, toffoliGates]

end ReversibleGate

private theorem runLayered_append {n : ℕ} (c d : Layered n) (ψ : QState n) :
    runLayered (c ++ d) ψ = runLayered d (runLayered c ψ) := List.foldl_append

/-- Amplitude semantics for every input state, including superpositions and garbage. -/
theorem compileReversible_apply {n : ℕ} (gates : List (ReversibleGate n)) (ψ : QState n) :
    runLayered (compileReversible gates) ψ = fun x => ψ ((reversibleAction gates).symm x) := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change runLayered (g.compile ++ compileReversible gs) ψ = _
    rw [runLayered_append, ih, g.compile_apply]
    rfl

theorem compileReversible_wellFormed {n : ℕ} (gates : List (ReversibleGate n)) :
    ∀ layer ∈ compileReversible gates, LayerOk layer := by
  intro layer hl
  obtain ⟨g, _, hgl⟩ := List.mem_flatMap.1 hl
  exact g.compile_wellFormed layer hgl

theorem compileReversible_depth {n : ℕ} (gates : List (ReversibleGate n)) :
    depth (compileReversible gates) ≤ 37 * gates.length := by
  induction gates with
  | nil => simp [compileReversible, depth]
  | cons g gs ih =>
    have hg := g.compile_depth
    change (g.compile ++ compileReversible gs).length ≤ _
    simp only [List.length_append, List.length_cons]
    change g.compile.length ≤ 37 at hg
    change (compileReversible gs).length ≤ _ at ih
    omega

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem toffoliInstructionWords_poly :
    Poly (fun x : Str × Str × Str => toffoliInstructionWords x.1 x.2.1 x.2.2) := by
  unfold toffoliInstructionWords
  fun_prop

@[fun_prop] theorem readReversibleInstruction_poly : Poly readReversibleInstruction := by
  unfold readReversibleInstruction
  fun_prop

theorem readReversibleInstruction_rest_length (xs : Str) :
    (readReversibleInstruction xs).1.length ≤ xs.length := by
  unfold readReversibleInstruction
  split_ifs
  · exact (readUnary_rest_length _).trans (readUnary_rest_length _)
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
  · exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
      ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem reversibleUniformUnaryWidth (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

theorem readReversibleInstruction_append {n : ℕ} (g : ReversibleGate n) (xs : Str) :
    readReversibleInstruction (g.code ++ xs) = (xs, g.compile.flatten.map encInstr) := by
  cases g <;> simp only [ReversibleGate.code, List.append_assoc, readReversibleInstruction,
    reversibleUniformUnaryWidth, readUnary_append] <;> norm_num <;> rfl

@[fun_prop] theorem readReversibleProgram_poly : Poly readReversibleProgram :=
  readList_poly readReversibleInstruction readReversibleInstruction_poly readReversibleInstruction_rest_length

theorem readReversibleProgram_append {n : ℕ} (gates : List (ReversibleGate n)) (xs : Str) :
    readReversibleProgram (encStr (gates.map ReversibleGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.flatten.map encInstr)) :=
  readList_append_mapped readReversibleInstruction ReversibleGate.code
    (fun g => g.compile.flatten.map encInstr) readReversibleInstruction_append gates xs

private theorem compiledWords {n : ℕ} (gates : List (ReversibleGate n)) :
    ((gates.map (fun g => g.compile.flatten.map encInstr)).flatten).map (fun word => [word]) =
      (compileReversible gates).map (List.map encInstr) := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, compileReversible,
      List.flatMap_cons] at ih ⊢
    rw [ih]
    congr 1
    cases g <;> rfl

@[fun_prop] theorem compileReversibleDescription_poly : Poly compileReversibleDescription := by
  unfold compileReversibleDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileReversibleDescription_code (F : ReversibleFamily) (n : ℕ) :
    compileReversibleDescription (F.code n) = encFamilyAt F.compile n := by
  unfold ReversibleFamily.code compileReversibleDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readReversibleProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h]
  have hh := congrArg (fun xs : List (List Str) => serializeWords (xs.map serializeWords))
    (compiledWords (F.gates n))
  simp only [List.map_map, Function.comp_def] at hh
  rw [hh]
  simp only [serializeWords_eq, encFamilyAt, ReversibleFamily.compile, encCirc, List.append_assoc]
  rfl

end InfoLossLAR.WorstCase

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule5

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanGate

theorem assign_other {n : ℕ} (g : BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _

theorem compile_length {n : ℕ} (g : BooleanGate n) : g.compile.length ≤ 2 := by
  cases g <;> simp only [compile] <;> (try split_ifs) <;> simp

theorem compile_action {n : ℕ} (g : BooleanGate n) (x : Bits n)
    (hz : x g.target = false) : reversibleAction g.compile x = g.assign x := by
  cases g with
  | constant t b =>
    cases b <;> simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | copy s t h =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
  | negate s t h =>
    funext i
    by_cases hi : i = t
    · subst i
      cases hv : x s <;>
        simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
          Function.update_of_ne h]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
        Function.update_of_ne hi]
  | xor a b t ha hb =>
    simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value,
      Function.update_of_ne hb]
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]
    · simp_all [compile, reversibleAction, ReversibleGate.equiv, ReversibleGate.act, assign, target, value]

end BooleanGate

theorem reversibleAction_append {n : ℕ} (a b : List (ReversibleGate n)) :
    reversibleAction (a ++ b) = (reversibleAction a).trans (reversibleAction b) := by
  induction a with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, reversibleAction, ih]
    rfl

/-- Complete Boolean-program semantics, with all intermediate values retained. -/
theorem booleanToReversible_action {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (x : Bits n)
    (hz : ∀ g ∈ gates, x g.target = false) :
    reversibleAction (booleanToReversible gates) x = booleanRun gates x := by
  induction gates generalizing x with
  | nil => rfl
  | cons g gates ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hf
    have hzero : ∀ h ∈ gates, g.assign x h.target = false := by
      intro h hh
      rw [g.assign_other x h.target (Ne.symm (hhead h hh))]
      exact hz h (by simp [hh])
    change reversibleAction (g.compile ++ booleanToReversible gates) x = _
    rw [reversibleAction_append]
    change reversibleAction (booleanToReversible gates) (reversibleAction g.compile x) = _
    rw [g.compile_action x (hz g (by simp)), ih htail _ hzero]
    rfl

theorem booleanToReversible_length {n : ℕ} (gates : List (BooleanGate n)) :
    (booleanToReversible gates).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp [booleanToReversible]
  | cons g gates ih =>
    have hg := g.compile_length
    change (g.compile ++ booleanToReversible gates).length ≤ _
    simp only [List.length_append, List.length_cons]
    omega

theorem booleanCircuit_depth {n : ℕ} (gates : List (BooleanGate n)) :
    depth (compileReversible (booleanToReversible gates)) ≤ 74 * gates.length := by
  have h := (compileReversible_depth (booleanToReversible gates)).trans
    (Nat.mul_le_mul_left 37 (booleanToReversible_length gates))
  omega

end InfoLossLAR.WorstCase

end P2MDyadicModule5

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem leftRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    leftRegister (Function.update state (Fin.castAdd m wire) bit)=Function.update (leftRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [leftRegister]
  · have he : Fin.castAdd m index ≠ Fin.castAdd m wire := fun hh => h (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) hh))
    simp [leftRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem rightRegister_update_left {n m : ℕ} (state : Bits (n+m)) (wire : Fin n) (bit : Bool) :
    rightRegister (Function.update state (Fin.castAdd m wire) bit)=rightRegister state := by
  funext index
  have he : Fin.natAdd n index ≠ Fin.castAdd m wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := wire.isLt
    omega
  simp [rightRegister,Function.update_of_ne he]

private theorem leftRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    leftRegister (Function.update state (Fin.natAdd n wire) bit)=leftRegister state := by
  funext index
  have he : Fin.castAdd m index ≠ Fin.natAdd n wire := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    have hi := index.isLt
    omega
  simp [leftRegister,Function.update_of_ne he]

private theorem rightRegister_update_right {n m : ℕ} (state : Bits (n+m)) (wire : Fin m) (bit : Bool) :
    rightRegister (Function.update state (Fin.natAdd n wire) bit)=Function.update (rightRegister state) wire bit := by
  funext index
  by_cases h : index=wire
  · subst index
    simp [rightRegister]
  · have he : Fin.natAdd n index ≠ Fin.natAdd n wire := by
      intro hh
      exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val hh)))
    simp [rightRegister,Function.update_of_ne h,Function.update_of_ne he]

private theorem apply1_left_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin n)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.castAdd m wire) (tensorState first second)=tensorState (apply1 matrix wire first) second := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_left,rightRegister_update_left]
  change (∑ bit,matrix (leftRegister state wire) bit*
    (first (Function.update (leftRegister state) wire bit)*second (rightRegister state))) =
      (∑ bit,matrix (leftRegister state wire) bit*first (Function.update (leftRegister state) wire bit))*
        second (rightRegister state)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro bit _
  ring

private theorem apply1_right_tensor {n m : ℕ} (matrix : Matrix Bool Bool ℂ) (wire : Fin m)
    (first : QState n) (second : QState m) :
    apply1 matrix (Fin.natAdd n wire) (tensorState first second)=tensorState first (apply1 matrix wire second) := by
  funext state
  simp only [apply1,tensorState,leftRegister_update_right,rightRegister_update_right]
  change (∑ bit,matrix (rightRegister state wire) bit*
    (first (leftRegister state)*second (Function.update (rightRegister state) wire bit))) =
      first (leftRegister state)*
        (∑ bit,matrix (rightRegister state wire) bit*second (Function.update (rightRegister state) wire bit))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bit _
  ring

/-- All five actual Clifford+T gate constructors act on their designated
left register and leave the other register untouched. -/
theorem leftInstruction_tensor {n m : ℕ} (gate : Instr n) (first : QState n) (second : QState m) :
    (leftInstruction gate).apply (tensorState first second)=tensorState (gate.apply first) second := by
  cases gate with
  | h wire => exact apply1_left_tensor hMat wire first second
  | s wire => exact apply1_left_tensor sMat wire first second
  | t wire => exact apply1_left_tensor tMat wire first second
  | x wire => exact apply1_left_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [leftInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_left,rightRegister_update_left]
    rfl

/-- The same exact gate semantics for the right physical register. -/
theorem rightInstruction_tensor {n m : ℕ} (gate : Instr m) (first : QState n) (second : QState m) :
    (rightInstruction gate).apply (tensorState first second)=tensorState first (gate.apply second) := by
  cases gate with
  | h wire => exact apply1_right_tensor hMat wire first second
  | s wire => exact apply1_right_tensor sMat wire first second
  | t wire => exact apply1_right_tensor tMat wire first second
  | x wire => exact apply1_right_tensor xMat wire first second
  | cnot control target hct =>
    funext state
    simp only [rightInstruction,Instr.apply,cnotState,tensorState,leftRegister_update_right,rightRegister_update_right]
    rfl

private theorem leftLayer_tensor {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map leftInstruction) (tensorState first second)=tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [leftInstruction_tensor]
    exact ih (gate.apply first)

private theorem rightLayer_tensor {n m : ℕ} (layer : List (Instr m)) (first : QState n) (second : QState m) :
    runLayer (layer.map rightInstruction) (tensorState first second)=tensorState first (runLayer layer second) := by
  induction layer generalizing second with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [rightInstruction_tensor]
    exact ih (gate.apply second)

theorem leftCircuit_tensor {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (leftCircuit circuit) (tensorState first second)=tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [leftLayer_tensor]
    exact ih (runLayer layer first)

theorem rightCircuit_tensor {n m : ℕ} (circuit : Layered m) (first : QState n) (second : QState m) :
    runLayered (rightCircuit circuit) (tensorState first second)=tensorState first (runLayered circuit second) := by
  induction circuit generalizing second with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [rightCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [rightLayer_tensor]
    exact ih (runLayer layer second)

/-- Two real circuits on disjoint registers have exactly their product action. -/
theorem disjointCircuits_tensor {n m : ℕ} (left : Layered n) (right : Layered m)
    (first : QState n) (second : QState m) :
    runLayered (leftCircuit left++rightCircuit right) (tensorState first second)=
      tensorState (runLayered left first) (runLayered right second) := by
  rw [runLayered,List.foldl_append]
  change runLayered (rightCircuit right) (runLayered (leftCircuit left) (tensorState first second)) = _
  rw [leftCircuit_tensor,rightCircuit_tensor]

private theorem left_support_disjoint {n m : ℕ} (first second : Instr n)
    (h : Disjoint first.support second.support) :
    Disjoint (leftInstruction (m := m) first).support (leftInstruction second).support := by
  rw [leftInstruction_support,leftInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (congrArg (fun k : Fin (n+m) => k.val) he)
  subst b
  exact Finset.disjoint_left.mp h ha hb

private theorem right_support_disjoint {n m : ℕ} (first second : Instr m)
    (h : Disjoint first.support second.support) :
    Disjoint (rightInstruction (n := n) first).support (rightInstruction second).support := by
  rw [rightInstruction_support,rightInstruction_support]
  apply Finset.disjoint_left.mpr
  intro index hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have hab : b=a := Fin.ext (Nat.add_left_cancel (congrArg Fin.val he))
  subst b
  exact Finset.disjoint_left.mp h ha hb

theorem leftLayer_ok {n m : ℕ} (layer : List (Instr n)) (h : LayerOk layer) :
    LayerOk (layer.map (leftInstruction (m := m))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => left_support_disjoint _ _ hab)

theorem rightLayer_ok {n m : ℕ} (layer : List (Instr m)) (h : LayerOk layer) :
    LayerOk (layer.map (rightInstruction (n := n))) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hab => right_support_disjoint _ _ hab)

theorem leftCircuit_wellFormed {n m : ℕ} (circuit : Layered n)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ leftCircuit (m := m) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact leftLayer_ok original (h original ho)

theorem rightCircuit_wellFormed {n m : ℕ} (circuit : Layered m)
    (h : ∀ layer ∈ circuit,LayerOk layer) : ∀ layer ∈ rightCircuit (n := n) circuit,LayerOk layer := by
  intro layer hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hl
  exact rightLayer_ok original (h original ho)

/-- A real compiled reversible circuit pulls each output event back along
its exact classical permutation, for arbitrary superpositions and garbage. -/
theorem reversibleCircuit_event_probability {n : ℕ} (gates : List (ReversibleGate n))
    (state : QState n) (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (compileReversible gates) state output‖^2 else 0)=
      ∑ input : Bits n,if event (reversibleAction gates input) then ‖state input‖^2 else 0 := by
  rw [compileReversible_apply]
  have h := (reversibleAction gates).sum_comp (fun output : Bits n =>
    if event output then ‖state ((reversibleAction gates).symm output)‖^2 else 0)
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- Fresh Boolean output selection has its exact classical event semantics
on quantum states supported on zero scratch inputs. -/
theorem booleanCircuit_event_probability {n : ℕ} (gates : List (BooleanGate n))
    (hf : BooleanFresh gates) (state : QState n)
    (hz : ∀ input,state input ≠ 0 → ∀ gate ∈ gates,input gate.target=false)
    (event : Bits n → Bool) :
    (∑ output : Bits n,if event output then
      ‖runLayered (compileReversible (booleanToReversible gates)) state output‖^2 else 0)=
      ∑ input : Bits n,if event (booleanRun gates input) then ‖state input‖^2 else 0 := by
  rw [reversibleCircuit_event_probability]
  apply Finset.sum_congr rfl
  intro input _
  by_cases he : state input=0
  · simp [he]
  · rw [booleanToReversible_action gates hf input (hz input he)]

end InfoLossLAR.WorstCase

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readBooleanInstruction_poly : Poly readBooleanInstruction := by
  unfold readBooleanInstruction
  fun_prop

theorem readBooleanInstruction_rest_length (xs : Str) :
    (readBooleanInstruction xs).1.length ≤ xs.length := by
  unfold readBooleanInstruction
  dsimp only
  split_ifs <;>
    first
      | exact (readUnary_rest_length _).trans (readUnary_rest_length _)
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans (readUnary_rest_length _))
      | exact (readUnary_rest_length _).trans ((readUnary_rest_length _).trans
          ((readUnary_rest_length _).trans (readUnary_rest_length _)))

private theorem unaryWidth_append (n : ℕ) (xs : Str) : inputWidth (encNat n ++ xs) = n := by
  simpa only [encNat, List.append_assoc, List.singleton_append] using inputWidth_prefix n xs

private theorem unaryWidth (n : ℕ) : inputWidth (encNat n) = n := by
  simpa using unaryWidth_append n []

theorem readBooleanInstruction_append {n : ℕ} (g : BooleanGate n) (xs : Str) :
    readBooleanInstruction (g.code ++ xs) = (xs, g.compile.map ReversibleGate.code) := by
  cases g with
  | constant t b =>
    cases b <;> simp only [BooleanGate.code, Bool.false_eq_true, ite_false, ite_true,
      readBooleanInstruction, List.append_assoc, readUnary_append, unaryWidth_append] <;> norm_num <;> rfl
  | copy s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | negate s t h =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | xor a b t ha hb =>
    simp only [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
      unaryWidth_append] <;> norm_num <;> rfl
  | and a b t ha hb =>
    by_cases hab : a = b
    · subst b
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code]
    · have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simp [BooleanGate.code, readBooleanInstruction, List.append_assoc, readUnary_append,
        unaryWidth_append, unaryWidth, BooleanGate.compile, ReversibleGate.code, hab, habv]

@[fun_prop] theorem readBooleanProgram_poly : Poly readBooleanProgram :=
  readList_poly readBooleanInstruction readBooleanInstruction_poly readBooleanInstruction_rest_length

theorem readBooleanProgram_append {n : ℕ} (gates : List (BooleanGate n)) (xs : Str) :
    readBooleanProgram (encStr (gates.map BooleanGate.code) ++ xs) =
      (xs, gates.map (fun g => g.compile.map ReversibleGate.code)) :=
  readList_append_mapped readBooleanInstruction BooleanGate.code
    (fun g => g.compile.map ReversibleGate.code) readBooleanInstruction_append gates xs

@[fun_prop] theorem compileBooleanDescription_poly : Poly compileBooleanDescription := by
  unfold compileBooleanDescription
  have hf : Poly (List.flatten : List (List Str) → List Str) :=
    ⟨PolyProgram.listFlatten (encodeList encodeBool) []⟩
  fun_prop

theorem compileBooleanDescription_code (F : BooleanFamily) (n : ℕ) :
    compileBooleanDescription (F.code n) = F.reversible.code n := by
  unfold BooleanFamily.code compileBooleanDescription
  simp only [List.append_assoc, readUnary_append]
  have h := readBooleanProgram_append (F.gates n) []
  simp only [List.append_nil] at h
  rw [h, serializeWords_eq]
  have hh : (List.map (fun g => List.map ReversibleGate.code g.compile) (F.gates n)).flatten =
      (booleanToReversible (F.gates n)).map ReversibleGate.code := by
    simp only [booleanToReversible, List.flatMap_def, List.map_flatten, List.map_map, Function.comp_def]
  rw [hh]
  simp only [ReversibleFamily.code, BooleanFamily.reversible, List.append_assoc]

end InfoLossLAR.WorstCase

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule8

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanOp

theorem toGate_target {total : ℕ} (op : BooleanOp) (target : Fin total) :
    (op.toGate target).target = target := by
  cases op <;> simp only [toGate] <;> (try split_ifs) <;> rfl

theorem toGate_value {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).value (fun i => s i.val) = op.eval s := by
  cases op <;> simp_all [Valid, sources, toGate, BooleanGate.value, eval]

theorem toGate_assign {total : ℕ} (op : BooleanOp) (target : Fin total)
    (hv : op.Valid target.val) (s : ℕ → Bool) :
    (op.toGate target).assign (fun i => s i.val) = fun i => op.assign target.val s i.val := by
  funext i
  rw [BooleanGate.assign, toGate_target, toGate_value op target hv]
  by_cases hi : i = target
  · subst i; simp [assign]
  · have hval : i.val ≠ target.val := fun h => hi (Fin.ext h)
    simp [assign, Function.update_of_ne hi, Function.update_of_ne hval]

end BooleanOp

namespace BooleanProgram

theorem target_range {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (g : BooleanGate total) (hg : g ∈ gates start ops h) :
    start ≤ g.target.val ∧ g.target.val < start + ops.length := by
  induction ops generalizing start with
  | nil => simp [gates] at hg
  | cons op rest ih =>
    simp only [gates, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [BooleanOp.toGate_target, List.length_cons]; omega
    · have hh := ih (start := start + 1) _ hg
      simp only [List.length_cons]; omega

theorem fresh {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) : BooleanFresh (gates start ops h) := by
  induction ops generalizing start with
  | nil => exact List.Pairwise.nil
  | cons op rest ih =>
    apply List.pairwise_cons.2
    constructor
    · intro g hg heq
      have hh := (target_range rest _ g hg).1
      rw [BooleanOp.toGate_target] at heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_mk] at hv
      omega
    · exact ih _

theorem run_below (start : ℕ) (ops : List BooleanOp) (s : ℕ → Bool)
    (i : ℕ) (hi : i < start) : run start ops s i = s i := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    rw [run, ih (start + 1) (op.assign start s) (by omega)]
    exact Function.update_of_ne (by omega) _ _

theorem run_append (start : ℕ) (a b : List BooleanOp) (s : ℕ → Bool) :
    run start (a ++ b) s = run (start + a.length) b (run start a s) := by
  induction a generalizing start s with
  | nil => simp [run]
  | cons op a ih =>
    simp only [List.cons_append, run, ih, List.length_cons]
    rw [show start + 1 + a.length = start + (a.length + 1) by omega]

theorem semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool) :
    booleanRun (gates start ops h) (fun i => s i.val) = fun i => run start ops s i.val := by
  induction ops generalizing start s with
  | nil => rfl
  | cons op rest ih =>
    change booleanRun (gates (start + 1) rest _) ((op.toGate _).assign (fun i => s i.val)) = _
    rw [BooleanOp.toGate_assign op _ hv.1, ih _ hv.2]
    rfl

theorem reversible_semantics {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    reversibleAction (booleanToReversible (gates start ops h)) (fun i => s i.val) =
      fun i => run start ops s i.val := by
  rw [booleanToReversible_action _ (fresh ops h)]
  · exact semantics ops h hv s
  · intro g hg
    obtain ⟨hl, hu⟩ := target_range ops h g hg
    exact hz _ hl hu

/-- The literal Clifford+T implementation has exactly the fresh-program basis semantics. -/
theorem circuit_basis {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) (hv : Valid start ops) (s : ℕ → Bool)
    (hz : ∀ i, start ≤ i → i < start + ops.length → s i = false) :
    runLayered (compileReversible (booleanToReversible (gates start ops h)))
      (fun x => if x = (fun i => s i.val) then (1 : ℂ) else 0) =
        fun x => if x = (fun i => run start ops s i.val) then 1 else 0 := by
  rw [compileReversible_basis, reversible_semantics ops h hv s hz]

theorem circuit_depth {total start : ℕ} (ops : List BooleanOp)
    (h : start + ops.length ≤ total) :
    depth (compileReversible (booleanToReversible (gates start ops h))) ≤ 74 * ops.length := by
  simpa only [gates_length] using booleanCircuit_depth (gates start ops h)

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem eval_congr {bound : ℕ} (e : BooleanExpr) (hv : e.Valid bound)
    {s t : ℕ → Bool} (h : ∀ i, i < bound → s i = t i) : e.eval s = e.eval t := by
  induction e with
  | input i => exact h i hv
  | constant b => rfl
  | negate a ih => exact congrArg Bool.not (ih hv)
  | xor a b ia ib => exact congrArg₂ Bool.xor (ia hv.1) (ib hv.2)
  | and a b ia ib => exact congrArg₂ Bool.and (ia hv.1) (ib hv.2)

private theorem singleton_at (start : ℕ) (op : BooleanOp) (s : ℕ → Bool) :
    BooleanProgram.run start [op] s start = op.eval s := by
  simp [BooleanProgram.run, BooleanOp.assign]

private theorem append_singleton_at (start : ℕ) (ops : List BooleanOp) (op : BooleanOp)
    (s : ℕ → Bool) :
    BooleanProgram.run start (ops ++ [op]) s (start + ops.length) =
      op.eval (BooleanProgram.run start ops s) := by
  rw [BooleanProgram.run_append, singleton_at]

theorem compile_eval (e : BooleanExpr) (start : ℕ) (hv : e.Valid start) (s : ℕ → Bool) :
    BooleanProgram.run start (e.compile start).1 s (e.compile start).2 = e.eval s := by
  induction e generalizing start s with
  | input i => rfl
  | constant b => exact singleton_at start (.constant b) s
  | negate a ih =>
    simp only [compile, append_singleton_at, BooleanOp.eval, eval]
    rw [ih start hv]
  | xor a b ia ib | and a b ia ib =>
    have hca := (a.compile_valid start hv.1).2
    have hcb := b.valid_mono hv.2 (Nat.le_add_right start a.size)
    have hb := ib (start + a.size) hcb (BooleanProgram.run start (a.compile start).1 s)
    have heq : b.eval (BooleanProgram.run start (a.compile start).1 s) = b.eval s :=
      b.eval_congr hv.2 (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [heq] at hb
    simp only [compile, compile_length]
    rw [show start + a.size + b.size = start +
      ((a.compile start).1 ++ (b.compile (start + a.size)).1).length by simp; omega,
      append_singleton_at, BooleanProgram.run_append]
    simp only [BooleanOp.eval, compile_length, eval]
    rw [BooleanProgram.run_below _ _ _ _ hca, ia start hv.1, hb]

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

namespace BooleanExpr

theorem lookup_eval {α : Type} [Fintype α] [DecidableEq α]
    (table : α → Bool) (inputs : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (inputs a).eval s = decide (a = actual)) :
    (lookup table inputs).eval s = table actual := by
  rw [Bool.eq_iff_iff]
  simp only [lookup, eval_any_true, List.mem_map, List.mem_filter,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, he⟩
    have heq : a = actual := by simpa only [h, decide_eq_true_eq] using he
    simpa only [heq] using ha
  · intro ha
    exact ⟨inputs actual, ⟨actual, ha, rfl⟩, by simp [h]⟩

theorem compileMany_eval (start : ℕ) (es : List BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) (s : ℕ → Bool) :
    (compileMany start es).2.map (BooleanProgram.run start (compileMany start es).1 s) =
      es.map (fun e => e.eval s) := by
  induction es generalizing start s with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hout := (e.compile_valid start he).2
    have ht := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
      (BooleanProgram.run start (e.compile start).1 s)
    have href : es.map (fun a => a.eval (BooleanProgram.run start (e.compile start).1 s)) =
        es.map (fun a => a.eval s) := by
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr (h a (by simp [ha])) (fun i hi => BooleanProgram.run_below _ _ _ i hi)
    rw [href] at ht
    simp only [compileMany, compile_length, List.map_cons, BooleanProgram.run_append]
    rw [BooleanProgram.run_below _ _ _ _ hout, e.compile_eval start he, ht]

theorem multiplex_eval {α : Type} [Fintype α] [DecidableEq α]
    (control payload : α → BooleanExpr) (s : ℕ → Bool) (actual : α)
    (h : ∀ a, (control a).eval s = decide (a = actual)) :
    (multiplex control payload).eval s = (payload actual).eval s := by
  rw [Bool.eq_iff_iff]
  simp only [multiplex, eval_any_true, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, he⟩
    simp only [eval, Bool.and_eq_true, h, decide_eq_true_eq] at he
    simpa only [he.1] using he.2
  · intro hp
    exact ⟨.and (control actual) (payload actual), ⟨actual, rfl⟩, by simp [eval, h, hp]⟩

end BooleanExpr

end InfoLossLAR.WorstCase

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace Symbolic

variable {width : ℕ}

theorem load_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → σ) :
    Encodes (sym.load f) {cfg with var := f cfg.var} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem push_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K) (f : σ → Bool) :
    Encodes (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [push, Function.update_self, ↓reduceIte]
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceDIte, List.getElem?_cons_zero]
      exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state
    · simp only [hi, ↓reduceDIte]
      rw [h.stack]
      congr 1
      have he : i.val = (i.val - 1) + 1 := by omega
      conv_rhs => rw [he]
      simp only [List.getElem?_cons_succ]
  · simpa only [push, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem read_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) :
    Encodes (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?} bits := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply BooleanExpr.lookup_eval _ _ _ (cfg.var, (cfg.stk k).head?)
  intro a
  simp only [BooleanExpr.eval, h.state, h.stack]
  simp [Prod.ext_iff, List.head?_eq_getElem?]

theorem pop_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (k : K)
    (hsize : (cfg.stk k).length ≤ width) :
    Encodes (sym.pop k) {cfg with stk := Function.update cfg.stk k (cfg.stk k).tail} bits := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  by_cases hj : j = k
  · subst j
    simp only [pop, Function.update_self, ↓reduceIte]
    by_cases hi : i.val + 1 < width
    · simp only [hi, ↓reduceDIte, h.stack]
      congr 1
      simp
    · simp only [hi, ↓reduceDIte, BooleanExpr.eval]
      have he : (cfg.stk k).tail[i.val]? = none :=
        List.getElem?_eq_none (by simp only [List.length_tail]; omega)
      rw [he]
  · simpa only [pop, hj, ↓reduceIte, Function.update_of_ne hj] using h.stack j i b

theorem jump_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) (f : σ → Λ) :
    Encodes (sym.jump f) {cfg with l := some (f cfg.var)} bits := by
  refine ⟨?_, h.state, h.stack⟩
  intro l
  exact BooleanExpr.lookup_eval _ _ _ cfg.var h.state

theorem halt_encodes (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ)
    (bits : ℕ → Bool) (h : Encodes sym cfg bits) :
    Encodes sym.halt {cfg with l := none} bits := ⟨fun _ => rfl, h.state, h.stack⟩

theorem select_encodes (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (cfgA cfgB : Configuration K Λ σ) (bits : ℕ → Bool)
    (ha : Encodes a cfgA bits) (hb : Encodes b cfgB bits) :
    Encodes (select condition a b) (if condition.eval bits then cfgA else cfgB) bits := by
  cases hc : condition.eval bits
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, Bool.false_eq_true, ↓reduceIte] using hb.stack k i b
  · refine ⟨?_, ?_, ?_⟩
    · intro l; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.label l
    · intro v; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.state v
    · intro k i b; simpa only [select, BooleanExpr.eval_select, hc, ↓reduceIte] using ha.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

/-- The stack-size premise is precisely the allocated capacity, including all pushes in this step. -/
theorem auxiliary_encodes (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + pushBound q ≤ width) :
    Encodes (auxiliary hw q sym) (TM2.stepAux q cfg.var cfg.stk) bits := by
  induction q generalizing sym cfg with
  | push k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (f cfg.var :: cfg.stk k)) ≤ stackSize cfg.stk + 1 :=
      stackSize_update_le cfg.stk k _ _ (Nat.le_add_right _ _)
        (by simpa only [List.length_cons] using Nat.succ_le_succ (length_le_stackSize cfg.stk k))
    exact ih (sym.push k f) {cfg with stk := Function.update cfg.stk k (f cfg.var :: cfg.stk k)}
      (sym.push_encodes cfg bits h k f) (by simp only [pushBound] at hsize; dsimp only; omega)
  | peek k f q ih =>
    exact ih (sym.read hw k f) {cfg with var := f cfg.var (cfg.stk k).head?}
      (sym.read_encodes cfg bits h hw k f) hsize
  | pop k f q ih =>
    have hs : stackSize (Function.update cfg.stk k (cfg.stk k).tail) ≤ stackSize cfg.stk :=
      stackSize_update_le cfg.stk k _ _ le_rfl
        (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (length_le_stackSize cfg.stk k))
    have hr := sym.read_encodes cfg bits h hw k f
    have hp := (sym.read hw k f).pop_encodes {cfg with var := f cfg.var (cfg.stk k).head?}
      bits hr k ((length_le_stackSize cfg.stk k).trans (by simp only [pushBound] at hsize; omega))
    exact ih ((sym.read hw k f).pop k)
      {cfg with var := f cfg.var (cfg.stk k).head?, stk := Function.update cfg.stk k (cfg.stk k).tail}
      hp (by simp only [pushBound] at hsize; dsimp only; omega)
  | load f q ih =>
    exact ih (sym.load f) {cfg with var := f cfg.var} (sym.load_encodes cfg bits h f) hsize
  | branch f q r iq ir =>
    have hq := iq sym cfg h (by simp only [pushBound] at hsize; have := le_max_left (pushBound q) (pushBound r); omega)
    have hr := ir sym cfg h (by simp only [pushBound] at hsize; have := le_max_right (pushBound q) (pushBound r); omega)
    have he := Symbolic.select_encodes (BooleanExpr.lookup f sym.state)
      (auxiliary hw q sym) (auxiliary hw r sym) _ _ bits hq hr
    rw [BooleanExpr.lookup_eval f sym.state bits cfg.var h.state] at he
    cases hf : f cfg.var <;> simpa only [auxiliary, TM2.stepAux, hf, Bool.cond_false,
      Bool.cond_true, Bool.false_eq_true, ↓reduceIte] using he
  | goto f => exact sym.jump_encodes cfg bits h f
  | halt => exact sym.halt_encodes cfg bits h

theorem multiplex_encodes {α : Type} [Fintype α] [DecidableEq α]
    (control : α → BooleanExpr) (choices : α → Symbolic K Λ σ width)
    (bits : ℕ → Bool) (actual : α) (cfg : Configuration K Λ σ)
    (hc : ∀ a, (control a).eval bits = decide (a = actual))
    (h : Encodes (choices actual) cfg bits) : Encodes (multiplex control choices) cfg bits := by
  constructor
  · intro l
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.label l
  · intro v
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.state v
  · intro k i b
    rw [multiplex, BooleanExpr.multiplex_eval control _ bits actual hc]
    exact h.stack k i b

theorem transition_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (h : Encodes sym cfg bits) (hsize : stackSize cfg.stk + programPushBound program ≤ width) :
    Encodes (transition hw program sym) (stickyStep program cfg) bits := by
  apply multiplex_encodes sym.label _ bits cfg.l _ h.label
  cases hl : cfg.l with
  | none => simpa only [hl, Option.elim_none, stickyStep] using h
  | some l =>
    have hq : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [hl, Option.elim_some, stickyStep] using
      auxiliary_encodes hw (program l) sym cfg bits h (by omega)

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.BooleanExpr

theorem size_any_le (es : List BooleanExpr) (bound : ℕ)
    (h : ∀ e ∈ es, e.size ≤ bound) : (any es).size ≤ (bound + 4) * es.length + 1 := by
  induction es with
  | nil => simp [any, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [any, size_or, List.length_cons]
    nlinarith

theorem size_lookup_le {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → BooleanExpr) (bound : ℕ)
    (h : ∀ a, (inputs a).size ≤ bound) :
    (lookup table inputs).size ≤ (bound + 4) * Fintype.card α + 1 := by
  have he := size_any_le ((Finset.univ.toList.filter table).map inputs) bound (by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
    exact h a)
  have hl : (Finset.univ.toList.filter table).length ≤ Fintype.card α := by
    simpa only [Finset.length_toList, Finset.card_univ] using
      List.length_filter_le table (Finset.univ.toList : List α)
  simp only [List.length_map] at he
  simpa only [lookup] using he.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) 1)

theorem size_multiplex_le {α : Type} [Fintype α]
    (control payload : α → BooleanExpr) (controlBound payloadBound : ℕ)
    (hc : ∀ a, (control a).size ≤ controlBound)
    (hp : ∀ a, (payload a).size ≤ payloadBound) :
    (multiplex control payload).size ≤
      (controlBound + payloadBound + 5) * Fintype.card α + 1 := by
  have he := size_any_le (Finset.univ.toList.map (fun a => and (control a) (payload a)))
    (controlBound + payloadBound + 1) (by
      intro e he
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
      simp only [size]
      have := hc a
      have := hp a
      omega)
  simpa only [multiplex, List.length_map, Finset.length_toList, Finset.card_univ, Nat.add_assoc]
    using he

end InfoLossLAR.WorstCase.BooleanExpr

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

end Symbolic

namespace Symbolic

/-- Each output reference evaluates to the formula it replaces after fresh compilation. -/
theorem output_eval (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (bits : ℕ → Bool) (i : Slot K Λ σ width) :
    BooleanProgram.run start (sym.compiled start).1 bits (sym.output start i) = (sym.get i).eval bits := by
  have he := BooleanExpr.compileMany_eval start sym.formulas (sym.formulas_valid h) bits
  have hi := congrArg (fun xs : List Bool => xs[(slotEquiv K Λ σ width i).val]?) he
  simp only [List.getElem?_map] at hi
  have ho : (sym.compiled start).2[(slotEquiv K Λ σ width i).val]? = some (sym.output start i) :=
    List.getElem?_eq_getElem _
  change (sym.compiled start).2[(slotEquiv K Λ σ width i).val]?.map
    (BooleanProgram.run start (sym.compiled start).1 bits) = _ at hi
  rw [ho] at hi
  simp only [formulas, List.getElem?_ofFn, dif_pos (slotEquiv K Λ σ width i).isLt,
    Fin.eta, Equiv.symm_apply_apply, Option.map_some, Option.some.injEq] at hi
  exact hi

theorem rebound_encodes (sym : Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (cfg : Configuration K Λ σ) (bits : ℕ → Bool) (he : Encodes sym cfg bits) :
    Encodes (sym.rebound start) cfg (BooleanProgram.run start (sym.compiled start).1 bits) := by
  constructor
  · intro l
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inl l)]
    exact he.label l
  · intro v
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inl v))]
    exact he.state v
  · intro k i b
    rw [rebound, ofSlots, BooleanExpr.eval, output_eval sym start h bits (.inr (.inr (k, i, b)))]
    exact he.stack k i b

end Symbolic

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem step_poly : Poly (fun x : State × Token => step x.1 x.2) := by
  unfold step emit
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open Polynomial

theorem Bounded.mono {N M : ℕ} {s : State} (h : Bounded N s) (hm : N ≤ M) :
    Bounded M s := by
  exact ⟨h.slots.trans hm, h.operands.trans hm, h.nodes.trans hm,
    fun x hx => (h.refs x hx).trans hm,
    fun x hx => ⟨(h.code x hx).1.trans hm, (h.code x hx).2.1.trans hm,
      (h.code x hx).2.2.trans hm⟩⟩

theorem getD_bound (xs : List ℕ) (i N : ℕ) (h : ∀ x ∈ xs, x.bits.length ≤ N) :
    ((xs[i]?).getD 0).bits.length ≤ N := by
  by_cases hi : i < xs.length
  · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (show xs.length ≤ i by omega)]
    simp

theorem emit_bounded {N : ℕ} {s : State} (h : Bounded N s) (x : Node)
    (hx : NodeBound (N+1) x) (rest : List ℕ) (hl : rest.length ≤ N)
    (hr : ∀ a ∈ rest, a.bits.length ≤ N+1) : Bounded (N+1) (emit s x rest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [emit] using Nat.add_le_add_right h.slots 1
  · simpa [emit] using Nat.add_le_add_right hl 1
  · simpa [emit] using Nat.add_le_add_right h.nodes 1
  · intro a ha
    simp only [emit, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (Nat.add_le_add_right h.slots 1)
    · exact hr a ha
  · intro a ha
    simp only [emit, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact (h.mono (Nat.le_succ N)).code a ha
    · exact hx

theorem step_bounded {N : ℕ} {s : State} (h : Bounded N s) (hN : 3 ≤ N)
    (token : Token) (ht : token.2.bits.length ≤ N+1) : Bounded (N+1) (step s token) := by
  have hh := h.mono (Nat.le_succ N)
  have h0 := getD_bound s.2.1 0 (N+1) hh.refs
  have h1 := getD_bound s.2.1 1 (N+1) hh.refs
  have tailLen : s.2.1.tail.length ≤ N := by rw [List.length_tail]; exact (Nat.sub_le _ _).trans h.operands
  have tailTailLen : s.2.1.tail.tail.length ≤ N :=
    by rw [List.length_tail]; omega
  have tailRefs : ∀ a ∈ s.2.1.tail, a.bits.length ≤ N+1 :=
    fun a ha => hh.refs a (List.mem_of_mem_tail ha)
  have tailTailRefs : ∀ a ∈ s.2.1.tail.tail, a.bits.length ≤ N+1 :=
    fun a ha => tailRefs a (List.mem_of_mem_tail ha)
  unfold step
  split
  · refine ⟨hh.slots, ?_, hh.nodes, ?_, hh.code⟩
    · simpa using Nat.add_le_add_right h.operands 1
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ht
      · exact hh.refs x hx
  · split
    · apply emit_bounded h _ _ _ h.operands hh.refs
      norm_num [NodeBound]
    · split
      · apply emit_bounded h _ _ _ h.operands hh.refs
        norm_num [NodeBound]
      · split
        · apply emit_bounded h _ _ _ tailLen tailRefs
          change (3:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ 0 ≤ N+1
          rw [show (3:ℕ).bits.length = 2 by decide]
          exact ⟨by omega, h0, Nat.zero_le _⟩
        · split
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩
          · apply emit_bounded h _ _ _ tailTailLen tailTailRefs
            change (_:ℕ).bits.length ≤ N+1 ∧ _ ≤ N+1 ∧ _ ≤ N+1
            norm_num only [show (4:ℕ).bits.length = 3 by decide, show (5:ℕ).bits.length = 3 by decide]
            exact ⟨by omega, h1, h0⟩

theorem run_bounded (tokens : List Token) {N : ℕ} {s : State} (h : Bounded N s)
    (hN : 3 ≤ N) (ht : ∀ t ∈ tokens, t.2.bits.length ≤ N) :
    Bounded (N+tokens.length) (run tokens s) := by
  induction tokens generalizing N s with
  | nil => simpa [run] using h
  | cons t ts ih =>
    have hs := step_bounded h hN t ((ht t (by simp)).trans (Nat.le_succ N))
    have hh := ih hs (by omega) (fun u hu => (ht u (by simp [hu])).trans (Nat.le_succ N))
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem encodedUnit_length (xs : List Unit) : (enc xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (encodeList (fun _ : Unit => []) (x::xs)).length = _
    rw [EncodedList.cons_length]
    change (encodeList (fun _ : Unit => []) xs).length = xs.length at ih
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.length_cons]
    omega

theorem bounded_of_encoding (s : State) : Bounded (enc s).length s := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_le Nat.bits s.2.1
  have hn := EncodedList.length_le (enc : Node → List Bool) s.2.2
  have he : (enc s).length = 2*(enc s.1).length+1+2*(enc s.2.1).length+1+(enc s.2.2).length := by
    simp only [enc, Coding.encode, encodePair_length]; omega
  change s.2.1.length ≤ (enc s.2.1).length at ho
  change s.2.2.length ≤ (enc s.2.2).length at hn
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · intro x hx
    have hh := EncodedList.member_length Nat.bits s.2.1 x hx
    change x.bits.length ≤ (enc s.2.1).length at hh
    omega
  · intro x hx
    have hh := EncodedList.member_length (enc : Node → List Bool) s.2.2 x hx
    change (enc x).length ≤ (enc s.2.2).length at hh
    have he' : (enc x).length = 2*x.1.bits.length+1+2*x.2.1.bits.length+1+x.2.2.bits.length := by
      simp only [enc, Coding.encode, encodePair_length]; omega
    exact ⟨by omega, by omega, by omega⟩

theorem encoding_bound {N : ℕ} {s : State} (h : Bounded N s) :
    (enc s).length ≤ 20*(N+1)^2 := by
  have hs := encodedUnit_length s.1
  have ho := EncodedList.length_bound Nat.bits s.2.1 N h.refs
  have hn := EncodedList.length_bound (enc : Node → List Bool) s.2.2 (5*N+2) (by
    intro x hx
    have hb := h.code x hx
    rcases hb with ⟨hb1, hb2, hb3⟩
    change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) x).length ≤ _
    simp only [encodePair_length]
    omega)
  have ho' : (enc s.2.1).length ≤ N*(2*N+1) := ho.trans (Nat.mul_le_mul_right _ h.operands)
  have hn' : (enc s.2.2).length ≤ N*(2*(5*N+2)+1) := hn.trans (Nat.mul_le_mul_right _ h.nodes)
  change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) s).length ≤ _
  simp only [encodePair_length]
  nlinarith [h.slots]

theorem run_partial_bound (tokens : List Token) (s : State) (pre suf : List Token)
    (he : tokens = pre ++ suf) :
    (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2 := by
  let L := (enc (tokens,s)).length
  have heL : L = 2*(enc tokens).length+1+(enc s).length := encodePair_length _ _ _
  have hpenc : (enc pre).length ≤ (enc tokens).length := by
    change (encodeList enc pre).length ≤ (encodeList enc tokens).length
    rw [he, EncodedList.append, List.length_append]; omega
  have hplen : pre.length ≤ L := by
    have hh := EncodedList.length_le (enc : Token → List Bool) pre
    change pre.length ≤ (enc pre).length at hh
    omega
  have hs := (bounded_of_encoding s).mono (show (enc s).length ≤ L+3 by omega)
  have ht : ∀ t ∈ pre, t.2.bits.length ≤ L+3 := by
    intro t ht
    have hh := EncodedList.member_length (enc : Token → List Bool) pre t ht
    change (enc t).length ≤ (enc pre).length at hh
    have hte : (enc t).length = 2*t.1.bits.length+1+t.2.bits.length := encodePair_length _ _ _
    omega
  have hb := run_bounded pre hs (by omega) ht
  have hb' := hb.mono (show L+3+pre.length ≤ 2*L+3 by omega)
  have hh := encoding_bound hb'
  simpa [L, Nat.add_assoc] using hh

@[fun_prop] theorem run_poly : Poly (fun x : List Token × State => run x.1 x.2) := by
  apply Poly.of_program
  exact step_poly.program.listFold (0,0) (20*(2*X+4)^2) (by
    intro tokens s pre suf he
    simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X]
    change (enc (run pre s)).length ≤ 20*(2*(enc (tokens,s)).length+4)^2
    exact run_partial_bound tokens s pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace CodePoly

variable {α β : Type} [Coding α] [Coding β]

theorem comp {f : β → BooleanExpr} {g : α → β} (hf : CodePoly f) (hg : Poly g) :
    CodePoly (fun a => f (g a)) := Automatic.Poly.comp (f := fun b => code (f b)) (g := g) hf hg

theorem input {f : α → ℕ} (hf : Poly f) : CodePoly (fun a => .input (f a)) := by
  unfold CodePoly code
  fun_prop

theorem constant (b : Bool) : CodePoly (fun _ : α => .constant b) := by
  unfold CodePoly
  exact Automatic.Poly.const _

theorem negate {f : α → BooleanExpr} (hf : CodePoly f) : CodePoly (fun a => .negate (f a)) := by
  unfold CodePoly at hf ⊢
  change Poly (fun a => code (f a) ++ [(3,0)])
  fun_prop

theorem and {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => .and (f a) (g a)) := by
  unfold CodePoly at hf hg ⊢
  change Poly (fun a => code (f a) ++ code (g a) ++ [(5,0)])
  fun_prop

theorem or {f g : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => BooleanExpr.or (f a) (g a)) := by
  exact (hf.negate.and hg.negate).negate

theorem select {f g h : α → BooleanExpr} (hf : CodePoly f) (hg : CodePoly g) (hh : CodePoly h) :
    CodePoly (fun a => BooleanExpr.select (f a) (g a) (h a)) := by
  exact (hf.and hg).or (hf.negate.and hh)

theorem ite {p : α → Bool} {f g : α → BooleanExpr} (hp : Poly p)
    (hf : CodePoly f) (hg : CodePoly g) :
    CodePoly (fun a => if p a then f a else g a) := by
  change Poly (fun a => code (if p a then f a else g a))
  have he : (fun a => code (if p a then f a else g a)) =
      (fun a => if p a then code (f a) else code (g a)) := by funext a; split <;> rfl
  rw [he]
  exact Poly.ite hp hf hg

theorem any {ι : Type} (indices : List ι) (f : ι → α → BooleanExpr)
    (hf : ∀ i ∈ indices, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.any (indices.map (fun i => f i a))) := by
  induction indices with
  | nil => exact constant false
  | cons i is ih =>
    exact (hf i (by simp)).or (ih (fun j hj => hf j (by simp [hj])))

theorem lookup {ι : Type} [Fintype ι] (table : ι → Bool) (f : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) :
    CodePoly (fun a => BooleanExpr.lookup table (fun i => f i a)) :=
  any _ f (fun i _ => hf i)

theorem multiplex {ι : Type} [Fintype ι] (f g : ι → α → BooleanExpr)
    (hf : ∀ i, CodePoly (f i)) (hg : ∀ i, CodePoly (g i)) :
    CodePoly (fun a => BooleanExpr.multiplex (fun i => f i a) (fun i => g i a)) :=
  any _ _ (fun i _ => (hf i).and (hg i))

end CodePoly

@[fun_prop] theorem compileTokens_poly :
    Poly (fun x : List Token × List Unit => compileTokens x.1 x.2) := by
  unfold compileTokens
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

variable [Coding α]

theorem load_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → σ) : (sym.load f).IsPoly :=
  ⟨h.label, fun v => CodePoly.lookup _ sym.state h.state, h.stack⟩

theorem push_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Bool) :
    (sym.push k f).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [push, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2 = 0)) := by fun_prop
    have hf := CodePoly.lookup (fun v => decide (b = some (f v)))
      (fun v (x : α × ℕ) => sym.state v x.1) (fun v => (h.state v).comp (by fun_prop))
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2-1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi hf ht
  · simpa only [push, hj, ↓reduceIte] using h.stack j b

theorem read_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (k : K) (f : σ → Option Bool → σ) :
    (sym.read k f).IsPoly := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  change CodePoly (fun a => BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2)) (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0))))
  apply CodePoly.lookup
  intro u
  exact (h.state u.1).and ((h.stack k u.2).comp (by fun_prop))

theorem pop_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (width : α → ℕ)
    (hw : Poly width) (k : K) : (sym.pop width k).IsPoly := by
  refine ⟨h.label, h.state, ?_⟩
  intro j b
  by_cases hj : j = k
  · subst j
    simp only [pop, ↓reduceIte]
    have hi : Poly (fun x : α × ℕ => decide (x.2+1 < width x.1)) := by fun_prop
    have ht := (h.stack k b).comp (show Poly (fun x : α × ℕ => (x.1,x.2+1)) by fun_prop)
    simpa only [decide_eq_true_eq] using CodePoly.ite hi ht (CodePoly.constant (decide (b=none)))
  · simpa only [pop, hj, ↓reduceIte] using h.stack j b

theorem jump_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) (f : σ → Λ) : (sym.jump f).IsPoly :=
  ⟨fun l => CodePoly.lookup _ sym.state h.state, h.state, h.stack⟩

theorem halt_poly (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) : sym.halt.IsPoly :=
  ⟨fun l => CodePoly.constant (decide (l=none)), h.state, h.stack⟩

theorem select_poly (condition : α → BooleanExpr) (a b : CodeFamily K Λ σ α)
    (hc : CodePoly condition) (ha : a.IsPoly) (hb : b.IsPoly) : (select condition a b).IsPoly :=
  ⟨fun l => hc.select (ha.label l) (hb.label l),
    fun v => hc.select (ha.state v) (hb.state v),
    fun k v => (hc.comp (by fun_prop)).select (ha.stack k v) (hb.stack k v)⟩

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable [Coding α]

theorem auxiliaryCode_poly (width : α → ℕ) (hw : Poly width)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (auxiliaryCode width q sym).IsPoly := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_poly h k f)
  | peek k f q ih => exact ih _ (sym.read_poly h k f)
  | pop k f q ih => exact ih _ ((sym.read k f).pop_poly (sym.read_poly h k f) width hw k)
  | load f q ih => exact ih _ (sym.load_poly h f)
  | branch f q r iq ir =>
    exact select_poly _ _ _ (CodePoly.lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_poly h f
  | halt => exact sym.halt_poly h

theorem multiplexCode_poly {ι : Type} [Fintype ι]
    (control : ι → α → BooleanExpr) (choices : ι → CodeFamily K Λ σ α)
    (hc : ∀ i, CodePoly (control i)) (hp : ∀ i, (choices i).IsPoly) :
    (multiplexCode control choices).IsPoly :=
  ⟨fun l => CodePoly.multiplex _ _ hc (fun i => (hp i).label l),
    fun v => CodePoly.multiplex _ _ hc (fun i => (hp i).state v),
    fun k b => CodePoly.multiplex _ _ (fun i => (hc i).comp (by fun_prop)) (fun i => (hp i).stack k b)⟩

theorem transitionCode_poly (width : α → ℕ) (hw : Poly width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : CodeFamily K Λ σ α) (h : sym.IsPoly) :
    (transitionCode width program sym).IsPoly := by
  apply multiplexCode_poly _ _ h.label
  intro l
  cases l with
  | none => exact h
  | some l => exact auxiliaryCode_poly width hw (program l) sym h

end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

theorem fixed_flatMap_poly {α β ι : Type} [Coding α] [Coding β] [Inhabited β]
    (indices : List ι) (f : ι → α → List β) (hf : ∀ i ∈ indices, Poly (f i)) :
    Poly (fun a => indices.flatMap (fun i => f i a)) := by
  induction indices with
  | nil => exact Automatic.Poly.const []
  | cons i is ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    change Poly (fun a => f i a ++ is.flatMap (fun j => f j a))
    fun_prop

namespace CodeFamily

variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]

theorem codes_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width : α → List Unit) (hw : Poly width) : Poly (sym.codes width) := by
  have hlabel := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Λ)))
    (fun l a => code (sym.label l a)) (fun l _ => h.label l)
  have hstate := fixed_flatMap_poly (enumerate (Fintype.equivFin σ))
    (fun v a => code (sym.state v a)) (fun v _ => h.state v)
  have hstack : ∀ k, Poly (fun a : α =>
      (List.range (width a).length).flatMap (fun i =>
        (enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => code (sym.stack k b (a,i))))) := by
    intro k
    have hcell := fixed_flatMap_poly (enumerate (Fintype.equivFin (Option Bool)))
      (fun b (x : α × ℕ) => code (sym.stack k b x)) (fun b _ => h.stack k b)
    apply Automatic.Poly.list_flatMap hcell
    exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := width) Automatic.Poly.list_indices hw
  have hstackAll := fixed_flatMap_poly (enumerate (Fintype.equivFin K)) _ (fun k _ => hstack k)
  unfold codes
  fun_prop

theorem compile_poly [Coding α] (sym : CodeFamily K Λ σ α) (h : sym.IsPoly)
    (width slots : α → List Unit) (hw : Poly width) (hs : Poly slots) : Poly (sym.compile width slots) := by
  have hc := sym.codes_poly h width hw
  unfold compile
  fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem stickyStep_size (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : Configuration K Λ σ) :
    stackSize (stickyStep program cfg).stk ≤ stackSize cfg.stk + programPushBound program := by
  cases hl : cfg.l with
  | none => simpa only [stickyStep, hl, Option.elim_none] using Nat.le_add_right (stackSize cfg.stk) _
  | some l =>
    have hc := stepAux_stackSize_le (program l) cfg.var cfg.stk
    have hb : pushBound (program l) ≤ programPushBound program :=
      Finset.le_sup (f := fun l => pushBound (program l)) (Finset.mem_univ l)
    simpa only [stickyStep, hl, Option.elim_some] using hc.trans (Nat.add_le_add_left hb _)

/-- Full bounded execution: each step is compiled and its formula outputs are rebound to fresh wires. -/
theorem compileRun_encodes (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (cfg : Configuration K Λ σ) (bits : ℕ → Bool)
    (hv : sym.Valid start) (he : Encodes sym cfg bits)
    (hsize : stackSize cfg.stk + programPushBound program * ticks ≤ width) :
    Encodes (compileRun hw program ticks start sym).2 ((stickyStep program)^[ticks] cfg)
      (BooleanProgram.run start (compileRun hw program ticks start sym).1 bits) := by
  induction ticks generalizing start sym cfg bits with
  | zero => exact he
  | succ ticks ih =>
    have ht := transition_valid hw program sym hv
    have hcap : stackSize cfg.stk + programPushBound program ≤ width := by nlinarith
    have hs := transition_encodes hw program sym cfg bits he hcap
    have hf := (transition hw program sym).rebound_encodes start ht _ bits hs
    have hv' := (transition hw program sym).rebound_valid start ht
    have hg := stickyStep_size program cfg
    have hremaining : stackSize (stickyStep program cfg).stk + programPushBound program * ticks ≤ width := by
      nlinarith
    have hh := ih _ _ _ _ hv' hf hremaining
    simpa only [compileRun, BooleanProgram.run_append, Function.iterate_succ_apply] using hh

theorem stickyStep_of_step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (h : TM2.step program a = some b) : stickyStep program a = b := by
  rcases a with ⟨l, v, stackStore⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa only [TM2.step, Option.some.injEq, stickyStep, Option.elim_some] using h

theorem stickyStep_of_halted (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a : Configuration K Λ σ) (h : a.l = none) : stickyStep program a = a := by
  simp only [stickyStep, h, Option.elim_none]

private theorem iterate_none {α : Type} (step : α → Option α) (n : ℕ) :
    ((fun c : Option α => c.bind step)^[n]) none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih

theorem sticky_iterate_of_steps (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (steps : ℕ) (a b : Configuration K Λ σ)
    (h : ((fun c : Option (Configuration K Λ σ) => c.bind (TM2.step program))^[steps]) (some a) = some b) :
    (stickyStep program)^[steps] a = b := by
  induction steps generalizing a with
  | zero => simpa using h
  | succ steps ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : TM2.step program a with
    | none => simp only [Option.bind_some, hs, iterate_none] at h; contradiction
    | some next =>
      simp only [Option.bind_some, hs] at h
      rw [Function.iterate_succ_apply, stickyStep_of_step program a next hs]
      exact ih next h

/-- A successful machine's budget can be padded after halt without changing its output. -/
theorem sticky_iterate_of_outputs (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (a b : Configuration K Λ σ) (ticks : ℕ)
    (h : EvalsToInTime (TM2.step program) a (some b) ticks) (hb : b.l = none) :
    (stickyStep program)^[ticks] a = b := by
  have hs := sticky_iterate_of_steps program h.steps a b h.evals_in_steps
  have he : ticks = (ticks - h.steps) + h.steps := by have := h.steps_le_m; omega
  rw [he, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (stickyStep_of_halted program b hb) _

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

namespace Symbolic

theorem Bounded.mono {small big : ℕ} {sym : Symbolic K Λ σ width}
    (h : sym.Bounded small) (hle : small ≤ big) : sym.Bounded big :=
  ⟨fun l => (h.label l).trans hle, fun v => (h.state v).trans hle,
    fun k i b => (h.stack k i b).trans hle⟩

private theorem old_le_operation (bound : ℕ) : bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem lookup_le_operation (bound : ℕ) : lookupBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

private theorem read_le_operation (bound : ℕ) : readBound σ bound ≤ operationBound σ bound := by
  unfold operationBound; omega

theorem load_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → σ) :
    (sym.load f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem push_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound),
    fun v => (h.state v).trans (old_le_operation bound), ?_⟩
  intro j i b
  dsimp only [push]
  split_ifs
  · exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)
  · exact (h.stack _ _ _).trans (old_le_operation bound)

theorem read_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) :
    (sym.read hw k f).Bounded (operationBound σ bound) := by
  refine ⟨fun l => (h.label l).trans (old_le_operation bound), ?_,
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro v
  have hi : ∀ a : σ × Option Bool,
      (BooleanExpr.and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2)).size ≤ 2 * bound + 1 := by
    intro a
    simp only [BooleanExpr.size]
    have := h.state a.1
    have := h.stack k ⟨0, hw⟩ a.2
    omega
  have ht := BooleanExpr.size_lookup_le (fun a : σ × Option Bool => decide (v = f a.1 a.2)) _
    (2 * bound + 1) hi
  have hb : ((sym.read hw k f).state v).size ≤ readBound σ bound := by
    simpa only [read, readBound, Nat.add_assoc] using ht
  exact hb.trans (read_le_operation bound)

theorem pop_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound)
    (hb : 1 ≤ bound) (k : K) : (sym.pop k).Bounded bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [pop]
  split_ifs
  · exact h.stack _ _ _
  · exact hb
  · exact h.stack _ _ _

theorem jump_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) (f : σ → Λ) :
    (sym.jump f).Bounded (operationBound σ bound) := by
  refine ⟨?_, fun v => (h.state v).trans (old_le_operation bound),
    fun k i b => (h.stack k i b).trans (old_le_operation bound)⟩
  intro l
  exact (BooleanExpr.size_lookup_le _ _ bound h.state).trans (lookup_le_operation bound)

theorem halt_bounded (sym : Symbolic K Λ σ width) {bound : ℕ} (h : sym.Bounded bound) :
    sym.halt.Bounded (bound + 1) :=
  ⟨fun _ => by simp only [halt, BooleanExpr.size]; omega,
    fun v => (h.state v).trans (Nat.le_add_right _ _),
    fun k i b => (h.stack k i b).trans (Nat.le_add_right _ _)⟩

theorem select_bounded (condition : BooleanExpr) (a b : Symbolic K Λ σ width)
    (conditionBound firstBound secondBound : ℕ)
    (hc : condition.size ≤ conditionBound) (ha : a.Bounded firstBound) (hb : b.Bounded secondBound) :
    (select condition a b).Bounded (2 * conditionBound + firstBound + secondBound + 7) := by
  have hh (e f : BooleanExpr) (he : e.size ≤ firstBound) (hf : f.size ≤ secondBound) :
      (BooleanExpr.select condition e f).size ≤ 2 * conditionBound + firstBound + secondBound + 7 := by
    rw [BooleanExpr.size_select]; omega
  exact ⟨fun l => hh _ _ (ha.label l) (hb.label l),
    fun v => hh _ _ (ha.state v) (hb.state v),
    fun k i b => hh _ _ (ha.stack k i b) (hb.stack k i b)⟩

theorem compiled_length_le (sym : Symbolic K Λ σ width) (start bound : ℕ) (h : sym.Bounded bound) :
    (sym.compiled start).1.length ≤ bound * Fintype.card (Slot K Λ σ width) := by
  rw [compiled, BooleanExpr.compileMany_length]
  have hh : ∀ e ∈ sym.formulas, e.size ≤ bound := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    generalize (slotEquiv K Λ σ width).symm i = slot
    rcases slot with l | v | ⟨k, i, b⟩
    · exact h.label l
    · exact h.state v
    · exact h.stack k i b
  have sumBound : ∀ es : List BooleanExpr, (∀ e ∈ es, e.size ≤ bound) →
      (es.map BooleanExpr.size).sum ≤ es.length * bound := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
      intro hx
      have he := hx e (by simp)
      have ht := ih (fun a ha => hx a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hl := sumBound sym.formulas hh
  simpa only [formulas_length, Nat.mul_comm] using hl

end Symbolic

theorem auxiliary_bounded (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (auxiliary hw q sym).Bounded (auxiliaryBound q bound) := by
  induction q generalizing sym bound with
  | push k f q ih => exact ih _ _ (sym.push_bounded h k f)
  | peek k f q ih => exact ih _ _ (sym.read_bounded h hw k f)
  | pop k f q ih =>
    exact ih _ _ ((sym.read hw k f).pop_bounded (sym.read_bounded h hw k f)
      (by simp only [Symbolic.operationBound, Symbolic.lookupBound, Symbolic.readBound]; omega) k)
  | load f q ih => exact ih _ _ (sym.load_bounded h f)
  | branch f q r iq ir =>
    exact Symbolic.select_bounded _ _ _ _ _ _ (BooleanExpr.size_lookup_le f sym.state bound h.state)
      (iq _ _ h) (ir _ _ h)
  | goto f => exact sym.jump_bounded h f
  | halt => exact sym.halt_bounded h

theorem transition_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : Symbolic K Λ σ width) (bound : ℕ) (h : sym.Bounded bound) :
    (transition hw program sym).Bounded (transitionBound program bound) := by
  have hh : ∀ l : Option Λ,
      (l.elim sym (fun l => auxiliary hw (program l) sym)).Bounded
        (bound + Finset.univ.sup (fun l => auxiliaryBound (program l) bound)) := by
    intro l
    cases l with
    | none => exact h.mono (Nat.le_add_right _ _)
    | some l =>
      exact (auxiliary_bounded hw (program l) sym bound h).mono
        ((Finset.le_sup (f := fun l => auxiliaryBound (program l) bound) (Finset.mem_univ l)).trans
          (Nat.le_add_left _ _))
  exact ⟨fun l => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).label l),
    fun v => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).state v),
    fun k i b => BooleanExpr.size_multiplex_le _ _ _ _ h.label (fun a => (hh a).stack k i b)⟩

/-- After rebinding, every new step has constant formula size per configuration slot. -/
theorem compileRun_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).1.length ≤
      ticks * (transitionBound program 0 * Fintype.card (Slot K Λ σ width)) := by
  induction ticks generalizing start sym with
  | zero => simp [compileRun]
  | succ ticks ih =>
    have hf := (transition hw program sym).compiled_length_le start _ (transition_bounded hw program sym 0 h)
    have hr := ih (start + ((transition hw program sym).compiled start).1.length) _
      ((transition hw program sym).rebound_bounded_zero start)
    simp only [compileRun, List.length_append]
    nlinarith

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem inputCell_eval (wire : ℕ) (b : Option Bool) (bits : ℕ → Bool) :
    (inputCell wire b).eval bits = decide (b = some (bits wire)) := by
  cases b with
  | none => rfl
  | some b => cases b <;> cases h : bits wire <;> simp [inputCell, BooleanExpr.eval, h]

theorem initial_bounded (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (initial input main initialState length width).Bounded 1 := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro k i b
  dsimp only [initial]
  split_ifs
  · cases b with
    | none => exact le_rfl
    | some b => cases b <;> simp [inputCell, BooleanExpr.size]
  · exact le_rfl

theorem initial_encodes (input : K) (main : Λ) (initialState : σ) (width : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i]) :
    Encodes (initial input main initialState word.length width)
      (initialConfiguration input main initialState word) bits := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro k i b
  dsimp only [initial, initialConfiguration]
  by_cases hk : k = input
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hi : i.val < word.length
    · simp only [hi, ↓reduceIte, inputCell_eval, hbits i.val hi, List.getElem?_eq_getElem hi]
    · simp only [hi, ↓reduceIte, BooleanExpr.eval, List.getElem?_eq_none (by omega : word.length ≤ i.val)]
  · simp [hk, BooleanExpr.eval]

theorem initial_size_le (input : K) (main : Λ) (initialState : σ) (word : List Bool) :
    stackSize (initialConfiguration input main initialState word).stk ≤ word.length := by
  apply Finset.sup_le
  intro k hk
  by_cases he : k = input
  · simp [initialConfiguration, he]
  · simp [initialConfiguration, he]

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

namespace CodeFamily

theorem initialCode_poly [Coding α] (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (hl : Poly length) : (initialCode input main initialState length).IsPoly := by
  refine ⟨fun l => CodePoly.constant _, fun v => CodePoly.constant _, ?_⟩
  intro k b
  have hc : CodePoly (fun x : α × ℕ => inputCell x.2 b) := by
    cases b with
    | none => exact CodePoly.constant false
    | some b => cases b
                · exact (CodePoly.input (show Poly (fun x : α × ℕ => x.2) by fun_prop)).negate
                · exact CodePoly.input (by fun_prop)
  by_cases hk : k = input
  · simp only [initialCode, hk, true_and]
    have hp : Poly (fun x : α × ℕ => decide (x.2 < length x.1)) := by fun_prop
    simpa only [decide_eq_true_eq] using CodePoly.ite hp hc (CodePoly.constant (decide (b=none)))
  · simpa only [initialCode, hk, false_and, ↓reduceIte] using
      (CodePoly.constant (α := α × ℕ) (decide (b=none)))

theorem reboundCode_poly [Coding α] (width : α → ℕ) (refs : α → List ℕ)
    (hw : Poly width) (hr : Poly refs) : (reboundCode (K := K) (Λ := Λ) (σ := σ) width refs).IsPoly := by
  constructor
  · intro l
    apply CodePoly.input
    fun_prop
  · intro v
    apply CodePoly.input
    fun_prop
  · intro k b
    apply CodePoly.input
    fun_prop

end CodeFamily

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

theorem code_length (e : BooleanExpr) : (code e).length ≤ 2*e.size+1 := by
  induction e with
  | input i => simp [code, BooleanExpr.size]
  | constant b => cases b <;> simp [code, BooleanExpr.size]
  | negate a ih => simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega
  | xor a b ia ib | and a b ia ib =>
    simp only [code, List.length_append, List.length_singleton, BooleanExpr.size]; omega

theorem valid_code_bits (e : BooleanExpr) (N : ℕ) (h : e.Valid (2^N)) :
    ∀ t ∈ code e, t.2.bits.length ≤ N := by
  induction e with
  | input i =>
    intro t ht
    simp only [code, List.mem_singleton] at ht
    subst t
    change i.bits.length ≤ N
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr h
  | constant b => cases b <;> simp [code]
  | negate a ih =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ih h t ht
    · simp
  | xor a b ia ib | and a b ia ib =>
    intro t ht
    simp only [code, List.mem_append, List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ia h.1 t ht
    · exact ib h.2 t ht
    · simp

theorem codes_length (es : List BooleanExpr) (C : ℕ) (h : ∀ e ∈ es, e.size ≤ C) :
    (es.flatMap code).length ≤ (2*C+1)*es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := (code_length e).trans (show 2*e.size+1 ≤ 2*C+1 by have := h e (by simp); omega)
    have hh := ih (fun f hf => h f (by simp [hf]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem reverse_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, s.2.1.reverse, s.2.2) := by
  refine ⟨h.slots, ?_, h.nodes, ?_, h.code⟩
  · simpa only [List.length_reverse] using h.operands
  · intro x hx
    exact h.refs x (List.mem_reverse.mp hx)

theorem clear_operands_bounded {N : ℕ} {s : State} (h : Bounded N s) :
    Bounded N (s.1, [], s.2.2) := ⟨h.slots, Nat.zero_le _, h.nodes, by simp, h.code⟩

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem registers_poly : (registers (K := K) (Λ := Λ) (σ := σ)).IsPoly :=
  CodeFamily.reboundCode_poly _ _ (by fun_prop) (by fun_prop)

theorem registers_bounded (x : Input) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Bounded 0 := by
  exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩

theorem registers_valid (x : Input) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ((registers (K := K) (Λ := Λ) (σ := σ)).restrict x x.1.length).Valid (2^N) := by
  have hb : ∀ i : ℕ, ((x.2.2.1[i]?).getD 0) < 2^N := by
    intro i
    have hi := getD_bound x.2.2.1 i N h
    rw [Nat.size_eq_bits_len] at hi
    exact Nat.size_le.mp hi
  exact ⟨fun _ => hb _, fun _ => hb _, fun _ _ _ => hb _⟩

@[fun_prop] theorem tokens_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (tokens program) :=
  CodeFamily.codes_poly _ (CodeFamily.transitionCode_poly _ (by fun_prop) program _ registers_poly) _ (by fun_prop)

@[fun_prop] theorem step_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Poly (step program) := by
  unfold step
  fun_prop

theorem tokens_length (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) : (tokens program x).length ≤ tokenBound program x.1.length := by
  rw [tokens_eq program x hw]
  have hb := transition_bounded hw program _ 0 (registers_bounded (K := K) (Λ := Λ) (σ := σ) x)
  have hh := codes_length (transition hw program (registers.restrict x x.1.length)).formulas
    (transitionBound program 0) (by
      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      rcases (slotEquiv K Λ σ x.1.length).symm i with l | v | ⟨k,i,b⟩
      · exact hb.label l
      · exact hb.state v
      · exact hb.stack k i b)
  simpa only [Symbolic.formulas_length, tokenBound] using hh

theorem tokens_bits (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (hw : 0 < x.1.length) (N : ℕ) (h : ∀ a ∈ x.2.2.1, a.bits.length ≤ N) :
    ∀ t ∈ tokens program x, t.2.bits.length ≤ N := by
  rw [tokens_eq program x hw]
  have hv := transition_valid hw program _ (registers_valid (K := K) (Λ := Λ) (σ := σ) x N h)
  intro t ht
  obtain ⟨e, he, ht⟩ := List.mem_flatMap.mp ht
  exact valid_code_bits e N ((transition hw program (registers.restrict x x.1.length)).formulas_valid hv e he) t ht

theorem step_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : Input)
    (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+tokenBound program x.1.length) (step program x).2 := by
  unfold step
  split
  · exact h.mono (Nat.le_add_right _ _)
  · rename_i hw
    have hw' : 0 < x.1.length := by
      have hx : x.1 ≠ [] := by simpa only [List.isEmpty_iff] using hw
      exact List.length_pos_iff.mpr hx
    have hb := run_bounded (tokens program x) (clear_operands_bounded h) hN (tokens_bits program x hw' N h.refs)
    exact (reverse_operands_bounded hb).mono (Nat.add_le_add_left (tokens_length program x hw') N)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

theorem iterateCode_bounded (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit)
    (x : Input) (N : ℕ) (hN : 3 ≤ N) (h : RPN.Bounded N x.2) :
    RPN.Bounded (N+fuel.length*tokenBound program x.1.length) (iterateCode program fuel x).2 := by
  induction fuel generalizing x N with
  | nil => simpa only [iterateCode, List.foldl_nil, List.length_nil, Nat.zero_mul, Nat.add_zero] using h
  | cons u fuel ih =>
    have hs := step_bounded program x N hN h
    have hh := ih (step program x) (N+tokenBound program x.1.length) (by omega) hs
    simpa only [iterateCode, List.foldl_cons, List.length_cons, step_width, Nat.add_mul,
      Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem tokenBound_le (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) :
    tokenBound program width ≤ tokenRate program*(width+1) := by
  unfold tokenBound tokenRate
  rw [slot_count]
  have h : Fintype.card Λ+1+Fintype.card σ+Fintype.card K*width*3 ≤
      (Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)*(width+1) := by nlinarith
  have hh := Nat.mul_le_mul_left (2*transitionBound program 0+1) h
  simpa only [Nat.mul_assoc] using hh

theorem iterateCode_partial_bound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (x : Input) (pre suf : List Unit) (he : fuel=pre++suf) :
    (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length := by
  let L := (enc (fuel,x)).length
  have heL : L = 2*fuel.length+1+2*x.1.length+1+(enc x.2).length := by
    change (encodePair (enc : List Unit → List Bool) (encodePair enc enc) (fuel,x)).length = _
    simp only [encodePair_length, encodedUnit_length]
    omega
  have hw : x.1.length ≤ L := by omega
  have hp : pre.length ≤ L := by have hh := congrArg List.length he; simp only [List.length_append] at hh; omega
  have hs := (bounded_of_encoding x.2).mono (show (enc x.2).length ≤ L+3 by omega)
  have hb := iterateCode_bounded program pre x (L+3) (by omega) hs
  have ht := (tokenBound_le program x.1.length).trans
    (Nat.mul_le_mul_left (tokenRate program) (Nat.add_le_add_right hw 1))
  have hm : pre.length * tokenBound program x.1.length ≤ L*tokenRate program*(L+1) := by
    exact (Nat.mul_le_mul hp ht).trans_eq (Nat.mul_assoc _ _ _).symm
  have hb' := hb.mono (Nat.add_le_add_left hm (L+3))
  have hh := encoding_bound hb'
  have hwidth := iterateCode_width program pre x
  have henc : (enc (iterateCode program pre x)).length = 2*x.1.length+1+(enc (iterateCode program pre x).2).length := by
    change (encodePair (enc : List Unit → List Bool) enc (iterateCode program pre x)).length = _
    rw [encodePair_length, encodedUnit_length, hwidth]
  simp only [loopBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_one, eval_pow, eval_C]
  change _ ≤ 2*L+1+20*(L+3+L*tokenRate program*(L+1)+1)^2
  omega

@[fun_prop] theorem iterateCode_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Poly (fun x : List Unit × Input => iterateCode program x.1 x.2) := by
  have hs : Poly (fun x : Input × Unit => step program x.1) := by fun_prop
  apply Automatic.Poly.of_program
  exact hs.program.listFold () (loopBound program) (by
    intro fuel x pre suf he
    change (enc (iterateCode program pre x)).length ≤ (loopBound program).eval (enc (fuel,x)).length
    exact iterateCode_partial_bound program fuel x pre suf he)

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem Encodes.get {sym : Symbolic K Λ σ width} {cfg : Configuration K Λ σ}
    {bits : ℕ → Bool} (h : Encodes sym cfg bits) (i : Slot K Λ σ width) :
    (sym.get i).eval bits = configurationBit cfg i := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

theorem compileRun_rebound_bounded (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : Symbolic K Λ σ width) (h : sym.Bounded 0) :
    (compileRun hw program ticks start sym).2.Bounded 0 := by
  induction ticks generalizing start sym with
  | zero => exact h
  | succ ticks ih => exact ih _ _ ((transition hw program sym).rebound_bounded_zero start)

theorem machineProgram_length_le (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    (machineProgram hw program input main initialState ticks length).ops.length ≤
      (1 + ticks * transitionBound program 0) * Fintype.card (Slot K Λ σ width) := by
  let init := initial input main initialState length width
  have hi : init.Bounded 1 := initial_bounded input main initialState length width
  have hp := init.compiled_length_le length 1 hi
  have hm := compileRun_length_le hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  have hz := compileRun_rebound_bounded hw program ticks (length + (init.compiled length).1.length) _
    (init.rebound_bounded_zero length)
  let middle := compileRun hw program ticks (length + (init.compiled length).1.length) (init.rebound length)
  have he := middle.2.compiled_length_le
    (length + (init.compiled length).1.length + middle.1.length) 0 hz
  change ((init.compiled length).1 ++ middle.1 ++
    (middle.2.compiled (length + (init.compiled length).1.length + middle.1.length)).1).length ≤ _
  simp only [List.length_append]
  nlinarith

/-- The whole generated straight-line program computes every field of the budgeted machine execution. -/
theorem machineProgram_semantics (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ)
    (word : List Bool) (bits : ℕ → Bool)
    (hbits : ∀ i, ∀ hi : i < word.length, bits i = word[i])
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops bits
      ((machineProgram hw program input main initialState ticks word.length).output i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i := by
  let init := initial input main initialState word.length width
  have hi : init.Valid word.length := initial_valid input main initialState word.length width
  have he : Encodes init (initialConfiguration input main initialState word) bits :=
    initial_encodes input main initialState width word bits hbits
  have hp := init.rebound_encodes word.length hi _ bits he
  have hr := compileRun_encodes hw program ticks _ _ _ _
    (init.rebound_valid word.length hi) hp
    ((Nat.add_le_add_right (initial_size_le input main initialState word) _).trans hsize)
  have hv := (compileRun_valid hw program ticks _ _ (init.rebound_valid word.length hi)).2
  let middle := compileRun hw program ticks (word.length + (init.compiled word.length).1.length)
    (init.rebound word.length)
  have ho := middle.2.output_eval _ hv
    (BooleanProgram.run (word.length + (init.compiled word.length).1.length) middle.1
      (BooleanProgram.run word.length (init.compiled word.length).1 bits)) i
  rw [hr.get i] at ho
  simpa only [machineProgram, BooleanProgram.run_append, List.length_append, Nat.add_assoc, init, middle] using ho

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem initialResult_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialResult input main initialState) :=
  CodeFamily.compile_poly _ (CodeFamily.initialCode_poly _ _ _ _ (by fun_prop)) _ _ (by fun_prop) (by fun_prop)

@[fun_prop] theorem initialInput_poly (input : K) (main : Λ) (initialState : σ) :
    Poly (initialInput input main initialState) := by
  unfold initialInput
  fun_prop

@[fun_prop] theorem generate_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) : Poly (generate program input main initialState) := by
  unfold generate
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem boundedNat_poly : Poly (fun x : List Unit × ℕ => boundedNat x.1 x.2) := by
  unfold boundedNat
  fun_prop

@[fun_prop] theorem instructionWord_poly :
    Poly (fun x : List Unit × (ℕ × Node) => instructionWord x.1 x.2.1 x.2.2) := by
  unfold instructionWord
  fun_prop

@[fun_prop] theorem instructionWords_poly :
    Poly (fun x : List Unit × (ℕ × List Node) => instructionWords x.1 x.2.1 x.2.2) := by
  unfold instructionWords
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Node => List.range xs.length)
      (g := fun x : List Unit × (ℕ × List Node) => x.2.2) Automatic.Poly.list_indices (by fun_prop)

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end P2MDyadicModule30

/- Helper module Solutions.AdvantageBridgeRegisterLoad. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean.RPN

theorem registerLoadOp_valid (start : ℕ) (source : Bool × ℕ)
    (h : source.1=true → source.2<start) : (registerLoadOp source).Valid start := by
  cases hs : source.1
  · simp [registerLoadOp,hs,BooleanOp.Valid,BooleanOp.sources]
  · simpa [registerLoadOp,hs,BooleanOp.Valid,BooleanOp.sources] using h hs

theorem registerLoadOps_valid (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) :
    BooleanProgram.Valid start (registerLoadOps sources) := by
  induction sources generalizing start with
  | nil => trivial
  | cons source rest ih =>
    change (registerLoadOp source).Valid start ∧ BooleanProgram.Valid (start+1) (registerLoadOps rest)
    refine ⟨registerLoadOp_valid start source (h source (by simp)),?_⟩
    apply ih (start+1)
    intro other ho ht
    exact (h other (by simp [ho]) ht).trans (by omega)

theorem registerLoadOp_value (source : Bool × ℕ) (state : ℕ → Bool) :
    (registerLoadOp source).eval state=registerLoadValue source state := by
  cases hs : source.1 <;> simp [registerLoadOp,registerLoadValue,BooleanOp.eval,hs]

/-- Every actually written wire has its stated old-input value; later copies
read only the original register, even when source addresses are repeated. -/
theorem registerLoadOps_value (start : ℕ) (sources : List (Bool × ℕ))
    (h : ∀ source∈sources,source.1=true → source.2<start) (state : ℕ → Bool)
    (index : ℕ) (hi : index<sources.length) :
    BooleanProgram.run start (registerLoadOps sources) state (start+index)=
      registerLoadValue sources[index] state := by
  induction sources generalizing start index state with
  | nil => simp at hi
  | cons source rest ih =>
    cases index with
    | zero =>
      change BooleanProgram.run (start+1) (registerLoadOps rest)
        ((registerLoadOp source).assign start state) (start+0)=_
      rw [BooleanProgram.run_below _ _ _ _ (by omega)]
      simp only [Nat.add_zero,BooleanOp.assign,Function.update_self,List.getElem_cons_zero,registerLoadOp_value]
    | succ index =>
      have hindex : index<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      change BooleanProgram.run (start+1) (registerLoadOps rest)
        ((registerLoadOp source).assign start state) (start+(index+1))=_
      rw [show start+(index+1)=(start+1)+index by omega,
        ih (start+1) (fun other ho ht => (h other (by simp [ho]) ht).trans (by omega)) _ index hindex]
      simp only [List.getElem_cons_succ,registerLoadValue]
      cases ht : rest[index].1
      · simp [ht]
      · have hb := h rest[index] (by simp) ht
        simp only [ht,ite_true,BooleanOp.assign]
        exact Function.update_of_ne (by omega) _ _

@[fun_prop] theorem registerLoadNode_poly : Poly registerLoadNode := by
  unfold registerLoadNode
  fun_prop

theorem registerLoadNode_eq (source : Bool × ℕ) : registerLoadNode source=node (registerLoadOp source) := by
  cases hs : source.1 <;> simp [registerLoadNode,registerLoadOp,node,hs]

@[fun_prop] theorem registerLoadGateWords_poly :
    Poly (fun x : List Unit × (ℕ × List (Bool × ℕ)) => registerLoadGateWords x.1 x.2.1 x.2.2) := by
  unfold registerLoadGateWords
  fun_prop

theorem registerLoadGateWords_correct {total : ℕ} (slots : List Unit) (start : ℕ)
    (sources : List (Bool × ℕ)) (h : ∀ source∈sources,source.1=true → source.2<start)
    (hn : start+sources.length ≤ total) (hs : start+sources.length ≤ slots.length) :
    registerLoadGateWords slots start sources=
      (BooleanProgram.gates start (registerLoadOps sources)
        (by simpa only [registerLoadOps_length] using hn)).map BooleanGate.code := by
  unfold registerLoadGateWords
  have he : sources.map registerLoadNode=(registerLoadOps sources).map node := by
    change sources.map registerLoadNode=(sources.map registerLoadOp).map node
    rw [List.map_map]
    exact List.map_congr_left (fun source _ => registerLoadNode_eq source)
  rw [he]
  exact instructionWords_gates slots start (registerLoadOps sources)
    (by simpa only [registerLoadOps_length] using hn) (registerLoadOps_valid start sources h)
    (by simpa only [registerLoadOps_length] using hs)

end InfoLossLAR.WorstCase

end P2MDyadicModule31

/- Helper module Solutions.AdvantageBridgeCircuitBundle. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

theorem bundleCircuit_wellFormed (blocks : List QuantumBlock)
    (h : ∀ block ∈ blocks,∀ layer ∈ block.circuit,LayerOk layer) :
    ∀ layer ∈ bundleCircuit blocks,LayerOk layer := by
  induction blocks with
  | nil => simp [bundleCircuit]
  | cons block blocks ih =>
    intro layer hl
    rcases List.mem_append.mp hl with hl|hl
    · exact leftCircuit_wellFormed block.circuit (h block (by simp)) layer hl
    · exact rightCircuit_wellFormed (bundleCircuit blocks)
        (ih (fun b hb => h b (by simp [hb]))) layer hl

theorem bundleCircuit_depth (blocks : List QuantumBlock) :
    depth (bundleCircuit blocks)=(blocks.map (fun block => depth block.circuit)).sum := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change depth (leftCircuit block.circuit++rightCircuit (bundleCircuit blocks)) = _
    have hd {n : ℕ} (first second : Layered n) : depth (first++second)=depth first+depth second := List.length_append
    rw [hd,leftCircuit_depth,rightCircuit_depth,ih]
    rfl

theorem bundlePhysical_fold (blocks : List QuantumBlock) :
    bundlePhysical blocks=(blocks.map (fun block => (⟨block.wires,block.circuit⟩ : Σ wires : ℕ,Layered wires))).foldr
      appendPhysical ⟨0,[]⟩ := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    change appendPhysical ⟨block.wires,block.circuit⟩ (bundlePhysical blocks)=_
    rw [List.map_cons,List.foldr_cons,ih]

end InfoLossLAR.WorstCase

end P2MDyadicModule32

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

private theorem append_registers_iff {n m : ℕ} (state : Bits (n+m)) (left : Bits n) (right : Bits m) :
    state=Fin.append left right ↔ leftRegister state=left ∧ rightRegister state=right := by
  constructor
  · rintro rfl
    exact ⟨by funext i; simp [leftRegister],by funext i; simp [rightRegister]⟩
  · rintro ⟨hl,hr⟩
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro i
      simpa only [Fin.append_left,leftRegister] using congrArg (fun word => word i) hl
    · intro i
      simpa only [Fin.append_right,rightRegister] using congrArg (fun word => word i) hr

/-- The actual platform input state is exactly the full computational-basis
word consisting of its input followed by the required zero ancillas. -/
theorem basisInput_eq_computationalBasis {n a : ℕ} (input : Bits n) :
    basisInput (a := a) input=computationalBasis (Fin.append input (fun _ => false)) := by
  funext state
  unfold basisInput computationalBasis
  congr 1
  apply propext
  rw [append_registers_iff]
  simp only [funext_iff,leftRegister,rightRegister]

theorem computationalBasis_tensor {n m : ℕ} (left : Bits n) (right : Bits m) :
    computationalBasis (Fin.append left right)=tensorState (computationalBasis left) (computationalBasis right) := by
  funext state
  change (if state=Fin.append left right then (1 : ℂ) else 0)=
    (if leftRegister state=left then 1 else 0)*(if rightRegister state=right then 1 else 0)
  by_cases hl : leftRegister state=left
  · by_cases hr : rightRegister state=right
    · rw [if_pos ((append_registers_iff state left right).mpr ⟨hl,hr⟩),if_pos hl,if_pos hr,mul_one]
    · have hs : state ≠ Fin.append left right := fun h => hr ((append_registers_iff state left right).mp h).2
      rw [if_neg hs,if_pos hl,if_neg hr,mul_zero]
  · have hs : state ≠ Fin.append left right := fun h => hl ((append_registers_iff state left right).mp h).1
    rw [if_neg hs,if_neg hl,zero_mul]

end InfoLossLAR.WorstCase

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

theorem wordExtension_before (word : List Bool) (i : ℕ) (h : i < word.length) :
    wordExtension word i = word[i] := by simp only [wordExtension, List.getElem?_eq_getElem h, Option.getD_some]

theorem wordExtension_after (word : List Bool) (i : ℕ) (h : word.length ≤ i) :
    wordExtension word i = false := by simp only [wordExtension, List.getElem?_eq_none h, Option.getD_none]

theorem wordExtension_basis (word : List Bool) (ancillas : ℕ) :
    Fin.append (toBits word) (fun _ : Fin (ancillas + 1) => false) =
      (fun i : Fin (word.length + (ancillas + 1)) => wordExtension word i.val) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [Fin.append_left, Fin.coe_castAdd, toBits, List.get_eq_getElem] using
      (wordExtension_before word j.val j.isLt).symm
  · intro j
    simp only [Fin.append_right, Fin.val_natAdd]
    exact (wordExtension_after word _ (Nat.le_add_right _ _)).symm

/-- Reading any output slot of the compiled basis state recovers the actual budgeted machine field. -/
theorem machineCircuit_output (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool)
    (hsize : word.length + programPushBound program * ticks ≤ width) (i : Slot K Λ σ width) :
    (fun j => BooleanProgram.run word.length
      (machineProgram hw program input main initialState ticks word.length).ops (wordExtension word) j.val)
      (machineOutputWire hw program input main initialState ticks word.length i) =
      configurationBit ((stickyStep program)^[ticks] (initialConfiguration input main initialState word)) i :=
  machineProgram_semantics hw program input main initialState ticks word (wordExtension word)
    (wordExtension_before word) hsize i

end InfoLossLAR.WorstCase.TM2Boolean

end P2MDyadicModule34

/- Helper module Solutions.AdvantageBridgeCopyPreparation. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity TM2Boolean

namespace BooleanProgram

/-- A fresh program preserves every wire after its complete write interval. -/
theorem run_after (start : ℕ) (ops : List BooleanOp) (state : ℕ → Bool) (index : ℕ)
    (hi : start+ops.length ≤ index) : run start ops state index=state index := by
  induction ops generalizing start state with
  | nil => rfl
  | cons op rest ih =>
    change run (start+1) rest (op.assign start state) index=state index
    rw [ih (start+1) _ (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi)]
    exact Function.update_of_ne (by simp only [List.length_cons] at hi; omega) _ _

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule35

/- Helper module StaticBatchLoad. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity TM2Boolean

noncomputable section

/-- Each register entry is a fixed Boolean or a copy of an original input
wire. The source list is completely fixed by the public input length. -/
abbrev StaticLoadSlot (n : ℕ) := Sum Bool (Fin n)

def StaticLoadSlot.op {n : ℕ} : StaticLoadSlot n → BooleanOp
  | .inl b => .constant b
  | .inr i => .copy i.val

def staticLoadOps {n : ℕ} (slots : List (StaticLoadSlot n)) : List BooleanOp :=
  slots.map StaticLoadSlot.op

theorem staticLoadOps_valid {n : ℕ} (slots : List (StaticLoadSlot n))
    (start : ℕ) (hstart : n ≤ start) : BooleanProgram.Valid start (staticLoadOps slots) := by
  induction slots generalizing start with
  | nil => trivial
  | cons slot slots ih =>
    refine ⟨?_, ih (start + 1) (by omega)⟩
    cases slot with
    | inl b => simp [StaticLoadSlot.op, BooleanOp.Valid, BooleanOp.sources]
    | inr i =>
      simpa [StaticLoadSlot.op, BooleanOp.Valid, BooleanOp.sources] using i.isLt.trans_le hstart

theorem staticLoadOps_value {n : ℕ} (slots : List (StaticLoadSlot n))
    (start : ℕ) (hstart : n ≤ start) (s : ℕ → Bool) (i : Fin slots.length) :
    BooleanProgram.run start (staticLoadOps slots) s (start + i.val) =
      slots[i.val].elim id (fun j => s j.val) := by
  induction slots generalizing start s with
  | nil => exact Fin.elim0 i
  | cons slot slots ih =>
    refine Fin.cases ?_ (fun tail => ?_) i
    · change BooleanProgram.run (start+1) (staticLoadOps slots)
        (slot.op.assign start s) (start+0) = slot.elim id (fun j => s j.val)
      rw [Nat.add_zero, BooleanProgram.run_below _ _ _ _ (by omega)]
      cases slot <;> simp [StaticLoadSlot.op, BooleanOp.assign, BooleanOp.eval]
    · have hindex : start + (Fin.succ tail).val = start+1+tail.val := by
        simp only [Fin.val_succ]
        omega
      rw [hindex]
      change BooleanProgram.run (start+1) (staticLoadOps slots)
        (slot.op.assign start s) (start+1+tail.val) = _
      rw [ih (start+1) (by omega)]
      change slots[tail.val].elim id (fun j => slot.op.assign start s j.val) =
        slots[tail.val].elim id (fun j => s j.val)
      cases slots[tail.val] with
      | inl b => rfl
      | inr j =>
        have hj : j.val ≠ start := Nat.ne_of_lt (j.isLt.trans_le hstart)
        simp [BooleanOp.assign, Function.update_of_ne hj]

def staticLoadCircuit {n a : ℕ} (slots : List (StaticLoadSlot n))
    (hfit : slots.length ≤ a+1) : Layered (n+(a+1)) :=
  compileReversible (booleanToReversible (BooleanProgram.gates n (staticLoadOps slots)
    (by simpa only [staticLoadOps, List.length_map] using Nat.add_le_add_left hfit n)))

def staticLoadedBit (word : Str) (slots : List (StaticLoadSlot word.length)) (i : ℕ) : Bool :=
  if i < word.length then wordExtension word i
  else if h : i-word.length < slots.length then
    slots[i-word.length].elim id (fun j => wordExtension word j.val)
  else false

theorem staticLoadCircuit_basis {a : ℕ} (word : Str)
    (slots : List (StaticLoadSlot word.length)) (hfit : slots.length ≤ a+1) :
    runLayered (staticLoadCircuit slots hfit) (basisInput (a := a) (toBits word)) =
      computationalBasis (fun i => staticLoadedBit word slots i.val) := by
  rw [basisInput_eq_computationalBasis, wordExtension_basis]
  unfold staticLoadCircuit computationalBasis
  rw [BooleanProgram.circuit_basis _ _ (staticLoadOps_valid slots word.length le_rfl)
    (wordExtension word) (fun i hi _ => wordExtension_after word i hi)]
  have hbits : (fun i : Fin (word.length+(a+1)) =>
      BooleanProgram.run word.length (staticLoadOps slots) (wordExtension word) i.val) =
      (fun i => staticLoadedBit word slots i.val) := by
    funext i
    unfold staticLoadedBit
    by_cases hi : i.val < word.length
    · rw [if_pos hi, BooleanProgram.run_below _ _ _ _ hi]
    · rw [if_neg hi]
      by_cases hs : i.val-word.length < slots.length
      · rw [dif_pos hs]
        have hv := staticLoadOps_value slots word.length le_rfl (wordExtension word)
          ⟨i.val-word.length, hs⟩
        simpa [Nat.add_sub_of_le (by omega : word.length ≤ i.val)] using hv
      · rw [dif_neg hs, BooleanProgram.run_after, wordExtension_after word i.val (by omega)]
        simpa only [staticLoadOps, List.length_map] using (show word.length + slots.length ≤ i.val by omega)
  simp only [hbits]

end

end InfoLossLAR.WorstCase

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option maxHeartbeats 3000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

open Turing QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open RPN

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

@[fun_prop] theorem description_poly (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) :
    Poly (fun x : Request × ℕ => description program input main initialState x.1 x.2) := by
  unfold description
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option maxHeartbeats 2500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing StateTransition QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

open OAI.MetricKMedian.Binary

namespace PolyProgramCircuit

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions

theorem final_configuration (word : Str) :
    (stickyStep P.machine.code)^[P.time.eval word.length]
      (initialConfiguration P.machine.input P.machine.main P.machine.initial word) =
        P.machine.finalCfg (f word) := by
  have hh := P.outputs word
  change EvalsToInTime (TM2.step P.machine.code)
    (initialConfiguration P.machine.input P.machine.main P.machine.initial word)
    (some (P.machine.finalCfg (f word))) (P.time.eval word.length) at hh
  exact sticky_iterate_of_outputs P.machine.code _ _ _ hh rfl

/-- An actual output wire gives each present/absent symbol of the encoded function output. -/
theorem output_correct (word : Str) (i : Fin (capacity P word.length)) (b : Option Bool) :
    result P word (outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := machineCircuit_output (capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [final_configuration P word] at hh
  simpa only [result, outputWire, compiled, configurationBit, Machine.finalCfg, ↓reduceIte] using hh

theorem spacePolynomial_eval (length : ℕ) :
    (spacePolynomial P).eval length =
      (1 + P.time.eval length * transitionBound P.machine.code 0) *
        Fintype.card (Slot P.machine.K P.machine.Label P.machine.State (capacity P length)) := by
  simp only [spacePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, slot_count, capacity]
  ring

theorem ancilla_bound (length : ℕ) : (compiled P length).ops.length ≤ (spacePolynomial P).eval length := by
  rw [spacePolynomial_eval]
  exact machineProgram_length_le _ _ _ _ _ _ _

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Turing StateTransition QAlgorithms.Complexity Polynomial

open Integration9_9.TM2OutputLength Integration9_9.TM2PlatformSerialization

open Integration9_9.TM2PolynomialBudget

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_1

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_1

@[fun_prop] theorem request_poly : Poly (request P) := by
  unfold request
  fun_prop

@[fun_prop] theorem descriptionGenerator_poly : Poly (descriptionGenerator P) := by
  unfold descriptionGenerator outputIndex
  fun_prop

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule39

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.TM2OutputLength

/-- The real machine's complete output fits in the compiled finite slot register. -/
theorem actualOutput_length_lt_capacity {f : Str → Str} (P : PolyProgram id id f) (word : Str) :
    (f word).length<capacity P word.length := by
  have h := output_length_le P.machine.tm word (f word) (P.time.eval word.length) (P.outputs word)
  change (f word).length≤word.length+programPushBound P.machine.code*P.time.eval word.length at h
  unfold capacity
  omega

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end P2MDyadicModule40

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CodeGenerator

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_3

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_3

@[fun_prop] theorem outputSlotIndex_poly :
    Poly (fun x : ℕ × ℕ => outputSlotIndex P x.1 x.2) := by
  unfold outputSlotIndex
  fun_prop

theorem outputSlotIndex_eq (width : ℕ) (index : Fin width) :
    outputSlotIndex P width index.val=
      (slotEquiv P.machine.K P.machine.Label P.machine.State width
        (.inr (.inr (P.machine.output,index,some true)))).val :=
  (slot_stack_index width P.machine.output index (some true)).symm

@[fun_prop] theorem generatedOutputAddress_poly :
    Poly (fun x : Request × ℕ => generatedOutputAddress P x.1 x.2) := by
  unfold generatedOutputAddress
  fun_prop

theorem generatedOutputAddress_eq (x : Request) (hw : 0<x.2.1.length) (index : Fin x.2.1.length) :
    generatedOutputAddress P x index.val=
      (machineProgram hw P.machine.code P.machine.input P.machine.main P.machine.initial
        x.2.2.length x.1.length).output (.inr (.inr (P.machine.output,index,some true))) := by
  unfold generatedOutputAddress
  rw [outputSlotIndex_eq]
  exact (generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial x hw).2.2 _

@[fun_prop] theorem generatedProgramOutputAddress_poly :
    Poly (fun x : Str × ℕ => generatedProgramOutputAddress P x.1 x.2) := by
  unfold generatedProgramOutputAddress
  fun_prop

/-- Exact transport of the physical program output across an equal stack capacity. -/
theorem outputProgram_transport {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) (index : Fin a) :
    (machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,index,some true)))=
    (machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).output
      (.inr (.inr (P.machine.output,Fin.cast he index,some true))) := by
  cases he
  rfl

/-- On each unary request, the emitted natural address is literally the
physical outputWire of the verified uniform compiler. -/
theorem generatedProgramOutputAddress_eq (length : ℕ) (index : Fin (capacity P length)) :
    generatedProgramOutputAddress P (unary length) index.val=(outputWire P length index (some true)).val := by
  unfold generatedProgramOutputAddress
  rw [request_unary]
  let width := (List.replicate (capacity P length) ()).length
  have hwidth : width=capacity P length := List.length_replicate
  have hw : 0<width := by rw [hwidth]; exact capacity_pos P length
  let i : Fin width := ⟨index.val,by rw [hwidth]; exact index.isLt⟩
  have hi : Fin.cast hwidth i=index := Fin.ext rfl
  have h := generatedOutputAddress_eq P
    (List.replicate length (),List.replicate (capacity P length) (),List.replicate (P.time.eval length) ()) hw i
  simp only [List.length_replicate] at h
  have he := outputProgram_transport P hwidth hw (capacity_pos P length) (P.time.eval length) length i
  rw [he,hi] at h
  simpa only [outputWire,machineOutputWire,compiled,i] using h

@[fun_prop] theorem generatedAddressRange_poly :
    Poly (fun x : Str × (List Unit × ℕ) => generatedAddressRange P x.1 x.2.1 x.2.2) := by
  unfold generatedAddressRange
  apply Automatic.Poly.list_map
  · fun_prop
  · exact Automatic.Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : Str × (List Unit × ℕ) => x.2.1) Automatic.Poly.list_indices (by fun_prop)

/-- All genuinely emitted addresses lie inside the actual physical circuit
register whenever the requested output cells fit its proved capacity. -/
theorem generatedAddressRange_bounded (length : ℕ) (slots : List Unit) (offset : ℕ)
    (h : offset+slots.length ≤ capacity P length) :
    ∀ address∈generatedAddressRange P (unary length) slots offset,
      address<length+((compiled P length).ops.length+1) := by
  intro address ha
  obtain ⟨index,hi,rfl⟩ := List.mem_map.mp ha
  have hin := List.mem_range.mp hi
  let cell : Fin (capacity P length) := ⟨offset+index,by omega⟩
  change generatedProgramOutputAddress P (unary length) cell.val<_
  rw [generatedProgramOutputAddress_eq]
  exact (outputWire P length cell (some true)).isLt

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule41

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem unaryPayload_poly : Poly unaryPayload := by
  unfold unaryPayload
  exact Poly.comp parser_take_poly (Poly.pair Poly.identity inputWidth_poly)

@[fun_prop] theorem shiftWireWord_poly : Poly (fun input : Str × Str => shiftWireWord input.1 input.2) := by
  unfold shiftWireWord
  fun_prop

@[fun_prop] theorem shiftInstructionWord_poly : Poly (fun input : Str × Str => shiftInstructionWord input.1 input.2) := by
  unfold shiftInstructionWord
  fun_prop

/-- The emitter offsets exactly the actual right-embedded platform gate. -/
theorem shiftInstructionWord_encInstr {n : ℕ} (prior : Str) (gate : Instr n) :
    shiftInstructionWord prior (encInstr gate)=encInstr (rightInstruction (n := prior.length) gate) := by
  cases gate <;>
    simp only [encInstr,List.append_assoc,shiftInstructionWord,readUnary_append,emitter_width_append,
      unaryPayload_encNat,unaryPayload_number,lengthToken_eq,List.length_append,unary,List.length_replicate,
      rightInstruction,Fin.val_natAdd] <;> norm_num <;> rfl

@[fun_prop] theorem shiftCircuitWords_poly :
    Poly (fun input : Str × List (List Str) => shiftCircuitWords input.1 input.2) := by
  have hg : Poly (fun x : ((Str × List (List Str)) × List Str) × Str =>
      shiftInstructionWord x.1.1.1 x.2) :=
    Poly.comp (f := fun p : Str × Str => shiftInstructionWord p.1 p.2)
      (g := fun x : ((Str × List (List Str)) × List Str) × Str => (x.1.1.1,x.2))
      shiftInstructionWord_poly (by fun_prop)
  have hl : Poly (fun x : (Str × List (List Str)) × List Str =>
      x.2.map (shiftInstructionWord x.1.1)) := Poly.list_map hg Poly.snd
  unfold shiftCircuitWords
  exact Poly.list_map hl Poly.snd

theorem shiftCircuitWords_correct {n : ℕ} (prior : Str) (circuit : Layered n) :
    shiftCircuitWords prior (circuit.map (List.map encInstr))=
      (rightCircuit (n := prior.length) circuit).map (List.map encInstr) := by
  simp only [shiftCircuitWords,rightCircuit,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  exact shiftInstructionWord_encInstr prior gate

@[fun_prop] theorem readFamilyFrame_poly : Poly readFamilyFrame := by
  unfold readFamilyFrame
  fun_prop

@[fun_prop] theorem precedingWireSlots_poly : Poly precedingWireSlots := by
  unfold precedingWireSlots
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.comp parser_take_poly Poly.identity

@[fun_prop] theorem bundleCircuitWordLayers_poly : Poly bundleCircuitWordLayers := by
  unfold bundleCircuitWordLayers
  apply Poly.list_flatMap
  · exact Poly.comp shiftCircuitWords_poly
      (Poly.pair precedingWireSlots_poly (by fun_prop))
  · exact Poly.list_indices

private theorem emitter_read_number (number : ℕ) : readUnary (encNat number)=(encNat number,[]) := by
  simpa only [List.append_nil] using readUnary_append number []

theorem shiftInstructionWord_spec (prior xs : Str) :
    shiftInstructionWord prior xs=
      encNat (inputWidth xs)++encNat (prior.length+inputWidth (readUnary xs).2)++
        (if inputWidth xs=4 then
          encNat (prior.length+inputWidth (readUnary (readUnary xs).2).2) else []) := by
  unfold shiftInstructionWord
  simp only [lengthToken_eq,List.length_append,unaryPayload_length]
  split_ifs <;> simp

theorem shiftInstructionWord_canonical (prior : Str) (tag first second : ℕ) :
    shiftInstructionWord prior (encNat tag++encNat first++(if tag=4 then encNat second else []))=
      encNat tag++encNat (prior.length+first)++(if tag=4 then encNat (prior.length+second) else []) := by
  rw [shiftInstructionWord_spec]
  by_cases h : tag=4 <;>
    simp [h,List.append_assoc,readUnary_append,emitter_width_append,emitter_width_number,emitter_read_number]

/-- Offset composition is exact even on malformed original gate words,
because every shifted word is canonically unary-framed. -/
theorem shiftInstructionWord_comp (first second xs : Str) :
    shiftInstructionWord first (shiftInstructionWord second xs)=shiftInstructionWord (first++second) xs := by
  rw [shiftInstructionWord_spec second xs,shiftInstructionWord_canonical,shiftInstructionWord_spec]
  simp only [List.length_append,Nat.add_assoc]

theorem shiftCircuitWords_comp (first second : Str) (layers : List (List Str)) :
    shiftCircuitWords first (shiftCircuitWords second layers)=shiftCircuitWords (first++second) layers := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro word _
  exact shiftInstructionWord_comp first second word

theorem shiftCircuitWords_flatMap {α : Type*} (prior : Str) (values : List α) (layers : α → List (List Str)) :
    shiftCircuitWords prior (values.flatMap layers)=values.flatMap (fun value => shiftCircuitWords prior (layers value)) := by
  simp only [shiftCircuitWords,List.map_flatMap]

theorem shiftCircuitWords_zero {n : ℕ} (circuit : Layered n) :
    shiftCircuitWords [] (circuit.map (List.map encInstr))=circuit.map (List.map encInstr) := by
  simp only [shiftCircuitWords,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro gate _
  rw [shiftInstructionWord_encInstr]
  cases gate <;> simp [rightInstruction,encInstr]

/-- The polynomial indexed emitter has exactly the recursive physical
head/offset-tail composition, with a canonicalized head layer description. -/
theorem bundleCircuitWordLayers_cons (frame : PhysicalFrameWords) (frames : List PhysicalFrameWords) :
    bundleCircuitWordLayers (frame::frames)=
      shiftCircuitWords [] frame.2.2++shiftCircuitWords frame.1 (bundleCircuitWordLayers frames) := by
  unfold bundleCircuitWordLayers
  simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
    List.getElem?_cons_zero,Option.getD_some,precedingWireSlots,List.take_zero,List.flatMap_nil]
  rw [shiftCircuitWords_flatMap]
  apply congrArg (fun tail => shiftCircuitWords [] frame.2.2++tail)
  apply List.flatMap_congr
  intro index _
  simp only [List.getElem?_cons_succ,precedingWireSlots,List.take_succ_cons,List.flatMap_cons]
  exact (shiftCircuitWords_comp frame.1 _ _).symm

private theorem rightCircuit_words_cast {n : ℕ} (first second : ℕ) (h : first=second) (circuit : Layered n) :
    (rightCircuit (n := first) circuit).map (List.map encInstr)=
      (rightCircuit (n := second) circuit).map (List.map encInstr) := by
  cases h
  rfl

theorem bundleCircuitWordLayers_correct (blocks : List QuantumBlock) :
    bundleCircuitWordLayers (blocks.map blockFrameWords)=
      (bundleCircuit blocks).map (List.map encInstr) := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    rw [List.map_cons,bundleCircuitWordLayers_cons]
    simp only [blockFrameWords,shiftCircuitWords_zero]
    have hlen : (unary block.wires).length=block.wires := by simp [unary]
    have hshift : shiftCircuitWords (unary block.wires) ((bundleCircuit blocks).map (List.map encInstr))=
        (rightCircuit (n := block.wires) (bundleCircuit blocks)).map (List.map encInstr) := by
      exact (shiftCircuitWords_correct (unary block.wires) (bundleCircuit blocks)).trans
        (rightCircuit_words_cast _ _ hlen _)
    rw [ih,hshift]
    simp only [bundleCircuit,bundleWidth,List.map_append,leftCircuit,List.map_map,Function.comp_def,
      leftInstruction_encInstr]

end InfoLossLAR.WorstCase

end P2MDyadicModule42

/- Helper module Solutions.AdvantageBridgeBundleUniform. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity Turing Function Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open Integration9_9 Integration9_9.TM2StockLists QMCNumericRuntime

theorem bundleRequests_correct (budget : Polynomial ℕ) (input : Str) :
    bundleRequests budget input = List.ofFn (fun index : Fin (budget.eval input.length+1) => unary index.val) := by
  apply List.ext_getElem
  · simp [bundleRequests,bundleRequestsFromSlots]
  · intro i hi hj
    simp only [bundleRequests,bundleRequestsFromSlots,List.length_map,List.length_range,
      List.length_replicate] at hi
    simp only [bundleRequests,bundleRequestsFromSlots,List.getElem_map,List.getElem_range,
      List.take_replicate,List.getElem_ofFn,List.map_replicate,unary]
    rw [Nat.min_eq_left (by omega)]

end InfoLossLAR.WorstCase

end P2MDyadicModule43

/- Helper module Solutions.AdvantageBridgeDRegisterLoad. -/
section P2MDyadicModule44

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

@[fun_prop] theorem dBlockLoadSources_poly :
    Poly (fun x : List ℕ × (List Unit × List Unit) => dBlockLoadSources x.1 x.2.1 x.2.2) := by
  unfold dBlockLoadSources
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun x : List ℕ × (List Unit × List Unit) => x.2.2) Poly.list_indices (by fun_prop)

theorem dBlockLoadSources_valid (start : ℕ) (querySources : List ℕ) (request slots : List Unit)
    (hq : request.length ≤ querySources.length)
    (hs : ∀ address∈querySources,address  <  start) :
    ∀ source∈dBlockLoadSources querySources request slots,source.1=true → source.2  <  start := by
  intro source hsource ht
  obtain ⟨index,hi,he⟩ := List.mem_map.mp hsource
  rw [←he] at ht ⊢
  have hj : index  <  request.length := by simpa using ht
  have hindex : index  <  querySources.length := hj.trans_le hq
  simpa only [List.getElem?_eq_getElem hindex,Option.getD_some] using
    hs querySources[index] (List.getElem_mem hindex)

end InfoLossLAR.WorstCase

end P2MDyadicModule44

/- Helper module Solutions.AdvantageBridgeQueryPointerSemantics. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

/-- The value at a really emitted pointer is the corresponding real machine
output bit, not an abstract address interpretation premise. -/
theorem generatedQueryBits_output {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (index : Fin (capacity P word.length)) :
    generatedQueryBits P word (generatedProgramOutputAddress P (unary word.length) index.val)=
      decide (some true=(f word)[index.val]?) := by
  rw [generatedProgramOutputAddress_eq]
  exact (selectorBitsExtension_get (result P word) (outputWire P word.length index (some true))).trans
    (output_correct P word index (some true))

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule45

/- Helper module Solutions.AdvantageBridgePreparedLoad. -/
section P2MDyadicModule46

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

theorem preparedLoadOps_valid {f : Str → Str} (P : PolyProgram id id f)
    (length : ℕ) (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < length+((compiled P length).ops.length+1)) :
    BooleanProgram.Valid length (preparedLoadOps P length sources) := by
  classical
  rw [preparedLoadOps,BooleanProgram.valid_append]
  refine ⟨(machineProgram_valid (capacity_pos P length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval length) length).1,?_⟩
  change (BooleanOp.constant false).Valid (length+(compiled P length).ops.length) ∧
    BooleanProgram.Valid (length+(compiled P length).ops.length+1) (registerLoadOps sources)
  constructor
  · simp [BooleanOp.Valid,BooleanOp.sources]
  · convert registerLoadOps_valid _ sources hs using 1  <;> omega

theorem preparedCoreBits_prefix {f : Str → Str} (P : PolyProgram id id f) (word : Str) (index : ℕ)
    (hi : index < word.length+((compiled P word.length).ops.length+1)) :
    preparedCoreBits P word index=generatedQueryBits P word index := by
  unfold preparedCoreBits generatedQueryBits selectorBitsExtension result
  simp only [dif_pos hi,Fin.val_mk]
  by_cases he : index=word.length+(compiled P word.length).ops.length
  · subst index
    rw [Function.update_self,BooleanProgram.run_after _ _ _ _ le_rfl,
      wordExtension_after word _ (by omega)]
  · exact Function.update_of_ne he _ _

/-- The combined true preprocessing/load program preserves every real machine
output flag/payload wire, including its actual terminal zero workspace bit. -/
theorem preparedLoadOps_prefix {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ)) (index : ℕ)
    (hi : index < word.length+((compiled P word.length).ops.length+1)) :
    BooleanProgram.run word.length (preparedLoadOps P word.length sources) (wordExtension word) index=
      generatedQueryBits P word index := by
  rw [preparedLoadOps,BooleanProgram.run_append]
  simp only [BooleanProgram.run,BooleanOp.assign,BooleanOp.eval]
  rw [BooleanProgram.run_below _ _ _ _ (by omega)]
  exact preparedCoreBits_prefix P word index hi

/-- Every D-load destination gets exactly the true previously computed query
output value at its emitted pointer, with all non-copy positions zero. -/
theorem preparedLoadOps_written {f : Str → Str} (P : PolyProgram id id f) (word : Str)
    (sources : List (Bool × ℕ))
    (hs : ∀ source∈sources,source.1=true → source.2 < word.length+((compiled P word.length).ops.length+1))
    (index : ℕ) (hi : index < sources.length) :
    BooleanProgram.run word.length (preparedLoadOps P word.length sources) (wordExtension word)
      (word.length+((compiled P word.length).ops.length+1)+index)=
        registerLoadValue sources[index] (generatedQueryBits P word) := by
  rw [preparedLoadOps,BooleanProgram.run_append]
  simp only [BooleanProgram.run,BooleanOp.assign,BooleanOp.eval]
  have he : word.length+(compiled P word.length).ops.length+1=
      word.length+((compiled P word.length).ops.length+1) := by omega
  rw [he]
  change BooleanProgram.run _ (registerLoadOps sources) (preparedCoreBits P word) _=_
  rw [registerLoadOps_value _ sources hs _ index hi]
  unfold registerLoadValue
  cases ht : sources[index].1
  · simp
  · simp only [ite_true]
    exact preparedCoreBits_prefix P word _ (hs sources[index] (List.getElem_mem hi) ht)

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule46

/- Helper module Solutions.AdvantageBridgeBodyCodeCapture. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readRawBooleanWord_poly : Poly readRawBooleanWord := by
  have hr : Poly (fun xs : Str => (readBooleanInstruction xs).1) :=
    Poly.comp Poly.fst readBooleanInstruction_poly
  have hn : Poly (fun xs : Str => xs.length-(readBooleanInstruction xs).1.length) :=
    Poly.comp Poly.nat_sub (Poly.pair Poly.list_length (Poly.comp Poly.list_length hr))
  have hc : Poly (fun xs : Str => xs.take (xs.length-(readBooleanInstruction xs).1.length)) :=
    Poly.comp (f := fun x : Str × ℕ => x.1.take x.2)
      (g := fun xs : Str => (xs,xs.length-(readBooleanInstruction xs).1.length))
      parser_take_poly (Poly.pair Poly.identity hn)
  exact Poly.pair hr hc

theorem readRawBooleanWord_rest_length (xs : Str) : (readRawBooleanWord xs).1.length ≤ xs.length :=
  readBooleanInstruction_rest_length xs

theorem readRawBooleanWord_append {n : ℕ} (gate : BooleanGate n) (suffix : Str) :
    readRawBooleanWord (gate.code++suffix)=(suffix,gate.code) := by
  unfold readRawBooleanWord
  rw [readBooleanInstruction_append]
  simp only [List.length_append,Nat.add_sub_cancel_right,List.take_left]

@[fun_prop] theorem readRawBooleanWords_poly : Poly readRawBooleanWords :=
  readList_poly readRawBooleanWord readRawBooleanWord_poly readRawBooleanWord_rest_length

theorem readRawBooleanWords_append {n : ℕ} (gates : List (BooleanGate n)) (suffix : Str) :
    readRawBooleanWords (encStr (gates.map BooleanGate.code)++suffix)=(suffix,gates.map BooleanGate.code) :=
  readList_append_mapped readRawBooleanWord BooleanGate.code BooleanGate.code readRawBooleanWord_append gates suffix

@[fun_prop] theorem readRawBooleanFamilyWords_poly : Poly readRawBooleanFamilyWords := by
  have hr : Poly (fun xs : Str => (readUnary xs).2) := Poly.comp Poly.snd readUnary_poly
  have ht : Poly (fun xs : Str => (readUnary ((readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (readUnary xs).2) (g := fun xs : Str => (readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => readRawBooleanWords ((readUnary ((readUnary xs).2)).2)) :=
    Poly.comp (f := readRawBooleanWords) (g := fun xs : Str => (readUnary ((readUnary xs).2)).2)
      readRawBooleanWords_poly ht
  exact Poly.comp (f := fun x : Str × List Str => x.2)
    (g := fun xs : Str => readRawBooleanWords ((readUnary ((readUnary xs).2)).2)) Poly.snd hp

theorem readRawBooleanFamilyWords_code (F : BooleanFamily) (n : ℕ) :
    readRawBooleanFamilyWords (F.code n)=(F.gates n).map BooleanGate.code := by
  unfold readRawBooleanFamilyWords BooleanFamily.code
  simp only [List.append_assoc,readUnary_append]
  have h := readRawBooleanWords_append (F.gates n) []
  simpa only [List.append_nil] using congrArg Prod.snd h

namespace BooleanProgram

/-- Exact finite-gate append for the actual contiguous fresh assignment program. -/
theorem gates_append {total start : ℕ} (first second : List BooleanOp)
    (h : start+(first++second).length ≤ total) :
    gates start (first++second) h=
      gates start first (by simp only [List.length_append] at h; omega) ++
        gates (start+first.length) second (by simpa only [List.length_append,Nat.add_assoc] using h) := by
  induction first generalizing start with
  | nil => simp only [List.nil_append,gates,List.length_nil,Nat.add_zero]
  | cons op rest ih =>
    simp only [List.cons_append,gates,List.length_cons]
    congr 1
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (start := start+1) (by simp only [List.length_cons,List.length_append] at h ⊢; omega)

/-- Actual serialized instructions depend on wire values, not the ambient
finite-register bound; both gate lists are genuine valid instantiations. -/
theorem gateCodes_width_independent {left right start : ℕ} (ops : List BooleanOp)
    (hl : start+ops.length ≤ left) (hr : start+ops.length ≤ right) (hv : Valid start ops) :
    (gates start ops hl).map BooleanGate.code=(gates start ops hr).map BooleanGate.code := by
  let slots := List.replicate (start+ops.length) ()
  have hs : start+ops.length ≤ slots.length := by simp [slots]
  exact (TM2Boolean.RPN.instructionWords_gates slots start ops hl hv hs).symm.trans
    (TM2Boolean.RPN.instructionWords_gates slots start ops hr hv hs)

end BooleanProgram

namespace TM2Boolean.PolyProgramCircuit

/-- Actual compiler gate words can be reused in the larger prep/D/selector
register while retaining the exact finite Boolean program semantics. -/
theorem compilerRawWords_correct {f : Str → Str} (P : PolyProgram id id f) (n total : ℕ)
    (hn : n+(compiled P n).ops.length ≤ total) :
    readRawBooleanFamilyWords (descriptionGenerator P (unary n))=
      (BooleanProgram.gates n (compiled P n).ops hn).map BooleanGate.code := by
  classical
  rw [descriptionGenerator_code,readRawBooleanFamilyWords_code]
  change (BooleanProgram.gates n (compiled P n).ops _).map BooleanGate.code=_
  exact BooleanProgram.gateCodes_width_independent _ _ hn
    (machineProgram_valid (capacity_pos P n) P.machine.code P.machine.input P.machine.main P.machine.initial
      (P.time.eval n) n).1

end TM2Boolean.PolyProgramCircuit

end InfoLossLAR.WorstCase

end P2MDyadicModule47

/- Helper module Solutions.AdvantageBridgeBodyFamily. -/
section P2MDyadicModule48

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

theorem castBodyCircuit_depth {left right : ℕ} (h : left=right) (circuit : Layered left) :
    depth (castBodyCircuit h circuit)=depth circuit := by cases h; rfl

theorem castBodyCircuit_wellFormed {left right : ℕ} (h : left=right) (circuit : Layered left)
    (hc : ∀ layer∈circuit,LayerOk layer) : ∀ layer∈castBodyCircuit h circuit,LayerOk layer := by
  cases h; exact hc

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget RPN

open scoped BigOperators Classical

variable {f : Str → Str} (P : PolyProgram id id f)

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqLabelMachineListBool_solutions_4

attribute [local instance] InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit.instDecidableEqStateMachineListBool_solutions_4

@[fun_prop] theorem quantumDescription_poly : Poly (quantumDescription P) := by
  unfold quantumDescription
  fun_prop

theorem quantumDescription_code (n : ℕ) : quantumDescription P (unary n)=encFamilyAt (family P) n := by
  unfold quantumDescription
  rw [descriptionGenerator_code,compileBooleanDescription_code,compileReversibleDescription_code]
  rfl

@[fun_prop] theorem multiTotalSlots_poly : Poly (multiTotalSlots P) := by
  have hp : Poly (fun word : Str => List.replicate ((spacePolynomial P).eval word.length) ()) := by
    have h := Poly.comp (f := fun xs : List Unit => List.replicate ((spacePolynomial P).eval xs.length) ())
      (g := fun word : Str => word.map (fun _ => ())) (polynomialSlots_poly (spacePolynomial P)) (by fun_prop)
    simpa only [List.length_map] using h
  unfold multiTotalSlots
  fun_prop

@[fun_prop] theorem multiOutputWords_poly : Poly (multiOutputWords P) := by
  unfold multiOutputWords
  fun_prop

theorem multiOutputWords_code (n : ℕ) : multiOutputWords P (unary n)=
    (List.ofFn (fun i : Fin (capacity P n) => outputWire P n i (some true))).map
      (fun wire => encNat wire.val) := by
  have hslots : (request P (unary n)).2.1.length=capacity P n := by
    rw [request_unary]
    simp
  have hr (index : ℕ) (hi : index < capacity P n) :
      generatedProgramOutputAddress P (unary n) index=
        (outputWire P n ⟨index,hi⟩ (some true)).val :=
    generatedProgramOutputAddress_eq P n ⟨index,hi⟩
  unfold multiOutputWords generatedAddressRange
  rw [hslots]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro index hleft hright
    have hi : index < capacity P n := by simpa only [List.length_map,List.length_ofFn] using hright
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,Nat.zero_add,hr index hi]
    apply boundedNat_eq
    have ha := ancilla_bound P n
    have ho := (outputWire P n ⟨index,hi⟩ (some true)).isLt
    simp only [multiTotalSlots,List.length_append,List.length_map,List.length_replicate,
      List.length_singleton,unary] 
    omega

theorem paddedOutput_eq_append (word : Str) :
    paddedOutput P word=f word++List.replicate (capacity P word.length-(f word).length) false := by
  have hl := actualOutput_length_lt_capacity P word
  apply List.ext_getElem
  · simp only [paddedOutput,List.length_ofFn,List.length_append,List.length_replicate]
    omega
  · intro index hleft hright
    simp only [paddedOutput,List.getElem_ofFn]
    by_cases hi : index < (f word).length
    · simp [List.getElem_append_left hi,List.getElem?_eq_getElem hi]
    · simp [List.getElem_append_right (Nat.le_of_not_gt hi),List.getElem?_eq_none (Nat.le_of_not_gt hi)]

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule49

/- Helper module Solutions.AdvantageBridgeBodyDEmission. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem leftCircuit_instructionWords {n m : ℕ} (circuit : Layered n) :
    (leftCircuit (m := m) circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by
  have hg (gate : Instr n) : encInstr (leftInstruction (m := m) gate)=encInstr gate := by cases gate <;> rfl
  simp only [leftCircuit,List.map_map,Function.comp_def,hg]

theorem rightCircuit_instructionWords_congr {n : ℕ} (left right : ℕ) (he : left=right) (circuit : Layered n) :
    (rightCircuit (n := left) circuit).map (List.map encInstr)=
      (rightCircuit (n := right) circuit).map (List.map encInstr) := by cases he; rfl

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization

theorem castBodyCircuit_instructionWords {left right : ℕ} (he : left=right) (circuit : Layered left) :
    (castBodyCircuit he circuit).map (List.map encInstr)=circuit.map (List.map encInstr) := by cases he; rfl

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeRepeatedQueryUniform. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RepeatedQuery

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

open scoped BigOperators Classical

noncomputable section

theorem loadedBlocks_physical (Q : Family) (L J : Polynomial ℕ) (n : ℕ)
    (queries : Fin (J.eval n) → Bits (L.eval n)) :
    bundlePhysical (loadedBlocks Q L J n queries)=bundlePhysical (blocks Q L J n) := by
  rw [bundlePhysical_fold,bundlePhysical_fold]
  congr 1
  simp only [loadedBlocks,blocks,List.map_ofFn,Function.comp_def,familyBlock]

@[fun_prop] theorem lastDescription_poly : Poly lastDescription := by
  unfold lastDescription
  fun_prop

theorem lastDescription_correct (Q : Family) (maximum : ℕ) :
    lastDescription (describedQueryBlocks Q maximum)=(unary maximum,encFamilyAt Q maximum) := by
  unfold lastDescription describedQueryBlocks
  rw [List.ofFn_succ']
  simp

@[fun_prop] theorem frames_poly (J : Polynomial ℕ) : Poly (frames J) := by
  unfold frames
  fun_prop

theorem frames_correct (Q : Family) (L J : Polynomial ℕ) (n : ℕ) :
    frames J (unary n,describedQueryBlocks Q (L.eval n))=(blocks Q L J n).map blockFrameWords := by
  unfold frames
  rw [lastDescription_correct,readFamilyFrame_correct]
  simp only [repeatSlots,unary,List.length_replicate,List.map_replicate,
    blocks,List.map_ofFn,Function.comp_def,blockFrameWords,familyBlock,List.ofFn_const]

end

end InfoLossLAR.WorstCase.RepeatedQuery

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

end InfoLossLAR.WorstCase

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeLoadedBatchShift. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase QAlgorithms.Complexity

open scoped BigOperators Classical

theorem shiftOp_valid (offset start : ℕ) (op : BooleanOp) (h : op.Valid start) :
    (shiftOp offset op).Valid (offset+start) := by
  cases op <;> simp_all [shiftOp,BooleanOp.Valid,BooleanOp.sources]

theorem shiftOp_eval (offset : ℕ) (op : BooleanOp) (state : ℕ → Bool) :
    (shiftOp offset op).eval state=op.eval (fun i => state (offset+i)) := by
  cases op <;> rfl

theorem shiftOp_assign (offset target : ℕ) (op : BooleanOp) (state : ℕ → Bool) :
    (fun i => (shiftOp offset op).assign (offset+target) state (offset+i))=
      op.assign target (fun i => state (offset+i)) := by
  funext i
  by_cases hi : i=target
  · subst i
    simp only [BooleanOp.assign,Function.update_self,shiftOp_eval]
  · have hs : offset+i ≠ offset+target := by omega
    simp only [BooleanOp.assign,Function.update_of_ne hs,Function.update_of_ne hi]

theorem shifted_valid (offset start : ℕ) (ops : List BooleanOp)
    (h : BooleanProgram.Valid start ops) :
    BooleanProgram.Valid (offset+start) (ops.map (shiftOp offset)) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op rest ih =>
    change (shiftOp offset op).Valid (offset+start) ∧
      BooleanProgram.Valid (offset+start+1) (rest.map (shiftOp offset))
    refine ⟨shiftOp_valid offset start op h.1,?_⟩
    convert ih (start+1) h.2 using 1 <;> omega

/-- A rebased real Boolean program has exactly the original local semantics.
All prefix and garbage values may be arbitrary. -/
theorem shifted_run (offset start : ℕ) (ops : List BooleanOp) (state : ℕ → Bool) :
    (fun i => BooleanProgram.run (offset+start) (ops.map (shiftOp offset)) state (offset+i))=
      BooleanProgram.run start ops (fun i => state (offset+i)) := by
  induction ops generalizing start state with
  | nil => rfl
  | cons op rest ih =>
    change (fun i => BooleanProgram.run (offset+start+1) (rest.map (shiftOp offset))
      ((shiftOp offset op).assign (offset+start) state) (offset+i))=
      BooleanProgram.run (start+1) rest (op.assign start (fun i => state (offset+i)))
    rw [show offset+start+1=offset+(start+1) by omega]
    rw [ih,shiftOp_assign]

end Integration9_9.LoadedBatch

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeLoadedBatchRebase. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase QAlgorithms.Complexity

private theorem shifted_eq_iff {n : ℕ} (offset : ℕ) (a b : Fin n) :
    Fin.natAdd offset a=Fin.natAdd offset b ↔ a=b := by
  constructor
  · intro h
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  · exact congrArg _

theorem shifted_reversible_compile {n : ℕ} (offset : ℕ) (gate : ReversibleGate n) :
    (shiftReversible offset gate).compile=rightCircuit gate.compile := by
  cases gate <;> rfl

theorem shifted_boolean_compile {n : ℕ} (offset : ℕ) (gate : BooleanGate n) :
    (shiftBoolean offset gate).compile=gate.compile.map (shiftReversible offset) := by
  cases gate with
  | constant target bit => cases bit <;> rfl
  | copy source target h => rfl
  | negate source target h => rfl
  | xor first second target hf hs => rfl
  | and first second target hf hs =>
    simp only [shiftBoolean,BooleanGate.compile,shifted_eq_iff]
    split_ifs <;> rfl

theorem shifted_reversible_program_compile {n : ℕ} (offset : ℕ) (gates : List (ReversibleGate n)) :
    compileReversible (gates.map (shiftReversible offset))=rightCircuit (compileReversible gates) := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
    change (shiftReversible offset gate).compile ++ compileReversible (rest.map (shiftReversible offset)) =
      rightCircuit (gate.compile ++ compileReversible rest)
    rw [shifted_reversible_compile, ih]
    simp only [rightCircuit,List.map_append]

theorem shifted_boolean_program_compile {n : ℕ} (offset : ℕ) (gates : List (BooleanGate n)) :
    compileReversible (booleanToReversible (gates.map (shiftBoolean offset)))=
      rightCircuit (compileReversible (booleanToReversible gates)) := by
  have he : booleanToReversible (gates.map (shiftBoolean offset))=
      (booleanToReversible gates).map (shiftReversible offset) := by
    induction gates with
    | nil => rfl
    | cons gate rest ih =>
      change (shiftBoolean offset gate).compile ++ booleanToReversible (rest.map (shiftBoolean offset)) =
        (gate.compile ++ booleanToReversible rest).map (shiftReversible offset)
      rw [shifted_boolean_compile,ih,List.map_append]
  rw [he,shifted_reversible_program_compile]

/-- Physical rebasing commutes with the actual malformed-reference fallback. -/
theorem shifted_toGate {n : ℕ} (offset : ℕ) (op : BooleanOp) (target : Fin n) :
    (shiftOp offset op).toGate (Fin.natAdd offset target)=shiftBoolean offset (op.toGate target) := by
  cases op <;> simp only [shiftOp,BooleanOp.toGate,Fin.val_natAdd,Nat.add_lt_add_iff_left]
  all_goals (try split_ifs) <;> rfl

/-- The real global fresh assignment program is the literal shifted local
Boolean gate list, so its emitted Clifford+T instructions agree exactly. -/
theorem shifted_program_gates {n start : ℕ} (offset : ℕ) (ops : List BooleanOp)
    (h : start+ops.length≤n) :
    BooleanProgram.gates (offset+start) (ops.map (shiftOp offset))
      (by simp only [List.length_map];omega : offset+start+(ops.map (shiftOp offset)).length≤offset+n)=
      (BooleanProgram.gates start ops h).map (shiftBoolean offset) := by
  induction ops generalizing start with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons,BooleanProgram.gates,shifted_toGate]
    congr 1
    · exact shifted_toGate offset op ⟨start, by simp only [List.length_cons] at h;omega⟩
    · simpa only [Nat.add_assoc] using ih (start := start+1)
        (by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)

end Integration9_9.LoadedBatch

end P2MDyadicModule53

/- Helper module Solutions.AdvantageBridgeBodyBooleanEmission. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.BooleanProgram

open QAlgorithms.Complexity

theorem gateCodes_start_congr {total left right : ℕ} (he : left=right) (ops : List BooleanOp)
    (hl : left+ops.length ≤ total) (hr : right+ops.length ≤ total) :
    (gates left ops hl).map BooleanGate.code=(gates right ops hr).map BooleanGate.code := by cases he; rfl

end InfoLossLAR.WorstCase.BooleanProgram

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime TM2PlatformSerialization TM2Boolean.RPN

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule54

/- Helper module Solutions.AdvantageBridgeBodyUniform. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option maxHeartbeats 500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

@[fun_prop] theorem readFamilyCircuitLayers_poly : Poly readFamilyCircuitLayers := by
  have hr : Poly (fun xs : Str => (readUnary xs).2) := Poly.comp Poly.snd readUnary_poly
  have ht : Poly (fun xs : Str => (readUnary ((readUnary xs).2)).2) :=
    Poly.comp (f := fun xs : Str => (readUnary xs).2) (g := fun xs : Str => (readUnary xs).2) hr hr
  have hp : Poly (fun xs : Str => readCircuitLayers ((readUnary ((readUnary xs).2)).2)) :=
    Poly.comp readCircuitLayers_poly ht
  exact Poly.comp (f := fun x : Str × List (List Str) => x.2)
    (g := fun xs : Str => readCircuitLayers ((readUnary ((readUnary xs).2)).2)) Poly.snd hp

theorem readFamilyCircuitLayers_correct (F : Family) (n : ℕ) :
    readFamilyCircuitLayers (encFamilyAt F n)=(F.circ n).map (List.map encInstr) := by
  unfold readFamilyCircuitLayers encFamilyAt
  simp only [List.append_assoc,readUnary_append]
  have h := readCircuitLayers_append (F.circ n) []
  simpa only [List.append_nil] using congrArg Prod.snd h

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2PlatformSerialization InfoLossLAR.WorstCase.TM2Boolean.RPN

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule55

/- Helper module Solutions.AdvantageBridgeBundleBasis. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem familyBlock_input_basis (D : Family) (query : Str) (length : ℕ) :
    (familyBlock D length (fun index => (query[index.val]?).getD false)).input=
      computationalBasis (familyInputBits D query length) := by
  change basisInput (a := D.anc length) (fun index => (query[index.val]?).getD false)=_
  rw [basisInput_eq_computationalBasis]
  apply congrArg computationalBasis
  funext index
  refine Fin.addCases (fun i => ?_) (fun i => ?_) index
  · simp [familyInputBits,i.isLt]
  · simp (disch := omega) [familyInputBits]

theorem sourceValueAt_get (sources : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ)
    (hi : index < sources.length) :
    sourceValueAt sources state index=registerLoadValue sources[index] state := by
  simp only [sourceValueAt,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

theorem sourceValueAt_append (first second : List (Bool × ℕ)) (state : ℕ → Bool) (index : ℕ) :
    sourceValueAt (first++second) state index=
      if index < first.length then sourceValueAt first state index else sourceValueAt second state (index-first.length) := by
  unfold sourceValueAt
  by_cases hi : index < first.length
  · rw [List.getElem?_append_left hi,if_pos hi]
  · rw [List.getElem?_append_right (by omega),if_neg hi]

theorem dBlockLoad_valueAt (querySources : List ℕ) (request slots : List Unit) (state : ℕ → Bool) (index : ℕ) :
    sourceValueAt (dBlockLoadSources querySources request slots) state index=
      if index < slots.length then
        (if index < request.length then state ((querySources[index]?).getD 0) else false)
      else false := by
  unfold sourceValueAt dBlockLoadSources
  by_cases hi : index < slots.length
  · rw [List.getElem?_map,List.getElem?_range hi]
    simp only [Option.map_some,Option.getD_some,registerLoadValue,decide_eq_true_eq,if_pos hi]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hi]

end InfoLossLAR.WorstCase

end P2MDyadicModule56

/- Helper module Solutions.AdvantageBridgeSelectorTensor. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- A basis ancilla can be summed out exactly even for an arbitrary event. -/
theorem tensorBasis_event_probability {left right : ℕ} (state : QState left)
    (bits : Bits right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖tensorState state (computationalBasis bits) input‖^2 else 0)=
      ∑ input : Bits left,if event (Fin.append input bits) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (leftRegister input) (rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,leftRegister]
    · simp only [Fin.append_right,rightRegister]
  have hsum := sum_registers (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖state first*computationalBasis bits second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖state (leftRegister input)*computationalBasis bits (rightRegister input)‖^2 else 0)=_
  rw [hsum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.sum_eq_single bits]
  · simp [computationalBasis]
  · intro second _ hne
    simp [computationalBasis,hne]
  · simp

end InfoLossLAR.WorstCase

end P2MDyadicModule57

/- Helper module Solutions.AdvantageBridgeBodyAcceptance. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open scoped BigOperators

/-- A retained computational-basis prefix has no probabilistic contribution. -/
theorem basisTensor_event_probability {left right : ℕ} (bits : Bits left)
    (state : QState right) (event : Bits (left+right) → Bool) :
    (∑ input : Bits (left+right),if event input then
      ‖tensorState (computationalBasis bits) state input‖^2 else 0)=
      ∑ input : Bits right,if event (Fin.append bits input) then ‖state input‖^2 else 0 := by
  classical
  have hsplit (input : Bits (left+right)) :
      Fin.append (leftRegister input) (rightRegister input)=input := by
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · simp only [Fin.append_left,leftRegister]
    · simp only [Fin.append_right,rightRegister]
  have hsum := sum_registers (fun first : Bits left => fun second : Bits right =>
    if event (Fin.append first second) then ‖computationalBasis bits first*state second‖^2 else 0)
  simp only [hsplit] at hsum
  change (∑ input : Bits (left+right),if event input then
    ‖computationalBasis bits (leftRegister input)*state (rightRegister input)‖^2 else 0)=_
  rw [hsum,Finset.sum_eq_single bits]
  · simp [computationalBasis]
  · intro first _ hne
    simp [computationalBasis,hne]
  · simp

end InfoLossLAR.WorstCase

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial QMCNumericRuntime TM2PlatformSerialization

open scoped BigOperators

end Integration9_9.LARCoinLayout

end

end P2MDyadicModule58

/- Helper module Solutions.RegevBridgeLoadedBatchPostprocess. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open scoped BigOperators

@[simp] theorem sourceWord_length {old : ℕ} (sources : List (Fin old)) (state : ℕ → Bool) :
    (sourceWord sources state).length=sources.length := by simp [sourceWord]

theorem copySources_valid {old : ℕ} (sources : List (Fin old)) :
    ∀ source∈copySources sources,source.1=true → source.2<old := by
  intro source hs _
  obtain ⟨wire,_,rfl⟩ := List.mem_map.mp hs
  exact wire.isLt

theorem postOps_valid {f : Str → Str} (P : PolyProgram id id f) {old : ℕ}
    (sources : List (Fin old)) : BooleanProgram.Valid old (postOps P sources) := by
  classical
  rw [postOps,BooleanProgram.valid_append]
  refine ⟨registerLoadOps_valid _ _ (copySources_valid sources),?_⟩
  simp only [registerLoadOps_length,copySources,List.length_map]
  apply shifted_valid
  exact (machineProgram_valid (capacity_pos P sources.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval sources.length) sources.length).1

theorem loaded_local_input {old : ℕ} (sources : List (Fin old)) (state : ℕ → Bool)
    (hz : ∀ i, old ≤ i → state i=false) :
    (fun i => BooleanProgram.run old (registerLoadOps (copySources sources)) state (old+i))=
      wordExtension (sourceWord sources state) := by
  funext i
  by_cases hi : i<sources.length
  · rw [registerLoadOps_value old _ (copySources_valid sources) state i
      (by simpa [copySources] using hi)]
    simp only [copySources,List.getElem_map,registerLoadValue,ite_true]
    rw [wordExtension_before _ i (by simpa using hi)]
    simp only [sourceWord,List.getElem_map]
  · rw [BooleanProgram.run_after]
    · rw [hz _ (by omega),wordExtension_after _ _ (by simpa using Nat.le_of_not_gt hi)]
    · simp only [registerLoadOps_length,copySources,List.length_map];omega

/-- Correct postprocessing of every designated bit on each basis component.
This is a deterministic statement on the actual compiled program. -/
theorem postOps_output {f : Str → Str} (P : PolyProgram id id f) {old : ℕ}
    (sources : List (Fin old)) (state : ℕ → Bool) (hz : ∀ i, old ≤ i → state i=false)
    (index : Fin (capacity P sources.length)) :
    BooleanProgram.run old (postOps P sources) state
      (old+(outputWire P sources.length index (some true)).val)=
      ((f (sourceWord sources state))[index.val]?).getD false := by
  rw [postOps,BooleanProgram.run_append]
  simp only [registerLoadOps_length,copySources,List.length_map]
  have he := congrFun (shifted_run old sources.length (compiled P sources.length).ops
    (BooleanProgram.run old (registerLoadOps (copySources sources)) state))
    (outputWire P sources.length index (some true)).val
  rw [loaded_local_input sources state hz] at he
  change BooleanProgram.run _ _ (BooleanProgram.run old (registerLoadOps (copySources sources)) state) _ = _
  rw [he]
  have hout (n : ℕ) (word : Str) (hlen : word.length=n) (i : Fin (capacity P n)) :
      BooleanProgram.run n (compiled P n).ops (wordExtension word)
        (outputWire P n i (some true)).val=((f word)[i.val]?).getD false := by
    subst n
    have hc := output_correct P word i (some true)
    change BooleanProgram.run word.length (compiled P word.length).ops (wordExtension word)
      (outputWire P word.length i (some true)).val=decide (some true=(f word)[i.val]?) at hc
    rw [hc]
    cases hb : (f word)[i.val]? with
    | none => rfl
    | some bit => cases bit <;> rfl
  exact hout sources.length (sourceWord sources state) (sourceWord_length sources state) index

/-- Actual native postprocessing preserves the exact Born event probability
of the corresponding classical operation. Quantum garbage in the old register
is arbitrary; only the fresh work suffix is initialized to zero. -/
theorem postCircuit_event_probability {f : Str → Str} (P : PolyProgram id id f) {old : ℕ}
    (sources : List (Fin old)) (state : QState (postWidth P sources))
    (hz : ∀ input, state input ≠ 0 → ∀ i : Fin (postWidth P sources), old ≤ i.val → input i = false)
    (event : Str → Bool) :
    (∑ output : Bits (postWidth P sources),if event (postOutputs P sources output) then
      ‖runLayered (compileReversible (booleanToReversible (postGates P sources))) state output‖^2 else 0)=
      ∑ input : Bits (postWidth P sources),if event (paddedOutput P
        (sourceWord sources (selectorBitsExtension input))) then ‖state input‖^2 else 0 := by
  rw [booleanCircuit_event_probability (postGates P sources)
    (BooleanProgram.fresh (postOps P sources) _) state _ (fun input => event (postOutputs P sources input))]
  · apply Finset.sum_congr rfl
    intro input _
    by_cases hs : state input=0
    · simp [hs]
    · have hzero : ∀ i, old ≤ i → selectorBitsExtension input i=false := by
        intro i hi
        by_cases hn : i<postWidth P sources
        · rw [show i=(⟨i,hn⟩ : Fin (postWidth P sources)).val from rfl,
            selectorBitsExtension_get]
          exact hz input hs _ hi
        · simp [selectorBitsExtension,hn]
      have houtputs : postOutputs P sources (booleanRun (postGates P sources) input)=
          paddedOutput P (sourceWord sources (selectorBitsExtension input)) := by
        unfold postGates
        have hsem : booleanRun (BooleanProgram.gates old (postOps P sources)
            (by simp only [postOps_length,postWidth];omega)) input=
            (fun i : Fin (postWidth P sources) =>
              BooleanProgram.run old (postOps P sources) (selectorBitsExtension input) i.val) := by
          simpa only [selectorBitsExtension_get] using
            BooleanProgram.semantics (total := postWidth P sources) (postOps P sources)
              (by simp only [postOps_length,postWidth];omega) (postOps_valid P sources)
              (selectorBitsExtension input)
        rw [hsem]
        unfold postOutputs paddedOutput
        simp only [sourceWord_length]
        apply congrArg List.ofFn
        funext i
        exact postOps_output P sources _ hzero i
      rw [houtputs]
  · intro input hs gate hg
    obtain ⟨hl,_⟩ := BooleanProgram.target_range (postOps P sources) _ gate hg
    exact hz input hs gate.target hl

end Integration9_9.LoadedBatch

end

end P2MDyadicModule59

/- Helper module Solutions.RegevBridgeLoadedBatchPostTensor. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open scoped BigOperators Classical

/-- Copying only designated old-register bits gives a literal native input
word, even when those old bits come from a quantum superposition. -/
theorem sourceWord_append {old fresh : ℕ} (sources : List (Fin old)) (bits : Bits old)
    (scratch : Bits fresh) : sourceWord sources (selectorBitsExtension (Fin.append bits scratch))=
      sources.map bits := by
  unfold sourceWord
  apply List.map_congr_left
  intro source _
  have he : source.val=(Fin.castAdd fresh source).val := rfl
  rw [he,selectorBitsExtension_get,Fin.append_left]

/-- Exact actual postprocessing channel with fresh zero work qubits. This
sums out the entire old quantum state, including all oracle garbage, and
reads only the specified observable old bits. -/
theorem postCircuit_tensor_event_probability {f : Str → Str} (P : PolyProgram id id f)
    {old : ℕ} (sources : List (Fin old)) (state : QState old) (event : Str → Bool) :
    (∑ output : Bits (postWidth P sources),if event (postOutputs P sources output) then
      ‖runLayered (compileReversible (booleanToReversible (postGates P sources)))
        (tensorState state (computationalBasis
          (fun _ : Fin (sources.length+((compiled P sources.length).ops.length+1)) => false))) output‖^2 else 0)=
      ∑ input : Bits old,if event (paddedOutput P (sources.map input)) then ‖state input‖^2 else 0 := by
  have hz : ∀ input,tensorState state (computationalBasis
        (fun _ : Fin (sources.length+((compiled P sources.length).ops.length+1)) => false)) input≠0 →
      ∀ i : Fin (postWidth P sources),old ≤ i.val → input i=false := by
    intro input hs i hi
    have hb : computationalBasis (fun _ : Fin (sources.length+((compiled P sources.length).ops.length+1)) => false)
        (rightRegister input)≠0 := by
      intro he
      apply hs
      simp only [tensorState,he,mul_zero]
    have he : rightRegister input=(fun _ => false) := by
      by_contra hn
      apply hb
      simp [computationalBasis,hn]
    let j : Fin (sources.length+((compiled P sources.length).ops.length+1)) :=
      ⟨i.val-old,by have hh := i.isLt;unfold postWidth at hh;omega⟩
    have hij : i=Fin.natAdd old j := by apply Fin.ext;simp only [Fin.val_natAdd];dsimp only [j];omega
    rw [hij]
    exact congrFun he j
  rw [postCircuit_event_probability P sources _ hz event]
  dsimp only [postWidth] at *
  rw [tensorBasis_event_probability]
  simp only [sourceWord_append]

end Integration9_9.LoadedBatch

end

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeLoadedBatchLoader. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

@[fun_prop] theorem loadSourcesFromFrame_poly {f : Str → Str} (P : PolyProgram id id f) :
    Poly (fun x : (Str × List ℕ) × (List Unit × List Unit) =>
      loadSourcesFromFrame P x.1.1 x.1.2 x.2.1 x.2.2) := by
  unfold loadSourcesFromFrame
  fun_prop

theorem trialBlocks_width {f : Str → Str} (P : PolyProgram id id f) (Q : Family)
    (width : ℕ) (word : Str) (trials : List ℕ) :
    bundleWidth (trialBlocks f P Q width word trials)=trials.length*(width+(Q.anc width+1)) := by
  induction trials with
  | nil => simp [trialBlocks,bundleWidth]
  | cons trial rest ih =>
    simp only [trialBlocks,List.map_cons,bundleWidth,familyBlock,List.length_cons] at *
    rw [ih]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem trialBlocks_basis {f : Str → Str} (P : PolyProgram id id f) (Q : Family)
    (width : ℕ) (word : Str) (trials : List ℕ) :
    bundleState (trialBlocks f P Q width word trials)=
      computationalBasis (fun index => trialBits f Q width word trials index.val) := by
  induction trials with
  | nil =>
    change (fun _ : Bits 0 => (1:ℂ))=computationalBasis (fun _ => false)
    funext state
    have he : state=(fun _ : Fin 0 => false) := Subsingleton.elim _ _
    simp [computationalBasis,he]
  | cons trial rest ih =>
    change tensorState (familyBlock Q width (fun i => ((f word)[trial*width+i.val]?).getD false)).input
      (bundleState (trialBlocks f P Q width word rest))=_
    have hblock : (familyBlock Q width (fun i => ((f word)[trial*width+i.val]?).getD false)).input=
        computationalBasis (familyInputBits Q (queryWord f width word trial) width) := by
      have he : (fun i : Fin width => ((f word)[trial*width+i.val]?).getD false)=
          (fun i : Fin width => ((queryWord f width word trial)[i.val]?).getD false) := by
        funext i
        simp [queryWord]
      rw [he]
      exact familyBlock_input_basis Q _ width
    rw [hblock,ih,←computationalBasis_tensor]
    apply congrArg computationalBasis
    funext index
    refine Fin.addCases (fun i => ?_) (fun i => ?_) index
    · have hil : i.val<width+(Q.anc width+1) := i.isLt
      simp only [Fin.append_left,Fin.val_castAdd,trialBits,if_pos hil,familyInputBits]
      by_cases hi : i.val<width
      · simp [hi,queryWord]
      · simp [hi]
    · simp (disch := omega) [trialBits,familyBlock]

theorem loadSourcesFromFrame_valid {f : Str → Str} (P : PolyProgram id id f)
    (n : ℕ) (trials : List ℕ) (request slots : List Unit)
    (hcap : ∀ trial∈trials,trial*request.length+request.length≤capacity P n) :
    ∀ source∈loadSourcesFromFrame P (unary n) trials request slots,
      source.1=true → source.2<n+((compiled P n).ops.length+1) := by
  intro source hs
  obtain ⟨trial,ht,hs⟩ := List.mem_flatMap.mp hs
  apply dBlockLoadSources_valid _ _ _ _ _ (generatedAddressRange_bounded P n request _ (hcap trial ht)) source hs
  simp [generatedAddressRange]

/-- Every query block is loaded from its own consecutive preprocessor output
cells. The oracle work and output ancillas are all genuinely initialized zero. -/
theorem loadSourcesFromFrame_value {f : Str → Str} (P : PolyProgram id id f) (Q : Family)
    (width : ℕ) (word : Str) (trials : List ℕ)
    (hcap : ∀ trial∈trials,trial*width+width≤capacity P word.length) (index : ℕ) :
    sourceValueAt (loadSourcesFromFrame P (unary word.length) trials
      (List.replicate width ()) (List.replicate (width+(Q.anc width+1)) ()))
      (generatedQueryBits P word) index=trialBits f Q width word trials index := by
  induction trials generalizing index with
  | nil => rfl
  | cons trial rest ih =>
    simp only [loadSourcesFromFrame,List.flatMap_cons]
    rw [sourceValueAt_append,dBlockLoadSources_length]
    simp only [List.length_replicate]
    by_cases hi : index<width+(Q.anc width+1)
    · rw [if_pos hi,dBlockLoad_valueAt]
      simp only [List.length_replicate,if_pos hi,trialBits]
      by_cases hj : index<width
      · rw [if_pos hj,if_pos hj]
        have ha : index<(generatedAddressRange P (unary word.length) (List.replicate width ())
            (trial*width)).length := by simp [generatedAddressRange,hj]
        rw [List.getElem?_eq_getElem ha,Option.getD_some]
        simp only [generatedAddressRange,List.getElem_map,List.getElem_range,List.length_replicate]
        rw [generatedQueryBits_output P word
          ⟨trial*width+index,by have hc := hcap trial (by simp);omega⟩]
        cases hb : (f word)[trial*width+index]? with
        | none => rfl
        | some bit => cases bit <;> rfl
      · rw [if_neg hj,if_neg hj]
    · rw [if_neg hi]
      simpa only [trialBits,if_neg hi,loadSourcesFromFrame,List.length_replicate] using
        ih (fun other ho => hcap other (by simp [ho])) (index-(width+(Q.anc width+1)))

end Integration9_9.LoadedBatch

end

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeLoadedBatchMachine. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

open Integration9_9.LARCoinLayout

variable {f : Str → Str} (P : PolyProgram id id f) (Q : Family) (L J : Polynomial ℕ)

@[fun_prop] theorem preAncSlots_poly : Poly (preAncSlots P) := by unfold preAncSlots;fun_prop

theorem preAncSlots_length (n : ℕ) : (preAncSlots P (unary n)).length=(compiled P n).ops.length := by
  unfold preAncSlots
  rw [descriptionGenerator_code]
  simp only [BooleanFamily.code,booleanFamily,List.append_assoc,unaryPayload_encNat,
    List.length_map,unary,List.length_replicate]

@[fun_prop] theorem preSlots_poly : Poly (preSlots P) := by unfold preSlots;fun_prop

theorem preSlots_length (n : ℕ) : (preSlots P (unary n)).length=preWidth P n := by
  simp only [preSlots,List.length_append,List.length_map,preAncSlots_length,List.length_singleton]
  simp only [unary,List.length_replicate,preWidth];omega

@[fun_prop] theorem querySlots_poly : Poly (querySlots J) := by unfold querySlots;fun_prop

theorem querySlots_length (n : ℕ) :
    (querySlots J (unary n,describedQueryBlocks Q (L.eval n))).length=callWidth Q L J n := by
  unfold querySlots
  rw [RepeatedQuery.frames_correct]
  simp [RepeatedQuery.blocks,blockFrameWords,familyBlock,unary,callWidth,
    List.length_flatMap]

@[fun_prop] theorem ancSlots_poly : Poly (ancSlots P J) := by unfold ancSlots;fun_prop

@[fun_prop] theorem allSlots_poly : Poly (allSlots P J) := by unfold allSlots;fun_prop

theorem ancSlots_length (n : ℕ) :
    (ancSlots P J (unary n,describedQueryBlocks Q (L.eval n))).length=machineAnc P Q L J n := by
  simp only [ancSlots,List.length_append,List.length_singleton,preAncSlots_length,querySlots_length,machineAnc]

theorem allSlots_length (n : ℕ) :
    (allSlots P J (unary n,describedQueryBlocks Q (L.eval n))).length=machineWidth P Q L J n := by
  simp only [allSlots,List.length_append,List.length_map,List.length_singleton,ancSlots_length]
  simp only [unary,List.length_replicate,machineWidth];omega

@[fun_prop] theorem sourcesEmitter_poly : Poly (sourcesEmitter P J) := by
  have ht : Poly (fun input : Str × List (Str × Str) =>
      List.range (RepeatedQuery.repeatSlots J input.1).length) :=
    Poly.comp (f := fun xs : List Unit => List.range xs.length)
      (g := fun input : Str × List (Str × Str) => RepeatedQuery.repeatSlots J input.1)
      Poly.list_indices (Poly.comp (RepeatedQuery.repeatSlots_poly J) Poly.fst)
  unfold sourcesEmitter
  exact Poly.comp (f := fun x : (Str × List ℕ) × (List Unit × List Unit) =>
      loadSourcesFromFrame P x.1.1 x.1.2 x.2.1 x.2.2)
    (g := fun input : Str × List (Str × Str) =>
      ((input.1,List.range (RepeatedQuery.repeatSlots J input.1).length),
       ((RepeatedQuery.lastDescription input.2).1.map (fun _ => ()),
        (readFamilyFrame (RepeatedQuery.lastDescription input.2)).1.map (fun _ => ()))))
    (loadSourcesFromFrame_poly P)
    (Poly.pair (Poly.pair (by fun_prop) ht) (Poly.pair (by fun_prop) (by fun_prop)))

theorem sourcesEmitter_correct (n : ℕ) :
    sourcesEmitter P J (unary n,describedQueryBlocks Q (L.eval n))=loadSources P Q L J n := by
  unfold sourcesEmitter
  simp only [RepeatedQuery.lastDescription_correct,readFamilyFrame_correct]
  simp only [RepeatedQuery.repeatSlots,unary,List.length_replicate,List.map_replicate,loadSources]

theorem loadSources_valid (hfits : Fits P L J) (n : ℕ) :
    ∀ source∈loadSources P Q L J n,source.1=true → source.2<preWidth P n := by
  apply loadSourcesFromFrame_valid
  intro trial ht
  have htrial := List.mem_range.mp ht
  have hm := Nat.mul_le_mul_right (L.eval n) (Nat.succ_le_iff.mpr htrial)
  have hc := hfits n
  simpa only [List.length_replicate,Nat.succ_mul] using hm.trans hc

theorem prepared_valid (hfits : Fits P L J) (n : ℕ) :
    BooleanProgram.Valid n (preparedLoadOps P n (loadSources P Q L J n)) :=
  preparedLoadOps_valid P n _ (loadSources_valid P Q L J hfits n)

theorem machine_wellFormed (hQ : WellFormed Q) :
    ∀ n layer,layer∈(machine P Q L J).circ n → LayerOk layer := by
  intro n layer hl
  simp only [machine,machineCircuit,List.mem_append] at hl
  rcases hl with hp|hq
  · exact compileReversible_wellFormed _ layer hp
  · exact castBodyCircuit_wellFormed _ _
      (leftCircuit_wellFormed _ (rightCircuit_wellFormed _
        (bundleCircuit_wellFormed _ (by
          intro block hb
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
          exact hQ (L.eval n))))) layer hq

end Integration9_9.LoadedBatch

end

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeLoadedBatchUniform. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

open Integration9_9.LARCoinLayout

variable {f : Str → Str} (P : PolyProgram id id f) (Q : Family) (L J : Polynomial ℕ)

@[fun_prop] theorem zeroWord_poly : Poly (zeroWord P) := by unfold zeroWord;fun_prop

theorem zeroWord_correct (n : ℕ) : zeroWord P (unary n)=encNat 0++encNat (n+(compiled P n).ops.length) := by
  simp only [zeroWord,lengthToken_eq,List.length_append,List.length_map,preAncSlots_length]
  simp only [unary,List.length_replicate]

@[fun_prop] theorem preparedWords_poly : Poly (preparedWords P J) := by unfold preparedWords;fun_prop

theorem preparedWords_correct (hfits : Fits P L J) (n : ℕ) :
    preparedWords P J (unary n,describedQueryBlocks Q (L.eval n))=
      (preparedGates P Q L J n).map BooleanGate.code := by
  let total := machineWidth P Q L J n
  let sources := loadSources P Q L J n
  have hp : n+(compiled P n).ops.length≤total := by dsimp [total];rw [width_eq];unfold preWidth;omega
  have hstart : (preSlots P (unary n)).length=n+(compiled P n).ops.length+1 := by rw [preSlots_length];unfold preWidth;omega
  have hd : (preSlots P (unary n)).length+sources.length≤total := by
    rw [preSlots_length]
    dsimp only [sources,total]
    rw [loadSources_length,width_eq];omega
  have hold : n+(compiled P n).ops.length+1+(registerLoadOps sources).length≤total := by
    rw [registerLoadOps_length]
    rw [hstart] at hd;exact hd
  have hs : ∀ source∈sources,source.1=true → source.2<(preSlots P (unary n)).length := by
    rw [preSlots_length];exact loadSources_valid P Q L J hfits n
  have hload := registerLoadGateWords_correct
    (allSlots P J (unary n,describedQueryBlocks Q (L.eval n)))
    (preSlots P (unary n)).length sources hs hd (by rw [allSlots_length];exact hd)
  have hload' : registerLoadGateWords (allSlots P J (unary n,describedQueryBlocks Q (L.eval n)))
      (preSlots P (unary n)).length sources=
      (BooleanProgram.gates (n+(compiled P n).ops.length+1) (registerLoadOps sources) hold).map BooleanGate.code :=
    hload.trans (BooleanProgram.gateCodes_start_congr hstart (registerLoadOps sources) _ hold)
  unfold preparedWords
  rw [sourcesEmitter_correct]
  change readRawBooleanFamilyWords (descriptionGenerator P (unary n))++[zeroWord P (unary n)]++
    registerLoadGateWords _ _ sources=_
  rw [compilerRawWords_correct P n total hp,zeroWord_correct,hload']
  unfold preparedGates preparedLoadOps
  rw [BooleanProgram.gates_append]
  simp only [List.map_append,BooleanProgram.gates,List.map_cons,BooleanGate.code,ite_false,
    List.singleton_append,List.append_assoc]
  rfl

@[fun_prop] theorem preparedDescription_poly : Poly (preparedDescription P J) := by unfold preparedDescription;fun_prop

theorem preparedDescription_correct (hfits : Fits P L J) (n : ℕ) :
    preparedDescription P J (unary n,describedQueryBlocks Q (L.eval n))=
      (preparedBooleanFamily P Q L J).code n := by
  unfold preparedDescription
  rw [lengthToken_eq,ancSlots_length,preparedWords_correct P Q L J hfits,serializeWords_eq]
  rfl

@[fun_prop] theorem preparedQuantumDescription_poly : Poly (preparedQuantumDescription P J) := by
  unfold preparedQuantumDescription;fun_prop

theorem preparedQuantumDescription_correct (hfits : Fits P L J) (n : ℕ) :
    preparedQuantumDescription P J (unary n,describedQueryBlocks Q (L.eval n))=
      encFamilyAt (preparedBooleanFamily P Q L J).reversible.compile n := by
  unfold preparedQuantumDescription
  rw [preparedDescription_correct P Q L J hfits,compileBooleanDescription_code,compileReversibleDescription_code]

@[fun_prop] theorem queryWordLayers_poly : Poly (queryWordLayers P J) := by unfold queryWordLayers;fun_prop

theorem queryWordLayers_correct (n : ℕ) :
    queryWordLayers P J (unary n,describedQueryBlocks Q (L.eval n))=
      (queryCircuit P Q L J n).map (List.map encInstr) := by
  unfold queryWordLayers
  rw [RepeatedQuery.frames_correct,bundleCircuitWordLayers_correct,shiftCircuitWords_correct]
  unfold queryCircuit
  rw [castBodyCircuit_instructionWords,leftCircuit_instructionWords]
  apply rightCircuit_instructionWords_congr
  simp only [List.length_map]
  exact preSlots_length P n

attribute [local irreducible] preparedQuantumDescription queryWordLayers

@[fun_prop] theorem wordLayers_poly : Poly (wordLayers P J) := by
  unfold wordLayers;fun_prop

theorem wordLayers_correct (hfits : Fits P L J) (n : ℕ) :
    wordLayers P J (unary n,describedQueryBlocks Q (L.eval n))=
      (machineCircuit P Q L J n).map (List.map encInstr) := by
  unfold wordLayers
  rw [preparedQuantumDescription_correct P Q L J hfits,readFamilyCircuitLayers_correct,queryWordLayers_correct]
  simp only [preparedBooleanFamily,BooleanFamily.reversible,ReversibleFamily.compile,machineCircuit,List.map_append]

end Integration9_9.LoadedBatch

end

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeLoadedBatchResources. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.LARCoinLayout

variable {f : Str → Str} (P : PolyProgram id id f) (Q : Family) (L J : Polynomial ℕ)

theorem queryCircuit_depth (n : ℕ) :
    depth (queryCircuit P Q L J n)=(J.eval n)*depth (Q.circ (L.eval n)) := by
  unfold queryCircuit
  rw [castBodyCircuit_depth,leftCircuit_depth,rightCircuit_depth]
  simp [bundleCircuit_depth,RepeatedQuery.blocks,List.map_ofFn,List.sum_ofFn,familyBlock]

/-- Real resource bounds include the native preprocessor workspace and all
loaded oracle registers, not just the number of calls. -/
theorem machine_polyBounded (hQ : PolyBounded Q) :
    ∃ p : Polynomial ℕ,∀ n,depth ((machine P Q L J).circ n) ≤ p.eval n ∧
      (machine P Q L J).anc n ≤ p.eval n ∧ (machine P Q L J).outLen n ≤ p.eval n := by
  obtain ⟨p,hdepth,hanc⟩ := hQ
  refine ⟨resourcePolynomial P L J p,?_⟩
  intro n
  have hc : callWidth Q L J n ≤ (J*(L+p.comp L+1)).eval n := by
    simp only [callWidth,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_one]
    apply Nat.mul_le_mul_left
    have hh := hanc (L.eval n)
    omega
  have hp := ancilla_bound P n
  have hpre : (preparedLoadOps P n (loadSources P Q L J n)).length ≤ 
      (spacePolynomial P+1+J*(L+p.comp L+1)).eval n := by
    rw [preparedLoadOps_length,loadSources_length]
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    omega
  have hpdepth := BooleanProgram.circuit_depth (preparedLoadOps P n (loadSources P Q L J n))
    (show n+(preparedLoadOps P n (loadSources P Q L J n)).length ≤ machineWidth P Q L J n from
      by rw [preparedLoadOps_length,loadSources_length,width_eq];unfold preWidth;omega)
  have hpdepth' := hpdepth.trans (Nat.mul_le_mul_left 74 hpre)
  have hqdepth := Nat.mul_le_mul_left (J.eval n) (hdepth (L.eval n))
  have hmachine : depth ((machine P Q L J).circ n) ≤ 
      74*(spacePolynomial P+1+J*(L+p.comp L+1)).eval n+(J*p.comp L).eval n := by
    change depth (compileReversible (booleanToReversible (preparedGates P Q L J n))++queryCircuit P Q L J n) ≤ _
    simp only [depth,List.length_append] at hpdepth' ⊢
    change depth (compileReversible (booleanToReversible (preparedGates P Q L J n)))+
      depth (queryCircuit P Q L J n) ≤ _
    rw [queryCircuit_depth]
    exact Nat.add_le_add hpdepth' (by simpa only [Polynomial.eval_mul,Polynomial.eval_comp] using hqdepth)
  have hmachineanc : (machine P Q L J).anc n ≤ 
      (spacePolynomial P+1+J*(L+p.comp L+1)).eval n := by
    change (compiled P n).ops.length+1+callWidth Q L J n ≤ _
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    omega
  simp only [resourcePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_one] at hmachine hmachineanc ⊢
  change _ ∧ _ ∧ J.eval n ≤ _
  omega

end Integration9_9.LoadedBatch

end

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeLoadedBatchPostFamily. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch.PostComposition

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.LARCoinLayout

variable (F : MFamily) {f : Str → Str} (P : PolyProgram id id f)

@[simp] theorem sources_length (n : ℕ) : (sources F n).length=n+F.outLen n := by simp [sources]

theorem embeddedCircuit_depth (n : ℕ) : depth (embeddedCircuit F P n)=depth (F.circ n) := by
  unfold embeddedCircuit
  rw [castBodyCircuit_depth,leftCircuit_depth]

theorem family_wellFormed
    (hF : ∀ n layer,layer∈F.circ n → LayerOk layer) :
    ∀ n layer,layer∈(family F P).circ n → LayerOk layer := by
  intro n
  apply castBodyCircuit_wellFormed
  intro layer hl
  rcases List.mem_append.mp hl with hleft|hpost
  · exact castBodyCircuit_wellFormed _ _ (leftCircuit_wellFormed _ (hF n)) layer hleft
  · exact compileReversible_wellFormed _ layer hpost

/-- The full gate list has polynomial resources whenever the original family
does; the native postprocessor's compiler space is included explicitly. -/
theorem family_polyBounded
    (hF : ∃ p : Polynomial ℕ,∀ n,depth (F.circ n) ≤ p.eval n ∧ F.anc n ≤ p.eval n ∧ F.outLen n ≤ p.eval n) :
    ∃ p : Polynomial ℕ,∀ n,depth ((family F P).circ n) ≤ p.eval n ∧
      (family F P).anc n ≤ p.eval n ∧ (family F P).outLen n ≤ p.eval n := by
  obtain ⟨p,hp⟩ := hF
  let inputBound : Polynomial ℕ := Polynomial.X+p
  let space : Polynomial ℕ := (spacePolynomial P).comp inputBound
  let outputs : Polynomial ℕ := (capacityPolynomial P).comp inputBound
  refine ⟨p+74*(inputBound+space)+p+1+inputBound+space+outputs,?_⟩
  intro n
  have hn : (sources F n).length ≤ inputBound.eval n := by
    rw [sources_length]
    simp only [inputBound,Polynomial.eval_add,Polynomial.eval_X]
    exact Nat.add_le_add_left (hp n).2.2 n
  have hspace : (compiled P (sources F n).length).ops.length ≤ space.eval n := by
    apply (ancilla_bound P (sources F n).length).trans
    simpa only [space,Polynomial.eval_comp] using polynomial_eval_mono (spacePolynomial P) hn
  have houtputs : capacity P (sources F n).length ≤ outputs.eval n := by
    rw [←capacityPolynomial_eval]
    simpa only [outputs,Polynomial.eval_comp] using
      (polynomial_eval_mono (capacityPolynomial P) hn : (capacityPolynomial P).eval (sources F n).length ≤
        (capacityPolynomial P).eval (inputBound.eval n))
  have hpost := BooleanProgram.circuit_depth (postOps P (sources F n))
    (show oldWidth F n+(postOps P (sources F n)).length ≤ postWidth P (sources F n) from
      by rw [postOps_length];unfold postWidth;omega)
  have hpost' : depth (compileReversible (booleanToReversible (postGates P (sources F n)))) ≤
      74*(inputBound+space).eval n := by
    apply hpost.trans
    rw [postOps_length,Polynomial.eval_add]
    exact Nat.mul_le_mul_left 74 (Nat.add_le_add hn hspace)
  have hdepth : depth ((family F P).circ n) ≤ (p+74*(inputBound+space)).eval n := by
    change depth (circuit F P n) ≤ _
    unfold circuit
    rw [castBodyCircuit_depth]
    simp only [depth,List.length_append]
    change depth (embeddedCircuit F P n)+depth (compileReversible (booleanToReversible (postGates P (sources F n)))) ≤ _
    rw [embeddedCircuit_depth]
    simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] using
      Nat.add_le_add (hp n).1 hpost'
  have hanc : (family F P).anc n ≤ (p+1+inputBound+space).eval n := by
    change F.anc n+1+(sources F n).length+(compiled P (sources F n).length).ops.length ≤ _
    simp only [Polynomial.eval_add,Polynomial.eval_one]
    have hfanc := (hp n).2.1
    omega
  change _ ∧ _ ∧ capacity P (sources F n).length ≤ _
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one] at hdepth hanc ⊢
  omega

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule65

/- Helper module Solutions.RegevBridgeLoadedBatchPostCompile. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

private theorem booleanCircuit_append {n : ℕ} (first second : List (BooleanGate n)) :
    compileReversible (booleanToReversible (first++second))=
      compileReversible (booleanToReversible first)++compileReversible (booleanToReversible second) := by
  simp only [booleanToReversible,List.flatMap_append,compileReversible]

/-- The global Boolean compiler is exactly the copy-load followed by the
shifted *actual* P circuit, not a circuit related only by abstract behavior. -/
theorem postCircuit_decompose {f : Str → Str} (P : PolyProgram id id f) {old : ℕ}
    (sources : List (Fin old)) :
    compileReversible (booleanToReversible (postGates P sources))=
      compileReversible (booleanToReversible
        (BooleanProgram.gates old (registerLoadOps (copySources sources))
          (by simp only [registerLoadOps_length,copySources,List.length_map];unfold postWidth;omega :
            old+(registerLoadOps (copySources sources)).length ≤ postWidth P sources)))++
      (show Layered (postWidth P sources) from
        rightCircuit (n := old) (TM2Boolean.PolyProgramCircuit.circuit P sources.length)) := by
  unfold postGates postOps
  rw [BooleanProgram.gates_append,booleanCircuit_append]
  congr 1
  simp only [registerLoadOps_length,copySources,List.length_map]
  rw [shifted_program_gates]
  rw [shifted_boolean_program_compile]
  rfl

end Integration9_9.LoadedBatch

end

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeLoadedBatchPostFrame. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch.PostComposition

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2StockLists Integration9_9.TM2PlatformSerialization

open QMCNumericRuntime

/-- Compose a real raw stock generator with a native descriptor builder,
retaining its unary input. The opaque generator may use any callee alphabet. -/
theorem generator_builder_polyTime (generator : Str → Str) (hg : PolyTimeComputable generator)
    (builder : Str × Str → Str) (hb : Poly builder) :
    PolyTimeComputable (fun word => builder (word,generator word)) := by
  obtain ⟨source⟩ := hg
  obtain ⟨quoted⟩ := stock_quoted source
  obtain ⟨paired⟩ := stock_pairWithInput quoted
  obtain ⟨built⟩ := TM2Composition.comp paired hb.program.stock
  obtain ⟨output⟩ := TM2Composition.comp built BooleanLists.unpackProgram.stock
  obtain ⟨whole⟩ := TM2Composition.comp BooleanLists.packProgram.stock output
  exact ⟨congrProgram whole _ (fun _ => rfl)⟩

@[fun_prop] theorem readWireWord_poly : Poly readWireWord := by
  exact Poly.pair (Poly.comp Poly.snd readUnary_poly) (Poly.comp Poly.fst readUnary_poly)

theorem readWireWord_rest_length (word : Str) : (readWireWord word).1.length ≤ word.length := by
  simp only [readWireWord,readUnary,List.length_drop]
  omega

theorem readWireWord_append (n : ℕ) (suffix : Str) :
    readWireWord (encNat n++suffix)=(suffix,encNat n) := by
  simp only [readWireWord,readUnary_append]

@[fun_prop] theorem readWireWords_poly : Poly readWireWords :=
  readList_poly readWireWord readWireWord_poly readWireWord_rest_length

theorem readWireWords_append (wires : List ℕ) (suffix : Str) :
    readWireWords (encStr (wires.map encNat)++suffix)=(suffix,wires.map encNat) :=
  readList_append_mapped readWireWord encNat encNat readWireWord_append wires suffix

theorem multi_encoding (F : MFamily) (n : ℕ) : F.encAt n=encNat (F.anc n)++
    encStr (((List.ofFn (F.outW n)).map Fin.val).map encNat)++encCirc (F.circ n) := by
  unfold MFamily.encAt
  simp only [bind_pure_comp]
  change encNat (F.anc n)++encStr (((List.ofFn (F.outW n)).map Fin.val).map encNat)++encCirc (F.circ n)=_
  rfl

@[fun_prop] theorem readFrame_poly : Poly readFrame := by unfold readFrame;fun_prop

theorem readFrame_correct (F : MFamily) (n : ℕ) :
    readFrame (unary n,F.encAt n)=
      (unary (oldWidth F n),
        ((List.ofFn (F.outW n)).map (fun wire => encNat wire.val),(F.circ n).map (List.map encInstr))) := by
  unfold readFrame
  rw [multi_encoding]
  simp only [List.append_assoc,readUnary_append,unaryPayload_encNat]
  rw [readWireWords_append]
  have hc := readCircuitLayers_append (F.circ n) []
  simp only [List.append_nil] at hc
  rw [hc,List.map_map]
  simp only [oldWidth,unary,List.replicate_add,List.append_assoc,List.replicate_one,Function.comp_def]

variable {f : Str → Str} (P : PolyProgram id id f)

@[fun_prop] theorem inputSlots_poly : Poly inputSlots := by unfold inputSlots;fun_prop

@[fun_prop] theorem inputWord_poly : Poly inputWord := by unfold inputWord;fun_prop

theorem inputWord_correct (F : MFamily) (n : ℕ) :
    inputWord (unary n,F.encAt n)=unary (sources F n).length := by
  unfold inputWord inputSlots
  rw [readFrame_correct]
  simp only [List.map_append,List.map_ofFn,Function.comp_def,List.ofFn_const,sources_length,
    unary,List.replicate_add,List.map_replicate]

@[fun_prop] theorem oldSlots_poly : Poly oldSlots := by unfold oldSlots;fun_prop

theorem oldSlots_length (F : MFamily) (n : ℕ) : (oldSlots (unary n,F.encAt n)).length=oldWidth F n := by
  unfold oldSlots
  rw [readFrame_correct]
  simp only [List.length_map,unary,List.length_replicate]

@[fun_prop] theorem sourcePairs_poly : Poly sourcePairs := by
  have hr : Poly (fun input : Str × Str => List.range input.1.length) :=
    Poly.comp (f := fun word : Str => List.range word.length) (g := Prod.fst) Poly.list_indices Poly.fst
  unfold sourcePairs
  fun_prop

theorem sourcePairs_correct (F : MFamily) (n : ℕ) :
    sourcePairs (unary n,F.encAt n)=copySources (sources F n) := by
  unfold sourcePairs
  rw [readFrame_correct]
  simp only [unary,List.length_replicate,List.map_map,Function.comp_def]
  unfold copySources sources sourceWire
  rw [List.ofFn_add,List.map_append]
  apply congrArg₂ List.append
  · apply List.ext_getElem
    · simp
    · intro i hl hr
      have hi : i<n := by simpa using hl
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      congr 1
      change i=(sourceWire F n (Fin.castAdd (F.outLen n) ⟨i,hi⟩)).val
      simp only [sourceWire,Fin.addCases_left,Fin.val_castAdd]
  · simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply,Fin.addCases_right]
    simp [QMCNumericRuntime.inputWidth_prefix,encNat]

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule67

/- Helper module BatchStock. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch

open QAlgorithms.Complexity Turing

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2StockLists

def batchDescriptions (generate : Str → Str) (requests : Str → List Str) (word : Str) :
    List (Str × Str) :=
  (requests word).map (fun query => (query, generate query))

/-- An arbitrary polynomial list of unary requests can call the sampler's
actual native generator. The opaque generator keeps its own work alphabet. -/
theorem batchDescriptions_stock (generate : Str → Str) (hgenerate : PolyTimeComputable generate)
    (requests : Str → List Str) (hrequests : Poly requests) :
    Nonempty (TM2ComputableInPolyTime id
      (encodeList (encodePair (encodeList encodeBool) (encodeList encodeBool)))
      (batchDescriptions generate requests)) := by
  obtain ⟨source⟩ := hgenerate
  obtain ⟨quoted⟩ := stock_quoted source
  obtain ⟨paired⟩ := stock_pairWithInput quoted
  obtain ⟨mapped⟩ := TM2StockLists.listMap paired []
  obtain ⟨requested⟩ := TM2Composition.comp BooleanLists.packProgram.stock hrequests.program.stock
  obtain ⟨whole⟩ := TM2Composition.comp requested mapped
  exact ⟨congrProgram whole _ (fun _ => rfl)⟩

theorem batchBuilder_polyTime (G : MFamily) (hG : IsMQPT G)
    (requests : Str → List Str) (hrequests : Poly requests)
    (hunary : ∀ word request, request ∈ requests word → request = unary request.length)
    (builder : Str × List (Str × Str) → Str) (hbuilder : Poly builder) :
    PolyTimeComputable (fun word =>
      builder (word, (requests word).map (fun query => (query, G.encAt query.length)))) := by
  obtain ⟨source, hsource, hsourceValue⟩ := hG.1
  obtain ⟨table⟩ := batchDescriptions_stock source hsource requests hrequests
  obtain ⟨quotedTable⟩ := TM2Composition.comp BooleanLists.unpackProgram.stock table
  obtain ⟨paired⟩ := stock_pairWithInput quotedTable
  obtain ⟨built⟩ := TM2Composition.comp paired hbuilder.program.stock
  obtain ⟨output⟩ := TM2Composition.comp built BooleanLists.unpackProgram.stock
  obtain ⟨whole⟩ := TM2Composition.comp BooleanLists.packProgram.stock output
  refine ⟨congrProgram whole _ ?_⟩
  intro word
  simp only [Function.comp_apply, id_eq, batchDescriptions]
  apply congrArg builder
  apply congrArg (fun descriptions => (word, descriptions))
  apply List.map_congr_left
  intro query hquery
  rw [hunary word query hquery, hsourceValue]
  simp [unary]

end InfoLossLAR.WorstCase.RegevSketch

end P2MDyadicModule68

/- Helper module BatchEmitter. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch

open QAlgorithms.Complexity TM2Boolean TM2Boolean.RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

open Integration9_9.LoadedBatch.PostComposition (MultiFrameWords readFrame)

/-- The flag distinguishes copies from constants. Only a copy interprets the
second field as an address. -/
def loadSource {n : ℕ} : StaticLoadSlot n → Bool × ℕ
  | .inl bit => (false, if bit then 1 else 0)
  | .inr index => (true, index.val)

def loadNode (source : Bool × ℕ) : Node :=
  if source.1 then (2, source.2, 0) else (if source.2 = 0 then 0 else 1, 0, 0)

@[fun_prop] theorem loadNode_poly : Poly loadNode := by
  unfold loadNode
  fun_prop

theorem loadNode_source {n : ℕ} (slot : StaticLoadSlot n) :
    loadNode (loadSource slot) = node slot.op := by
  cases slot with
  | inl bit => cases bit <;> rfl
  | inr index => rfl

abbrev LoadDescriptionInput := Str × (List Unit × List (Bool × ℕ))

def loadBooleanDescription (input : LoadDescriptionInput) : Str :=
  let width := (input.1.map fun _ => ()) ++ input.2.1 ++ [()]
  lengthToken input.2.1 ++ encNat 0 ++
    serializeWords (instructionWords width input.1.length (input.2.2.map loadNode))

@[fun_prop] theorem loadBooleanDescription_poly : Poly loadBooleanDescription := by
  unfold loadBooleanDescription
  fun_prop

def loadLayers (input : LoadDescriptionInput) : List (List Str) :=
  readFamilyCircuitLayers
    (compileReversibleDescription (compileBooleanDescription (loadBooleanDescription input)))

@[fun_prop] theorem loadLayers_poly : Poly loadLayers := by
  unfold loadLayers
  fun_prop

theorem loadLayers_correct {n a : ℕ} (slots : List (StaticLoadSlot n))
    (hfit : slots.length ≤ a + 1) :
    loadLayers (unary n, List.replicate a (), slots.map loadSource) =
      (staticLoadCircuit slots hfit).map (List.map encInstr) := by
  let hwidth : n + (staticLoadOps slots).length ≤ n + (a + 1) := by
    simpa only [staticLoadOps, List.length_map] using Nat.add_le_add_left hfit n
  let gates := BooleanProgram.gates n (staticLoadOps slots) hwidth
  let loader : BooleanFamily :=
    { anc := fun _ => a
      gates := fun k => if hk : k = n then hk.symm ▸ gates else []
      out := fun _ => ⟨0, by omega⟩ }
  have hnodes : (slots.map loadSource).map loadNode = (staticLoadOps slots).map node := by
    simp only [staticLoadOps, List.map_map, Function.comp_def]
    exact List.map_congr_left (fun slot _ => loadNode_source slot)
  have hwords : instructionWords (((unary n).map fun _ => ()) ++ List.replicate a () ++ [()])
      n ((slots.map loadSource).map loadNode) = gates.map BooleanGate.code := by
    rw [hnodes]
    apply instructionWords_gates _ _ _ hwidth (staticLoadOps_valid slots n le_rfl)
    simpa only [List.length_append, List.length_map, unary, List.length_replicate,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc] using hwidth
  have hdesc : loadBooleanDescription (unary n, List.replicate a (), slots.map loadSource) =
      loader.code n := by
    have hlen : (unary n).length = n := by simp [unary]
    simp only [loadBooleanDescription, lengthToken_eq, List.length_replicate, hlen, serializeWords_eq]
    rw [hwords]
    simp [loader, BooleanFamily.code]
  unfold loadLayers
  rw [hdesc, compileBooleanDescription_code, compileReversibleDescription_code,
    readFamilyCircuitLayers_correct]
  simp [loader, BooleanFamily.reversible, ReversibleFamily.compile, staticLoadCircuit, gates]

def physicalFrame (frame : MultiFrameWords) : PhysicalFrameWords :=
  (frame.1, (encNat 0, frame.2.2))

@[fun_prop] theorem physicalFrame_poly : Poly physicalFrame := by
  unfold physicalFrame
  fun_prop

def samplerFrames (descriptions : List (Str × Str)) : List MultiFrameWords :=
  descriptions.map readFrame

@[fun_prop] theorem samplerFrames_poly : Poly samplerFrames := by
  unfold samplerFrames
  fun_prop

def samplerLayers (input : Str × List MultiFrameWords) : List (List Str) :=
  shiftCircuitWords input.1 (bundleCircuitWordLayers (input.2.map physicalFrame))

@[fun_prop] theorem samplerLayers_poly : Poly samplerLayers := by
  unfold samplerLayers
  fun_prop

end InfoLossLAR.WorstCase.RegevSketch

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeLoadedBatchPostUniform. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch.PostComposition

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.LARCoinLayout

variable {f : Str → Str} (P : PolyProgram id id f)

theorem inputSlots_length (F : MFamily) (n : ℕ) : (inputSlots (unary n,F.encAt n)).length=(sources F n).length := by
  unfold inputSlots
  rw [readFrame_correct]
  simp only [List.length_append,List.length_map,List.length_ofFn,sources_length,unary,List.length_replicate]

@[fun_prop] theorem ancSlots_poly : Poly (ancSlots P) := by unfold ancSlots;fun_prop

theorem ancSlots_length (F : MFamily) (n : ℕ) :
    (ancSlots P (unary n,F.encAt n)).length=finalAnc F P n := by
  unfold ancSlots
  rw [inputWord_correct]
  simp only [List.length_append,List.length_map,List.length_singleton,LoadedBatch.preAncSlots_length,inputSlots_length]
  rw [multi_encoding]
  simp only [List.append_assoc,unaryPayload_encNat,unary,List.length_replicate,finalAnc]

@[fun_prop] theorem allSlots_poly : Poly (allSlots P) := by unfold allSlots;fun_prop

theorem allSlots_length (F : MFamily) (n : ℕ) :
    (allSlots P (unary n,F.encAt n)).length=n+(finalAnc F P n+1) := by
  simp only [allSlots,List.length_append,List.length_map,List.length_singleton,ancSlots_length]
  simp only [unary,List.length_replicate];omega

@[fun_prop] theorem copyWords_poly : Poly (copyWords P) := by unfold copyWords;fun_prop

theorem copyWords_correct (F : MFamily) (n : ℕ) :
    copyWords P (unary n,F.encAt n)=(copyGates P F n).map BooleanGate.code := by
  unfold copyWords
  rw [sourcePairs_correct,oldSlots_length]
  apply registerLoadGateWords_correct
  · exact copySources_valid (sources F n)
  · rw [←width_eq]
    simp only [copySources,List.length_map]
    unfold postWidth;omega
  · rw [allSlots_length,←width_eq]
    simp only [copySources,List.length_map]
    unfold postWidth;omega

@[fun_prop] theorem copyBooleanDescription_poly : Poly (copyBooleanDescription P) := by
  unfold copyBooleanDescription;fun_prop

theorem copyBooleanDescription_correct (F : MFamily) (n : ℕ) :
    copyBooleanDescription P (unary n,F.encAt n)=(copyBooleanFamily P F).code n := by
  unfold copyBooleanDescription
  rw [lengthToken_eq,ancSlots_length,copyWords_correct,serializeWords_eq]
  rfl

@[fun_prop] theorem copyQuantumDescription_poly : Poly (copyQuantumDescription P) := by unfold copyQuantumDescription;fun_prop

theorem copyQuantumDescription_correct (F : MFamily) (n : ℕ) :
    copyQuantumDescription P (unary n,F.encAt n)=encFamilyAt (copyBooleanFamily P F).reversible.compile n := by
  unfold copyQuantumDescription
  rw [copyBooleanDescription_correct,compileBooleanDescription_code,compileReversibleDescription_code]

section
attribute [local irreducible] quantumDescription inputWord oldSlots shiftCircuitWords readFamilyCircuitLayers

@[fun_prop] theorem nativeWordLayers_poly : Automatic.Poly (nativeWordLayers P) := by
  have hprefix : Automatic.Poly (fun x : Str × Str => (oldSlots x).map (fun _ => true)) :=
    Automatic.Poly.list_map
      (f := fun (_ : Str × Str) (_ : Unit) => true) (as := oldSlots)
      (Automatic.Poly.const true) oldSlots_poly
  have hquantum := Automatic.Poly.comp (f := quantumDescription P) (g := inputWord)
    (quantumDescription_poly P) inputWord_poly
  have hlayers := Automatic.Poly.comp (f := readFamilyCircuitLayers)
    (g := fun x : Str × Str => quantumDescription P (inputWord x))
    readFamilyCircuitLayers_poly hquantum
  have hp := Automatic.Poly.pair
    (f := fun x : Str × Str => (oldSlots x).map (fun _ => true))
    (g := fun x : Str × Str => readFamilyCircuitLayers (quantumDescription P (inputWord x)))
    hprefix hlayers
  unfold nativeWordLayers
  exact Automatic.Poly.comp
    (f := fun x : Str × List (List Str) => shiftCircuitWords x.1 x.2)
    (g := fun x : Str × Str => ((oldSlots x).map (fun _ => true),
      readFamilyCircuitLayers (quantumDescription P (inputWord x))))
    shiftCircuitWords_poly hp
end


theorem nativeWordLayers_correct (F : MFamily) (n : ℕ) :
    nativeWordLayers P (unary n,F.encAt n)=
      (rightCircuit (n := oldWidth F n) (TM2Boolean.PolyProgramCircuit.circuit P (sources F n).length)).map (List.map encInstr) := by
  unfold nativeWordLayers
  rw [inputWord_correct,quantumDescription_code,readFamilyCircuitLayers_correct,shiftCircuitWords_correct]
  apply rightCircuit_instructionWords_congr
  simp only [List.length_map]
  exact oldSlots_length F n

attribute [local irreducible] copyQuantumDescription nativeWordLayers

@[fun_prop] theorem wordLayers_poly : Poly (wordLayers P) := by unfold wordLayers;fun_prop

private theorem freshCircuit_words_width_congr {left right start : ℕ} (he : left=right)
    (ops : List BooleanOp) (hl : start+ops.length ≤ left) (hr : start+ops.length ≤ right) :
    (compileReversible (booleanToReversible (BooleanProgram.gates start ops hl))).map (List.map encInstr)=
      (compileReversible (booleanToReversible (BooleanProgram.gates start ops hr))).map (List.map encInstr) := by
  cases he;rfl

theorem wordLayers_correct (F : MFamily) (n : ℕ) :
    wordLayers P (unary n,F.encAt n)=(circuit F P n).map (List.map encInstr) := by
  unfold wordLayers
  rw [readFrame_correct,copyQuantumDescription_correct,readFamilyCircuitLayers_correct,nativeWordLayers_correct]
  unfold circuit
  rw [castBodyCircuit_instructionWords]
  simp only [List.map_append]
  rw [postCircuit_decompose]
  simp only [List.map_append,List.append_assoc]
  apply congrArg₂ List.append
  · unfold embeddedCircuit
    rw [castBodyCircuit_instructionWords,leftCircuit_instructionWords]
  · apply congrArg₂ List.append
    · change (compileReversible (booleanToReversible (copyGates P F n))).map (List.map encInstr)=_
      unfold copyGates
      exact freshCircuit_words_width_congr (width_eq F P n).symm _ _ _
    · rfl

@[fun_prop] theorem outputWords_poly : Poly (outputWords P) := by unfold outputWords;fun_prop

theorem outputWords_correct (F : MFamily) (n : ℕ) :
    outputWords P (unary n,F.encAt n)=(List.ofFn ((family F P).outW n)).map (fun wire => encNat wire.val) := by
  unfold outputWords
  rw [inputWord_correct,multiOutputWords_code,List.map_map,List.map_ofFn,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def,shiftWireWord_spec,List.length_map,oldSlots_length,family,output,
    Fin.val_cast,Fin.val_natAdd]
  congr 1
  simp [QMCNumericRuntime.inputWidth_prefix,encNat]

@[fun_prop] theorem builder_poly : Poly (builder P) := by unfold builder;fun_prop

theorem builder_correct (F : MFamily) (n : ℕ) :
    builder P (unary n,F.encAt n)=(family F P).encAt n := by
  unfold builder
  rw [lengthToken_eq,ancSlots_length,outputWords_correct,wordLayers_correct,multi_encoding]
  simp only [serializeWords_eq,encCirc,List.map_map,Function.comp_def,family]
  rfl

/-- Uniformity is constructed from the original multi-output generator and
actual native descriptor transformation; it is not an extra closure premise. -/
theorem family_uniform (F : MFamily)
    (hF : ∃ generator : Str → Str,PolyTimeComputable generator ∧ ∀ n,generator (unary n)=F.encAt n) :
    ∃ generator : Str → Str,PolyTimeComputable generator ∧ ∀ n,generator (unary n)=(family F P).encAt n := by
  obtain ⟨generator,hg,hcode⟩ := hF
  refine ⟨fun word => builder P (word,generator word),generator_builder_polyTime generator hg (builder P) (builder_poly P),?_⟩
  intro n
  change builder P (unary n,generator (unary n))=_
  rw [hcode]
  exact builder_correct P F n

/-- Genuine same-register native postprocessing closure for MQPT families. -/
theorem family_isMQPT (F : MFamily) (hF : IsMQPT F) : IsMQPT (family F P) :=
  ⟨family_uniform P F hF.1,family_wellFormed F P hF.2.1,family_polyBounded F P hF.2.2⟩

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule70

/- Helper module Solutions.RegevBridgeLoadedBatchState. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.LARCoinLayout

variable {f : Str → Str} (P : PolyProgram id id f) (Q : Family) (L J : Polynomial ℕ)

theorem actualBlocks_eq_loaded (word : Str) :
    actualBlocks P Q L J word=RepeatedQuery.loadedBlocks Q L J word.length
      (fun trial index => ((f word)[trial.val*(L.eval word.length)+index.val]?).getD false) := by
  unfold actualBlocks trialBlocks RepeatedQuery.loadedBlocks
  apply List.ext_getElem <;> simp

theorem actualBlocks_width (word : Str) : bundleWidth (actualBlocks P Q L J word)=callWidth Q L J word.length := by
  simp only [actualBlocks,trialBlocks_width,List.length_range,callWidth]

theorem actualBlocks_basis (word : Str) : bundleState (actualBlocks P Q L J word)=
    computationalBasis (fun index =>
      trialBits f Q (L.eval word.length) word (List.range (J.eval word.length)) index.val) :=
  trialBlocks_basis P Q (L.eval word.length) word (List.range (J.eval word.length))

theorem actualBlocks_physical (word : Str) :
    bundlePhysical (actualBlocks P Q L J word)=bundlePhysical (RepeatedQuery.blocks Q L J word.length) := by
  rw [actualBlocks_eq_loaded]
  exact RepeatedQuery.loadedBlocks_physical Q L J word.length _

theorem preparedBits_prefix (word : Str) (index : ℕ) (hi : index<preWidth P word.length) :
    preparedBits P Q L J word index=generatedQueryBits P word index :=
  preparedLoadOps_prefix P word _ index hi

theorem preparedBits_queries (hfits : Fits P L J) (word : Str) (index : ℕ)
    (hi : index<callWidth Q L J word.length) :
    preparedBits P Q L J word (preWidth P word.length+index)=
      trialBits f Q (L.eval word.length) word (List.range (J.eval word.length)) index := by
  have his : index<(loadSources P Q L J word.length).length := by rw [loadSources_length];exact hi
  unfold preparedBits preWidth
  rw [preparedLoadOps_written P word _ (loadSources_valid P Q L J hfits word.length) index his]
  rw [←sourceValueAt_get _ _ index his]
  apply loadSourcesFromFrame_value
  intro trial ht
  have htrial := List.mem_range.mp ht
  have hm := Nat.mul_le_mul_right (L.eval word.length) (Nat.succ_le_iff.mpr htrial)
  simpa only [Nat.succ_mul] using hm.trans (hfits word.length)

theorem preparedBits_after (word : Str) (index : ℕ)
    (hi : preWidth P word.length+callWidth Q L J word.length ≤ index) :
    preparedBits P Q L J word index=false := by
  unfold preparedBits
  rw [BooleanProgram.run_after]
  · exact wordExtension_after word index (by unfold preWidth at hi;omega)
  · rw [preparedLoadOps_length,loadSources_length]
    unfold preWidth at hi
    omega

theorem preparedCircuit_basis (hfits : Fits P L J) (word : Str) :
    runLayered (compileReversible (booleanToReversible (preparedGates P Q L J word.length)))
      (basisInput (a := machineAnc P Q L J word.length) (toBits word))=
      computationalBasis (fun index => preparedBits P Q L J word index.val) := by
  rw [basisInput_eq_computationalBasis,wordExtension_basis]
  unfold preparedGates preparedBits computationalBasis
  exact BooleanProgram.circuit_basis _ _ (prepared_valid P Q L J hfits word.length)
    (wordExtension word) (fun index hi _ => wordExtension_after word index hi)

theorem castState_basis {left right : ℕ} (he : left=right) (bits : Bits left) :
    castState he (computationalBasis bits)=computationalBasis (fun i => bits (Fin.cast he.symm i)) := by
  cases he;rfl

theorem runLayered_cast {left right : ℕ} (he : left=right) (circuit : Layered left) (state : QState left) :
    runLayered (castBodyCircuit he circuit) (castState he state)=castState he (runLayered circuit state) := by cases he;rfl

theorem tensorWidth (word : Str) :
    (preWidth P word.length+bundleWidth (actualBlocks P Q L J word))+1=machineWidth P Q L J word.length := by
  rw [actualBlocks_width,width_eq]

theorem preparedState_tensor (hfits : Fits P L J) (word : Str) :
    computationalBasis (fun index : Fin (machineWidth P Q L J word.length) => preparedBits P Q L J word index.val)=
      castState (tensorWidth P Q L J word)
        (tensorState (tensorState (computationalBasis (result P word))
          (bundleState (actualBlocks P Q L J word))) (computationalBasis (fun _ => false))) := by
  rw [actualBlocks_basis,←computationalBasis_tensor,←computationalBasis_tensor,castState_basis]
  apply congrArg computationalBasis
  have hbits (index : Fin ((preWidth P word.length+bundleWidth (actualBlocks P Q L J word))+1)) :
      preparedBits P Q L J word index.val=
        (Fin.append (Fin.append (result P word)
          (fun index => trialBits f Q (L.eval word.length) word (List.range (J.eval word.length)) index.val))
          (fun _ => false)) index := by
    refine Fin.addCases (fun block => ?_) (fun scratch => ?_) index
    · refine Fin.addCases (fun previous => ?_) (fun data => ?_) block
      · simp only [Fin.val_castAdd,Fin.append_left]
        rw [preparedBits_prefix P Q L J word previous.val previous.isLt]
        exact selectorBitsExtension_get (result P word) previous
      · simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left]
        dsimp only [preWidth] at *
        rw [Fin.append_right]
        exact preparedBits_queries P Q L J hfits word data.val
          (lt_of_lt_of_eq data.isLt (actualBlocks_width P Q L J word))
    · simp only [Fin.val_natAdd]
      dsimp only [preWidth] at *
      rw [Fin.append_right]
      apply preparedBits_after
      unfold preWidth
      rw [actualBlocks_width];omega
  funext index
  simpa only [Fin.val_cast] using hbits (Fin.cast (tensorWidth P Q L J word).symm index)

private theorem packedCircuit_cast {left right total : ℕ} (first : Layered left) (second : Layered right)
    (h : (⟨left,first⟩ : Σ width : ℕ,Layered width)=⟨right,second⟩)
    (hf : left=total) (hs : right=total) : castBodyCircuit hf first=castBodyCircuit hs second := by
  cases h;rfl

theorem queryCircuit_actual (word : Str) :
    queryCircuit P Q L J word.length=castBodyCircuit (tensorWidth P Q L J word)
      (leftCircuit (m := 1) (rightCircuit (n := preWidth P word.length)
        (bundleCircuit (actualBlocks P Q L J word)))) := by
  have h := congrArg (fun circuit : (Σ width : ℕ,Layered width) =>
    (⟨(preWidth P word.length+circuit.1)+1,
      leftCircuit (m := 1) (rightCircuit (n := preWidth P word.length) circuit.2)⟩ : Σ width : ℕ,Layered width))
    (actualBlocks_physical P Q L J word).symm
  unfold queryCircuit
  exact packedCircuit_cast _ _ h _ _

/-- Exact coherent state of the full emitted loaded batch. Every real native
query is present in its own physical register; retained preprocessor garbage
and the mandatory terminal wire are explicit tensor factors. -/
theorem machineState_tensor (hfits : Fits P L J) (word : Str) :
    runLayered ((machine P Q L J).circ word.length)
      (basisInput (a := (machine P Q L J).anc word.length) (toBits word))=
      castState (tensorWidth P Q L J word)
        (tensorState (tensorState (computationalBasis (result P word))
          (runLayered (bundleCircuit (actualBlocks P Q L J word)) (bundleState (actualBlocks P Q L J word))))
          (computationalBasis (fun _ => false))) := by
  change runLayered (compileReversible (booleanToReversible (preparedGates P Q L J word.length))++
    queryCircuit P Q L J word.length) _=_
  rw [show ∀ {n : ℕ} (first second : Layered n) (state : QState n),
      runLayered (first++second) state=runLayered second (runLayered first state) from
        fun _ _ _ => List.foldl_append]
  rw [preparedCircuit_basis P Q L J hfits,preparedState_tensor P Q L J hfits,queryCircuit_actual,
    runLayered_cast,leftCircuit_tensor,rightCircuit_tensor]

end Integration9_9.LoadedBatch

end

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeLoadedBatchBorn. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open InfoLossLAR.WorstCase.DecisionSearch

open QAlgorithms.Complexity AFT

open OAI.MetricKMedian.Binary

open scoped BigOperators Classical

variable {f : Str → Str} (P : PolyProgram id id f) (Q : Family) (L J : Polynomial ℕ)

theorem castState_event {left right : ℕ} (he : left=right) (state : QState left)
    (event : Bits right → Prop) :
    (∑ input : Bits right,if event input then ‖castState he state input‖^2 else 0)=
      ∑ input : Bits left,if event (fun i => input (Fin.cast he.symm i)) then ‖state input‖^2 else 0 := by
  cases he;rfl

end Integration9_9.LoadedBatch

end

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeLoadedBatchPostSemantics. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch.PostComposition

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.LARCoinLayout

open scoped BigOperators Classical

variable (F : MFamily) {f : Str → Str} (P : PolyProgram id id f)

theorem initial_tensor (word : Str) :
    castState (width_eq F P word.length)
      (tensorState (basisInput (a := F.anc word.length) (toBits word))
        (computationalBasis (fun _ : Fin (localWidth F P word.length) => false)))=
      basisInput (a := finalAnc F P word.length) (toBits word) := by
  rw [basisInput_eq_computationalBasis,basisInput_eq_computationalBasis,←computationalBasis_tensor]
  rw [wordExtension_basis,wordExtension_basis]
  rw [castState_basis]
  apply congrArg computationalBasis
  have he : (Fin.append (fun i : Fin (oldWidth F word.length) => wordExtension word i.val)
      (fun _ : Fin (localWidth F P word.length) => false))=
      (fun i => wordExtension word i.val) := by
    funext i
    refine Fin.addCases (fun previous => ?_) (fun fresh => ?_) i
    · simp only [Fin.append_left,Fin.val_castAdd]
    · rw [Fin.append_right]
      symm
      apply wordExtension_after
      unfold oldWidth
      simp only [Fin.val_natAdd]
      omega
  funext i
  exact congrFun he (Fin.cast (width_eq F P word.length).symm i)

/-- Exact semantics of the single uniform postprocessed family. The native
program sees the observed original-register bits followed by all designated
QPT outputs. No independence is asserted between those old bits. -/
theorem family_outputProbability (word : Str) (event : Str → Prop) :
    outputProb (family F P) word event=
      ∑ input : Bits (oldWidth F word.length),
        if event (paddedOutput P ((sources F word.length).map input)) then
          ‖runLayered (F.circ word.length) (basisInput (a := F.anc word.length) (toBits word)) input‖^2 else 0 := by
  unfold outputProb
  change (∑ input : Bits (word.length+(finalAnc F P word.length+1)),
    if event (List.ofFn (fun i => input (output F P word.length i))) then
      ‖runLayered (circuit F P word.length) (basisInput (a := finalAnc F P word.length) (toBits word)) input‖^2 else 0)=_
  rw [←initial_tensor F P word]
  unfold circuit
  rw [runLayered_cast]
  rw [show ∀ {n : ℕ} (first second : Layered n) (state : QState n),
      runLayered (first++second) state=runLayered second (runLayered first state) from
        fun _ _ _ => List.foldl_append]
  unfold embeddedCircuit
  dsimp only [castBodyCircuit]
  rw [leftCircuit_tensor]
  rw [castState_event]
  have he (input : Bits (postWidth P (sources F word.length))) :
      (List.ofFn fun i => (fun wire => input (Fin.cast (width_eq F P word.length).symm wire))
        (output F P word.length i))=postOutputs P (sources F word.length) input := by
    unfold output postOutputs
    apply congrArg List.ofFn
    funext i
    congr 1
  dsimp only [family,oldWidth,localWidth,postWidth] at *
  simp_rw [he]
  simpa only [decide_eq_true_eq,oldWidth,localWidth,postWidth] using postCircuit_tensor_event_probability P (sources F word.length)
    (runLayered (F.circ word.length) (basisInput (a := F.anc word.length) (toBits word)))
    (fun word => decide (event word))

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeLoadedBatchPostProbability. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Integration9_9.LoadedBatch

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open InfoLossLAR.WorstCase.DecisionSearch QAlgorithms.Complexity AFT

open OAI.MetricKMedian.Binary

open scoped BigOperators Classical

theorem postSources_map (F : MFamily) (n : ℕ) (input : Bits (PostComposition.oldWidth F n)) :
    (PostComposition.sources F n).map input=
      (List.ofFn (fun i : Fin n => input (Fin.castAdd (F.anc n+1) i)))++
      List.ofFn (fun i : Fin (F.outLen n) => input (F.outW n i)) := by
  unfold PostComposition.sources PostComposition.sourceWire
  rw [List.map_ofFn,List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply]
    change input (PostComposition.sourceWire F n (Fin.castAdd (F.outLen n) i))=_
    simp only [PostComposition.sourceWire,Fin.addCases_left]
  · apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply,Fin.addCases_right]

variable {pre : Str → Str} (P : PolyProgram id id pre) (Q : Family) (L J : Polynomial ℕ)

end Integration9_9.LoadedBatch

end

end P2MDyadicModule74

/- Helper module Build. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace ParityFlags

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.LARPlatformEncoding Integration9_9.TM2PlatformSerialization

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open Integration9_9.LoadedBatch.PostComposition

open scoped BigOperators Classical

def readStrings : Str → Str × List Str := readBinaryList readS

@[fun_prop] theorem readStrings_poly : Poly readStrings := readBinaryList_poly readS readS_poly readS_rest_length

end ParityFlags

end P2MDyadicModule75

/- Helper module BundleMarginal. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

theorem tensorState_left_event {n m : ℕ} (first : QState n) (second : QState m)
    (event : Bits n → Prop) (hsecond : ∑ state,‖second state‖^2=1) :
    (∑ state : Bits (n+m), if event (leftRegister state) then ‖tensorState first second state‖^2 else 0) =
      ∑ state : Bits n, if event state then ‖first state‖^2 else 0 := by
  change (∑ state : Bits (n+m), if event (leftRegister state) then
    ‖first (leftRegister state) * second (rightRegister state)‖^2 else 0) = _
  rw [sum_registers (fun left right => if event left then ‖first left * second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if event left then ‖first left * second right‖^2 else 0) =
        (if event left then ‖first left‖^2 else 0) * ‖second right‖^2 := by
    by_cases h : event left <;> simp [h, mul_pow]
  simp only [hpoint, ←Finset.mul_sum, hsecond, mul_one]

theorem tensorState_right_event {n m : ℕ} (first : QState n) (second : QState m)
    (event : Bits m → Prop) (hfirst : ∑ state,‖first state‖^2=1) :
    (∑ state : Bits (n+m), if event (rightRegister state) then ‖tensorState first second state‖^2 else 0) =
      ∑ state : Bits m, if event state then ‖second state‖^2 else 0 := by
  change (∑ state : Bits (n+m), if event (rightRegister state) then
    ‖first (leftRegister state) * second (rightRegister state)‖^2 else 0) = _
  rw [sum_registers (fun left right => if event right then ‖first left * second right‖^2 else 0)]
  have hpoint (left : Bits n) (right : Bits m) :
      (if event right then ‖first left * second right‖^2 else 0) =
        ‖first left‖^2 * (if event right then ‖second right‖^2 else 0) := by
    by_cases h : event right <;> simp [h, mul_pow]
  simp only [hpoint, ←Finset.mul_sum, ←Finset.sum_mul, hfirst, one_mul]

end InfoLossLAR.WorstCase

end P2MDyadicModule76

/- Helper module StaticBatchCore. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.StaticBatch

open QAlgorithms.Complexity TM2Boolean

open Integration9_9.LoadedBatch Integration9_9.LARCoinLayout

noncomputable section

abbrev Tasks (n : ℕ) := List (List (StaticLoadSlot n))

def blockWidth (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) : ℕ :=
  task.length + (G.anc task.length + 1)

def gridWidth (G : MFamily) {n : ℕ} : Tasks n → ℕ
  | [] => 0
  | task :: rest => blockWidth G task + gridWidth G rest

def gridCircuit (G : MFamily) {n : ℕ} : (tasks : Tasks n) → Layered (gridWidth G tasks)
  | [] => []
  | task :: rest => leftCircuit (m := gridWidth G rest) (show Layered (blockWidth G task) from G.circ task.length) ++
      rightCircuit (n := blockWidth G task) (gridCircuit G rest)

def gridWire (G : MFamily) {n : ℕ} : (tasks : Tasks n) →
    (i : Fin tasks.length) → Fin (blockWidth G (tasks.get i)) → Fin (gridWidth G tasks)
  | [], i, _ => Fin.elim0 i
  | task :: rest, i, j => Fin.cases
    (motive := fun a => Fin (blockWidth G ((task :: rest).get a)) →
      Fin (gridWidth G (task :: rest)))
    (fun a => Fin.castAdd (gridWidth G rest) a)
    (fun tail a => Fin.natAdd (blockWidth G task) (gridWire G rest tail a)) i j

def taskSlots (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) :
    List (StaticLoadSlot n) :=
  task ++ List.replicate (G.anc task.length + 1) (.inl false)

@[simp] theorem taskSlots_length (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) :
    (taskSlots G task).length = blockWidth G task := by
  simp [taskSlots, blockWidth]

def gridSlots (G : MFamily) {n : ℕ} : Tasks n → List (StaticLoadSlot n)
  | [] => []
  | task :: rest => taskSlots G task ++ gridSlots G rest

@[simp] theorem gridSlots_length (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (gridSlots G tasks).length = gridWidth G tasks := by
  induction tasks with
  | nil => rfl
  | cons task rest ih => simp [gridSlots, gridWidth, ih]

def coreSlots (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    List (StaticLoadSlot n) :=
  gridSlots G tasks ++ [.inl true]

@[simp] theorem coreSlots_length (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (coreSlots G tasks).length = gridWidth G tasks + 1 := by simp [coreSlots]

def batchAnc (G : MFamily) {n : ℕ} (tasks : Tasks n) : ℕ := gridWidth G tasks + 1

theorem coreWidth_eq (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (n + gridWidth G tasks) + 2 = n + (batchAnc G tasks + 1) := by
  unfold batchAnc
  omega

def inputWire (G : MFamily) {n : ℕ} (tasks : Tasks n) (i : Fin n) :
    Fin (n + (batchAnc G tasks + 1)) := Fin.castAdd (batchAnc G tasks + 1) i

def blockWire (G : MFamily) {n : ℕ} (tasks : Tasks n) (i : Fin tasks.length)
    (j : Fin (blockWidth G (tasks.get i))) : Fin (n + (batchAnc G tasks + 1)) :=
  Fin.cast (coreWidth_eq G tasks)
    (Fin.castAdd 2 (Fin.natAdd n (gridWire G tasks i j)))

def constantWire (G : MFamily) {n : ℕ} (tasks : Tasks n) (b : Bool) :
    Fin (n + (batchAnc G tasks + 1)) :=
  Fin.cast (coreWidth_eq G tasks)
    (Fin.natAdd (n + gridWidth G tasks) (if b then 0 else 1 : Fin 2))

def coreCircuit (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    Layered (n + (batchAnc G tasks + 1)) :=
  staticLoadCircuit (coreSlots G tasks) (by simp [batchAnc]) ++
    castBodyCircuit (coreWidth_eq G tasks)
      (leftCircuit (m := 2) (rightCircuit (n := n) (gridCircuit G tasks)))

theorem gridCircuit_wellFormed (G : MFamily)
    (hG : ∀ p layer, layer ∈ G.circ p → LayerOk layer)
    {n : ℕ} (tasks : Tasks n) :
    ∀ layer ∈ gridCircuit G tasks, LayerOk layer := by
  induction tasks with
  | nil => simp [gridCircuit]
  | cons task rest ih =>
    intro layer h
    rw [gridCircuit, List.mem_append] at h
    rcases h with h | h
    · exact leftCircuit_wellFormed _ (hG _) _ h
    · exact rightCircuit_wellFormed _ ih _ h

theorem coreCircuit_wellFormed (G : MFamily)
    (hG : ∀ p layer, layer ∈ G.circ p → LayerOk layer)
    {n : ℕ} (tasks : Tasks n) :
    ∀ layer ∈ coreCircuit G tasks, LayerOk layer := by
  intro layer h
  rw [coreCircuit, List.mem_append] at h
  rcases h with h | h
  · exact compileReversible_wellFormed _ _ h
  · apply castBodyCircuit_wellFormed _ _ _ _ h
    exact leftCircuit_wellFormed _
      (rightCircuit_wellFormed _ (gridCircuit_wellFormed G hG tasks))

theorem gridWidth_bound (G : MFamily) {n : ℕ} (tasks : Tasks n) (w : ℕ)
    (h : ∀ task ∈ tasks, blockWidth G task ≤ w) :
    gridWidth G tasks ≤ tasks.length * w := by
  induction tasks with
  | nil => simp [gridWidth]
  | cons task rest ih =>
    simp only [gridWidth, List.length_cons, Nat.succ_mul]
    have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have ht := h task (by simp)
    omega

theorem gridCircuit_depth_bound (G : MFamily) {n : ℕ} (tasks : Tasks n) (hdepth : ℕ)
    (h : ∀ task ∈ tasks, depth (G.circ task.length) ≤ hdepth) :
    depth (gridCircuit G tasks) ≤ tasks.length * hdepth := by
  induction tasks with
  | nil => simp [gridCircuit, depth]
  | cons task rest ih =>
    rw [gridCircuit, show ∀ {p : ℕ} (a b : Layered p),
      depth (a ++ b) = depth a + depth b from fun _ _ => List.length_append,
      leftCircuit_depth, rightCircuit_depth, List.length_cons, Nat.succ_mul]
    change depth (G.circ task.length) + depth (gridCircuit G rest) ≤ rest.length * hdepth + hdepth
    have hr := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have ht := h task (by simp)
    omega

theorem coreCircuit_depth_bound (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    depth (coreCircuit G tasks) ≤
      74 * (gridWidth G tasks + 1) + depth (gridCircuit G tasks) := by
  rw [coreCircuit, show ∀ {p : ℕ} (a b : Layered p),
    depth (a ++ b) = depth a + depth b from fun _ _ => List.length_append,
    castBodyCircuit_depth, leftCircuit_depth, rightCircuit_depth]
  apply Nat.add_le_add_right
  unfold staticLoadCircuit
  have h := BooleanProgram.circuit_depth (staticLoadOps (coreSlots G tasks))
    (show n + (staticLoadOps (coreSlots G tasks)).length ≤ n + (batchAnc G tasks + 1) by
      simp [staticLoadOps, batchAnc])
  simpa only [staticLoadOps, List.length_map, coreSlots_length] using h

end

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule77

/- Helper module GridEmitter. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch

open QAlgorithms.Complexity StaticBatch Integration9_9.LARCoinLayout

open Integration9_9.LoadedBatch.PostComposition (MultiFrameWords readFrame_correct)

def actualSamplerFrame (G : MFamily) (size : ℕ) : MultiFrameWords :=
  (unary (size + (G.anc size + 1)),
    ((List.ofFn (G.outW size)).map (fun wire => encNat wire.val),
      (G.circ size).map (List.map encInstr)))

def samplerDescriptions (G : MFamily) (sizes : List ℕ) : List (Str × Str) :=
  sizes.map (fun size => (unary size, G.encAt size))

theorem samplerFrames_eq (G : MFamily) (sizes : List ℕ) :
    samplerFrames (samplerDescriptions G sizes) = sizes.map (actualSamplerFrame G) := by
  simp only [samplerFrames, samplerDescriptions, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro size _
  exact readFrame_correct G size

theorem samplerFrameSlots (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (tasks.map (fun task => actualSamplerFrame G task.length)).flatMap Prod.fst =
      unary (gridWidth G tasks) := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
    change unary (blockWidth G task) ++
        (tasks.map (fun work => actualSamplerFrame G work.length)).flatMap Prod.fst =
      unary (blockWidth G task + gridWidth G tasks)
    rw [ih]
    simp only [unary, List.replicate_add]

theorem gridLayers_correct (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    bundleCircuitWordLayers (tasks.map (fun task => physicalFrame (actualSamplerFrame G task.length))) =
      (gridCircuit G tasks).map (List.map encInstr) := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
    rw [List.map_cons, bundleCircuitWordLayers_cons, ih, gridCircuit, List.map_append,
      leftCircuit_instructionWords]
    simp only [physicalFrame, actualSamplerFrame, shiftCircuitWords_zero]
    congr 1
    rw [shiftCircuitWords_correct]
    apply rightCircuit_instructionWords_congr
    simp [blockWidth, unary]

theorem samplerLayers_correct (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    samplerLayers (unary n, samplerFrames (samplerDescriptions G (tasks.map List.length))) =
      (castBodyCircuit (coreWidth_eq G tasks)
        (leftCircuit (m := 2) (rightCircuit (n := n) (gridCircuit G tasks)))).map
          (List.map encInstr) := by
  unfold samplerLayers
  rw [samplerFrames_eq, castBodyCircuit_instructionWords, leftCircuit_instructionWords]
  simp only [List.map_map, Function.comp_def]
  rw [gridLayers_correct, shiftCircuitWords_correct]
  apply rightCircuit_instructionWords_congr
  simp [unary]

end InfoLossLAR.WorstCase.RegevSketch

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

@[fun_prop] theorem takeTicks_poly : Poly (fun input : List Unit × ℕ => input.1.take input.2) :=
  ⟨PolyProgram.listTake Automatic.enc ()⟩

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule79

/- Helper module FramedReadout. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.NativeIndependence

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding TM2PlatformSerialization

/-- The first component provides physical-width slots and the second
provides the local sampler output wire positions. -/
abbrev Frame := List Unit × List ℕ

abbrev Layout := List Unit × List Frame

def constants (input : (ℕ × ℕ) × Str) : List ℕ :=
  input.2.map fun bit => if bit then input.1.2 else input.1.1

@[fun_prop] theorem constants_poly : Poly constants := by unfold constants; fun_prop

def frameWord (input : (ℕ × ℕ) × List ℕ) : List ℕ :=
  constants (input.1, encB input.2.length) ++ input.2

@[fun_prop] theorem frameWord_poly : Poly frameWord := by unfold frameWord; fun_prop

def frameWords (input : (ℕ × ℕ) × List (List ℕ)) : List ℕ :=
  constants (input.1, encB input.2.length) ++ input.2.flatMap (fun refs => frameWord (input.1, refs))

@[fun_prop] theorem frameWords_poly : Poly frameWords := by
  unfold frameWords
  have h : Poly (fun input : (ℕ × ℕ) × List (List ℕ) =>
      input.2.flatMap (fun refs => frameWord (input.1, refs))) := by
    apply Poly.list_flatMap _ Poly.snd
    fun_prop
  fun_prop

def fullFrame (input : (ℕ × ℕ) × (List ℕ × List (List ℕ))) : List ℕ :=
  frameWord (input.1, input.2.1) ++ frameWords (input.1, input.2.2)

@[fun_prop] theorem fullFrame_poly : Poly fullFrame := by unfold fullFrame; fun_prop

theorem constants_observed (obs : ℕ → Bool) {f t : ℕ} (hf : obs f = false) (ht : obs t = true)
    (word : Str) : (constants ((f,t),word)).map obs = word := by
  unfold constants
  rw [List.map_map]
  have h : obs ∘ (fun bit : Bool => if bit = true then t else f) = id := by
    funext bit
    cases bit <;> simp [hf,ht]
  rw [h, List.map_id]

theorem frameWord_observed (obs : ℕ → Bool) {f t : ℕ} (hf : obs f = false) (ht : obs t = true)
    (refs : List ℕ) : (frameWord ((f,t),refs)).map obs = encS (refs.map obs) := by
  simp only [frameWord, List.map_append, constants_observed obs hf ht, encS,List.length_map]

theorem frameWords_observed (obs : ℕ → Bool) {f t : ℕ} (hf : obs f = false) (ht : obs t = true)
    (refs : List (List ℕ)) : (frameWords ((f,t),refs)).map obs =
      encL encS (refs.map (List.map obs)) := by
  simp only [frameWords,List.map_append,constants_observed obs hf ht,List.map_flatMap,
    frameWord_observed obs hf ht, encL, List.length_map, List.flatMap_map]

theorem fullFrame_observed (obs : ℕ → Bool) {f t : ℕ} (hf : obs f = false) (ht : obs t = true)
    (basis : List ℕ) (pools : List (List ℕ)) :
    (fullFrame ((f,t),(basis,pools))).map obs =
      encS (basis.map obs) ++ encL encS (pools.map (List.map obs)) := by
  rw [fullFrame, List.map_append, frameWord_observed obs hf ht, frameWords_observed obs hf ht]

def bodySlots (layout : Layout) : List Unit :=
  layout.1 ++ layout.2.flatMap Prod.fst

@[fun_prop] theorem bodySlots_poly : Poly bodySlots := by
  unfold bodySlots
  have hz : Poly (fun layout : Layout => layout.2.flatMap Prod.fst) := by
    exact Poly.list_flatMap (Poly.comp Poly.fst Poly.snd) Poly.snd
  fun_prop

def allSlots (layout : Layout) : List Unit := bodySlots layout ++ [(),()]

@[fun_prop] theorem allSlots_poly : Poly allSlots := by unfold allSlots; fun_prop

/-- Offsets are measured before frame k of the consecutive sampler blocks. -/
def offset (input : Layout × ℕ) : ℕ :=
  input.1.1.length + ((input.1.2.take input.2).flatMap Prod.fst).length

@[fun_prop] theorem offset_poly : Poly offset := by
  unfold offset
  have htake : Poly (fun input : Layout × ℕ => input.1.2.take input.2) :=
    Poly.comp (f := fun x : List Frame × ℕ => x.1.take x.2)
      (g := fun x : Layout × ℕ => (x.1.2,x.2)) TM2NativeFiniteDraw.take_poly (by fun_prop)
  have hslots : Poly (fun input : Layout × ℕ => (input.1.2.take input.2).flatMap Prod.fst) :=
    Poly.list_flatMap (Poly.comp Poly.fst Poly.snd) htake
  fun_prop

def blockRefs (input : Layout × ℕ) : List ℕ :=
  (input.1.2[input.2]?.getD ([],[])).2.map (fun i => offset input + i)

@[fun_prop] theorem blockRefs_poly : Poly blockRefs := by unfold blockRefs; fun_prop

def blocksRefs (layout : Layout) : List (List ℕ) :=
  (List.range layout.2.length).map (fun i => blockRefs (layout,i))

@[fun_prop] theorem blocksRefs_poly : Poly blocksRefs := by
  unfold blocksRefs
  have h : Poly (fun layout : Layout => List.range layout.2.length) :=
    Poly.comp (f := fun frames : List Frame => List.range frames.length) Poly.list_indices Poly.snd
  fun_prop

def basisRefs (layout : Layout) : List ℕ := List.range layout.1.length

@[fun_prop] theorem basisRefs_poly : Poly basisRefs :=
  Poly.comp (f := fun slots : List Unit => List.range slots.length) Poly.list_indices Poly.fst

/-- Reserve the two final wires, true then false, and frame the observed
input and the designated sampler wire lists with their exact binary headers. -/
def readoutRefs (layout : Layout) : List ℕ :=
  fullFrame (((bodySlots layout).length + 1, (bodySlots layout).length),
    (basisRefs layout, blocksRefs layout))

@[fun_prop] theorem readoutRefs_poly : Poly readoutRefs := by unfold readoutRefs; fun_prop

theorem readoutRefs_observed (layout : Layout) (obs : ℕ → Bool)
    (hfalse : obs ((bodySlots layout).length + 1) = false)
    (htrue : obs (bodySlots layout).length = true) :
    (readoutRefs layout).map obs =
      encS ((basisRefs layout).map obs) ++ encL encS ((blocksRefs layout).map (List.map obs)) :=
  fullFrame_observed obs hfalse htrue _ _

theorem blockRefs_get (layout : Layout) (i : Fin layout.2.length) :
    (blocksRefs layout)[i.val]'(by simp [blocksRefs]) =
      layout.2[i.val].2.map (fun j => offset (layout,i.val) + j) := by
  simp only [blocksRefs, List.getElem_map, List.getElem_range, blockRefs,
    List.getElem?_eq_getElem i.isLt, Option.getD_some]

def wireToken (input : List Unit × ℕ) : Str := lengthToken (input.1.take input.2)

@[fun_prop] theorem wireToken_poly : Poly wireToken := by unfold wireToken; fun_prop

theorem wireToken_eq (slots : List Unit) (i : ℕ) (hi : i ≤ slots.length) :
    wireToken (slots,i) = encNat i := by
  simp only [wireToken, lengthToken_eq, List.length_take, Nat.min_eq_left hi]

def outputWireWords (layout : Layout) : List Str :=
  (readoutRefs layout).map (fun i => wireToken (allSlots layout, i))

@[fun_prop] theorem outputWireWords_poly : Poly outputWireWords := by unfold outputWireWords; fun_prop

theorem outputWireWords_eq (layout : Layout)
    (h : ∀ i ∈ readoutRefs layout, i < (allSlots layout).length) :
    outputWireWords layout = (readoutRefs layout).map encNat := by
  apply List.map_congr_left
  intro i hi
  exact wireToken_eq _ _ (h i hi).le

end Integration9_9.DyadicReadout

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def WellFormedLayout (layout : Layout) : Prop :=
  ∀ frame ∈ layout.2, ∀ i ∈ frame.2, i < frame.1.length

theorem offset_add_width_le (layout : Layout) (i : Fin layout.2.length) :
    offset (layout, i.val) + layout.2[i.val].1.length ≤ (bodySlots layout).length := by
  have hs := List.take_append_drop i.val layout.2
  rw [List.drop_eq_getElem_cons i.isLt] at hs
  have hl := congrArg (fun frames : List Frame => (frames.flatMap Prod.fst).length) hs
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append] at hl
  simp only [offset, bodySlots, List.length_append]
  omega

theorem blockRefs_bounded (layout : Layout) (h : WellFormedLayout layout)
    (i : Fin layout.2.length) (j : ℕ)
    (hj : j ∈ blockRefs (layout,i.val)) : j < (bodySlots layout).length := by
  unfold blockRefs at hj
  simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some, List.mem_map] at hj
  obtain ⟨k,hk,rfl⟩ := hj
  exact (Nat.add_lt_add_left (h _ (List.getElem_mem i.isLt) _ hk) _).trans_le
    (offset_add_width_le layout i)

private theorem constants_bounded {width f t : ℕ} (hf : f < width) (ht : t < width)
    (xs : Str) (r : ℕ) (hr : r ∈ constants ((f,t),xs)) : r < width := by
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
  cases b
  · exact hf
  · exact ht

private theorem frameWord_bounded {width f t : ℕ} (hf : f < width) (ht : t < width)
    (xs : List ℕ) (hx : ∀ r ∈ xs, r < width) (r : ℕ) (hr : r ∈ frameWord ((f,t),xs)) :
    r < width := by
  rcases List.mem_append.mp hr with hc | hx'
  · exact constants_bounded hf ht _ _ hc
  · exact hx _ hx'

theorem readoutRefs_bounded (layout : Layout) (h : WellFormedLayout layout) :
    ∀ r ∈ readoutRefs layout, r < (allSlots layout).length := by
  have hall : (allSlots layout).length = (bodySlots layout).length + 2 := by simp [allSlots]
  have hf : (bodySlots layout).length + 1 < (allSlots layout).length := by omega
  have ht : (bodySlots layout).length < (allSlots layout).length := by omega
  have hb (i : ℕ) (hi : i ∈ basisRefs layout) : i < (allSlots layout).length := by
    have hbasis := List.mem_range.mp hi
    have hlen : layout.1.length ≤ (bodySlots layout).length := by
      simp [bodySlots]
    omega
  have hlo (refs : List ℕ) (hr : refs ∈ blocksRefs layout) (i : ℕ) (hi : i ∈ refs) :
      i < (allSlots layout).length := by
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    have h' := blockRefs_bounded layout h ⟨k, List.mem_range.mp hk⟩ i hi
    omega
  intro r hr
  rcases List.mem_append.mp hr with hfb | hfp
  · exact frameWord_bounded hf ht _ hb _ hfb
  · rcases List.mem_append.mp hfp with hc | hrefs
    · exact constants_bounded hf ht _ _ hc
    · obtain ⟨refs,hrefs,hfref⟩ := List.mem_flatMap.mp hrefs
      exact frameWord_bounded hf ht _ (hlo _ hrefs) _ hfref

/-- The output wire selector, with genuine finite physical addresses. -/
def framedOutput (layout : Layout) (h : WellFormedLayout layout)
    (r : Fin (readoutRefs layout).length) : Fin (allSlots layout).length :=
  ⟨(readoutRefs layout)[r.val], readoutRefs_bounded layout h _ (List.getElem_mem r.isLt)⟩

theorem outputWireWords_spec (layout : Layout) (h : WellFormedLayout layout) :
    outputWireWords layout =
      (List.ofFn (framedOutput layout h)).map (fun i => encNat i.val) := by
  rw [outputWireWords_eq layout (readoutRefs_bounded layout h)]
  simp only [List.map_ofFn, Function.comp_def, framedOutput]
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map encNat) (List.ofFn_getElem (xs := readoutRefs layout)).symm

/-- A total observation of a natural wire address, with a harmless default outside the layout. -/
def rawBit {width : ℕ} (b : Bits width) (i : ℕ) : Bool :=
  if hi : i < width then b ⟨i,hi⟩ else false

end Integration9_9.DyadicReadout

end P2MDyadicModule80

/- Helper module StaticBatchReadout. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.StaticBatch

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open LoadedBatch.PostComposition (MultiFrameWords readFrame readFrame_correct)

def typedFrame (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) : Frame :=
  (List.replicate (blockWidth G task) (),
    List.ofFn fun j => (G.outW task.length j).val)

def typedLayout (G : MFamily) {n : ℕ} (tasks : Tasks n) : Layout :=
  (List.replicate n (), tasks.map (typedFrame G))

def encodedFrame (frame : MultiFrameWords) : Frame :=
  (frame.1.map (fun _ => ()), frame.2.1.map QMCNumericRuntime.inputWidth)

@[fun_prop] theorem encodedFrame_poly : Poly encodedFrame := by unfold encodedFrame; fun_prop

def encodedLayout (data : Str × List MultiFrameWords) : Layout :=
  (data.1.map (fun _ => ()), data.2.map encodedFrame)

@[fun_prop] theorem encodedLayout_poly : Poly encodedLayout := by unfold encodedLayout; fun_prop

theorem encodedFrame_correct (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) :
    encodedFrame (readFrame (unary task.length, G.encAt task.length)) = typedFrame G task := by
  unfold encodedFrame typedFrame
  rw [readFrame_correct]
  change ((unary (blockWidth G task)).map (fun _ => ()),
      (_ : List ℕ)) = _
  congr 1
  · simp [unary]
  · rw [List.map_map, List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    simp [Function.comp_def, QMCNumericRuntime.inputWidth_prefix, encNat]

theorem encodedLayout_correct (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    encodedLayout (unary n, tasks.map (fun task => readFrame (unary task.length, G.encAt task.length))) =
      typedLayout G tasks := by
  unfold encodedLayout typedLayout
  simp only [unary, List.map_replicate, List.map_map, Function.comp_def]
  exact congrArg (Prod.mk (List.replicate n ())) (List.map_congr_left (fun task _ => encodedFrame_correct G task))

theorem frameWellFormed (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    WellFormedLayout (typedLayout G tasks) := by
  intro frame hframe i hi
  obtain ⟨task, _, rfl⟩ := List.mem_map.mp hframe
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  change (G.outW task.length j).val < (List.replicate (blockWidth G task) ()).length
  rw [List.length_replicate]
  exact (G.outW task.length j).isLt

theorem typedLayout_frame_width (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    ((tasks.map (typedFrame G)).flatMap Prod.fst).length = gridWidth G tasks := by
  induction tasks with
  | nil => rfl
  | cons task rest ih => simp [typedFrame, gridWidth, ih]

theorem typedLayout_body_width (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (bodySlots (typedLayout G tasks)).length = n + gridWidth G tasks := by
  simp only [bodySlots, typedLayout, List.length_append, List.length_replicate, typedLayout_frame_width]

theorem typedLayout_width (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    (allSlots (typedLayout G tasks)).length = n + (batchAnc G tasks + 1) := by
  simpa [allSlots, typedLayout_body_width] using coreWidth_eq G tasks

private theorem gridWire_prefix {n : ℕ} (G : MFamily) (tasks : Tasks n)
    (i : Fin tasks.length) (j : Fin (blockWidth G (tasks.get i))) :
    (gridWire G tasks i j).val = gridWidth G (tasks.take i.val) + j.val := by
  induction tasks with
  | nil => exact Fin.elim0 i
  | cons head rest ih =>
    refine Fin.cases (motive := fun a => ∀ j : Fin (blockWidth G ((head :: rest).get a)),
      (gridWire G (head :: rest) a j).val = gridWidth G ((head :: rest).take a.val) + j.val)
      ?_ ?_ i j
    · intro k
      simp only [gridWire, Fin.cases_zero, Fin.val_castAdd, Fin.val_zero, List.take_zero, gridWidth, zero_add]
    · intro a k
      simp only [gridWire, Fin.cases_succ, Fin.val_natAdd, Fin.val_succ, List.take_succ_cons, gridWidth]
      rw [ih a k, Nat.add_assoc]

private theorem offset_eq {n : ℕ} (G : MFamily) (tasks : Tasks n) (i : ℕ) :
    offset (typedLayout G tasks,i) = n + gridWidth G (tasks.take i) := by
  simp only [offset, typedLayout, List.length_replicate, ← List.map_take, typedLayout_frame_width]

theorem blockWire_val {n : ℕ} (G : MFamily) (tasks : Tasks n)
    (i : Fin tasks.length) (j : Fin (blockWidth G (tasks.get i))) :
    (blockWire G tasks i j).val = offset (typedLayout G tasks,i.val) + j.val := by
  simp only [blockWire, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, offset_eq, gridWire_prefix, Nat.add_assoc]

def readoutWire (G : MFamily) {n : ℕ} (tasks : Tasks n)
    (j : Fin (readoutRefs (typedLayout G tasks)).length) :
    Fin (n + (batchAnc G tasks + 1)) :=
  Fin.cast (typedLayout_width G tasks) (framedOutput (typedLayout G tasks) (frameWellFormed G tasks) j)

/-- The physical core followed by an output wire list that frames projected
sampler words. Repeated wire indices encode the public fixed header bits. -/
noncomputable def batchReadoutFamily (G : MFamily) (tasks : ∀ n, Tasks n) : MFamily where
  anc n := batchAnc G (tasks n)
  circ n := coreCircuit G (tasks n)
  outLen n := (readoutRefs (typedLayout G (tasks n))).length
  outW n := readoutWire G (tasks n)

theorem batchReadout_encodedWires (G : MFamily) (tasks : ∀ n, Tasks n) (n : ℕ) :
    (List.ofFn ((batchReadoutFamily G tasks).outW n)).map (fun j => encNat j.val) =
      outputWireWords (typedLayout G (tasks n)) := by
  rw [outputWireWords_spec (typedLayout G (tasks n)) (frameWellFormed G (tasks n))]
  simp only [batchReadoutFamily,readoutWire,List.map_ofFn,Function.comp_def,Fin.val_cast]

def inputWord (G : MFamily) {n : ℕ} (tasks : Tasks n) (bits : Bits (n + (batchAnc G tasks + 1))) : Str :=
  List.ofFn (fun i => bits (inputWire G tasks i))

def trialWords (G : MFamily) {n : ℕ} (tasks : Tasks n) (bits : Bits (n + (batchAnc G tasks + 1))) : List Str :=
  List.ofFn fun i => List.ofFn fun j => bits (blockWire G tasks i (G.outW (tasks.get i).length j))

private theorem basisRefs_observed {n : ℕ} (G : MFamily) (tasks : Tasks n)
    (bits : Bits (n + (batchAnc G tasks + 1))) :
    (basisRefs (typedLayout G tasks)).map (rawBit bits) = inputWord G tasks bits := by
  apply List.ext_getElem
  · simp [basisRefs, typedLayout, inputWord]
  · intro i hi ho
    have h : i < n := by simpa only [inputWord, List.length_ofFn] using ho
    simp only [basisRefs, List.getElem_map, List.getElem_range, inputWord, List.getElem_ofFn]
    unfold rawBit inputWire
    rw [dif_pos (show i < n + (batchAnc G tasks + 1) by omega)]
    rfl

private theorem blocksRefs_observed {n : ℕ} (G : MFamily) (tasks : Tasks n)
    (bits : Bits (n + (batchAnc G tasks + 1))) :
    (blocksRefs (typedLayout G tasks)).map (List.map (rawBit bits)) = trialWords G tasks bits := by
  apply List.ext_getElem
  · simp [blocksRefs, typedLayout, trialWords]
  · intro i hi ho
    let j : Fin tasks.length := ⟨i, by simpa [trialWords] using ho⟩
    have hj : i < (typedLayout G tasks).2.length := by simpa only [typedLayout,List.length_map] using j.isLt
    rw [List.getElem_map, blockRefs_get (typedLayout G tasks) ⟨i,hj⟩]
    simp only [typedLayout,List.getElem_map,typedFrame,List.map_ofFn,Function.comp_def,
      trialWords,List.getElem_ofFn,List.get_eq_getElem]
    apply congrArg List.ofFn
    funext k
    have he := blockWire_val G tasks j (G.outW (tasks.get j).length k)
    let wire := blockWire G tasks j (G.outW (tasks.get j).length k)
    change rawBit bits (offset (typedLayout G tasks,i) + (G.outW (tasks.get j).length k).val) = bits wire
    have he' : wire.val = offset (typedLayout G tasks,i) + (G.outW (tasks.get j).length k).val := he
    rw [← he', rawBit, dif_pos wire.isLt]

theorem batchReadout_word {n : ℕ} (G : MFamily) (tasks : Tasks n)
    (bits : Bits (n + (batchAnc G tasks + 1)))
    (htrue : bits (constantWire G tasks true) = true)
    (hfalse : bits (constantWire G tasks false) = false) :
    List.ofFn (fun j => bits (readoutWire G tasks j)) =
      encS (inputWord G tasks bits) ++ encL encS (trialWords G tasks bits) := by
  have hT : rawBit bits (bodySlots (typedLayout G tasks)).length = true := by
    rw [typedLayout_body_width, rawBit,
      dif_pos (show n + gridWidth G tasks < n + (batchAnc G tasks + 1) by unfold batchAnc; omega)]
    exact htrue
  have hF : rawBit bits ((bodySlots (typedLayout G tasks)).length + 1) = false := by
    rw [typedLayout_body_width, rawBit,
      dif_pos (show n + gridWidth G tasks + 1 < n + (batchAnc G tasks + 1) by unfold batchAnc; omega)]
    exact hfalse
  rw [← basisRefs_observed G tasks bits, ← blocksRefs_observed G tasks bits,
    ← readoutRefs_observed (typedLayout G tasks) (rawBit bits) hF hT]
  apply List.ext_getElem
  · simp
  · intro i hi ho
    have hix : i < (readoutRefs (typedLayout G tasks)).length := by simpa using hi
    have h := readoutRefs_bounded (typedLayout G tasks) (frameWellFormed G tasks)
      (readoutRefs (typedLayout G tasks))[i] (List.getElem_mem hix)
    rw [typedLayout_width] at h
    simp only [List.getElem_map,List.getElem_ofFn,readoutWire,framedOutput,rawBit,dif_pos h]
    rfl

end Integration9_9.DyadicReadout

end P2MDyadicModule81

/- Helper module StaticBatchSemantics. -/
section P2MDyadicModule82

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.StaticBatch

open QAlgorithms.Complexity TM2Boolean

open Integration9_9.LoadedBatch Integration9_9.LARCoinLayout

noncomputable section

def slotValue {n : ℕ} (input : Bits n) (slot : StaticLoadSlot n) : Bool :=
  slot.elim id input

def queryBits {n : ℕ} (input : Bits n) (task : List (StaticLoadSlot n)) : Bits task.length :=
  fun i => slotValue input task[i.val]

def queryWord {n : ℕ} (input : Bits n) (task : List (StaticLoadSlot n)) : Str :=
  List.ofFn (queryBits input task)

@[simp] theorem queryWord_length {n : ℕ} (input : Bits n) (task : List (StaticLoadSlot n)) :
    (queryWord input task).length = task.length := by simp [queryWord]

theorem taskSlots_value (G : MFamily) {n : ℕ} (input : Bits n)
    (task : List (StaticLoadSlot n)) (i : Fin (blockWidth G task)) :
    slotValue input ((taskSlots G task)[i.val]'(by simpa only [taskSlots_length] using i.isLt)) =
      (Fin.append (queryBits input task) (fun _ => false) : Bits (blockWidth G task)) i := by
  unfold blockWidth at i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [taskSlots, Fin.val_castAdd, Fin.append_left, queryBits]
    rw [List.getElem_append_left j.isLt]
  · intro j
    simp only [taskSlots, Fin.val_natAdd, Fin.append_right]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [List.getElem_replicate, slotValue, Sum.elim_inl, id_eq]

def gridBits (G : MFamily) {n : ℕ} (input : Bits n) :
    (tasks : Tasks n) → Bits (gridWidth G tasks)
  | [] => fun _ => false
  | task :: rest => Fin.append
      (show Bits (blockWidth G task) from Fin.append (queryBits input task) (fun _ => false))
      (gridBits G input rest)

theorem gridSlots_value (G : MFamily) {n : ℕ} (input : Bits n) (tasks : Tasks n)
    (i : Fin (gridWidth G tasks)) :
    slotValue input ((gridSlots G tasks)[i.val]'(by simpa only [gridSlots_length] using i.isLt)) =
      gridBits G input tasks i := by
  induction tasks with
  | nil => exact Fin.elim0 i
  | cons task rest ih =>
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [gridSlots, Fin.val_castAdd, gridBits, Fin.append_left]
      rw [List.getElem_append_left (by simpa only [taskSlots_length] using j.isLt)]
      exact taskSlots_value G input task j
    · intro j
      simp only [gridSlots, Fin.val_natAdd, gridBits, Fin.append_right]
      rw [List.getElem_append_right (by simp only [taskSlots_length]; omega)]
      simpa only [taskSlots_length, Nat.add_sub_cancel_left] using ih j

def reserveBits : Bits 2 := fun i => decide (i.val = 0)

def packedBits (G : MFamily) {n : ℕ} (input : Bits n) (tasks : Tasks n) :
    Bits ((n + gridWidth G tasks) + 2) :=
  Fin.append (Fin.append input (gridBits G input tasks)) reserveBits

theorem wordExtension_input (word : Str) (i : Fin word.length) :
    wordExtension word i.val = toBits word i := by
  have h := congrFun (wordExtension_basis word 0) (Fin.castAdd 1 i)
  simpa only [Fin.append_left, Fin.val_castAdd] using h.symm

theorem coreLoadedBit (G : MFamily) (word : Str) (tasks : Tasks word.length)
    (i : Fin ((word.length + gridWidth G tasks) + 2)) :
    staticLoadedBit word (coreSlots G tasks) i.val = packedBits G (toBits word) tasks i := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [packedBits, Fin.append_left, Fin.val_castAdd, staticLoadedBit, k.isLt, if_true]
      exact wordExtension_input word k
    · intro k
      have hidx : word.length + k.val - word.length = k.val := by omega
      have hk : k.val < (coreSlots G tasks).length := by simp only [coreSlots_length]; omega
      simp only [packedBits, Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd,
        staticLoadedBit, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false, hidx, hk, dif_pos]
      have hgrid : k.val < (gridSlots G tasks).length := by simpa only [gridSlots_length] using k.isLt
      unfold coreSlots
      rw [List.getElem_append_left hgrid]
      refine Eq.trans ?_ (gridSlots_value G (toBits word) tasks k)
      cases (gridSlots G tasks)[k.val] with
      | inl b => rfl
      | inr s => exact wordExtension_input word s
  · intro j
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    simp only [packedBits, Fin.append_right, Fin.val_natAdd, staticLoadedBit, reserveBits]
    have hl : ¬ word.length + gridWidth G tasks + j.val < word.length := by omega
    have he : word.length + gridWidth G tasks + j.val - word.length = gridWidth G tasks + j.val := by omega
    simp only [hl, if_false, he]
    rcases hj with h0 | h1
    · simp only [h0, Nat.add_zero, coreSlots_length, Nat.lt_succ_self, dif_pos, decide_true]
      unfold coreSlots
      rw [List.getElem_append_right (by simp)]
      simp [gridSlots_length]
    · simp [h1]

theorem coreCircuit_tensor (G : MFamily) (word : Str) (tasks : Tasks word.length) :
    runLayered (coreCircuit G tasks) (basisInput (a := batchAnc G tasks) (toBits word)) =
      castState (coreWidth_eq G tasks)
        (tensorState (tensorState (computationalBasis (toBits word))
          (runLayered (gridCircuit G tasks) (computationalBasis (gridBits G (toBits word) tasks))))
          (computationalBasis reserveBits)) := by
  unfold coreCircuit
  rw [show ∀ {p : ℕ} (a b : Layered p) (s : QState p),
    runLayered (a ++ b) s = runLayered b (runLayered a s) from
    fun _ _ _ => List.foldl_append]
  rw [staticLoadCircuit_basis]
  have hinit : computationalBasis (fun i : Fin (word.length + (batchAnc G tasks + 1)) =>
      staticLoadedBit word (coreSlots G tasks) i.val) =
      castState (coreWidth_eq G tasks) (computationalBasis (packedBits G (toBits word) tasks)) := by
    rw [castState_basis]
    congr 1
    funext i
    exact coreLoadedBit G word tasks (Fin.cast (coreWidth_eq G tasks).symm i)
  rw [hinit, runLayered_cast]
  unfold packedBits
  rw [computationalBasis_tensor, computationalBasis_tensor, leftCircuit_tensor, rightCircuit_tensor]

end

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule82

/- Helper module schedule.ScheduleTasks. -/
section P2MDyadicModule83

set_option autoImplicit false

set_option maxHeartbeats 900000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def slotSource {length : ℕ} : StaticLoadSlot length → Bool × ℕ
  | .inl b => (false, if b then 1 else 0)
  | .inr i => (true, i.val)

end InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule

end P2MDyadicModule83

/- Helper module DyadicUniform. -/
section P2MDyadicModule84

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSketch

open QAlgorithms.Complexity StaticBatch

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.DyadicReadout

open Integration9_9.LoadedBatch.PostComposition (MultiFrameWords multi_encoding)

abbrev Sources := List (Bool × ℕ)

def loadBlock (input : Sources × (Str × Str)) : Sources :=
  input.1 ++ ((unaryPayload input.2.2 ++ [false]).map (fun _ => (false, 0)))

@[fun_prop] theorem loadBlock_poly : Poly loadBlock := by
  unfold loadBlock
  fun_prop

def loadAll (input : List Sources × List (Str × Str)) : Sources :=
  (input.1.zip input.2).flatMap loadBlock ++ [(false, 1)]

@[fun_prop] theorem loadAll_poly : Poly loadAll := by
  unfold loadAll
  have h : Poly (fun input : List Sources × List (Str × Str) =>
      (input.1.zip input.2).flatMap loadBlock) :=
    Poly.list_flatMap (Poly.comp loadBlock_poly Poly.snd) Poly.list_zip
  fun_prop

theorem loadBlock_correct (G : MFamily) {n : ℕ} (task : List (StaticLoadSlot n)) :
    loadBlock (task.map DyadicSchedule.slotSource, (unary task.length, G.encAt task.length)) =
      (taskSlots G task).map loadSource := by
  unfold loadBlock taskSlots
  rw [multi_encoding]
  simp only [List.append_assoc, unaryPayload_encNat, List.map_append,
    List.map_replicate, List.map_cons, List.map_nil, unary]
  have hsource : task.map DyadicSchedule.slotSource = task.map loadSource :=
    List.map_congr_left (fun slot _ => by cases slot <;> rfl)
  rw [hsource]
  simp only [List.replicate_add, List.replicate_one, loadSource, Bool.false_eq_true, if_false]

theorem loadAll_correct (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    loadAll (tasks.map (List.map DyadicSchedule.slotSource),
      samplerDescriptions G (tasks.map List.length)) = (coreSlots G tasks).map loadSource := by
  unfold loadAll coreSlots
  simp only [List.map_append]
  congr 1
  induction tasks with
  | nil => rfl
  | cons task rest ih =>
    simp only [List.map_cons, samplerDescriptions, List.zip_cons_cons, List.flatMap_cons, gridSlots]
    rw [loadBlock_correct, List.map_append]
    congr 1

def ancillaSlots (frames : List MultiFrameWords) : List Unit :=
  (frames.flatMap Prod.fst).map (fun _ => ()) ++ [()]

@[fun_prop] theorem ancillaSlots_poly : Poly ancillaSlots := by
  unfold ancillaSlots
  have h : Poly (fun frames : List MultiFrameWords => frames.flatMap Prod.fst) :=
    Poly.list_flatMap (Poly.comp Poly.fst Poly.snd) Poly.identity
  fun_prop

theorem ancillaSlots_correct (G : MFamily) {n : ℕ} (tasks : Tasks n) :
    ancillaSlots (samplerFrames (samplerDescriptions G (tasks.map List.length))) =
      List.replicate (batchAnc G tasks) () := by
  unfold ancillaSlots
  simp only [samplerFrames_eq, List.map_map, Function.comp_def, samplerFrameSlots]
  simp only [unary, batchAnc, List.replicate_add, List.replicate_one, List.map_replicate]

end InfoLossLAR.WorstCase.RegevSketch

end P2MDyadicModule84

/- Helper module PreFamily. -/
section P2MDyadicModule85

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.LoadedBatch

open Integration9_9.TM2PlatformSerialization

open LoadedBatch.PostComposition (readFrame)

open TM2Boolean.PolyProgramCircuit

noncomputable section

def erase (K : MFamily) : Family where
  anc := K.anc
  circ := K.circ
  out _ := ⟨0, by omega⟩

def eraseWord (x : Str × Str) : Str :=
  lengthToken (unaryPayload x.2) ++ encNat 0 ++
    serializeWords ((readFrame x).2.2.map serializeWords)

@[fun_prop] theorem eraseWord_poly : Poly eraseWord := by
  unfold eraseWord
  fun_prop

def withSingle (x : Str × Str) : Str × Str := (x.1,eraseWord x)

@[fun_prop] theorem withSingle_poly : Poly withSingle := by unfold withSingle; fun_prop

def tables (K : MFamily) (k : ℕ) := List.ofFn (fun i : Fin (k+1) => (unary i.val,K.encAt i.val))

def wire {f : Str → Str} (P : PolyProgram id id f) (K : MFamily) (L : Polynomial ℕ)
    (n : ℕ) (j : Fin (K.outLen (L.eval n))) : Fin (machineWidth P (erase K) L 1 n) :=
  ⟨preWidth P n + (K.outW (L.eval n) j).val, by
    have hj := (K.outW (L.eval n) j).isLt
    rw [width_eq]
    simp only [callWidth,Polynomial.eval_one,one_mul,erase]
    omega⟩

def family {f : Str → Str} (P : PolyProgram id id f) (K : MFamily) (L : Polynomial ℕ) : MFamily where
  anc := machineAnc P (erase K) L 1
  circ := machineCircuit P (erase K) L 1
  outLen n := K.outLen (L.eval n)
  outW := wire P K L

def instructions {f : Str → Str} (P : PolyProgram id id f) (x : Str × List (Str × Str)) : Str :=
  let one := (x.1, x.2.map withSingle)
  let out := (readFrame (RepeatedQuery.lastDescription x.2)).2.1
  let shifted := out.map (shiftWireWord ((preSlots P x.1).map (fun _ => true)))
  lengthToken (ancSlots P 1 one) ++ serializeWords shifted ++
    serializeWords ((wordLayers P 1 one).map serializeWords)

@[fun_prop] theorem instructions_poly {f : Str → Str} (P : PolyProgram id id f) :
    Poly (instructions P) := by unfold instructions; fun_prop

end

end MultiPre

end P2MDyadicModule85

/- Helper module PreUniform. -/
section P2MDyadicModule86

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.LoadedBatch

open RegevSketch (batchBuilder_polyTime)

open Integration9_9.TM2PlatformSerialization

open LoadedBatch.PostComposition (readFrame_correct)

open TM2Boolean.PolyProgramCircuit

noncomputable section

theorem eraseWord_correct (K : MFamily) (n : ℕ) :
    eraseWord (unary n,K.encAt n) = encFamilyAt (erase K) n := by
  unfold eraseWord
  rw [readFrame_correct,PostComposition.multi_encoding]
  simp only [List.append_assoc, unaryPayload_encNat, lengthToken_eq,unary,List.length_replicate,
    serializeWords_eq, encFamilyAt,erase, encCirc,List.map_map, Function.comp_def]
  rfl

theorem tables_erase (K : MFamily) (k : ℕ) :
    (tables K k).map withSingle = describedQueryBlocks (erase K) k := by
  simp only [tables, List.map_ofFn, Function.comp_def, withSingle, eraseWord_correct, describedQueryBlocks]

theorem tables_last (K : MFamily) (k : ℕ) :
    RepeatedQuery.lastDescription (tables K k) = (unary k,K.encAt k) := by
  unfold RepeatedQuery.lastDescription tables
  rw [List.ofFn_succ']
  simp

theorem instructions_correct {f : Str → Str} (P : PolyProgram id id f) (K : MFamily)
    (L : Polynomial ℕ) (hfits : Fits P L 1) (n : ℕ) :
    instructions P (unary n,tables K (L.eval n)) = (family P K L).encAt n := by
  simp only [instructions,tables_erase,tables_last,readFrame_correct]
  simp only [lengthToken_eq,ancSlots_length,wordLayers_correct P (erase K) L 1 hfits,
    serializeWords_eq,PostComposition.multi_encoding, family,encCirc,List.map_map,
    List.map_ofFn, Function.comp_def]
  congr 2
  apply congrArg encStr
  apply congrArg List.ofFn
  funext i
  simp only [shiftWireWord_spec,List.length_map,preSlots_length,wire,Fin.val_mk]
  simp [QMCNumericRuntime.inputWidth_prefix,encNat]

theorem family_isMQPT {f : Str → Str} (P : PolyProgram id id f) (K : MFamily) (hK : IsMQPT K)
    (L : Polynomial ℕ) (hfits : Fits P L 1) : IsMQPT (family P K L) := by
  have unary_mem (word query : Str) (h : query ∈ bundleRequests L word) :
      query = unary query.length := by
    rw [bundleRequests_correct] at h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    simp [unary]
  constructor
  · refine ⟨fun word => instructions P (word,tables K (L.eval word.length)), ?_, ?_⟩
    · have h := batchBuilder_polyTime K hK _ (bundleRequests_poly L) unary_mem _ (instructions_poly P)
      simpa only [bundleRequests_correct,List.map_ofFn,Function.comp_def,unary,List.length_replicate,tables] using h
    · intro n
      simpa only [unary,List.length_replicate] using instructions_correct P K L hfits n
  · obtain ⟨p,hp⟩ := hK.2.2
    have hQ : PolyBounded (erase K) :=
      ⟨p,fun n => (hp n).1,fun n => (hp n).2.1⟩
    obtain ⟨b,hb⟩ := machine_polyBounded P (erase K) L 1 hQ
    refine ⟨machine_wellFormed P (erase K) L 1 hK.2.1, b+p.comp L,?_⟩
    intro n
    have h := hb n
    have hlength := (hp (L.eval n)).2.2
    simp only [Polynomial.eval_add,Polynomial.eval_comp]
    exact ⟨le_trans h.1 (Nat.le_add_right _ _),le_trans h.2.1 (Nat.le_add_right _ _),
      le_trans hlength (Nat.le_add_left _ _)⟩

end

end MultiPre

end P2MDyadicModule86

/- Helper module PreLaw. -/
section P2MDyadicModule87

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary Integration9_9 Integration9_9.LoadedBatch

open TM2Boolean.PolyProgramCircuit

open scoped BigOperators Classical

noncomputable section

def bitAt {k : ℕ} (s : Bits k) (index : ℕ) : Bool :=
  if h : index < k then s ⟨index,h⟩ else false

def read {k : ℕ} (K : MFamily) (length : ℕ) (s : Bits k) : Str :=
  List.ofFn fun j => bitAt s (K.outW length j).val

def gridProb (K : MFamily) (length : ℕ) (ev : Str → Prop) (tasks : List QuantumBlock) : ℝ :=
  ∑ s : Bits (bundleWidth tasks), if ev (read K length s) then
    ‖runLayered (bundleCircuit tasks) (bundleState tasks) s‖^2 else 0

private theorem rightBasis {l r : ℕ} (s : QState l) (b : Bits r) (ev : Bits (l+r) → Prop) :
    (∑ x, if ev x then ‖tensorState s (computationalBasis b) x‖^2 else 0) =
    ∑ x, if ev (Fin.append x b) then ‖s x‖^2 else 0 := by
  simpa only [decide_eq_true_eq] using tensorBasis_event_probability s b (fun x => decide (ev x))

private theorem leftBasis {l r : ℕ} (b : Bits l) (s : QState r) (ev : Bits (l+r) → Prop) :
    (∑ x, if ev x then ‖tensorState (computationalBasis b) s x‖^2 else 0) =
    ∑ x, if ev (Fin.append b x) then ‖s x‖^2 else 0 := by
  simpa only [decide_eq_true_eq] using basisTensor_event_probability b s (fun x => decide (ev x))

theorem lawGrid {f : Str → Str} (P : PolyProgram id id f) (K : MFamily) (L : Polynomial ℕ)
    (hfits : Fits P L 1) (word : Str) (ev : Str → Prop) :
    outputProb (family P K L) word ev = gridProb K (L.eval word.length) ev
        (actualBlocks P (erase K) L 1 word) := by
  let Q := erase K
  change (∑ s, if ev (List.ofFn fun j => s (wire P K L word.length j)) then
    ‖runLayered ((machine P Q L 1).circ word.length)
      (basisInput (a := (machine P Q L 1).anc word.length) (toBits word)) s‖^2 else 0) = _
  rw [machineState_tensor P Q L 1 hfits,castState_event,rightBasis,leftBasis]
  apply Finset.sum_congr rfl
  intro data _
  have hw := actualBlocks_width P Q L 1 word
  have hlen : bundleWidth (actualBlocks P Q L 1 word) =
      L.eval word.length + (K.anc (L.eval word.length) + 1) := by
    simpa only [callWidth,Polynomial.eval_one,one_mul,Q,erase] using hw
  have hp (j : Fin (K.outLen (L.eval word.length))) :
      (Fin.append (Fin.append (result P word) data) (fun _ : Fin 1 => false))
        (Fin.cast (tensorWidth P Q L 1 word).symm (wire P K L word.length j)) =
      bitAt data (K.outW (L.eval word.length) j).val := by
    let location := Fin.cast hlen.symm (K.outW (L.eval word.length) j)
    have he : Fin.cast (tensorWidth P Q L 1 word).symm (wire P K L word.length j) =
        Fin.castAdd 1 (Fin.natAdd (preWidth P word.length) location) := Fin.ext rfl
    rw [he,Fin.append_left]
    rw [Fin.append_right (show Bits (preWidth P word.length) from result P word) data location]
    simp only [bitAt, show (K.outW (L.eval word.length) j).val < _ from location.isLt, dif_pos]
    rfl
  have hh := congrArg List.ofFn (funext hp)
  change (if ev _ then _ else 0) = (if ev (read K (L.eval word.length) data) then _ else 0)
  dsimp only [read] at *
  rw [hh]

theorem singleton (K : MFamily) (k : ℕ) (bits : Bits k) (ev : Str → Prop) :
    gridProb K k ev [familyBlock (erase K) k bits] =
    ∑ s : Bits (k+(K.anc k+1)), if ev (List.ofFn fun j => s (K.outW k j)) then
      ‖runLayered (K.circ k) (basisInput bits) s‖^2 else 0 := by
  let b : Bits 0 := fun j => Fin.elim0 j
  have single : bundleState [] = computationalBasis b := by
    funext y
    have h : y = b := funext fun i => Fin.elim0 i
    simp [bundleState,computationalBasis,h]
  change (∑ s : Bits ((k+(K.anc k+1))+0), if ev (read K k s) then
    ‖runLayered (leftCircuit (m := 0) (K.circ k) ++ rightCircuit (n := k+(K.anc k+1)) (show Layered 0 from bundleCircuit []))
      (tensorState (basisInput bits) (bundleState [])) s‖^2 else 0) = _
  rw [disjointCircuits_tensor,single]
  change (∑ s, if ev (read K k s) then ‖tensorState (runLayered (K.circ k) (basisInput bits))
    (computationalBasis b) s‖^2 else 0) = _
  rw [rightBasis]
  apply Finset.sum_congr rfl
  intro s _
  have h (j : Fin (K.outLen k)) : bitAt (Fin.append s b) (K.outW k j).val = s (K.outW k j) := by
    have hj : (K.outW k j).val < (k+(K.anc k+1))+0 := (K.outW k j).isLt
    rw [bitAt,dif_pos hj]
    exact Fin.append_left s b (K.outW k j)
  rw [read, congrArg List.ofFn (funext h)]

private theorem prob_at {n : ℕ} (K : MFamily) (word : Str) (ev : Str → Prop)
    (h : word.length = n) (x : Bits n) (hx : (fun i => toBits word (Fin.cast h.symm i)) = x) :
    outputProb K word ev = ∑ s : Bits (n+(K.anc n+1)), if ev (List.ofFn fun j => s (K.outW n j))
      then ‖runLayered (K.circ n) (basisInput x) s‖^2 else 0 := by
  cases h
  subst x
  rfl

theorem prob_ofFn {n : ℕ} (K : MFamily) (x : Bits n) (ev : Str → Prop) :
    outputProb K (List.ofFn x) ev = ∑ s : Bits (n+(K.anc n+1)), if ev (List.ofFn fun j => s (K.outW n j))
      then ‖runLayered (K.circ n) (basisInput x) s‖^2 else 0 := by
  apply prob_at _ _ _ List.length_ofFn x
  funext i
  simp [toBits]

theorem law {f : Str → Str} (P : PolyProgram id id f) (K : MFamily) (L : Polynomial ℕ)
    (hfits : Fits P L 1) (word : Str) (ev : Str → Prop) :
    outputProb (family P K L) word ev = outputProb K (queryWord f (L.eval word.length) word 0) ev := by
  rw [lawGrid P K L hfits]
  let bits := fun i : Fin (L.eval word.length) => ((f word)[i.val]?).getD false
  have h : actualBlocks P (erase K) L 1 word = [familyBlock (erase K) (L.eval word.length) bits] := by
    simp [actualBlocks,trialBlocks,bits]
  rw [h,singleton,queryWord,prob_ofFn]
  simp only [bits,Nat.zero_mul,Nat.zero_add]

end

end MultiPre

end P2MDyadicModule87

/- Helper module PreFinal. -/
section P2MDyadicModule88

set_option autoImplicit false

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.LoadedBatch

open TM2Boolean.PolyProgramCircuit

noncomputable section

theorem precompose (f : Str → Str) (hf : Poly f) (K : MFamily) (hK : IsMQPT K) :
    ∃ F : MFamily, IsMQPT F ∧ ∀ w event, outputProb F w event =
      outputProb K (paddedOutput (LARCoinLayout.rawPolyProgram hf) w) event := by
  let P := LARCoinLayout.rawPolyProgram hf
  let L := capacityPolynomial P
  have fits : Fits P L 1 := by
    intro n
    simp only [L,Polynomial.eval_one,one_mul,capacityPolynomial_eval,le_refl]
  refine ⟨family P K L,family_isMQPT P K hK L fits,?_⟩
  intro word event
  rw [law P K L fits]
  apply congrArg (fun w => outputProb K w event)
  simp only [L,capacityPolynomial_eval,queryWord,paddedOutput,Nat.zero_mul,Nat.zero_add,P,Fin.val_cast]

end

end MultiPre

end P2MDyadicModule88

/- Helper module StaticBatchBornReadout. -/
section P2MDyadicModule89

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.StaticBatch

open QAlgorithms.Complexity

open Integration9_9.LoadedBatch

noncomputable section

private theorem computationalBasis_unit {n : ℕ} (input : Bits n) :
    (∑ state, ‖computationalBasis input state‖^2) = (1 : ℝ) := by
  rw [Fintype.sum_eq_single input]
  · simp [computationalBasis]
  · intro s hs
    simp [computationalBasis, hs]

def gridBlockRead (G : MFamily) {n : ℕ} (tasks : Tasks n) (i : Fin tasks.length)
    (state : Bits (gridWidth G tasks)) : Bits (blockWidth G (tasks.get i)) :=
  fun j => state (gridWire G tasks i j)

def coreGridRead (G : MFamily) {n : ℕ} (tasks : Tasks n)
    (state : Bits (n + (batchAnc G tasks + 1))) : Bits (gridWidth G tasks) :=
  rightRegister (leftRegister (fun j => state (Fin.cast (coreWidth_eq G tasks) j)))

theorem coreGridRead_blockWire (G : MFamily) {n : ℕ} (tasks : Tasks n)
    (state : Bits (n + (batchAnc G tasks + 1))) (i : Fin tasks.length)
    (j : Fin (blockWidth G (tasks.get i))) :
    gridBlockRead G tasks i (coreGridRead G tasks state) j = state (blockWire G tasks i j) := rfl

theorem core_grid_event (G : MFamily) (word : Str) (tasks : Tasks word.length)
    (event : Bits (gridWidth G tasks) → Prop) :
    (∑ state : Bits (word.length + (batchAnc G tasks + 1)),
      if event (coreGridRead G tasks state) then
        ‖runLayered (coreCircuit G tasks) (basisInput (a := batchAnc G tasks) (toBits word)) state‖^2
        else 0) =
    (∑ state : Bits (gridWidth G tasks), if event state then
      ‖runLayered (gridCircuit G tasks) (computationalBasis (gridBits G (toBits word) tasks)) state‖^2
      else 0) := by
  rw [coreCircuit_tensor, castState_event]
  simp only [coreGridRead, Fin.cast_eq_self]
  rw [tensorState_left_event _ _ (fun state => event (rightRegister state)),
    tensorState_right_event _ _ event]
  · exact computationalBasis_unit _
  · exact computationalBasis_unit _

private theorem apply_castState {n m : ℕ} (h : n = m)
    (ψ : QState n) (state : Bits m) :
    castState h ψ state = ψ (fun i => state (Fin.cast h i)) := by
  cases h
  rfl

theorem core_preserves (G : MFamily) (word : Str) (tasks : Tasks word.length)
    (state : Bits (word.length + (batchAnc G tasks + 1)))
    (hs : runLayered (coreCircuit G tasks)
      (basisInput (a := batchAnc G tasks) (toBits word)) state ≠ 0) :
    (∀ i, state (inputWire G tasks i) = toBits word i) ∧
      ∀ b, state (constantWire G tasks b) = b := by
  let r := fun j => state (Fin.cast (coreWidth_eq G tasks) j)
  rw [coreCircuit_tensor, apply_castState] at hs
  change tensorState _ _ r ≠ 0 at hs
  have hleft : (computationalBasis (toBits word)) (leftRegister (leftRegister r)) ≠ 0 := by
    intro h
    exact hs (by simp only [tensorState, h, zero_mul])
  have hright : (computationalBasis reserveBits) (rightRegister r) ≠ 0 := by
    intro h
    exact hs (by simp only [tensorState, h, mul_zero])
  have hin : leftRegister (leftRegister r) = toBits word := by
    by_contra h
    exact hleft (by simp [computationalBasis,h])
  have hreserve : rightRegister r = reserveBits := by
    by_contra h
    exact hright (by simp [computationalBasis,h])
  constructor
  · intro i
    have he : inputWire G tasks i =
        Fin.cast (coreWidth_eq G tasks) (Fin.castAdd 2 (Fin.castAdd (gridWidth G tasks) i)) := by
      apply Fin.ext
      rfl
    rw [he]
    exact congrFun hin i
  · intro b
    have h := congrFun hreserve (if b then 0 else 1 : Fin 2)
    change state (constantWire G tasks b) = _ at h
    cases b <;> simpa [reserveBits] using h

end

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule89

/- Helper module JointCircuit. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.StaticBatch

open QAlgorithms.Complexity Integration9_9.LoadedBatch

noncomputable section

/-- Assemble an entire physical basis assignment from the separate block outcomes. -/
def assembleGrid (H : MFamily) {n : ℕ} : (tasks : Tasks n) →
    ((i : Fin tasks.length) → Bits (blockWidth H (tasks.get i))) → Bits (gridWidth H tasks)
  | [], _ => fun i => Fin.elim0 i
  | _t :: ts, ys => Fin.append (ys 0) (assembleGrid H ts (fun i => ys i.succ))

private theorem read_assembled (H : MFamily) {n : ℕ} (tasks : Tasks n)
    (ys : (i : Fin tasks.length) → Bits (blockWidth H (tasks.get i))) :
    (fun i => gridBlockRead H tasks i (assembleGrid H tasks ys)) = ys := by
  induction tasks with
  | nil => exact funext fun i => Fin.elim0 i
  | cons t ts ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · funext j
      exact Fin.append_left _ _ j
    · have h := congrFun (ih (fun j => ys j.succ)) j
      funext k
      change Fin.append (ys 0) (assembleGrid H ts (fun i => ys i.succ))
        (Fin.natAdd (blockWidth H t) (gridWire H ts j k)) = _
      exact (Fin.append_right (show Bits (blockWidth H t) from ys 0)
        (assembleGrid H ts (fun i => ys i.succ)) (gridWire H ts j k)).trans (congrFun h k)

private theorem assemble_read (H : MFamily) {n : ℕ} (tasks : Tasks n)
    (s : Bits (gridWidth H tasks)) :
    assembleGrid H tasks (fun i => gridBlockRead H tasks i s) = s := by
  induction tasks with
  | nil => exact funext fun i => Fin.elim0 i
  | cons t ts ih =>
    change Fin.append (leftRegister s)
      (assembleGrid H ts (fun i => gridBlockRead H ts i (rightRegister s))) = s
    rw [ih]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left (leftRegister s) (rightRegister s) j
    · exact Fin.append_right (leftRegister s) (rightRegister s) j

def gridOutcomes (H : MFamily) {n : ℕ} (tasks : Tasks n) :
    Bits (gridWidth H tasks) ≃ ((i : Fin tasks.length) → Bits (blockWidth H (tasks.get i))) where
  toFun s i := gridBlockRead H tasks i s
  invFun := assembleGrid H tasks
  left_inv := assemble_read H tasks
  right_inv := read_assembled H tasks

theorem grid_joint_weight (H : MFamily) {n : ℕ} (bits : Bits n) (tasks : Tasks n)
    (s : Bits (gridWidth H tasks)) :
    ‖runLayered (gridCircuit H tasks) (computationalBasis (gridBits H bits tasks)) s‖^2 =
      ∏ i : Fin tasks.length, ‖runLayered (H.circ (tasks.get i).length)
        (basisInput (queryBits bits (tasks.get i))) (gridBlockRead H tasks i s)‖^2 := by
  induction tasks with
  | nil =>
    have he : s = gridBits H bits [] := funext fun i => Fin.elim0 i
    subst s
    simp [gridCircuit,runLayered,computationalBasis]
  | cons t ts ih =>
    change ‖runLayered (leftCircuit (show Layered (blockWidth H t) from H.circ t.length) ++
        rightCircuit (gridCircuit H ts)) (computationalBasis (Fin.append
          (Fin.append (queryBits bits t) (fun _ => false)) (gridBits H bits ts))) s‖^2 = _
    rw [computationalBasis_tensor,disjointCircuits_tensor,← basisInput_eq_computationalBasis]
    change ‖runLayered (H.circ t.length) (basisInput (queryBits bits t)) (leftRegister s) *
      runLayered (gridCircuit H ts) (computationalBasis (gridBits H bits ts)) (rightRegister s)‖^2 = _
    rw [norm_mul,mul_pow,ih (rightRegister s)]
    exact (Fin.prod_univ_succ (n := ts.length) (fun i : Fin (ts.length+1) =>
      ‖runLayered (H.circ ((t::ts).get i).length) (basisInput (queryBits bits ((t::ts).get i)))
        (gridBlockRead H (t::ts) i s)‖^2)).symm

/-- The physical core realizes the joint distribution of every block's full
basis record, against an arbitrary event depending on all those records. -/
theorem core_joint_event (H : MFamily) (input : Str) (tasks : Tasks input.length)
    (event : ((i : Fin tasks.length) → Bits (blockWidth H (tasks.get i))) → Prop) :
    (∑ s : Bits (input.length + (batchAnc H tasks + 1)),
      if event (fun i => gridBlockRead H tasks i (coreGridRead H tasks s)) then
        ‖runLayered (coreCircuit H tasks) (basisInput (a := batchAnc H tasks) (toBits input)) s‖^2
      else 0) =
    ∑ ys : (i : Fin tasks.length) → Bits (blockWidth H (tasks.get i)),
      if event ys then ∏ i : Fin tasks.length, ‖runLayered (H.circ (tasks.get i).length)
        (basisInput (queryBits (toBits input) (tasks.get i))) (ys i)‖^2 else 0 := by
  rw [core_grid_event H input tasks (fun s => event (fun i => gridBlockRead H tasks i s))]
  simp_rw [grid_joint_weight]
  exact (gridOutcomes H tasks).sum_comp (fun ys => if event ys then
    ∏ i : Fin tasks.length, ‖runLayered (H.circ (tasks.get i).length)
      (basisInput (queryBits (toBits input) (tasks.get i))) (ys i)‖^2 else 0)

end

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule90

/- Helper module Transport. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option maxHeartbeats 800000

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase.StaticBatch

open scoped BigOperators

noncomputable section

private def width (G : MFamily) (n : ℕ) := n + (G.anc n + 1)

private def bitEquiv (G : MFamily) {a b : ℕ} (h : a=b) :
    Bits (width G a) ≃ Bits (width G b) := Equiv.cast (congrArg (fun n => Bits (width G n)) h)

private theorem oldWords (G : MFamily) {a b : ℕ} (h : a=b) (s : Bits (width G a)) :
    (List.ofFn fun j => s (G.outW a j)) =
      List.ofFn fun j => (bitEquiv G h s) (G.outW b j) := by cases h; rfl

private theorem oldMass (G : MFamily) {a b : ℕ} (h : a=b) (x : Bits a) (y : Bits b)
    (xy : ∀ j, x j = y (Fin.cast h j)) (s : Bits (width G a)) :
    ‖runLayered (G.circ a) (basisInput x) s‖^2 =
      ‖runLayered (G.circ b) (basisInput y) (bitEquiv G h s)‖^2 := by
  cases h
  have he : x=y := funext xy
  subst y
  rfl

def outEquiv (G : MFamily) {n : ℕ} (u : Bits n) (t : List (StaticLoadSlot n)) {r : Str}
    (hr : queryWord u t=r) : Bits (blockWidth G t) ≃ Bits (r.length+(G.anc r.length+1)) :=
  bitEquiv G ((queryWord_length u t).symm.trans (congrArg List.length hr))

theorem outEquiv_words (G : MFamily) {n : ℕ} (u : Bits n) (t : List (StaticLoadSlot n)) {r : Str}
    (hr : queryWord u t=r) (s : Bits (blockWidth G t)) :
    (List.ofFn fun j => s (G.outW t.length j)) =
      List.ofFn fun j => (outEquiv G u t hr s) (G.outW r.length j) :=
  oldWords G _ _

theorem outEquiv_mass (G : MFamily) {n : ℕ} (u : Bits n) (t : List (StaticLoadSlot n)) {r : Str}
    (hr : queryWord u t=r) (s : Bits (blockWidth G t)) :
    ‖runLayered (G.circ t.length) (basisInput (queryBits u t)) s‖^2 =
      ‖runLayered (G.circ r.length) (basisInput (toBits r)) (outEquiv G u t hr s)‖^2 := by
  apply oldMass
  subst r
  intro j
  simp [queryWord,toBits,Fin.cast]

theorem sum_transport {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : ι → Type*} [∀ i, Fintype (X i)]
    [∀ i, Fintype (Y i)] (e : ∀ i, X i ≃ Y i) (f : ((i : ι) → Y i) → ℝ) :
    (∑ x : (i : ι) → X i, f (fun i => e i (x i))) = ∑ y, f y :=
  (Equiv.piCongrRight e).sum_comp f

end

end MultiPre

end P2MDyadicModule91

/- Helper module GridMarginal. -/
section P2MDyadicModule92

set_option autoImplicit false

open scoped BigOperators Classical

namespace ParityGrid

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

variable {X : J → Type*} [(j : J) → Fintype (X j)]

private def compatible (f : I ↪ J) (ys : (i:I) → X (f i)) (j:J) (b:X j) : Prop :=
  ∀ (i:I) (e : f i = j), (e ▸ ys i) = b

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [(j : J) → Fintype (X j)] in
private theorem compatible_at (f : I ↪ J) (ys : (i:I) → X (f i)) (i:I) (b : X (f i)) :
    compatible f ys (f i) b ↔ ys i = b := by
  constructor
  · intro h
    exact h i rfl
  · intro h l he
    have hl : l = i := f.injective he
    subst l
    exact h

omit [DecidableEq I] in
private theorem fiber (f : I ↪ J) (W : (j:J) → X j → ℝ)
    (hW : ∀j, ∑ x, W j x = 1) (ys : (i:I) → X (f i)) :
    (∑ xs : ((j:J) → X j), if (fun i => xs (f i)) = ys then ∏ j, W j (xs j) else 0) =
      ∏ i, W (f i) (ys i) := by
  classical
  let F (j:J) (x:X j) := if compatible f ys j x then W j x else 0
  have fact (xs : (j:J) → X j) :
      (if (fun i => xs (f i)) = ys then ∏ j, W j (xs j) else 0) = ∏ j, F j (xs j) := by
    by_cases he : (fun i => xs (f i)) = ys
    · rw [if_pos he]
      apply Finset.prod_congr rfl
      intro j _
      have hc : compatible f ys j (xs j) := by
        intro i hij
        subst j
        exact (congrFun he i).symm
      simp [F,hc]
    · rw [if_neg he]
      have hn : ∃ i, xs (f i) ≠ ys i := by
        by_contra! hn
        exact he (funext hn)
      obtain ⟨i, hi⟩ := hn
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (f i))
      simp [F,compatible_at,Ne.symm hi]
  simp_rw [fact]
  rw [← Fintype.prod_sum]
  have onImage (i:I) : ∑ b, F (f i) b = W (f i) (ys i) := by
    simp [F,compatible_at]
  have hsub : ((Finset.univ : Finset I).map f) ⊆ Finset.univ := Finset.subset_univ _
  calc
    _ = ∏ j ∈ (Finset.univ.map f), ∑ b, F j b := by
      symm
      apply Finset.prod_subset hsub
      intro j _ hj
      have hn : ∀ i, f i ≠ j := by simpa using hj
      have hc (b : X j) : compatible f ys j b := by
        intro i hi
        exact (hn i hi).elim
      simpa [F,hc] using hW j
    _ = _ := by simp [Finset.prod_map,onImage]

theorem restrict_expectation (f : I ↪ J) (W : (j:J) → X j → ℝ)
    (hW : ∀j, ∑ x, W j x = 1) (test : ((i:I) → X (f i)) → ℝ) :
    (∑ xs : ((j:J) → X j), (∏ j, W j (xs j)) * test (fun i => xs (f i))) =
      ∑ ys : ((i:I) → X (f i)), (∏ i, W (f i) (ys i)) * test ys := by
  classical
  calc
    _ = ∑ xs : ((j:J) → X j), ∑ ys : ((i:I) → X (f i)),
          (if (fun i => xs (f i)) = ys then ∏ j, W j (xs j) else 0) * test ys := by
      apply Finset.sum_congr rfl
      intro xs _
      simp [ite_mul]
    _ = ∑ ys : ((i:I) → X (f i)),
          (∑ xs : ((j:J) → X j), if (fun i => xs (f i)) = ys then ∏ j, W j (xs j) else 0) * test ys := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp_rw [fiber f W hW]

theorem restrict_event (f : I ↪ J) (W : (j:J) → X j → ℝ)
    (hW : ∀j, ∑ x, W j x = 1) (event : ((i:I) → X (f i)) → Prop) [DecidablePred event] :
    (∑ xs : ((j:J) → X j), if event (fun i => xs (f i)) then ∏ j, W j (xs j) else 0) =
      ∑ ys : ((i:I) → X (f i)), if event ys then ∏ i, W (f i) (ys i) else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using
    restrict_expectation f W hW (fun ys => if event ys then 1 else 0)

end ParityGrid

end P2MDyadicModule92

/- Helper module StaticBatchResources. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.StaticBatch

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

/-- A polynomial bound for both quantum resources of the emitted core,
given polynomial bounds on the number and individual sizes of requests. -/
theorem core_resources (G : MFamily) (hG : IsMQPT G) (tasks : (n : ℕ) → Tasks n)
    (count width : Polynomial ℕ)
    (hcount : ∀ n, (tasks n).length ≤ count.eval n)
    (hwidth : ∀ n task, task ∈ tasks n → task.length ≤ width.eval n) :
    ∃ p : Polynomial ℕ, (∀ n, depth (coreCircuit G (tasks n)) ≤ p.eval n) ∧
      (∀ n, batchAnc G (tasks n) ≤ p.eval n) := by
  obtain ⟨q, hq⟩ := hG.2.2
  let queryAnc : Polynomial ℕ := q.comp width
  let gridAnc : Polynomial ℕ := count * (width + queryAnc + 1)
  let gridDepth : Polynomial ℕ := count * queryAnc
  let p : Polynomial ℕ := 74 * (gridAnc + 1) + gridDepth + (gridAnc + 1)
  have hanc (n : ℕ) : gridWidth G (tasks n) ≤ gridAnc.eval n := by
    have hlocal (task : List (StaticLoadSlot n)) (htask : task ∈ tasks n) :
        blockWidth G task ≤ (width + queryAnc + 1).eval n := by
      have hlen := hwidth n task htask
      have ha := (hq task.length).2.1.trans (polynomial_eval_mono q hlen)
      unfold blockWidth queryAnc
      simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
      omega
    apply (gridWidth_bound G (tasks n) _ hlocal).trans
    simpa only [gridAnc, Polynomial.eval_mul] using
      Nat.mul_le_mul_right ((width + queryAnc + 1).eval n) (hcount n)
  have hdep (n : ℕ) : depth (gridCircuit G (tasks n)) ≤ gridDepth.eval n := by
    have hlocal (task : List (StaticLoadSlot n)) (htask : task ∈ tasks n) :
        depth (G.circ task.length) ≤ queryAnc.eval n := by
      have hlen := hwidth n task htask
      simpa only [queryAnc, Polynomial.eval_comp] using
        (hq task.length).1.trans (polynomial_eval_mono q hlen)
    apply (gridCircuit_depth_bound G (tasks n) _ hlocal).trans
    simpa only [gridDepth, Polynomial.eval_mul] using
      Nat.mul_le_mul_right (queryAnc.eval n) (hcount n)
  refine ⟨p, ?_, ?_⟩
  · intro n
    have h := coreCircuit_depth_bound G (tasks n)
    have ha := hanc n
    have hd := hdep n
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
    omega
  · intro n
    have ha := hanc n
    simp only [batchAnc, p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
    omega

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule93

/- Helper module StaticReadoutBounds. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.StaticBatch

open scoped BigOperators Classical

private theorem encB_len_le (n : ℕ) : (encB n).length ≤ 2 * n + 1 := by
  have hbits (xs : List Bool) : (xs.flatMap (fun b => [true,b])).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons b xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  have hsize := (Nat.size_le).mpr n.lt_two_pow_self
  simp only [encB, List.length_append, List.length_cons, List.length_nil, hbits, Nat.size_eq_bits_len]
  omega

private theorem frameWord_length_le (constants' : ℕ × ℕ) (refs : List ℕ) :
    (frameWord (constants',refs)).length ≤ 3 * refs.length + 1 := by
  have h := encB_len_le refs.length
  simp only [frameWord, constants,List.length_append,List.length_map]
  omega

private theorem framedBlocks_length_le (constants' : ℕ × ℕ) (refs : List (List ℕ)) (b : ℕ)
    (h : ∀ row ∈ refs, row.length ≤ b) :
    (refs.flatMap (fun row => frameWord (constants',row))).length ≤ refs.length * (3 * b + 1) := by
  induction refs with
  | nil => simp
  | cons head rest ih =>
    have hhead := frameWord_length_le constants' head
    have hb := h head List.mem_cons_self
    have hrest := ih (fun row hr => h row (List.mem_cons_of_mem head hr))
    rw [List.flatMap_cons, List.length_cons, List.length_append]
    calc
      _ ≤ (3 * b + 1) + rest.length * (3 * b + 1) :=
        Nat.add_le_add (by omega) hrest
      _ = _ := by ring

theorem readout_length_le (G : MFamily) {n : ℕ} (tasks : Tasks n) (b : ℕ)
    (h : ∀ task ∈ tasks, G.outLen task.length ≤ b) :
    (readoutRefs (typedLayout G tasks)).length ≤ 3 * n + 2 + tasks.length * (3 * b + 3) := by
  let layout := typedLayout G tasks
  let constants' := ((bodySlots layout).length + 1, (bodySlots layout).length)
  have hlen : (blocksRefs layout).length = tasks.length := by simp [blocksRefs, layout, typedLayout]
  have hin : (basisRefs layout).length = n := by simp [basisRefs, layout, typedLayout]
  have hb (row : List ℕ) (hr : row ∈ blocksRefs layout) : row.length ≤ b := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    have hi' : i < tasks.length := by simpa only [layout,typedLayout,List.length_map] using List.mem_range.mp hi
    simp only [blockRefs, layout, typedLayout, List.getElem?_map, List.getElem?_eq_getElem hi',
      Option.map_some, Option.getD_some, List.length_map, typedFrame, List.length_ofFn]
    exact h _ (List.getElem_mem hi')
  have hbody := framedBlocks_length_le constants' (blocksRefs layout) b hb
  have hbasis := frameWord_length_le constants' (basisRefs layout)
  have hp := encB_len_le tasks.length
  change (fullFrame (constants', (basisRefs layout, blocksRefs layout))).length ≤ _
  simp only [fullFrame, frameWords, List.length_append, constants, List.length_map, hlen]
  simp only [hlen] at hbody
  simp only [hin] at hbasis
  simp only [Nat.mul_add, Nat.mul_one] at hbody ⊢
  omega

end Integration9_9.DyadicReadout

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.StaticBatch

open scoped BigOperators Classical

end Integration9_9.DyadicReadout

namespace Integration9_9.DyadicReadout

open QAlgorithms.Complexity

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.StaticBatch

open OAI.MetricKMedian.Binary

theorem batchReadout_isMQPT (G : MFamily) (hG : IsMQPT G)
    (tasks : ∀ n, Tasks n) (count width : Polynomial ℕ)
    (hcount : ∀ n, (tasks n).length ≤ count.eval n)
    (hwidth : ∀ n task, task ∈ tasks n → task.length ≤ width.eval n)
    (hgen : ∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ n, f (unary n) = (batchReadoutFamily G tasks).encAt n) :
    IsMQPT (batchReadoutFamily G tasks) := by
  refine ⟨hgen, fun n => coreCircuit_wellFormed G hG.2.1 (tasks n), ?_⟩
  obtain ⟨p, hdepth, hanc⟩ := core_resources G hG tasks count width hcount hwidth
  obtain ⟨q, hq⟩ := hG.2.2
  let outCap : Polynomial ℕ := 3 * Polynomial.X + 2 + count * (3 * q.comp width + 3)
  refine ⟨p + outCap, fun n => ⟨?_,?_,?_⟩⟩
  · exact (hdepth n).trans (by simp only [Polynomial.eval_add]; omega)
  · exact (hanc n).trans (by simp only [Polynomial.eval_add]; omega)
  · have hlocal (task : List (StaticLoadSlot n)) (ht : task ∈ tasks n) :
        G.outLen task.length ≤ q.eval (width.eval n) :=
      (hq task.length).2.2.trans (polynomial_eval_mono q (hwidth n task ht))
    calc
      _ ≤ 3 * n + 2 + (tasks n).length * (3 * q.eval (width.eval n) + 3) :=
        readout_length_le G (tasks n) _ hlocal
      _ ≤ 3 * n + 2 + count.eval n * (3 * q.eval (width.eval n) + 3) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (hcount n)) _
      _ = outCap.eval n := by simp [outCap]
      _ ≤ _ := by simp only [Polynomial.eval_add]; omega

end Integration9_9.DyadicReadout

end P2MDyadicModule94

/- Helper module Slice. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option maxHeartbeats 2200000

set_option backward.isDefEq.respectTransparency false

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.StaticBatch Integration9_9 Integration9_9.DyadicReadout

open Integration9_9.TM2PlatformSerialization Integration9_9.LARCoinLayout

open Integration9_9.LoadedBatch.PostComposition (multi_encoding)

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QMCNumericRuntime

def copies (n : ℕ) : List (StaticLoadSlot n) := List.ofFn fun j : Fin n => Sum.inr j

def window (n start len : ℕ) : List (StaticLoadSlot n) := ((copies n).drop start).take len

def gridTasks (n : ℕ) : Tasks n :=
  List.ofFn fun k : Fin ((n+1)*(n+1)) => window n (k.val / (n+1)) (k.val % (n+1))

def pairIndices (word : Str) : List ℕ :=
  List.range (((false::word).flatMap (fun _ => (false::word))).length)

@[fun_prop] theorem pairIndices_poly : Poly pairIndices := by
  unfold pairIndices
  apply Poly.comp (f := fun l : Str => List.range l.length) Poly.list_indices
  fun_prop

theorem pairIndices_eq (word : Str) : pairIndices word = List.range ((word.length+1)*(word.length+1)) := by
  simp [pairIndices,List.length_flatMap]
  congr 1
  ring

@[fun_prop] private theorem quotient_poly : Poly (fun x : ℕ × ℕ => x.1/x.2) := ⟨PolyProgram.natDiv⟩

@[fun_prop] private theorem remainder_poly : Poly (fun x : ℕ × ℕ => x.1%x.2) := ⟨PolyProgram.natMod⟩

def sourceWindow (x : Str × ℕ) : Sources :=
  (((List.range x.1.length).drop (x.2 / (x.1.length+1))).take (x.2 % (x.1.length+1))).map
    fun a => (true,a)

@[fun_prop] theorem sourceWindow_poly : Poly sourceWindow := by
  unfold sourceWindow
  have hr : Poly (fun w : Str => List.range w.length) := Poly.list_indices
  have hq : Poly (fun x : Str × ℕ => x.2 / (x.1.length+1)) :=
    Poly.comp quotient_poly (Poly.pair Poly.snd (by fun_prop))
  have hmod : Poly (fun x : Str × ℕ => x.2 % (x.1.length+1)) :=
    Poly.comp remainder_poly (Poly.pair Poly.snd (by fun_prop))
  have hd : Poly (fun x : Str × ℕ => (List.range x.1.length).drop (x.2 / (x.1.length+1))) :=
    Poly.comp (f := fun p : List ℕ × ℕ => p.1.drop p.2)
      (g := fun x : Str × ℕ => (List.range x.1.length, x.2 / (x.1.length+1))) parser_drop_poly (Poly.pair (Poly.comp (f := fun w : Str => List.range w.length) (g := fun x : Str × ℕ => x.1) hr Poly.fst) hq)
  have htake : Poly (fun x : Str × ℕ => ((List.range x.1.length).drop (x.2 / (x.1.length+1))).take (x.2 % (x.1.length+1))) :=
    Poly.comp (f := fun p : List ℕ × ℕ => p.1.take p.2)
      (g := fun x : Str × ℕ => ((List.range x.1.length).drop (x.2 / (x.1.length+1)), x.2 % (x.1.length+1))) parser_take_poly (Poly.pair hd hmod)
  exact Poly.list_map (f := fun (_ : Str × ℕ) (a : ℕ) => (true,a)) (by fun_prop) htake

def allSources (w : Str) : List Sources := (pairIndices w).map fun i => sourceWindow (w,i)

@[fun_prop] theorem allSources_poly : Poly allSources := by unfold allSources; fun_prop

theorem allSources_eq (n : ℕ) : allSources (unary n) = (gridTasks n).map (List.map DyadicSchedule.slotSource) := by
  have hr : (List.range n).map (fun i => (true,i)) =
      List.ofFn (fun i : Fin n => (true,i.val)) := by
    apply List.ext_getElem <;> simp
  rw [allSources,pairIndices_eq]
  apply List.ext_getElem
  · simp [gridTasks,unary]; ring
  · intro j hj hk
    simp only [gridTasks,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      sourceWindow,window,copies,unary,List.length_replicate,
      List.map_take,List.map_drop,List.map_ofFn,Function.comp_def,DyadicSchedule.slotSource]
    rw [hr]

def requestedSizes (w : Str) : List Str := (allSources w).map fun s => s.map (fun _ => true)

@[fun_prop] theorem requestedSizes_poly : Poly requestedSizes := by unfold requestedSizes; fun_prop

theorem requestedSizes_unary (w r : Str) (hr : r ∈ requestedSizes w) : r = unary r.length := by
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp hr
  simp [unary,List.map_const']

theorem requests_eq (n : ℕ) : requestedSizes (unary n) = (gridTasks n).map (fun t => unary t.length) := by
  rw [requestedSizes, allSources_eq]
  simp [List.map_map,Function.comp_def,List.map_const',unary]

def frameBuilder (x : Str × List (Str × Str)) : Str :=
  let frames := samplerFrames x.2
  let anc := ancillaSlots frames
  let prepared := loadLayers (x.1, (anc, loadAll (allSources x.1, x.2)))
  let samples := samplerLayers (x.1, frames)
  lengthToken anc ++ serializeWords (outputWireWords (encodedLayout (x.1, frames))) ++
    serializeWords ((prepared ++ samples).map serializeWords)

@[fun_prop] theorem frameBuilder_poly : Poly frameBuilder := by
  unfold frameBuilder
  fun_prop

theorem frameBuilder_correct (G : MFamily) (n : ℕ) :
    frameBuilder (unary n, samplerDescriptions G ((gridTasks n).map List.length)) =
      (batchReadoutFamily G gridTasks).encAt n := by
  let ts := gridTasks n
  let ds := samplerDescriptions G (ts.map List.length)
  have hanc : ancillaSlots (samplerFrames ds) = List.replicate (batchAnc G ts) () :=
    ancillaSlots_correct G ts
  have hsrc : loadAll (allSources (unary n), ds) = (coreSlots G ts).map loadSource := by
    rw [allSources_eq]
    exact loadAll_correct G ts
  have hgate : loadLayers (unary n, (ancillaSlots (samplerFrames ds), loadAll (allSources (unary n), ds))) ++
      samplerLayers (unary n, samplerFrames ds) = (coreCircuit G ts).map (List.map encInstr) := by
    rw [hanc, hsrc, loadLayers_correct (coreSlots G ts) (by simp [batchAnc])]
    rw [show samplerLayers (unary n, samplerFrames ds) =
      (castBodyCircuit (coreWidth_eq G ts)
        (leftCircuit (m := 2) (rightCircuit (n := n) (gridCircuit G ts)))).map
          (List.map encInstr) from samplerLayers_correct G ts]
    exact (List.map_append ..).symm
  have hlayout : encodedLayout (unary n, samplerFrames ds) = typedLayout G ts := by
    simpa only [ds, samplerFrames, samplerDescriptions, List.map_map, Function.comp_def] using
      encodedLayout_correct G ts
  have henc {width : ℕ} (circuit : Layered width) :
      serializeWords ((circuit.map (List.map encInstr)).map serializeWords) = encCirc circuit := by
    simp only [encCirc, List.map_map, Function.comp_def, serializeWords_eq]
    rfl
  calc
    _ = encNat (batchAnc G ts) ++ encStr (outputWireWords (typedLayout G ts)) ++ encCirc (coreCircuit G ts) := by
      change frameBuilder (unary n, ds) = _
      dsimp only [frameBuilder]
      rw [hgate, henc, hlayout, hanc]
      simp only [lengthToken_eq, List.length_replicate, serializeWords_eq]
    _ = _ := by
      rw [multi_encoding]
      simp only [List.map_map, Function.comp_def]
      rw [batchReadout_encodedWires]
      rfl

theorem grid_uniform (G : MFamily) (hG : IsMQPT G) :
    ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n, f (unary n) = (batchReadoutFamily G gridTasks).encAt n := by
  refine ⟨fun w => frameBuilder (w,(requestedSizes w).map fun r => (r,G.encAt r.length)),
    batchBuilder_polyTime G hG _ requestedSizes_poly requestedSizes_unary _ frameBuilder_poly, ?_⟩
  intro n
  dsimp only
  rw [requests_eq]
  simpa only [samplerDescriptions,List.map_map,Function.comp_def,unary,List.length_replicate] using frameBuilder_correct G n

theorem grid_qpt (G : MFamily) (hG : IsMQPT G) : IsMQPT (batchReadoutFamily G gridTasks) := by
  apply batchReadout_isMQPT G hG gridTasks ((Polynomial.X+1)^2) Polynomial.X
  · intro n
    simp [gridTasks,pow_two]
    nlinarith
  · intro n task ht
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
    simp [window,copies]
  · exact grid_uniform G hG

end EncodedBatch

end P2MDyadicModule95

/- Helper module Layout. -/
section P2MDyadicModule96

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open InfoLossLAR.WorstCase.StaticBatch Integration9_9 Integration9_9.DyadicReadout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding QMCNumericRuntime

def pack (w : Str) (rs : List Str) : Str := encS w ++ encL encS rs

@[fun_prop] theorem pack_poly : Poly (fun p : Str × List Str => pack p.1 p.2) := by
  unfold pack encL
  have h : Poly (fun p : Str × List Str => p.2.flatMap encS) := Poly.list_flatMap (Poly.comp encS_poly Poly.snd) Poly.snd
  fun_prop

def base (w : Str) (rs : List Str) : ℕ := (encS w).length + (encB rs.length).length

def startAt (w : Str) (rs : List Str) (i : ℕ) : ℕ :=
  base w rs + ((rs.take i).flatMap encS).length + (encB (rs[i]?.getD []).length).length

@[fun_prop] theorem startAt_poly : Poly (fun p : (Str × List Str) × ℕ => startAt p.1.1 p.1.2 p.2) := by
  have ht : Poly (fun p : (Str × List Str) × ℕ => p.1.2.take p.2) :=
    Poly.comp (f := fun p : List Str × ℕ => p.1.take p.2) (g := fun p : (Str × List Str) × ℕ => (p.1.2, p.2)) parser_take_poly (by fun_prop)
  have hm : Poly (fun p : (Str × List Str) × ℕ => (p.1.2.take p.2).flatMap encS) :=
    Poly.list_flatMap (Poly.comp encS_poly Poly.snd) ht
  unfold startAt base
  fun_prop

private theorem split_word (w : Str) (rs : List Str) (i : Fin rs.length) (tail : Str) :
    pack w rs ++ tail =
    (encS w ++ encB rs.length ++ (rs.take i.val).flatMap encS ++ encB (rs.get i).length) ++
    rs.get i ++ ((rs.drop (i.val+1)).flatMap encS ++ tail) := by
  have split : rs = rs.take i.val ++ [rs.get i] ++ rs.drop (i.val+1) := by
    rw [List.get_eq_getElem,List.append_assoc,List.singleton_append,←List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
  unfold pack encL
  conv_lhs => arg 1; arg 2; arg 2; rw [split]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,encS]

theorem startAt_end (w : Str) (rs : List Str) (i : Fin rs.length) (tail : Str) :
    startAt w rs i + (rs.get i).length ≤ (pack w rs ++ tail).length := by
  rw [split_word w rs i tail]
  simp [startAt,base,List.length_append]
  omega

theorem startAt_slice (w : Str) (rs : List Str) (i : Fin rs.length) (tail : Str) :
    ((pack w rs ++ tail).drop (startAt w rs i)).take (rs.get i).length = rs.get i := by
  let pre := encS w ++ encB rs.length ++ (rs.take i.val).flatMap encS ++ encB (rs.get i).length
  have hlen : startAt w rs i = pre.length := by simp [pre,startAt,base,Nat.add_assoc]
  rw [split_word w rs i tail, hlen]
  change ((pre ++ rs.get i ++ _).drop pre.length).take _ = _
  rw [List.append_assoc, List.drop_left, List.take_left]

theorem startAt_strict (w : Str) (rs : List Str) {i j : Fin rs.length} (h : i < j) :
    startAt w rs i < startAt w rs j := by
  have incl : (rs.take (i.val+1)).flatMap encS <+: (rs.take j.val).flatMap encS := by
    have hpre : rs.take (i.val+1) <+: rs.take j.val := List.take_prefix_take_left h
    obtain ⟨t,ht⟩ := hpre
    exact ⟨t.flatMap encS,by rw [←ht,List.flatMap_append]⟩
  have hl := incl.length_le
  rw [List.take_add_one (l := rs) (i := i.val)] at hl
  simp only [List.getElem?_eq_getElem i.isLt,Option.toList_some,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.length_append,List.append_nil] at hl
  have hp := encB_length_pos rs[j.val].length
  simp only [startAt,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,Option.getD_some]
  simp only [encS,List.length_append] at hl
  omega

def gridIndex (m s l : ℕ) : ℕ := s*(m+1)+l

def actualIndex (w : Str) (rs : List Str) (tail : Str) (i : Fin rs.length) :
    Fin (gridTasks (pack w rs ++ tail).length).length :=
  ⟨gridIndex (pack w rs ++ tail).length (startAt w rs i) (rs.get i).length, by
    have h := startAt_end w rs i tail
    have hs := Nat.mul_le_mul_right ((pack w rs ++ tail).length+1) (Nat.le_trans (Nat.le_add_right _ _) h)
    simp only [gridTasks,List.length_ofFn,gridIndex]
    rw [Nat.succ_mul]
    omega⟩

theorem actualIndex_start (w : Str) (rs : List Str) (tail : Str) (i : Fin rs.length) :
    (actualIndex w rs tail i).val / ((pack w rs ++ tail).length+1) = startAt w rs i := by
  have h := startAt_end w rs i tail
  simp only [actualIndex,gridIndex]
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_succ _), Nat.div_eq_of_lt (by omega),Nat.add_zero]

theorem actualIndex_injective (w : Str) (rs : List Str) (tail : Str) :
    Function.Injective (actualIndex w rs tail) := by
  intro i j e
  have hs := congrArg (fun k : Fin (gridTasks (pack w rs ++ tail).length).length =>
      k.val / ((pack w rs ++ tail).length+1)) e
  simp only [actualIndex_start] at hs
  rcases lt_trichotomy i j with less | eq | more
  · exact ((startAt_strict w rs less).ne hs).elim
  · exact eq
  · exact ((startAt_strict w rs more).ne hs.symm).elim

theorem grid_actual_task (w : Str) (rs : List Str) (tail : Str) (i : Fin rs.length) :
    (gridTasks (pack w rs ++ tail).length).get (actualIndex w rs tail i) =
      window (pack w rs ++ tail).length (startAt w rs i) (rs.get i).length := by
  have h := startAt_end w rs i tail
  have hlen : (rs.get i).length < (pack w rs ++ tail).length + 1 := by omega
  have hrem : (actualIndex w rs tail i).val % ((pack w rs ++ tail).length+1) = (rs.get i).length := by
    exact Nat.mul_add_mod_of_lt hlen
  simp only [gridTasks,List.get_eq_getElem,List.getElem_ofFn,actualIndex_start,hrem]

theorem query_window (u : Str) (s l : ℕ) :
    queryWord (toBits u) (window u.length s l) = (u.drop s).take l := by
  have hmap (x : Bits u.length) (t : List (StaticLoadSlot u.length)) :
      queryWord x t = t.map (slotValue x) := by
    apply List.ext_getElem
    · simp [queryWord]
    · intro i hi hj
      simp [queryWord, queryBits]
  rw [hmap, window,List.map_take,List.map_drop]
  have h : (copies u.length).map (slotValue (toBits u)) = u := by
    simpa only [copies,List.map_ofFn,Function.comp_def,slotValue,Sum.elim_inr,toBits] using List.ofFn_get u
  rw [h]

theorem query_actual (w : Str) (rs : List Str) (tail : Str) (i : Fin rs.length) :
    queryWord (toBits (pack w rs ++ tail)) ((gridTasks (pack w rs ++ tail).length).get (actualIndex w rs tail i)) =
      rs.get i := by
  rw [grid_actual_task,query_window,startAt_slice]

end EncodedBatch

end P2MDyadicModule96

/- Helper module Post. -/
section P2MDyadicModule97

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding

open ParityFlags (readStrings)

abbrev PostData := (Str × List Str) × ℕ × List Str

def takeWord (data : PostData × ℕ) : Str :=
  let x := data.1
  let i := data.2
  let len := (x.1.2[i]?.getD []).length
  let idx := gridIndex x.2.1 (startAt x.1.1 x.1.2 i) len
  x.2.2[idx]?.getD []

@[fun_prop] theorem takeWord_poly : Poly takeWord := by
  have hs : Poly (fun p : PostData × ℕ => startAt p.1.1.1 p.1.1.2 p.2) :=
    Poly.comp (f := fun q : (Str × List Str) × ℕ => startAt q.1.1 q.1.2 q.2)
      (g := fun p : PostData × ℕ => (p.1.1,p.2)) startAt_poly (by fun_prop)
  change Poly (fun data : PostData × ℕ =>
    data.1.2.2[startAt data.1.1.1 data.1.1.2 data.2 * (data.1.2.1+1) +
      (data.1.1.2[data.2]?.getD []).length]?.getD [])
  fun_prop

def chooseBlocks (x : PostData) : Str :=
  pack x.1.1 ((List.range x.1.2.length).map (fun i => takeWord (x,i)))

@[fun_prop] theorem chooseBlocks_poly : Poly chooseBlocks := by
  have h : Poly (fun x : PostData => List.range x.1.2.length) :=
    Poly.comp (f := fun xs : List Str => List.range xs.length) Poly.list_indices (by fun_prop)
  unfold chooseBlocks
  fun_prop

def post (input : Str) : Str :=
  let outer := readS input.reverse
  let u := outer.2
  let inner := readS u
  chooseBlocks ((inner.2,(readStrings inner.1).2), u.length, (readStrings outer.1).2)

@[fun_prop] theorem post_poly : Poly post := by unfold post; fun_prop

private theorem readStrings_append (xs : List Str) (rest : Str) :
    readStrings (encL encS xs ++ rest) = (rest,xs) := by
  have h := readBinaryList_append_mapped readS encS id
    (fun word => (encB_length_pos word.length).trans_le (by simp [encS]))
    readS_append xs rest
  simpa only [readStrings, List.map_id] using h

theorem post_correct (w : Str) (rs : List Str) (tail garbage : Str) (gridWords : List Str) :
    let u := pack w rs ++ tail
    post (u ++ (encS u ++ encL encS gridWords ++ garbage).reverse) =
      pack w (List.ofFn fun j : Fin rs.length => (gridWords[(actualIndex w rs tail j).val]?).getD []) := by
  dsimp only
  let u := pack w rs ++ tail
  have houter : readS ((u ++ (encS u ++ encL encS gridWords ++ garbage).reverse).reverse) =
      ((encL encS gridWords ++ garbage) ++ u.reverse,u) := by
    simp only [List.reverse_append,List.reverse_reverse,List.append_assoc,readS_append]
  have hinner : readS u = (encL encS rs ++ tail,w) := by
    simp only [u,pack,List.append_assoc,readS_append]
  change post (u ++ (encS u ++ encL encS gridWords ++ garbage).reverse) = _
  rw [post,houter]
  dsimp only
  rw [hinner]
  dsimp only
  rw [List.append_assoc,readStrings_append,readStrings_append]
  dsimp only [chooseBlocks]
  apply congrArg (pack w)
  apply List.ext_getElem
  · simp
  · intro k hk hh
    have h : k < rs.length := by simpa using hk
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,takeWord,actualIndex,
      List.getElem?_eq_getElem h,Option.getD_some, List.get_eq_getElem,u]

end EncodedBatch

end P2MDyadicModule97

/- Helper module GridLaw. -/
section P2MDyadicModule98

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase.StaticBatch Integration9_9.DyadicReadout

abbrev GridBits (G : MFamily) (u : Str) :=
  (j : Fin (gridTasks u.length).length) → Bits (blockWidth G ((gridTasks u.length).get j))

def allWords (G : MFamily) (u : Str) (xs : GridBits G u) : List Str :=
  List.ofFn fun j => List.ofFn fun k => xs j (G.outW ((gridTasks u.length).get j).length k)

noncomputable def blockMass (G : MFamily) (u : Str) (j : Fin (gridTasks u.length).length)
    (s : Bits (blockWidth G ((gridTasks u.length).get j))) : ℝ :=
  ‖runLayered (G.circ ((gridTasks u.length).get j).length)
    (basisInput (queryBits (toBits u) ((gridTasks u.length).get j))) s‖^2

theorem raw_law (G : MFamily) (u : Str) (event : Str → Prop) :
    outputProb (batchReadoutFamily G gridTasks) u event = ∑ xs : GridBits G u,
        if event (encS u ++ encL encS (allWords G u xs))
        then ∏ j, blockMass G u j (xs j) else 0 := by
  classical
  let tasks := gridTasks u.length
  refine Eq.trans ?_ (core_joint_event G u tasks (fun xs => event (encS u ++ encL encS (allWords G u xs))))
  unfold outputProb
  apply Finset.sum_congr rfl
  intro y _
  change (if event (List.ofFn (fun j => y (readoutWire G tasks j))) then
    ‖runLayered (coreCircuit G tasks) (basisInput (toBits u)) y‖^2 else 0) = _
  by_cases hz : runLayered (coreCircuit G tasks) (basisInput (toBits u)) y = 0
  · simp [hz]
  obtain ⟨hd,hc⟩ := core_preserves G u tasks y hz
  rw [batchReadout_word G tasks y (hc true) (hc false)]
  have hin : inputWord G tasks y = u := by
    unfold inputWord
    simp only [hd,toBits,List.ofFn_get]
  have hout : trialWords G tasks y = allWords G u (fun j => gridBlockRead G tasks j (coreGridRead G tasks y)) := by
    unfold trialWords allWords
    apply congrArg List.ofFn
    funext j
    apply congrArg List.ofFn
    funext k
    exact (coreGridRead_blockWire G tasks y j (G.outW (tasks.get j).length k)).symm
  simp only [hin,hout]
  rfl

theorem blockMass_sum (G : MFamily) (u : Str) (j : Fin (gridTasks u.length).length) :
    ∑ s, blockMass G u j s = 1 := by
  let task := (gridTasks u.length).get j
  have h := runLayered_mass (G.circ task.length)
    (basisInput (a := G.anc task.length) (queryBits (toBits u) task))
  have hb := h.trans (basisInput_mass (a := G.anc task.length) (queryBits (toBits u) task))
  simp only [Complex.normSq_eq_norm_sq] at hb
  exact hb

end EncodedBatch

end P2MDyadicModule98

/- Helper module Reverse. -/
section P2MDyadicModule99

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.TM2PlatformSerialization

open Integration9_9.LoadedBatch.PostComposition

open scoped BigOperators Classical

def revFamily (F : MFamily) : MFamily where
  anc := F.anc
  circ := F.circ
  outLen := F.outLen
  outW n i := F.outW n i.rev

theorem list_rev_fn {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i : Fin n => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp [List.getElem_reverse, Fin.rev]
    congr 2
    omega

def revDescription (x : Str × Str) : Str :=
  let anc := readUnary x.2
  let outs := readWireWords anc.2
  anc.1 ++ serializeWords outs.2.reverse ++ outs.1

@[fun_prop] theorem revDescription_poly : Poly revDescription := by
  unfold revDescription
  fun_prop

theorem revDescription_eq (F : MFamily) (n : ℕ) :
    revDescription (unary n,F.encAt n) = (revFamily F).encAt n := by
  simp only [revDescription,multi_encoding,List.append_assoc,readUnary_append,
    readWireWords_append,revFamily,list_rev_fn,List.map_reverse,serializeWords_eq]

theorem revFamily_qpt (F : MFamily) (hF : IsMQPT F) : IsMQPT (revFamily F) := by
  obtain ⟨⟨s,hs,he⟩,hw,hp⟩ := hF
  refine ⟨⟨fun w => revDescription (w,s w),
    generator_builder_polyTime _ hs _ revDescription_poly,?_⟩,hw,hp⟩
  intro n
  simpa only [he] using revDescription_eq F n

theorem revProb (F : MFamily) (w : Str) (event : Str → Prop) :
    outputProb (revFamily F) w event = outputProb F w (fun z => event z.reverse) := by
  classical
  unfold outputProb
  apply Finset.sum_congr rfl
  intro y _
  simp only [revFamily]
  rw [list_rev_fn (fun j => y (F.outW w.length j))]

end EncodedBatch

end P2MDyadicModule99

/- Helper module PostLaw. -/
section P2MDyadicModule100

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase.StaticBatch Integration9_9 Integration9_9.DyadicReadout

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable def picked {f : Str → Str} (P : PolyProgram id id f) (G : MFamily) : MFamily :=
  revFamily (LoadedBatch.PostComposition.family (revFamily (batchReadoutFamily G gridTasks)) P)

theorem picked_qpt {f : Str → Str} (P : PolyProgram id id f) (G : MFamily) (hG : IsMQPT G) :
    IsMQPT (picked P G) :=
  revFamily_qpt _ (LoadedBatch.PostComposition.family_isMQPT P _ (revFamily_qpt _ (grid_qpt G hG)))

noncomputable def prefixed {f : Str → Str} (P : PolyProgram id id f) (G : MFamily) (n : ℕ) (s : Str) : Str :=
  List.replicate (capacity P (n + (batchReadoutFamily G gridTasks).outLen n) - s.length) false ++ s.reverse

theorem picked_raw {f : Str → Str} (P : PolyProgram id id f) (G : MFamily) (u : Str) (event : Str → Prop) :
    outputProb (picked P G) u event =
      outputProb (batchReadoutFamily G gridTasks) u (fun z => event (prefixed P G u.length (f (u ++ z.reverse)))) := by
  classical
  let block := gridTasks u.length
  let fam := batchReadoutFamily G gridTasks
  rw [picked,revProb,LoadedBatch.PostComposition.family_outputProbability]
  unfold outputProb
  apply Finset.sum_congr rfl
  intro y _
  by_cases hz : runLayered (coreCircuit G block) (basisInput (toBits u)) y = 0
  · change (if _ then ‖runLayered (coreCircuit G block) (basisInput (toBits u)) y‖^2 else 0) =
        (if _ then ‖runLayered (coreCircuit G block) (basisInput (toBits u)) y‖^2 else 0)
    simp [hz]
  have hpre : (List.ofFn fun i : Fin u.length => y (Fin.castAdd (fam.anc u.length+1) i)) = u := by
    have h := (core_preserves G u block y hz).1
    change inputWord G block y = u
    unfold inputWord
    rw [show (fun i => y (inputWire G block i)) = toBits u from funext h]
    exact List.ofFn_getElem
  have hs : (LoadedBatch.PostComposition.sources (revFamily fam) u.length).map y =
      u ++ (List.ofFn (fun i => y (fam.outW u.length i))).reverse := by
    rw [LoadedBatch.postSources_map]
    change (List.ofFn fun i : Fin u.length => y (Fin.castAdd (fam.anc u.length+1) i)) ++
      List.ofFn (fun i => y (fam.outW u.length i.rev)) = _
    rw [hpre,list_rev_fn (fun i => y (fam.outW u.length i))]
  change (if event (paddedOutput P ((LoadedBatch.PostComposition.sources (revFamily fam) u.length).map y)).reverse
    then _ else 0) = _
  rw [paddedOutput_eq_append, hs]
  simp only [List.reverse_append,List.reverse_replicate,List.length_append,List.length_reverse,List.length_ofFn,prefixed]
  rfl

theorem picked_law {f : Str → Str} (P : PolyProgram id id f) (G : MFamily) (u : Str) (event : Str → Prop) :
    outputProb (picked P G) u event =
      ∑ xs : GridBits G u,
        if event (prefixed P G u.length (f (u ++ (encS u ++ encL encS (allWords G u xs)).reverse)))
        then ∏ j, blockMass G u j (xs j) else 0 := by
  rw [picked_raw,raw_law]

end EncodedBatch

end P2MDyadicModule100

/- Helper module EncodedTranscript. -/
section P2MDyadicModule101

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.StaticBatch

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 Integration9_9.DyadicReadout

open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

abbrev Sample (G : MFamily) (rs : List Str) :=
  (i : Fin rs.length) → Bits ((rs.get i).length + (G.anc (rs.get i).length+1))

def sampleWords (G : MFamily) (rs : List Str) (xs : Sample G rs) : List Str :=
  List.ofFn fun i => List.ofFn fun j => xs i (G.outW (rs.get i).length j)

noncomputable def sampleMass (G : MFamily) (rs : List Str) (xs : Sample G rs) : ℝ :=
  ∏ i, ‖runLayered (G.circ (rs.get i).length) (basisInput (toBits (rs.get i))) (xs i)‖^2

noncomputable def pickProgram : PolyProgram id id post := LARCoinLayout.rawPolyProgram post_poly

theorem allWords_get (G : MFamily) (u : Str) (xs : GridBits G u) (k : Fin (gridTasks u.length).length) :
    ((allWords G u xs)[k.val]?).getD [] = List.ofFn fun j => xs k (G.outW ((gridTasks u.length).get k).length j) := by
  have hk : k.val < (allWords G u xs).length := by simpa only [allWords,List.length_ofFn] using k.isLt
  rw [List.getElem?_eq_getElem hk]
  simp only [Option.getD_some,allWords,List.getElem_ofFn]

theorem select_law (G : MFamily) (w : Str) (rs : List Str) (tail : Str) (event : Str → Prop) :
    let u := pack w rs ++ tail
    outputProb (picked pickProgram G) u event = ∑ xs : Sample G rs,
      if event (prefixed pickProgram G u.length (pack w (sampleWords G rs xs))) then sampleMass G rs xs else 0 := by
  classical
  let u := pack w rs ++ tail
  let ts := gridTasks u.length
  let f : Fin rs.length ↪ Fin ts.length :=
    ⟨actualIndex w rs tail, actualIndex_injective w rs tail⟩
  let X (k : Fin ts.length) := Bits (blockWidth G (ts.get k))
  let Ys := (i : Fin rs.length) → X (f i)
  let e (i : Fin rs.length) := MultiPre.outEquiv G (toBits u) (ts.get (f i)) (query_actual w rs tail i)
  let words (ys : Ys) := List.ofFn fun i => List.ofFn fun j => ys i (G.outW (ts.get (f i)).length j)
  let good (ys : Ys) := event (prefixed pickProgram G u.length (pack w (words ys)))
  let test (ys : Sample G rs) : ℝ :=
    if event (prefixed pickProgram G u.length (pack w (sampleWords G rs ys))) then sampleMass G rs ys else 0
  change outputProb (picked pickProgram G) u event = ∑ xs : Sample G rs, test xs
  have s1 : outputProb (picked pickProgram G) u event = ∑ xs : GridBits G u, if good (fun i => xs (f i)) then ∏ k, blockMass G u k (xs k) else 0 := by
    rw [picked_law pickProgram G u event]
    apply Finset.sum_congr rfl
    intro xs _
    have hp := post_correct w rs tail [] (allWords G u xs)
    simp only [List.append_nil] at hp
    change post (u ++ (encS u ++ encL encS (allWords G u xs)).reverse) = _ at hp
    rw [hp]
    have hw : (List.ofFn fun i : Fin rs.length => ((allWords G u xs)[(actualIndex w rs tail i).val]?).getD []) =
        words (fun i => xs (f i)) := by
      apply congrArg List.ofFn
      funext i
      exact allWords_get G u xs (f i)
    rw [hw]
  have s2 : (∑ xs : GridBits G u, if good (fun i => xs (f i)) then ∏ k, blockMass G u k (xs k) else 0) = ∑ ys : Ys, if good ys then ∏ i, blockMass G u (f i) (ys i) else 0 :=
      ParityGrid.restrict_event (X := X) f (blockMass G u) (blockMass_sum G u) good
  have s3 : (∑ ys : Ys, if good ys then ∏ i, blockMass G u (f i) (ys i) else 0) = ∑ ys : Ys, test (fun i => e i (ys i)) := by
      apply Finset.sum_congr rfl
      intro ys _
      have hwords : words ys = sampleWords G rs (fun i => e i (ys i)) := by
        apply congrArg List.ofFn
        funext i
        exact MultiPre.outEquiv_words G (toBits u) (ts.get (f i)) (query_actual w rs tail i) (ys i)
      have hmass : (∏ i, blockMass G u (f i) (ys i)) = sampleMass G rs (fun i => e i (ys i)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact MultiPre.outEquiv_mass G (toBits u) (ts.get (f i)) (query_actual w rs tail i) (ys i)
      simp only [good,test,hwords,hmass]
  exact s1.trans (s2.trans (s3.trans (MultiPre.sum_transport e test)))

theorem genericTranscript
    (G : MFamily) (hG : IsMQPT G) (q : Str → List Str) (hq : Poly q) :
    ∃ F : MFamily, IsMQPT F ∧ ∀ w : Str,
      ∃ padding : Sample G (q w) → Str, ∀ event : Str → Prop,
        outputProb F w event = ∑ xs : Sample G (q w),
          if event (padding xs ++ (pack w (sampleWords G (q w) xs)).reverse)
          then sampleMass G (q w) xs else 0 := by
  let f (w : Str) := pack w (q w)
  have hf : Poly f := Poly.comp (f := fun z : Str × List Str => pack z.1 z.2) (g := fun w : Str => (w, q w)) pack_poly
    (Poly.pair (show Poly (fun w : Str => w) by fun_prop) hq)
  obtain ⟨F,hF,law⟩ := MultiPre.precompose f hf (picked pickProgram G) (picked_qpt pickProgram G hG)
  refine ⟨F,hF,?_⟩
  intro w
  let rs := q w
  let tail := List.replicate (capacity (LARCoinLayout.rawPolyProgram hf) w.length - (f w).length) false
  let n := (pack w rs ++ tail).length
  refine ⟨fun xs => List.replicate (capacity pickProgram (n + (batchReadoutFamily G gridTasks).outLen n) -
    (pack w (sampleWords G rs xs)).length) false,?_⟩
  intro event
  rw [law,paddedOutput_eq_append]
  exact select_law G w rs tail event

end EncodedBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

theorem solution
    (G : MFamily) (hG : IsMQPT G) (q : Str → List Str)
    (hq : OAI.MetricKMedian.Binary.Automatic.Poly q) :
    ∃ F : MFamily, IsMQPT F ∧ ∀ w : Str,
      let requests := q w
      let width (i : Fin requests.length) :=
        (requests.get i).length + (G.anc (requests.get i).length + 1)
      ∃ padding : ((i : Fin requests.length) → Bits (width i)) → Str,
        ∀ event : Str → Prop, outputProb F w event =
          ∑ xs : (i : Fin requests.length) → Bits (width i),
            let outs := List.ofFn (fun i => List.ofFn fun j =>
              xs i (G.outW (requests.get i).length j))
            if event (padding xs ++ (encS w ++ encL encS outs).reverse)
            then ∏ i, ‖runLayered (G.circ (requests.get i).length)
              (basisInput (toBits (requests.get i))) (xs i)‖^2 else 0 :=
  EncodedBatch.genericTranscript G hG q hq

end P2MDyadicModule101
