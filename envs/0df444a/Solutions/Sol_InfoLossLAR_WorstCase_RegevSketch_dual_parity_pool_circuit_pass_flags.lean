-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_circuit_pass_flags
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T15:11:43.824502+00:00
-- url     : https://prove2.me/submissions/7bc299db-7112-4a30-a884-edba45747cbc

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_02
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_mqpt_encoded_query_transcript
import Mathlib
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_native_integer_determinant
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_native_integer_psd_test

section CompactCircuitProof

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

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

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

namespace Integration9_9.TM2NativeAffineApply
end Integration9_9.TM2NativeAffineApply

namespace Integration9_9.TM2NativeAffineEmitter
end Integration9_9.TM2NativeAffineEmitter

namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding

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
section P2MDyadicModule1

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

end P2MDyadicModule1

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule2

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

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeInverseUniform. -/
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

end P2MDyadicModule3

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
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

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
section P2MDyadicModule5

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

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule6

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

end P2MDyadicModule6

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule7

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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule8

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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule9

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

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule10

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

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule11

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

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule12

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

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule13

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

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule14

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

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule19

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule20

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

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule21

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

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule22

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

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule23

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

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule24

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

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule25

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

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule26

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

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule27

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

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule28

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

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule30

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

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule31

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

end P2MDyadicModule31

/- Helper module Solutions.AdvantageBridgeRegisterLoad. -/
section P2MDyadicModule32

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

end InfoLossLAR.WorstCase

end P2MDyadicModule42

/- Helper module Solutions.AdvantageBridgeBodyCodeCapture. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime Integration9_9.TM2PlatformSerialization

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

end BooleanProgram

namespace TM2Boolean.PolyProgramCircuit

end TM2Boolean.PolyProgramCircuit

end InfoLossLAR.WorstCase

end P2MDyadicModule43

/- Helper module Solutions.AdvantageBridgeBodyFamily. -/
section P2MDyadicModule44

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

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule45

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

end P2MDyadicModule45

/- Helper module Solutions.AdvantageBridgeBodyDEmission. -/
section P2MDyadicModule46

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

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeLoadedBatchShift. -/
section P2MDyadicModule47

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeLoadedBatchRebase. -/
section P2MDyadicModule48

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

end P2MDyadicModule48

/- Helper module Solutions.AdvantageBridgeBodyUniform. -/
section P2MDyadicModule49

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

end P2MDyadicModule49

/- Helper module Solutions.AdvantageBridgeSelectorTensor. -/
section P2MDyadicModule50

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

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeLoadedBatchPostprocess. -/
section P2MDyadicModule51

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

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeLoadedBatchPostTensor. -/
section P2MDyadicModule52

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

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeLoadedBatchMachine. -/
section P2MDyadicModule53

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

end Integration9_9.LoadedBatch

end

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeLoadedBatchPostFamily. -/
section P2MDyadicModule54

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

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeLoadedBatchPostCompile. -/
section P2MDyadicModule55

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

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeLoadedBatchPostFrame. -/
section P2MDyadicModule56

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

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeLoadedBatchState. -/
section P2MDyadicModule60

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

theorem castState_basis {left right : ℕ} (he : left=right) (bits : Bits left) :
    castState he (computationalBasis bits)=computationalBasis (fun i => bits (Fin.cast he.symm i)) := by
  cases he;rfl

theorem runLayered_cast {left right : ℕ} (he : left=right) (circuit : Layered left) (state : QState left) :
    runLayered (castBodyCircuit he circuit) (castState he state)=castState he (runLayered circuit state) := by cases he;rfl

end Integration9_9.LoadedBatch

end

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeLoadedBatchBorn. -/
section P2MDyadicModule61

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

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeLoadedBatchPostUniform. -/
section P2MDyadicModule88

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

end P2MDyadicModule88

/- Helper module Solutions.RegevBridgeLoadedBatchPostSemantics. -/
section P2MDyadicModule89

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

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeLoadedBatchPostProbability. -/
section P2MDyadicModule99

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

end P2MDyadicModule99


section FlagCircuitPart0

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

def firstDecision (F : MFamily) (hlen : ∀ n, 0 < F.outLen n) : Family where
  anc := F.anc
  circ := F.circ
  out n := F.outW n ⟨0, hlen n⟩

def firstDescription (x : Str × Str) : Str :=
  let a := readUnary x.2
  let wires := readWireWords a.2
  a.1 ++ (wires.2[0]?).getD (encNat 0) ++ wires.1

@[fun_prop] theorem firstDescription_poly : Poly firstDescription := by
  unfold firstDescription
  fun_prop

theorem firstDescription_correct (F : MFamily) (hlen : ∀ n, 0 < F.outLen n) (n : ℕ) :
    firstDescription (unary n, F.encAt n) = encFamilyAt (firstDecision F hlen) n := by
  simp only [firstDescription, multi_encoding, List.append_assoc, readUnary_append, readWireWords_append,
    encFamilyAt, firstDecision, List.getElem?_map]
  simp only [List.getElem?_eq_getElem (by simpa using hlen n : 0 < (List.ofFn (F.outW n)).length),
    Option.map_some, Option.getD_some, List.getElem_ofFn]

theorem firstDecision_qpt (F : MFamily) (hF : IsMQPT F) (hlen : ∀ n, 0 < F.outLen n) :
    IsQPT (firstDecision F hlen) := by
  obtain ⟨⟨source, hs, henc⟩, hwf, p, hp⟩ := hF
  refine ⟨⟨fun w => firstDescription (w, source w),
    generator_builder_polyTime _ hs _ firstDescription_poly, ?_⟩, hwf, p, ?_⟩
  · intro n
    simpa only [henc] using firstDescription_correct F hlen n
  · exact ⟨fun n => (hp n).1, fun n => (hp n).2.1⟩

theorem firstDecision_prob (F : MFamily) (hlen : ∀ n, 0 < F.outLen n) (w : Str) :
    acceptProb (firstDecision F hlen) w = outputProb F w (fun z => z[0]? = some true) := by
  classical
  unfold acceptProb outputProb
  apply Finset.sum_congr rfl
  intro y _
  simp only [firstDecision, List.getElem?_eq_getElem (by simpa using hlen w.length :
    0 < (List.ofFn fun j => y (F.outW w.length j)).length),List.getElem_ofFn, Option.some.injEq]

abbrev Test := Str × (ℕ × Str) → Bool

def frame (word : Str) (outputs : List Str) : Str :=
  (encS word ++ encL encS outputs).reverse

def readStrings : Str → Str × List Str := readBinaryList readS

@[fun_prop] theorem readStrings_poly : Poly readStrings := readBinaryList_poly readS readS_poly readS_rest_length

def bad (test : Str × (ℕ × Str) → Bool) (x : Str × List Str) : Bool :=
  decide (0 < ((List.range x.2.length).filter (fun i => !(test (x.1, i, x.2[i]?.getD [])))).length)

@[fun_prop] theorem bad_poly (test : Str × (ℕ × Str) → Bool) (ht : Poly test) : Poly (bad test) := by
  have hidx : Poly (fun x : Str × List Str => List.range x.2.length) :=
    Poly.comp (f := fun xs : List Str => List.range xs.length) Poly.list_indices Poly.snd
  unfold bad
  fun_prop

def decideFrame (test : Str × (ℕ × Str) → Bool) (input : Str) : Str :=
  let h := readS input.reverse
  [bad test (h.2, (readStrings h.1).2)]

@[fun_prop] theorem decideFrame_poly (test : Str × (ℕ × Str) → Bool) (ht : Poly test) : Poly (decideFrame test) := by
  unfold decideFrame
  fun_prop

theorem decideFrame_correct (test : Str × (ℕ × Str) → Bool) (w garbage : Str) (outputs : List Str) :
    decideFrame test (garbage ++ frame w outputs) = [bad test (w,outputs)] := by
  have h := readBinaryList_append_mapped readS encS id
    (fun word => (encB_length_pos word.length).trans_le (by simp [encS]))
    readS_append outputs garbage.reverse
  simp only [decideFrame,frame,List.reverse_append,List.reverse_reverse,List.append_assoc,readS_append,
    readStrings,h,List.map_id]

theorem bad_iff (test : Str × (ℕ × Str) → Bool) (w : Str) (outputs : List Str) :
    bad test (w,outputs) = true ↔ ∃ i : Fin outputs.length, test (w,i.val,outputs.get i) = false := by
  let f := fun i : ℕ => !(test (w,i,outputs[i]?.getD []))
  change decide (0 < ((List.range outputs.length).filter f).length) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro hlen
    obtain ⟨i,hi⟩ := List.exists_mem_of_length_pos hlen
    obtain ⟨h,hv⟩ := List.mem_filter.mp hi
    let j : Fin outputs.length := ⟨i, List.mem_range.mp h⟩
    exact ⟨j, by simpa [f,List.getElem?_eq_getElem j.isLt,j] using hv⟩
  · rintro ⟨j,hj⟩
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨List.mem_range.mpr j.isLt,
      by simpa [f,List.getElem?_eq_getElem j.isLt] using hj⟩)

end ParityFlags

end FlagCircuitPart0

section FlagCircuitPart1

set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
namespace ParityFlags
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open Integration9_9.LoadedBatch.PostComposition
open scoped BigOperators Classical
noncomputable section

def program (test : Str × (ℕ × Str) → Bool) (ht : Poly test) : PolyProgram id id (decideFrame test) :=
  LARCoinLayout.rawPolyProgram (decideFrame_poly test ht)

def decideFamily (F : MFamily) (test : Str × (ℕ × Str) → Bool) (ht : Poly test) : Family :=
  firstDecision (LoadedBatch.PostComposition.family F (program test ht))
    (fun n => capacity_pos (program test ht) (sources F n).length)

theorem decideFamily_qpt (F : MFamily) (hF : IsMQPT F) (test : Str × (ℕ × Str) → Bool)
    (ht : Poly test) : IsQPT (decideFamily F test ht) :=
  firstDecision_qpt _ (family_isMQPT (program test ht) F hF) _

def measured (F : MFamily) (w : Str) (y : Bits (w.length + (F.anc w.length+1))) : Str :=
  List.ofFn fun j => y (F.outW w.length j)

theorem decideFamily_prob (F : MFamily) (test : Str × (ℕ × Str) → Bool) (ht : Poly test)
    (w : Str)
    (hframe : ∀ y, runLayered (F.circ w.length) (basisInput (toBits w)) y ≠ 0 →
      ∃ padding outputs, measured F w y = padding ++ frame w outputs) :
    acceptProb (decideFamily F test ht) w =
    outputProb F w (fun z => (decideFrame test z)[0]? = some true) := by
  rw [decideFamily, firstDecision_prob, family_outputProbability]
  unfold outputProb
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : runLayered (F.circ w.length) (basisInput (toBits w)) y = 0
  · simp [hy]
  · obtain ⟨padding, outputs, ho⟩ := hframe y hy
    change List.ofFn (fun j => y (F.outW w.length j)) = padding ++ frame w outputs at ho
    simp only [LoadedBatch.postSources_map, paddedOutput_eq_append, ho, ← List.append_assoc,
      decideFrame_correct, List.cons_append, List.getElem?_cons_zero, Option.some.injEq]

theorem support_from_law {α : Type*} [Fintype α] (F : MFamily) (w : Str)
    (padding : α → Str) (outputs : α → List Str) (mass : α → ℝ)
    (hlaw : ∀ event : Str → Prop, outputProb F w event =
      ∑ x, if event (padding x ++ frame w (outputs x)) then mass x else 0) :
    ∀ y, runLayered (F.circ w.length) (basisInput (toBits w)) y ≠ 0 →
      ∃ pad os, measured F w y = pad ++ frame w os := by
  classical
  intro y hy
  by_contra h
  let miss := fun z : Str => ¬ ∃ pad os, z = pad ++ frame w os
  have hm : outputProb F w miss = 0 := by
    rw [hlaw]
    apply Finset.sum_eq_zero
    intro x _
    exact if_neg (fun hn => hn ⟨padding x,outputs x,rfl⟩)
  let weights := fun b : Bits (w.length + (F.anc w.length+1)) =>
    if miss (measured F w b) then ‖runLayered (F.circ w.length) (basisInput (toBits w)) b‖^2 else 0
  have hs : weights y ≤ ∑ b, weights b := Finset.single_le_sum
    (fun b _ => by dsimp [weights]; split_ifs <;> positivity) (Finset.mem_univ y)
  have hm' : (∑ b, weights b) = 0 := by
    rw [← hm,outputProb]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [weights,measured]
    split_ifs <;> rfl
  have hp : 0 < weights y := by
    rw [show weights y = ‖runLayered (F.circ w.length) (basisInput (toBits w)) y‖^2 from if_pos h]
    exact sq_pos_of_pos (norm_pos_iff.mpr hy)
  linarith

/-- A uniformly prepared framed transcript can be verified reversibly with a
single output wire. The experiment need only have the specified measured law. -/
theorem decideFamily_law {α : Type*} [Fintype α] (F : MFamily)
    (test : Str × (ℕ × Str) → Bool) (ht : Poly test) (w : Str)
    (padding : α → Str) (outputs : α → List Str) (mass : α → ℝ)
    (hlaw : ∀ event : Str → Prop, outputProb F w event =
      ∑ x, if event (padding x ++ frame w (outputs x)) then mass x else 0) :
    acceptProb (decideFamily F test ht) w =
      ∑ x, if bad test (w, outputs x) then mass x else 0 := by
  rw [decideFamily_prob F test ht w (support_from_law F w padding outputs mass hlaw), hlaw]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decideFrame_correct, List.getElem?_cons_zero, Option.some.injEq]

end
end ParityFlags

end FlagCircuitPart1

section FlagCircuitPart2

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace ParityFlags
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators Classical
noncomputable section

theorem fail_product {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ι → Type*} [∀ i, Fintype (T i)]
    (weight : ∀ i, T i → ℝ) (good : ∀ i, T i → Bool) (total : ∀ i, ∑ s, weight i s = 1) :
    (∑ xs : (i : ι) → T i,
      if ∃ i, good i (xs i) = false then ∏ i, weight i (xs i) else 0) =
      1 - ∏ i, ∑ s, if good i s then weight i s else 0 := by
  classical
  apply eq_sub_of_add_eq
  rw [Fintype.prod_sum]
  rw [← Finset.sum_add_distrib]
  have ht : (∑ xs : (i : ι) → T i, ∏ i, weight i (xs i)) = 1 := by
    rw [← Fintype.prod_sum, show (∏ i, ∑ s, weight i s) = 1 by simp [total]]
  rw [← ht]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases h : ∃ i, good i (xs i) = false
  · obtain ⟨i,hi⟩ := h
    rw [if_pos (show ∃ i, good i (xs i) = false from ⟨i,hi⟩)]
    have hz : (∏ j, if good j (xs j) then weight j (xs j) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hz, add_zero]
  · rw [if_neg h, zero_add]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : good i (xs i) with
    | false => exact (h ⟨i,hi⟩).elim
    | true => rfl

abbrev BasisOutcomes (G : MFamily) (q : Str → List Str) (w : Str) :=
  (i : Fin (q w).length) → Bits (((q w).get i).length + (G.anc ((q w).get i).length+1))

def outputWords (G : MFamily) (q : Str → List Str) (w : Str) (xs : BasisOutcomes G q w) : List Str :=
  List.ofFn fun i => measured G ((q w).get i) (xs i)

def branchMass (G : MFamily) (request : Str) (y : Bits (request.length + (G.anc request.length + 1))) : ℝ :=
  ‖runLayered (G.circ request.length) (basisInput (toBits request)) y‖^2

theorem branchMass_total (G : MFamily) (request : Str) : ∑ y, branchMass G request y = 1 := by
  have h := runLayered_mass (G.circ request.length) (basisInput (a := G.anc request.length) (toBits request))
  simpa only [branchMass, Complex.normSq_eq_norm_sq] using
    h.trans (basisInput_mass (a := G.anc request.length) (toBits request))

theorem weighted_bad (G : MFamily) (q : Str → List Str) (test : Str × (ℕ × Str) → Bool) (w : Str) :
    (∑ xs : BasisOutcomes G q w,
      if bad test (w, outputWords G q w xs) then
        ∏ i, branchMass G ((q w).get i) (xs i) else 0) =
    1 - ∏ i : Fin (q w).length, outputProb G ((q w).get i)
      (fun out => test (w,i.val,out) = true) := by
  classical
  let good := fun (i : Fin (q w).length) (s : Bits (((q w).get i).length +
      (G.anc ((q w).get i).length + 1))) => test (w,i.val,measured G ((q w).get i) s)
  have hbad (xs : BasisOutcomes G q w) :
      bad test (w,outputWords G q w xs) = true ↔ ∃ i, good i (xs i) = false := by
    rw [bad_iff]
    constructor
    · rintro ⟨j,hj⟩
      refine ⟨⟨j.val, by simpa only [outputWords,List.length_ofFn] using j.isLt⟩,?_⟩
      simpa only [outputWords, List.get_eq_getElem, List.getElem_ofFn, good] using hj
    · rintro ⟨j,hj⟩
      refine ⟨⟨j.val, by simpa only [outputWords,List.length_ofFn] using j.isLt⟩,?_⟩
      simpa only [outputWords, List.get_eq_getElem, List.getElem_ofFn, good] using hj
  simp_rw [hbad]
  have h := fail_product (fun i => branchMass G ((q w).get i)) good (fun i => branchMass_total G ((q w).get i))
  convert h using 1
  · apply Finset.sum_congr rfl
    intro xs _
    split_ifs <;> rfl
  · congr 1
    apply Finset.prod_congr rfl
    intro i _
    unfold outputProb
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [good,measured,branchMass]
    split_ifs <;> rfl

theorem batch_test_of_transcript (G F : MFamily) (hF : IsMQPT F) (q : Str → List Str)
    (test : Str × (ℕ × Str) → Bool) (ht : Poly test)
    (hj : ∀ w, ∃ padding : BasisOutcomes G q w → Str,
      ∀ event : Str → Prop, outputProb F w event = ∑ xs : BasisOutcomes G q w,
        if event (padding xs ++ frame w (outputWords G q w xs))
        then ∏ i, branchMass G ((q w).get i) (xs i) else 0) :
    ∃ A : Family, IsQPT A ∧ ∀ w,
      acceptProb A w = 1 - ∏ i : Fin (q w).length, outputProb G ((q w).get i)
        (fun out => test (w,i.val,out) = true) := by
  refine ⟨decideFamily F test ht,decideFamily_qpt F hF test ht,?_⟩
  intro w
  obtain ⟨padding,h⟩ := hj w
  rw [decideFamily_law F test ht w padding _ _ h,weighted_bad]

end
end ParityFlags

end FlagCircuitPart2

section FlagCircuitPart3

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators Classical

namespace ParityFlags

theorem generic_of_transcript (G : MFamily) (q : Str → List Str)
    (test : Str × (ℕ × Str) → Bool) (ht : Poly test)
    (h : ∃ F : MFamily, IsMQPT F ∧ ∀ w : Str,
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
              (basisInput (toBits (requests.get i))) (xs i)‖^2 else 0) :
    ∃ A : Family, IsQPT A ∧ ∀ w : Str, acceptProb A w =
      1 - ∏ j : Fin (q w).length,
        outputProb G ((q w).get j) (fun y => test (w,(j.val,y)) = true) := by
  obtain ⟨F,hF,hj⟩ := h
  exact batch_test_of_transcript G F hF q test ht hj

end ParityFlags

end FlagCircuitPart3

open scoped BigOperators Classical
open QAlgorithms.Complexity InfoLossLAR.WorstCase OAI.MetricKMedian.Binary.Automatic

theorem ParityFlags.verify_batch (G : MFamily) (hG : IsMQPT G) (q : Str → List Str) (hq : Poly q)
    (test : Str × (ℕ × Str) → Bool) (ht : Poly test) :
    ∃ A : Family, IsQPT A ∧ ∀ w : Str, acceptProb A w =
      1 - ∏ j : Fin (q w).length,
        outputProb G ((q w).get j) (fun y => test (w,(j.val,y)) = true) := by
  exact ParityFlags.generic_of_transcript G q test ht
    (RegevSketch.mqpt_encoded_query_transcript G hG q hq)

end CompactCircuitProof

section NativeQueriesProof

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false

namespace ParityFlagQueries
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 Integration9_9.LARPlatformEncoding
open InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent
open QMCNumericRuntime

abbrev Rows := List (List ℤ)
abbrev ColumnData := ℚ × ℕ × ℤ × Rows

def gapData (w : Str) : Rows × ℚ :=
  ((TM2NativeAffineEncoding.readMatrix (readS w).2).2, (readRational (readS (readS w).1).2).2)

@[fun_prop] theorem gapData_poly : Poly gapData := by unfold gapData; fun_prop

theorem gapData_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    gapData (encGapInstance B δ) = (List.ofFn (fun a => List.ofFn (B a)), δ) := by
  have hmat : TM2NativeAffineEncoding.readMatrix (encMat encI B) =
      ([], List.ofFn fun i => List.ofFn (B i)) := by
    simpa only [List.append_nil] using TM2NativeAffineEncoding.readMatrix_append B []
  have hs : readS (encS (encQ δ)) = ([], encQ δ) := by
    simpa only [List.append_nil] using readS_append (encQ δ) []
  have hq : readRational (encQ δ) = ([], δ) := by
    simpa only [List.append_nil, rationalCode, encQ] using readRational_append δ []
  simp only [gapData,encGapInstance,encPair,readS_append,hmat,hs,hq]

def doubleRow (input : List ℤ × ℕ) : List ℤ :=
  (List.range input.1.length).map fun j =>
    input.1[j]?.getD 0 * (if j = input.2 then 2 else 1)

@[fun_prop] theorem doubleRow_poly : Poly doubleRow := by
  unfold doubleRow
  apply Poly.list_map
  · fun_prop
  · exact Poly.comp (f := fun xs : List ℤ => List.range xs.length) (g := Prod.fst) Poly.list_indices Poly.fst

def doubleColumn (input : Rows × ℕ) : Rows :=
  input.1.map fun row => doubleRow (row,input.2)

@[fun_prop] theorem doubleColumn_poly : Poly doubleColumn := by
  unfold doubleColumn
  apply Poly.list_map (by fun_prop) Poly.fst

theorem doubleRow_correct {n : ℕ} (v : Fin n → ℤ) (i : Fin n) :
    doubleRow (List.ofFn v, i.val) = List.ofFn (fun j => v j * (if j=i then 2 else 1)) := by
  apply List.ext_getElem
  · simp [doubleRow]
  · intro j hj hk
    have hjn : j < n := by simpa using hk
    simp [doubleRow,hjn,Fin.ext_iff]

def doubled {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  fun a b => B a b * (if b=i then 2 else 1)

theorem doubleColumn_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    doubleColumn (List.ofFn (fun a => List.ofFn (B a)),i.val) =
      List.ofFn fun a => List.ofFn (doubled B i a) := by
  simp only [doubleColumn,List.map_ofFn,Function.comp_def,doubleRow_correct]
  rfl

def columnData (alg : Rows → ℤ × Rows) (input : Str × ℕ) : ColumnData :=
  let gap := gapData input.1
  let out := alg (doubleColumn (gap.1,input.2))
  (gap.2, gap.1.length, out.1, out.2)

@[fun_prop] theorem columnData_poly (alg : Rows → ℤ × Rows) (hAlg : Poly alg) :
    Poly (columnData alg) := by unfold columnData; fun_prop

abbrev Correct (alg : Rows → ℤ × Rows) := ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ),
  alg (List.ofFn fun a => List.ofFn (H a)) =
    (H.det, List.ofFn fun a => List.ofFn (H.adjugate.transpose a))

theorem columnData_correct (alg : Rows → ℤ × Rows) (hExact : Correct alg)
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (i : Fin n) :
    columnData alg (encGapInstance B δ,i.val) =
      (δ,n,(doubled B i).det,List.ofFn fun a => List.ofFn ((doubled B i).adjugate.transpose a)) := by
  simp only [columnData, gapData_correct, List.length_ofFn, doubleColumn_correct, hExact]

def rowCode (v : List ℤ) : Str := encL encI v
def matrixCode (v : Rows) : Str := encL rowCode v

@[fun_prop] theorem rowCode_poly : Poly rowCode := by unfold rowCode encL; fun_prop
@[fun_prop] theorem matrixCode_poly : Poly matrixCode := by unfold matrixCode encL; fun_prop

theorem matrixCode_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    matrixCode (List.ofFn fun a => List.ofFn (B a)) = encMat encI B := by
  have hm : (List.ofFn fun a => List.ofFn (B a)) =
      (List.ofFn (fun a : Fin n => B a)).map (fun row : Fin n → ℤ => List.ofFn row) :=
    (List.map_ofFn (f := fun a : Fin n => B a) (g := fun row : Fin n → ℤ => List.ofFn row)).symm
  simp only [matrixCode, encMat, encL, List.length_ofFn]
  congr 1
  rw [hm, List.flatMap_map]
  rfl

def sampleWidth (x : ℤ × ℚ) : ℚ := (x.1.natAbs : ℚ) / (100 * x.2)

@[fun_prop] theorem sampleWidth_poly : Poly sampleWidth := by
  unfold sampleWidth
  fun_prop

def unarySlots (p : Polynomial ℕ) (rows : Rows) : Str :=
  (List.replicate (p.eval rows.length) ()).map (fun _ => true)

@[fun_prop] theorem unarySlots_poly (p : Polynomial ℕ) : Poly (unarySlots p) := by
  have h := Poly.comp (TM2PolynomialBudget.polynomialSlots_poly p)
    (show Poly (fun rows : Rows => rows.map (fun _ => ())) by fun_prop)
  simp only [List.length_map] at h
  unfold unarySlots
  apply Poly.list_map (by fun_prop) h

noncomputable def queryAt (alg : Rows → ℤ × Rows) (input : Str × ℕ) : Str :=
  let data := columnData alg input
  let rows := (gapData input.1).1
  let count := unarySlots ((Polynomial.X+1)^3) rows
  let budget := unarySlots (16*(Polynomial.X+1)) rows
  encPair (matrixCode data.2.2.2) (encPair (rationalCode (sampleWidth (data.2.2.1,data.1))) (encPair count budget))

@[fun_prop] theorem queryAt_poly (alg : Rows → ℤ × Rows) (hAlg : Poly alg) :
    Poly (queryAt alg) := by unfold queryAt; fun_prop

theorem queryAt_correct (alg : Rows → ℤ × Rows) (hExact : Correct alg)
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (i : Fin n) :
    queryAt alg (encGapInstance B δ,i.val) =
      dgsInput (doubled B i).adjugate.transpose ((Int.natAbs (doubled B i).det : ℚ) / (100*δ))
        ((n+1)^3) (16*(n+1)) := by
  simp [queryAt, columnData_correct alg hExact, gapData_correct, unarySlots,
    matrixCode_correct, sampleWidth, dgsInput,unary,rationalCode,encQ]

noncomputable def queries (alg : Rows → ℤ × Rows) (w : Str) : List Str :=
  (List.range (gapData w).1.length).map fun i => queryAt alg (w,i)

theorem queries_poly (alg : Rows → ℤ × Rows) (hAlg : Poly alg) : Poly (queries alg) := by
  unfold queries
  apply Poly.list_map (by fun_prop)
  exact Poly.comp (f := fun rows : Rows => List.range rows.length) (g := fun w : Str => (gapData w).1) Poly.list_indices (by fun_prop)

theorem queries_correct (alg : Rows → ℤ × Rows) (hExact : Correct alg)
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    queries alg (encGapInstance B δ) = List.ofFn fun i : Fin n =>
      dgsInput (doubled B i).adjugate.transpose ((Int.natAbs (doubled B i).det : ℚ) / (100*δ))
        ((n+1)^3) (16*(n+1)) := by
  unfold queries
  simp only [gapData_correct, List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hin : i < n := by simpa only [List.length_ofFn] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact queryAt_correct alg hExact B δ ⟨i,hin⟩

end ParityFlagQueries

end NativeQueriesProof

section AdjugateFromDetProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ParityFlagQueries
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev DetCorrect (det : Rows → ℤ) := ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ),
  det (List.ofFn fun a => List.ofFn (B a)) = B.det

def indices (rows : Rows) : List ℕ := List.range rows.length
@[fun_prop] theorem indices_poly : Poly indices := Poly.list_indices

def unitRow (x : Rows × ℕ) : List ℤ :=
  (indices x.1).map fun j => if j = x.2 then 1 else 0
@[fun_prop] theorem unitRow_poly : Poly unitRow := by
  unfold unitRow
  apply Poly.list_map <;> fun_prop

def withUnitRow (x : Rows × (ℕ × ℕ)) : Rows :=
  (indices x.1).map fun a =>
    if a=x.2.1 then unitRow (x.1,x.2.2) else x.1[a]?.getD []
@[fun_prop] theorem withUnitRow_poly : Poly withUnitRow := by
  unfold withUnitRow
  apply Poly.list_map <;> fun_prop

def cofactorRow (det : Rows → ℤ) (x : Rows × ℕ) : List ℤ :=
  (indices x.1).map fun b => det (withUnitRow (x.1,(x.2,b)))
@[fun_prop] theorem cofactorRow_poly (det : Rows → ℤ) (hd : Poly det) : Poly (cofactorRow det) := by
  unfold cofactorRow
  apply Poly.list_map <;> fun_prop

def detAndDual (det : Rows → ℤ) (rows : Rows) : ℤ × Rows :=
  (det rows, (indices rows).map fun a => cofactorRow det (rows,a))
theorem detAndDual_poly (det : Rows → ℤ) (hd : Poly det) : Poly (detAndDual det) := by
  unfold detAndDual
  exact Poly.pair hd (Poly.list_map (by fun_prop) indices_poly)

private theorem map_indices {α : Type*} {n : ℕ} (rows : Rows) (hlen : rows.length=n)
    (f : ℕ → α) : (indices rows).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp [indices,hlen]
  · intro i hi hj
    simp [indices]

def asRows {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Rows := List.ofFn fun a => List.ofFn (H a)

theorem withUnitRow_correct {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (a b : Fin n) :
    withUnitRow (asRows H, (a.val,b.val)) = asRows (H.updateRow a (Pi.single b 1)) := by
  have hl : (asRows H).length=n := List.length_ofFn
  unfold withUnitRow
  rw [map_indices _ hl]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i = a
  · subst i
    simp only [Matrix.updateRow_self]
    unfold unitRow
    rw [map_indices _ hl]
    apply congrArg List.ofFn
    funext j
    simp [Pi.single_apply,Fin.ext_iff]
  · have hv : i.val ≠ a.val := fun h => hi (Fin.ext h)
    simp [hv,asRows, Matrix.updateRow_ne hi]

theorem detAndDual_correct (det : Rows → ℤ) (hd : DetCorrect det) :
    Correct (detAndDual det) := by
  intro n H
  let rows := asRows H
  have hl : rows.length=n := List.length_ofFn
  change (det rows, (indices rows).map (fun a => cofactorRow det (rows,a))) = _
  rw [show det rows = H.det from hd n H, map_indices _ hl]
  congr 1
  apply congrArg List.ofFn
  funext a
  unfold cofactorRow
  rw [map_indices _ hl]
  apply congrArg List.ofFn
  funext b
  rw [withUnitRow_correct, Matrix.transpose_apply, Matrix.adjugate_apply]
  exact hd n _

end ParityFlagQueries

end AdjugateFromDetProof

section PSDProof

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace PassFlagsPSD

variable {n m : ℕ}

def certificateMatrix (δ : ℚ) (det : ℤ) (D : Matrix (Fin n) (Fin n) ℤ)
    (p : Fin m → Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  ((m : ℤ) * det^2 * (δ.den : ℤ)^2) • (1 : Matrix (Fin n) (Fin n) ℤ) -
    (64 * δ.num^2) • ∑ j, vecMulVec (D.mulVec (p j)) (D.mulVec (p j))

theorem certificateMatrix_hermitian (δ : ℚ) (det : ℤ)
    (D : Matrix (Fin n) (Fin n) ℤ) (p : Fin m → Fin n → ℤ) :
    (certificateMatrix δ det D p).IsHermitian := by
  apply IsHermitian.ext
  intro a b
  simp only [certificateMatrix, star_trivial, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  simp only [show (b = a) ↔ (a = b) from eq_comm, mul_comm (D.mulVec _ b) (D.mulVec _ a)]

private theorem square_form (x u : Fin n → ℤ) :
    x ⬝ᵥ ((vecMulVec u u) *ᵥ x) = (x ⬝ᵥ u)^2 := by
  rw [dotProduct_mulVec, vecMul_vecMulVec, smul_dotProduct, dotProduct_comm u x]
  simp [sq]

theorem certificateMatrix_form (δ : ℚ) (det : ℤ)
    (D : Matrix (Fin n) (Fin n) ℤ) (p : Fin m → Fin n → ℤ) (x : Fin n → ℤ) :
    x ⬝ᵥ ((certificateMatrix δ det D p) *ᵥ x) =
      (m : ℤ) * det^2 * (δ.den : ℤ)^2 * (∑ a, (x a)^2) -
        (64 * δ.num^2) * (∑ j, (∑ a, x a * D.mulVec (p j) a)^2) := by
  simp only [certificateMatrix, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, sum_mulVec, dotProduct_sum, square_form, smul_eq_mul]
  simp only [dotProduct, sq]

private theorem clear_threshold (δ : ℚ) (det a b : ℤ) (m : ℕ) :
    (64 * δ.num^2 * a ≤ (m : ℤ) * det^2 * (δ.den : ℤ)^2 * b) ↔
      64 * δ^2 * (a : ℚ) ≤ (m : ℚ) * (det : ℚ)^2 * (b : ℚ) := by
  have hden : (0 : ℚ) < δ.den := by exact_mod_cast δ.pos
  have hn : (δ.num : ℚ) = δ * (δ.den : ℚ) := (div_eq_iff hden.ne').mp δ.num_div_den
  have hcast : (64 * δ.num^2 * a ≤ (m : ℤ) * det^2 * (δ.den : ℤ)^2 * b) ↔
      (64 * (δ.num : ℚ)^2 * (a : ℚ) ≤ (m : ℚ) * (det : ℚ)^2 * (δ.den : ℚ)^2 * (b : ℚ)) := by
    exact_mod_cast Iff.rfl
  rw [hcast,hn]
  convert mul_le_mul_iff_of_pos_right (sq_pos_of_pos hden) using 1
  ring_nf

theorem certificateMatrix_posSemidef_iff (δ : ℚ) (det : ℤ)
    (D : Matrix (Fin n) (Fin n) ℤ) (p : Fin m → Fin n → ℤ) :
    (certificateMatrix δ det D p).PosSemidef ↔
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * D.mulVec (p j) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * (det : ℚ)^2 * (∑ a, (x a : ℚ)^2) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, and_iff_right (certificateMatrix_hermitian δ det D p)]
  apply forall_congr'
  intro x
  rw [star_trivial, certificateMatrix_form, sub_nonneg, clear_threshold]
  push_cast
  rfl

end PassFlagsPSD

end PSDProof

section PoolTestProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PassFlagsPSD
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeAffineApply (dot dot_poly)

abbrev Rows := List (List ℤ)
abbrev PoolInput := (ℤ × ℕ) × ℤ × Rows × ℕ × Rows

def indices (rows : Rows) := List.range rows.length
@[fun_prop] theorem indices_poly : Poly indices := Poly.list_indices

def scores (v : Rows × List ℤ) : List ℤ :=
  v.1.map fun row => dot (v.2, row)
@[fun_prop] theorem scores_poly : Poly scores := by unfold scores; fun_prop

def gramEntry (v : PoolInput × ℕ × ℕ) : ℤ :=
  let x := v.1
  let a := v.2.1
  let b := v.2.2
  let rows := x.2.2.2.2
  let D := x.2.2.1
  let u := scores (rows, D[a]?.getD [])
  let t := scores (rows, D[b]?.getD [])
  let den : ℤ := x.1.2
  let c := (rows.length : ℤ) * x.2.1 * x.2.1 * den * den
  (if a = b then c else 0) - 64 * x.1.1 * x.1.1 * dot (u,t)

@[fun_prop] theorem gramEntry_poly : Poly gramEntry := by unfold gramEntry; fun_prop

def gramRows (x : PoolInput) : Rows :=
  (indices x.2.2.1).map fun a => (indices x.2.2.1).map fun b => gramEntry (x,a,b)
@[fun_prop] theorem gramRows_poly : Poly gramRows := by unfold gramRows; fun_prop

def oddTest (x : ℕ × List ℤ) : Bool := decide ((x.2[x.1]?.getD 0).natAbs % 2 = 1)
@[fun_prop] theorem oddTest_poly : Poly oddTest := by unfold oddTest; fun_prop

def oddCount (x : ℕ × Rows) : ℕ :=
  (x.2.filter fun row => oddTest (x.1,row)).length
@[fun_prop] theorem oddCount_poly : Poly oddCount := by unfold oddCount; fun_prop

def poolTest (pos : Rows → Bool) (x : PoolInput) : Bool :=
  decide (x.2.2.2.2.length ≤ 4*oddCount (x.2.2.2.1,x.2.2.2.2)) && pos (gramRows x)
theorem poolTest_poly (pos : Rows → Bool) (hpos : Poly pos) : Poly (poolTest pos) := by
  unfold poolTest
  fun_prop

end PassFlagsPSD

end PoolTestProof

section PoolCorrectProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace PassFlagsPSD
open Integration9_9.TM2NativeAffineApply (dot)
variable {n m : ℕ}

def rowsOf {k l : ℕ} (M : Fin k → Fin l → ℤ) : Rows :=
  List.ofFn fun i => List.ofFn (M i)

def poolInput (δ : ℚ) (det : ℤ) (D : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (p : Fin m → Fin n → ℤ) : PoolInput :=
  ((δ.num,δ.den), det, rowsOf D, i.val, rowsOf p)

private theorem dot_ofFn {k : ℕ} (x y : Fin k → ℤ) :
    dot (List.ofFn x,List.ofFn y) = ∑ j, x j * y j := by
  have hz : (List.ofFn x).zip (List.ofFn y) = List.ofFn (fun j => (x j, y j)) := by
    apply List.ext_getElem <;> simp
  simp only [dot, hz, List.map_ofFn, Function.comp_def, List.sum_ofFn]

theorem scores_value (D : Matrix (Fin n) (Fin n) ℤ) (p : Fin m → Fin n → ℤ) (i : Fin n) :
    scores (rowsOf p, List.ofFn (D i)) = List.ofFn fun j => D.mulVec (p j) i := by
  simp only [scores, rowsOf, List.map_ofFn, Function.comp_def, dot_ofFn, Matrix.mulVec, dotProduct]

private theorem lookup_ofFn {α : Type} {k : ℕ} (f : Fin k → α) (i : Fin k) (d : α) :
    ((List.ofFn f)[i.val]?).getD d = f i := by
  simp

theorem gramEntry_value (δ : ℚ) (det : ℤ) (D : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (p : Fin m → Fin n → ℤ) (a b : Fin n) :
    gramEntry (poolInput δ det D i p, a.val, b.val) = certificateMatrix δ det D p a b := by
  simp only [gramEntry, poolInput, rowsOf, List.length_ofFn, lookup_ofFn]
  change (if a.val = b.val then _ else 0) - _ *
    dot (scores (rowsOf p, List.ofFn (D a)),scores (rowsOf p,List.ofFn (D b))) = _
  rw [scores_value, scores_value, dot_ofFn]
  simp only [certificateMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Fin.val_inj]
  by_cases h : a = b <;> simp only [h, ite_true, ite_false, mul_one, mul_zero] <;> ring

private theorem range_map {α : Type} {k : ℕ} (f : ℕ → α) :
    (List.range k).map f = List.ofFn (fun i : Fin k => f i.val) := by
  apply List.ext_getElem <;> simp

theorem gramRows_value (δ : ℚ) (det : ℤ) (D : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (p : Fin m → Fin n → ℤ) :
    gramRows (poolInput δ det D i p) = rowsOf (certificateMatrix δ det D p) := by
  have hidx : indices (poolInput δ det D i p).2.2.1 = List.range n := by
    simp [indices, poolInput, rowsOf]
  simp only [gramRows,hidx,range_map,gramEntry_value,rowsOf]

theorem oddCount_value (i : Fin n) (p : Fin m → Fin n → ℤ) :
    oddCount (i.val,rowsOf p) = (Finset.univ.filter fun j => Odd (p j i)).card := by
  classical
  have hrow (j : Fin m) : oddTest (i.val,List.ofFn (p j)) = decide (Odd (p j i)) := by
    simp only [oddTest,lookup_ofFn,← Nat.odd_iff, Int.natAbs_odd]
  rw [Finset.card_filter]
  change ((List.ofFn fun j => List.ofFn (p j)).filter _).length = _
  have hsum {α : Type} (xs : List α) (q : α → Bool) :
      (xs.filter q).length = (xs.map fun z => if q z then 1 else 0).sum := by
    induction xs with
    | nil => rfl
    | cons x xs ih => cases h : q x <;> simp [h,ih,Nat.add_comm]
  rw [hsum]
  simp only [List.map_ofFn, Function.comp_def,hrow,decide_eq_true_eq,List.sum_ofFn]

theorem poolTest_correct (pos : Rows → Bool)
    (hspec : ∀ {k : ℕ} (S : Matrix (Fin k) (Fin k) ℤ), pos (rowsOf S) = true ↔ S.PosSemidef)
    (δ : ℚ) (det : ℤ) (D : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (p : Fin m → Fin n → ℤ) :
    poolTest pos (poolInput δ det D i p) = true ↔
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * D.mulVec (p j) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * (det : ℚ)^2 * (∑ a, (x a : ℚ)^2) := by
  simp only [poolTest, Bool.and_eq_true, decide_eq_true_eq, gramRows_value, hspec,
    certificateMatrix_posSemidef_iff]
  change ((rowsOf p).length ≤ 4 * oddCount (i.val, rowsOf p) ∧ _) ↔ _
  rw [oddCount_value]
  simp only [rowsOf, List.length_ofFn]

end PassFlagsPSD

end PoolCorrectProof

section PrefixProof

set_option autoImplicit false
set_option maxHeartbeats 1200000
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeAffineEncoding (readMatrix readMatrix_append readMatrix_poly)
open Integration9_9.TM2NativeAffineEmitter (serializeMatrix serializeVector serializeMatrix_poly)
open Integration9_9.LARPlatformEncoding (serializeBinaryWords_map)

namespace ParityPoolPrefix
abbrev Rows := List (List ℤ)

def rowsOf {m n : ℕ} (p : Fin m → Fin n → ℤ) : Rows :=
  List.ofFn (fun j => List.ofFn (p j))

theorem serialize_rows {n m : ℕ} (p : Fin m → Fin n → ℤ) :
    serializeMatrix (rowsOf p) = encVec (encVec encI) p := by
  have hv (v : Fin n → ℤ) : serializeVector (List.ofFn v) = encVec encI v := by
    simp only [serializeVector,serializeBinaryWords_map,encVec]
  simp only [serializeMatrix,rowsOf,List.map_ofFn,Function.comp_def,hv]
  change _ = encL (encVec encI) (List.ofFn p)
  simpa only [List.map_ofFn,Function.comp_def] using
    serializeBinaryWords_map (encVec encI) (List.ofFn p)

def bitMatch (x : (Str × Str) × ℕ) : Bool :=
  let left := x.1.1[x.2]?.getD false
  let right := x.1.2[x.2]?.getD false
  if left then right else !right

@[fun_prop] theorem bitMatch_poly : Poly bitMatch := by unfold bitMatch; fun_prop

def wordMatch (x : Str × Str) : Bool :=
  decide (x.1.length = x.2.length) &&
    decide (((List.range x.1.length).filter fun i => bitMatch (x,i)).length = x.1.length)

@[fun_prop] theorem wordMatch_poly : Poly wordMatch := by
  have hi : Poly (fun x : Str × Str => List.range x.1.length) :=
    Poly.comp (f := fun xs : Str => List.range xs.length) Poly.list_indices Poly.fst
  unfold wordMatch
  fun_prop

theorem wordMatch_eq (s t : Str) : wordMatch (s,t) = true ↔ s = t := by
  have hmatch (i : ℕ) : bitMatch ((s,t),i) = true ↔
      s[i]?.getD false = t[i]?.getD false := by
    unfold bitMatch
    cases s[i]?.getD false <;> cases t[i]?.getD false <;> decide
  have hlen : ((List.range s.length).filter fun i => bitMatch ((s,t),i)).length = s.length ↔
      ∀ i < s.length, bitMatch ((s,t),i) = true := by
    simpa only [List.length_range,List.mem_range] using
      (List.length_filter_eq_length_iff (l := List.range s.length) (p := fun i => bitMatch ((s,t),i)))
  simp only [wordMatch,Bool.and_eq_true,decide_eq_true_eq, hlen, hmatch]
  constructor
  · rintro ⟨hs,he⟩
    apply List.ext_getElem hs
    intro i hi hj
    simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using he i hi
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩

def valid (input : ℕ × ℕ × Str) : Bool :=
  let result := readMatrix input.2.2
  decide (result.2.length = input.1) &&
    decide ((result.2.filter fun row => decide (row.length = input.2.1)).length = result.2.length) &&
    wordMatch (serializeMatrix result.2 ++ result.1, input.2.2)

@[fun_prop] theorem valid_poly : Poly valid := by
  unfold valid
  fun_prop

private theorem rowsOf_rectangular (m n : ℕ) (rows : Rows)
    (hm : rows.length = m) (hn : ∀ r ∈ rows, r.length = n) :
    ∃ p : Fin m → Fin n → ℤ, rowsOf p = rows := by
  let p (j : Fin m) (i : Fin n) : ℤ :=
    (rows[j.val]?.getD [])[i.val]?.getD 0
  refine ⟨p, ?_⟩
  apply List.ext_getElem
  · simp [rowsOf, hm]
  · intro j hp hj
    simp only [rowsOf, List.getElem_ofFn]
    have hr := hn _ (List.getElem_mem hj)
    apply List.ext_getElem
    · simp [hr]
    · intro i hi hri
      simp [p,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hri]

theorem valid_iff {m n : ℕ} (w : Str) (test : Rows → Bool)
    (event : (Fin m → Fin n → ℤ) → Prop)
    (correct : ∀ p, test (rowsOf p) = true ↔ event p) :
    (valid (m,n,w) && test (readMatrix w).2) = true ↔ decodedPoolEvent event w := by
  constructor
  · intro h
    rcases Bool.and_eq_true_iff.mp h with ⟨hv, ht⟩
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.length_filter_eq_length_iff,decide_eq_true_eq,wordMatch_eq] at hv
    obtain ⟨p,hp⟩ := rowsOf_rectangular m n (readMatrix w).2 hv.1.1 hv.1.2
    refine ⟨p, ⟨(readMatrix w).1, ?_⟩, (correct p).1 (hp ▸ ht)⟩
    rw [← serialize_rows, hp]
    exact hv.2
  · rintro ⟨p,⟨rest,rfl⟩,he⟩
    have hr : readMatrix (encVec (encVec encI) p ++ rest) = (rest,rowsOf p) :=
      readMatrix_append p rest
    have hs : ∀ row ∈ rowsOf p, row.length = n := by
      intro row h
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      simp
    simp only [valid,hr,Bool.and_eq_true,decide_eq_true_eq,List.length_filter_eq_length_iff,decide_eq_true_eq,wordMatch_eq]
    exact ⟨⟨⟨by simp [rowsOf],hs⟩, by rw [serialize_rows]⟩, (correct p).2 he⟩
end ParityPoolPrefix

end PrefixProof

section TestGateProof

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

namespace ParityPassGate
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QMCNumericRuntime
open Integration9_9.TM2NativeAffineEncoding (readMatrix readMatrix_poly)
open ParityFlagQueries (columnData columnData_correct)
abbrev Rows := List (List ℤ)
abbrev PSDspec (pos : Rows → Bool) := ∀ {k : ℕ} (S : Matrix (Fin k) (Fin k) ℤ),
  pos (PassFlagsPSD.rowsOf S) = true ↔ S.PosSemidef

def actualTest (alg : Rows → ℤ × Rows) (pos : Rows → Bool)
    (input : Str × (ℕ × Str)) : Bool :=
  let d := columnData alg (input.1,input.2.1)
  let y := input.2.2
  ParityPoolPrefix.valid ((d.2.1+1)^3,d.2.1,y) &&
    PassFlagsPSD.poolTest pos ((d.1.num,d.1.den),d.2.2.1,d.2.2.2,input.2.1,(readMatrix y).2)

theorem actualTest_poly (alg : Rows → ℤ × Rows) (hAlg : Poly alg) (pos : Rows → Bool)
    (hpos : Poly pos) : Poly (actualTest alg pos) := by
  have hnum : Poly Rat.num := ⟨PolyProgram.ratNum⟩
  have hden : Poly Rat.den := ⟨PolyProgram.ratDen⟩
  have hpool := PassFlagsPSD.poolTest_poly pos hpos
  have hcol := ParityFlagQueries.columnData_poly alg hAlg
  unfold actualTest
  fun_prop

theorem actualTest_correct (alg : Rows → ℤ × Rows) (hAlg : ParityFlagQueries.Correct alg)
    (pos : Rows → Bool) (hpos : PSDspec pos) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (i : Fin n) (w : Str) :
    actualTest alg pos (encGapInstance B δ,i.val,w) = true ↔
      decodedPoolEvent (fun p : Fin ((n+1)^3) → Fin n → ℤ =>
        (n+1)^3 ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
        ∀ x : Fin n → ℤ, 64 * δ^2 *
          (∑ j, ((∑ a, x a * ((ParityFlagQueries.doubled B i).adjugate.transpose.mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (((n+1)^3 : ℕ) : ℚ) * ((ParityFlagQueries.doubled B i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)) w := by
  simp only [actualTest,columnData_correct alg hAlg B δ i]
  refine ParityPoolPrefix.valid_iff w (fun rows => PassFlagsPSD.poolTest pos
    ((δ.num,δ.den), (ParityFlagQueries.doubled B i).det,
      PassFlagsPSD.rowsOf (ParityFlagQueries.doubled B i).adjugate.transpose,i.val,rows)) _ ?_
  intro p
  exact PassFlagsPSD.poolTest_correct pos hpos δ _ _ i p

end ParityPassGate

end TestGateProof

section BernoulliFlagsProof

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open scoped BigOperators

namespace ParityFlagLaw

theorem outputProb_bounds (G : MFamily) (w : Str) (event : Str → Prop) :
    0 ≤ outputProb G w event ∧ outputProb G w event ≤ 1 := by
  classical
  unfold outputProb
  let state := runLayered (G.circ w.length) (basisInput (toBits w))
  have total : (∑ y, ‖state y‖^2) = 1 := by
    simpa only [state, ← Complex.normSq_eq_norm_sq] using
      (runLayered_mass (G.circ w.length) (basisInput (toBits w))).trans
        (basisInput_mass (a := G.anc w.length) (toBits w))
  constructor
  · exact Finset.sum_nonneg (by intro y _; split_ifs <;> positivity)
  · apply le_trans _ total.le
    apply Finset.sum_le_sum
    intro y _
    split_ifs <;> first | exact le_rfl | positivity

def bitMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

def weights {n : ℕ} (p : Fin n → ℝ) (flags : Fin n → Bool) : ℝ :=
  ∏ i, bitMass (p i) (flags i)

theorem weights_nonneg {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (flags : Fin n → Bool) : 0 ≤ weights p flags := by
  apply Finset.prod_nonneg
  intro i _
  unfold bitMass
  split_ifs
  · exact (hp i).1
  · exact sub_nonneg.mpr (hp i).2

theorem weights_total {n : ℕ} (p : Fin n → ℝ) : (∑ f, weights p f) = 1 := by
  unfold weights
  rw [← Fintype.prod_sum]
  simp [bitMass]

theorem weights_marginal {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    (∑ f : Fin n → Bool, if f i then weights p f else 0) = p i := by
  classical
  let restricted := fun (j : Fin n) (b : Bool) =>
    if j=i ∧ b=false then 0 else bitMass (p j) b
  have term (f : Fin n → Bool) :
      (if f i then weights p f else 0) = ∏ j, restricted j (f j) := by
    cases h : f i with
    | false =>
      apply Eq.symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [restricted,h]
    | true =>
      change (∏ j, bitMass (p j) (f j)) = _
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j=i
      · subst j
        simp [restricted,h]
      · simp [restricted,hj]
  simp_rw [term]
  rw [← Fintype.prod_sum, Fintype.prod_eq_single i]
  · simp [restricted, bitMass]
  · intro j hj
    simp [restricted, hj, bitMass]

theorem weights_failure {n : ℕ} (p : Fin n → ℝ) :
    (∑ f : Fin n → Bool, if ∃ i, f i = false then weights p f else 0) = 1-∏ i, p i := by
  classical
  let pass : Fin n → Bool := fun _ => true
  have all_pass (f : Fin n → Bool) : ¬(∃ i, f i = false) ↔ f = pass := by
    constructor
    · intro h
      funext i
      cases hi : f i with
      | false => exact (h ⟨i,hi⟩).elim
      | true => rfl
    · rintro rfl ⟨i,hi⟩
      contradiction
  have splitMass (f : Fin n → Bool) :
      (if ∃ i, f i = false then weights p f else 0) +
        (if f = pass then weights p f else 0) = weights p f := by
    by_cases h : ∃ i, f i = false
    · have hne : f ≠ pass := fun hpass => (all_pass f).mpr hpass h
      simp [h,hne]
    · simp [(all_pass f).mp h]
  have splitSum := congrArg (fun g : (Fin n → Bool) → ℝ => ∑ f, g f) (funext splitMass)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, weights_total] at splitSum
  have hpass : weights p pass = ∏ i, p i := by simp [weights, pass,bitMass]
  linarith

end ParityFlagLaw

end BernoulliFlagsProof

section ReindexProof

open QAlgorithms.Complexity InfoLossLAR.WorstCase
open scoped BigOperators Classical

namespace ParityPassGate
noncomputable def passProduct (G : MFamily) (w : Str) (t : Str × (ℕ × Str) → Bool)
    (qs : List Str) : ℝ :=
  ∏ j : Fin qs.length, outputProb G (qs.get j) (fun y => t (w,j.val,y) = true)

theorem passProduct_ofFn (G : MFamily) (w : Str) (t : Str × (ℕ × Str) → Bool)
    {n : ℕ} (v : Fin n → Str) :
    passProduct G w t (List.ofFn v) =
      ∏ i : Fin n, outputProb G (v i) (fun y => t (w,i.val,y) = true) := by
  unfold passProduct
  apply Fintype.prod_equiv (finCongr (List.length_ofFn (f := v))) _ _
  intro i
  simp [List.get_eq_getElem, finCongr, Fin.cast]
end ParityPassGate

end ReindexProof

section RootProof

set_option autoImplicit false
set_option maxHeartbeats 1400000
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open scoped BigOperators Classical

theorem solution :
    ∀ G : MFamily, IsMQPT G → ∃ A : Family, IsQPT A ∧
    ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    ∃ weights : (Fin n → Bool) → ℝ,
      (∀ flags, 0 ≤ weights flags) ∧
      (∑ flags, weights flags) = 1 ∧
      (∀ i : Fin n,
        (∑ flags, if flags i then weights flags else 0) =
          outputProb G (dgsInput (D i) (r i) m (16*(n+1))) (decodedPoolEvent (E i))) ∧
      acceptProb A (encGapInstance B δ) =
        ∑ flags, if ∃ i : Fin n, flags i = false then weights flags else 0 := by
  classical
  intro G hG
  obtain ⟨det, hdet, hdetExact⟩ := native_integer_determinant
  obtain ⟨pos, hpos, hposExact⟩ := native_integer_psd_test
  let alg := ParityFlagQueries.detAndDual det
  have hAlg := ParityFlagQueries.detAndDual_poly det hdet
  have hExact := ParityFlagQueries.detAndDual_correct det hdetExact
  let q := ParityFlagQueries.queries alg
  let test := ParityPassGate.actualTest alg pos
  obtain ⟨A,hA,law⟩ := ParityFlags.verify_batch G hG q
    (ParityFlagQueries.queries_poly alg hAlg) test
    (ParityPassGate.actualTest_poly alg hAlg pos hpos)
  refine ⟨A,hA,?_⟩
  intro n hn B hB δ hδ m H D r E
  let v (i : Fin n) := dgsInput (D i) (r i) m (16*(n+1))
  let p (i : Fin n) := outputProb G (v i) (decodedPoolEvent (E i))
  refine ⟨ParityFlagLaw.weights p, ParityFlagLaw.weights_nonneg p
    (fun i => ParityFlagLaw.outputProb_bounds G (v i) _), ParityFlagLaw.weights_total p,
    ParityFlagLaw.weights_marginal p, ?_⟩
  let w := encGapInstance B δ
  have hq : q w = List.ofFn v := ParityFlagQueries.queries_correct alg hExact B δ
  have h := law w
  change acceptProb A w = 1 - ParityPassGate.passProduct G w test (q w) at h
  rw [hq,ParityPassGate.passProduct_ofFn] at h
  have heq (i : Fin n) :
      outputProb G (v i) (fun y => test (w,i.val,y) = true) = p i := by
    have events : (fun y => test (w,i.val,y) = true) = decodedPoolEvent (E i) := by
      funext y
      exact propext (ParityPassGate.actualTest_correct alg hExact pos
        (fun {_} S => hposExact _ S) B δ i y)
    exact congrArg (outputProb G (v i)) events
  have prodEq :
      (∏ i, outputProb G (v i) (fun y => test (w,i.val,y) = true)) = ∏ i, p i :=
    Finset.prod_congr rfl (fun i _ => heq i)
  exact h.trans ((congrArg (fun z : ℝ => 1-z) prodEq).trans (ParityFlagLaw.weights_failure p).symm)

end RootProof
