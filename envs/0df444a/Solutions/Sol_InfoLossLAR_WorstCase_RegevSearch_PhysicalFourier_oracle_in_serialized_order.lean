-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier.oracle_in_serialized_order
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:40:04.360636+00:00
-- url     : https://prove2.me/submissions/2eca830b-0d1c-4941-a51b-f5b0ed88d8fe

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PaddedDecoder_native_request

set_option linter.all false

namespace AFT.BinaryArithmetic.readVector
end AFT.BinaryArithmetic.readVector

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.CoherentDecoder
end InfoLossLAR.WorstCase.CoherentDecoder

namespace InfoLossLAR.WorstCase.CoherentProjection
end InfoLossLAR.WorstCase.CoherentProjection

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier
end InfoLossLAR.WorstCase.FiniteLatticeFourier

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries
end InfoLossLAR.WorstCase.GaussianPoissonSeries

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile
end InfoLossLAR.WorstCase.NativeQFTPlanCompile

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.QuantumXorOracle
end InfoLossLAR.WorstCase.QuantumXorOracle

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder
end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.LARPlatformEncoding.readS
end Integration9_9.LARPlatformEncoding.readS

namespace Integration9_9.LARPlatformEncoding.serializeVector
end Integration9_9.LARPlatformEncoding.serializeVector

namespace Integration9_9.LoadedBatch
end Integration9_9.LoadedBatch

namespace Integration9_9.TM2NativeAffineEmitter
end Integration9_9.TM2NativeAffineEmitter

namespace Integration9_9.TM2NativeAffineEmitter.serializeVector
end Integration9_9.TM2NativeAffineEmitter.serializeVector

namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding

namespace Integration9_9.TM2PlatformSerialization
end Integration9_9.TM2PlatformSerialization

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QAlgorithms
end QAlgorithms

namespace QAlgorithms.Complexity
end QAlgorithms.Complexity

namespace QMCNumericRuntime
end QMCNumericRuntime

namespace RegevLWE.GaussConv
end RegevLWE.GaussConv

namespace SharedPoolCoherence
end SharedPoolCoherence

/- Helper module Solutions.RegevBridgeInverseCircuit. -/
section P2MDyadicModule0

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- Exact left inverse for the gate sequence, with every ancillary amplitude preserved. -/
theorem inverseGates_left {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayer (inverseGates gates) (runLayer gates ψ) = ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g rest ih =>
    rw [inverseGates_cons, runLayer_append]
    change runLayer (inverseInstr g)
      (runLayer (inverseGates rest) (runLayer rest (g.apply ψ))) = ψ
    rw [ih, inverseInstr_left]

theorem runLayered_singletons {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayered (gates.map (fun g => [g])) ψ = runLayer gates ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g rest ih =>
    change runLayered (rest.map (fun g => [g])) (g.apply ψ) =
      runLayer rest (g.apply ψ)
    exact ih _

theorem runLayered_flatten {n : ℕ} (circuit : Layered n) (ψ : QState n) :
    runLayered circuit ψ = runLayer circuit.flatten ψ := by
  induction circuit generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    change runLayered rest (runLayer layer ψ) = runLayer (layer ++ rest.flatten) ψ
    rw [runLayer_append, ih]

theorem inverseCircuit_left {n : ℕ} (circuit : Layered n) (ψ : QState n) :
    runLayered (inverseCircuit circuit) (runLayered circuit ψ) = ψ := by
  rw [inverseCircuit, runLayered_singletons, runLayered_flatten, inverseGates_left]

end InfoLossLAR.WorstCase

end P2MDyadicModule0

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

end InfoLossLAR.WorstCase

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
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

end InfoLossLAR.WorstCase

end P2MDyadicModule2

/- Helper module Solutions.AdvantageBridgeDisjointCircuit. -/
section P2MDyadicModule3

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

private theorem leftLayer_tensor {n m : ℕ} (layer : List (Instr n)) (first : QState n) (second : QState m) :
    runLayer (layer.map leftInstruction) (tensorState first second)=tensorState (runLayer layer first) second := by
  induction layer generalizing first with
  | nil => rfl
  | cons gate layer ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons]
    rw [leftInstruction_tensor]
    exact ih (gate.apply first)

theorem leftCircuit_tensor {n m : ℕ} (circuit : Layered n) (first : QState n) (second : QState m) :
    runLayered (leftCircuit circuit) (tensorState first second)=tensorState (runLayered circuit first) second := by
  induction circuit generalizing first with
  | nil => rfl
  | cons layer circuit ih =>
    simp only [leftCircuit,List.map_cons,runLayered,List.foldl_cons]
    rw [leftLayer_tensor]
    exact ih (runLayer layer first)

end InfoLossLAR.WorstCase

end P2MDyadicModule3

/- Helper module PreLaw. -/
section P2MDyadicModule4

set_option autoImplicit false

set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false

namespace MultiPre

open QAlgorithms.Complexity InfoLossLAR.WorstCase

open OAI.MetricKMedian.Binary Integration9_9 Integration9_9.LoadedBatch

open TM2Boolean.PolyProgramCircuit

open scoped BigOperators Classical

noncomputable section

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

end

end MultiPre

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeCoherentBasisEmbedding. -/
section P2MDyadicModule5

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open scoped BigOperators

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]

theorem basisEmbedding_at (e : I ↪ W) (ψ : I → ℂ) (i : I) :
    basisEmbedding e ψ (e i)=ψ i := by
  classical
  simp [basisEmbedding,basis,e.injective.eq_iff]

theorem basisEmbedding_outside (e : I ↪ W) (ψ : I → ℂ) (w : W)
    (h : w∉Set.range e) : basisEmbedding e ψ w=0 := by
  have he (i : I) : w≠e i := fun hh => h ⟨i,hh.symm⟩
  simp [basisEmbedding,basis,he]

theorem basisEmbedding_mass (e : I ↪ W) (ψ : I → ℂ) :
    (∑ w,‖basisEmbedding e ψ w‖^2)=∑ i,‖ψ i‖^2 := by
  classical
  calc
    _ = ∑ w∈Finset.univ.image e,‖basisEmbedding e ψ w‖^2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w _ hw
      have hn : w∉Set.range e := by
        rintro ⟨i,rfl⟩
        exact hw (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simp [basisEmbedding_outside e ψ w hn]
    _ = ∑ i,‖basisEmbedding e ψ (e i)‖^2 :=
      Finset.sum_image (fun _ _ _ _ he => e.injective he)
    _ = _ := by simp only [basisEmbedding_at]

theorem basisEmbedding_norm (e : I ↪ W) (ψ : I → ℂ) :
    ‖(WithLp.toLp 2 (basisEmbedding e ψ) : EuclideanSpace ℂ W)‖=
      ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ I)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,basisEmbedding_mass]

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule6

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

abbrev OutsideBits {k n : ℕ} (w : Fin k ↪ Fin n) :=
  {a : Fin n // a ∉ Set.range w} → Bool

/-- The selected wires and all remaining wires, with no restriction on their state. -/
noncomputable def wireBitsEquiv {k n : ℕ} (w : Fin k ↪ Fin n) :
    Bits n ≃ Bits k × OutsideBits w where
  toFun y := (fun i => y (w i), fun i => y i)
  invFun p a := if h : a ∈ Set.range w then
    p.1 ((Equiv.ofInjective w w.injective).symm ⟨a,h⟩) else p.2 ⟨a,h⟩
  left_inv y := by
    funext a
    dsimp
    split_ifs with h
    · exact congrArg y (congrArg Subtype.val ((Equiv.ofInjective w w.injective).apply_symm_apply ⟨a,h⟩))
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      dsimp
      simp only [dif_pos (Set.mem_range_self i),Equiv.ofInjective_symm_apply]
    · funext i
      dsimp
      rw [dif_neg i.property]

noncomputable def splitState {k n : ℕ} (w : Fin k ↪ Fin n) (ψ : QState n) :
    Bits k × OutsideBits w → ℂ := fun p => ψ ((wireBitsEquiv w).symm p)

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeCoherentXorCopy. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentXorCopy

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent

open scoped BigOperators

variable {W k : ℕ}

theorem gate_append (controls : Fin k → Fin W) (i : Fin k) (work : Bits W) (data : Bits k) :
    (gate controls i).act (Fin.append work data)=
      Fin.append work (Function.update data i (xor (data i) (work (controls i)))) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro l
    have hn : l.castAdd k≠Fin.natAdd W i := by
      intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hl:=l.isLt;omega
    simp [gate,ReversibleGate.act,Function.update_of_ne hn]
  · intro l
    by_cases h : l=i
    · subst l;simp [gate,ReversibleGate.act]
    · have hn : Fin.natAdd W l≠Fin.natAdd W i := by
        intro he;exact h (Fin.ext (Nat.add_left_cancel (congrArg Fin.val he)))
      simp [gate,ReversibleGate.act,Function.update_of_ne hn,Function.update_of_ne h]

def xorData (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) : Bits k :=
  fun j => xor (data j) (work (controls j))

theorem action_slots (controls : Fin k → Fin W) (slots : List (Fin k)) (hn : slots.Nodup)
    (work : Bits W) (data : Bits k) :
    reversibleAction (slots.map (gate controls)) (Fin.append work data)=
      Fin.append work (fun j => xor (data j) (if j∈slots then work (controls j) else false)) := by
  induction slots generalizing data with
  | nil => simp [reversibleAction]
  | cons i slots ih =>
    change reversibleAction (slots.map (gate controls)) ((gate controls i).act (Fin.append work data))=_
    rw [gate_append,ih (List.nodup_cons.mp hn).2]
    congr 1
    funext j
    by_cases h : j=i
    · subst j
      simp only [Function.update_self,List.mem_cons_self,if_true,
        if_neg (List.nodup_cons.mp hn).1,Bool.xor_false]
    · simp only [Function.update_of_ne h,List.mem_cons,h,false_or]

theorem action_all (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) :
    reversibleAction ((List.finRange k).map (gate controls)) (Fin.append work data)=
      Fin.append work (xorData controls work data) := by
  rw [action_slots controls _ (List.nodup_finRange k)]
  simp only [List.mem_finRange,if_true]
  rfl

theorem compile_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (basis x)=basis (reversibleAction gates x) := by
  rw [compileReversible_apply]
  funext y
  simp only [basis,Equiv.symm_apply_eq]

theorem circuit_basis (controls : Fin k → Fin W) (work : Bits W) (data : Bits k) :
    runLayered (circuit controls) (basis (Fin.append work data))=
      basis (Fin.append work (xorData controls work data)) := by
  rw [circuit,compile_basis,action_all]

theorem append_eq_iff (a c : Bits W) (b d : Bits k) :
    Fin.append a b=Fin.append c d ↔ a=c ∧ b=d := by
  change (qubitsAppendEquiv W k).symm (a,b)=(qubitsAppendEquiv W k).symm (c,d) ↔ _
  rw [(qubitsAppendEquiv W k).symm.injective.eq_iff,Prod.mk.injEq]

end InfoLossLAR.WorstCase.CoherentXorCopy

end

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeCoherentProjection. -/
section P2MDyadicModule8

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

noncomputable def project {X : Type*} [Fintype X]
    (event : X → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => if event x then ψ x else 0)

theorem projection_error_sq {X : Type*} [Fintype X]
    (event : X → Prop) [DecidablePred event] (ψ : EuclideanSpace ℂ X) :
    ‖ψ-project event ψ‖^2=∑ x,if event x then 0 else ‖ψ x‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : event x <;> simp [project,h]

end InfoLossLAR.WorstCase.CoherentProjection

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeQuantumXorGoodState. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute

open ControlledNativeGates

open scoped BigOperators

variable {W k : ℕ}

def appendEmbedding (data : Bits k) : Bits W ↪ Bits (W+k) where
  toFun w := Fin.append w data
  inj' := by intro w v he;exact (CoherentXorCopy.append_eq_iff _ _ _ _).mp he |>.1

def attach (data : Bits k) : QState W →ₗ[ℂ] QState (W+k) := basisEmbedding (appendEmbedding data)

theorem attach_tensor (data : Bits k) (η : QState W) : attach data η=tensorState η (basis data) := by
  classical
  funext x
  obtain ⟨⟨w,d⟩,rfl⟩ := (qubitsAppendEquiv W k).symm.surjective x
  change attach data η (Fin.append w d)=tensorState η (basis data) (Fin.append w d)
  by_cases hd : d=data
  · subst d
    change basisEmbedding (appendEmbedding data) η (appendEmbedding data w)=_
    rw [basisEmbedding_at]
    have hl : leftRegister (Fin.append w data)=w := by funext i;exact Fin.append_left w data i
    have hr : rightRegister (Fin.append w data)=data := by funext i;exact Fin.append_right w data i
    rw [tensorState,hl,hr]
    simp [basis]
  · have ho : Fin.append w d∉Set.range (appendEmbedding data) := by
      rintro ⟨z,hz⟩
      have hh := (CoherentXorCopy.append_eq_iff _ _ _ _).mp hz
      exact hd hh.2.symm
    rw [attach,basisEmbedding_outside _ _ _ ho]
    have hl : leftRegister (Fin.append w d)=w := by funext i;exact Fin.append_left w d i
    have hr : rightRegister (Fin.append w d)=d := by funext i;exact Fin.append_right w d i
    rw [tensorState,hl,hr]
    simp [basis,hd]

theorem attach_norm (data : Bits k) (η : QState W) : stateNorm (attach data η)=stateNorm η :=
  basisEmbedding_norm _ _

theorem attach_error (data : Bits k) (η ζ : QState W) :
    stateNorm (attach data η-attach data ζ)=stateNorm (η-ζ) := by rw [←map_sub,attach_norm]

def readout (controls : Fin k→Fin W) (work : Bits W) : Bits k := fun i => work (controls i)

def xorMask (data answer : Bits k) : Bits k := fun i => xor (data i) (answer i)

def good (controls : Fin k→Fin W) (answer : Bits k) (η : QState W) : QState W :=
  fun work => if readout controls work=answer then η work else 0

def failure (controls : Fin k→Fin W) (answer : Bits k) (η : QState W) : ℝ :=
  ∑ work,if readout controls work=answer then 0 else ‖η work‖^2

theorem failure_nonnegative (controls : Fin k→Fin W) (answer : Bits k) (η : QState W) :
    0≤failure controls answer η := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs <;> positivity

theorem good_error_sq (controls : Fin k→Fin W) (answer : Bits k) (η : QState W) :
    stateNorm (η-good controls answer η)^2=failure controls answer η := by
  exact CoherentProjection.projection_error_sq (fun w => readout controls w=answer) (WithLp.toLp 2 η)

theorem good_error (controls : Fin k→Fin W) (answer : Bits k) (η : QState W) :
    stateNorm (η-good controls answer η)=Real.sqrt (failure controls answer η) := by
  rw [←good_error_sq]
  have hn : 0 ≤ stateNorm (η-good controls answer η) := norm_nonneg _
  exact (Real.sqrt_sq hn).symm

/-- On the unnormalized correct-answer subspace, the actual CNOT array
copies the one intended answer exactly while retaining all quantum work. -/
theorem copy_good (controls : Fin k→Fin W) (answer data : Bits k) (η : QState W) :
    runLayered (CoherentXorCopy.circuit controls) (attach data (good controls answer η))=
      attach (xorMask data answer) (good controls answer η) := by
  change runLayered (CoherentXorCopy.circuit controls)
      (∑ w,good controls answer η w • basis (Fin.append w data))=
        ∑ w,good controls answer η w • basis (Fin.append w (xorMask data answer))
  rw [←runLayeredLinearMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [map_smul,runLayeredLinearMap_apply,CoherentXorCopy.circuit_basis]
  by_cases h : readout controls w=answer
  · have hx : CoherentXorCopy.xorData controls w data=xorMask data answer := by
      funext i
      exact congrArg (xor (data i)) (congrFun h i)
    rw [hx]
  · simp only [good,if_neg h,zero_smul]

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeQuantumXorError. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute ControlledNativeGates

variable {W k : ℕ}

theorem run_error {n : ℕ} (U : Layered n) (φ ψ : QState n) :
    stateNorm (runLayered U φ-runLayered U ψ)=stateNorm (φ-ψ) := by
  rw [←runLayeredLinearMap_apply,←runLayeredLinearMap_apply,←map_sub,runLayeredLinearMap_apply]
  exact (circuitIsometry U).norm_map (WithLp.toLp 2 (φ-ψ))

theorem stateNorm_sub_rev {n : ℕ} (φ ψ : QState n) : stateNorm (φ-ψ)=stateNorm (ψ-φ) :=
  norm_sub_rev (WithLp.toLp 2 φ) (WithLp.toLp 2 ψ)

/-- A low Born failure probability controls the entire copied state. The
incorrect branch is retained; there is no postselection or discarded work. -/
theorem copy_error (controls : Fin k→Fin W) (answer data : Bits k) (η : QState W) :
    stateNorm (runLayered (CoherentXorCopy.circuit controls) (attach data η)-
      attach (xorMask data answer) η)≤2*Real.sqrt (failure controls answer η) := by
  have ht : stateNorm (runLayered (CoherentXorCopy.circuit controls) (attach data η)-
      attach (xorMask data answer) η)≤
      stateNorm (runLayered (CoherentXorCopy.circuit controls) (attach data η)-
        runLayered (CoherentXorCopy.circuit controls) (attach data (good controls answer η)))+
      stateNorm (runLayered (CoherentXorCopy.circuit controls) (attach data (good controls answer η))-
        attach (xorMask data answer) η) :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [run_error,attach_error,copy_good,attach_error,stateNorm_sub_rev (good controls answer η) η,
    good_error] at ht
  linarith

theorem left_attach (U : Layered W) (data : Bits k) (η : QState W) :
    runLayered (leftCircuit U) (attach data η)=attach data (runLayered U η) := by
  rw [attach_tensor,leftCircuit_tensor,attach_tensor]

theorem circuit_stages (U : Layered W) (controls : Fin k→Fin W) (data : Bits k) (η : QState W) :
    runLayered (circuit U controls) (attach data η)=
      runLayered (leftCircuit (inverseCircuit U))
        (runLayered (CoherentXorCopy.circuit controls) (attach data (runLayered U η))) := by
  have h : runLayered (circuit U controls) (attach data η)=
      runLayered (leftCircuit (inverseCircuit U))
        (runLayered (CoherentXorCopy.circuit controls) (runLayered (leftCircuit U) (attach data η))) := by
    simp only [circuit,runLayered,List.foldl_append]
  rw [h,left_attach]

/-- Compute, copy, and uncompute approximately realize a clean XOR oracle
with the original work state restored. The sole error is bounded by twice
the square root of the actual probability of an incorrect output. -/
theorem circuit_error (U : Layered W) (controls : Fin k→Fin W)
    (answer data : Bits k) (η : QState W) :
    stateNorm (runLayered (circuit U controls) (attach data η)-attach (xorMask data answer) η)≤
      2*Real.sqrt (failure controls answer (runLayered U η)) := by
  have hi : runLayered (leftCircuit (inverseCircuit U))
      (attach (xorMask data answer) (runLayered U η))=attach (xorMask data answer) η := by
    rw [left_attach,inverseCircuit_left]
  rw [circuit_stages,←hi,run_error]
  exact copy_error controls answer data (runLayered U η)

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeQuantumXorReference. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute ControlledNativeGates

open scoped BigOperators

variable {n r W k : ℕ}

/-- The final register is a retained coherent query or pool reference. -/
def referenced (η : Bits r → QState n) : QState (n+r) :=
  fun x => η (rightRegister x) (leftRegister x)

theorem referenced_append (η : Bits r → QState n) (x : Bits n) (i : Bits r) :
    referenced η (Fin.append x i)=η i x := by
  have hl : leftRegister (Fin.append x i)=x := by funext j;exact Fin.append_left x i j
  have hr : rightRegister (Fin.append x i)=i := by funext j;exact Fin.append_right x i j
  rw [referenced,hl,hr]

theorem referenced_sum (η : Bits r → QState n) : referenced η=∑ i,attach i (η i) := by
  funext x
  simp only [Finset.sum_apply,attach_tensor,tensorState]
  simp [referenced,basis]

theorem referenced_left (U : Layered n) (η : Bits r → QState n) :
    runLayered (leftCircuit U) (referenced η)=referenced (fun i => runLayered U (η i)) := by
  rw [referenced_sum,←runLayeredLinearMap_apply,map_sum,referenced_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [runLayeredLinearMap_apply,left_attach]

theorem referenced_sub (η ζ : Bits r → QState n) :
    referenced η-referenced ζ=referenced (fun i => η i-ζ i) := rfl

theorem referenced_norm_sq (η : Bits r → QState n) :
    stateNorm (referenced η)^2=∑ i,stateNorm (η i)^2 := by
  change ‖(WithLp.toLp 2 (referenced η) : EuclideanSpace ℂ (Bits (n+r)))‖^2=_
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ p : Bits n × Bits r,‖referenced η (Fin.append p.1 p.2)‖^2 := by
      apply Fintype.sum_equiv (qubitsAppendEquiv n r)
      intro x
      change ‖referenced η x‖^2=‖referenced η ((qubitsAppendEquiv n r).symm ((qubitsAppendEquiv n r) x))‖^2
      rw [Equiv.symm_apply_apply]
    _ = ∑ i,∑ x,‖η i x‖^2 := by
      simp only [referenced_append,Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (η i))).symm

theorem run_smul (U : Layered n) (a : ℂ) (η : QState n) :
    runLayered U (a • η)=a • runLayered U η := by
  rw [←runLayeredLinearMap_apply,map_smul,runLayeredLinearMap_apply]

theorem stateNorm_smul (a : ℂ) (η : QState n) : stateNorm (a • η)=‖a‖*stateNorm η :=
  norm_smul a (WithLp.toLp 2 η)

/-- A shared classical pool and its coherent query label remain in the
reference register. Thus errors add in squared norm with their actual
amplitude weights; no independence or pointwise success bound is used. -/
theorem referenced_circuit_error (U : Layered W) (controls : Fin k → Fin W)
    (answer data : Bits r → Bits k) (η : Bits r → QState W) (a : Bits r → ℂ) :
    stateNorm (runLayered (leftCircuit (circuit U controls))
      (referenced (fun i => a i • attach (data i) (η i)))-
      referenced (fun i => a i • attach (xorMask (data i) (answer i)) (η i))) ≤
      2*Real.sqrt (∑ i,‖a i‖^2*failure controls (answer i) (runLayered U (η i))) := by
  let ε : Bits r → ℝ := fun i => failure controls (answer i) (runLayered U (η i))
  have he (i : Bits r) : 0 ≤ ε i := failure_nonnegative _ _ _
  have hp (i : Bits r) :
      stateNorm (runLayered (circuit U controls) (a i • attach (data i) (η i))-
        a i • attach (xorMask (data i) (answer i)) (η i))^2 ≤ 4*‖a i‖^2*ε i := by
    rw [run_smul,←smul_sub,stateNorm_smul,mul_pow]
    have hh := circuit_error U controls (answer i) (data i) (η i)
    have hn : 0 ≤ stateNorm (runLayered (circuit U controls) (attach (data i) (η i))-
      attach (xorMask (data i) (answer i)) (η i)) := norm_nonneg _
    have hs : (Real.sqrt (ε i))^2=ε i := Real.sq_sqrt (he i)
    have hsq : stateNorm (runLayered (circuit U controls) (attach (data i) (η i))-
      attach (xorMask (data i) (answer i)) (η i))^2 ≤ 4*ε i := by
      dsimp [ε] at hs
      nlinarith [Real.sqrt_nonneg (ε i)]
    nlinarith [sq_nonneg ‖a i‖,mul_nonneg (sq_nonneg ‖a i‖) (sub_nonneg.mpr hsq)]
  rw [referenced_left,referenced_sub]
  have hsq := referenced_norm_sq (fun i =>
    runLayered (circuit U controls) (a i • attach (data i) (η i))-
      a i • attach (xorMask (data i) (answer i)) (η i))
  have hsum : (∑ i,stateNorm (runLayered (circuit U controls) (a i • attach (data i) (η i))-
      a i • attach (xorMask (data i) (answer i)) (η i))^2) ≤
      4*(∑ i,‖a i‖^2*ε i) := by
    calc
      _ ≤ ∑ i,4*‖a i‖^2*ε i := Finset.sum_le_sum (fun i _ => hp i)
      _ = _ := by simp only [mul_assoc,Finset.mul_sum]
  have hnonneg : 0 ≤ ∑ i,‖a i‖^2*ε i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (he i))
  have hsqrt := Real.sq_sqrt hnonneg
  have hnorm : 0 ≤ stateNorm (referenced (fun i =>
      runLayered (circuit U controls) (a i • attach (data i) (η i))-
      a i • attach (xorMask (data i) (answer i)) (η i))) := norm_nonneg _
  change _ ≤ 2*Real.sqrt (∑ i,‖a i‖^2*ε i)
  nlinarith [Real.sqrt_nonneg (∑ i,‖a i‖^2*ε i)]

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end P2MDyadicModule11

/- Helper module PhysicalXor. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

theorem failure_eq (F : MFamily) {l k : ℕ} (h : k ≤ F.outLen l) (input : Bits l) (answer : Bits k) :
    failure (controls F l k h) answer (runLayered (F.circ l) (basisInput input)) =
      outputProb F (List.ofFn input) (fun s => prefixBits k s ≠ answer) := by
  rw [MultiPre.prob_ofFn]
  apply Finset.sum_congr rfl
  intro w _
  have he : prefixBits k (List.ofFn fun j => w (F.outW l j)) = readout (controls F l k h) w := by
    funext i
    have hi : i.val < F.outLen l := i.isLt.trans_le h
    simp [prefixBits,readout,controls,hi]
    rfl
  rw [he]
  by_cases hread : readout (controls F l k h) w = answer <;> simp [hread]

/-- A single uniform machine runs each variable-length quantum query on its
exact length. On a fixed input width the actual forward/CNOT/inverse circuit
preserves an arbitrary joint reference and performs the prescribed XOR with
error charged solely to the original decoder's failure probabilities. -/
theorem physical_requests (T : MFamily) (hT : IsMQPT T) (q : Str → Str) (hq : Poly q)
    (f : Str × Str → Str) (hf : Poly f) :
    ∃ F : MFamily, IsMQPT F ∧
    (∀ (w : Str) (fail bad : Str → Prop), (∀ o tail, fail (f (w,o) ++ tail) → bad o) →
      outputProb F w fail ≤ outputProb T (q w) bad) ∧ ∀ {l k r : ℕ} (h : k ≤ F.outLen l)
      (input : Bits r → Bits l) (answer data : Bits r → Bits k) (amplitude : Bits r → ℂ)
      (bad : Bits r → Str → Prop),
      (∀ i o tail, prefixBits k (f (List.ofFn (input i),o) ++ tail) ≠ answer i → bad i o) →
      let init (i : Bits r) := basisInput (a := F.anc l) (input i)
      let actual := runLayered (leftCircuit (m := r) (circuit (F.circ l) (controls F l k h)))
        (referenced (fun i => amplitude i • attach (data i) (init i)))
      let ideal := referenced (fun i => amplitude i • attach (xorMask (data i) (answer i)) (init i))
      stateNorm (actual - ideal) ≤
        2*Real.sqrt (∑ i, ‖amplitude i‖^2*outputProb T (q (List.ofFn (input i))) (bad i)) := by
  obtain ⟨F,hF,hlaw⟩ := native_request T hT q hq f hf
  refine ⟨F,hF,hlaw,?_⟩
  intro l k r h input answer data amplitude bad hbad
  dsimp only
  apply (referenced_circuit_error (F.circ l) (controls F l k h) answer data _ amplitude).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖amplitude i‖)
  rw [failure_eq]
  exact hlaw (List.ofFn (input i)) _ _ (hbad i)

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule12

/- Helper module FramedQueryXor. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding (readS readS_append serializeBinaryWords_map)

open Integration9_9.TM2NativeAffineEncoding (readVector readVector_append)

open Integration9_9.TM2NativeAffineEmitter (serializeVector)

noncomputable section

def requestWord (w : Str) : Str := (readS w).2

@[fun_prop] theorem requestWord_poly : Poly requestWord := by unfold requestWord; fun_prop

def signedResult (s : Str × Str) : Str := serializeVector (readVector s.2).2 ++ s.1.map (fun _ => false)

@[fun_prop] theorem signedResult_poly : Poly signedResult := by unfold signedResult; fun_prop

theorem requestWord_frame (s pad : Str) : requestWord (encS s ++ pad) = s := by simp [requestWord,readS_append]

theorem protected_prefix (s tail : Str) {k l : ℕ} (h : k ≤ l) :
    prefixBits k (s ++ List.replicate l false ++ tail) = prefixBits k s := by
  funext i
  change ((s ++ List.replicate l false ++ tail)[i.val]?).getD false = (s[i.val]?).getD false
  rw [List.getElem?_append_left (by simp; omega)]
  by_cases hs : i.val < s.length
  · rw [List.getElem?_append_left hs]
  · have hi : s.length ≤ i.val := by omega
    rw [List.getElem?_append_right hi,List.getElem?_eq_none hi,List.getElem?_replicate,if_pos (by omega)]
    rfl

theorem fixed_width (F : MFamily) (T : MFamily) (w : Str)
    (hlaw : ∀ (fail bad : Str → Prop),
       (∀ o tail, fail (signedResult (w,o) ++ tail) → bad o) →
       outputProb F w fail ≤ outputProb T (requestWord w) bad) : w.length ≤ F.outLen w.length := by
  by_contra! hn
  let fail := fun s : Str => s.length < w.length
  have hbad := hlaw fail (fun _ => False) (by intro o tail h; simp [fail,signedResult] at h; omega)
  have htotal : outputProb F w fail = 1 := by
    simp only [outputProb,fail,List.length_ofFn,if_pos hn]
    simpa only [Complex.normSq_eq_norm_sq] using
      (runLayered_mass (F.circ w.length) (basisInput (a:=F.anc w.length) (toBits w))).trans (basisInput_mass _)
  rw [htotal] at hbad
  norm_num [outputProb] at hbad

/-- The queried word is length framed, so arbitrary zero padding leaves the
native decoder's argument unchanged. Its signed-vector output is copied to a
fixed-width target, even when different decoded vectors have different code lengths. -/
theorem signed_query_circuit (T : MFamily) (hT : IsMQPT T) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ widths : ∀ l, l ≤ F.outLen l,
    ∀ {n l k r : ℕ} (hk : k ≤ l) (x : Bits r → Bits l) (s : Bits r → Str) (pad : Bits r → Str)
      (hx : ∀ i, List.ofFn (x i) = encS (s i) ++ pad i)
      (z : Bits r → Fin n → ℤ) (data : Bits r → Bits k) (a : Bits r → ℂ),
      let U := leftCircuit (m:=r) (circuit (F.circ l) (controls F l k (hk.trans (widths l))))
      let init (i : Bits r) := basisInput (a := F.anc l) (x i)
      let want (i : Bits r) := prefixBits k (encVec encI (z i))
      let actual := runLayered U (referenced (fun i => a i • attach (data i) (init i)))
      let ideal := referenced (fun i => a i • attach (xorMask (data i) (want i)) (init i))
      stateNorm (actual - ideal) ≤
        2*Real.sqrt (∑ i, ‖a i‖^2 * outputProb T (s i) (fun o => ¬ encVec encI (z i) <+: o)) := by
  obtain ⟨F,hF,hlaw,hxor⟩ := physical_requests T hT requestWord requestWord_poly signedResult signedResult_poly
  have widths (l : ℕ) : l ≤ F.outLen l := by
    simpa using fixed_width F T (List.replicate l false) (hlaw _)
  refine ⟨F,hF,widths,?_⟩
  intro n l k r hk x s pad hx z data a
  dsimp only
  have htest (i : Bits r) (o tail : Str) :
      prefixBits k (signedResult (List.ofFn (x i),o) ++ tail) ≠ prefixBits k (encVec encI (z i)) → ¬encVec encI (z i) <+: o := by
    intro hfail hprefix
    obtain ⟨suffix,rfl⟩ := hprefix
    have hs : serializeVector (List.ofFn (z i)) = encVec encI (z i) := by
      simp only [serializeVector,serializeBinaryWords_map,encVec]
    apply hfail
    simp only [signedResult,readVector_append,hs,List.map_const',List.length_ofFn]
    exact protected_prefix _ _ hk
  have h := hxor (hk.trans (widths l)) x _ data a _ htest
  have hw (i) : requestWord (List.ofFn (x i)) = s i := by rw [hx i,requestWord_frame]
  simpa only [hw] using h

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity

open scoped BigOperators

theorem selected_value {k n : ℕ} (w : Fin k ↪ Fin n)
    (p : Bits k×OutsideBits w) (i : Fin k) : (wireBitsEquiv w).symm p (w i)=p.1 i :=
  congrFun (congrArg Prod.fst ((wireBitsEquiv w).apply_symm_apply p)) i

theorem split_update {k n : ℕ} (w : Fin k ↪ Fin n)
    (x : Bits n) (i : Fin k) (b : Bool) :
    wireBitsEquiv w (Function.update x (w i) b)=
      (Function.update (wireBitsEquiv w x).1 i b,(wireBitsEquiv w x).2) := by
  apply Prod.ext
  · funext j
    by_cases h : j=i
    · subst j; simp [wireBitsEquiv]
    · have hw : w j≠w i := w.injective.ne h
      simp [wireBitsEquiv,Function.update_of_ne hw,Function.update_of_ne h]
  · funext j
    have h : j.val≠w i := fun he => j.property ⟨i,he.symm⟩
    simp [wireBitsEquiv,Function.update_of_ne h]

theorem unsplit_update {k n : ℕ} (w : Fin k ↪ Fin n)
    (p : Bits k×OutsideBits w) (i : Fin k) (b : Bool) :
    Function.update ((wireBitsEquiv w).symm p) (w i) b=
      (wireBitsEquiv w).symm (Function.update p.1 i b,p.2) := by
  apply (wireBitsEquiv w).injective
  rw [split_update,Equiv.apply_symm_apply,Equiv.apply_symm_apply]

theorem relocate_apply1 {k n : ℕ} (w : Fin k ↪ Fin n)
    (M : Matrix Bool Bool ℂ) (i : Fin k) (ψ : QState n) :
    splitState w (apply1 M (w i) ψ)=
      fun p => apply1 M i (fun x => splitState w ψ (x,p.2)) p.1 := by
  funext p
  simp only [splitState,apply1,selected_value,unsplit_update]

/-- All spectator amplitudes are retained, including entanglement with the
selected register. No product-state assumption is used. -/
theorem relocateInstr_split {k n : ℕ} (w : Fin k ↪ Fin n) (g : Instr k) (ψ : QState n) :
    splitState w ((relocateInstr w g).apply ψ)=
      fun p => g.apply (fun x => splitState w ψ (x,p.2)) p.1 := by
  cases g with
  | h i => exact relocate_apply1 w hMat i ψ
  | s i => exact relocate_apply1 w sMat i ψ
  | t i => exact relocate_apply1 w tMat i ψ
  | x i => exact relocate_apply1 w xMat i ψ
  | cnot i j h =>
    funext p
    simp only [relocateInstr,Instr.apply,cnotState,splitState,selected_value,unsplit_update]

theorem relocateLayer_split {k n : ℕ} (w : Fin k ↪ Fin n) (gates : List (Instr k))
    (ψ : QState n) :
    splitState w (runLayer (gates.map (relocateInstr w)) ψ)=
      fun p => runLayer gates (fun x => splitState w ψ (x,p.2)) p.1 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    change splitState w (runLayer (gs.map (relocateInstr w)) ((relocateInstr w g).apply ψ))=_
    rw [ih,relocateInstr_split]
    rfl

/-- The actual relocated whole circuit acts on every reference slice. -/
theorem relocateCircuit_split {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k)
    (ψ : QState n) :
    splitState w (runLayered (relocateCircuit w circuit) ψ)=
      fun p => runLayered circuit (fun x => splitState w ψ (x,p.2)) p.1 := by
  induction circuit generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    change splitState w (runLayered (relocateCircuit w rest)
      (runLayer (layer.map (relocateInstr w)) ψ))=_
    rw [ih,relocateLayer_split]
    rfl

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule14

/- Helper module SparseOracle. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1350000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates

noncomputable section

variable {n l k a r : ℕ} {I : Type} [Fintype I]

private theorem basisInput_eq (x : Bits l) : basisInput (a:=a) x = basis (Fin.append x (fun _ : Fin (a+1) => false)) := by
  funext y
  unfold basisInput basis
  congr 1
  apply propext
  constructor
  · rintro ⟨hl,hr⟩
    funext i
    induction i using Fin.addCases with
    | left t => simpa using hl t
    | right t => simpa using hr t
  · rintro rfl
    exact ⟨Fin.append_left _ _,Fin.append_right _ _⟩

theorem attached_basis {W : ℕ} (x : Bits W) (d : Bits k) :
    attach d (basis x) = basis (Fin.append x d) := by
  rw [attach_tensor]
  funext y
  obtain ⟨⟨z,t⟩,rfl⟩ := (qubitsAppendEquiv W k).symm.surjective y
  change (if (qubitsAppendEquiv W k ((qubitsAppendEquiv W k).symm (z,t))).1=x then 1 else 0)*
      (if (qubitsAppendEquiv W k ((qubitsAppendEquiv W k).symm (z,t))).2=d then 1 else 0) =
      if (qubitsAppendEquiv W k).symm (z,t)=(qubitsAppendEquiv W k).symm (x,d) then 1 else 0
  simp only [Equiv.apply_symm_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem oracle_amplitudes [Nonempty I] (x : I → Bits l) (d : I → Bits k) (tag : I ↪ Bits r) (v : I → ℂ) :
    basisEmbedding (oracleEmbedding (a:=a) x d tag) v =
      referenced (fun q => basisEmbedding tag v q • attach (d (Function.invFun tag q)) (basisInput (a:=a) (x (Function.invFun tag q)))) := by
  classical
  funext u
  obtain ⟨⟨t,q⟩,rfl⟩ := (qubitsAppendEquiv (l+(a+1)+k) r).symm.surjective u
  change _ = referenced _ (Fin.append t q)
  rw [referenced_append,basisInput_eq,attached_basis,Pi.smul_apply,smul_eq_mul]
  by_cases hq : q ∈ Set.range tag
  · obtain ⟨i,rfl⟩ := hq
    rw [basisEmbedding_at,Function.leftInverse_invFun tag.injective]
    by_cases ht : t = Fin.append (Fin.append (x i) (fun _ : Fin (a+1) => false)) (d i)
    · subst t
      rw [basis,if_pos rfl,mul_one]
      exact basisEmbedding_at (oracleEmbedding (a:=a) x d tag) v i
    · rw [basis,if_neg ht,mul_zero,basisEmbedding_outside]
      rintro ⟨p,h⟩
      change (qubitsAppendEquiv (l+(a+1)+k) r).symm (Fin.append (Fin.append (x p) (fun _ : Fin (a+1) => false)) (d p),tag p)=_ at h
      have eq := (qubitsAppendEquiv (l+(a+1)+k) r).symm.injective h
      have hi := tag.injective (congrArg (fun p : Bits (l+(a+1)+k) × Bits r => p.2) eq)
      subst p
      exact ht (congrArg (fun p : Bits (l+(a+1)+k) × Bits r => p.1) eq).symm
  · rw [basisEmbedding_outside tag v q hq,zero_mul,basisEmbedding_outside]
    rintro ⟨i,h⟩
    change (qubitsAppendEquiv (l+(a+1)+k) r).symm (Fin.append (Fin.append (x i) (fun _ : Fin (a+1) => false)) (d i),tag i)=_ at h
    have eq := (qubitsAppendEquiv (l+(a+1)+k) r).symm.injective h
    exact hq ⟨i,congrArg (fun p : Bits (l+(a+1)+k) × Bits r => p.2) eq⟩

theorem sparse_sum [Nonempty I] (tag : I ↪ Bits r) (v : I → ℂ) (f : I → ℝ) :
    (∑ q, ‖basisEmbedding tag v q‖^2*f (Function.invFun tag q)) = ∑ i, ‖v i‖^2*f i := by
  classical
  let g (q : Bits r) := ‖basisEmbedding tag v q‖^2*f (Function.invFun tag q)
  calc
    _ = ∑ q ∈ Finset.univ.image tag, g q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro q _ hq
      have hx : q ∉ Set.range tag := by rintro ⟨i,rfl⟩; exact hq (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
      simp [g,basisEmbedding_outside tag v q hx]
    _ = ∑ i, g (tag i) := Finset.sum_image (fun _ _ _ _ h => tag.injective h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [g,basisEmbedding_at,Function.leftInverse_invFun tag.injective i]

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule15

/- Helper module NativeErasure. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1700000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open CoherentComputeUncompute QAlgorithms QAlgorithms.Complexity QuantumXorOracle ControlledNativeGates

open SharedPoolCoherence

noncomputable section

/-- Erasure on arbitrary finite physical labels, including genuine residual
registers and independent finite preparation garbage. The authentic shared
decoder circuits erase the entire preloaded fixed-width signed answer. -/
theorem physical_erasure (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ widths : ∀ l, l ≤ F.outLen l,
    ∀ {n m l k r : ℕ} (hk : k ≤ l) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ)
    (prec : ℕ) (pool : Fin m → Fin n → ℤ) (I : Type) [Fintype I] [Nonempty I] (tag : I ↪ Bits r)
    (q : I → Query B R) (v : I → ℂ) (x : I → Bits l)
    (_hx : ∀ i, ∃ pad : Str, List.ofFn (x i) = encS (word prec pool (q i)) ++ pad),
    let d (i : I) := prefixBits k (encVec encI (q i).answer)
    let init := basisEmbedding (oracleEmbedding (a:=F.anc l) x d tag) v
    let goal := basisEmbedding (oracleEmbedding (a:=F.anc l) x (fun _ => (0:Bits k)) tag) v
    let U := leftCircuit (m:=r) (circuit (F.circ l) (controls F l k (hk.trans (widths l))))
    ∀ (actual : QState (l+(F.anc l+1)+k+r)),
    stateNorm (runLayered U actual-goal) ≤ stateNorm (actual-init)+2*Real.sqrt (failureMass C prec pool q v) := by
  obtain ⟨F,hF,widths,h⟩ := signed_query_circuit C hC
  refine ⟨F,hF,widths,?_⟩
  intro n m l k r hk B R prec pool I _ _ tag q v x hx
  dsimp only
  intro actual
  choose pad hpad using hx
  let idx := Function.invFun tag
  let d (i : I) := prefixBits k (encVec encI (q i).answer)
  let init := basisEmbedding (oracleEmbedding (a:=F.anc l) x d tag) v
  let goal := basisEmbedding (oracleEmbedding (a:=F.anc l) x (fun _ => (0:Bits k)) tag) v
  let U := leftCircuit (m:=r) (circuit (F.circ l) (controls F l k (hk.trans (widths l))))
  have he := h hk (x ∘ idx) ((fun i => word prec pool (q i)) ∘ idx) (pad ∘ idx) (fun a => hpad (idx a))
    ((fun i => (q i).answer) ∘ idx) (d ∘ idx) (basisEmbedding tag v)
  have hz (a : Bits r) : xorMask (d (idx a)) (prefixBits k (encVec encI (q (idx a)).answer))=0 := by
    funext i
    change xor _ _ = false
    exact Bool.xor_self _
  change stateNorm (runLayered U actual-goal) ≤ stateNorm (actual-init)+_
  apply (norm_sub_le_norm_sub_add_norm_sub (WithLp.toLp 2 (runLayered U actual))
    (WithLp.toLp 2 (runLayered U init)) (WithLp.toLp 2 goal)).trans
  change stateNorm (runLayered U actual-runLayered U init)+stateNorm (runLayered U init-goal) ≤ _
  rw [run_error]
  apply add_le_add (le_refl _)
  dsimp only [Function.comp_apply] at he
  rw [show init = _ from oracle_amplitudes x d tag v,show goal = _ from oracle_amplitudes x (fun _ => (0:Bits k)) tag v]
  simp only [hz] at he
  have hsum := sparse_sum tag v (fun i => outputProb C (word prec pool (q i)) (fun o => ¬encVec encI (q i).answer <+: o))
  change (∑ i, ‖basisEmbedding tag v i‖^2 * outputProb C (word prec pool (q (idx i)))
    (fun o => ¬encVec encI (q (idx i)).answer <+: o)) = failureMass C prec pool q v at hsum
  rw [hsum] at he
  exact he

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end P2MDyadicModule16

/- Helper module Outcome. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeQFTPlanCompile CoherentDecoder

open CoherentProjection GaussianPoissonSeries FiniteLatticeFourier IntegerBasis RegevLWE.GaussConv

noncomputable section

variable {n b : ℕ}

theorem reindex_norm {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (v : EuclideanSpace ℂ Y) :
    ‖reindex e v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end

end GridReadout.Axis

end P2MDyadicModule17

/- Helper module OraclePlacement. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute

noncomputable section

def relabel {p N : ℕ} (e : Fin p ≃ Fin N) (v : QState p) : QState N := v ∘ wirePull e

theorem relabel_error {p N : ℕ} (e : Fin p ≃ Fin N) (v w : QState p) :
    stateNorm (relabel e v-relabel e w)=stateNorm (v-w) :=
  GridReadout.Axis.reindex_norm (wirePull e) (WithLp.toLp 2 (v-w))

theorem relabel_emb {p N : ℕ} {I : Type} [Fintype I] (e : Fin p ≃ Fin N) (f : I ↪ Bits p) (v : I→ℂ) :
    relabel e (basisEmbedding f v) = basisEmbedding (f.trans (wirePull e).symm.toEmbedding) v := by
  funext x
  obtain ⟨t,rfl⟩ := (wirePull e).symm.surjective x
  change basisEmbedding f v ((wirePull e) ((wirePull e).symm t))=_
  rw [Equiv.apply_symm_apply]
  by_cases ht : t ∈ Set.range f
  · obtain ⟨i,rfl⟩ := ht
    exact (basisEmbedding_at f v i).trans (basisEmbedding_at (f.trans (wirePull e).symm.toEmbedding) v i).symm
  · rw [basisEmbedding_outside f v t ht,basisEmbedding_outside]
    rintro ⟨i,h⟩
    exact ht ⟨i,(wirePull e).symm.injective h⟩

theorem relabel_run {p N : ℕ} (e : Fin p ≃ Fin N) (U : Layered p) (v : QState p) :
    runLayered (relocateCircuit e.toEmbedding U) (relabel e v) = relabel e (runLayered U v) := by
  funext x
  let w := e.toEmbedding
  let t := wireBitsEquiv w x
  have he := congrFun (relocateCircuit_split w U (relabel e v)) t
  have hy : (fun y => splitState w (relabel e v) (y,t.2))=v := by
    funext y
    change v (((wireBitsEquiv w).symm (y,t.2)) ∘ e)=v y
    apply congrArg v
    exact congrArg Prod.fst ((wireBitsEquiv w).apply_symm_apply (y,t.2))
  rw [hy] at he
  change runLayered (relocateCircuit w U) (relabel e v) ((wireBitsEquiv w).symm ((wireBitsEquiv w) x))= runLayered U v t.1 at he
  rw [Equiv.symm_apply_apply] at he
  exact he

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule18

/- Helper module RunSerialized. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute QuantumXorOracle

open PaddedDecoder SharedPoolCoherence

noncomputable section

variable {H K L J A : ℕ}

theorem _root_.solution (C : MFamily) (hC : IsMQPT C) :
    ∃ F : MFamily, IsMQPT F ∧ ∃ widths : ∀ l, l ≤ F.outLen l,
    ∀ {n m H K L J : ℕ} (hkl : K ≤ L) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ)
    (prec : ℕ) (pool : Fin m → Fin n → ℤ) (I : Type) [Fintype I] [Nonempty I]
    (h : I → Bits H) (j : I → Bits J) (hi : Function.Injective (fun i => (h i,j i)))
    (q : I → Query B R) (v : I → ℂ) (x : I → Bits L)
    (_hx : ∀ i, ∃ pad : Str, List.ofFn (x i) = encS (word prec pool (q i)) ++ pad),
    let d (i : I) := prefixBits K (encVec encI (q i).answer)
    let init := basisEmbedding (emittedBasis (A:=F.anc L) h j hi x d) v
    let goal := basisEmbedding (emittedBasis (A:=F.anc L) h j hi x (fun _ => (0:Bits K))) v
    let U := leftCircuit (m:=H+J) (circuit (F.circ L) (controls F L K (hkl.trans (widths L))))
    let V := relocateCircuit (oraclePerm H K L J (F.anc L+1)).toEmbedding U
    ∀ (actual : QState (H+K+L+J+(F.anc L+1))),
    stateNorm (runLayered V actual-goal) ≤ stateNorm (actual-init)+2*Real.sqrt (failureMass C prec pool q v) := by
  obtain ⟨F,hF,widths,he⟩ := physical_erasure C hC
  refine ⟨F,hF,widths,?_⟩
  intro n m H K L J hkl B R prec pool I _ _ h j hi q v x hx
  dsimp only
  intro actual
  let tag := frontRear h j hi
  let e := oraclePerm H K L J (F.anc L+1)
  let before := relabel e.symm actual
  have hb : relabel e before = actual := by
    funext i
    change actual ((i ∘ e) ∘ e.symm)=actual i
    congr 1
    funext t;simp
  have er := he hkl B R prec pool I tag q v x hx before
  change stateNorm (runLayered (relocateCircuit e.toEmbedding _) actual - basisEmbedding ((oracleEmbedding _ _ tag).trans (wirePull e).symm.toEmbedding) v) ≤
    stateNorm (actual-basisEmbedding ((oracleEmbedding _ _ tag).trans (wirePull e).symm.toEmbedding) v)+_
  rw [←hb,relabel_run,←relabel_emb,←relabel_emb,relabel_error,relabel_error]
  exact er

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end P2MDyadicModule19
#print axioms solution
