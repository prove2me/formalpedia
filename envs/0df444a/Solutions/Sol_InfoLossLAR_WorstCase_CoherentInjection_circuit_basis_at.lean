-- Prove2me | solution 1 for InfoLossLAR.WorstCase.CoherentInjection.circuit_basis_at
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:02:17.391318+00:00
-- url     : https://prove2.me/submissions/5f0d53cf-150b-4260-9aa0-bf3a45ccacd6

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_ReversibleStringInjection
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_ShorAlgorithms_QFT_Circuit
set_option Elab.async true

set_option linter.all false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.ControlledLetterPlan
end InfoLossLAR.WorstCase.ControlledLetterPlan

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength

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

namespace QAlgorithms.Papers.Independent.Renew46.P12
end QAlgorithms.Papers.Independent.Renew46.P12

namespace QMCNumericRuntime
end QMCNumericRuntime

namespace Turing
end Turing

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

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule3

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

namespace BooleanGate

theorem assign_other {n : ℕ} (g : BooleanGate n) (x : Bits n) (i : Fin n)
    (hi : i ≠ g.target) : g.assign x i = x i := Function.update_of_ne hi _ _

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

end InfoLossLAR.WorstCase

end P2MDyadicModule3

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule4

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

end P2MDyadicModule4

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule5

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

end BooleanProgram

end InfoLossLAR.WorstCase

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule6

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

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule7

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

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule8

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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule9

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

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule10

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Papers.Independent.Renew46.P12

open scoped BigOperators

/-- Reassemble the physical register after selecting local and spectator wires. -/
noncomputable def unsplitState {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : QState n := fun x => ψ (wireBitsEquiv w x)

@[simp] theorem split_unsplit {k n : ℕ} (w : Fin k ↪ Fin n)
    (ψ : Bits k × OutsideBits w → ℂ) : splitState w (unsplitState w ψ)=ψ := by
  funext p
  simp only [splitState,unsplitState,Equiv.apply_symm_apply]

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule11

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open FiniteGateTransport

open scoped BigOperators

variable {D W I : Type*} [Fintype D] [Fintype W] [DecidableEq W]

noncomputable def tensor (v : D → ℂ) (w : W) : D×W → ℂ := fun p => v p.1*basis w p.2

/-- Reversible work computation acts on the full work register, retaining the
fresh data register as an arbitrary coherent reference. -/
noncomputable def onWork (U : (W → ℂ) →ₗ[ℂ] (W → ℂ)) :
    (D×W → ℂ) →ₗ[ℂ] (D×W → ℂ) where
  toFun ψ p := U (fun r => ψ (p.1,r)) p.2
  map_add' ψ φ := by
    funext p
    change U ((fun r => ψ (p.1,r))+(fun r => φ (p.1,r))) p.2=_
    rw [map_add]
    rfl
  map_smul' c ψ := by
    funext p
    change U (c • (fun r => ψ (p.1,r))) p.2=_
    rw [map_smul]
    rfl

theorem onWork_tensor (U : (W → ℂ) →ₗ[ℂ] (W → ℂ)) (v : D → ℂ) (w r : W)
    (hU : U (basis w)=basis r) : onWork U (tensor v w)=tensor v r := by
  funext p
  change U ((v p.1) • basis w) p.2=v p.1*basis r p.2
  rw [map_smul,hU]
  rfl

/-- Actual circuit inversion supplies cleanup from the basis semantics of
the forward computation; no independent inverse-oracle assumption is needed. -/
theorem inverse_basis {n : ℕ} (gates : QAlgorithms.Complexity.Layered n)
    (input computed : QAlgorithms.Complexity.Bits n)
    (h : runLayeredLinearMap gates (basis input)=basis computed) :
    runLayeredLinearMap (inverseCircuit gates) (basis computed)=basis input := by
  rw [←h,runLayeredLinearMap_apply,runLayeredLinearMap_apply]
  exact inverseCircuit_left gates (basis input)

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeCircuitInitializedEmbedding. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity CoherentComputeUncompute

open scoped BigOperators

/-- Put a local quantum state into public wires and initialize exactly the
complementary physical wires. This is an amplitude specification. -/
noncomputable def initializedWires {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (ψ : QState k) : QState n :=
  unsplitState w (fun p => ψ p.1*basis outside p.2)

/-- The actual relocated whole circuit implements its local action with
all complementary wires present and fixed, with no assumed state-preparation
oracle and no renormalization. -/
theorem relocateCircuit_initialized {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (circuit : Layered k) (ψ : QState k) :
    runLayered (relocateCircuit w circuit) (initializedWires w outside ψ)=
      initializedWires w outside (runLayered circuit ψ) := by
  have hh : splitState w (runLayered (relocateCircuit w circuit) (initializedWires w outside ψ))=
      splitState w (initializedWires w outside (runLayered circuit ψ)) := by
        rw [relocateCircuit_split]
        simp only [initializedWires,split_unsplit]
        funext p
        have hs : (fun x => ψ x*basis outside p.2)=basis outside p.2 • ψ := by
          funext x;simp only [Pi.smul_apply,smul_eq_mul,mul_comm]
        rw [hs,←runLayeredLinearMap_apply,map_smul,runLayeredLinearMap_apply]
        simp only [Pi.smul_apply,smul_eq_mul,mul_comm]
  funext x
  have he := congrFun hh (wireBitsEquiv w x)
  simpa only [splitState,Equiv.symm_apply_apply] using he

end InfoLossLAR.WorstCase.FiniteGateTransport

end

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeCircuitRelocationBasis. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity CoherentComputeUncompute

theorem initializedWires_basis {k n : ℕ} (w : Fin k ↪ Fin n)
    (outside : OutsideBits w) (localBits : Bits k) :
    initializedWires w outside (basis localBits)=
      basis ((wireBitsEquiv w).symm (localBits,outside)) := by
  classical
  funext x
  have he : x=(wireBitsEquiv w).symm (localBits,outside) ↔
      (wireBitsEquiv w x).1=localBits ∧ (wireBitsEquiv w x).2=outside := by
    rw [Equiv.eq_symm_apply,Prod.mk.injEq]
  simp only [initializedWires,unsplitState,basis,he]
  split_ifs <;> simp_all

/-- Relocating a literal circuit preserves every physical bit outside its
wire image, even when those bits vary between coherent input branches. -/
theorem relocateCircuit_basis {k n : ℕ} (w : Fin k ↪ Fin n)
    (circuit : Layered k) (input output : Bits n)
    (hlocal : runLayered circuit (basis ((wireBitsEquiv w input).1))=
      basis ((wireBitsEquiv w output).1))
    (houtside : (wireBitsEquiv w input).2=(wireBitsEquiv w output).2) :
    runLayered (relocateCircuit w circuit) (basis input)=basis output := by
  have hi : basis input=initializedWires w (wireBitsEquiv w input).2
      (basis (wireBitsEquiv w input).1) := by
    rw [initializedWires_basis,Prod.mk.eta,Equiv.symm_apply_apply]
  rw [hi,relocateCircuit_initialized,hlocal,houtside,initializedWires_basis,
    Prod.mk.eta,Equiv.symm_apply_apply]

end InfoLossLAR.WorstCase.FiniteGateTransport

end

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule14

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

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule15

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

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule16

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

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule17

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

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule18

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

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule19

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

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule20

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

/-- This is the literal Clifford+T circuit on the platform's actual input basis state. -/
theorem machineCircuit_basis (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks : ℕ) (word : List Bool) :
    runLayered (machineCircuit hw program input main initialState ticks word.length)
      (basisInput (toBits word)) = computationalBasis (fun j =>
        BooleanProgram.run word.length (machineProgram hw program input main initialState ticks word.length).ops
          (wordExtension word) j.val) := by
  rw [basisInput_eq_computationalBasis, wordExtension_basis]
  exact BooleanProgram.circuit_basis _ _
    (machineProgram_valid hw program input main initialState ticks word.length).1
    (wordExtension word) (fun i hi _ => wordExtension_after word i hi)

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

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule21

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

/-- The real fixed-gate circuit computes the machine's complete deterministic basis output. -/
theorem circuit_basis (word : Str) :
    runLayered (circuit P word.length) (basisInput (toBits word)) = computationalBasis (result P word) :=
  machineCircuit_basis _ _ _ _ _ _ word

/-- An actual output wire gives each present/absent symbol of the encoded function output. -/
theorem output_correct (word : Str) (i : Fin (capacity P word.length)) (b : Option Bool) :
    result P word (outputWire P word.length i b) = decide (b = (f word)[i.val]?) := by
  have hh := machineCircuit_output (capacity_pos P word.length) P.machine.code P.machine.input P.machine.main
    P.machine.initial (P.time.eval word.length) word (by unfold capacity; omega)
    (.inr (.inr (P.machine.output, i, b)))
  rw [final_configuration P word] at hh
  simpa only [result, outputWire, compiled, configurationBit, Machine.finalCfg, ↓reduceIte] using hh

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeNativeWordCoherentCompute. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- Physical ordering is the complete work register followed by data. -/
def assembleMap (W k : ℕ) : (Bits k×Bits W → ℂ) →ₗ[ℂ] QState (W+k) where
  toFun φ x :=φ (fun j => x (Fin.natAdd W j),fun j => x (j.castAdd k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def separateMap (W k : ℕ) : QState (W+k) →ₗ[ℂ] (Bits k×Bits W → ℂ) where
  toFun φ pair :=φ (Fin.append pair.2 pair.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem separate_assemble (W k : ℕ) (φ : Bits k×Bits W → ℂ) :
    separateMap W k (assembleMap W k φ)=φ := by
  funext pair
  simp only [separateMap,assembleMap,LinearMap.coe_mk,AddHom.coe_mk,Fin.append_left,Fin.append_right]

@[simp] theorem assemble_separate (W k : ℕ) (φ : QState (W+k)) :
    assembleMap W k (separateMap W k φ)=φ := by
  funext x
  change φ (Fin.append (fun j => x (j.castAdd k)) (fun j => x (Fin.natAdd W j)))=φ x
  exact congrArg φ ((qubitsAppendEquiv W k).symm_apply_apply x)

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

variable {I : Type*} [Fintype I]

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeNativeWordLift. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

theorem append_update {W k : ℕ} (work : Bits W) (data : Bits k) (i : Fin W) (b : Bool) :
    Function.update (Fin.append work data) (i.castAdd k) b=Fin.append (Function.update work i b) data := by
  funext x
  refine Fin.addCases ?_ ?_ x
  · intro j
    by_cases h : j=i
    · subst j;simp
    · have hn : j.castAdd k≠i.castAdd k := by intro he;exact h (Fin.castAdd_inj.mp he)
      simp only [Function.update_of_ne hn,Fin.append_left,Function.update_of_ne h]
  · intro j
    have hn : Fin.natAdd W j≠i.castAdd k := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    simp only [Function.update_of_ne hn,Fin.append_right]

theorem separate_instr {W k : ℕ} (gate : Instr W) (ψ : QState (W+k)) :
    separateMap W k ((extendInstr k gate).apply ψ)=
      fun pair => gate.apply (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  funext pair
  cases gate <;>
    simp [extendInstr,Instr.apply,apply1,cnotState,append_update,separateMap]

theorem separate_layer {W k : ℕ} (gates : List (Instr W)) (ψ : QState (W+k)) :
    separateMap W k (runLayer (gates.map (extendInstr k)) ψ)=
      fun pair => runLayer gates (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons gate rest ih =>
    simp only [List.map_cons,runLayer,List.foldl_cons] at *
    rw [ih]
    funext pair
    have he : (fun work => separateMap W k ((extendInstr k gate).apply ψ) (pair.1,work))=
        gate.apply (fun work => separateMap W k ψ (pair.1,work)) := by
      funext work
      exact congrFun (separate_instr gate ψ) (pair.1,work)
    rw [he]

theorem separate_circuit {W k : ℕ} (gates : Layered W) (ψ : QState (W+k)) :
    separateMap W k (runLayered (extendCircuit k gates) ψ)=
      fun pair => runLayered gates (fun work => separateMap W k ψ (pair.1,work)) pair.2 := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons layer rest ih =>
    simp only [extendCircuit,List.map_cons,runLayered,List.foldl_cons] at *
    rw [ih]
    funext pair
    have he : (fun work => separateMap W k (runLayer (layer.map (extendInstr k)) ψ) (pair.1,work))=
        runLayer layer (fun work => separateMap W k ψ (pair.1,work)) := by
      funext work
      exact congrFun (separate_layer layer ψ) (pair.1,work)
    rw [he]

def workAction {W : ℕ} (gates : Layered W) (k : ℕ) : QState (W+k) →ₗ[ℂ] QState (W+k) :=
  (assembleMap W k).comp ((CoherentComputeUncompute.onWork (runLayeredLinearMap gates)).comp (separateMap W k))

/-- This tensor action is exactly the literal extended original circuit. -/
theorem extendCircuit_semantics {W : ℕ} (gates : Layered W) (k : ℕ) (ψ : QState (W+k)) :
    runLayered (extendCircuit k gates) ψ=workAction gates k ψ := by
  have hh : separateMap W k (runLayered (extendCircuit k gates) ψ)=
      CoherentComputeUncompute.onWork (runLayeredLinearMap gates) (separateMap W k ψ) := by
    simpa only [CoherentComputeUncompute.onWork,LinearMap.coe_mk,AddHom.coe_mk,runLayeredLinearMap_apply] using
      separate_circuit gates ψ
  have he:=congrArg (assembleMap W k) hh
  rw [assemble_separate] at he
  exact he

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeCoherentXorCopy. -/
section P2MDyadicModule24

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

/-- The full finite circuit has the same XOR action on arbitrary coherent
data amplitudes while its computed work basis remains unchanged. -/
theorem circuit_tensor (controls : Fin k → Fin W) (work : Bits W) (v : QState k) :
    runLayered (circuit controls) (assembleMap W k (tensor v work))=
      assembleMap W k (tensor (fun data => v (xorData controls work data)) work) := by
  have hs : assembleMap W k (tensor v work)=∑ data : Bits k,v data • basis (Fin.append work data) := by
    funext x
    simp only [assembleMap,LinearMap.coe_mk,AddHom.coe_mk,tensor,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    have hx : x=Fin.append (fun i => x (i.castAdd k)) (fun i => x (Fin.natAdd W i)) :=
      ((qubitsAppendEquiv W k).symm_apply_apply x).symm
    rw [hx]
    by_cases hw : (fun i => x (i.castAdd k))=work <;> simp [basis,append_eq_iff,hw]
  rw [hs,←runLayeredLinearMap_apply,map_sum]
  simp only [map_smul,runLayeredLinearMap_apply,circuit_basis]
  have hi : Function.Involutive (xorData controls work) := by intro d;funext j;simp [xorData,Bool.xor_assoc]
  have he := Fintype.sum_equiv (hi.toPerm (xorData controls work))
    (fun d => v d • basis (Fin.append work (xorData controls work d)))
    (fun d => v (xorData controls work d) • basis (Fin.append work d)) (by
      intro d
      change v d • basis (Fin.append work (xorData controls work d))=
        v (xorData controls work (xorData controls work d)) • basis (Fin.append work (xorData controls work d))
      rw [hi])
  rw [he]
  have hs' : assembleMap W k (tensor (fun data => v (xorData controls work data)) work)=
      ∑ data : Bits k,v (xorData controls work data) • basis (Fin.append work data) := by
    funext x
    simp only [assembleMap,LinearMap.coe_mk,AddHom.coe_mk,tensor,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    have hx : x=Fin.append (fun i => x (i.castAdd k)) (fun i => x (Fin.natAdd W i)) :=
      ((qubitsAppendEquiv W k).symm_apply_apply x).symm
    rw [hx]
    by_cases hw : (fun i => x (i.castAdd k))=work <;> simp [basis,append_eq_iff,hw]
  exact hs'.symm

end InfoLossLAR.WorstCase.CoherentXorCopy

end

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeCoherentClassicalOracle. -/
section P2MDyadicModule25

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f : Str → Str} (P : PolyProgram id id f)

def initialWork (n : ℕ) (word : Str) : Bits (width P n) := fun i => wordExtension word i.val

def computedWork (word : Str) : Bits (width P word.length) := result P word

def inputState (word : Str) (v : QState (capacity P word.length)) : QState (width P word.length+capacity P word.length) :=
  assembleMap _ _ (tensor v (initialWork P word.length word))

def maskedData (word : Str) (data : Bits (capacity P word.length)) : Bits (capacity P word.length) :=
  fun i => xor (data i) (wordExtension (f word) i.val)

def cleanState (word : Str) (v : QState (capacity P word.length)) : QState (width P word.length+capacity P word.length) :=
  inputState P word (fun data => v (maskedData P word data))

theorem base_computes (word : Str) :
    runLayeredLinearMap (base P word.length) (basis (initialWork P word.length word))=basis (computedWork P word) := by
  have h := PolyProgramCircuit.circuit_basis P word
  rw [basisInput_eq_computationalBasis,wordExtension_basis] at h
  rw [runLayeredLinearMap_apply]
  exact h

theorem inverse_computed (word : Str) :
    runLayeredLinearMap (inverseCircuit (base P word.length)) (basis (computedWork P word))=
      basis (initialWork P word.length word) :=
  CoherentComputeUncompute.inverse_basis _ _ _ (base_computes P word)

theorem control_value (word : Str) (i : Fin (capacity P word.length)) :
    computedWork P word (controls P word.length i)=wordExtension (f word) i.val := by
  change result P word (outputWire P word.length i (some true))=wordExtension (f word) i.val
  rw [output_correct]
  unfold wordExtension
  cases h : (f word)[i.val]? with
  | none => simp [h]
  | some bit => cases bit <;> simp [h]

theorem xorData_result (word : Str) (data : Bits (capacity P word.length)) :
    CoherentXorCopy.xorData (controls P word.length) (computedWork P word) data=maskedData P word data := by
  funext i
  simp only [CoherentXorCopy.xorData,control_value,maskedData]

/- The actual compute/output-XOR/inverse circuit evaluates the native
polynomial-time function without leaving any of its machine workspace.
Its original input remains, and the target register may be in any coherent state. -/
section
attribute [local irreducible] initialWork computedWork controls base maskedData width capacity
theorem fullCircuit_exact (word : Str) (v : QState (capacity P word.length)) :
    runLayered (fullCircuit P word.length) (inputState P word v)=cleanState P word v := by
  have hf : runLayered (extendCircuit (capacity P word.length) (base P word.length)) (inputState P word v)=
      assembleMap _ _ (tensor v (computedWork P word)) := by
    rw [extendCircuit_semantics]
    simp only [workAction,inputState,LinearMap.comp_apply,separate_assemble]
    exact congrArg (fun φ => assembleMap (width P word.length) (capacity P word.length) φ)
      (CoherentComputeUncompute.onWork_tensor (runLayeredLinearMap (base P word.length)) v
        (initialWork P word.length word) (computedWork P word) (base_computes P word))
  have hm : runLayered (CoherentXorCopy.circuit (controls P word.length))
      (assembleMap _ _ (tensor v (computedWork P word)))=
      assembleMap _ _ (tensor (fun data => v (maskedData P word data)) (computedWork P word)) := by
    rw [CoherentXorCopy.circuit_tensor]
    simp only [xorData_result]
  have hb : runLayered (extendCircuit (capacity P word.length) (inverseCircuit (base P word.length)))
      (assembleMap _ _ (tensor (fun data => v (maskedData P word data)) (computedWork P word)))=
      cleanState P word v := by
    rw [extendCircuit_semantics]
    simp only [workAction,cleanState,inputState,LinearMap.comp_apply,separate_assemble]
    exact congrArg (fun φ => assembleMap (width P word.length) (capacity P word.length) φ)
      (CoherentComputeUncompute.onWork_tensor (runLayeredLinearMap (inverseCircuit (base P word.length)))
        (fun data => v (maskedData P word data)) (computedWork P word) (initialWork P word.length word)
        (inverse_computed P word))
  have he : runLayered (fullCircuit P word.length) (inputState P word v)=
      runLayered (extendCircuit (capacity P word.length) (inverseCircuit (base P word.length)))
        (runLayered (CoherentXorCopy.circuit (controls P word.length))
          (runLayered (extendCircuit (capacity P word.length) (base P word.length)) (inputState P word v))) := by
    simp only [fullCircuit,runLayered,List.foldl_append]
  rw [he,hf,hm,hb]

end

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeCoherentClassicalOracleBasis. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentClassicalOracle

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute NativeWordCoherent NativeWordLayout

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

variable {f : Str → Str} (P : PolyProgram id id f)

theorem initialWork_append (word : Str) :
    initialWork P word.length word=Fin.append (toBits word) (fun _ => false) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [initialWork,Fin.val_castAdd,Fin.append_left,wordExtension_before _ _ j.isLt]
    rfl
  · intro j
    simp only [initialWork,Fin.val_natAdd,Fin.append_right]
    exact wordExtension_after word _ (by omega)

theorem inputState_basis (word : Str) (data : Bits (capacity P word.length)) :
    inputState P word (basis data)=basis (Fin.append (initialWork P word.length word) data) := by
  rw [show basis (Fin.append (initialWork P word.length word) data)=
      tensorState (basis (initialWork P word.length word)) (basis data) from
        computationalBasis_tensor _ _]
  funext x
  change basis data (rightRegister x)*basis (initialWork P word.length word) (leftRegister x)=_
  exact mul_comm _ _

theorem maskedData_involutive (word : Str) : Function.Involutive (maskedData P word) := by
  intro data
  funext i
  simp [maskedData]

theorem basis_maskedData (word : Str) (data : Bits (capacity P word.length)) :
    (fun x => basis data (maskedData P word x))=basis (maskedData P word data) := by
  funext x
  have he : maskedData P word x=data ↔ x=maskedData P word data := by
    constructor
    · intro h;rw [←h,maskedData_involutive]
    · intro h;rw [h,maskedData_involutive]
  simp only [basis,he]

/-- The whole actual program implements a clean classical XOR oracle on
basis states, preserving its input and returning every machine-work bit to zero. -/
theorem fullCircuit_basis (word : Str) (data : Bits (capacity P word.length)) :
    runLayered (fullCircuit P word.length) (basis (Fin.append (initialWork P word.length word) data))=
      basis (Fin.append (initialWork P word.length word) (maskedData P word data)) := by
  rw [←inputState_basis,fullCircuit_exact,cleanState,basis_maskedData,inputState_basis]

@[simp] theorem paddedOutput_length (word : Str) : (paddedOutput P word).length=capacity P word.length :=
  List.length_ofFn

/-- Zero target bits produce the literal function output followed by false
padding in the fixed public output capacity. -/
theorem fullCircuit_zero (word : Str) :
    runLayered (fullCircuit P word.length)
      (basis (Fin.append (initialWork P word.length word) (fun _ => false)))=
      basis (Fin.append (initialWork P word.length word)
        (fun i : Fin (capacity P word.length) => wordExtension (f word) i.val)) := by
  rw [fullCircuit_basis]
  apply congrArg (fun mask : Bits (capacity P word.length) => basis (Fin.append (initialWork P word.length word) mask))
  funext i
  simp [maskedData]

end InfoLossLAR.WorstCase.CoherentClassicalOracle

end

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeCoherentInjectionLayout. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

theorem forward_input (n x y a b : ℕ) (hn : n ≤ x) (i : Fin n) :
    (forwardWires n x y a b hn) ((i.castAdd a).castAdd y)=⟨i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,dif_pos i.isLt]

theorem forward_work (n x y a b : ℕ) (hn : n ≤ x) (i : Fin a) :
    (forwardWires n x y a b hn) ((i.natAdd n).castAdd y)=⟨x+y+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem forward_output (n x y a b : ℕ) (hn : n ≤ x) (i : Fin y) :
    (forwardWires n x y a b hn) (i.natAdd (n+a))=⟨x+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [forwardWires,Function.Embedding.coeFn_mk,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_neg (by omega)]
  simp

theorem backward_input (x y a b : ℕ) (i : Fin y) :
    (backwardWires x y a b) ((i.castAdd b).castAdd x)=⟨x+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,dif_pos i.isLt]

theorem backward_work (x y a b : ℕ) (i : Fin b) :
    (backwardWires x y a b) ((i.natAdd y).castAdd x)=⟨x+y+a+i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_castAdd,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem backward_output (x y a b : ℕ) (i : Fin x) :
    (backwardWires x y a b) (i.natAdd (y+b))=⟨i.val,by unfold width;omega⟩ := by
  apply Fin.ext
  simp only [backwardWires,Function.Embedding.coeFn_mk,Fin.val_natAdd]
  rw [dif_neg (by omega),dif_neg (by omega)]
  simp

@[simp] theorem dataBits_old {x y a b : ℕ} (old : Bits x) (fresh : Bits y) (i : Fin x) :
    dataBits (a:=a) (b:=b) old fresh ⟨i.val,by unfold width;omega⟩=old i := by
  simp only [dataBits,dif_pos i.isLt]

@[simp] theorem dataBits_fresh {x y a b : ℕ} (old : Bits x) (fresh : Bits y) (i : Fin y) :
    dataBits (a:=a) (b:=b) old fresh ⟨x+i.val,by unfold width;omega⟩=fresh i := by
  simp only [dataBits]
  rw [dif_neg (by omega),dif_pos (by omega)]
  simp

theorem dataBits_work {x y a b : ℕ} (old : Bits x) (fresh : Bits y)
    (i : Fin (width x y a b)) (hi : x+y ≤ i.val) : dataBits old fresh i=false := by
  simp only [dataBits]
  rw [dif_neg (by omega),dif_neg (by omega)]

end InfoLossLAR.WorstCase.CoherentInjection

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeCoherentInjectionRegisters. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms.Complexity FiniteGateTransport

theorem forward_selected (n x y a b : ℕ) (hn : n ≤ x) (old : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh)).1=
      Fin.append (Fin.append (fun i : Fin n => old ⟨i.val,by omega⟩) (fun _ => false)) fresh := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.append_left]
      change dataBits old fresh (forwardWires n x y a b hn ((k.castAdd a).castAdd y))=_
      rw [forward_input]
      simp only [dataBits,dif_pos (by omega : k.val<x)]
    · intro k
      simp only [Fin.append_left,Fin.append_right]
      change dataBits old fresh (forwardWires n x y a b hn ((k.natAdd n).castAdd y))=_
      rw [forward_work]
      exact dataBits_work old fresh _ (by dsimp;omega)
  · intro k
    simp only [Fin.append_right]
    change dataBits old fresh (forwardWires n x y a b hn (k.natAdd (n+a)))=_
    rw [forward_output,dataBits_fresh]

theorem backward_selected (x y a b : ℕ) (old : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (backwardWires x y a b) (dataBits old fresh)).1=
      Fin.append (Fin.append fresh (fun _ => false)) old := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [Fin.append_left]
      change dataBits old fresh (backwardWires x y a b ((k.castAdd b).castAdd x))=_
      rw [backward_input,dataBits_fresh]
    · intro k
      simp only [Fin.append_left,Fin.append_right]
      change dataBits old fresh (backwardWires x y a b ((k.natAdd y).castAdd x))=_
      rw [backward_work]
      exact dataBits_work old fresh _ (by dsimp;omega)
  · intro k
    simp only [Fin.append_right]
    change dataBits old fresh (backwardWires x y a b (k.natAdd (y+b)))=_
    rw [backward_output,dataBits_old]

theorem forward_outside (n x y a b : ℕ) (hn : n ≤ x)
    (old : Bits x) (fresh fresh' : Bits y) :
    (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh)).2=
      (wireBitsEquiv (forwardWires n x y a b hn) (dataBits old fresh')).2 := by
  funext i
  have hy : ¬(x ≤ i.val.val ∧ i.val.val<x+y) := by
    rintro ⟨hlo,hhi⟩
    have hk : i.val.val-x<y := by omega
    apply i.property
    refine ⟨(⟨i.val.val-x,hk⟩ : Fin y).natAdd (n+a),?_⟩
    rw [forward_output]
    apply Fin.ext
    simp only
    omega
  change dataBits old fresh i.val=dataBits old fresh' i.val
  simp only [dataBits]
  split_ifs <;> first | rfl | omega

theorem backward_outside (x y a b : ℕ) (old old' : Bits x) (fresh : Bits y) :
    (wireBitsEquiv (backwardWires x y a b) (dataBits old fresh)).2=
      (wireBitsEquiv (backwardWires x y a b) (dataBits old' fresh)).2 := by
  funext i
  have hx : ¬i.val.val<x := by
    intro h
    apply i.property
    refine ⟨(⟨i.val.val,h⟩ : Fin x).natAdd (y+b),?_⟩
    rw [backward_output]
  change dataBits old fresh i.val=dataBits old' fresh i.val
  simp only [dataBits,dif_neg hx]

end InfoLossLAR.WorstCase.CoherentInjection

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeCoherentInjectionOracle. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

theorem originalSize_ge (n : ℕ) : n ≤ originalSize P Q n := by
  simp only [originalSize,outputSize,capacity]
  omega

def originalBits (word : Str) : Bits (originalSize P Q word.length) := fun i => wordExtension word i.val

def outputBits (word : Str) : Bits (outputSize P word.length) := fun i => wordExtension (f word) i.val

def inputBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (originalBits P Q word) (fun _ => false)

def middleBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (originalBits P Q word) (outputBits P word)

def finalBits (word : Str) : Bits (totalWidth P Q word.length) :=
  dataBits (fun _ => false) (outputBits P word)

theorem forward_selected_word (word : Str) (fresh : Bits (outputSize P word.length)) :
    (wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) fresh)).1=
      Fin.append (CoherentClassicalOracle.initialWork P word.length word) fresh := by
  calc
    _ = Fin.append (Fin.append (fun i : Fin word.length => wordExtension word i.val) (fun _ => false)) fresh :=
      forward_selected _ _ _ _ _ _ _ _
    _ = _ := by
      rw [CoherentClassicalOracle.initialWork_append]
      congr 2
      funext i
      exact wordExtension_before word i.val i.isLt

theorem firstCircuit_basis (word : Str) :
    runLayered (firstCircuit P Q word.length) (basis (inputBits P Q word))=basis (middleBits P Q word) := by
  apply relocateCircuit_basis
  · change runLayered (CoherentClassicalOracle.fullCircuit P word.length)
      (basis ((wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) (fun _ => false))).1))=
        basis ((wireBitsEquiv (firstWires P Q word.length) (dataBits (originalBits P Q word) (outputBits P word))).1)
    rw [forward_selected_word,forward_selected_word]
    exact CoherentClassicalOracle.fullCircuit_zero P word
  · exact forward_outside _ _ _ _ _ _ _ _ _

theorem paddedOutput_bits (word : Str) :
    (fun i : Fin (outputSize P word.length) =>
      wordExtension (CoherentClassicalOracle.paddedOutput P word) i.val)=outputBits P word := by
  funext i
  have hi : i.val<(CoherentClassicalOracle.paddedOutput P word).length := by
    simpa only [CoherentClassicalOracle.paddedOutput_length,outputSize] using i.isLt
  rw [wordExtension_before _ _ hi]
  change (List.ofFn (fun j : Fin (capacity P word.length) => wordExtension (f word) j.val))[i.val]=_
  rw [List.getElem_ofFn]
  rfl

theorem initialWork_at (word : Str) (n : ℕ) (hn : word.length=n) :
    CoherentClassicalOracle.initialWork P n word=
      Fin.append (fun i : Fin n => wordExtension word i.val) (fun _ => false) := by
  subst n
  rw [CoherentClassicalOracle.initialWork_append]
  congr 1
  funext i
  exact (wordExtension_before word i.val i.isLt).symm

theorem fullCircuit_basis_at (word : Str) (n : ℕ) (hn : word.length=n)
    (data : Bits (capacity P n)) :
    runLayered (CoherentClassicalOracle.fullCircuit P n)
        (basis (Fin.append (CoherentClassicalOracle.initialWork P n word) data))=
      basis (Fin.append (CoherentClassicalOracle.initialWork P n word)
        (fun i => xor (data i) (wordExtension (f word) i.val))) := by
  subst n
  exact CoherentClassicalOracle.fullCircuit_basis P word data

theorem backward_selected_word (word : Str) (old : Bits (originalSize P Q word.length)) :
    (wireBitsEquiv (secondWires P Q word.length) (dataBits old (outputBits P word))).1=
      Fin.append (CoherentClassicalOracle.initialWork Q (outputSize P word.length)
        (CoherentClassicalOracle.paddedOutput P word)) old := by
  have hlen : (CoherentClassicalOracle.paddedOutput P word).length=outputSize P word.length :=
    CoherentClassicalOracle.paddedOutput_length P word
  have hw : CoherentClassicalOracle.initialWork Q (outputSize P word.length)
      (CoherentClassicalOracle.paddedOutput P word)=Fin.append (outputBits P word) (fun _ => false) := by
    rw [initialWork_at Q _ _ hlen,paddedOutput_bits]
  calc
    _ = Fin.append (Fin.append (outputBits P word) (fun _ => false)) old := backward_selected _ _ _ _ _ _
    _ = _ := congrArg (fun work : Bits (NativeWordLayout.width Q (outputSize P word.length)) =>
      Fin.append work old) hw.symm

/-- The inverse is evaluated on the literal padded output of the forward
machine. Its contract must therefore hold on that actual fixed-length word,
not on an abstract unpadded value. -/
theorem secondCircuit_basis (word : Str)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (secondCircuit P Q word.length) (basis (middleBits P Q word))=
      basis (finalBits P Q word) := by
  apply relocateCircuit_basis
  · change runLayered (CoherentClassicalOracle.fullCircuit Q (outputSize P word.length))
        (basis ((wireBitsEquiv (secondWires P Q word.length) (dataBits (originalBits P Q word) (outputBits P word))).1))=
      basis ((wireBitsEquiv (secondWires P Q word.length) (dataBits (fun _ => false) (outputBits P word))).1)
    rw [backward_selected_word,backward_selected_word]
    have hlen : (CoherentClassicalOracle.paddedOutput P word).length=outputSize P word.length :=
      CoherentClassicalOracle.paddedOutput_length P word
    rw [fullCircuit_basis_at Q _ _ hlen]
    congr 2
    funext i
    simp [originalBits,hinverse]
  · exact backward_outside _ _ _ _ _ _ _

/-- A literal two-machine fixed-gate circuit realizes an injective native
map coherently, erasing the old input and returning both workspaces to zero. -/
theorem circuit_basis (word : Str)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (circuit P Q word.length) (basis (inputBits P Q word))=
      basis (finalBits P Q word) := by
  have he : runLayered (circuit P Q word.length) (basis (inputBits P Q word))=
      runLayered (secondCircuit P Q word.length)
        (runLayered (firstCircuit P Q word.length) (basis (inputBits P Q word))) := by
    simp only [circuit,runLayered,List.foldl_append]
  rw [he,firstCircuit_basis,secondCircuit_basis P Q word hinverse]

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeCoherentInjectionSuperposition. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentInjection

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary

open scoped BigOperators

variable {f g : Str → Str} (P : PolyProgram id id f) (Q : PolyProgram id id g)

theorem _root_.solution (n : ℕ) (word : Str) (hlen : word.length=n)
    (hinverse : g (CoherentClassicalOracle.paddedOutput P word)=word) :
    runLayered (circuit P Q n) (basis (inputBitsAt P Q n word))=basis (finalBitsAt P Q n word) := by
  subst n
  exact circuit_basis P Q word hinverse

variable {I : Type*} [Fintype I]

end InfoLossLAR.WorstCase.CoherentInjection

end

end P2MDyadicModule30
