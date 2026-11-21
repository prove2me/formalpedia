-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.compile_placed_gate_recipes
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:51:15.036806+00:00
-- url     : https://prove2.me/submissions/a3b4baa5-390c-4e89-80fe-ad2039a06325

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_04
import Definitions.Def_QAlgorithms_Defs_Measurement

set_option linter.all false

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute
end InfoLossLAR.WorstCase.CoherentComputeUncompute

namespace InfoLossLAR.WorstCase.ControlledLetterPlan
end InfoLossLAR.WorstCase.ControlledLetterPlan

namespace InfoLossLAR.WorstCase.ControlledNativeCode
end InfoLossLAR.WorstCase.ControlledNativeCode

namespace InfoLossLAR.WorstCase.ControlledNativeGates
end InfoLossLAR.WorstCase.ControlledNativeGates

namespace InfoLossLAR.WorstCase.ControlledRelocation
end InfoLossLAR.WorstCase.ControlledRelocation

namespace InfoLossLAR.WorstCase.FiniteGateNative
end InfoLossLAR.WorstCase.FiniteGateNative

namespace InfoLossLAR.WorstCase.FiniteGateTransport
end InfoLossLAR.WorstCase.FiniteGateTransport

namespace InfoLossLAR.WorstCase.NativeWordCoherent
end InfoLossLAR.WorstCase.NativeWordCoherent

namespace InfoLossLAR.WorstCase.NativeWordDescription
end InfoLossLAR.WorstCase.NativeWordDescription

namespace InfoLossLAR.WorstCase.NativeWordLayout
end InfoLossLAR.WorstCase.NativeWordLayout

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages
end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

namespace InfoLossLAR.WorstCase.RegevSearch.GaussianIteration
end InfoLossLAR.WorstCase.RegevSearch.GaussianIteration

namespace InfoLossLAR.WorstCase.RegevSearch.SamplerParameters
end InfoLossLAR.WorstCase.RegevSearch.SamplerParameters

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

namespace Integration9_9.LARRankOneMachine
end Integration9_9.LARRankOneMachine

namespace Integration9_9.LoadedBatch.PostComposition
end Integration9_9.LoadedBatch.PostComposition

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

end InfoLossLAR.WorstCase

end P2MDyadicModule0

/- Helper module Solutions.RegevBridgeCoherentComputeUncompute. -/
section P2MDyadicModule1

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open FiniteGateTransport

open scoped BigOperators

variable {D W I : Type*} [Fintype D] [Fintype W] [DecidableEq W]

noncomputable def basis (w : W) : W → ℂ := fun r => if r=w then 1 else 0

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end P2MDyadicModule1

/- Helper module Solutions.RegevBridgeWireRelocation. -/
section P2MDyadicModule2

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

end P2MDyadicModule2

/- Helper module Solutions.RegevBridgeToffoli. -/
section P2MDyadicModule3

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

end P2MDyadicModule3

/- Helper module Integration9_9.TM2PlatformSerialization. -/
section P2MDyadicModule4

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

end P2MDyadicModule4

/- Helper module Integration9_9.TM2OutputLength. -/
section P2MDyadicModule5

set_option autoImplicit false

namespace Integration9_9.TM2OutputLength

open Turing StateTransition

variable {K Λ σ : Type} {Γ : K → Type} [Fintype K] [DecidableEq K]

variable [Fintype Λ]

attribute [local instance] Integration9_9.TM2OutputLength.tmStacksFintype

attribute [local instance] Integration9_9.TM2OutputLength.tmLabelsFintype

/-- Polynomial-time TM2 computations have polynomially bounded encoded output
length. This is the size estimate required when composing time polynomials. -/
theorem polynomial_output_length {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (machine : TM2ComputableInPolyTime ea eb f) :
    ∃ p : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ p.eval (ea a).length := by
  refine ⟨Polynomial.X + Polynomial.C (programPushBound machine.tm.m) * machine.time, ?_⟩
  intro a
  have h := output_length_le machine.tm
    (List.map machine.inputAlphabet.invFun (ea a))
    (List.map machine.outputAlphabet.invFun (eb (f a)))
    (machine.time.eval (ea a).length) (machine.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C] using h

end Integration9_9.TM2OutputLength

end P2MDyadicModule5

/- Helper module Solutions.RegevBridgeInverseUniform. -/
section P2MDyadicModule6

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

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeReversibleCircuit. -/
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

/-- A computational basis input is sent to the exact classical output. -/
theorem compileReversible_basis {n : ℕ} (gates : List (ReversibleGate n)) (x : Bits n) :
    runLayered (compileReversible gates) (fun y => if y = x then (1 : ℂ) else 0) =
      fun y => if y = reversibleAction gates x then 1 else 0 := by
  rw [compileReversible_apply]
  funext y
  congr 1
  exact propext (Equiv.symm_apply_eq _)

end InfoLossLAR.WorstCase

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeReversibleUniform. -/
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

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeBooleanCircuit. -/
section P2MDyadicModule9

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

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeCircuitRelocation. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity

open scoped BigOperators

/-- Relocate all five actual gate constructors along public physical wires. -/
def relocateInstr {k n : ℕ} (w : Fin k ↪ Fin n) : Instr k → Instr n
  | .h i => .h (w i)
  | .s i => .s (w i)
  | .t i => .t (w i)
  | .x i => .x (w i)
  | .cnot i j h => .cnot (w i) (w j) (w.injective.ne h)

def relocateCircuit {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k) : Layered n :=
  circuit.map (List.map (relocateInstr w))

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

@[simp] theorem relocateInstr_support {k n : ℕ} (w : Fin k ↪ Fin n) (g : Instr k) :
    (relocateInstr w g).support=g.support.image w := by cases g <;> simp [relocateInstr,Instr.support]

theorem relocate_support_disjoint {k n : ℕ} (w : Fin k ↪ Fin n) (g h : Instr k)
    (hd : Disjoint g.support h.support) :
    Disjoint (relocateInstr w g).support (relocateInstr w h).support := by
  rw [relocateInstr_support,relocateInstr_support]
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hj
  have heq := w.injective he
  subst b
  exact Finset.disjoint_left.mp hd ha hb

theorem relocateLayer_ok {k n : ℕ} (w : Fin k ↪ Fin n) (layer : List (Instr k))
    (h : LayerOk layer) : LayerOk (layer.map (relocateInstr w)) := by
  unfold LayerOk at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun hd => relocate_support_disjoint w _ _ hd)

theorem relocateCircuit_wellFormed {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k)
    (h : ∀ l∈circuit,LayerOk l) : ∀ l∈relocateCircuit w circuit,LayerOk l := by
  intro l hl
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp (show l∈circuit.map (List.map (relocateInstr w)) from hl)
  exact relocateLayer_ok w original (h original ho)

end InfoLossLAR.WorstCase.FiniteGateTransport

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeInitializedRelocation. -/
section P2MDyadicModule11

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

/- Helper module Solutions.RegevBridgeFiniteGateNativeAlgebra. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Executable rational coordinates for `a + b sqrt(2)`. -/
abbrev RealPair := ℚ × ℚ

/-- Executable rational coordinates for `(a + b sqrt(2)) + i(c + d sqrt(2))`. -/
abbrev Scalar := RealPair × RealPair

def addReal (x y : RealPair) : RealPair := (x.1+y.1,x.2+y.2)

def negReal (x : RealPair) : RealPair := (-x.1,-x.2)

def subReal (x y : RealPair) : RealPair := addReal x (negReal y)

def mulReal (x y : RealPair) : RealPair :=
  (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)

def zero : Scalar := ((0,0),(0,0))

def one : Scalar := ((1,0),(0,0))

def add (x y : Scalar) : Scalar := (addReal x.1 y.1,addReal x.2 y.2)

def neg (x : Scalar) : Scalar := (negReal x.1,negReal x.2)

def mul (x y : Scalar) : Scalar :=
  (subReal (mulReal x.1 y.1) (mulReal x.2 y.2),
   addReal (mulReal x.1 y.2) (mulReal x.2 y.1))

def conj (x : Scalar) : Scalar := (x.1,negReal x.2)

noncomputable def evalReal (x : RealPair) : ℝ := x.1+(x.2 : ℝ)*Real.sqrt 2

noncomputable def eval (x : Scalar) : ℂ := ⟨evalReal x.1,evalReal x.2⟩

@[simp] theorem evalReal_add (x y : RealPair) : evalReal (addReal x y)=evalReal x+evalReal y := by
  simp only [evalReal,addReal,Rat.cast_add]
  ring

@[simp] theorem evalReal_neg (x : RealPair) : evalReal (negReal x)= -evalReal x := by
  simp only [evalReal,negReal,Rat.cast_neg]
  ring

@[simp] theorem evalReal_sub (x y : RealPair) : evalReal (subReal x y)=evalReal x-evalReal y := by
  simp [subReal,sub_eq_add_neg]

@[simp] theorem evalReal_mul (x y : RealPair) : evalReal (mulReal x y)=evalReal x*evalReal y := by
  simp only [evalReal,mulReal,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ)≤2 by norm_num)]

@[simp] theorem eval_zero : eval zero=0 := by apply Complex.ext <;> simp [eval,evalReal,zero]

@[simp] theorem eval_one : eval one=1 := by apply Complex.ext <;> simp [eval,evalReal,one]

@[simp] theorem eval_add (x y : Scalar) : eval (add x y)=eval x+eval y := by
  apply Complex.ext <;> simp [eval,add]

@[simp] theorem eval_neg (x : Scalar) : eval (neg x)= -eval x := by
  apply Complex.ext <;> simp [eval,neg]

@[simp] theorem eval_mul (x y : Scalar) : eval (mul x y)=eval x*eval y := by
  apply Complex.ext <;> simp [eval,mul,Complex.mul_re,Complex.mul_im]

@[simp] theorem eval_conj (x : Scalar) : eval (conj x)=star (eval x) := by
  apply Complex.ext <;> simp [eval,conj]

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeFiniteGateNativeCoefficients. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.FiniteGateNative

def hScale : Scalar := ((0,1/2),(0,0))

def tPhase : Scalar := ((0,1/2),(0,1/2))

@[simp] theorem eval_hScale : eval hScale=((Real.sqrt 2)⁻¹ : ℂ) := by
  apply Complex.ext
  · norm_num [eval,evalReal,hScale]
    ring
  · simp [eval,evalReal,hScale]

@[simp] theorem eval_tPhase : eval tPhase=Complex.exp (Complex.I*Real.pi/4) := by
  have harg : Complex.I*(Real.pi : ℂ)/4=(((Real.pi/4 : ℝ) : ℂ)*Complex.I) := by
    push_cast
    ring
  rw [harg]
  apply Complex.ext
  · norm_num [eval,evalReal,tPhase,Complex.exp_re,Complex.mul_re,Complex.mul_im,Real.cos_pi_div_four]
    ring
  · norm_num [eval,evalReal,tPhase,Complex.exp_im,Complex.mul_re,Complex.mul_im,Real.sin_pi_div_four]
    ring

def hCoefficient (row column : Bool) : Scalar := if row && column then neg hScale else hScale

def tCoefficient (row column : Bool) : Scalar := if row=column then (if row then tPhase else one) else zero

@[simp] theorem eval_hCoefficient (row column : Bool) :
    eval (hCoefficient row column)=QAlgorithms.Complexity.hMat row column := by
  simp only [hCoefficient,QAlgorithms.Complexity.hMat,Matrix.of_apply]
  split <;> simp

@[simp] theorem eval_tCoefficient (row column : Bool) :
    eval (tCoefficient row column)=QAlgorithms.Complexity.tMat row column := by
  simp only [tCoefficient,QAlgorithms.Complexity.tMat,Matrix.of_apply]
  by_cases h : row=column
  · rw [if_pos h,if_pos h]
    split <;> simp_all
  · simp [h]

end InfoLossLAR.WorstCase.FiniteGateNative

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeControlledHadamard. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option maxHeartbeats 2400000

namespace InfoLossLAR.WorstCase.ControlledHadamard

open QAlgorithms QAlgorithms.Complexity

open FiniteGateNative

abbrev Mat2 := Bool→Bool→Scalar

def mul2 (A B : Mat2) : Mat2 := fun i j =>
  add (mul (A i false) (B false j)) (mul (A i true) (B true j))

def star2 (A : Mat2) : Mat2 := fun i j => conj (A j i)

noncomputable def eval2 (A : Mat2) : Matrix Bool Bool ℂ := fun i j => eval (A i j)

def S : Mat2 := fun i j => if i=j then (if i then ((0,0),(1,0)) else one) else zero

def turn : Mat2 := mul2 S (mul2 hCoefficient (mul2 tCoefficient (mul2 hCoefficient (star2 S))))

theorem eval2_mul (A B : Mat2) : eval2 (mul2 A B)=eval2 A*eval2 B := by
  ext i j
  simp only [eval2,mul2,eval_add,eval_mul,Matrix.mul_apply,Fintype.sum_bool]
  ring

theorem eval2_star (A : Mat2) : eval2 (star2 A)=star (eval2 A) := by
  ext i j
  simp only [eval2,star2,eval_conj,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

theorem eval2_H : eval2 hCoefficient=hMat := by ext i j;exact eval_hCoefficient i j

theorem eval2_T : eval2 tCoefficient=tMat := by ext i j;exact eval_tCoefficient i j

theorem eval2_S : eval2 S=sMat := by
  ext i j
  cases i <;> cases j <;> apply Complex.ext <;> norm_num [eval2,S,eval,evalReal,one,zero,sMat]

noncomputable def V : Matrix Bool Bool ℂ := sMat*hMat*tMat*hMat*star sMat

theorem eval2_turn : eval2 turn=V := by
  simp only [turn,eval2_mul,eval2_star,eval2_H,eval2_T,eval2_S,V,Matrix.mul_assoc]

def X : Mat2 := fun i j => if i=j then zero else one

def controlTurn : Mat2 := mul2 turn hCoefficient

theorem controlTurn_conjugates_X : mul2 controlTurn (mul2 X (star2 controlTurn))=hCoefficient := by
  funext i j
  cases i <;> cases j <;> decide +kernel

theorem controlTurn_unitary : mul2 controlTurn (star2 controlTurn)=fun i j => if i=j then one else zero := by
  funext i j
  cases i <;> cases j <;> decide +kernel

theorem eval2_X : eval2 X=xMat := by
  ext i j
  cases i <;> cases j <;> simp [eval2,X,xMat,eval_one,eval_zero]

noncomputable def W : Matrix Bool Bool ℂ := V*hMat

theorem eval2_controlTurn : eval2 controlTurn=W := by
  simp only [controlTurn,eval2_mul,eval2_turn,eval2_H,W]

theorem W_unitary : W∈Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := congrArg eval2 controlTurn_unitary
  rw [eval2_mul,eval2_star,eval2_controlTurn] at h
  convert h using 1
  ext i j
  cases i <;> cases j <;> simp [eval2,Matrix.one_apply,eval_one,eval_zero]

theorem W_conjugates_X : W*xMat*star W=hMat := by
  have h := congrArg eval2 controlTurn_conjugates_X
  simpa only [eval2_mul,eval2_star,eval2_controlTurn,eval2_X,eval2_H,Matrix.mul_assoc] using h

/-- Controlled action on a target wire. The control and every other wire
remain in the state, so the definition applies to arbitrary superpositions. -/
noncomputable def controlled {n : ℕ} (U : Matrix Bool Bool ℂ) (c t : Fin n)
    (ψ : QState n) : QState n := fun x => if x c then apply1 U t ψ x else ψ x

theorem apply1_control_split {n : ℕ} (U : Matrix Bool Bool ℂ) (c t : Fin n) (hct : c≠t)
    (ψ φ : QState n) : apply1 U t (fun x => if x c then ψ x else φ x)=
      fun x => if x c then apply1 U t ψ x else apply1 U t φ x := by
  funext x
  cases hc : x c <;> simp [apply1,Function.update_of_ne hct,hc]

theorem controlled_conjugate {n : ℕ} (U Z V : Matrix Bool Bool ℂ)
    (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    apply1 U t (controlled Z c t (apply1 V t ψ))=
      fun x => if x c then apply1 (U*Z*V) t ψ x else apply1 (U*V) t ψ x := by
  unfold controlled
  rw [apply1_control_split U c t hct]
  simp only [apply1_comp,Matrix.mul_assoc]

theorem controlled_X {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    controlled xMat c t ψ=cnotState c t hct ψ := by
  funext x
  cases hc : x c <;> cases ht : x t <;>
    simp [controlled,apply1,xMat,cnotState,hc,ht]
  all_goals rw [←ht,Function.update_eq_self]

theorem W_sandwich_cnot {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    apply1 W t (cnotState c t hct (apply1 (star W) t ψ))=controlled hMat c t ψ := by
  rw [←controlled_X,controlled_conjugate W xMat (star W) c t hct,W_conjugates_X,
    Matrix.mem_unitaryGroup_iff.mp W_unitary,apply1_one]
  rfl

theorem sMat_cube : sMat^3=star sMat := by
  ext i j
  cases i <;> cases j <;>
    norm_num [pow_succ,Matrix.mul_apply,sMat,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

def turnWord {n : ℕ} (t : Fin n) : List (Instr n) :=
  [.h t]++List.replicate 3 (.s t)++[.h t,.t t,.h t,.s t]

theorem turnWord_semantics {n : ℕ} (t : Fin n) (ψ : QState n) :
    runLayer (turnWord t) ψ=apply1 W t ψ := by
  simp only [turnWord,runLayer_append,runLayer_replicate,Instr.apply,apply1_iterate,sMat_cube]
  simp only [runLayer,List.foldl_cons,List.foldl_nil,Instr.apply,apply1_comp,W,V,Matrix.mul_assoc]

theorem inverse_turnWord_semantics {n : ℕ} (t : Fin n) (ψ : QState n) :
    runLayer (inverseGates (turnWord t)) ψ=apply1 (star W) t ψ := by
  have h := inverseGates_left (turnWord t) (apply1 (star W) t ψ)
  rw [turnWord_semantics,apply1_comp,Matrix.mem_unitaryGroup_iff.mp W_unitary,apply1_one] at h
  exact h

/-- A fixed exact native gate sequence for controlled Hadamard. -/
def gates {n : ℕ} (c t : Fin n) (hct : c≠t) : List (Instr n) :=
  inverseGates (turnWord t)++[.cnot c t hct]++turnWord t

theorem gates_semantics {n : ℕ} (c t : Fin n) (hct : c≠t) (ψ : QState n) :
    runLayer (gates c t hct) ψ=controlled hMat c t ψ := by
  rw [gates,runLayer_append,runLayer_append,inverse_turnWord_semantics,turnWord_semantics]
  change apply1 W t (cnotState c t hct (apply1 (star W) t ψ))=_
  exact W_sandwich_cnot c t hct ψ

end InfoLossLAR.WorstCase.ControlledHadamard

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeControlledLetterPlan. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledLetterPlan

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

theorem runLayered_singletons {n : ℕ} (gates : List (Instr n)) (ψ : QState n) :
    runLayered (gates.map (fun g => [g])) ψ=runLayer gates ψ := by
  induction gates generalizing ψ with
  | nil => rfl
  | cons gate rest ih => exact ih (gate.apply ψ)

theorem toffoliGates_semantics {n : ℕ} (c i j : Fin n) (hci : c≠i) (hcj : c≠j) (hij : i≠j)
    (ψ : QState n) : runLayer (toffoliGates c i j hci hcj hij) ψ=
      fun x => ψ (Function.update x j (xor (x j) (x c && x i))) := by
  rw [←runLayered_singletons]
  exact toffoliCircuit_apply c i j hci hcj hij ψ

end InfoLossLAR.WorstCase.ControlledLetterPlan

end P2MDyadicModule17

/- Helper module Solutions.RegevBridgeControlledNativeCode. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Tags 0,1,2,3,4 mean H,S,T,X,CNOT. Natural addresses use binary coding. -/
abbrev GateCode := ℕ×ℕ×ℕ

/-- Tag 5 is an exact ideal eighth phase in the input plan only. The Boolean
is its sign. The output has only the five finite native gate tags. -/
abbrev AtomCode := GateCode×Bool

def encodeInstr {n : ℕ} : Instr n → GateCode
  | .h i => (0,i.val,0)
  | .s i => (1,i.val,0)
  | .t i => (2,i.val,0)
  | .x i => (3,i.val,0)
  | .cnot i j _ => (4,i.val,j.val)

def decodeGate (n : ℕ) (code : GateCode) : Option (Instr n) :=
  if hi : code.2.1< n then
    match code.1 with
    | 0 => some (.h ⟨code.2.1,hi⟩)
    | 1 => some (.s ⟨code.2.1,hi⟩)
    | 2 => some (.t ⟨code.2.1,hi⟩)
    | 3 => some (.x ⟨code.2.1,hi⟩)
    | 4 => if hj : code.2.2< n then
        if hij : code.2.1≠code.2.2 then some (.cnot ⟨code.2.1,hi⟩ ⟨code.2.2,hj⟩ (by
          intro h;exact hij (congrArg Fin.val h))) else none
      else none
    | _ => none
  else none

theorem decode_encode {n : ℕ} (g : Instr n) : decodeGate n (encodeInstr g)=some g := by
  cases g with
  | h i => simp [encodeInstr,decodeGate,i.isLt]
  | s i => simp [encodeInstr,decodeGate,i.isLt]
  | t i => simp [encodeInstr,decodeGate,i.isLt]
  | x i => simp [encodeInstr,decodeGate,i.isLt]
  | cnot i j h =>
    have hv : i.val≠j.val := by intro he;exact h (Fin.ext he)
    simp [encodeInstr,decodeGate,i.isLt,j.isLt,hv]

end InfoLossLAR.WorstCase.ControlledNativeCode

end P2MDyadicModule18

/- Helper module AdaptiveLoad. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 950000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

noncomputable section

variable {h k : ℕ}

inductive Source (h : ℕ) where
  | literal (b : Bool)
  | wire (i : Fin h)

def Source.read (s : Source h) (x : Bits h) : Bool :=
  match s with | .literal b => b | .wire i => x i

def gate (target : Fin k) (v : Source h) : List (Instr (h+k)) :=
  match v with
  | .literal true => [.x (Fin.natAdd h target)]
  | .literal false => []
  | .wire i => [.cnot (Fin.castAdd k i) (Fin.natAdd h target) (by intro he;have := congrArg Fin.val he;simp at this;omega)]

def load (a : Fin k → Source h) := (List.finRange k).flatMap (fun t => gate t (a t))

private theorem x_action {n : ℕ} (t : Fin n) (ψ : QState n) (x : Bits n) :
    (Instr.x t).apply ψ x=ψ (Function.update x t (!(x t))) := by
  cases ht : x t <;> simp [Instr.apply,apply1,xMat,ht]

theorem append_update (x : Bits h) (y : Bits k) (t : Fin k) (b : Bool) :
    Function.update (Fin.append x y) (Fin.natAdd h t) b=Fin.append x (Function.update y t b) := by
  funext u; refine Fin.addCases ?_ ?_ u
  · intro i
    have hn : Fin.castAdd k i≠Fin.natAdd h t := by intro he; have := congrArg Fin.val he;simp at this;omega
    simp [Function.update_of_ne hn]
  · intro i
    by_cases he : i=t
    · subst i; simp
    · have hne : Fin.natAdd h i≠Fin.natAdd h t := by intro hi; apply he;exact Fin.ext (by have := congrArg Fin.val hi;simpa using this)
      simp [Function.update_of_ne he,Function.update_of_ne hne]

theorem single_action (t : Fin k) (s : Source h) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (gate t s) ψ (Fin.append x y)=
      ψ (Fin.append x (Function.update y t (xor (y t) (s.read x)))) := by
  cases s with
  | literal b =>
    cases b
    · simp [gate,Source.read,runLayer]
    · change (Instr.x _).apply ψ _=_
      rw [x_action,append_update]
      simp [Source.read]
  | wire i =>
    change ψ (Function.update _ _ _) = _
    rw [append_update]
    simp [Source.read]

def mask (a : Fin k → Source h) (x : Bits h) (l : List (Fin k)) (y : Bits k) :=
  fun i => xor (y i) (decide (i∈l) && (a i).read x)

private theorem mask_push (a : Fin k → Source h) (x : Bits h) (t : Fin k) (l : List (Fin k))
    (ht : t∉l) (y : Bits k) :
    Function.update (mask a x l y) t (xor (mask a x l y t) ((a t).read x))=mask a x (t::l) y := by
  funext i
  by_cases hi : i=t
  · subst i;simp [mask,ht]
  · simp [mask,hi,Function.update_of_ne hi]

theorem partial_load (a : Fin k → Source h) (l : List (Fin k)) (hl : l.Nodup)
    (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (l.flatMap (fun t => gate t (a t))) ψ (Fin.append x y)=ψ (Fin.append x (mask a x l y)) := by
  induction l generalizing ψ with
  | nil =>
    have hm : mask a x [] y = y := by funext i;simp [mask]
    rw [hm];rfl
  | cons t l ih =>
    rw [List.flatMap_cons,runLayer_append,ih hl.of_cons,single_action,mask_push _ _ _ _ (List.nodup_cons.mp hl).1]

theorem load_action (a : Fin k → Source h) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayer (load a) ψ (Fin.append x y)=ψ (Fin.append x (fun i => xor (y i) ((a i).read x))) := by
  rw [load,partial_load _ _ (List.nodup_finRange k)]
  apply congrArg (fun v => ψ (Fin.append x v))
  funext i;simp [mask]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule19

/- Helper module AdaptiveBranch. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport

open scoped BigOperators Classical

noncomputable section

variable {h k : ℕ}

def right (h k : ℕ) : Fin k ↪ Fin (h+k) := Fin.natAddEmb h

theorem right_parts (x : Bits h) (y z : Bits k) :
    (wireBitsEquiv (right h k) (Fin.append x y)).2=(wireBitsEquiv (right h k) (Fin.append x z)).2 := by
  funext i
  rcases i with ⟨i,hi⟩
  change Fin.append x y i=Fin.append x z i
  revert hi
  refine Fin.addCases ?_ ?_ i
  · intro i _;simp
  · intro j hj;exact False.elim (hj ⟨j,rfl⟩)

@[simp] theorem right_selected (x : Bits h) (y : Bits k) :
    (wireBitsEquiv (right h k) (Fin.append x y)).1=y := by funext i;exact Fin.append_right _ _ _

theorem right_slice (U : Layered k) (ψ : QState (h+k)) (x : Bits h) (y : Bits k) :
    runLayered (relocateCircuit (right h k) U) ψ (Fin.append x y)=runLayered U (fun j => ψ (Fin.append x j)) y := by
  let w := right h k
  let p := wireBitsEquiv w (Fin.append x y)
  have hs := congrFun (relocateCircuit_split w U ψ) p
  change runLayered (relocateCircuit w U) ψ ((wireBitsEquiv w).symm ((wireBitsEquiv w) (Fin.append x y)))=_ at hs
  rw [Equiv.symm_apply_apply] at hs
  have hf (j : Bits k) : (wireBitsEquiv w).symm (j,p.2)=Fin.append x j := by
    apply (wireBitsEquiv w).symm_apply_eq.mpr
    exact Prod.ext (right_selected x j).symm (right_parts x y j)
  rw [hs]
  have he : (fun j => splitState w ψ (j,p.2))=(fun j => ψ (Fin.append x j)) := by
    funext j; change ψ _=_; rw [hf]
  rw [he]
  exact congrArg (runLayered U (fun j => ψ (Fin.append x j))) (right_selected x y)

def stage (a : Fin k → Source h) (U : Layered k) : Layered (h+k) :=
  (load a).map (fun g => [g]) ++ relocateCircuit (right h k) U

theorem read_zero (u v : Bits k) :
    (fun i => xor (u i) (v i))=(fun _ => false) ↔ u=v := by
  constructor
  · intro h;funext i;have hi:=congrFun h i;cases a : u i <;> cases b : v i <;> simp_all
  · rintro rfl;funext i;simp

theorem stage_branch (a : Fin k→Source h) (U : Layered k) (v : QState h)
    (x : Bits h) (y : Bits k) :
    runLayered (stage a U) (tensorState v (basis (fun _ : Fin k => false))) (Fin.append x y)=
    v x * runLayered U (basis (fun i => (a i).read x)) y := by
  rw [stage,show ∀ {n : ℕ} (c d : Layered n) (ψ : QState n),runLayered (c++d) ψ=runLayered d (runLayered c ψ)
        from fun _ _ _ => List.foldl_append,runLayered_singletons,right_slice]
  have hf : (fun j => runLayer (load a) (tensorState v (basis (fun _ => false))) (Fin.append x j)) =
      (v x) • basis (fun i => (a i).read x) := by
    funext j
    rw [load_action]
    have hl (u : Bits k) : leftRegister (Fin.append x u)=x := by funext i;exact Fin.append_left _ _ _
    have hr (u : Bits k) : rightRegister (Fin.append x u)=u := by funext i;exact Fin.append_right _ _ _
    simp only [tensorState,hl,hr,basis,Pi.smul_apply,smul_eq_mul,read_zero]
  rw [hf,←runLayeredLinearMap_apply,map_smul]
  simp only [Pi.smul_apply,smul_eq_mul,runLayeredLinearMap_apply]

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeControlledPlanNative. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.ControlledPlanNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Exact finite inverse expansion: S inverse is S^3 and T inverse is T^7. -/
def inverseCode (gate : GateCode) : List GateCode :=
  if gate.1=1 then (List.replicate 3 ()).map (fun _ => gate)
  else if gate.1=2 then (List.replicate 7 ()).map (fun _ => gate)
  else [gate]

@[fun_prop] theorem inverseCode_poly : Poly inverseCode := by unfold inverseCode;fun_prop

def turnCodes (target : ℕ) : List GateCode :=
  [(0,target,0),(1,target,0),(1,target,0),(1,target,0),(0,target,0),(2,target,0),(0,target,0),(1,target,0)]

@[fun_prop] theorem turnCodes_poly : Poly turnCodes := by unfold turnCodes;fun_prop

def inverseTurnCodes (target : ℕ) : List GateCode := (turnCodes target).reverse.flatMap inverseCode

@[fun_prop] theorem inverseTurnCodes_poly : Poly inverseTurnCodes := by
  unfold inverseTurnCodes
  have hr : Poly (fun target => (turnCodes target).reverse) :=
    Poly.comp QMCNumericRuntime.parser_reverse_poly turnCodes_poly
  exact Poly.list_flatMap (Poly.comp inverseCode_poly Poly.snd) hr

def hPlan (control target : ℕ) : List AtomCode :=
  (inverseTurnCodes target++[(4,control,target)]++turnCodes target).map (fun gate => (gate,false))

def cnotPlan (p q r : ℕ) : List AtomCode :=
  [(0,r,0),
   (2,p,0),(2,q,0),(2,r,0),
   (4,p,q),
   (2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),
   (4,p,q),(4,q,r),
   (2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),
   (4,q,r),(4,p,r),
   (2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),
   (4,p,r),(4,p,r),(4,q,r),(2,r,0),(4,q,r),(4,p,r),(0,r,0)].map (fun gate => (gate,false))

@[fun_prop] theorem hPlan_poly : Poly (fun x : ℕ×ℕ => hPlan x.1 x.2) := by unfold hPlan;fun_prop

@[fun_prop] theorem cnotPlan_poly : Poly (fun x : ℕ×ℕ×ℕ => cnotPlan x.1 x.2.1 x.2.2) := by unfold cnotPlan;fun_prop

end InfoLossLAR.WorstCase.ControlledPlanNative

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeBooleanUniform. -/
section P2MDyadicModule22

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

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeBooleanProgram. -/
section P2MDyadicModule23

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

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeBooleanExpr. -/
section P2MDyadicModule24

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

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeBooleanBundle. -/
section P2MDyadicModule25

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

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeTM2Symbolic. -/
section P2MDyadicModule26

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

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeTM2Transition. -/
section P2MDyadicModule27

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

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeBooleanSize. -/
section P2MDyadicModule28

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

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeTM2CompileStep. -/
section P2MDyadicModule29

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

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeBooleanRPN. -/
section P2MDyadicModule30

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

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeBooleanRPNRun. -/
section P2MDyadicModule31

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

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeBooleanCodePoly. -/
section P2MDyadicModule32

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

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeTM2CodeFamily. -/
section P2MDyadicModule33

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

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeTM2CodeTransition. -/
section P2MDyadicModule34

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

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeTM2CodeEnumeration. -/
section P2MDyadicModule35

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

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeTM2BoundedRun. -/
section P2MDyadicModule36

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

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeTM2Size. -/
section P2MDyadicModule37

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

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeTM2Initial. -/
section P2MDyadicModule38

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

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeTM2CodeRegisters. -/
section P2MDyadicModule39

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

end P2MDyadicModule39

/- Helper module Solutions.RegevBridgeBooleanRPNBounds. -/
section P2MDyadicModule40

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

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeTM2CodeStep. -/
section P2MDyadicModule41

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

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeTM2CodeLoop. -/
section P2MDyadicModule42

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

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeTM2MachineProgram. -/
section P2MDyadicModule43

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

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeTM2CodeGenerate. -/
section P2MDyadicModule44

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

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeBooleanNodeSerialization. -/
section P2MDyadicModule45

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

end P2MDyadicModule45

/- Helper module Solutions.AdvantageBridgeCoinPreparation. -/
section P2MDyadicModule46

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

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeTM2Quantum. -/
section P2MDyadicModule47

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

theorem machineCircuit_wellFormed (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    ∀ layer ∈ machineCircuit hw program input main initialState ticks length, LayerOk layer :=
  compileReversible_wellFormed _

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

end P2MDyadicModule47

/- Helper module Solutions.RegevBridgeTM2CodeDescription. -/
section P2MDyadicModule48

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

end P2MDyadicModule48

/- Helper module Solutions.RegevBridgeTM2PolyCircuit. -/
section P2MDyadicModule49

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

theorem circuit_wellFormed (length : ℕ) : ∀ layer ∈ circuit P length, LayerOk layer :=
  machineCircuit_wellFormed _ _ _ _ _ _ _

end PolyProgramCircuit

end InfoLossLAR.WorstCase.TM2Boolean

end

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeTM2PolyUniform. -/
section P2MDyadicModule50

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

theorem family_circuit (n : ℕ) : (family P).circ n = circuit P n := rfl

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule50

/- Helper module Solutions.AdvantageBridgeQueryQuantum. -/
section P2MDyadicModule51

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

end P2MDyadicModule51

/- Helper module Solutions.AdvantageBridgeQueryMetadata. -/
section P2MDyadicModule52

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

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeTM2MultiOutput. -/
section P2MDyadicModule53

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

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

end

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeControlledRelocation. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ControlledRelocation

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open ControlledLetterPlan

theorem spectator_value {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : {c : Fin n // c ∉ Set.range w}) (p : Bits k×OutsideBits w) :
    (wireBitsEquiv w).symm p c.val=p.2 c := by
  have h := congrArg Prod.snd ((wireBitsEquiv w).apply_symm_apply p)
  exact congrFun h c

end InfoLossLAR.WorstCase.ControlledRelocation

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeNativeWordLayout. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordLayout

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledLetterPlan ControlledRelocation

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

variable {f : Str → Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

/-- Exact width of the entire generated reversible machine, including its
old input, all work/output wires, and the reserved guard wire. -/
def machineWidth (word : Str) : ℕ :=
  word.length+(generate P.machine.code P.machine.input P.machine.main P.machine.initial (request P word)).2.2.2.length+1

@[fun_prop] theorem machineWidth_poly : Poly (machineWidth P) := by unfold machineWidth;fun_prop

def width (n : ℕ) : ℕ := n+((compiled P n).ops.length+1)

private theorem machine_ops_transport {a b : ℕ} (he : a=b) (ha : 0<a) (hb : 0<b)
    (ticks length : ℕ) :
    (machineProgram ha P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).ops=
      (machineProgram hb P.machine.code P.machine.input P.machine.main P.machine.initial ticks length).ops := by
  cases he
  rfl

theorem machineWidth_eq (n : ℕ) : machineWidth P (unary n)=width P n := by
  have hwidth : (request P (unary n)).2.1.length=capacity P n := by
    rw [request_unary,List.length_replicate]
  have hw : 0<(request P (unary n)).2.1.length := hwidth.symm ▸ capacity_pos P n
  have ht : (request P (unary n)).2.2.length=P.time.eval n := by
    rw [request_unary,List.length_replicate]
  have hn : (request P (unary n)).1.length=n := by rw [request_unary,List.length_replicate]
  have hh :=(generate_machineProgram P.machine.code P.machine.input P.machine.main P.machine.initial
    (request P (unary n)) hw).1
  have ho:=machine_ops_transport P hwidth hw (capacity_pos P n) (P.time.eval n) n
  rw [ht,hn,ho] at hh
  unfold machineWidth
  rw [hh,List.length_map]
  simp only [unary,List.length_replicate,compiled,width]
  omega

def slots (word : Str) : List Unit := List.replicate (p.eval word.length) ()

@[fun_prop] theorem slots_poly : Poly (slots p) := by
  have hh :=Poly.comp (polynomialSlots_poly p) (by fun_prop : Poly (fun word : Str => word.map (fun _ => ())))
  unfold slots
  simpa only [List.length_map] using hh

theorem slots_length (word : Str) : (slots p word).length=p.eval word.length := by
  simp only [slots,List.length_replicate]

attribute [local irreducible] machineWidth slots

end InfoLossLAR.WorstCase.NativeWordLayout

end

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeNativeWordSerializer. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000

set_option maxRecDepth 10000

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordDescription

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout NativeWordCoherent ControlledNativeGates ControlledNativeCode

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator RPN

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

/-- A bounded total emitter, so invalid binary addresses cannot cause an
exponential unary output. The correctness theorem uses only valid gate codes. -/
def gateWord (ticks : List Unit) (gate : GateCode) : Str :=
  boundedNat (List.replicate 4 ()) gate.1++boundedNat ticks gate.2.1++
    if gate.1=4 then boundedNat ticks gate.2.2 else []

@[fun_prop] theorem gateWord_poly : Poly (fun x : List Unit×GateCode => gateWord x.1 x.2) := by
  unfold gateWord
  fun_prop

theorem gateWord_encode {m : ℕ} (ticks : List Unit) (gate : Instr m) (h : m≤ ticks.length) :
    gateWord ticks (encodeInstr gate)=encInstr gate := by
  cases gate with
  | h i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 0 (by decide)]
    simp
  | s i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 1 (by decide)]
    simp
  | t i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 2 (by decide)]
    simp
  | x i =>
    have hi:=i.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq (List.replicate 4 ()) 3 (by decide)]
    simp
  | cnot i j hij =>
    have hi:=i.isLt.le.trans h
    have hj:=j.isLt.le.trans h
    simp only [gateWord,encodeInstr,encInstr]
    rw [boundedNat_eq ticks i.val hi,boundedNat_eq ticks j.val hj]
    rfl

variable {f : Str → Str} (program : PolyProgram id id f)

def forwardWords (word : Str) : List (List Str) :=
  (readCircuitLayers (readUnary (readUnary (quantumDescription program word)).2).2).2

@[fun_prop] theorem forwardWords_poly : Poly (forwardWords program) := by
  have hfirst : Poly (fun word => readUnary (quantumDescription program word)) :=
    Poly.comp readUnary_poly (quantumDescription_poly program)
  have hsecond : Poly (fun word => readUnary (readUnary (quantumDescription program word)).2) :=
    Poly.comp readUnary_poly (Poly.comp Poly.snd hfirst)
  unfold forwardWords
  exact Poly.comp Poly.snd (Poly.comp readCircuitLayers_poly (Poly.comp Poly.snd hsecond))

theorem forwardWords_code (n : ℕ) :
    forwardWords program (unary n)=(circuit program n).map (List.map encInstr) := by
  unfold forwardWords
  rw [quantumDescription_code]
  simp only [encFamilyAt,List.append_assoc,readUnary_append]
  have hh:=congrArg Prod.snd (readCircuitLayers_append ((family program).circ n) [])
  simpa only [List.append_nil,family_circuit] using hh

def totalSlots (word : Str) : List Unit := multiTotalSlots program word++List.replicate 5 ()

theorem totalSlots_bound (n : ℕ) : width program n+5≤(totalSlots program (unary n)).length := by
  have hh:=ancilla_bound program n
  simp only [totalSlots,multiTotalSlots,List.length_append,List.length_map,List.length_replicate,
    List.length_singleton,unary]
  unfold width
  omega

variable (words : Str → List ℕ) (hw : Poly words) (p q : Polynomial ℕ)

end InfoLossLAR.WorstCase.NativeWordDescription

end

end P2MDyadicModule56

/- Helper module ProgramGate. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity ControlledLetterPlan ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

variable {n : ℕ}

def clearAt (a : Fin n) (ψ : QState n) := ∀ x : Bits n, x a=true → ψ x=0

def phaseWord (c t a : Fin n) (hct : c ≠ t) (hca : c ≠ a) (hta : t ≠ a) (T : Bool) :
    List (Instr n) :=
  toffoliGates c t a hct hca hta ++ [if T then .t a else .s a] ++ toffoliGates c t a hct hca hta

private noncomputable def phase (T : Bool) (x : Bool) : ℂ :=
  if x then (if T then Complex.exp (Complex.I*Real.pi/4) else Complex.I) else 1

private theorem diag (t : Fin n) (T : Bool) (ψ : QState n) (x : Bits n) :
    (if T then (.t t : Instr n) else .s t).apply ψ x = phase T (x t)*ψ x := by
  cases T <;> cases ht : x t <;>
    simp [Instr.apply,apply1,tMat,sMat,phase,ht] <;>
    rw [← ht,Function.update_eq_self]

theorem phaseWord_apply (c t a : Fin n) (hct : c ≠ t) (hca : c ≠ a) (hta : t ≠ a)
    (T : Bool) (ψ : QState n) (hψ : clearAt a ψ) :
    runLayer (phaseWord c t a hct hca hta T) ψ =
    fun x => if x c then (if T then (.t t : Instr n) else .s t).apply ψ x else ψ x := by
  have hψ' : runLayer [if T then (.t a : Instr n) else .s a] =
      (fun s => (if T then (.t a : Instr n) else .s a).apply s) := rfl
  rw [phaseWord,runLayer_append,runLayer_append,toffoliGates_semantics,toffoliGates_semantics,hψ']
  funext x
  simp only [diag,Function.update_self,Function.update_of_ne hca,Function.update_of_ne hta,
    Function.update_idem]
  cases hc : x c <;> cases ht : x t <;> cases ha : x a <;>
    simp [hc,ht,ha,phase,Bool.xor] <;>
    first | rw [← ha,Function.update_eq_self] <;> simp [hψ x ha] | simp [hψ x ha]

def disjointFrom (c : Fin n) (g : Instr n) := c ∉ g.support

def controlWord (c a : Fin n) (hc : c≠a) (g : Instr n) (h : disjointFrom c g) (ha : disjointFrom a g) :
    List (Instr n) := match g with
  | .h i => ControlledHadamard.gates c i (by simpa [disjointFrom,Instr.support] using h)
  | .x i => [.cnot c i (by simpa [disjointFrom,Instr.support] using h)]
  | .t i => phaseWord c i a (by simpa [disjointFrom,Instr.support] using h) hc
      (Ne.symm (by simpa [disjointFrom,Instr.support] using ha)) true
  | .s i => phaseWord c i a (by simpa [disjointFrom,Instr.support] using h) hc
      (Ne.symm (by simpa [disjointFrom,Instr.support] using ha)) false
  | .cnot i j hij => toffoliGates c i j (by simp_all [disjointFrom,Instr.support])
      (by simp_all [disjointFrom,Instr.support]) hij

theorem controlWord_apply (c a : Fin n) (hc : c≠a) (g : Instr n)
    (h : disjointFrom c g) (ha : disjointFrom a g) (ψ : QState n) (hψ : clearAt a ψ) :
    runLayer (controlWord c a hc g h ha) ψ = fun x => if x c then g.apply ψ x else ψ x := by
  cases g with
  | h t => exact ControlledHadamard.gates_semantics _ _ _ _
  | x t => exact (ControlledHadamard.controlled_X c t (by simpa [disjointFrom,Instr.support] using h) ψ).symm
  | t t => exact phaseWord_apply _ _ _ _ _ _ true ψ hψ
  | s t => exact phaseWord_apply _ _ _ _ _ _ false ψ hψ
  | cnot i j hij =>
    rw [controlWord,toffoliGates_semantics]
    funext x
    cases hxc : x c <;> simp [hxc,Instr.apply,cnotState]

def codes (v : (ℕ × ℕ) × GateCode) : List GateCode :=
  let c := v.1.1
  let a := v.1.2
  let g := v.2
  let t := g.2.1
  let tof := (ControlledPlanNative.cnotPlan c t a).map Prod.fst
  if g.1=0 then (ControlledPlanNative.hPlan c t).map Prod.fst
  else if g.1=1 then tof ++ [(1,a,0)] ++ tof
  else if g.1=2 then tof ++ [(2,a,0)] ++ tof
  else if g.1=3 then [(4,c,t)]
  else (ControlledPlanNative.cnotPlan c t g.2.2).map Prod.fst

@[fun_prop] theorem codes_poly : Poly codes := by unfold codes;fun_prop

theorem codes_exact (c a : Fin n) (hc : c≠a) (g : Instr n) (h : disjointFrom c g) (ha : disjointFrom a g) :
    codes ((c.val,a.val),encodeInstr g) = (controlWord c a hc g h ha).map encodeInstr := by
  cases g <;> rfl

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule57

/- Helper module ProgramRun. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

variable {k n : ℕ}

abbrev Outside (w : Fin k ↪ Fin n) := {c : Fin n // c ∉ Set.range w}

abbrev Op (w : Fin k ↪ Fin n) (a : Outside w) := {c : Outside w // c≠a} × Instr k

theorem avoids (w : Fin k ↪ Fin n) (c : Outside w) (g : Instr k) :
    disjointFrom c.val (relocateInstr w g) := by
  unfold disjointFrom
  rw [relocateInstr_support]
  intro hin
  obtain ⟨i,_,h⟩ := Finset.mem_image.mp hin
  exact c.property ⟨i,h⟩

def word (w : Fin k ↪ Fin n) (a : Outside w) (o : Op w a) :=
  controlWord o.1.val.val a.val (fun h => o.1.property (Subtype.ext h)) (relocateInstr w o.2)
    (avoids w _ _) (avoids w _ _)

def circuit (w : Fin k ↪ Fin n) (a : Outside w) (ops : List (Op w a)) :=
  ops.flatMap (word w a)

def chosen {w : Fin k ↪ Fin n} {a : Outside w} (ops : List (Op w a)) (r : OutsideBits w) :=
  ops.filterMap (fun o => if r o.1.val then some o.2 else none)

theorem step (w : Fin k ↪ Fin n) (a : Outside w) (o : Op w a) (ψ : QState n)
    (hψ : clearAt a.val ψ) :
    splitState w (runLayer (word w a o) ψ) = fun p =>
      if p.2 o.1.val then o.2.apply (fun j => splitState w ψ (j,p.2)) p.1
      else splitState w ψ p := by
  rw [word,controlWord_apply _ _ _ _ _ _ _ hψ]
  funext p
  change (if (wireBitsEquiv w).symm p o.1.val.val then
    (relocateInstr w o.2).apply ψ ((wireBitsEquiv w).symm p) else
    ψ ((wireBitsEquiv w).symm p))=_
  rw [ControlledRelocation.spectator_value]
  have hs := congrFun (relocateInstr_split w o.2 ψ) p
  change (relocateInstr w o.2).apply ψ ((wireBitsEquiv w).symm p)=_ at hs
  rw [hs]
  rfl

theorem step_clear (w : Fin k ↪ Fin n) (a : Outside w) (o : Op w a) (ψ : QState n)
    (hψ : clearAt a.val ψ) : clearAt a.val (runLayer (word w a o) ψ) := by
  intro x hx
  let p := wireBitsEquiv w x
  have h (i : Bits k) : splitState w ψ (i,p.2)=0 := hψ _ (by
    rw [ControlledRelocation.spectator_value]
    exact hx)
  have hz : o.2.apply (fun i => splitState w ψ (i,p.2))=0 := by
    have hfun : (fun i => splitState w ψ (i,p.2)) = (0 : QState k) := funext h
    rw [hfun];exact (instrLinearMap o.2).map_zero
  have he := congrFun (step w a o ψ hψ) p
  change runLayer (word w a o) ψ ((wireBitsEquiv w).symm ((wireBitsEquiv w) x))=_ at he
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  change (if p.2 o.1.val then o.2.apply (fun j => splitState w ψ (j,p.2)) p.1 else
    splitState w ψ (p.1,p.2))=0
  rw [hz,h];simp

theorem simulate (w : Fin k ↪ Fin n) (a : Outside w) (ops : List (Op w a)) (ψ : QState n)
    (hψ : clearAt a.val ψ) :
    splitState w (runLayer (circuit w a ops) ψ) = fun p =>
      runLayer (chosen ops p.2) (fun j => splitState w ψ (j,p.2)) p.1 := by
  induction ops generalizing ψ with
  | nil => rfl
  | cons o os ih =>
    change splitState w (runLayer (word w a o ++ circuit w a os) ψ)=_
    rw [runLayer_append,ih _ (step_clear w a o ψ hψ),step w a o ψ hψ]
    funext p
    cases hb : p.2 o.1.val <;>
      simp only [chosen,List.filterMap_cons,hb,Bool.false_eq_true,if_false,if_true,runLayer,List.foldl_cons]
    all_goals rfl

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule58

/- Helper module ProgramGrid. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {k n : ℕ}

def addr (k : ℕ) (g : GateCode) := (g.1*(k+1)+g.2.1)*(k+1)+g.2.2

def gateAt (k u : ℕ) : GateCode := (u/(k+1)/(k+1),u/(k+1)%(k+1),u%(k+1))

theorem field_bounds (g : Instr k) : (encodeInstr g).1<5 ∧
    (encodeInstr g).2.1<k+1 ∧ (encodeInstr g).2.2<k+1 := by
  cases g <;> simp [encodeInstr] <;> omega

theorem address_fits (g : Instr k) : addr k (encodeInstr g) < 5*(k+1)*(k+1) := by
  obtain ⟨ht,hi,hj⟩ := field_bounds g
  let u := encodeInstr g
  have step (a b : ℕ) (hb : b<k+1) : a*(k+1)+b < (a+1)*(k+1) := by rw [Nat.add_mul];omega
  have h1 : u.1*(k+1)+u.2.1 < 5*(k+1) := (step _ _ hi).trans_le (Nat.mul_le_mul_right _ ht)
  exact (step _ _ hj).trans_le (Nat.mul_le_mul_right _ h1)

theorem address_gate (g : Instr k) : gateAt k (addr k (encodeInstr g))=encodeInstr g := by
  obtain ⟨_,hi,hj⟩ := field_bounds g
  rcases he : encodeInstr g with ⟨t,i,j⟩
  rw [he] at hi hj
  change i<k+1 at hi
  change j<k+1 at hj
  have hd (a b : ℕ) (hb : b<k+1) : (a*(k+1)+b)/(k+1)=a := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.zero_lt_succ k),Nat.div_eq_of_lt hb,Nat.zero_add]
  simp [addr,gateAt,hd _ _ hj,hd _ _ hi,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj]

def indexTape (wires : List Unit) :=
  (wires++[()]).flatMap (fun _ => (wires++[()]).flatMap (fun _ => List.replicate 5 ()))

@[fun_prop] theorem indexTape_poly : Poly indexTape := by unfold indexTape;fun_prop

theorem indexTape_length (wires : List Unit) : (indexTape wires).length=5*(wires.length+1)*(wires.length+1) := by
  simp [indexTape,List.length_flatMap,List.sum_replicate];ring

private theorem selected_once {α β : Type*} [DecidableEq α] (l : List α) (h : l.Nodup) (v : α) (hv : v∈l) (g : β) :
    l.filterMap (fun x => if x=v then some g else none) = [g] := by
  induction l with
  | nil => simp at hv
  | cons a l ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp h
    by_cases ha : a=v
    · subst a
      have h0 : l.filterMap (fun x => if x=v then some g else none)=[] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro x hx; simp [show x≠v by rintro rfl;exact hn hx]
      simp [h0]
    · have hmem : v∈l := (List.mem_cons.mp hv).resolve_left (Ne.symm ha)
      simp [ha,ih ht hmem]

abbrev Controls (w : Fin k ↪ Fin n) (a : Outside w) := ℕ → ℕ → {c : Outside w // c≠a}

def rowOps (w : Fin k ↪ Fin n) (a : Outside w) (ctrl : Controls w a) (slot : ℕ) :=
  (List.range (5*(k+1)*(k+1))).filterMap fun index =>
    (decodeGate k (gateAt k index)).map (fun g => (ctrl slot index,g))

def allOps (w : Fin k ↪ Fin n) (a : Outside w) (ctrl : Controls w a) (slots : ℕ) :=
  (List.range slots).flatMap (rowOps w a ctrl)

theorem row_chosen (w : Fin k ↪ Fin n) (a : Outside w) (ctrl : Controls w a)
    (slot : ℕ) (r : OutsideBits w) (want : Option (Instr k))
    (hw : ∀ j<5*(k+1)*(k+1), r (ctrl slot j).val = decide (want.map (fun g => addr k (encodeInstr g))=some j)) :
    chosen (rowOps w a ctrl slot) r = want.toList := by
  unfold rowOps chosen
  rw [List.filterMap_filterMap]
  cases want with
  | none =>
    apply List.filterMap_eq_nil_iff.mpr
    intro x hx;have hh := hw x (List.mem_range.mp hx); cases h : decodeGate k (gateAt k x) <;> simp [h,hh]
  | some g =>
    have hfun (x : ℕ) (hx : x ∈ List.range (5*(k+1)*(k+1))) :
        (((decodeGate k (gateAt k x)).map (fun g => (ctrl slot x,g))).bind
          (fun op => if r op.1.val then some op.2 else none)) =
        (if x=addr k (encodeInstr g) then some g else none) := by
      have hh := hw x (List.mem_range.mp hx)
      by_cases he : x=addr k (encodeInstr g)
      · subst x; simp [address_gate,decode_encode,hh]
      · cases h : decodeGate k (gateAt k x) <;> simp [h,hh,he,Ne.symm he]
    rw [List.filterMap_congr hfun]
    exact selected_once _ List.nodup_range _ (List.mem_range.mpr (address_fits _)) _

theorem all_chosen (w : Fin k ↪ Fin n) (a : Outside w) (ctrl : Controls w a)
    (slots : ℕ) (r : OutsideBits w) (gs : List (Instr k)) (hs : gs.length ≤ slots)
    (hw : ∀ i<slots, ∀ code<5*(k+1)*(k+1), r (ctrl i code).val = decide ((gs[i]?).map (fun g => addr k (encodeInstr g))=some code)) :
    chosen (allOps w a ctrl slots) r = gs := by
  have hp (m : ℕ) (hm : m ≤ slots) : chosen (allOps w a ctrl m) r = gs.take m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [allOps,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      unfold chosen
      rw [List.filterMap_append]
      change chosen (allOps w a ctrl m) r ++ chosen (rowOps w a ctrl m) r=_
      rw [ih (by omega),row_chosen w a ctrl m r (gs[m]?) (hw m (by omega)),List.take_add_one]
  rw [hp slots (le_refl _),List.take_of_length_le hs]

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule59

/- Helper module ProgramEmit. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

open Integration9_9.TM2PolynomialBudget

@[fun_prop] theorem gateAt_poly : Poly (fun x : ℕ×ℕ => gateAt x.1 x.2) := by unfold gateAt;fun_prop

abbrev Settings := (List Unit × List Unit) × List GateCode

def gateIds (s : Settings) := s.2.map (fun g => addr s.1.1.length g)

@[fun_prop] theorem gateIds_poly : Poly gateIds := by unfold gateIds addr;fun_prop

def tableTicks (s : Settings) := s.1.2.flatMap (fun _ => indexTape s.1.1)

@[fun_prop] theorem tableTicks_poly : Poly tableTicks := by unfold tableTicks;fun_prop

def flag (v : List ℕ × (ℕ×ℕ)) :=
  decide (v.2.1<v.1.length) && decide (v.1[v.2.1]?.getD 0=v.2.2)

@[fun_prop] theorem flag_poly : Poly flag := by unfold flag;fun_prop

theorem flag_eq (l : List ℕ) (i j : ℕ) : flag (l,(i,j)) = decide (l[i]?=some j) := by
  by_cases h : i<l.length
  · simp [flag,h,List.getElem?_eq_getElem h]
  · simp [flag,h,List.getElem?_eq_none (by omega : l.length ≤ i)]

def controlBits (s : Settings) : Str :=
  let width := (indexTape s.1.1).length
  (List.range (tableTicks s).length).map (fun i => flag (gateIds s,(i/width,i%width)))

@[fun_prop] theorem controlBits_poly : Poly controlBits := by
  unfold controlBits
  apply Poly.list_map
  · exact Poly.comp flag_poly (by fun_prop)
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=tableTicks) Poly.list_indices tableTicks_poly

theorem table_length (s : Settings) : (controlBits s).length=s.1.2.length*(indexTape s.1.1).length := by
  simp [controlBits,tableTicks,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

theorem control_value (s : Settings) (t u : ℕ) (ht : t<s.1.2.length) (hu : u<(indexTape s.1.1).length) :
    (controlBits s)[t*(indexTape s.1.1).length+u]?=some (decide ((gateIds s)[t]?=some u)) := by
  let W := (indexTape s.1.1).length
  have h : t*W+u<s.1.2.length*W := by
    calc _ < (t+1)*W := by rw [Nat.add_mul];omega
         _ ≤ _ := Nat.mul_le_mul_right W ht
  have hh : t*W+u < (controlBits s).length := h.trans_le (table_length s).symm.le
  rw [List.getElem?_eq_getElem hh]
  simp only [Option.some.injEq]
  simp only [controlBits,List.getElem_map,List.getElem_range,flag_eq]
  change decide ((gateIds s)[(t*W+u)/W]?=some ((t*W+u)%W))=_
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hu,Nat.zero_add,
    Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hu]

def liftedCode (base : ℕ) (g : GateCode) : GateCode :=
  (g.1,base+1+g.2.1,if g.1=4 then base+1+g.2.2 else 0)

def validCode (k : ℕ) (g : GateCode) : Bool :=
  decide (g.2.1<k) && (decide (g.1<4) || (decide (g.1=4) && decide (g.2.2<k) && !(decide (g.2.1=g.2.2))))

def gateCodes (base ctrl k i : ℕ) :=
  let g := gateAt k i
  if validCode k g then codes ((ctrl,base), liftedCode base g) else []

@[fun_prop] theorem gateCodes_poly : Poly (fun x : (ℕ×ℕ)×(ℕ×ℕ) => gateCodes x.1.1 x.1.2 x.2.1 x.2.2) := by
  let ctx := fun x : (ℕ×ℕ)×(ℕ×ℕ) => (x.1, (x.2.1,gateAt x.2.1 x.2.2))
  have hctx : Poly ctx := by unfold ctx;exact Poly.pair Poly.fst (Poly.pair (by fun_prop) (Poly.comp gateAt_poly Poly.snd))
  apply Poly.comp (f:=fun s : (ℕ×ℕ)×(ℕ×GateCode) =>
    if validCode s.2.1 s.2.2 then codes ((s.1.2,s.1.1),liftedCode s.1.1 s.2.2) else []) (g:=ctx) _ hctx
  have hv : Poly (fun s : (ℕ×ℕ)×(ℕ×GateCode) => validCode s.2.1 s.2.2) := by unfold validCode;fun_prop
  have hc : Poly (fun s : (ℕ×ℕ)×(ℕ×GateCode) => codes ((s.1.2,s.1.1),liftedCode s.1.1 s.2.2)) := by
    apply Poly.comp (g:=fun s : (ℕ×ℕ)×(ℕ×GateCode) => ((s.1.2,s.1.1),liftedCode s.1.1 s.2.2)) codes_poly
    unfold liftedCode;fun_prop
  exact Poly.ite_prop (by simpa using hv) hc (Automatic.Poly.const [])

variable {f : Str→Str} (P : PolyProgram id id f)

noncomputable def emit (p q : Polynomial ℕ) (w : Str) : List GateCode :=
  let data := NativeWordLayout.slots p w
  let slots := NativeWordLayout.slots q w
  let ids := indexTape data
  (List.range slots.length).flatMap (fun t => (List.range ids.length).flatMap (fun j =>
    gateCodes (NativeWordLayout.machineWidth P w) (generatedProgramOutputAddress P w (t*ids.length+j)) data.length j))

@[fun_prop] theorem emit_poly (p q : Polynomial ℕ) : Poly (emit P p q) := by
  unfold emit
  have hdata := NativeWordLayout.slots_poly p
  have hslots := NativeWordLayout.slots_poly q
  have hd : Poly (fun w : Str => List.range (indexTape (NativeWordLayout.slots p w)).length) :=
    Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=fun w => indexTape (NativeWordLayout.slots p w)) Poly.list_indices (Poly.comp indexTape_poly hdata)
  have ht : Poly (fun w : Str => List.range (NativeWordLayout.slots q w).length) :=
    Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=NativeWordLayout.slots q) Poly.list_indices hslots
  apply Poly.list_flatMap _ ht
  apply Poly.list_flatMap _ (Poly.comp hd Poly.fst)
  exact Poly.comp (g:=fun x : (Str×ℕ)×ℕ => ((NativeWordLayout.machineWidth P x.1.1,generatedProgramOutputAddress P x.1.1 (x.1.2*(indexTape (NativeWordLayout.slots p x.1.1)).length+x.2)),((NativeWordLayout.slots p x.1.1).length,x.2))) gateCodes_poly (by fun_prop)

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule60

/- Helper module ProgramLayout. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

noncomputable section

def wires (base k : ℕ) : Fin k ↪ Fin (base+1+k) := Fin.natAddEmb (base+1)

def helper (base k : ℕ) : Outside (wires base k) :=
  ⟨⟨base,by omega⟩,by
    rintro ⟨i,hi⟩; have h := congrArg Fin.val hi
    change base+1+i.val=base at h;omega⟩

def rawControl (base k : ℕ) (i : Fin base) : {c : Outside (wires base k) // c≠helper base k} :=
  ⟨⟨⟨i.val,by omega⟩,by
    rintro ⟨j,h⟩;have he := congrArg Fin.val h
    change base+1+j.val=i.val at he;omega⟩,by
    intro h;have he := congrArg (fun j : Outside (wires base k) => j.val.val) h
    change i.val=base at he;omega⟩

variable {f : Str→Str} (P : PolyProgram id id f)

def index (l x : ℕ) : Fin (capacity P l) := if h : x<capacity P l then ⟨x,h⟩ else ⟨0,capacity_pos P l⟩

def cpus (l k : ℕ) : Controls (wires (NativeWordLayout.width P l) k) (helper _ _) :=
  fun t j => rawControl _ k (outputWire P l (index P l (t*(5*(k+1)*(k+1))+j)) (some true))

theorem cpu_address (l k t j : ℕ) (h : t*(5*(k+1)*(k+1))+j<capacity P l) :
    (cpus P l k t j).val.val.val = generatedProgramOutputAddress P (unary l) (t*(5*(k+1)*(k+1))+j) := by
  let x := t*(5*(k+1)*(k+1))+j
  have hx : (index P l x).val=x := by simp only [index,dif_pos (show x<capacity P l from h)]
  change (outputWire P l (index P l x) (some true)).val=generatedProgramOutputAddress P (unary l) x
  rw [←hx,generatedProgramOutputAddress_eq,hx]

theorem record_eq (k : ℕ) (g : GateCode) :
    (decodeGate k g).isSome=validCode k g ∧ ∀ (i : Instr k), decodeGate k g=some i →
      encodeInstr i = (g.1,g.2.1,if g.1=4 then g.2.2 else 0) := by
  rcases g with ⟨tag,i,j⟩
  have splitTag : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ 5 ≤ tag := by omega
  rcases splitTag with h|h|h|h|h|h
  all_goals first
    | subst tag;by_cases hi : i<k <;> by_cases hj : j<k <;> by_cases he : i=j <;>
        simp [decodeGate,validCode,hi,hj,he,encodeInstr] <;> rintro _ rfl <;> rfl
    | obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
      rw [Nat.add_comm 5 t]
      by_cases hi : i<k <;> simp [decodeGate,validCode,hi] <;> omega

theorem lift_encode (base k : ℕ) (g : Instr k) :
    encodeInstr (relocateInstr (wires base k) g)=liftedCode base (encodeInstr g) := by
  cases g <;> rfl

theorem one_code {k : ℕ} (base : ℕ) (c : Fin base) (s : ℕ) :
    gateCodes base c.val k s =
      ((decodeGate k (gateAt k s)).map (fun g =>
        (word (wires base k) (helper base k) (rawControl base k c,g)).map encodeInstr)).getD [] := by
  let v := gateAt k s
  obtain ⟨hv,he⟩ := record_eq k v
  cases hd : decodeGate k v with
  | none =>
    have hz : validCode k v=false := by rw [←hv,hd];rfl
    change (if validCode k v then _ else _) = []
    rw [hz];rfl
  | some g =>
    have hz : validCode k v=true := by rw [←hv,hd];rfl
    change (if validCode k v then _ else _) = _
    rw [hz]
    change codes ((c.val,base),liftedCode base v) = (word _ _ _).map encodeInstr
    unfold word
    rw [←codes_exact, lift_encode,he _ hd]
    unfold liftedCode
    by_cases h : v.1=4 <;> simp [h,helper,rawControl]

end

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule61

/- Helper module ProgramExact. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

noncomputable section

variable {f : Str→Str} (P : PolyProgram id id f)

private theorem expanded {α β γ : Type*} (l : List α) (f : α→Option β) (g : β→List γ) :
    (l.filterMap f).flatMap g=l.flatMap (fun x => ((f x).map g).getD []) := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [h,ih]

theorem emit_code (p q : Polynomial ℕ) (l : ℕ)
    (hf : q.eval l * (5*(p.eval l+1)*(p.eval l+1)) ≤ capacity P l) :
    emit P p q (unary l) =
      (circuit (wires (NativeWordLayout.width P l) (p.eval l)) (helper _ _)
        (allOps _ _ (cpus P l (p.eval l)) (q.eval l))).map encodeInstr := by
  let k := p.eval l
  let base := NativeWordLayout.width P l
  let W := 5*(k+1)*(k+1)
  simp only [emit,NativeWordLayout.slots_length,indexTape_length,NativeWordLayout.machineWidth_eq,
    circuit,allOps,List.map_flatMap,List.flatMap_assoc,show (unary l).length=l by simp [unary]]
  apply List.flatMap_congr
  intro t ht
  unfold rowOps
  rw [expanded]
  apply List.flatMap_congr
  intro j hj
  have hcap : t*W+j < capacity P l := by
    have hh : t<q.eval l := List.mem_range.mp ht
    have h' : j<W := List.mem_range.mp hj
    calc
      _ < (t+1)*W := by rw [Nat.add_mul];omega
      _ ≤ q.eval l*W := Nat.mul_le_mul_right W hh
      _ ≤ _ := hf
  rw [←cpu_address P l k t j hcap]
  let a : Fin base := outputWire P l (index P l (t*W+j)) (some true)
  change gateCodes base a.val k j = _
  refine (one_code (k:=k) base a j).trans ?_
  change ((decodeGate k (gateAt k j)).map _).getD [] = (((decodeGate k (gateAt k j)).map _).map _).getD []
  cases hd : decodeGate k (gateAt k j) <;> rfl

end

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule62

/- Helper module ProgramMachine. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

open Integration9_9.TM2PlatformSerialization NativeWordDescription TM2Boolean.RPN

noncomputable section

def raw (gen : Str→List GateCode) (p q : Polynomial ℕ) (s : Str) : Str :=
  controlBits ((NativeWordLayout.slots p s,NativeWordLayout.slots q s),gen s)

@[fun_prop] theorem raw_poly (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) :
    Poly (raw gen p q) := by
  apply Poly.comp (f:=controlBits) (g:=fun s => ((NativeWordLayout.slots p s,NativeWordLayout.slots q s),gen s))
  · exact controlBits_poly
  · fun_prop

def cpu (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) :=
  Integration9_9.LARCoinLayout.rawPolyProgram (raw_poly gen hg p q)

theorem fits (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) (l : ℕ) :
    q.eval l*(5*(p.eval l+1)*(p.eval l+1)) ≤ capacity (cpu gen hg p q) l := by
  have h := actualOutput_length_lt_capacity (cpu gen hg p q) (unary l)
  change (controlBits _).length<_ at h
  simp only [table_length,indexTape_length,NativeWordLayout.slots_length,show (unary l).length=l by simp [unary]] at h
  exact h.le

variable {f : Str→Str} (P : PolyProgram id id f) (p q : Polynomial ℕ)

def forward (l : ℕ) := relocateCircuit
  (Fin.castLEEmb (show NativeWordLayout.width P l ≤ NativeWordLayout.width P l+1+p.eval l by omega))
  (TM2Boolean.PolyProgramCircuit.circuit P l)

def body (l : ℕ) :=
  forward P p l ++ ((circuit (wires (NativeWordLayout.width P l) (p.eval l)) (helper _ _)
    (allOps _ _ (cpus P l (p.eval l)) (q.eval l)))).map (fun g => [g])

def ancillary (l : ℕ) := (compiled P l).ops.length+1+p.eval l

theorem shape (l : ℕ) : NativeWordLayout.width P l+1+p.eval l=l+(ancillary P p l+1) := by
  unfold NativeWordLayout.width ancillary;omega

def family : MFamily where
  anc := ancillary P p
  circ l := shape P p l ▸ body P p q l
  outLen l := p.eval l
  outW l i := ⟨NativeWordLayout.width P l+1+i.val,by rw [←shape];omega⟩

def tape (s : Str) := multiTotalSlots P s ++ [()] ++ NativeWordLayout.slots p s

@[fun_prop] theorem tape_poly : Poly (tape P p) := by unfold tape;fun_prop

theorem tape_fit (l : ℕ) : NativeWordLayout.width P l+1+p.eval l ≤ (tape P p (unary l)).length := by
  have h := NativeWordDescription.totalSlots_bound P l
  simp only [NativeWordDescription.totalSlots,List.length_append,List.length_replicate] at h
  simp only [tape,List.length_append,List.length_cons,List.length_nil,NativeWordLayout.slots_length,
    show (unary l).length=l by simp [unary]]
  omega

attribute [local irreducible] emit NativeWordLayout.machineWidth forwardWords

def desc (s : Str) : Str :=
  let ticks := tape P p s
  let base := NativeWordLayout.machineWidth P s
  let ws := NativeWordLayout.slots p s
  let ans := (List.range ws.length).map (fun i => boundedNat ticks (base+1+i))
  let layers := forwardWords P s ++ (emit P p q s).map (fun g => [gateWord ticks g])
  boundedNat ticks (base-s.length+ws.length) ++ serializeWords ans ++ serializeWords (layers.map serializeWords)

theorem desc_poly : Poly (desc P p q) := by
  unfold desc
  have hi : Poly (fun s : Str => List.range (NativeWordLayout.slots p s).length) :=
    Poly.comp (f:=fun xs : List Unit => List.range xs.length) (g:=NativeWordLayout.slots p) Poly.list_indices
      (NativeWordLayout.slots_poly p)
  dsimp only
  have hs : Poly (fun s : Str => (List.range (NativeWordLayout.slots p s).length).map
      (fun i => boundedNat (tape P p s) (NativeWordLayout.machineWidth P s+1+i))) :=
    Poly.list_map (by fun_prop) hi
  have hgate : Poly (fun s : Str => (emit P p q s).map (fun g => [gateWord (tape P p s) g])) :=
    Poly.list_map (by fun_prop) (emit_poly P p q)
  have hl : Poly (fun s : Str => forwardWords P s ++ (emit P p q s).map (fun g => [gateWord (tape P p s) g])) := by fun_prop
  have hls : Poly (fun s : Str => (forwardWords P s ++ (emit P p q s).map (fun g => [gateWord (tape P p s) g])).map serializeWords) :=
    Poly.list_map (Poly.comp serializeWords_poly Poly.snd) hl
  fun_prop

private theorem coeList {m : ℕ} (a : List (Fin m)) : (do let v ← a; pure v.val : List ℕ) = a.map Fin.val := by
  induction a with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons x.val) ih

private theorem transport_code {a b : ℕ} (h : a=b) (V : Layered a) :
    encCirc (h ▸ V)=encCirc V := by subst b;rfl

private theorem transport_ok {a b : ℕ} (h : a=b) (V : Layered a) (hV : ∀ s∈V,LayerOk s) :
    ∀ s∈(h ▸ V : Layered b), LayerOk s := by subst b; exact hV

theorem code_exact (l : ℕ) (fit : q.eval l*(5*(p.eval l+1)*(p.eval l+1)) ≤ capacity P l) :
    desc P p q (unary l)=(family P p q).encAt l := by
  have tfit := tape_fit P p l
  have hanc : NativeWordLayout.width P l-l+p.eval l=ancillary P p l := by
    unfold NativeWordLayout.width ancillary;omega
  have ha : ancillary P p l ≤ (tape P p (unary l)).length := (by rw [shape] at tfit;omega)
  have he (i : Fin (p.eval l)) : boundedNat (tape P p (unary l)) (NativeWordLayout.width P l+1+i.val)=
      encNat (NativeWordLayout.width P l+1+i.val) := boundedNat_eq _ _ (by omega)
  have ho : (List.range (p.eval l)).map (fun i => boundedNat (tape P p (unary l)) (NativeWordLayout.width P l+1+i))=
      (List.ofFn ((family P p q).outW l)).map (fun i => encNat i.val) := by
    apply List.ext_getElem
    · simp [family]
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact he ⟨i,by simpa [family] using hi⟩
  have hforward : (forward P p l).map (List.map encInstr)=(TM2Boolean.PolyProgramCircuit.circuit P l).map (List.map encInstr) := by
    unfold forward relocateCircuit
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left; intro row _
    first | simp only [List.map_map,Function.comp_def] | skip
    apply List.map_congr_left;intro g _;cases g <;> rfl
  simp only [desc,NativeWordLayout.machineWidth_eq,NativeWordLayout.slots_length,
    show (unary l).length=l by simp [unary],hanc,boundedNat_eq _ _ ha,ho,serializeWords_eq,forwardWords_code,
    ←hforward,emit_code _ _ _ _ fit,List.map_map,Function.comp_def]
  change _=encNat _++encStr _++encCirc (shape P p l ▸ body P p q l)
  rw [transport_code]
  simp only [encCirc,body,List.map_append,List.map_map,Function.comp_def,encLayer]
  simp only [gateWord_encode _ _ tfit,List.map_cons,List.map_nil,serializeWords_eq,coeList,List.map_map,Function.comp_def,encLayer]
  rfl

theorem machine_ok (l : ℕ) : ∀ s∈ (family P p q).circ l, LayerOk s := by
  apply transport_ok
  intro s hs
  rcases List.mem_append.mp hs with hl|hr
  · exact relocateCircuit_wellFormed _ _ (circuit_wellFormed P l) _ hl
  · obtain ⟨g,_,rfl⟩ := List.mem_map.mp hr
    simp [LayerOk]

theorem of_description (F : MFamily) (generator : Str→Str) (hg : PolyTimeComputable generator)
    (h : ∀ l,generator (unary l)=F.encAt l) (hok : ∀ l,∀ s∈F.circ l,LayerOk s) : IsMQPT F := by
  obtain ⟨C,hC⟩ := polynomial_output_length hg.some
  refine ⟨⟨_,hg,h⟩,hok,C,?_⟩
  intro l
  have hc := hC (unary l)
  change (generator (unary l)).length ≤ C.eval (unary l).length at hc
  rw [h] at hc
  simp only [MFamily.encAt,encStr,encCirc,encNat,unary,List.length_append,List.length_replicate,
    List.length_cons,List.length_nil,List.length_map,List.length_ofFn] at hc
  unfold depth
  have ho : ((do let a ← List.ofFn (F.outW l); pure a.val) : List ℕ).length=F.outLen l := by
    rw [coeList,List.length_map,List.length_ofFn]
  omega

end

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule63

/- Helper module ProgramInput. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit

noncomputable section

variable {f : Str→Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

def boot (s : Str) : Bits (NativeWordLayout.width P s.length+1+p.eval s.length) :=
  fun i => wordExtension s i.val

def started (s : Str) : Bits (NativeWordLayout.width P s.length+1+p.eval s.length) :=
  fun i => if h : i.val<NativeWordLayout.width P s.length then result P s ⟨i.val,h⟩ else false

theorem cpuRead (s : Str) (i : Fin (NativeWordLayout.width P s.length)) :
    started P p s ⟨i.val,by omega⟩=result P s i := by
  unfold started
  rw [dif_pos i.isLt]
  rfl

theorem boot_cpu (s : Str) :
    runLayered (forward P p s.length) (basis (boot P p s))=basis (started P p s) := by
  unfold forward
  apply relocateCircuit_basis
  · have h := circuit_basis P s
    rw [basisInput_eq_computationalBasis,wordExtension_basis] at h
    refine h.trans (congrArg computationalBasis ?_)
    funext i
    exact (cpuRead P p s i).symm
  · funext i
    have h : NativeWordLayout.width P s.length ≤ i.val.val := by
      by_contra! hh
      exact i.property ⟨⟨i.val.val,hh⟩, rfl⟩
    have h0 : s.length ≤ i.val.val := by
      apply le_trans _ h;unfold NativeWordLayout.width;omega
    change wordExtension s i.val.val=(if h : i.val.val<NativeWordLayout.width P s.length then _ else false)
    rw [dif_neg (Nat.not_lt.mpr h),wordExtension_after _ _ h0]

theorem started_data (s : Str) :
    (wireBitsEquiv (wires (NativeWordLayout.width P s.length) (p.eval s.length)) (started P p s)).1=
      fun _ => false := by
  funext i;change (if h : NativeWordLayout.width P s.length+1+i.val < NativeWordLayout.width P s.length then _ else false)=_
  rw [dif_neg (by omega)]

theorem started_clear (s : Str) :
    clearAt (helper (NativeWordLayout.width P s.length) (p.eval s.length)).val (basis (started P p s)) := by
  have hc : started P p s (helper (NativeWordLayout.width P s.length) (p.eval s.length)).val=false := by
    change (if h : NativeWordLayout.width P s.length<NativeWordLayout.width P s.length then _ else false)=_
    rw [dif_neg (lt_irrefl _)]
  intro x hx
  have h : x≠started P p s := by rintro rfl;rw [hc] at hx;contradiction
  simp [basis,h]

theorem controls_read (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) (s : Str)
    (gs : List (Instr (p.eval s.length))) (hgs : gen s=gs.map encodeInstr)
    (t : ℕ) (ht : t<q.eval s.length) (j : ℕ) (hj : j<5*(p.eval s.length+1)*(p.eval s.length+1)) :
    let P := cpu gen hg p q
    let w := wires (NativeWordLayout.width P s.length) (p.eval s.length)
    (wireBitsEquiv w (started P p s)).2 (cpus P s.length (p.eval s.length) t j).val =
      decide (gs[t]?.map (fun g => addr (p.eval s.length) (encodeInstr g))=some j) := by
  let C := cpu gen hg p q
  let k := p.eval s.length
  let W := 5*(k+1)*(k+1)
  have hjW : j<W := hj
  let i := t*W+j
  have hcap : i < capacity C s.length := by
    calc i < (t+1)*W := by dsimp [i];rw [Nat.add_mul];omega
         _ ≤ q.eval s.length*W := Nat.mul_le_mul_right _ ht
         _ ≤ _ := fits _ hg p q _
  let v := index C s.length i
  have hv : v.val=i := by simp only [v,index,dif_pos hcap]
  let o := outputWire C s.length v (some true)
  change started C p s ⟨o.val,_⟩=_
  rw [cpuRead C p s o]
  change result C s o = _
  rw [output_correct,hv]
  let S : Settings := ((NativeWordLayout.slots p s,NativeWordLayout.slots q s),gen s)
  have hW : (indexTape S.1.1).length=W := by simp [S,W,k,indexTape_length,NativeWordLayout.slots_length]
  have hi : (raw gen p q s)[i]?=some (decide ((gateIds S)[t]?=some j)) := by
    change (controlBits S)[i]?=_
    rw [show i=t*(indexTape S.1.1).length+j by rw [hW]]
    apply control_value
    · simpa [S,NativeWordLayout.slots_length] using ht
    · rwa [hW]
  rw [hi]
  simpa only [S,gateIds,hgs,List.map_map,Function.comp_def,List.getElem?_map,NativeWordLayout.slots_length,
    Option.some.injEq,decide_eq_true_eq,Bool.true_eq] using
    (show decide (some true=some (decide ((gateIds S)[t]?=some j)))=decide ((gateIds S)[t]?=some j) by simp)

end

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule64

/- Helper module ProgramOutput. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.ProgrammableStage

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit

open scoped BigOperators Classical

noncomputable section

private theorem split_basis {k n : ℕ} (w : Fin k ↪ Fin n) (v : Bits n) (x : Bits k) (r : OutsideBits w) :
    splitState w (basis v) (x,r)=if r=(wireBitsEquiv w v).2 then basis (wireBitsEquiv w v).1 x else 0 := by
  change (if (wireBitsEquiv w).symm (x,r)=v then _ else _) = _
  simp only [Equiv.symm_apply_eq,Prod.ext_iff,basis]
  split_ifs <;> simp_all

theorem body_run (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) (s : Str)
    (gs : List (Instr (p.eval s.length))) (hgs : gen s=gs.map encodeInstr) (hsize : gs.length ≤ q.eval s.length) :
    let P := cpu gen hg p q
    let w := wires (NativeWordLayout.width P s.length) (p.eval s.length)
    let r := (wireBitsEquiv w (started P p s)).2
    runLayered (body P p q s.length) (basis (boot P p s)) =
      initializedWires w r (runLayer gs (basis (fun _ => false))) := by
  let C := cpu gen hg p q
  let w := wires (NativeWordLayout.width C s.length) (p.eval s.length)
  let v := started C p s
  let r := (wireBitsEquiv w v).2
  change runLayered (body C p q s.length) (basis (boot C p s))=_
  rw [body,show ∀ {n : ℕ} (a b : Layered n) (ψ : QState n), runLayered (a++b) ψ=runLayered b (runLayered a ψ) from fun _ _ _ => List.foldl_append,boot_cpu,runLayered_singletons]
  apply funext
  intro y
  let z := wireBitsEquiv w y
  let c := cpus C s.length (p.eval s.length)
  let a := helper (NativeWordLayout.width C s.length) (p.eval s.length)
  let ops := allOps w a c (q.eval s.length)
  have hh := congrFun (simulate w a ops (basis v) (started_clear C p s)) z
  change runLayer (circuit w a ops) (basis v) ((wireBitsEquiv w).symm ((wireBitsEquiv w) y))=_ at hh
  rw [Equiv.symm_apply_apply] at hh
  change runLayer (circuit w a ops) (basis v) y=runLayer gs (basis (fun _ => false)) z.1*basis r z.2
  rw [hh]
  by_cases he : z.2=r
  · have hchoice : chosen ops z.2=gs := all_chosen w a c _ z.2 gs hsize (by
        intro i hi j hj
        rw [he]
        exact controls_read gen hg p q s gs hgs i hi j hj)
    rw [hchoice]
    have hs : (fun j => splitState w (basis v) (j,z.2)) = basis (fun _ => false) := by
      funext j; rw [split_basis,if_pos he,started_data]
    rw [hs];simp [basis,he]
  · have hs : (fun j => splitState w (basis v) (j,z.2)) = (0:QState _) := by
      funext j;rw [split_basis,if_neg he];rfl
    rw [hs,←runLayerLinearMap_apply,map_zero]
    simp [basis,he]

theorem born_read {k n : ℕ} (w : Fin k ↪ Fin n) (r : OutsideBits w) (φ : QState k) (E : Str→Prop) :
    (∑ y : Bits n, if E (List.ofFn fun i => y (w i)) then ‖initializedWires w r φ y‖^2 else 0)=
      ∑ z : Bits k, if E (List.ofFn z) then ‖φ z‖^2 else 0 := by
  calc _ = ∑ x : Bits k × OutsideBits w, if E (List.ofFn x.1) then ‖φ x.1*basis r x.2‖^2 else 0 :=
          Fintype.sum_equiv (wireBitsEquiv w) _ _ (fun _ => rfl)
       _ = _ := by
         rw [Fintype.sum_prod_type]
         apply Finset.sum_congr rfl
         intro t ht
         by_cases h : E (List.ofFn t)
         · simp only [h,if_true]
           rw [Finset.sum_eq_single r]
           · simp [basis]
           · intro x _ hx;simp [basis,hx]
           · simp
         · simp [h]

private theorem measure_cast {a b k : ℕ} (h : a=b) (V : Layered a) (x : Bits a) (read : Fin k→Fin a)
    (E : Str→Prop) :
    (∑ y : Bits b, if E (List.ofFn fun i => y (Fin.cast h (read i))) then
      ‖runLayered (h ▸ V) (basis (fun j => x (Fin.cast h.symm j))) y‖^2 else 0)=
    ∑ y : Bits a, if E (List.ofFn fun i => y (read i)) then ‖runLayered V (basis x) y‖^2 else 0 := by
  subst b;rfl

theorem native_born (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) (s : Str)
    (gs : List (Instr (p.eval s.length))) (hgs : gen s=gs.map encodeInstr) (hsize : gs.length ≤ q.eval s.length)
    (E : Str→Prop) :
    outputProb (family (cpu gen hg p q) p q) s E =
      ∑ z : Bits (p.eval s.length), if E (List.ofFn z) then ‖runLayer gs (basis (fun _ => false)) z‖^2 else 0 := by
  let C := cpu gen hg p q
  let w := wires (NativeWordLayout.width C s.length) (p.eval s.length)
  let v := started C p s
  let r := (wireBitsEquiv w v).2
  unfold outputProb
  rw [basisInput_eq_computationalBasis,wordExtension_basis]
  refine (measure_cast (shape C p s.length) (body C p q s.length) (boot C p s) w E).trans ?_
  rw [body_run gen hg p q s gs hgs hsize]
  exact born_read w r _ E

end

end InfoLossLAR.WorstCase.ProgrammableStage

end P2MDyadicModule65

/- Helper module PlanCode. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option maxHeartbeats 1300000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

variable {h k : ℕ}

abbrev Pin := ℕ×ℕ

def pin {h : ℕ} : Source h→Pin | .literal false => (0,0) | .literal true => (1,0) | .wire i => (2,i.val)

def loadCode (base i : ℕ) (p : Pin) : List GateCode :=
  if p.1=0 then [] else if p.1=1 then [(3,base+i,0)] else [(4,p.2,base+i)]

@[fun_prop] theorem loadCode_poly : Poly (fun x : (ℕ×ℕ)×Pin => loadCode x.1.1 x.1.2 x.2) := by
  unfold loadCode;fun_prop

def shifted (d : ℕ) (g : GateCode) : GateCode := (g.1,d+g.2.1,if g.1=4 then d+g.2.2 else 0)

@[fun_prop] theorem shifted_poly : Poly (fun x : ℕ×GateCode => shifted x.1 x.2) := by unfold shifted;fun_prop

abbrev Block := List Pin × List GateCode

def pack (a : Fin k→Source h) (U : Layered k) : Block :=
  (List.ofFn (fun i => pin (a i)), U.flatten.map encodeInstr)

def blockCode (d : ℕ) (b : Block) : List GateCode :=
  ((List.range b.1.length).flatMap (fun i => loadCode d i (b.1[i]?.getD (0,0)))) ++
    b.2.map (shifted d)

@[fun_prop] theorem blockCode_poly : Poly (fun x : ℕ×Block => blockCode x.1 x.2) := by
  unfold blockCode
  have hi : Poly (fun x : ℕ×Block => List.range x.2.1.length) :=
    Poly.comp (f:=fun a : List Pin => List.range a.length) (g:=fun x : ℕ×Block => x.2.1) Poly.list_indices (by fun_prop)
  have hload : Poly (fun x : ℕ×Block => (List.range x.2.1.length).flatMap (fun i => loadCode x.1 i (x.2.1[i]?.getD (0,0)))) :=
    Poly.list_flatMap (Poly.comp (g:=fun u : (ℕ×Block)×ℕ => ((u.1.1,u.2),u.1.2.1[u.2]?.getD (0,0))) loadCode_poly (by fun_prop)) hi
  have hs : Poly (fun x : ℕ×Block => x.2.2.map (shifted x.1)) :=
    Poly.list_map (Poly.comp (g:=fun u : (ℕ×Block)×GateCode => (u.1.1,u.2)) shifted_poly (by fun_prop)) (by fun_prop)
  fun_prop

theorem loadCode_eq (i : Fin k) (s : Source h) : loadCode h i.val (pin s)=(gate i s).map encodeInstr := by
  cases s with
  | literal b => cases b <;> rfl
  | wire j => rfl

theorem block_eq (a : Fin k → Source h) (U : Layered k) :
    blockCode h (pack a U) = (stage a U).flatten.map encodeInstr := by
  simp only [blockCode,pack,List.length_ofFn,stage,List.flatten_append,
    relocateCircuit,List.map_append,List.map_flatMap,List.map_map]
  congr 1
  · rw [show List.range k = (List.finRange k).map Fin.val by simp]
    rw [show ((load a).map (fun g => [g])).flatten=load a by induction load a with | nil => rfl | cons x xs ih => simpa using ih]
    simp only [List.flatMap_map,load,List.map_flatMap,Function.comp_def,List.getElem?_ofFn,Fin.isLt,
      dif_pos,Option.getD_some,loadCode_eq]
  · induction U with
    | nil => rfl
    | cons row rest ih =>
      simp only [List.flatten_cons,List.map_cons,List.map_append,←ih]
      congr 1
      simp only [List.map_map,Function.comp_def]
      apply List.map_congr_left;intro g _;cases g <;> rfl

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule66

/- Helper module PlanTrace. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open scoped Classical BigOperators

noncomputable section

variable {s h k : ℕ}

def zeroBits (n : ℕ) : Bits n := fun _ => false

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages

end P2MDyadicModule67

/- Helper module Solutions.AdvantageBridgeBundleEmitter. -/
section P2MDyadicModule68

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

end InfoLossLAR.WorstCase

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeLoadedBatchPostFrame. -/
section P2MDyadicModule69

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

end Integration9_9.LoadedBatch.PostComposition

end

end P2MDyadicModule69

/- Helper module AdviceInput. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1400000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open QAlgorithms.Papers.Independent.Renew46.P12

open TM2Boolean TM2Boolean.PolyProgramCircuit

open scoped Classical BigOperators

noncomputable section

def literals {n : ℕ} (w : Str) (a : ℕ) : Fin (w.length+(a+1))→Source n :=
  Fin.append (fun i => Source.literal (toBits w i)) (fun _ => Source.literal false)

def prepare (n : ℕ) (w : Str) (a : ℕ) := stage (literals (n:=n) w a) ([] : Layered _)

theorem literals_read {n : ℕ} (w : Str) (a : ℕ) (x : Bits n) :
    (fun i => (literals w a i).read x)=Fin.append (toBits w) (zeroBits (a+1)) := by
  funext i;refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [literals,Source.read,zeroBits]

theorem prepare_basis {n : ℕ} (x : Bits n) (w : Str) (a : ℕ) :
    runLayered (prepare n w a) (basis (Fin.append x (zeroBits _)))=
      basis (Fin.append x (Fin.append (toBits w) (zeroBits _))) := by
  have ht {l m : ℕ} (u : Bits l) (v : Bits m) : basis (Fin.append u v)=tensorState (basis u) (basis v) := computationalBasis_tensor u v
  rw [ht,ht x]
  funext z
  obtain ⟨⟨l,r⟩,rfl⟩ := (qubitsAppendEquiv n (w.length+(a+1))).symm.surjective z
  change runLayered (stage _ []) (tensorState (basis x) (basis (fun _ => false))) (Fin.append l r)=_
  rw [stage_branch (literals w a) [] (basis x) l r,literals_read]
  change basis x l*basis (Fin.append (toBits w) (zeroBits (a+1))) r=_
  change _=tensorState _ _ (Fin.append l r)
  have el : leftRegister (Fin.append l r)=l := funext (Fin.append_left _ _)
  have er : rightRegister (Fin.append l r)=r := funext (Fin.append_right _ _)
  simp only [tensorState,el,er]

def lengthAt (v : ℕ→Str) (n : ℕ) := n+(v n).length

def reserve (F : MFamily) (v : ℕ→Str) (n : ℕ) := (v n).length+F.anc (lengthAt v n)

theorem shape (F : MFamily) (v : ℕ→Str) (n : ℕ) :
    lengthAt v n+(F.anc (lengthAt v n)+1)=n+(reserve F v n+1) := by simp only [reserve,lengthAt];omega

theorem localShape (F : MFamily) (v : ℕ→Str) (n : ℕ) :
    n+((v n).length+(F.anc (lengthAt v n)+1))=n+(reserve F v n+1) := by unfold reserve;omega

def changeWidth {a b : ℕ} (h : a=b) (U : Layered a) : Layered b := h ▸ U

def family (F : MFamily) (v : ℕ→Str) : MFamily where
  anc := reserve F v
  circ n := changeWidth (localShape F v n) (prepare n (v n) (F.anc (lengthAt v n))) ++
    changeWidth (shape F v n) (F.circ (lengthAt v n))
  outLen n := F.outLen (lengthAt v n)
  outW n i := Fin.cast (shape F v n) (F.outW (lengthAt v n) i)

theorem prep_ok {n a : ℕ} (w : Str) : ∀ l∈prepare n w a,LayerOk l := by
  intro l hl
  simp only [prepare,stage,relocateCircuit,List.map_nil,List.append_nil,List.mem_map] at hl
  obtain ⟨g,_,rfl⟩ := hl;simp [LayerOk]

theorem cast_ok {a b : ℕ} (h : a=b) (U : Layered a) (hu : ∀ l∈U,LayerOk l) : ∀ l∈changeWidth h U,LayerOk l := by subst b;exact hu

theorem ok (F : MFamily) (v : ℕ→Str) (ho : ∀ n,∀ l∈F.circ n,LayerOk l) (n : ℕ) :
    ∀ l∈(family F v).circ n,LayerOk l := by
  intro l hl
  rcases List.mem_append.mp hl with h|h
  · exact cast_ok _ _ (prep_ok _) _ h
  · exact cast_ok _ _ (ho _) _ h

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule70

/- Helper module AdviceLaw. -/
section P2MDyadicModule71

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open TM2Boolean TM2Boolean.PolyProgramCircuit

open scoped Classical BigOperators

noncomputable section

def extended (n : ℕ) (w : Str) : Bits n := fun i => wordExtension w i.val

theorem input_bits (s : Str) (a : ℕ) : extended (s.length+a) s=Fin.append (toBits s) (zeroBits a) := by
  funext i;refine Fin.addCases ?_ ?_ i
  · intro j;rw [Fin.append_left];exact wordExtension_before _ _ j.isLt
  · intro j;rw [Fin.append_right];exact wordExtension_after _ _ (by simp)

theorem appended_bits (s v : Str) (a : ℕ) :
    extended (s.length+(v.length+a)) (s++v)=Fin.append (toBits s) (Fin.append (toBits v) (zeroBits a)) := by
  funext i;refine Fin.addCases ?_ ?_ i
  · intro j;rw [Fin.append_left]
    change wordExtension (s++v) j.val=_
    rw [wordExtension_before _ _ (by simp;omega),List.getElem_append_left j.isLt];rfl
  · intro j;rw [Fin.append_right];refine Fin.addCases ?_ ?_ j
    · intro l;rw [Fin.append_left]
      change wordExtension (s++v) (s.length+l.val)=_
      rw [wordExtension_before _ _ (by simp),List.getElem_append_right (by omega)]
      simp [toBits]
    · intro l;rw [Fin.append_right]
      exact wordExtension_after _ _ (by simp <;> omega)

theorem prepare_actual (s v : Str) (a : ℕ) :
    runLayered (prepare s.length v a) (basis (extended _ s))=basis (extended _ (s++v)) := by
  rw [input_bits,appended_bits];exact prepare_basis _ _ _

theorem cast_run {u v : ℕ} (h : u=v) (U : Layered u) (s t : Str)
    (he : runLayered U (basis (extended u s))=basis (extended u t)) :
    runLayered (changeWidth h U) (basis (extended v s))=basis (extended v t) := by subst v;exact he

def probAt (F : MFamily) (n : ℕ) (s : Str) (E : Str→Prop) :=
  ∑ z, if E (List.ofFn fun i => z (F.outW n i)) then ‖runLayered (F.circ n) (basis (extended _ s)) z‖^2 else 0

theorem probAt_eq (F : MFamily) (s : Str) (E : Str→Prop) :
    probAt F s.length s E=outputProb F s E := by
  unfold probAt outputProb;rw [basisInput_eq_computationalBasis,wordExtension_basis];rfl

private theorem measured_cast {a b k : ℕ} (h : a=b) (V : Layered a) (s : Str) (read : Fin k→Fin a) (E : Str→Prop) :
    (∑ y : Bits b, if E (List.ofFn fun i => y (Fin.cast h (read i))) then
      ‖runLayered (changeWidth h V) (basis (extended b s)) y‖^2 else 0)=
    ∑ y : Bits a, if E (List.ofFn fun i => y (read i)) then ‖runLayered V (basis (extended a s)) y‖^2 else 0 := by
  subst b;rfl

theorem probability (F : MFamily) (v : ℕ→Str) (s : Str) (E : Str→Prop) :
    outputProb (family F v) s E=outputProb F (s++v s.length) E := by
  rw [←probAt_eq,←probAt_eq,List.length_append]
  unfold probAt
  change (∑ z, if E (List.ofFn fun i => z (Fin.cast (shape F v s.length) (F.outW _ i))) then
    ‖runLayered (changeWidth (localShape F v s.length) (prepare s.length (v s.length) (F.anc (lengthAt v s.length))) ++ changeWidth (shape F v s.length) (F.circ (lengthAt v s.length))) (basis (extended _ s)) z‖^2 else 0)=_
  have bound := cast_run (localShape F v s.length) _ _ _ (prepare_actual s (v s.length) (F.anc (lengthAt v s.length)))
  have run (z : Bits (s.length+(reserve F v s.length+1))) :
      runLayered (changeWidth (localShape F v s.length) (prepare s.length (v s.length) (F.anc (lengthAt v s.length))) ++ changeWidth (shape F v s.length) (F.circ (lengthAt v s.length)))
        (basis (extended _ s)) z=runLayered (changeWidth (shape F v s.length) (F.circ (lengthAt v s.length))) (basis (extended _ (s++v s.length))) z := by
    rw [show ∀ {n : ℕ} (U V : Layered n) (ψ : QState n),runLayered (U++V) ψ=runLayered V (runLayered U ψ) from fun _ _ _ => List.foldl_append]
    rw [bound]
  simp only [run]
  exact measured_cast _ _ _ _ _

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule71

/- Helper module AdviceWords. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open NativeWordDescription TM2Boolean TM2Boolean.CodeGenerator

open Integration9_9.TM2PlatformSerialization Integration9_9.LoadedBatch.PostComposition

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Classical BigOperators

noncomputable section

def lit (b : Bool) : Pin := if b then (1,0) else (0,0)

def pinsCode (w : Str) (a : List Unit) := w.map lit ++ (a++[()]).map (fun _ => ((0,0):Pin))

@[fun_prop] theorem pinsCode_poly : Poly (fun v : Str×List Unit => pinsCode v.1 v.2) := by unfold pinsCode lit;fun_prop

theorem packed (n : ℕ) (w : Str) (a : ℕ) :
    pack (literals (n:=n) w a) []=(pinsCode w (List.replicate a ()),[]) := by
  have he : (fun i => pin (literals (n:=n) w a i))=Fin.append (fun i => lit (toBits w i)) (fun _ : Fin (a+1) => ((0,0):Pin)) := by
    funext i; refine Fin.addCases ?_ ?_ i
    · intro i; simp only [literals,Fin.append_left];cases toBits w i <;> rfl
    · intro i;simp only [literals,Fin.append_right];rfl
  have hl : List.ofFn (toBits w)=w := by apply List.ext_getElem <;> simp [toBits]
  have hm := List.map_ofFn (f:=toBits w) (g:=lit)
  rw [hl] at hm
  change w.map lit=List.ofFn (fun i => lit (toBits w i)) at hm
  simp only [pack,he,List.ofFn_fin_append,List.ofFn_const,←hm,pinsCode,List.map_append,List.map_cons,List.map_nil,List.map_replicate]
  rw [List.replicate_succ']
  rfl

def bodyUnary (x : Str×Str) : Str := x.1++x.2.map (fun _ => true)

@[fun_prop] theorem bodyUnary_poly : Poly bodyUnary := by unfold bodyUnary;fun_prop

def children (g : Str→Str) (x : Str×Str) := readFrame (bodyUnary x,g (bodyUnary x))

@[fun_prop] theorem children_poly (g : Str→Str) (hg : Poly g) : Poly (children g) := by unfold children;fun_prop

def oldAnc (g : Str→Str) (x : Str×Str) := unarySlots (g (bodyUnary x))

@[fun_prop] theorem oldAnc_poly (g : Str→Str) (hg : Poly g) : Poly (oldAnc g) := by unfold oldAnc;fun_prop

def prefixLayers (g : Str→Str) (x : Str×Str) : List (List Str) :=
  (blockCode x.1.length (pinsCode x.2 (oldAnc g x),[])).map fun gate =>
    [gateWord ((children g x).1.map (fun _ => ())) gate]

@[fun_prop] theorem prefixLayers_poly (g : Str→Str) (hg : Poly g) : Poly (prefixLayers g) := by
  have hc := Poly.comp (f:=fun v : ℕ×Block => blockCode v.1 v.2)
    (g:=fun x : Str×Str => (x.1.length,(pinsCode x.2 (oldAnc g x),[]))) blockCode_poly (by fun_prop)
  unfold prefixLayers
  apply Poly.list_map _ hc
  have h : Poly (fun u : (Str×Str)×GateCode => ((children g u.1).1.map (fun _ => ()),u.2)) := by fun_prop
  have he := Poly.comp gateWord_poly h
  fun_prop

def descriptor (g : Str→Str) (x : Str×Str) : Str :=
  lengthToken ((x.2.map (fun _ => ()))++oldAnc g x)++serializeWords (children g x).2.1++
    serializeWords (((prefixLayers g x)++(children g x).2.2).map serializeWords)

@[fun_prop] theorem descriptor_poly (g : Str→Str) (hg : Poly g) : Poly (descriptor g) := by
  unfold descriptor;fun_prop

theorem unary_ex (n : ℕ) (w : Str) : bodyUnary (unary n,w)=unary (n+w.length) := by simp only [bodyUnary,unary,List.map_const',List.replicate_add]

theorem anc_eq (F : MFamily) (g : Str→Str) (hg : ∀ n,g (unary n)=F.encAt n) (n : ℕ) (v : Str) :
    oldAnc g (unary n,v)=List.replicate (F.anc (n+v.length)) () := by
  simp only [oldAnc,unary_ex,hg,multi_encoding,List.append_assoc,unarySlots_append]

theorem header_eq (F : MFamily) (g : Str→Str) (hg : ∀ n,g (unary n)=F.encAt n) (n : ℕ) (v : Str) :
    prefixLayers g (unary n,v)=(prepare n v (F.anc (n+v.length))).map (List.map encInstr) := by
  let m := n+v.length
  have hshape : n+(v.length+(F.anc m+1))≤Integration9_9.LoadedBatch.PostComposition.oldWidth F m := by
    unfold Integration9_9.LoadedBatch.PostComposition.oldWidth m;omega
  simp only [prefixLayers,children,unary_ex,hg,readFrame_correct,anc_eq F g hg,show (unary n).length=n by simp [unary]]
  rw [←packed n v (F.anc (n+v.length)),block_eq]
  let U := prepare n v (F.anc m)
  have hs : n+(v.length+(F.anc m+1))≤((unary (Integration9_9.LoadedBatch.PostComposition.oldWidth F m)).map (fun _ => ())).length := by simpa [unary] using hshape
  change (U.flatten.map encodeInstr).map _=U.map (List.map encInstr)
  have encode (g : Instr (n+(v.length+(F.anc (n+v.length)+1)))) :
      gateWord ((unary (Integration9_9.LoadedBatch.PostComposition.oldWidth F (n+v.length))).map (fun _ => ())) (encodeInstr g)=encInstr g := gateWord_encode _ _ hs
  simp only [List.map_map,Function.comp_def,encode]
  unfold U prepare stage
  simp only [relocateCircuit,List.map_nil,List.append_nil]
  induction load (literals (n:=n) v (F.anc m)) with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons,List.flatten_cons,List.singleton_append,List.map_nil] using congrArg (List.cons [encInstr x]) ih

theorem descriptor_eq (F : MFamily) (v : ℕ→Str) (g : Str→Str) (hg : ∀ n,g (unary n)=F.encAt n) (n : ℕ) :
    descriptor g (unary n,v n)=(family F v).encAt n := by
  rw [multi_encoding]
  simp only [descriptor,children,unary_ex,hg,readFrame_correct,anc_eq F g hg,header_eq F g hg,
    lengthToken_eq,List.length_append,List.length_map,List.length_replicate,serializeWords_eq]
  have cast_enc {a b : ℕ} (h : a=b) (U : Layered a) : (changeWidth h U).map encLayer=U.map encLayer := by subst b;rfl
  simp only [family,reserve,lengthAt,encCirc,List.map_append,cast_enc,List.map_map,Function.comp_def,encLayer,Fin.val_cast]
  congr 2
  · simp only [List.map_ofFn,Function.comp_def,Fin.val_cast]
  · simp only [serializeWords_eq];rfl

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule72

/- Helper module PlacedCPU. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Classical BigOperators

noncomputable section

variable {k N : ℕ}

def blank (w : Fin k ↪ Fin N) : OutsideBits w := fun _ => false

def restore (w : Fin k ↪ Fin N) (x : Bits k) : Bits N := (wireBitsEquiv w).symm (x,blank w)

theorem restore_zero (w : Fin k ↪ Fin N) : restore w (zeroBits k)=zeroBits N := by
  apply (wireBitsEquiv w).symm_apply_eq.mpr;rfl

theorem full_event (w : Fin k ↪ Fin N) (c : Layered k) (f : Bits N→ℝ) :
    (∑ z, ‖runLayered (relocateCircuit w c) (basis (zeroBits N)) z‖^2*f z) =
    ∑ z, ‖runLayered c (basis (zeroBits k)) z‖^2 * f (restore w z) := by
  rw [←restore_zero w,restore,←initializedWires_basis,relocateCircuit_initialized]
  calc _ = ∑ p : Bits k × OutsideBits w,
        ‖runLayered c (basis (zeroBits k)) p.1*basis (blank w) p.2‖^2*f ((wireBitsEquiv w).symm p) := by
          apply Fintype.sum_equiv (wireBitsEquiv w)
          intro z
          rw [Equiv.symm_apply_apply];rfl
       _ = _ := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_eq_single (blank w)]
          · simp [basis,restore]
          · intro r _ hr;simp [basis,hr]
          · simp

def offset (pre tail index : ℕ) := if index<pre then tail+index else index-pre

def move (pre tail : ℕ) (g : GateCode) : GateCode := (g.1,offset pre tail g.2.1,if g.1=4 then offset pre tail g.2.2 else 0)

@[fun_prop] theorem move_poly : Poly (fun v : (ℕ×ℕ)×GateCode => move v.1.1 v.1.2 v.2) := by unfold move offset;fun_prop

def place (pre tail : ℕ) (fit : tail+pre ≤ N) : Fin (pre+tail) ↪ Fin N :=
  ((finAddFlip : Fin (pre+tail) ≃ Fin (tail+pre)).toEmbedding).trans (Fin.castLEEmb fit)

theorem place_val (pre tail : ℕ) (fit : tail+pre≤N) (i : Fin (pre+tail)) :
    (place pre tail fit i).val=offset pre tail i.val := by
  refine Fin.addCases ?_ ?_ i
  · intro j;simp [place,offset,finAddFlip_apply_castAdd]
  · intro j;simp [place,offset,finAddFlip_apply_natAdd]

theorem move_exact (pre tail : ℕ) (fit : tail+pre≤N) (g : Instr (pre+tail)) :
    move pre tail (encodeInstr g)=encodeInstr (relocateInstr (place pre tail fit) g) := by
  cases g <;> simp only [move,encodeInstr,relocateInstr,place_val] <;> rfl

theorem code_eq (pre tail : ℕ) (fit : tail+pre≤N) (c : Layered (pre+tail)) :
    (c.flatten.map encodeInstr).map (move pre tail)=(relocateCircuit (place pre tail fit) c).flatten.map encodeInstr := by
  simp only [List.map_map,List.map_flatten,relocateCircuit,Function.comp_def,move_exact pre tail fit]

theorem restored_bit (pre tail : ℕ) (fit : tail+pre≤N) (z : Bits (pre+tail)) (i : Fin tail) :
    restore (place pre tail fit) z ⟨i.val,by omega⟩ = z (Fin.natAdd pre i) := by
  have he := (wireBitsEquiv (place pre tail fit)).apply_symm_apply (z,blank _)
  have hh := congrFun (congrArg Prod.fst he) (Fin.natAdd pre i)
  change restore (place pre tail fit) z (place pre tail fit (Fin.natAdd pre i))=_ at hh
  convert hh using 2
  apply Fin.ext
  simp [place_val,offset]

theorem native (gen : Str→List GateCode) (hg : Poly gen) (p q : Polynomial ℕ) (s : Str)
    (pre tail : ℕ) (fit : tail+pre≤p.eval s.length) (c : Layered (pre+tail))
    (hc : gen s=(c.flatten.map encodeInstr).map (move pre tail)) (hlen : c.flatten.length≤q.eval s.length)
    (E : Str→Prop) :
    outputProb (ProgrammableStage.family (ProgrammableStage.cpu gen hg p q) p q) s E =
      ∑ z, if E (List.ofFn (restore (place pre tail fit) z)) then ‖runLayered c (basis (zeroBits _)) z‖^2 else 0 := by
  let w := place pre tail fit
  let gs := (relocateCircuit w c).flatten
  have he : gen s=gs.map encodeInstr := hc.trans (code_eq _ _ fit c)
  have hl : gs.length≤q.eval s.length := by
    simpa only [gs,relocateCircuit,List.length_flatten,List.map_map,Function.comp_def,List.length_map] using hlen
  rw [ProgrammableStage.native_born gen hg p q s gs he hl]
  change (∑ x, if E (List.ofFn x) then ‖runLayer (relocateCircuit w c).flatten (basis (zeroBits _)) x‖^2 else 0)=_
  rw [←runLayered_flatten]
  simpa only [mul_ite,mul_one,mul_zero] using full_event w c (fun z => if E (List.ofFn z) then 1 else 0)

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

end P2MDyadicModule73

/- Helper module RunRecipe. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1100000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

open QAlgorithms QAlgorithms.Complexity ControlledNativeCode CoherentComputeUncompute

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped Classical BigOperators

noncomputable section

abbrev Recipe := (List Unit×List Unit)×List GateCode

def code (r : Recipe) := r.2.map (move r.1.1.length r.1.2.length)

@[fun_prop] theorem code_poly : Poly code := by
  unfold code
  exact Poly.list_map (as:=Prod.snd) (Poly.comp (f:=fun v : (ℕ×ℕ)×GateCode => move v.1.1 v.1.2 v.2) (g:=fun u : Recipe×GateCode => ((u.1.1.1.length,u.1.1.2.length),u.2)) move_poly (by fun_prop)) Poly.snd

def wires (r : Recipe) := r.1.1++r.1.2

@[fun_prop] theorem wires_poly : Poly wires := by unfold wires;fun_prop

def bound {α : Type} [Coding α] {f : Str→List α} (hf : Poly f) :=
  hf.program.sizeBound.comp (3*Polynomial.X)

theorem bound_length {α : Type} [Coding α] {f : Str→List α} (hf : Poly f) (s : Str) :
    (f s).length≤(bound hf).eval s.length := by
  have hl := hf.program.length_bound s
  change (encodeList enc (f s)).length ≤ hf.program.sizeBound.eval (encodeList encodeBool s).length at hl
  apply (EncodedList.length_le _ _).trans
  simpa only [bound,BooleanLists.length,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using hl

variable (plan : Str→Recipe) (hp : Poly plan)

def raw (s : Str) := code (plan s)

include hp in
@[fun_prop] theorem raw_poly : Poly (raw plan) := Poly.comp (f:=code) (g:=plan) code_poly hp

def sizeP := bound (Poly.comp (f:=wires) (g:=plan) wires_poly hp)

def sizeQ := bound (raw_poly plan hp)

def cpu := ProgrammableStage.cpu (raw plan) (raw_poly plan hp) (sizeP plan hp) (sizeQ plan hp)

def interpreter := ProgrammableStage.family (cpu plan hp) (sizeP plan hp) (sizeQ plan hp)

theorem fits (s : Str) : (plan s).1.2.length+(plan s).1.1.length≤(sizeP plan hp).eval s.length := by
  have hl := bound_length (Poly.comp (f:=wires) (g:=plan) wires_poly hp) s
  calc _ = (wires (plan s)).length := by simp [wires,Nat.add_comm]
       _ ≤ _ := hl

theorem execute (s : Str) (c : Layered ((plan s).1.1.length+(plan s).1.2.length))
    (h : (plan s).2=c.flatten.map encodeInstr) (E : Str→Prop) :
    outputProb (interpreter plan hp) s E =
      ∑ z, if E (List.ofFn (restore (place _ _ (fits plan hp s)) z)) then ‖runLayered c (basis (zeroBits _)) z‖^2 else 0 := by
  apply native
  · simp only [raw,code,h]
  · have hq := bound_length (raw_poly plan hp) s
    calc _ = (raw plan s).length := by simp only [raw,code,h,List.length_map]
         _ ≤ _ := hq

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.PlacedCPU

end P2MDyadicModule74

/- Helper module UniformCompilation. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LoadedBatch.PostComposition

open scoped Classical BigOperators

noncomputable section

/-- The length-dependent table comes from a stock polynomial-time machine,
whose work alphabet need not be the one of the native gate compiler. -/
theorem generated (F : MFamily) (g : Str→Str) (hg : Poly g) (cg : ∀ n,g (unary n)=F.encAt n)
    (ho : ∀ n, ∀ l∈F.circ n,LayerOk l) (table : Str→Str) (ht : PolyTimeComputable table) :
    IsMQPT (family F (fun n => table (unary n))) := by
  apply ProgrammableStage.of_description _ (fun w => descriptor g (w,table w))
  · exact generator_builder_polyTime _ ht _ (descriptor_poly _ hg)
  · exact descriptor_eq F _ g cg
  · exact ok F _ ho

variable (plan : Str→PlacedCPU.Recipe) (hp : Poly plan)

def emitted := ProgrammableStage.desc (PlacedCPU.cpu plan hp) (PlacedCPU.sizeP plan hp) (PlacedCPU.sizeQ plan hp)

theorem emitted_poly : Poly (emitted plan hp) := ProgrammableStage.desc_poly _ _ _

theorem emitted_eq (n : ℕ) : emitted plan hp (unary n)=(PlacedCPU.interpreter plan hp).encAt n :=
  ProgrammableStage.code_exact _ _ _ _ (ProgrammableStage.fits _ _ _ _ _)

def universal (table : Str→Str) := family (PlacedCPU.interpreter plan hp) (fun n => table (unary n))

theorem universal_qpt (table : Str→Str) (ht : PolyTimeComputable table) :
    IsMQPT (universal plan hp table) := generated _ _ (emitted_poly plan hp) (emitted_eq plan hp)
      (ProgrammableStage.machine_ok _ _ _) _ ht

theorem universal_event (table : Str→Str) (s : Str) (E : Str→Prop) :
    outputProb (universal plan hp table) s E =
      outputProb (PlacedCPU.interpreter plan hp) (s++table (unary s.length)) E :=
  probability _ _ _ _

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.UniformInput

end P2MDyadicModule75

/- Helper module WaveRead. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1300000

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeCode CoherentComputeUncompute GaussianIteration SamplerParameters

noncomputable section

theorem prefix_restore {h k N : ℕ} (hi : k+h≤N) (y : Bits (h+k)) :
    List.ofFn (rightRegister y : Bits k) <+: List.ofFn (PlacedCPU.restore (PlacedCPU.place h k hi) y) := by
  let out:=List.ofFn (PlacedCPU.restore (PlacedCPU.place h k hi) y)
  have h : out.take k=List.ofFn (rightRegister y : Bits k) := by
    apply List.ext_getElem
    · simp [out,Nat.min_eq_left (by omega : k≤N)]
    · intro i hl hr
      have hk : i<k := by simpa using hr
      simp only [out,List.getElem_take,List.getElem_ofFn]
      exact PlacedCPU.restored_bit h k hi y ⟨i,hk⟩
  exact h ▸ List.take_prefix k out

end

end InfoLossLAR.WorstCase.RegevSearch.AdaptiveStages.Outer

end P2MDyadicModule76

/- Helper module PlacedGateCompiler. -/
section P2MDyadicModule77

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

open InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase

open QAlgorithms QAlgorithms.Complexity AdaptiveStages OAI.MetricKMedian.Binary.Automatic

theorem solution
    (plan : Str→(List Unit × List Unit) × List (ℕ × ℕ × ℕ)) (hp : Poly plan) (table : Str→Str) :
    ∃ H : MFamily, (PolyTimeComputable table → IsMQPT H) ∧ ∀ w : Str,
      let s := w ++ table (unary w.length)
      let h := (plan s).1.1.length
      let k := (plan s).1.2.length
      ∃ message : Bits (h+k) → Str,
        (∀ z, List.ofFn (fun i : Fin k => z (Fin.natAdd h i)) <+: message z) ∧
        ∀ (c : Layered (h+k)), (plan s).2 = c.flatten.map (fun g => match g with
          | .h i => (0,i.val,0)
          | .s i => (1,i.val,0)
          | .t i => (2,i.val,0)
          | .x i => (3,i.val,0)
          | .cnot i j _ => (4,i.val,j.val)) →
          ∀ E : Str→Prop, outputProb H w E =
            ∑ z, if E (message z) then ‖runLayered c (fun x => if x = (fun _ => false) then 1 else 0) z‖^2 else 0 := by
  refine ⟨UniformInput.universal plan hp table,UniformInput.universal_qpt plan hp table,?_⟩
  intro w s h k
  let fit := PlacedCPU.fits plan hp s
  let msg (z : Bits (h+k)) := List.ofFn (PlacedCPU.restore (PlacedCPU.place h k fit) z)
  refine ⟨msg,fun z => Outer.prefix_restore fit z,?_⟩
  intro c hc E
  have eq : (plan s).2 = c.flatten.map ControlledNativeCode.encodeInstr := by
    convert hc using 1
    congr 1
    funext g
    cases g <;> rfl
  exact (UniformInput.universal_event plan hp table w E).trans (PlacedCPU.execute plan hp s c eq E)

end P2MDyadicModule77
