-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.sivp_dimension_dispatch
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T14:27:19.355256+00:00
-- url     : https://prove2.me/submissions/5130d830-ec7a-4daf-958c-ac96b10d82af

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

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule0

namespace AFT.RationalNumerics

open scoped BigOperators

namespace HeightBound

theorem mono {value : ℚ} {first second : ℕ} (h : HeightBound value first) (hle : first ≤ second) :
    HeightBound value second := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  exact ⟨h.1.trans hp,h.2.trans hp⟩

private theorem reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))

theorem zero : HeightBound 0 0 := by norm_num [HeightBound]

theorem of_int {value : ℤ} {bits : ℕ} (h : value.natAbs ≤ 2^bits) : HeightBound (value : ℚ) bits := by
  constructor
  · simpa using h
  · simpa using (Nat.one_le_pow bits 2 (by decide))

theorem mul {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first*second) (firstBits+secondBits) := by
  have heq : first*second=Rat.divInt (first.num*second.num) (first.den*second.den : ℤ) := by
    calc
      _ = Rat.divInt first.num first.den * Rat.divInt second.num second.den := by rw [Rat.num_divInt_den,Rat.num_divInt_den]
      _ = _ := Rat.divInt_mul_divInt _ _
  have hr := reduced_le (first.num*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul,← heq] at hr
  simp only [Int.natAbs_mul] at hr
  rw [HeightBound,pow_add]
  exact ⟨hr.1.trans (Nat.mul_le_mul hf.1 hs.1),hr.2.trans (Nat.mul_le_mul hf.2 hs.2)⟩

theorem inv {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by
  by_cases hz : value=0
  · subst value
    norm_num [HeightBound]
    exact Nat.one_le_pow bits 2 (by decide)
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hsign : value.num.sign.natAbs=1 := by
      rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hz) with hn|hn
      · simp [Int.sign_eq_neg_one_of_neg hn]
      · simp [Int.sign_eq_one_of_pos hn]
    simpa only [hsign,one_mul,mul_one] using h.2
  · simpa only [Rat.den_inv_of_ne_zero hz] using h.1

theorem div {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first/second) (firstBits+secondBits) := by
  simpa only [div_eq_mul_inv] using hf.mul hs.inv

end HeightBound

end AFT.RationalNumerics

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

/- Helper module BatchStock. -/
section P2MDyadicModule57

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

end P2MDyadicModule57

/- Helper module BatchEmitter. -/
section P2MDyadicModule58

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

end P2MDyadicModule58

/- Helper module BundleMarginal. -/
section P2MDyadicModule59

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

end P2MDyadicModule59

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

/- Helper module StaticBatchCore. -/
section P2MDyadicModule62

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

end P2MDyadicModule62

/- Helper module GridEmitter. -/
section P2MDyadicModule63

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

end P2MDyadicModule63

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

/- Helper module FramedReadout. -/
section P2MDyadicModule90

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

end P2MDyadicModule90

/- Helper module StaticBatchReadout. -/
section P2MDyadicModule92

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

end P2MDyadicModule92

/- Helper module StaticBatchSemantics. -/
section P2MDyadicModule94

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

end P2MDyadicModule94

namespace InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule
open InfoLossLAR.WorstCase
def slotSource {length : ℕ} : StaticLoadSlot length → Bool × ℕ
  | .inl b => (false, if b then 1 else 0)
  | .inr i => (true, i.val)

end InfoLossLAR.WorstCase.RegevSketch.DyadicSchedule
/- Helper module DyadicUniform. -/
section P2MDyadicModule96

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
end P2MDyadicModule96
/- Helper module StaticBatchBornReadout. -/
section P2MDyadicModule97

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

theorem grid_selected_event (G : MFamily) {n : ℕ} (input : Bits n) (tasks : Tasks n)
    (i : Fin tasks.length) (event : Bits (blockWidth G (tasks.get i)) → Prop) :
    (∑ state : Bits (gridWidth G tasks), if event (gridBlockRead G tasks i state) then
      ‖runLayered (gridCircuit G tasks) (computationalBasis (gridBits G input tasks)) state‖^2
      else 0) =
    (∑ state : Bits (blockWidth G (tasks.get i)), if event state then
      ‖runLayered (G.circ (tasks.get i).length) (basisInput (queryBits input (tasks.get i))) state‖^2
      else 0) := by
  induction tasks with
  | nil => exact Fin.elim0 i
  | cons task rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i event
    · intro E
      change (∑ state : Bits (blockWidth G task + gridWidth G rest), if E (leftRegister state) then
        ‖runLayered (leftCircuit (show Layered (blockWidth G task) from G.circ task.length) ++ rightCircuit (gridCircuit G rest))
          (computationalBasis (Fin.append (Fin.append (queryBits input task) (fun _ => false))
            (gridBits G input rest))) state‖^2 else 0) =
        ∑ state : Bits (blockWidth G task), if E state then
          ‖runLayered (G.circ task.length) (basisInput (queryBits input task)) state‖^2 else 0
      rw [computationalBasis_tensor, disjointCircuits_tensor, ← basisInput_eq_computationalBasis]
      apply tensorState_left_event
      have h := runLayered_mass (gridCircuit G rest) (computationalBasis (gridBits G input rest))
      simpa only [Complex.normSq_eq_norm_sq, computationalBasis_unit] using h
    · intro E
      change (∑ state : Bits (blockWidth G task + gridWidth G rest),
        if E (gridBlockRead G rest j (rightRegister state)) then
          ‖runLayered (leftCircuit (show Layered (blockWidth G task) from G.circ task.length) ++ rightCircuit (gridCircuit G rest))
            (computationalBasis (Fin.append (Fin.append (queryBits input task) (fun _ => false))
              (gridBits G input rest))) state‖^2 else 0) = _
      rw [computationalBasis_tensor, disjointCircuits_tensor,
        tensorState_right_event _ _ (fun state => E (gridBlockRead G rest j state))]
      · exact ih j E
      · have h := runLayered_mass (G.circ task.length)
          (computationalBasis (Fin.append (queryBits input task) (fun _ => false)))
        simpa only [Complex.normSq_eq_norm_sq, computationalBasis_unit, blockWidth] using h

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

theorem core_selected_event (G : MFamily) (word : Str) (tasks : Tasks word.length)
    (i : Fin tasks.length) (event : Bits (blockWidth G (tasks.get i)) → Prop) :
    (∑ state : Bits (word.length + (batchAnc G tasks + 1)),
      if event (fun j => state (blockWire G tasks i j)) then
        ‖runLayered (coreCircuit G tasks) (basisInput (a := batchAnc G tasks) (toBits word)) state‖^2
        else 0) =
    (∑ state : Bits (blockWidth G (tasks.get i)), if event state then
      ‖runLayered (G.circ (tasks.get i).length)
        (basisInput (queryBits (toBits word) (tasks.get i))) state‖^2 else 0) := by
  simp_rw [← coreGridRead_blockWire G tasks _ i]
  rw [core_grid_event _ _ _ (fun state => event (gridBlockRead G tasks i state))]
  exact grid_selected_event G (toBits word) tasks i event

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

/-- The complete string, including any repeated output wire, read from
one designated block of the circuit. -/
def trialWord (G : MFamily) {n : ℕ} (tasks : Tasks n) (i : Fin tasks.length)
    (state : Bits (n + (batchAnc G tasks + 1))) : Str :=
  List.ofFn fun j => state (blockWire G tasks i (G.outW (tasks.get i).length j))

private theorem outputProb_at_length (G : MFamily) (word : Str) {n : ℕ}
    (hn : word.length = n) (input : Bits n)
    (hi : (fun i : Fin n => toBits word (Fin.cast hn.symm i)) = input)
    (event : Str → Prop) :
    outputProb G word event =
      ∑ state : Bits (n + (G.anc n + 1)),
        if event (List.ofFn (fun j => state (G.outW n j))) then
          ‖runLayered (G.circ n) (basisInput input) state‖^2 else 0 := by
  cases hn
  subst input
  rfl

theorem core_selected_output (G : MFamily) (word : Str) (tasks : Tasks word.length)
    (i : Fin tasks.length) (event : Str → Prop) :
    (∑ state : Bits (word.length + (batchAnc G tasks + 1)),
      if event (trialWord G tasks i state) then
        ‖runLayered (coreCircuit G tasks) (basisInput (a := batchAnc G tasks) (toBits word)) state‖^2
        else 0) =
    outputProb G (queryWord (toBits word) (tasks.get i)) event := by
  have hbits : (fun j : Fin (tasks.get i).length =>
      toBits (queryWord (toBits word) (tasks.get i))
        (Fin.cast (queryWord_length (toBits word) (tasks.get i)).symm j)) =
      queryBits (toBits word) (tasks.get i) := by
    funext j
    simp only [toBits, queryWord, List.get_eq_getElem, List.getElem_ofFn, Fin.val_cast, Fin.eta]
  rw [outputProb_at_length G _ (queryWord_length (toBits word) (tasks.get i)) _ hbits]
  exact core_selected_event G word tasks i
    (fun bits => event (List.ofFn (fun j => bits (G.outW (tasks.get i).length j))))

end

end InfoLossLAR.WorstCase.StaticBatch

end P2MDyadicModule97

/- Helper module StaticBatchResources. -/
section P2MDyadicModule98

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

end P2MDyadicModule98

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

/- Helper module StaticReadoutBounds. -/
section P2MDyadicModule100

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
end P2MDyadicModule100

section SIVPDispatchModule0


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SIVPPair
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.StaticBatch Integration9_9.DyadicReadout
open Integration9_9.LARCoinLayout
noncomputable section

def atFamily (F : ℕ → MFamily) : MFamily where
  anc n := (F n).anc n
  circ n := (F n).circ n
  outLen n := (F n).outLen n
  outW n := (F n).outW n

theorem padWidth (A : MFamily) (n : ℕ) :
    (n + (A.anc n + 1)) + 1 = n + 1 + (A.anc n + 1) := by omega

def pad (A : MFamily) : MFamily where
  anc
    | 0 => A.anc 0
    | n+1 => A.anc n
  circ
    | 0 => A.circ 0
    | n+1 => castBodyCircuit (padWidth A n) (leftCircuit (m := 1) (A.circ n))
  outLen
    | 0 => A.outLen 0
    | n+1 => A.outLen n
  outW
    | 0 => A.outW 0
    | n+1 => fun i => Fin.cast (padWidth A n) (Fin.castAdd 1 (A.outW n i))

def proxy (E A : MFamily) (n : ℕ) : MFamily :=
  atFamily fun q => if q = n then E else pad A

def copies (n : ℕ) : List (StaticLoadSlot n) :=
  List.ofFn (fun i : Fin n => Sum.inr i)
def tasks (n : ℕ) : Tasks n := [copies n, copies n ++ [Sum.inl false]]

def pair (E A : MFamily) : MFamily :=
  atFamily fun n => batchReadoutFamily (proxy E A n) tasks

end
end SIVPPair

end SIVPDispatchModule0

section SIVPDispatchModule1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SIVPPair
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.TM2Boolean
open Integration9_9.LoadedBatch Integration9_9.LARCoinLayout
open scoped BigOperators Classical

private theorem prob_at_length (F : MFamily) (word : Str) {n : ℕ} (h : word.length = n)
    (input : Bits n) (hi : (fun i => toBits word (Fin.cast h.symm i)) = input)
    (event : Str → Prop) :
    outputProb F word event = ∑ y : Bits (n + (F.anc n + 1)),
      if event (List.ofFn fun j => y (F.outW n j)) then
        ‖runLayered (F.circ n) (basisInput input) y‖^2 else 0 := by
  cases h
  subst input
  rfl

private theorem padInput {n a : ℕ} (bits : Bits n)
    (h : (n+(a+1))+1 = n+1+(a+1)) :
    castState h (tensorState (basisInput (a := a) bits)
      (computationalBasis (fun _ : Fin 1 => false))) =
    basisInput (a := a) (Fin.append bits (fun _ : Fin 1 => false)) := by
  rw [basisInput_eq_computationalBasis, ← computationalBasis_tensor, castState_basis,
    basisInput_eq_computationalBasis]
  apply congrArg computationalBasis
  funext i
  simp only [Fin.append, Fin.addCases, Fin.castLT, Fin.val_cast]
  split_ifs <;> simp_all <;> omega

theorem pad_output (A : MFamily) (w : Str) (event : Str → Prop) :
    outputProb (pad A) (w ++ [false]) event = outputProb A w event := by
  classical
  let x := Fin.append (toBits w) (fun _ : Fin 1 => false)
  have hl : (w ++ [false]).length = w.length + 1 := by simp
  have hx : (fun i => toBits (w ++ [false]) (Fin.cast hl.symm i)) = x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      change (w ++ [false])[j.val] = Fin.append (toBits w) (fun _ => false) (Fin.castAdd 1 j)
      rw [Fin.append_left,List.getElem_append_left j.isLt]
      rfl
    · intro j
      change (w ++ [false])[w.length + j.val] = Fin.append (toBits w) (fun _ => false) (Fin.natAdd w.length j)
      rw [Fin.append_right,List.getElem_append_right (by omega)]
      simp
  rw [prob_at_length (pad A) (w ++ [false]) hl x hx event]
  change (∑ y : Bits (w.length + 1 + (A.anc w.length + 1)), if event
    (List.ofFn fun j => y (Fin.cast (padWidth A w.length) (Fin.castAdd 1 (A.outW w.length j))))
    then ‖runLayered (castBodyCircuit (padWidth A w.length) (leftCircuit (m := 1) (A.circ w.length)))
      (basisInput (a := A.anc w.length) x) y‖^2 else 0) = _
  rw [← padInput (toBits w) (padWidth A w.length), runLayered_cast, leftCircuit_tensor, castState_event]
  change (∑ s, if event (List.ofFn (fun j => leftRegister s (A.outW w.length j))) then
    ‖tensorState (runLayered (A.circ w.length) (basisInput (toBits w)))
      (computationalBasis (fun _ : Fin 1 => false)) s‖^2 else 0) = _
  apply tensorState_left_event _ _ (fun s => event (List.ofFn (fun j => s (A.outW w.length j))))
  rw [Fintype.sum_eq_single (fun _ : Fin 1 => false)]
  · simp [computationalBasis]
  · intro s hs
    simp [computationalBasis,hs]

end SIVPPair

end SIVPDispatchModule1

section SIVPDispatchModule2


set_option autoImplicit false

namespace SIVPPair
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.StaticBatch Integration9_9.DyadicReadout
open Integration9_9.LARCoinLayout
noncomputable section

private def wfAt (F : MFamily) (n : ℕ) : Prop := ∀ layer ∈ F.circ n, LayerOk layer
private def depthAt (F : MFamily) (n : ℕ) : ℕ := depth (F.circ n)

theorem pair_wellFormed (E A : MFamily) (hE : IsMQPT E) (hA : IsMQPT A) :
    ∀ n layer, layer ∈ (pair E A).circ n → LayerOk layer := by
  intro n
  apply coreCircuit_wellFormed
  intro p
  change wfAt (if p=n then E else pad A) p
  split
  · exact hE.2.1 p
  · cases p with
    | zero => exact hA.2.1 0
    | succ p => exact castBodyCircuit_wellFormed _ _ (leftCircuit_wellFormed _ (hA.2.1 p))

theorem pair_resources (E A : MFamily) (hE : IsMQPT E) (hA : IsMQPT A) :
    ∃ p : Polynomial ℕ, ∀ n : ℕ, depth ((pair E A).circ n) ≤ p.eval n ∧
      (pair E A).anc n ≤ p.eval n ∧ (pair E A).outLen n ≤ p.eval n := by
  obtain ⟨pe, he⟩ := hE.2.2
  obtain ⟨pa, ha⟩ := hA.2.2
  refine ⟨400 * (Polynomial.X + pe + pa + 1), ?_⟩
  intro n
  have grid : gridWidth (proxy E A n) (tasks n) =
      (n + (E.anc n + 1)) + ((n+1) + (A.anc n + 1)) := by
    simp [gridWidth, blockWidth, tasks, copies, proxy, atFamily, pad]
  have lengths {task} (ht : task ∈ tasks n) : task.length = n ∨ task.length = n+1 := by
    rcases List.mem_cons.mp ht with rfl | h
    · exact Or.inl (by simp [copies])
    · obtain rfl := List.mem_singleton.mp h
      exact Or.inr (by simp [copies])
  have depthEach task (ht : task ∈ tasks n) :
      depth ((proxy E A n).circ task.length) ≤ pe.eval n + pa.eval n := by
    change depthAt (proxy E A n) task.length ≤ _
    rcases lengths ht with eq | eq
    · rw [eq]
      change depthAt (if n=n then E else pad A) n ≤ _
      rw [if_pos rfl]
      exact (he n).1.trans (Nat.le_add_right _ _)
    · rw [eq]
      change depthAt (if n+1=n then E else pad A) (n+1) ≤ _
      rw [if_neg (by omega)]
      simpa [depthAt, pad, castBodyCircuit_depth] using (ha n).1.trans (Nat.le_add_left _ (pe.eval n))
  have outEach task (ht : task ∈ tasks n) :
      (proxy E A n).outLen task.length ≤ pe.eval n + pa.eval n := by
    rcases lengths ht with eq | eq
    · simp only [eq, proxy, atFamily]
      exact (he n).2.2.trans (by omega)
    · simp only [eq, proxy, atFamily, Nat.add_one_ne_self, if_false, pad]
      exact (ha n).2.2.trans (by omega)
  have hd := coreCircuit_depth_bound (proxy E A n) (tasks n)
  have hg := gridCircuit_depth_bound (proxy E A n) (tasks n) _ depthEach
  have ho := readout_length_le (proxy E A n) (tasks n) _ outEach
  have hlen : (tasks n).length = 2 := rfl
  rw [hlen] at hg ho
  have be := (he n).2.1
  have ba := (ha n).2.1
  change depth (coreCircuit (proxy E A n) (tasks n)) ≤ _ ∧
    batchAnc (proxy E A n) (tasks n) ≤ _ ∧
    (readoutRefs (typedLayout (proxy E A n) (tasks n))).length ≤ _
  simp only [batchAnc, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  exact ⟨hd.trans (by omega), by omega, ho.trans (by omega)⟩
end
end SIVPPair

end SIVPDispatchModule2

section SIVPDispatchModule3



set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace SIVPPair
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.StaticBatch Integration9_9 Integration9_9.DyadicReadout
open Integration9_9.TM2PlatformSerialization Integration9_9.LARCoinLayout
open Integration9_9.LoadedBatch.PostComposition (multi_encoding)
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def bothSources (word : Str) : List Sources :=
  let indices := (List.range word.length).map (fun i => (true, i))
  [indices, indices ++ [(false, 0)]]

@[fun_prop] theorem bothSources_poly : Poly bothSources := by
  have hr : Poly (fun word : Str => List.range word.length) := Poly.list_indices
  have hm : Poly (fun word : Str => (List.range word.length).map fun i => (true, i)) :=
    Poly.list_map (by fun_prop) hr
  unfold bothSources
  fun_prop

theorem bothSources_correct (n : ℕ) :
    bothSources (unary n) = (tasks n).map (List.map DyadicSchedule.slotSource) := by
  have h : ((List.range n).map (fun i => (true, i))) =
      List.ofFn (fun i : Fin n => (true, i.val)) := by
    apply List.ext_getElem <;> simp
  simp [bothSources, unary, tasks, copies, List.map_ofFn, DyadicSchedule.slotSource,
    Function.comp_def, h]

def frameBuilder (x : Str × List (Str × Str)) : Str :=
  let frames := samplerFrames x.2
  let anc := ancillaSlots frames
  let prepared := loadLayers (x.1, (anc, loadAll (bothSources x.1, x.2)))
  let samples := samplerLayers (x.1, frames)
  lengthToken anc ++ serializeWords (outputWireWords (encodedLayout (x.1, frames))) ++
    serializeWords ((prepared ++ samples).map serializeWords)

@[fun_prop] theorem frameBuilder_poly : Poly frameBuilder := by
  unfold frameBuilder
  fun_prop

theorem frameBuilder_correct (G : MFamily) (n : ℕ) :
    frameBuilder (unary n, samplerDescriptions G ((tasks n).map List.length)) =
      (batchReadoutFamily G tasks).encAt n := by
  let ts := tasks n
  let ds := samplerDescriptions G (ts.map List.length)
  have hanc : ancillaSlots (samplerFrames ds) = List.replicate (batchAnc G ts) () :=
    ancillaSlots_correct G ts
  have hsrc : loadAll (bothSources (unary n), ds) = (coreSlots G ts).map loadSource := by
    rw [bothSources_correct]
    exact loadAll_correct G ts
  have hgate : loadLayers (unary n, (ancillaSlots (samplerFrames ds), loadAll (bothSources (unary n), ds))) ++
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

theorem pad_enc (A : MFamily) (n : ℕ) : (pad A).encAt (n+1) = A.encAt n := by
  simp only [multi_encoding, List.map_map, Function.comp_def]
  change _ ++ _ ++ encCirc (castBodyCircuit (padWidth A n) (leftCircuit (m := 1) (A.circ n))) = _
  have hc {w : ℕ} (c : Layered w) : encCirc c = encStr ((c.map (List.map encInstr)).map encStr) := by
    simp only [encCirc, List.map_map, Function.comp_def]
    rfl
  rw [hc, castBodyCircuit_instructionWords, leftCircuit_instructionWords, ← hc]
  simp only [List.map_ofFn, Function.comp_def]
  rfl

theorem atFamily_enc (f : ℕ → MFamily) (n : ℕ) : (atFamily f).encAt n = (f n).encAt n := rfl

def buildCodes (data : (Str × Str) × Str) : Str :=
  frameBuilder (data.1.1, [(data.1.1, data.1.2), (data.1.1 ++ [true], data.2)])

@[fun_prop] theorem buildCodes_poly : Poly buildCodes := by
  unfold buildCodes
  fun_prop

theorem generate_correct (E A : MFamily) (n : ℕ) :
    buildCodes ((unary n, E.encAt n), A.encAt n) = (pair E A).encAt n := by
  let G := proxy E A n
  have he : G.encAt n = E.encAt n := by simp [G, proxy, atFamily_enc]
  have ha : G.encAt (n+1) = A.encAt n := by simp [G, proxy, atFamily_enc, pad_enc]
  have hd : samplerDescriptions G ((tasks n).map List.length) =
      [(unary n, E.encAt n), (unary n ++ [true], A.encAt n)] := by
    simp [samplerDescriptions, tasks, copies, he, ha, unary, List.replicate_succ']
  change _ = (batchReadoutFamily G tasks).encAt n
  rw [← frameBuilder_correct, hd]
  rfl

theorem pair_uniform (E A : MFamily) (hE : IsMQPT E) (hA : IsMQPT A) :
    ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n, f (unary n) = (pair E A).encAt n := by
  obtain ⟨g, ⟨pg⟩, hg⟩ := hE.1
  obtain ⟨h, ⟨ph⟩, hh⟩ := hA.1
  refine ⟨fun w => buildCodes ((w, g w), h w), ?_, fun n => by simpa only [hg, hh] using generate_correct E A n⟩
  obtain ⟨qg⟩ := stock_quoted pg
  obtain ⟨qh⟩ := stock_quoted ph
  obtain ⟨withG⟩ := stock_pairWithInput qg
  obtain ⟨projH⟩ := TM2Composition.comp (PolyProgram.fst (encodeList encodeBool) (encodeList encodeBool)).stock qh
  obtain ⟨withH⟩ := stock_pairWithInput projH
  obtain ⟨paired⟩ := TM2Composition.comp withG withH
  obtain ⟨built⟩ := TM2Composition.comp paired buildCodes_poly.program.stock
  obtain ⟨output⟩ := TM2Composition.comp built BooleanLists.unpackProgram.stock
  obtain ⟨whole⟩ := TM2Composition.comp BooleanLists.packProgram.stock output
  exact ⟨TM2StockLists.congrProgram whole _ (fun _ => rfl)⟩
end SIVPPair

end SIVPDispatchModule3

section SIVPDispatchModule4




set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SIVPDispatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9 Integration9_9.LARPlatformEncoding
open Integration9_9.TM2NativeAffineEncoding
open InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit
open scoped BigOperators Classical

def tokens (z : Str) : Str := (readB (readS z).1).1
def first (z : Str) : Str := (readS (tokens z)).2
def second (z : Str) : Str := (readS (readS (tokens z)).1).2

/-- Decode the self-delimiting input matrix and take the selected full word
from the common measured transcript. All reads are total on malformed strings. -/
def choose (cutoff : ℕ) (x : Str) : Str :=
  let m := TM2NativeAffineEncoding.readMatrix x
  if m.2.length < cutoff then first m.1 else second m.1

@[fun_prop] theorem choose_poly (cutoff : ℕ) : Poly (choose cutoff) := by
  unfold choose first second tokens
  fun_prop

theorem choose_encode (cutoff n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (z : Str) :
    choose cutoff (encMat encI B ++ z) = if n < cutoff then first z else second z := by
  simp only [choose, TM2NativeAffineEncoding.readMatrix_append, List.length_ofFn]

noncomputable def program (cutoff : ℕ) : PolyProgram id id (choose cutoff) :=
  LARCoinLayout.rawPolyProgram (choose_poly cutoff)

theorem dispatch_of_pair (A E F : MFamily) (hF : IsMQPT F)
    (hinput : ∀ (w : Str) (y : Bits (w.length + (F.anc w.length + 1))),
      runLayered (F.circ w.length) (basisInput (toBits w)) y ≠ 0 →
        ∀ i : Fin w.length, y (Fin.castAdd (F.anc w.length + 1) i) = toBits w i)
    (hmarg : ∀ (w : Str) (event : Str → Prop),
      outputProb F w (fun z => event (first z)) = outputProb E w event ∧
      outputProb F w (fun z => event (second z)) = outputProb A w event)
    (cutoff : ℕ) :
    ∃ P : MFamily, IsMQPT P ∧
      ∀ n, ∀ B : Matrix (Fin n) (Fin n) ℤ, ∀ event : Str → Prop,
        (∀ s t, event s → s <+: t → event t) →
        (if n < cutoff then outputProb E (encMat encI B) event
          else outputProb A (encMat encI B) event) ≤ outputProb P (encMat encI B) event := by
  classical
  let prog := program cutoff
  refine ⟨LoadedBatch.PostComposition.family F prog,
    LoadedBatch.PostComposition.family_isMQPT prog F hF, ?_⟩
  intro n B event hevent
  let w := encMat encI B
  let pick := if n < cutoff then first else second
  have hm : (if n < cutoff then outputProb E w event else outputProb A w event) =
      outputProb F w (fun z => event (pick z)) := by
    dsimp only [pick]
    split_ifs
    · exact (hmarg w event).1.symm
    · exact (hmarg w event).2.symm
  change (if n < cutoff then outputProb E w event else outputProb A w event) ≤ _
  rw [hm, LoadedBatch.PostComposition.family_outputProbability]
  apply Finset.sum_le_sum
  intro y _
  let z := List.ofFn (fun i => y (F.outW w.length i))
  change (if event (pick z) then _ else 0) ≤
      (if event (paddedOutput prog ((LoadedBatch.PostComposition.sources F w.length).map y))
        then ‖runLayered (F.circ w.length) (basisInput (toBits w)) y‖^2 else 0)
  by_cases hz : runLayered (F.circ w.length) (basisInput (toBits w)) y = 0
  · simp [hz]
  · have hw : List.ofFn (fun i : Fin w.length => y (Fin.castAdd (F.anc w.length+1) i)) = w := by
      rw [show (fun i : Fin w.length => y (Fin.castAdd (F.anc w.length+1) i)) =
        toBits w from funext (hinput w y hz)]
      exact List.ofFn_get w
    have hs : (LoadedBatch.PostComposition.sources F w.length).map y = w ++ z := by
      rw [LoadedBatch.postSources_map, hw]
    have hc : choose cutoff (w ++ z) = pick z := by
      rw [choose_encode]
      by_cases h : n < cutoff <;> simp only [pick,h,ite_true,ite_false]
    rw [hs, paddedOutput_eq_append, hc]
    by_cases hp : event (pick z)
    · rw [if_pos hp, if_pos (hevent (pick z) _ hp (List.prefix_append (pick z) _))]
    · rw [if_neg hp]
      split_ifs <;> positivity

end SIVPDispatch

end SIVPDispatchModule4

section SIVPDispatchModule5


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace SIVPPair
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.StaticBatch Integration9_9.DyadicReadout
open Integration9_9.LARPlatformEncoding Integration9_9.TM2PlatformSerialization
open SIVPDispatch
open scoped BigOperators Classical
noncomputable section

theorem atFamily_prob (F : ℕ → MFamily) (w : Str) (event : Str → Prop) :
    outputProb (atFamily F) w event = outputProb (F w.length) w event := rfl

theorem query_eq_map {n : ℕ} (x : Bits n) (l : List (StaticLoadSlot n)) :
    queryWord x l = l.map (slotValue x) := by
  apply List.ext_getElem
  · simp [queryWord]
  · intro i hi hj
    simp [queryWord, queryBits]

theorem query_copies (w : Str) : queryWord (toBits w) (copies w.length) = w := by
  rw [query_eq_map]
  simpa only [copies, List.map_ofFn, Function.comp_def, slotValue, Sum.elim_inr, toBits] using List.ofFn_get w

theorem query_padded (w : Str) :
    queryWord (toBits w) (copies w.length ++ [.inl false]) = w ++ [false] := by
  rw [query_eq_map, List.map_append, ← query_eq_map, query_copies]
  rfl

theorem pair_input (E A : MFamily) (w : Str) (y : Bits (w.length + ((pair E A).anc w.length + 1)))
    (h : runLayered ((pair E A).circ w.length) (basisInput (toBits w)) y ≠ 0) :
    ∀ i : Fin w.length, y (Fin.castAdd ((pair E A).anc w.length + 1) i) = toBits w i :=
  (core_preserves (proxy E A w.length) w (tasks w.length) y h).1

theorem frame_first (w e a : Str) : first (encS w ++ encL encS [e,a]) = e := by
  simp only [first, tokens, readS_append, encL, readB_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem frame_second (w e a : Str) : second (encS w ++ encL encS [e,a]) = a := by
  simp only [second, tokens, readS_append, encL, readB_append, List.flatMap_cons,
    List.flatMap_nil]

abbrev idx0 (n : ℕ) : Fin (tasks n).length := ⟨0, by change 0 < 2; decide⟩
abbrev idx1 (n : ℕ) : Fin (tasks n).length := ⟨1, by change 1 < 2; decide⟩

theorem two_trials (G : MFamily) {n : ℕ} (y : Bits (n + (batchAnc G (tasks n) + 1))) :
    trialWords G (tasks n) y = [trialWord G (tasks n) (idx0 n) y, trialWord G (tasks n) (idx1 n) y] := by
  exact List.ext_getElem (by simp [trialWords,tasks]) (by
    intro i hi hj
    have hlt : i < 2 := by simpa using hj
    interval_cases i <;> simp only [trialWords, List.getElem_ofFn] <;> rfl)

theorem selected (G : MFamily) (w : Str) (get : Str → Str) (i : Fin (tasks w.length).length)
    (hg : ∀ x e a, get (encS x ++ encL encS [e,a]) = if i.val = 0 then e else a)
    (event : Str → Prop) :
    outputProb (batchReadoutFamily G tasks) w (fun z => event (get z)) =
      outputProb G (queryWord (toBits w) ((tasks w.length).get i)) event := by
  rw [← core_selected_output G w (tasks w.length) i event]
  unfold outputProb
  apply Finset.sum_congr rfl
  intro y _
  change (if event (get (List.ofFn fun j => y (readoutWire G (tasks w.length) j))) then
      ‖runLayered (coreCircuit G (tasks w.length)) (basisInput (toBits w)) y‖^2 else 0) = _
  by_cases hz : runLayered (coreCircuit G (tasks w.length)) (basisInput (toBits w)) y = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), ite_self]
  obtain ⟨_, hc⟩ := core_preserves G w (tasks w.length) y hz
  rw [batchReadout_word _ _ _ (hc true) (hc false), two_trials, hg]
  by_cases hi : i.val = 0
  · have he : i = idx0 _ := Fin.ext hi
    subst i
    rfl
  · have he : i = idx1 _ := by
      apply Fin.ext
      have hh := i.isLt
      change i.val < 2 at hh
      change i.val = 1
      omega
    subst i
    rfl


theorem task0 (n : ℕ) : (tasks n).get (idx0 n) = copies n := rfl
theorem task1 (n : ℕ) : (tasks n).get (idx1 n) = copies n ++ [.inl false] := rfl

theorem raw_marginals (E A : MFamily) (w : Str) (event : Str → Prop) :
    outputProb (pair E A) w (fun z => event (first z)) = outputProb E w event ∧
    outputProb (pair E A) w (fun z => event (second z)) = outputProb (pad A) (w ++ [false]) event := by
  have h0 := selected (proxy E A w.length) w first (idx0 w.length)
    (fun x e a => frame_first x e a) event
  have h1 := selected (proxy E A w.length) w second (idx1 w.length)
    (fun x e a => frame_second x e a) event
  rw [task0, query_copies, proxy, atFamily_prob, if_pos rfl] at h0
  rw [task1, query_padded, proxy, atFamily_prob,
    if_neg (show (w ++ [false]).length ≠ w.length by simp)] at h1
  exact ⟨h0,h1⟩

end
end SIVPPair

end SIVPDispatchModule5

section SIVPDispatchModule6





set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open SIVPPair

theorem solution (A E : MFamily) (hA : IsMQPT A) (hE : IsMQPT E)
    (cutoff : ℕ) : ∃ P : MFamily, IsMQPT P ∧
      ∀ n, ∀ B : Matrix (Fin n) (Fin n) ℤ, ∀ event : Str → Prop,
        (∀ s t, event s → s <+: t → event t) →
        (if n < cutoff then outputProb E (encMat encI B) event
          else outputProb A (encMat encI B) event) ≤
            outputProb P (encMat encI B) event := by
  have hpair : IsMQPT (pair E A) :=
    ⟨pair_uniform E A hE hA, pair_wellFormed E A hE hA, pair_resources E A hE hA⟩
  apply SIVPDispatch.dispatch_of_pair A E (pair E A) hpair (pair_input E A) _ cutoff
  intro w event
  obtain ⟨left, right⟩ := raw_marginals E A w event
  exact ⟨left, right.trans (pad_output A w event)⟩

end SIVPDispatchModule6
