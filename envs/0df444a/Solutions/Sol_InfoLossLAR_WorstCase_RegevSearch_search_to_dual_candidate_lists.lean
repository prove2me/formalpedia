-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.search_to_dual_candidate_lists
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T04:50:30.104932+00:00
-- url     : https://prove2.me/submissions/ff3c6331-f7d0-48d9-97cf-9694f8f2ee0c

import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_mqpt_encoded_query_transcript
import Theorems.Thm_InfoLossLAR_WorstCase_ShortProbe_good_real_trial
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_ShortProbeCircuit_compiled
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_gaussian_tail
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dgs_pool_rank_failure
import Theorems.Thm_RegevLWE_GaussConv_smoothing_remark
import Theorems.Thm_RegevLWE_GaussConv_claim_3_8
import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSearch
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_InfoLossLAR_WorstCase_FixedT
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Laws
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_ShorAlgorithms_QFT_Circuit
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Lp.lpSpace
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
import Mathlib.NumberTheory.Bertrand
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

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport
end InfoLossLAR.WorstCase.GaussianLatticeTransport

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.IntegerBasis
end InfoLossLAR.WorstCase.IntegerBasis

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

namespace InfoLossLAR.WorstCase.RationalInverse
end InfoLossLAR.WorstCase.RationalInverse

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.TM2NativeAffineEncoding
end Integration9_9.TM2NativeAffineEncoding

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace QMCNumericRuntime
end QMCNumericRuntime

/- Helper module AFT.CountableNormalizedTilt. -/
section P2MDyadicModule0

namespace AFT

open scoped BigOperators

/-- Normalizing a positive approximate density costs at most
`error / (1-error)` in total variation. Both masses are genuine normalized
countable laws; no unknown normalizer is treated as one. -/
theorem normalized_tilt_total_variation {State : Type*}
    (reference actual : State → ℝ)
    (href : ∀ state, 0 ≤ reference state)
    (hreference : Summable reference) (hactual : Summable actual)
    (href_one : ∑' state, reference state = 1)
    (hactual_one : ∑' state, actual state = 1)
    (scale error : ℝ) (herror : 0 ≤ error) (herror_one : error < 1)
    (hpoint : ∀ state, |actual state - scale * reference state| ≤
      error * scale * reference state) :
    (∑' state, |actual state-reference state|) / 2 ≤ error / (1-error) := by
  have hdiff := hactual.sub (hreference.mul_left scale)
  have hnorm : |1-scale| ≤ error*scale := by
    have ht := norm_tsum_le_tsum_norm hdiff.norm
    rw [hactual.tsum_sub (hreference.mul_left scale),tsum_mul_left,hactual_one,href_one,mul_one,Real.norm_eq_abs] at ht
    have hb := hdiff.norm.tsum_le_tsum (fun state => by
      simpa only [Real.norm_eq_abs] using hpoint state) (hreference.mul_left (error*scale))
    rw [tsum_mul_left,href_one,mul_one] at hb
    exact ht.trans hb
  have hs : scale ≤ 1/(1-error) := by
    apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
    have hh' := (neg_le_abs (1-scale)).trans hnorm
    nlinarith
  have hbound (state : State) : |actual state-reference state| ≤
      (2*error*scale)*reference state := by
    calc
      _ = |(actual state-scale*reference state)+(scale-1)*reference state| := by congr 1; ring
      _ ≤ |actual state-scale*reference state|+|(scale-1)*reference state| := abs_add_le _ _
      _ ≤ error*scale*reference state+(error*scale)*reference state := by
        apply add_le_add (hpoint state)
        rw [abs_mul,abs_of_nonneg (href state),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hnorm (href state)
      _ = _ := by ring
  have hsum := (hactual.sub hreference).norm.tsum_le_tsum
    (fun state => by simpa only [Real.norm_eq_abs] using hbound state)
    (hreference.mul_left (2*error*scale))
  simp only [Real.norm_eq_abs,tsum_mul_left,href_one,mul_one] at hsum
  have hmul := mul_le_mul_of_nonneg_left hs herror
  rw [mul_one_div] at hmul
  linarith

end AFT

end P2MDyadicModule0

/- Helper module AFT.CountableChannelComposition. -/
section P2MDyadicModule1

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {First Second Output : Type*} [Fintype Output]

theorem countableChannel_summable (mass : First → ℝ) (hs : Summable mass)
    (channel : First → FiniteDist Output) (output : Output) :
    Summable (fun point => mass point*(channel point).weight output) := by
  apply Summable.of_norm_bounded hs.norm
  intro point
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel point).nonneg output)]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [← (channel point).sum_one]
  exact Finset.single_le_sum (fun value _ => (channel point).nonneg value) (Finset.mem_univ output)

end

end AFT.FiniteDist

end P2MDyadicModule1

/- Helper module AFT.FiniteProductVariation. -/
section P2MDyadicModule2

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [Fintype A] [Fintype B]

theorem l1_map_le (first second : FiniteDist A) (map : A → B) :
    (∑ b,|(first.map map).weight b-(second.map map).weight b|) ≤ ∑ a,|first.weight a-second.weight a| := by
  simp only [map_weight,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b,∑ a,|(if map a=b then first.weight a else 0)-(if map a=b then second.weight a else 0)| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (map a)]
      · simp
      · intro b _ hba
        simp [Ne.symm hba]
      · simp

theorem l1_prod_le (first first' : FiniteDist A) (second second' : FiniteDist B) :
    (∑ pair,|(first.prod second).weight pair-(first'.prod second').weight pair|) ≤
      (∑ a,|first.weight a-first'.weight a|)+(∑ b,|second.weight b-second'.weight b|) := by
  simp only [prod_weight,Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a,∑ b,(|first.weight a-first'.weight a| *second.weight b+
        first'.weight a*|second.weight b-second'.weight b|) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have he : first.weight a*second.weight b-first'.weight a*second'.weight b=
          (first.weight a-first'.weight a)*second.weight b+first'.weight a*(second.weight b-second'.weight b) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg (second.nonneg _),abs_of_nonneg (first'.nonneg _)] using abs_add_le
        ((first.weight a-first'.weight a)*second.weight b) (first'.weight a*(second.weight b-second'.weight b))
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,second.sum_one,mul_one,← Finset.sum_mul,first'.sum_one,one_mul]

omit [Fintype B] in
/-- The comparison is for the literal finite product law; all coordinate
errors are summed once. -/
theorem l1_independent_fin_le (count : ℕ) (first second : Fin count → FiniteDist A) :
    (∑ word,|(independent first).weight word-(independent second).weight word|) ≤
      ∑ i,∑ a,|(first i).weight a-(second i).weight a| := by
  induction count with
  | zero => simp only [independent,Fin.prod_univ_zero,sub_self,abs_zero,Finset.sum_const_zero,Fin.sum_univ_zero,le_refl]
  | succ count ih =>
    let tailFirst := independent (fun i : Fin count => first i.succ)
    let tailSecond := independent (fun i : Fin count => second i.succ)
    have hsplit (law : Fin (count+1) → FiniteDist A) : independent law=
        ((law 0).prod (independent (fun i : Fin count => law i.succ))).map (Fin.consEquiv (fun _ : Fin (count+1) => A)) := by
      ext word
      rw [map_equiv_weight]
      change (∏ i,(law i).weight (word i))=(law 0).weight (word 0)*∏ i : Fin count,(law i.succ).weight (word i.succ)
      exact Fin.prod_univ_succ _
    rw [hsplit first,hsplit second,Fin.sum_univ_succ]
    apply (l1_map_le _ _ _).trans
    exact (l1_prod_le (first 0) (second 0) tailFirst tailSecond).trans (add_le_add le_rfl (ih _ _))

end

end AFT.FiniteDist

end P2MDyadicModule2

/- Helper module AFT.RationalHeight. -/
section P2MDyadicModule3

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

end P2MDyadicModule3

/- Helper module Amplify. -/
section P2MDyadicModule4

set_option autoImplicit false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

noncomputable section

/-- Fubini specialized to independent discrete coefficient pools. Bounded
conditional failure may involve arbitrarily many Born outcomes per trial. -/
theorem iid_product_hasSum {X : Type} (μ g : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hg : ∀ x, 0 ≤ g x) (h : Summable (fun x => μ x * g x)) (n : ℕ) :
    HasSum (fun xs : Fin n → X => (∏ i, μ (xs i)) * ∏ i, g (xs i))
      ((∑' x, μ x * g x)^n) := by
  classical
  induction n with
  | zero =>
    have e : (fun xs : Fin 0 → X => (∏ i, μ (xs i)) * ∏ i, g (xs i)) =
        fun _ : Fin 0 → X => (1 : ℝ) := by funext x; simp
    rw [e, pow_zero]
    simpa using hasSum_fintype (fun _ : Fin 0 → X => (1:ℝ))
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => X)
    let f (xs : Fin n → X) := (∏ i, μ (xs i)) * ∏ i, g (xs i)
    have hf (xs) : 0 ≤ f xs := mul_nonneg (Finset.prod_nonneg (fun _ _ => hμ _))
      (Finset.prod_nonneg (fun _ _ => hg _))
    have ha := h.hasSum.mul ih (h.mul_of_nonneg ih.summable (fun x => mul_nonneg (hμ x) (hg x)) hf)
    have he : (fun ab : X × (Fin n → X) => μ ab.1 * g ab.1 * f ab.2) =
        (fun xs : Fin (n+1) → X => (∏ i, μ (xs i)) * ∏ i, g (xs i)) ∘ e := by
      funext ab
      simp [e,f,Fin.consEquiv,Fin.prod_univ_succ]
      ring
    change HasSum (fun ab : X × (Fin n → X) => μ ab.1 * g ab.1 * f ab.2) _ at ha
    rw [he] at ha
    simpa only [pow_succ'] using e.hasSum_iff.mp ha

end

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

end P2MDyadicModule4

/- Helper module Solutions.AdvantageBridgeArithmetic. -/
section P2MDyadicModule5

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Bertrand's postulate bounds the least-prime modulus by the explicit polynomial. -/
theorem famq_le_explicit_polynomial (lam : ℕ) :
    famq lam ≤ 2 ^ 17 * (lam + 2) ^ 64 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul
    (2 ^ 16 * famL lam ^ 64) (by unfold famL; positivity)
  have hminimal : famq lam ≤ p :=
    Nat.find_min' (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64)) ⟨hlt.le, hp⟩
  calc
    famq lam ≤ p := hminimal
    _ ≤ 2 * (2 ^ 16 * famL lam ^ 64) := hle
    _ = 2 ^ 17 * (lam + 2) ^ 64 := by unfold famL; norm_num [← mul_assoc]

/-- The block dimension is also bounded by one explicit polynomial. -/
theorem famd_polynomially_bounded : PolyBoundedFn famd := by
  refine ⟨Polynomial.C (2 ^ 17) * (Polynomial.X + Polynomial.C 2) ^ 160 +
    Polynomial.C 2 * (Polynomial.X + Polynomial.C 2) ^ 128, ?_⟩
  intro lam
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  unfold famd famL
  calc
    famq lam * (lam + 2) ^ 96 + 2 * (lam + 2) ^ 128 ≤
      (2 ^ 17 * (lam + 2) ^ 64) * (lam + 2) ^ 96 + 2 * (lam + 2) ^ 128 := by
        gcongr
        exact famq_le_explicit_polynomial lam
    _ = _ := by rw [mul_assoc, ← pow_add]

end InfoLossLAR.WorstCase

end P2MDyadicModule5

/- Helper module Budget. -/
section P2MDyadicModule6

set_option autoImplicit false

set_option maxHeartbeats 800000

namespace InfoLossLAR.WorstCase.ShortProbePlan

open Polynomial

noncomputable section

def rows (p : Polynomial ℕ) (n : ℕ) := p.eval n*famd n

def widths (p : Polynomial ℕ) (n : ℕ) := 768*(rows p n + 1)

def cutoffSize (p : Polynomial ℕ) (n : ℕ) := (n+2)*widths p n

def coinWidth (p : Polynomial ℕ) (n : ℕ) := (widths p n + 1) + (2*cutoffSize p n + 1) + 1

def trialSize (p : Polynomial ℕ) (n : ℕ) := rows p n + rows p n*coinWidth p n

def saved (n : ℕ) := 16*(n+1)^2

def used (p : Polynomial ℕ) (n : ℕ) := saved n + n*trialSize p n

def jobCount (p : Polynomial ℕ) (n : ℕ) := (widths p n + 1)*n

theorem pool_budget (p : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ n, used p n ≤ P.eval n ∧ jobCount p n ≤ P.eval n ∧
      cutoffSize p n ≤ P.eval n ∧ widths p n ≤ P.eval n ∧ famd n ≤ P.eval n ∧ p.eval n ≤ P.eval n := by
  obtain ⟨d,hd⟩ := famd_polynomially_bounded
  let c := p*d
  let m := C 768 * (c+1)
  let t := (X+2)*m
  let b := (m+1) + (C 2*t+1) + 1
  let z := C 16*(X+1)^2 + X*(c+c*b)
  let tasks := (m+1)*X
  refine ⟨z+tasks+t+m+d+p,fun n => ?_⟩
  have hc : rows p n ≤ c.eval n := by simpa [rows,c] using Nat.mul_le_mul_left (p.eval n) (hd n)
  have hm : widths p n ≤ m.eval n := by
    simpa [widths,m] using Nat.mul_le_mul_left 768 (Nat.add_le_add_right hc 1)
  have ht : cutoffSize p n ≤ t.eval n := by simpa [cutoffSize,t] using Nat.mul_le_mul_left (n+2) hm
  have hb : coinWidth p n ≤ b.eval n := by
    simp only [coinWidth,b,eval_add,eval_one,eval_mul,eval_C]; omega
  have hz : used p n ≤ z.eval n := by
    simp only [used, saved, trialSize,z,eval_add,eval_mul,eval_C,eval_pow,eval_X,eval_one]
    gcongr
  have hj : jobCount p n ≤ tasks.eval n := by
    simpa [jobCount,tasks] using Nat.mul_le_mul_right n (Nat.add_le_add_right hm 1)
  have hd' := hd n
  simp only [eval_add]
  omega

end

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule6

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule7

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

theorem anchor_eq (center : ℚ) : anchor center=(centeredGaussianAnchor center : ℚ) := by
  unfold anchor
  split <;> rename_i hc
  · have hn := Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hc.le)
    rw [←Int.cast_natCast,hn,Int.ceil_neg,Int.cast_neg,neg_neg]
    rfl
  · rw [←Int.cast_natCast,Int.natCast_floor_eq_floor (le_of_not_gt hc)]
    rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

end P2MDyadicModule7

/- Helper module Solutions.RegevBridgeGaussianLatticeTransport. -/
section P2MDyadicModule8

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

instance image_discrete (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    DiscreteTopology (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

instance image_full_rank (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    IsZLattice ℝ (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

/-- Self-adjointness transports dual membership through the forward map. -/
theorem mem_dual_image_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : Space (dimension := dimension)) :
    value ∈ dual (imageLattice lattice transform) ↔ transform value ∈ dual lattice := by
  change (∀ test ∈ imageLattice lattice transform,
    inner ℝ value test ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ test ∈ lattice, inner ℝ (transform value) test ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro membership test test_mem
    rw [selfAdjoint]
    apply membership
    simpa using test_mem
  · intro membership test test_mem
    have h := membership (transform.symm test) test_mem
    rw [selfAdjoint, transform.apply_symm_apply] at h
    exact h

/-- The dual of the image is parametrized by the inverse map on the old dual. -/
def dualEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    dual lattice ≃ dual (imageLattice lattice transform) where
  toFun value := ⟨transform.symm value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mpr (by simpa using value.property)⟩
  invFun value := ⟨transform value,
    (mem_dual_image_iff lattice transform selfAdjoint _).mp value.property⟩
  left_inv value := by ext; simp
  right_inv value := by ext; simp

@[simp] theorem dualEquiv_eq_zero_iff (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (value : dual lattice) :
    dualEquiv lattice transform selfAdjoint value = 0 ↔ value = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun z : dual (imageLattice lattice transform) =>
      transform (z : Space (dimension := dimension))) h
    change transform (transform.symm (value : Space (dimension := dimension))) =
      transform (0 : Space (dimension := dimension)) at h'
    change (value : Space (dimension := dimension)) = 0
    simpa only [transform.apply_symm_apply, map_zero] using h'
  · rintro rfl
    apply Subtype.ext
    change transform.symm (0 : Space (dimension := dimension)) = 0
    exact map_zero _

def dualNonzeroEquiv (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) :
    {value : dual lattice // value ≠ 0} ≃
      {value : dual (imageLattice lattice transform) // value ≠ 0} :=
  (dualEquiv lattice transform selfAdjoint).subtypeEquiv (by
    intro value
    exact not_congr (dualEquiv_eq_zero_iff lattice transform selfAdjoint value).symm)

/-- Exact reindexing of the entire nonzero-dual Gaussian sum. -/
theorem rhoDualNonzero_image (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (selfAdjoint : ∀ first second, inner ℝ (transform first) second =
      inner ℝ first (transform second)) (width : ℝ) :
    rhoDualNonzero width (imageLattice lattice transform) =
      ∑' value : {value : dual lattice // value ≠ 0},
        rho width (transform.symm ((value : dual lattice) : Space (dimension := dimension))) := by
  unfold rhoDualNonzero
  symm
  have reindex := (dualNonzeroEquiv lattice transform selfAdjoint).tsum_eq
    (fun value : {value : dual (imageLattice lattice transform) // value ≠ 0} =>
      rho width ((value.val : dual (imageLattice lattice transform)) : Space (dimension := dimension)))
  exact reindex

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end P2MDyadicModule8

/- Helper module Solutions.RegevBridgeGaussianProjectionSmoothing. -/
section P2MDyadicModule9

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv

noncomputable section

open scoped BigOperators

/-- A usable public version of the smoothing-threshold consequence. The
zero-dimensional case is discharged, and the positive-dimensional case
uses the recovered, proved exact characterization of smoothingParam. -/
theorem dual_mass_le_of_smoothing {dimension : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    {error width : ℝ} (herror : 0<error) (hwidth : 0<width) (hsmoothing : smoothingParam lattice error ≤ width) :
    rhoDualNonzero (1/width) lattice ≤ error := by
  rcases Nat.eq_zero_or_pos dimension with rfl | hdimension
  · have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    have : IsEmpty {value : dual lattice // value≠0} :=
      ⟨fun value => value.property (Subsingleton.elim value.val 0)⟩
    unfold rhoDualNonzero
    simp [herror.le]
  · obtain ⟨_,hantitone,_,_,hthreshold⟩ := RegevLWE.GaussConv.smoothing_remark hdimension lattice
    obtain ⟨hpositive,hequal⟩ := hthreshold error herror
    rw [←hequal]
    exact hantitone.antitoneOn hpositive hwidth hsmoothing

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule9

/- Helper module Solutions.RegevBridgeGaussianLatticeScaling. -/
section P2MDyadicModule10

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem dilation_apply (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    dilation factor hfactor value=factor • value := rfl

theorem dilation_symmetric (factor : ℝ) (hfactor : 0<factor) (first second : ScalingSpace (dimension:=dimension)) :
    inner ℝ (dilation factor hfactor first) second=inner ℝ first (dilation factor hfactor second) := by
  rw [dilation_apply,dilation_apply,real_inner_smul_left,real_inner_smul_right]

theorem rho_dilation_inverse (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width)
    (value : ScalingSpace (dimension:=dimension)) :
    rho width ((dilation factor hfactor).symm value)=rho (factor*width) value := by
  unfold rho
  rw [dilation_symm_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hfactor)]
  congr 1
  field_simp [hfactor.ne',hwidth.ne']

theorem rhoDualNonzero_dilation (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension)))
    (factor width : ℝ) (hfactor : 0<factor) (hwidth : 0<width) :
    rhoDualNonzero width (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor))=
      rhoDualNonzero (factor*width) lattice := by
  rw [rhoDualNonzero_image lattice (dilation factor hfactor) (dilation_symmetric factor hfactor)]
  simp_rw [rho_dilation_inverse factor width hfactor hwidth]
  rfl

/-- A proved smoothing upper bound under actual lattice dilation.
Only the source smoothing condition is required. -/
theorem dilation_smoothing_le
    (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (factor width error : ℝ) (hfactor : 0<factor) (hwidth : 0<width) (herror : 0<error)
    (hsmoothing : smoothingParam lattice error ≤ width) :
    smoothingParam (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) error ≤ factor*width := by
  have hm : rhoDualNonzero (1/(factor*width)) (GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor)) ≤ error := by
    rw [rhoDualNonzero_dilation lattice factor (1/(factor*width)) hfactor (by positivity)]
    have he : factor*(1/(factor*width))=1/width := by field_simp
    rw [he]
    exact dual_mass_le_of_smoothing lattice herror hwidth hsmoothing
  unfold smoothingParam
  apply csInf_le
  · exact ⟨0,fun value membership => membership.1.le⟩
  · exact ⟨mul_pos hfactor hwidth,hm⟩

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule10

/- Helper module Solutions.RegevBridgeGaussianProjectionProbability. -/
section P2MDyadicModule11

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ProbabilitySpace := EuclideanSpace ℝ (Fin dimension)

/-- Positive coset normalizer from the actual Poisson mass bound. -/
theorem rhoCoset_pos_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    0<rhoCoset width lattice shift := by
  have h := (abs_le.mp (claim_3_8 lattice shift herror hwidth hsmoothing)).1
  have hp : 0<width^dimension*(ZLattice.covolume lattice)⁻¹ :=
    mul_pos (pow_pos hwidth _) (inv_pos.mpr (ZLattice.covolume_pos lattice))
  nlinarith

theorem summable_coset_of_smoothing
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (fun value : lattice => rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  have hpos := rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing
  exact hpos.ne' hzero

/-- The genuine discrete Gaussian masses on the actual lattice coset. -/
def cosetMass (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) : ℝ :=
  discreteGaussian lattice shift width ((value : ProbabilitySpace (dimension:=dimension))+shift)

theorem cosetMass_formula (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) :
    cosetMass lattice shift width value=
      rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  unfold cosetMass discreteGaussian
  rw [Set.indicator_of_mem]
  simpa only [Set.mem_ofPred_eq,add_sub_cancel_right] using value.property

theorem cosetMass_nonneg
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) : 0 ≤ cosetMass lattice shift width value := by
  rw [cosetMass_formula]
  exact div_nonneg (Real.exp_nonneg _) (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).le

theorem cosetMass_summable
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    Summable (cosetMass lattice shift width) := by
  simp_rw [funext (cosetMass_formula lattice shift width)]
  exact (summable_coset_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).div_const _

theorem cosetMass_sum
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    (∑' value : lattice,cosetMass lattice shift width value)=1 := by
  simp_rw [cosetMass_formula]
  rw [tsum_div_const]
  exact div_self (rhoCoset_pos_of_smoothing lattice shift hwidth herror herrorOne hsmoothing).ne'

/-- Literal PMF of the input lattice-Gaussian sample law. This does not
assert the existence of an efficient DGS sampler. -/
def cosetPMF
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) : PMF lattice :=
  ⟨fun value => ENNReal.ofReal (cosetMass lattice shift width value),by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [←ENNReal.ofReal_tsum_of_nonneg (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing)
      (cosetMass_summable lattice shift hwidth herror herrorOne hsmoothing),
      cosetMass_sum lattice shift hwidth herror herrorOne hsmoothing,ENNReal.ofReal_one]⟩

theorem cosetPMF_toReal
    (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (shift : ProbabilitySpace (dimension:=dimension)) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (value : lattice) :
    (cosetPMF lattice shift hwidth herror herrorOne hsmoothing value).toReal=cosetMass lattice shift width value :=
  ENNReal.toReal_ofReal (cosetMass_nonneg lattice shift hwidth herror herrorOne hsmoothing value)

/-- Normalization of the real masses of any literal countable PMF. -/
theorem pmf_realMass_sum {State : Type*} (law : PMF State) :
    (∑' value : State,(law value).toReal)=1 := by
  rw [←ENNReal.tsum_toReal_eq (fun value => law.apply_ne_top value),law.tsum_coe,ENNReal.toReal_one]

theorem pmf_realMass_summable {State : Type*} (law : PMF State) :
    Summable (fun value : State => (law value).toReal) := by
  by_contra hnonsummable
  have hzero := tsum_eq_zero_of_not_summable hnonsummable
  rw [pmf_realMass_sum] at hzero
  norm_num at hzero

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule11

/- Helper module Solutions.RegevBridgeGaussianCosetGeometry. -/
section P2MDyadicModule12

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Public coefficients and the hidden secret live in the same fixed
input basis; zero secret coordinates are allowed. -/
def publicCoordinates {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) : Index → ZMod q :=
  fun index => (basis.equivFun value index : ZMod q)

/-- Canonical input-basis representative of each public residue vector. -/
def lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) : lattice :=
  basis.equivFun.symm (fun index => ((color index).val : ℤ))

theorem publicCoordinates_lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) :
    publicCoordinates q lattice basis (lift q lattice basis color)=color := by
  funext index
  unfold publicCoordinates lift
  rw [LinearEquiv.apply_symm_apply]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem modulusLattice_le (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) :
    modulusLattice q lattice ≤ lattice := by
  intro value membership
  obtain ⟨original,horiginal,rfl⟩ := (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) value).mp membership
  have h := lattice.smul_mem (q : ℤ) horiginal
  simpa only [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h

/-- The actual point in the coset qL+u, viewed back in L. -/
def sample (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (shift : lattice) (value : modulusLattice q lattice) : lattice :=
  ⟨(value : Space (dimension:=dimension))+(shift : Space (dimension:=dimension)),
    lattice.add_mem (modulusLattice_le q lattice value.property) shift.property⟩

instance modulus_discrete (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] :
    DiscreteTopology (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

instance modulus_full_rank (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice] :
    IsZLattice ℝ (modulusLattice q lattice) := by unfold modulusLattice;infer_instance

theorem publicCoordinates_add {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first+second)=publicCoordinates q lattice basis first+publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_add,Pi.add_apply,Int.cast_add]

theorem publicCoordinates_sub {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (first second : lattice) :
    publicCoordinates q lattice basis (first-second)=publicCoordinates q lattice basis first-publicCoordinates q lattice basis second := by
  funext index
  simp only [publicCoordinates,map_sub,Pi.sub_apply,Int.cast_sub]

/-- The zero public-coefficient fiber is exactly the actual q-dilate. -/
theorem publicCoordinates_zero_iff {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (value : lattice) :
    publicCoordinates q lattice basis value=0 ↔ (value : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  constructor
  · intro hzero
    have hdiv (index : Index) : (q : ℤ) ∣ basis.equivFun value index :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp (by simpa only [publicCoordinates,Pi.zero_apply] using congrFun hzero index)
    let original := basis.equivFun.symm (fun index => basis.equivFun value index/(q : ℤ))
    have he : (q : ℤ) • original=value := by
      apply basis.equivFun.injective
      rw [map_smul]
      funext index
      simp only [original,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
      exact Int.mul_ediv_cancel' (hdiv index)
    apply (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mpr
    refine ⟨(original : Space (dimension:=dimension)),original.property,?_⟩
    have h := congrArg (fun point : lattice => (point : Space (dimension:=dimension))) he
    simpa only [Submodule.coe_smul,←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast] using h
  · intro membership
    obtain ⟨original,horiginal,heq⟩ :=
      (mem_dilated_lattice lattice (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)) (value : Space (dimension:=dimension))).mp membership
    let originalPoint : lattice := ⟨original,horiginal⟩
    have he : value=(q : ℤ) • originalPoint := by
      apply Subtype.ext
      change (value : Space (dimension:=dimension))=(q : ℤ) • original
      rw [←Int.cast_smul_eq_zsmul ℝ,Int.cast_natCast]
      exact heq.symm
    rw [he]
    funext index
    simp [publicCoordinates,Pi.smul_apply]

theorem publicCoordinates_sample {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (shift : lattice) (value : modulusLattice q lattice) :
    publicCoordinates q lattice basis (sample q lattice shift value)=publicCoordinates q lattice basis shift := by
  let original : lattice := ⟨(value : Space (dimension:=dimension)),modulusLattice_le q lattice value.property⟩
  have hz : publicCoordinates q lattice basis original=0 :=
    (publicCoordinates_zero_iff q lattice basis original).mpr value.property
  change publicCoordinates q lattice basis (original+shift)=publicCoordinates q lattice basis shift
  rw [publicCoordinates_add,hz,zero_add]

theorem publicCoordinates_fiber {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice)
    (color : Index → ZMod q) (value : lattice) :
    publicCoordinates q lattice basis value=color ↔
      ((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)) ∈ modulusLattice q lattice := by
  rw [←publicCoordinates_zero_iff q lattice basis (value-lift q lattice basis color),
    publicCoordinates_sub,publicCoordinates_lift,sub_eq_zero]

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule12

/- Helper module Solutions.RegevBridgeFiniteProductMass. -/
section P2MDyadicModule13

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- The full countable joint product law, not just its coordinate marginals. -/
def finiteProductMass {Index : Type*} (dimension : ℕ) (mass : Index → ℝ) (word : Fin dimension → Index) : ℝ :=
  ∏ index,mass (word index)

theorem finiteProductMass_nonnegative {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (word : Fin dimension → Index) :
    0 ≤ finiteProductMass dimension mass word := Finset.prod_nonneg (fun _ _ => hnonnegative _)

/-- A genuine full infinite product-law normalization in finitely many
coordinates, valid without finiteness of the individual coordinate space. -/
theorem finiteProductMass_hasSum {Index : Type*} (dimension : ℕ) (mass : Index → ℝ)
    (hnonnegative : ∀ value,0 ≤ mass value) (hsummable : Summable mass) :
    HasSum (finiteProductMass dimension mass) ((∑' value,mass value)^dimension) := by
  classical
  induction dimension with
  | zero =>
    rw [pow_zero]
    have heq : finiteProductMass 0 mass=(fun _ : Fin 0 → Index => (1 : ℝ)) := by
      funext word
      simp only [finiteProductMass,Finset.univ_eq_empty,Finset.prod_empty]
    rw [heq]
    convert hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)) using 1
    simp
  | succ dimension ih =>
    have hs := hsummable.mul_of_nonneg ih.summable hnonnegative
      (finiteProductMass_nonnegative dimension mass hnonnegative)
    have hp := hsummable.hasSum.mul ih hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass pair.1*finiteProductMass dimension mass pair.2)=
        (finiteProductMass (dimension+1) mass) ∘ (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,finiteProductMass,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [pow_succ,mul_comm] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule13

/- Helper module Solutions.RegevBridgeDependentProductMass. -/
section P2MDyadicModule14

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped BigOperators

noncomputable section

/-- Full jointly independent countable family normalization, allowing
coordinate-dependent channels and output tests in every factor. -/
theorem dependentProductMass_hasSum {Index : Type*} (dimension : ℕ)
    (mass : Fin dimension → Index → ℝ)
    (hnonnegative : ∀ index value,0 ≤ mass index value) (hsummable : ∀ index,Summable (mass index)) :
    HasSum (fun word : Fin dimension → Index => ∏ index,mass index (word index))
      (∏ index,∑' value,mass index value) := by
  classical
  induction dimension with
  | zero =>
    have heq : (fun word : Fin 0 → Index => ∏ index,mass index (word index))=(fun _ => (1 : ℝ)) := by
      funext word
      simp
    rw [heq]
    simpa only [Finset.univ_eq_empty,Finset.prod_empty,Fintype.sum_unique] using
      (hasSum_fintype (fun _ : Fin 0 → Index => (1 : ℝ)))
  | succ dimension ih =>
    have htail := ih (fun index => mass index.succ) (fun index => hnonnegative index.succ)
      (fun index => hsummable index.succ)
    have htailNonnegative (word : Fin dimension → Index) : 0 ≤ ∏ index,mass index.succ (word index) :=
      Finset.prod_nonneg (fun _ _ => hnonnegative _ _)
    have hs := (hsummable 0).mul_of_nonneg htail.summable (hnonnegative 0) htailNonnegative
    have hp := (hsummable 0).hasSum.mul htail hs
    have hcompose : (fun pair : Index×(Fin dimension → Index) => mass 0 pair.1*(∏ index,mass index.succ (pair.2 index)))=
        (fun word : Fin (dimension+1) → Index => ∏ index,mass index (word index)) ∘
          (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)) := by
      funext pair
      simp only [Function.comp_apply,Fin.consEquiv,Equiv.coe_fn_mk,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rw [hcompose] at hp
    have h := (Fin.consEquiv (fun _ : Fin (dimension+1) => Index)).hasSum_iff.mp hp
    simpa only [Fin.prod_univ_succ] using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule14

/- Helper module Solutions.RegevBridgeCountableProductChannel. -/
section P2MDyadicModule15

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open AFT

open scoped BigOperators

noncomputable section

/-- The literal full output table after independent finite kernels are
applied to the whole independent countable source pool. -/
def countableProductChannel {Source Output : Type*} [Fintype Output]
    (count : ℕ) (mass : Source → ℝ) (hnonnegative : ∀ source,0 ≤ mass source)
    (hsummable : Summable mass) (hmass : (∑' source,mass source)=1)
    (kernel : Fin count → Source → FiniteDist Output) : FiniteDist (Fin count → Output) :=
  FiniteDist.countableMix (finiteProductMass count mass) (finiteProductMass_nonnegative count mass hnonnegative)
    (finiteProductMass_hasSum count mass hnonnegative hsummable).summable
    (by rw [(finiteProductMass_hasSum count mass hnonnegative hsummable).tsum_eq,hmass,one_pow])
    (fun source => FiniteDist.independent (fun index => kernel index (source index)))

/-- Every joint table probability factors exactly; the statement is much
stronger than correctness of the separate output marginals. -/
theorem countableProductChannel_eq {Source Output : Type*} [Fintype Output]
    (count : ℕ) (mass : Source → ℝ) (hnonnegative : ∀ source,0 ≤ mass source)
    (hsummable : Summable mass) (hmass : (∑' source,mass source)=1)
    (kernel : Fin count → Source → FiniteDist Output) :
    countableProductChannel count mass hnonnegative hsummable hmass kernel=
      FiniteDist.independent (fun index => FiniteDist.countableMix mass hnonnegative hsummable hmass (kernel index)) := by
  classical
  ext output
  change (∑' source : Fin count → Source,
    (∏ index,mass (source index))*(∏ index,(kernel index (source index)).weight (output index)))=
    ∏ index,∑' source,mass source*(kernel index source).weight (output index)
  have hpoint (source : Fin count → Source) :
      (∏ index,mass (source index))*(∏ index,(kernel index (source index)).weight (output index))=
        ∏ index,mass (source index)*(kernel index (source index)).weight (output index) :=
    (Finset.prod_mul_distrib).symm
  simp_rw [hpoint]
  exact (dependentProductMass_hasSum count
    (fun index source => mass source*(kernel index source).weight (output index))
    (fun _ _ => mul_nonneg (hnonnegative _) ((kernel _ _).nonneg _))
    (fun index => FiniteDist.countableChannel_summable mass hsummable (kernel index) (output index))).tsum_eq

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end P2MDyadicModule15

/- Helper module Solutions.RegevBridgeGaussianCosetPartition. -/
section P2MDyadicModule16

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators Classical

noncomputable section

variable {dimension : ℕ} {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Exact partition of L by its actual input-basis residue vector. -/
def partitionEquiv (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) : lattice ≃ (Index → ZMod q) × modulusLattice q lattice where
  toFun value :=
    let color := publicCoordinates q lattice basis value
    (color,⟨((value-lift q lattice basis color : lattice) : Space (dimension:=dimension)),
      (publicCoordinates_fiber q lattice basis color value).mp rfl⟩)
  invFun pair := sample q lattice (lift q lattice basis pair.1) pair.2
  left_inv value := by
    apply Subtype.ext
    change ((value : Space (dimension:=dimension))-(lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension)))+
      (lift q lattice basis (publicCoordinates q lattice basis value) : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
    abel
  right_inv pair := by
    rcases pair with ⟨color,value⟩
    have hc := (publicCoordinates_sample q lattice basis (lift q lattice basis color) value).trans
      (publicCoordinates_lift q lattice basis color)
    apply Prod.ext
    · exact hc
    · apply Subtype.ext
      change ((sample q lattice (lift q lattice basis color) value : Space (dimension:=dimension))-
        (lift q lattice basis (publicCoordinates q lattice basis (sample q lattice (lift q lattice basis color) value)) : Space (dimension:=dimension)))=
        (value : Space (dimension:=dimension))
      rw [hc]
      change ((value : Space (dimension:=dimension))+(lift q lattice basis color : Space (dimension:=dimension)))-
        (lift q lattice basis color : Space (dimension:=dimension))=(value : Space (dimension:=dimension))
      abel

omit [DecidableEq Index] in
theorem partitionEquiv_public_symm (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis Index ℤ lattice) (pair : (Index → ZMod q) × modulusLattice q lattice) :
    publicCoordinates q lattice basis ((partitionEquiv q lattice basis).symm pair)=pair.1 := by
  exact congrArg Prod.fst ((partitionEquiv q lattice basis).apply_symm_apply pair)

/-- The true public coefficient law of the original lattice Gaussian. -/
def coefficientLaw (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width) :
    FiniteDist (Index → ZMod q) :=
  finiteLaw ((cosetPMF lattice 0 hwidth herror herrorOne hsmoothing).map (publicCoordinates q lattice basis))

/-- Every public point mass is the actual qL-coset Gaussian mass divided
by the original lattice normalizer. No coset probability is assumed. -/
theorem coefficientLaw_weight (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1) (hsmoothing : smoothingParam lattice error ≤ width)
    (color : Index → ZMod q) :
    (coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 := by
  classical
  let source := cosetPMF lattice 0 hwidth herror herrorOne hsmoothing
  let function : lattice → ℝ := fun value =>
    if publicCoordinates q lattice basis value=color then (source value).toReal else 0
  have hfunction : Summable function := by
    apply Summable.of_nonneg_of_le _ _ (pmf_realMass_summable source)
    · intro value;dsimp only [function];split_ifs <;> positivity
    · intro value;dsimp only [function];split_ifs <;> simp [ENNReal.toReal_nonneg]
  let equivalence := partitionEquiv q lattice basis
  have hpairs : Summable (function ∘ equivalence.symm) := equivalence.symm.summable_iff.mpr hfunction
  change Summable (fun pair => function (equivalence.symm pair)) at hpairs
  have hreindex := equivalence.symm.tsum_eq function
  rw [hpairs.tsum_prod,tsum_fintype] at hreindex
  unfold coefficientLaw
  rw [Integration.finiteLaw_map_weight]
  suffices hfinal : (∑' value : lattice,function value)=
      rhoCoset width (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension))/rhoCoset width lattice 0 by
    calc
      _ = ∑' value : lattice,function value := by
        apply tsum_congr
        intro value
        dsimp only [function,source]
        split_ifs <;> rfl
      _ = _ := hfinal
  rw [←hreindex]
  have hinner (selected : Index → ZMod q) :
      (∑' value : modulusLattice q lattice,function (equivalence.symm (selected,value)))=
      if selected=color then rhoCoset width (modulusLattice q lattice)
        (lift q lattice basis selected : Space (dimension:=dimension))/rhoCoset width lattice 0 else 0 := by
    have hpublic (value : modulusLattice q lattice) : publicCoordinates q lattice basis (equivalence.symm (selected,value))=selected :=
      partitionEquiv_public_symm q lattice basis (selected,value)
    dsimp only [function]
    simp_rw [hpublic]
    by_cases hc : selected=color
    · simp only [hc,ite_true]
      simp only [source,cosetPMF_toReal,cosetMass_formula,add_zero]
      rw [tsum_div_const]
      rfl
    · simp only [hc,ite_false,tsum_zero]
  simp_rw [hinner]
  simp

/-- The actual public residues of a wide lattice Gaussian are near uniform.
The common covolume scale is removed using both laws' true normalization,
so no determinant-index identity or unproved conditional law is needed. -/
theorem coefficientLaw_uniform (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (basis : Module.Basis Index ℤ lattice) {width error : ℝ}
    (hwidth : 0<width) (herror : 0<error) (herrorOne : error<1)
    (hsmoothing : smoothingParam lattice error ≤ width)
    (hmodulus : smoothingParam (modulusLattice q lattice) error ≤ width) :
    (∑ color : Index → ZMod q, |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-
      (FiniteDist.uniform (Index → ZMod q)).weight color|)/2 ≤ error/(1-error) := by
  classical
  let actual := coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing
  let reference := FiniteDist.uniform (Index → ZMod q)
  let mass := rhoCoset width lattice 0
  let main := width^dimension*(ZLattice.covolume (modulusLattice q lattice))⁻¹
  let scale := (Fintype.card (Index → ZMod q) : ℝ)*main/mass
  have hmass : 0 < mass := rhoCoset_pos_of_smoothing lattice 0 hwidth herror herrorOne hsmoothing
  have hcard : (Fintype.card (Index → ZMod q) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hscaled (color : Index → ZMod q) : scale*reference.weight color=main/mass := by
    change ((Fintype.card (Index → ZMod q) : ℝ)*main/mass)*(Fintype.card (Index → ZMod q) : ℝ)⁻¹=main/mass
    field_simp
  have hpoint (color : Index → ZMod q) : |actual.weight color-scale*reference.weight color| ≤
      error*scale*reference.weight color := by
    rw [mul_assoc error scale,hscaled]
    change |(coefficientLaw q lattice basis hwidth herror herrorOne hsmoothing).weight color-main/mass| ≤ error*(main/mass)
    rw [coefficientLaw_weight,←sub_div,abs_div,abs_of_pos hmass]
    have h := div_le_div_of_nonneg_right
      (claim_3_8 (modulusLattice q lattice) (lift q lattice basis color : Space (dimension:=dimension)) herror hwidth hmodulus) hmass.le
    simpa only [main,mul_div_assoc] using h
  have h := normalized_tilt_total_variation reference.weight actual.weight reference.nonneg
    (hasSum_fintype _).summable (hasSum_fintype _).summable
    (by rw [tsum_fintype];exact reference.sum_one)
    (by rw [tsum_fintype];exact actual.sum_one) scale error herror.le herrorOne hpoint
  simpa only [tsum_fintype] using h

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule16

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule17

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

theorem projection_spec (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (value : Fin dimension → ℤ) :
    (projection basis query value : ℝ)=inner ℝ (rationalPoint query) (latVec basis value) := by
  unfold projection rationalPoint latVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

theorem publicCoordinates_coefficient_point (q : ℕ)
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (value : Fin dimension → ℤ) :
    CosetGeometry.publicCoordinates q (inputLattice basis hdet) (integerBasis basis hdet)
      ((integerBasis basis hdet).equivFun.symm value)=(fun index => (value index : ZMod q)) := by
  unfold CosetGeometry.publicCoordinates
  rw [LinearEquiv.apply_symm_apply]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule17

/- Helper module Integration9_9.TM2NativeAffineApply. -/
section P2MDyadicModule18

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeAffineApply

open AFT AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open InfoLossLAR.WorstCase

open scoped BigOperators

private theorem zip_ofFn {α β : Type} {n : ℕ} (f : Fin n→α) (g : Fin n→β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i=>(f i,g i)) := by apply List.ext_getElem <;> simp

theorem dot_ofFn {n : ℕ} (f g : Fin n→ℤ) : dot (List.ofFn f,List.ofFn g)=∑i,f i*g i := by
  simp only [dot,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]

end Integration9_9.TM2NativeAffineApply

end P2MDyadicModule18

/- Helper module Solutions.RegevBridgeIntegerBasisNative. -/
section P2MDyadicModule19

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

private theorem zip_ofFn {α β : Type*} {count : ℕ} (left : Fin count → α) (right : Fin count → β) :
    (List.ofFn left).zip (List.ofFn right)=List.ofFn (fun index => (left index,right index)) := by
  apply List.ext_getElem
  · simp
  · intros;simp

theorem dot_ofFn {count : ℕ} (left : Fin count → ℚ) (right : Fin count → ℤ) :
    dot (List.ofFn left,List.ofFn right)=∑ index,left index*(right index : ℚ) := by
  simp only [dot,zip_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

theorem matrixApply_ofFn {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (value : Fin dimension → ℤ) :
    matrixApply (List.ofFn (fun row => List.ofFn (basis row)),List.ofFn value)=List.ofFn (basis.mulVec value) := by
  simp only [matrixApply,List.map_ofFn]
  apply congrArg List.ofFn
  funext row
  simp only [Function.comp_apply,Integration9_9.TM2NativeAffineApply.dot,zip_ofFn,List.map_ofFn,List.sum_ofFn]
  rfl

theorem projection_ofFn {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (value : Fin dimension → ℤ) (query : Fin dimension → ℚ) :
    projection ((List.ofFn (fun row => List.ofFn (basis row)),List.ofFn value),List.ofFn query)=
      IntegerBasis.projection basis query value := by
  rw [projection,matrixApply_ofFn,dot_ofFn]
  rfl

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule19

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule20

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

@[fun_prop] theorem naturalBits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩

@[fun_prop] theorem signedAbsolute_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule20

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule21

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

abbrev QVector (dimension : ℕ) := Fin dimension → ℚ

abbrev Space (dimension : ℕ) := EuclideanSpace ℝ (Fin dimension)

def innerQ {dimension : ℕ} (left right : QVector dimension) : ℚ := ∑ index,left index*right index

def realVec {dimension : ℕ} (vector : QVector dimension) : Space dimension :=
  WithLp.toLp 2 (fun index => (vector index : ℝ))

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

/-- Every projection uses the original current vector and cached earlier
orthogonal vectors; the running algorithm never recomputes its recursion tree. -/
def projection {dimension : ℕ} (orthogonal current : QVector dimension) : QVector dimension :=
  (innerQ orthogonal current/innerQ orthogonal orthogonal) • orthogonal

def orthogonalStep {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) : QVector dimension :=
  current-(previous.map (fun orthogonal => projection orthogonal current)).sum

/-- Materialized rational Gram--Schmidt cache. A finite input prefix is
processed exactly once; division by zero keeps malformed inputs total. -/
def cache {dimension count : ℕ} (vectors : Fin count → QVector dimension) : ℕ → List (QVector dimension)
  | 0 => []
  | steps+1 =>
      let previous := cache vectors steps
      let current := if h : steps<count then vectors ⟨steps,h⟩ else 0
      previous++[orthogonalStep previous current]

theorem cache_length {dimension count : ℕ} (vectors : Fin count → QVector dimension) (steps : ℕ) :
    (cache vectors steps).length=steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cache,List.length_append,List.length_singleton,ih]

def orthogonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : QVector dimension :=
  (cache vectors count).getD index.val 0

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

/-- Orthogonal projection only decreases the original column's square norm. -/
theorem gramSchmidt_norm_sq_le {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    ‖gramSchmidt ℝ vectors index‖^2 ≤ ‖vectors index‖^2 := by
  let orthogonal := gramSchmidt ℝ vectors
  have heq : inner ℝ (orthogonal index) (vectors index)=inner ℝ (orthogonal index) (orthogonal index) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal index)
        (∑ previous ∈ Finset.Iio index,
          (inner ℝ (orthogonal previous) (vectors index)/‖orthogonal previous‖^2) • orthogonal previous)=0 by
      change inner ℝ (orthogonal index) (orthogonal index)+_=inner ℝ (orthogonal index) (orthogonal index)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro previous membership
    rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := vectors index-orthogonal index))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal index) (vectors index),heq,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hnonneg
  change ‖orthogonal index‖^2 ≤ _
  linarith

theorem squaredNorm_le {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    squaredNorm vectors index ≤ innerQ (vectors index) (vectors index) := by
  have h := gramSchmidt_norm_sq_le (fun position => realVec (vectors position)) index
  rw [←squaredNorm_real,←real_inner_self_eq_norm_sq,←innerQ_real] at h
  exact_mod_cast h

end

def inputVectors {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (column : Fin dimension) : QVector dimension := fun row => (basis row column : ℚ)

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent

end

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule21

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule22

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule22

/- Helper module Solutions.RegevBridgeWideGaussianFlatTapes. -/
section P2MDyadicModule23

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

noncomputable section

theorem independent_uniform {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Value] [Nonempty Value] :
    FiniteDist.independent (fun _ : Index => FiniteDist.uniform Value)=FiniteDist.uniform (Index → Value) := by
  ext word
  simp only [FiniteDist.independent,FiniteDist.uniform_weight,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow,inv_pow]

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule23

/- Helper module Solutions.RegevBridgeGramDeterminant. -/
section P2MDyadicModule24

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

def prefixGram {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) : Matrix (Fin steps) (Fin steps) ℤ :=
  fun first second => ∑ row,basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)

noncomputable section

theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]

theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h

/-- The subtraction made by Gram--Schmidt lies in the span of precisely
the original earlier columns, not an assumed short basis. -/
theorem gramSchmidt_correction_mem_prefix {dimension count : ℕ}
    (vectors : Fin count → QVector dimension) (index : Fin count) :
    realVec (vectors index)-realVec (orthogonal vectors index) ∈
      Submodule.span ℝ (Set.range (fun previous : Fin index.val =>
        realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))) := by
  classical
  let family := fun position => realVec (vectors position)
  have hset : Set.range (fun previous : Fin index.val =>
      realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))=family '' Set.Iio index := by
    ext point
    constructor
    · rintro ⟨previous,rfl⟩
      refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,?_,rfl⟩
      exact previous.isLt
    · rintro ⟨previous,hprevious,rfl⟩
      exact ⟨⟨previous.val,hprevious⟩,rfl⟩
  rw [hset,←span_gramSchmidt_Iio ℝ family index,orthogonal_real]
  have h := gramSchmidt_def'' ℝ family index
  have hcorrection : family index-gramSchmidt ℝ family index=
      ∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ family previous) (family index)/‖gramSchmidt ℝ family previous‖^2) •
          gramSchmidt ℝ family previous := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,RCLike.ofReal_real_eq_id,id_eq] using h)
  change family index-gramSchmidt ℝ family index ∈ _
  rw [hcorrection]
  apply Submodule.sum_mem
  intro previous hprevious
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨previous,Finset.mem_Iio.mp hprevious,rfl⟩

end

def prefixPairing {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (previous : Fin index.val) : ℤ :=
  ∑ row,basis row ⟨previous.val,previous.isLt.trans index.isLt⟩*basis row index

def gramNumerator {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (row : Fin dimension) : ℤ :=
  (prefixGram basis index.val index.isLt.le).det*basis row index-
    ∑ previous : Fin index.val,
      Matrix.cramer (prefixGram basis index.val index.isLt.le) (prefixPairing basis index) previous*
        basis row ⟨previous.val,previous.isLt.trans index.isLt⟩

noncomputable section

/-- Multiplying the cached rational GS vector by the original integer
prefix-Gram determinant gives an explicitly integral Cramer numerator.
This is the denominator control needed for binary, rather than unit-cost,
complexity of the cached rational orthogonalization. -/
theorem gram_determinant_scales_orthogonal {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (index : Fin dimension) :
    ((prefixGram basis index.val index.isLt.le).det : ℚ) • orthogonal (inputVectors basis) index=
      fun row => (gramNumerator basis index row : ℚ) := by
  classical
  let previousColumn (previous : Fin index.val) : Fin dimension :=
    ⟨previous.val,previous.isLt.trans index.isLt⟩
  let family (previous : Fin index.val) := realVec (inputVectors basis (previousColumn previous))
  let gram := prefixGram basis index.val index.isLt.le
  let rhs := prefixPairing basis index
  let castGram := gram.map (fun value => (value : ℝ))
  obtain ⟨coefficients,hcoefficients⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gramSchmidt_correction_mem_prefix (inputVectors basis) index)
  change (∑ previous,coefficients previous • family previous)=
    realVec (inputVectors basis index)-realVec (orthogonal (inputVectors basis) index) at hcoefficients
  have hinner (first second : Fin index.val) : inner ℝ (family first) (family second)=
      (gram first second : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,
      gram,prefixGram,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
    rfl
  have htarget (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (inputVectors basis index))=(rhs previous : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,prefixPairing,rhs,
      Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
  have horthogonal (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (orthogonal (inputVectors basis) index))=0 := by
    rw [orthogonal_real,real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ (fun position => realVec (inputVectors basis position)) previous.isLt
  have hlinear : castGram.mulVec coefficients=fun previous => (rhs previous : ℝ) := by
    funext previous
    have h := congrArg (fun vector : Space dimension => inner ℝ (family previous) vector) hcoefficients
    simp only [inner_sum,inner_smul_right,inner_sub_right,horthogonal,sub_zero,htarget,hinner] at h
    simpa only [Matrix.mulVec,dotProduct,castGram,Matrix.map_apply,mul_comm] using h
  have hcramer : Matrix.cramer castGram (fun previous => (rhs previous : ℝ))=
      (gram.det : ℝ) • coefficients := by
    rw [←hlinear,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec,←Int.cast_det]
  have hcramerCast (previous : Fin index.val) :
      Matrix.cramer castGram (fun position => (rhs position : ℝ)) previous=
        (Matrix.cramer gram rhs previous : ℝ) := by
    rw [Matrix.cramer_apply,Matrix.cramer_apply]
    have hmatrix : castGram.updateCol previous (fun position => (rhs position : ℝ))=
        (gram.updateCol previous rhs).map (fun value => (value : ℝ)) := by
      ext first second
      simp only [Matrix.updateCol_apply,Matrix.map_apply,castGram]
      split_ifs <;> rfl
    rw [hmatrix,←Int.cast_det]
  have hscaled : (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=
      ∑ previous,(Matrix.cramer gram rhs previous : ℝ) • family previous := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro previous _
    rw [smul_smul]
    have h := congrArg (fun values : Fin index.val → ℝ => values previous) hcramer
    simp only [Pi.smul_apply,smul_eq_mul,hcramerCast] at h
    rw [←h]
  have h := congrArg (fun vector : Space dimension => (gram.det : ℝ) • vector) hcoefficients
  change (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=_ at h
  rw [hscaled] at h
  ext row
  have hrow := congrArg (fun vector : Space dimension => vector row) h
  simp only [family,previousColumn,realVec,inputVectors,WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_sub,Finset.sum_apply,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Rat.cast_intCast] at hrow
  change (gram.det : ℚ)*orthogonal (inputVectors basis) index row=(gramNumerator basis index row : ℚ)
  apply Rat.cast_injective (α:=ℝ)
  simp only [gramNumerator,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_intCast,Int.cast_sub,Int.cast_mul,Int.cast_sum]
  change (gram.det : ℝ)*(orthogonal (inputVectors basis) index row : ℝ)=_
  dsimp [gram,rhs] at hrow ⊢
  linarith

theorem prefixGram_entry_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) (first second : Fin steps) :
    |prefixGram basis steps hsteps first second| ≤ (dimension : ℤ)*bound^2 := by
  unfold prefixGram
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ row,|basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)|) ≤
        ∑ _row : Fin dimension,bound^2 := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hentries row _) (hentries row _) (abs_nonneg _) hbound
    _ = _ := by simp

/-- Every prefix determinant has a bound whose logarithm is polynomial
in the input dimension and the logarithmic entry bound. -/
theorem prefixGram_det_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) :
    |(prefixGram basis steps hsteps).det| ≤ (steps.factorial : ℤ)*((dimension : ℤ)*bound^2)^steps := by
  have h := Matrix.det_le (abv:=AbsoluteValue.abs)
    (prefixGram_entry_bound basis steps hsteps bound hbound hentries)
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using h

/-- A uniform polynomial exponent bounds every integer prefix Gram
normalizer, directly from an entry bit bound of the original input. -/
theorem prefixGram_det_binary_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height) :
    |(prefixGram basis steps hsteps).det| ≤ (2 : ℤ)^((2*dimension+2*height)*dimension) := by
  have hdimension : (dimension : ℤ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hstep : (steps : ℤ) ≤ 2^dimension := (by exact_mod_cast hsteps : (steps : ℤ) ≤ dimension).trans hdimension
  have hfactorial : (steps.factorial : ℤ) ≤ 2^(dimension*steps) := by
    calc
      _ ≤ (steps : ℤ)^steps := by exact_mod_cast Nat.factorial_le_pow steps
      _ ≤ ((2 : ℤ)^dimension)^steps := pow_le_pow_left₀ (Nat.cast_nonneg steps) hstep _
      _ = _ := by rw [←pow_mul]
  have hentryGram : (dimension : ℤ)*((2 : ℤ)^height)^2 ≤ 2^(dimension+2*height) := by
    calc
      _ ≤ (2 : ℤ)^dimension*((2 : ℤ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimension (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _ ≤ (steps.factorial : ℤ)*((dimension : ℤ)*((2 : ℤ)^height)^2)^steps :=
      prefixGram_det_bound basis steps hsteps ((2 : ℤ)^height) (by positivity) hentries
    _ ≤ (2 : ℤ)^(dimension*steps)*(2^(dimension+2*height))^steps :=
      mul_le_mul hfactorial (pow_le_pow_left₀ (by positivity) hentryGram _)
        (by positivity) (by positivity)
    _ = 2^((2*dimension+2*height)*steps) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left (2*dimension+2*height) hsteps)

/-- Every cached rational coordinate has a small absolute magnitude even
when canonical numerators and denominators require separate control. -/
theorem orthogonal_coordinate_abs_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    |orthogonal (inputVectors basis) index row| ≤ (2 : ℚ)^(dimension+height) := by
  have hcoordinate : orthogonal (inputVectors basis) index row^2 ≤
      squaredNorm (inputVectors basis) index := by
    unfold squaredNorm innerQ
    simp only [←sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ row)
  have hcolumn : innerQ (inputVectors basis index) (inputVectors basis index) ≤
      (dimension : ℚ)*((2 : ℚ)^height)^2 := by
    unfold innerQ inputVectors
    simp only [←sq]
    calc
      _ ≤ ∑ _ : Fin dimension,((2 : ℚ)^height)^2 := by
        apply Finset.sum_le_sum
        intro position _
        have hentry : |(basis position index : ℚ)| ≤ (2 : ℚ)^height := by
          exact_mod_cast hentries position index
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hentry
      _ = _ := by simp
  have hdimension : (dimension : ℚ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hpower : (1 : ℚ) ≤ 2^dimension := one_le_pow₀ (by norm_num)
  have hdimensionSquare : (dimension : ℚ) ≤ ((2 : ℚ)^dimension)^2 := by nlinarith
  have hsquare : orthogonal (inputVectors basis) index row^2 ≤ ((2 : ℚ)^(dimension+height))^2 := by
    calc
      _ ≤ squaredNorm (inputVectors basis) index := hcoordinate
      _ ≤ innerQ (inputVectors basis index) (inputVectors basis index) := squaredNorm_le _ index
      _ ≤ (dimension : ℚ)*((2 : ℚ)^height)^2 := hcolumn
      _ ≤ ((2 : ℚ)^dimension)^2*((2 : ℚ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimensionSquare (sq_nonneg _)
      _ = _ := by rw [pow_add,mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsquare)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule24

/- Helper module Solutions.RegevBridgeRationalDenominator. -/
section P2MDyadicModule25

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalDenominator

/-- Any nonzero integral clearing denominator is divisible by the canonical
positive denominator of the rational number. -/
theorem den_dvd {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    (r.den : ℤ) ∣ D := by
  have hDQ : (D : ℚ)≠0 := by exact_mod_cast hD
  have hr : r=(N : ℚ)/(D : ℚ) := (eq_div_iff hDQ).mpr (by simpa only [mul_comm] using h)
  rw [hr]
  simpa only [Rat.divInt_eq_div] using Rat.den_dvd N D

/-- Canonical denominators never exceed any nonzero integral clearing denominator. -/
theorem den_le_natAbs {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    r.den≤D.natAbs := by
  have hd := den_dvd hD h
  have hn : r.den ∣ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hn

/-- Clearing-denominator bounds control the canonical numerator as well. -/
theorem num_bound_rat {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    |(r.num : ℚ)| ≤ |(D : ℚ)| * |r| := by
  have hd : (r.den : ℚ) ≤ |(D : ℚ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (Nat.cast_le (α := ℚ)).mpr (den_le_natAbs hD h)
  calc
    |(r.num : ℚ)|=|(r.den : ℚ)*r| := congrArg abs (Rat.den_mul_eq_num r).symm
    _ = (r.den : ℚ)*|r| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- A magnitude bound and clearing-denominator bound yield a natural bound
on both stored rational integer fields. -/
theorem fields_bound {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N)
    (M : ℕ) (hM : |r|≤M) : r.den≤D.natAbs ∧ r.num.natAbs≤D.natAbs*M := by
  refine ⟨den_le_natAbs hD h,?_⟩
  have hn := (num_bound_rat hD h).trans (mul_le_mul_of_nonneg_left hM (abs_nonneg _))
  have hn' : (r.num.natAbs : ℚ) ≤ ((D.natAbs*M : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs] using hn
  exact_mod_cast hn'

end InfoLossLAR.WorstCase.RationalDenominator

end P2MDyadicModule25

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule26

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

/-- A fixed polynomial in the dimension and input entry height controls
every reduced cached rational coordinate. -/
def coordinateHeight (dimension height : ℕ) : ℕ :=
  (2*dimension+2*height)*dimension+dimension+height

noncomputable section

/-- Canonical numerator and denominator sizes are polynomial, using the
actual integer Gram determinant rather than an arithmetic-operation count. -/
theorem orthogonal_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    HeightBound (orthogonal (inputVectors basis) index row) (coordinateHeight dimension height) := by
  have hnonzero := prefixGram_det_ne_zero basis hdet index.val index.isLt.le
  have hvector := gram_determinant_scales_orthogonal basis index
  have hcoordinate := congrArg (fun vector : QVector dimension => vector row) hvector
  simp only [Pi.smul_apply,smul_eq_mul] at hcoordinate
  have habs := orthogonal_coordinate_abs_bound basis height hentries index row
  have hM : |orthogonal (inputVectors basis) index row| ≤ ((2^(dimension+height) : ℕ) : ℚ) := by
    exact_mod_cast habs
  obtain ⟨hden,hnum⟩ := RationalDenominator.fields_bound hnonzero hcoordinate (2^(dimension+height)) hM
  have hD : (prefixGram basis index.val index.isLt.le).det.natAbs ≤
      2^((2*dimension+2*height)*dimension) := by
    have h := prefixGram_det_binary_bound basis index.val index.isLt.le height hentries
    have hcast : (((prefixGram basis index.val index.isLt.le).det.natAbs : ℕ) : ℤ) ≤
        (2 : ℤ)^((2*dimension+2*height)*dimension) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hcast
  constructor
  · apply hnum.trans
    apply (Nat.mul_le_mul_right (2^(dimension+height)) hD).trans_eq
    rw [←pow_add]
    congr 1
    unfold coordinateHeight
    omega
  · apply (hden.trans hD).trans
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by unfold coordinateHeight;omega)

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

/-- Every materialized prefix consists of the very same final cached
orthogonal vectors, so all prefix state encodings share one height bound. -/
theorem cache_prefix_eq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    cache vectors steps=List.ofFn (fun index : Fin steps => orthogonal vectors (Fin.castLE hsteps index)) := by
  apply (List.map_injective_iff.mpr realVec_injective)
  rw [cache_real vectors steps hsteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (orthogonal_real vectors _).symm

theorem cache_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) (vector : QVector dimension)
    (membership : vector ∈ cache (inputVectors basis) steps) (row : Fin dimension) :
    HeightBound (vector row) (coordinateHeight dimension height) := by
  rw [cache_prefix_eq _ steps hsteps] at membership
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp membership
  exact orthogonal_coordinate_height basis hdet height hentries _ row

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule26

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule27

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Total native rational list dot product; malformed lengths truncate. -/
def dot (input : List ℚ × List ℚ) : ℚ :=
  ((input.1.zip input.2).map (fun pair => pair.1*pair.2)).sum

@[fun_prop] theorem dot_poly : Poly dot := by unfold dot;fun_prop

def projectionEntry (input : (List ℚ × List ℚ) × ℕ) : ℚ :=
  dot (input.1.1,input.1.2)/dot (input.1.1,input.1.1)*input.1.1[input.2]?.getD 0

@[fun_prop] theorem projectionEntry_poly : Poly projectionEntry := by unfold projectionEntry;fun_prop

def rowValue (input : (List (List ℚ) × List ℚ) × ℕ) : ℚ :=
  input.1.2[input.2]?.getD 0-
    (input.1.1.map (fun previous => projectionEntry ((previous,input.1.2),input.2))).sum

@[fun_prop] theorem rowValue_poly : Poly rowValue := by unfold rowValue;fun_prop

/-- One native materialized Gram--Schmidt step uses its original current
column throughout and stores the complete new rational vector. -/
def orthogonalStep (input : List (List ℚ) × List ℚ) : List ℚ :=
  (List.range input.2.length).map (fun row => rowValue (input,row))

@[fun_prop] theorem orthogonalStep_poly : Poly orthogonalStep := by
  have hindices : Poly (fun input : List (List ℚ) × List ℚ => List.range input.2.length) :=
    Poly.comp (f:=fun values : List ℚ => List.range values.length) (g:=Prod.snd) Poly.list_indices Poly.snd
  unfold orthogonalStep
  exact Poly.list_map rowValue_poly hindices

/-- Unary size reflection materializes the exact actual binary encoding
length; it never enumerates a Gaussian window or a numerical magnitude. -/
def rationalTicks (value : ℚ) : List Unit :=
  List.replicate 7 ()++(value.num.natAbs.bits.flatMap (fun _ => [(),()]))++
    value.den.bits.map (fun _ => ())

@[fun_prop] theorem rationalTicks_poly : Poly rationalTicks := by unfold rationalTicks;fun_prop

def vectorTicks (vector : List ℚ) : List Unit :=
  vector.flatMap (fun value => rationalTicks value++rationalTicks value++[()])

@[fun_prop] theorem vectorTicks_poly : Poly vectorTicks := by unfold vectorTicks;fun_prop

def matrixTicks (matrix : List (List ℚ)) : List Unit :=
  matrix.flatMap (fun vector => vectorTicks vector++vectorTicks vector++[()])

@[fun_prop] theorem matrixTicks_poly : Poly matrixTicks := by unfold matrixTicks;fun_prop

theorem rationalTicks_length (value : ℚ) : (rationalTicks value).length=(Ratio.encode value).length := by
  rw [Ratio.encode_length]
  simp only [rationalTicks,List.length_append,List.length_replicate,List.length_flatMap,
    List.map_const',List.sum_replicate,List.length_cons,List.length_nil,nsmul_eq_mul,Nat.cast_id]
  omega

theorem vectorTicks_length (vector : List ℚ) :
    (vectorTicks vector).length=(encodeList Ratio.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [vectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      rationalTicks_length,EncodedList.cons_length] at *
    omega

theorem matrixTicks_length (matrix : List (List ℚ)) :
    (matrixTicks matrix).length=(encodeList (encodeList Ratio.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [matrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      vectorTicks_length,EncodedList.cons_length] at *
    omega

/-- Every intermediate cache is size-guarded, giving an unconditional
polynomial-time loop on arbitrary encodings. Valid matrix correctness will
be discharged using the independently proved integer-Gram height bound. -/
def cacheStep (state : List Unit × List (List ℚ)) (current : List ℚ) : List Unit × List (List ℚ) :=
  let next := state.2++[orthogonalStep (state.2,current)]
  (state.1,if (matrixTicks next).length ≤ state.1.length then next else [])

@[fun_prop] theorem cacheStep_poly : Poly (fun input : (List Unit × List (List ℚ)) × List ℚ =>
    cacheStep input.1 input.2) := by unfold cacheStep;fun_prop

theorem ticks_encoding_length (ticks : List Unit) : (enc ticks).length=ticks.length := by
  change (encodeList (fun _ : Unit => []) ticks).length=ticks.length
  induction ticks with
  | nil => rfl
  | cons head tail ih => simp only [EncodedList.cons_length,List.length_nil,List.length_cons,ih];omega

theorem state_encoding_length (state : List Unit × List (List ℚ)) :
    (enc state).length=2*state.1.length+1+(encodeList (encodeList Ratio.encode) state.2).length := by
  change (encodePair (encodeList enc) (encodeList (encodeList Ratio.encode)) state).length=_
  rw [encodePair_length]
  change 2*(enc state.1).length+1+_= _
  rw [ticks_encoding_length]

theorem cacheStep_length (state : List Unit × List (List ℚ)) (current : List ℚ) :
    (enc (cacheStep state current)).length ≤ 3*state.1.length+1 := by
  rw [state_encoding_length]
  unfold cacheStep
  simp only
  split_ifs with h
  · rw [matrixTicks_length] at h
    omega
  · change 2*state.1.length+1+0 ≤ _
    omega

theorem fold_encoding_length (columns : List (List ℚ)) (state : List Unit × List (List ℚ)) :
    (enc (columns.foldl cacheStep state)).length ≤ max (enc state).length (3*state.1.length+1) := by
  induction columns generalizing state with
  | nil => simp only [List.foldl_nil];exact le_max_left _ _
  | cons current rest ih =>
    rw [List.foldl_cons]
    apply (ih (cacheStep state current)).trans
    apply max_le
    · exact (cacheStep_length state current).trans (le_max_right _ _)
    · exact le_max_right _ _

theorem cacheFold_bound (columns : List (List ℚ)) (state : List Unit × List (List ℚ))
    (pre suffix : List (List ℚ)) (_hsplit : columns=pre++suffix) :
    (enc (pre.foldl cacheStep state)).length ≤
      (3*Polynomial.X+1 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length := by
  let inputLength := (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length
  have hstate : (enc state).length ≤ inputLength := by
    dsimp [inputLength]
    rw [encodePair_length]
    change (enc state).length ≤ 2*(encodeList (enc : List ℚ → List Bool) columns).length+1+(enc state).length
    omega
  have hticks : state.1.length ≤ inputLength := by
    rw [state_encoding_length] at hstate
    omega
  apply (fold_encoding_length pre state).trans
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change max _ _ ≤ 3*inputLength+1
  omega

@[fun_prop] theorem cacheFold_poly : Poly (fun input : List (List ℚ) × (List Unit × List (List ℚ)) =>
    input.1.foldl cacheStep input.2) :=
  ⟨cacheStep_poly.program.listFold [] (3*Polynomial.X+1) cacheFold_bound⟩

/-- Actual guarded list cache program. The guard's complete runtime bound
holds for every encoded input, including malformed or singular matrices. -/
def cached (input : List (List ℚ) × List Unit) : List (List ℚ) :=
  (input.1.foldl cacheStep (input.2,[])).2

@[fun_prop] theorem cached_poly : Poly cached := by
  have hf := Poly.comp cacheFold_poly
    (show Poly (fun input : List (List ℚ) × List Unit => (input.1,(input.2,([] : List (List ℚ))))) by fun_prop)
  unfold cached
  exact Poly.comp Poly.snd hf

theorem dot_ofFn {dimension : ℕ} (first second : QVector dimension) :
    dot (List.ofFn first,List.ofFn second)=innerQ first second := by
  induction dimension with
  | zero => simp [dot,innerQ]
  | succ dimension ih =>
    simp only [dot,List.ofFn_succ,List.zip_cons_cons,List.map_cons,List.sum_cons]
    change first 0*second 0+dot (List.ofFn (Fin.tail first),List.ofFn (Fin.tail second))= _
    rw [ih]
    simp only [innerQ,Fin.sum_univ_succ,Fin.tail_def]

theorem vector_list_sum_apply {dimension : ℕ} (vectors : List (QVector dimension)) (index : Fin dimension) :
    vectors.sum index=(vectors.map (fun vector => vector index)).sum := by
  induction vectors with
  | nil => rfl
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,Pi.add_apply,ih]

theorem orthogonalStep_ofFn {dimension : ℕ} (previous : List (QVector dimension))
    (current : QVector dimension) :
    orthogonalStep (previous.map List.ofFn,List.ofFn current)=
      List.ofFn (RationalGramSchmidt.orthogonalStep previous current) := by
  apply List.ext_getElem
  · simp only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < dimension := by
      simpa only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [orthogonalStep,List.length_ofFn,List.getElem_map,List.getElem_range,rowValue,
      List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some,List.map_map,Function.comp_def,
      projectionEntry,dot_ofFn,List.getElem_ofFn]
    simp only [RationalGramSchmidt.orthogonalStep,Pi.sub_apply,vector_list_sum_apply,List.map_map,
      Function.comp_def,projection,Pi.smul_apply,smul_eq_mul]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule27

/- Helper module Solutions.RegevBridgeRationalGramSchmidtCacheBudget. -/
section P2MDyadicModule28

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem encoded_list_length_bound {Value : Type} (encoding : Value → List Bool)
    (values : List Value) (bound : ℕ) (hbound : ∀ value ∈ values,(encoding value).length ≤ bound) :
    (encodeList encoding values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp only [EncodedList.nil,List.length_nil,zero_mul,le_refl]
  | cons head tail ih =>
    rw [EncodedList.cons_length,List.length_cons]
    have hhead := hbound head (by simp)
    have htail := ih (fun value membership => hbound value (by simp [membership]))
    nlinarith

theorem rational_encoding_height {value : ℚ} {height : ℕ} (hvalue : HeightBound value height) :
    (Ratio.encode value).length ≤ 3*height+10 := by
  apply Ratio.length_height
  constructor
  · have h := (Nat.cast_le (α:=ℤ)).mpr hvalue.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h
  · exact_mod_cast hvalue.2

theorem vector_encoding_height {dimension : ℕ} (vector : QVector dimension) (height : ℕ)
    (hvector : ∀ row,HeightBound (vector row) height) :
    (encodeList Ratio.encode (List.ofFn vector)).length ≤ dimension*(6*height+21) := by
  have h := encoded_list_length_bound Ratio.encode (List.ofFn vector) (3*height+10) (by
    intro value membership
    obtain ⟨row,rfl⟩ := List.mem_ofFn.mp membership
    exact rational_encoding_height (hvector row))
  simpa only [List.length_ofFn,show 2*(3*height+10)+1=6*height+21 by omega] using h

def cacheEncodingBound (dimension height : ℕ) : ℕ :=
  dimension*(2*dimension*(6*coordinateHeight dimension height+21)+1)

/-- The original determinant-derived height bound controls every complete
native cache-prefix encoding by one public polynomial. -/
theorem cache_encoding_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (encodeList (encodeList Ratio.encode) ((cache (inputVectors basis) steps).map List.ofFn)).length ≤
      cacheEncodingBound dimension height := by
  have h := encoded_list_length_bound (encodeList Ratio.encode)
    ((cache (inputVectors basis) steps).map List.ofFn) (dimension*(6*coordinateHeight dimension height+21)) (by
      intro vector membership
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp membership
      exact vector_encoding_height source _ (cache_coordinate_height basis hdet height hentries steps hsteps source hsource))
  rw [List.length_map,cache_length] at h
  apply h.trans
  unfold cacheEncodingBound
  calc
    steps*(2*(dimension*(6*coordinateHeight dimension height+21))+1) ≤
        dimension*(2*(dimension*(6*coordinateHeight dimension height+21))+1) := Nat.mul_le_mul_right _ hsteps
    _ = _ := by ring

/-- Prefix refinement is proved for the actual guarded list loop. Its
encoding bound is a local arithmetic invariant, discharged below from the
original integer matrix's determinant-derived size bounds. -/
theorem cacheFold_ofFn {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (ticks : List Unit)
    (hbudget : ∀ steps,steps ≤ count →
      (encodeList (encodeList Ratio.encode) ((cache vectors steps).map List.ofFn)).length ≤ ticks.length)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hsteps index)))).foldl cacheStep (ticks,[])=
      (ticks,(cache vectors steps).map List.ofFn) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps < count := by omega
    rw [List.ofFn_succ_last,List.foldl_append]
    change List.foldl cacheStep
      ((List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hprevious index)))).foldl cacheStep (ticks,[]))
      [List.ofFn (vectors ⟨steps,hstep⟩)] = _
    rw [ih hprevious,List.foldl_cons,List.foldl_nil]
    have hnext : (cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))]=
        (cache vectors (steps+1)).map List.ofFn := by
      rw [orthogonalStep_ofFn,cache,List.map_append,List.map_singleton,dif_pos hstep]
    have hguard : (matrixTicks ((cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))])).length ≤ ticks.length := by
      rw [hnext,matrixTicks_length]
      exact hbudget (steps+1) hsteps
    simp only [cacheStep,hguard,if_true]
    exact congrArg (fun matrix => (ticks,matrix)) hnext

/-- For every nonsingular input basis, the actual native cache agrees
exactly with rational Gram--Schmidt once supplied the public polynomial
encoding budget. No oracle or assumed GS algorithm appears. -/
theorem cached_integer_basis {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (ticks : List Unit) (hticks : cacheEncodingBound dimension height ≤ ticks.length) :
    cached (List.ofFn (fun index => List.ofFn (inputVectors basis index)),ticks)=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  have h := cacheFold_ofFn (inputVectors basis) ticks (fun steps hsteps =>
    (cache_encoding_bound basis hdet height hentries steps hsteps).trans hticks) dimension (le_refl dimension)
  change (List.ofFn (fun index : Fin dimension => List.ofFn (inputVectors basis index))).foldl cacheStep (ticks,[])=_ at h
  exact congrArg Prod.snd h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule28

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule29

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

def integerTicks (value : ℤ) : List Unit := List.replicate 3 ()++value.natAbs.bits.map (fun _ => ())

@[fun_prop] theorem integerTicks_poly : Poly integerTicks := by unfold integerTicks;fun_prop

def integerVectorTicks (vector : List ℤ) : List Unit :=
  vector.flatMap (fun value => integerTicks value++integerTicks value++[()])

@[fun_prop] theorem integerVectorTicks_poly : Poly integerVectorTicks := by unfold integerVectorTicks;fun_prop

def integerMatrixTicks (matrix : List (List ℤ)) : List Unit :=
  matrix.flatMap (fun vector => integerVectorTicks vector++integerVectorTicks vector++[()])

@[fun_prop] theorem integerMatrixTicks_poly : Poly integerMatrixTicks := by unfold integerMatrixTicks;fun_prop

/-- The guard budget is generated in unary polynomial size from the
actual binary input length, not from an exponentially large entry value. -/
def inputBudget (input : List (List ℤ)) : List Unit :=
  let slots := integerMatrixTicks input++[()]
  slots.flatMap (fun _ => slots.flatMap (fun _ => slots.flatMap
    (fun _ => slots.flatMap (fun _ => List.replicate 128 ()))))

@[fun_prop] theorem inputBudget_poly : Poly inputBudget := by unfold inputBudget;fun_prop

def rationalColumn (column : List ℤ) : List ℚ := column.map (fun value : ℤ => (value : ℚ))

@[fun_prop] theorem rationalColumn_poly : Poly rationalColumn := by
  unfold rationalColumn
  exact Poly.list_map (show Poly (fun input : List ℤ × ℤ => (input.2 : ℚ)) by fun_prop) Poly.identity

def rationalColumns (input : List (List ℤ)) : List (List ℚ) := input.map rationalColumn

@[fun_prop] theorem rationalColumns_poly : Poly rationalColumns := by
  unfold rationalColumns
  exact Poly.list_map (Poly.comp rationalColumn_poly Poly.snd) Poly.identity

/-- Complete unconditional native cached orthogonalization of original
integer input columns, with all guards and loop sizes computed publicly. -/
def inputCache (input : List (List ℤ)) : List (List ℚ) := cached (rationalColumns input,inputBudget input)

@[fun_prop] theorem inputCache_poly : Poly inputCache := by unfold inputCache;fun_prop

theorem integerTicks_length (value : ℤ) : (integerTicks value).length=(Signed.encode value).length := by
  simp only [integerTicks,List.length_append,List.length_replicate,List.length_map,Signed.encode_length]

theorem integerVectorTicks_length (vector : List ℤ) :
    (integerVectorTicks vector).length=(encodeList Signed.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerVectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerTicks_length,EncodedList.cons_length] at *
    omega

theorem integerMatrixTicks_length (matrix : List (List ℤ)) :
    (integerMatrixTicks matrix).length=(encodeList (encodeList Signed.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerMatrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerVectorTicks_length,EncodedList.cons_length] at *
    omega

theorem inputBudget_length (matrix : List (List ℤ)) :
    (inputBudget matrix).length=128*((integerMatrixTicks matrix).length+1)^4 := by
  simp only [inputBudget,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    List.length_append,List.length_singleton,nsmul_eq_mul,Nat.cast_id]
  ring

def transposeColumn (input : List (List ℤ) × ℕ) : List ℤ :=
  input.1.map (fun row => row[input.2]?.getD 0)

@[fun_prop] theorem transposeColumn_poly : Poly transposeColumn := by unfold transposeColumn;fun_prop

def transpose (input : List (List ℤ)) : List (List ℤ) :=
  (List.range input.length).map (fun column => transposeColumn (input,column))

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  exact Poly.list_map transposeColumn_poly Poly.list_indices

/-- Actual row-encoded matrix input is transposed by a native program
before the cached column orthogonalization. -/
def basisCache (input : List (List ℤ)) : List (List ℚ) := inputCache (transpose input)

@[fun_prop] theorem basisCache_poly : Poly basisCache := by unfold basisCache;fun_prop

noncomputable section

/-- Coarse fixed polynomial suitable for unconditional guarded runtime. -/
theorem cacheEncodingBound_coarse (dimension height length : ℕ)
    (hdimension : dimension ≤ length) (hheight : height ≤ length) :
    cacheEncodingBound dimension height ≤ 128*(length+1)^4 := by
  have hlinear : length ≤ (length+1)^2 := by nlinarith
  have hcross : height*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hheight hdimension
      _ ≤ _ := by nlinarith
  have hsquare : dimension*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hdimension hdimension
      _ ≤ _ := by nlinarith
  have hcache : coordinateHeight dimension height ≤ 6*(length+1)^2 := by
    unfold coordinateHeight
    nlinarith
  unfold cacheEncodingBound
  calc
    _ ≤ (length+1)*(2*(length+1)*(6*(6*(length+1)^2)+21)+1) := by gcongr <;> omega
    _ ≤ _ := by
      have hpowerOne := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 1 ≤ 4 by omega)
      have hpowerTwo := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 2 ≤ 4 by omega)
      simp only [pow_one] at hpowerOne
      nlinarith

def inputColumns {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : List (List ℤ) :=
  List.ofFn (fun column => List.ofFn (fun row => basis row column))

theorem inputColumns_dimension {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    dimension ≤ (integerMatrixTicks (inputColumns basis)).length := by
  rw [integerMatrixTicks_length]
  have h := EncodedList.length_le (encodeList Signed.encode) (inputColumns basis)
  simpa only [inputColumns,List.length_ofFn] using h

theorem inputColumns_entry_height {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (row column : Fin dimension) :
    |basis row column| ≤ (2 : ℤ)^(integerMatrixTicks (inputColumns basis)).length := by
  have hcolumn : List.ofFn (fun position => basis position column) ∈ inputColumns basis :=
    List.mem_ofFn.mpr ⟨column,rfl⟩
  have hentry : basis row column ∈ List.ofFn (fun position => basis position column) :=
    List.mem_ofFn.mpr ⟨row,rfl⟩
  have hcolumnSize := EncodedList.member_length (encodeList Signed.encode) (inputColumns basis) _ hcolumn
  have hentrySize := EncodedList.member_length Signed.encode _ _ hentry
  have hbits : (basis row column).natAbs.bits.length ≤ (integerMatrixTicks (inputColumns basis)).length := by
    rw [integerMatrixTicks_length]
    rw [Signed.encode_length] at hentrySize
    omega
  have hvalue := (NatBinary.le_two_pow_length (basis row column).natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  have hcast := (Nat.cast_le (α:=ℤ)).mpr hvalue
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using hcast

theorem rationalColumns_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    rationalColumns (inputColumns basis)=List.ofFn (fun index => List.ofFn (inputVectors basis index)) := by
  simp only [rationalColumns,rationalColumn,inputColumns,List.map_ofFn,Function.comp_def]
  rfl

/-- The fully generated binary-input native cache exactly returns the
original nonsingular integer basis's rational orthogonalization. Every
size guard is discharged from the actual input encoding itself. -/
theorem inputCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    inputCache (inputColumns basis)=(cache (inputVectors basis) dimension).map List.ofFn := by
  unfold inputCache
  rw [rationalColumns_input]
  apply cached_integer_basis basis hdet (integerMatrixTicks (inputColumns basis)).length
    (inputColumns_entry_height basis)
  rw [inputBudget_length]
  exact cacheEncodingBound_coarse dimension _ _ (inputColumns_dimension basis) le_rfl

theorem transpose_input_rows {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    transpose (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=inputColumns basis := by
  apply List.ext_getElem
  · simp only [transpose,List.length_map,List.length_range,List.length_ofFn,inputColumns]
  · intro column hfirst hsecond
    have hcolumn : column < dimension := by
      simpa only [transpose,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [transpose,List.length_ofFn,List.getElem_map,List.getElem_range,transposeColumn,
      List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hcolumn,↓reduceDIte,Option.getD_some,
      inputColumns,List.getElem_ofFn]

/-- End-to-end exact native GS caching for the target's original row-major
integer matrix convention, with an unconditional polynomial-time program. -/
theorem basisCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    basisCache (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  rw [basisCache,transpose_input_rows,inputCache_correct basis hdet]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule29

/- Helper module Solutions.RegevBridgeRationalInverseAlgebra. -/
section P2MDyadicModule30

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

noncomputable section

/-- Analytical Cramer specification only. The native implementation below
will use the cached rational orthogonalization and reverse substitution. -/
def dualVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : QVector n :=
  fun row => (Matrix.cramer B.transpose (Pi.single i 1) row : ℚ)/(B.det : ℚ)

theorem dualVector_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (i k : Fin n) : innerQ (dualVector B i) (inputVectors B k)=if k=i then 1 else 0 := by
  have hD : (B.det : ℚ)≠0 := by exact_mod_cast hdet
  have hh:=congrFun (Matrix.mulVec_cramer B.transpose (Pi.single i 1)) k
  simp only [Matrix.mulVec,dotProduct,Matrix.det_transpose,Pi.smul_apply,smul_eq_mul,
    Matrix.transpose_apply,Pi.single_apply] at hh
  have hcast : (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))=
      (B.det : ℚ)*(if k=i then 1 else 0) := by exact_mod_cast hh
  calc
    _ = (∑ row,(B row k : ℚ)*(Matrix.cramer B.transpose (Pi.single i 1) row : ℚ))/(B.det : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro row _
      simp only [innerQ,dualVector,inputVectors]
      ring
    _ = ((B.det : ℚ)*(if k=i then 1 else 0))/(B.det : ℚ) := by rw [hcast]
    _ = _ := by split_ifs <;> simp [hD]

/-- Pairings with the original input columns determine the entire real
vector, using the actual Euclidean dual basis. -/
theorem real_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : IntegerBasis.Space (dimension:=n))
    (h : ∀ k,inner ℝ x (IntegerBasis.realBasis B hdet k)=inner ℝ y (IntegerBasis.realBasis B hdet k)) : x=y := by
  apply (IntegerBasis.dualRealBasis B hdet).ext_elem
  intro k
  change ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
    (IntegerBasis.realBasis B hdet)).repr x) k=
    ((LinearMap.BilinForm.dualBasis (innerₗ _) IntegerBasis.inner_nondegenerate
      (IntegerBasis.realBasis B hdet)).repr y) k
  rw [LinearMap.BilinForm.dualBasis_repr_apply,LinearMap.BilinForm.dualBasis_repr_apply]
  exact h k

theorem rational_pairings_unique {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (x y : QVector n) (h : ∀ k,innerQ x (inputVectors B k)=innerQ y (inputVectors B k)) : x=y := by
  apply realVec_injective
  apply real_pairings_unique B hdet
  intro k
  rw [←inputVectors_real B hdet k,←innerQ_real,←innerQ_real,h k]

/-- A coarse binary determinant bound has polynomial exponent in dimension
and original integer entry height. -/
theorem determinant_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) : |B.det|≤(2 : ℤ)^((n+H)*n) := by
  have hdim : (n : ℤ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hfac : (n.factorial : ℤ)≤2^(n*n) := by
    calc
      _ ≤ (n : ℤ)^n := by exact_mod_cast Nat.factorial_le_pow n
      _ ≤ ((2 : ℤ)^n)^n := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim _
      _ = _ := by rw [←pow_mul]
  have hh:=Matrix.det_le (abv:=AbsoluteValue.abs) hentries
  have hd : |B.det|≤(n.factorial : ℤ)*((2 : ℤ)^H)^n := by
    simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using hh
  calc
    _ ≤ (n.factorial : ℤ)*((2 : ℤ)^H)^n := hd
    _ ≤ (2 : ℤ)^(n*n)*((2 : ℤ)^H)^n := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = _ := by rw [←pow_mul,←pow_add];congr 1;ring

theorem cramer_binary_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    |Matrix.cramer B.transpose (Pi.single i 1) row|≤(2 : ℤ)^((n+H)*n) := by
  rw [Matrix.cramer_apply]
  apply determinant_binary_bound _ H
  intro r c
  simp only [Matrix.updateCol_apply,Matrix.transpose_apply]
  split_ifs
  · simp only [Pi.single_apply]
    split_ifs <;> simp
    exact one_le_pow₀ (by norm_num : (1 : ℤ)≤2)
  · exact hentries c r

def dualHeight (n H : ℕ) : ℕ := 2*((n+H)*n)

theorem dualVector_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H) (i row : Fin n) :
    HeightBound (dualVector B i row) (dualHeight n H) := by
  have hnum : (Matrix.cramer B.transpose (Pi.single i 1) row).natAbs≤2^((n+H)*n) := by
    have hh : ((Matrix.cramer B.transpose (Pi.single i 1) row).natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using cramer_binary_bound B H hentries i row
    exact_mod_cast hh
  have hden : B.det.natAbs≤2^((n+H)*n) := by
    have hh : (B.det.natAbs : ℤ)≤(2 : ℤ)^((n+H)*n) := by
      simpa only [Int.natCast_natAbs] using determinant_binary_bound B H hentries
    exact_mod_cast hh
  have hh:=(HeightBound.of_int hnum).div (HeightBound.of_int hden)
  simpa only [dualVector,dualHeight,two_mul] using hh

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule30

/- Helper module Solutions.RegevBridgeRationalInverseRecurrence. -/
section P2MDyadicModule31

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse

open RationalGramSchmidt AFT.RationalNumerics

open scoped BigOperators

@[simp] theorem innerQ_sub_left {n : ℕ} (x y z : QVector n) :
    innerQ (x-y) z=innerQ x z-innerQ y z := by simp [innerQ,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem innerQ_smul_left {n : ℕ} (a : ℚ) (x y : QVector n) :
    innerQ (a • x) y=a*innerQ x y := by simp [innerQ,Finset.mul_sum,mul_assoc]

theorem innerQ_sum_left {n : ℕ} {J : Type*} (s : Finset J) (x : J → QVector n) (y : QVector n) :
    innerQ (∑ j∈s,x j) y=∑ j∈s,innerQ (x j) y := by
  simp only [innerQ,Finset.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One reverse triangular substitution step. Its only arithmetic operands
are the cached original rational orthogonalization and future dual columns. -/
def dualStep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (cache : Fin n → QVector n) (i : Fin n) : QVector n :=
  (squaredNorm (inputVectors B) i)⁻¹ • orthogonal (inputVectors B) i-
    ∑ j∈Finset.Ioi i,upper (inputVectors B) i j • cache j

noncomputable section

theorem dualStep_pairing {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i k : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) :
    innerQ (dualStep B cache i) (inputVectors B k)=if k=i then 1 else 0 := by
  rw [dualStep,innerQ_sub_left,innerQ_smul_left,innerQ_sum_left]
  simp only [innerQ_smul_left]
  have hfirst : (squaredNorm (inputVectors B) i)⁻¹*innerQ (orthogonal (inputVectors B) i) (inputVectors B k)=
      upper (inputVectors B) i k := by unfold upper;ring
  rw [hfirst]
  have hsum : (∑ j∈Finset.Ioi i,upper (inputVectors B) i j*innerQ (cache j) (inputVectors B k))=
      if i< k then upper (inputVectors B) i k else 0 := by
    calc
      _ = ∑ j∈Finset.Ioi i,if k=j then upper (inputVectors B) i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcache j (Finset.mem_Ioi.mp hj),dualVector_pairing B hdet]
        split_ifs <;> simp
      _ = _ := by simp only [Finset.sum_ite_eq,Finset.mem_Ioi]
  rw [hsum]
  by_cases he : k=i
  · subst k
    simp [upper_diagonal _ (inputVectors_independent B hdet)]
  · by_cases hi : i< k
    · simp [hi,he]
    · have hk : k< i := lt_of_le_of_ne (le_of_not_gt hi) he
      rw [upper_triangular _ i k hk]
      simp [hi,he]

theorem dualStep_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (cache : Fin n → QVector n) (i : Fin n)
    (hcache : ∀ j,i< j → cache j=dualVector B j) : dualStep B cache i=dualVector B i := by
  apply rational_pairings_unique B hdet
  intro k
  rw [dualStep_pairing B hdet cache i k hcache,dualVector_pairing B hdet]

/-- A complete matrix cache is updated from the last column backwards.
Every completed column is already a final original-input dual column. -/
def dualCache {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → QVector n
  | 0 => fun _ => 0
  | steps+1 =>
      let previous :=dualCache B steps
      if h : steps< n then
        let i : Fin n :=⟨n-1-steps,by omega⟩
        Function.update previous i (dualStep B previous i)
      else previous

theorem dualCache_formula {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (steps : ℕ) (hsteps : steps≤ n) (j : Fin n) :
    dualCache B steps j=if n-steps≤ j.val then dualVector B j else 0 := by
  induction steps generalizing j with
  | zero =>
    have hj : ¬n≤ j.val := by omega
    simp [dualCache,hj]
  | succ steps ih =>
    have hs : steps< n := by omega
    let i : Fin n :=⟨n-1-steps,by omega⟩
    have hf : ∀ k,i< k → dualCache B steps k=dualVector B k := by
      intro k hk
      rw [ih (by omega) k]
      have ht : n-steps≤ k.val := by change i.val< k.val at hk;dsimp [i] at hk;omega
      simp only [if_pos ht]
    have he:=dualStep_correct B hdet (dualCache B steps) i hf
    change (if h : steps< n then Function.update (dualCache B steps)
      (⟨n-1-steps,by omega⟩ : Fin n) (dualStep B (dualCache B steps) ⟨n-1-steps,by omega⟩) else dualCache B steps) j=_
    rw [dif_pos hs]
    change Function.update (dualCache B steps) i (dualStep B (dualCache B steps) i) j=_
    rw [he]
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      have ht : n-(steps+1)≤ i.val := by dsimp [i];omega
      simp only [if_pos ht]
    · rw [Function.update_of_ne hj,ih (by omega) j]
      have hv : j.val≠n-1-steps := by intro h;apply hj;exact Fin.ext h
      have ht : (n-steps≤ j.val)=(n-(steps+1)≤ j.val) := propext (by omega)
      simp only [ht]

theorem dualCache_complete {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    dualCache B n=dualVector B := by
  funext j
  rw [dualCache_formula B hdet n (le_refl n)]
  simp

theorem dualCache_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤(2 : ℤ)^H)
    (steps : ℕ) (hs : steps≤ n) (j row : Fin n) :
    HeightBound (dualCache B steps j row) (coordinateHeight n H) := by
  rw [dualCache_formula B hdet steps hs]
  split_ifs
  · exact (dualVector_height B H hentries j row).mono (by unfold dualHeight coordinateHeight;nlinarith)
  · exact HeightBound.zero.mono (Nat.zero_le _)

end

end InfoLossLAR.WorstCase.RationalInverse

end P2MDyadicModule31

/- Helper module Solutions.RegevBridgeRationalInverseNative. -/
section P2MDyadicModule32

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

abbrev Context := List (List ℚ) × List (List ℚ)

abbrev State := Context × (List Unit × List (List ℚ))

/-- One rational summand of reverse triangular substitution. -/
def term (input : (((Context × List (List ℚ)) × ℕ) × ℕ) × ℕ) : ℚ :=
  let source := input.1
  let gs := source.1.1.1.2[source.1.2]?.getD []
  if source.1.2< input.2 then
    dot (gs,source.1.1.1.1[input.2]?.getD [])/dot (gs,gs)*
      (source.1.1.2[input.2]?.getD [])[source.2]?.getD 0 else 0

@[fun_prop] theorem term_poly : Poly term := by unfold term;fun_prop

/-- One entry uses only native rational operations and bounded index lists. -/
def entry (input : ((Context × List (List ℚ)) × ℕ) × ℕ) : ℚ :=
  let gs := input.1.1.1.2[input.1.2]?.getD []
  gs[input.2]?.getD 0/dot (gs,gs)-
    ((List.range input.1.1.1.1.length).map (fun j => term (input,j))).sum

@[fun_prop] theorem entry_poly : Poly entry := by
  have hi : Poly (fun input : ((Context × List (List ℚ)) × ℕ) × ℕ => List.range input.1.1.1.1.length) :=
    Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : ((Context × List (List ℚ)) × ℕ) × ℕ => input.1.1.1.1) Poly.list_indices (by fun_prop)
  have ht := Poly.list_map (f:=fun input j => term (input,j)) term_poly hi
  have hs := Poly.comp (show Poly (List.sum : List ℚ → ℚ) from ⟨PolyProgram.ratSum⟩) ht
  have hf : Poly (fun input : ((Context × List (List ℚ)) × ℕ) × ℕ =>
      let gs := input.1.1.1.2[input.1.2]?.getD []
      gs[input.2]?.getD 0/dot (gs,gs)) := by fun_prop
  unfold entry
  exact Poly.comp Poly.rat_sub (Poly.pair hf hs)

def column (input : (Context × List (List ℚ)) × ℕ) : List ℚ :=
  (List.range input.1.1.1.length).map (fun row => entry (input,row))

@[fun_prop] theorem column_poly : Poly column := by
  have hi : Poly (fun input : (Context × List (List ℚ)) × ℕ => List.range input.1.1.1.length) := by
    exact Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (Context × List (List ℚ)) × ℕ => input.1.1.1) Poly.list_indices (by fun_prop)
  unfold column
  exact Poly.list_map entry_poly hi

def replaceColumn (input : (List (List ℚ) × ℕ) × List ℚ) : List (List ℚ) :=
  (List.range input.1.1.length).map (fun j => if j=input.1.2 then input.2 else input.1.1[j]?.getD [])

@[fun_prop] theorem replaceColumn_poly : Poly replaceColumn := by
  have hi : Poly (fun input : (List (List ℚ) × ℕ) × List ℚ => List.range input.1.1.length) :=
    Poly.comp (f:=fun values : List (List ℚ) => List.range values.length)
      (g:=fun input : (List (List ℚ) × ℕ) × List ℚ => input.1.1) Poly.list_indices (by fun_prop)
  unfold replaceColumn
  exact Poly.list_map (by fun_prop) hi

/-- A public encoding-length guard bounds every fold state, including
malformed and singular inputs. Correctness proves that it never fires on
nonsingular original integer matrices. -/
def step (state : State) (counter : ℕ) : State :=
  let index := state.1.1.length-1-counter
  let next := replaceColumn ((state.2.2,index),column ((state.1,state.2.2),index))
  (state.1,(state.2.1,if (matrixTicks next).length≤ state.2.1.length then next else []))

@[fun_prop] theorem step_poly : Poly (fun input : State × ℕ => step input.1 input.2) := by
  unfold step
  fun_prop

theorem state_encoding_length (state : State) :
    (enc state).length=2*(enc state.1).length+2*state.2.1.length+2+
      (encodeList (encodeList Ratio.encode) state.2.2).length := by
  change (encodePair enc enc state).length=_
  rw [encodePair_length,RationalGramSchmidt.Native.state_encoding_length]
  omega

theorem step_length (state : State) (counter : ℕ) :
    (enc (step state counter)).length≤ 2*(enc state.1).length+3*state.2.1.length+2 := by
  rw [state_encoding_length]
  unfold step
  simp only
  split_ifs with h
  · rw [matrixTicks_length] at h
    omega
  · change 2*(enc state.1).length+2*state.2.1.length+2+0≤ _
    omega

theorem fold_encoding_length (counters : List ℕ) (state : State) :
    (enc (counters.foldl step state)).length≤
      max (enc state).length (2*(enc state.1).length+3*state.2.1.length+2) := by
  induction counters generalizing state with
  | nil => exact le_max_left _ _
  | cons counter rest ih =>
    rw [List.foldl_cons]
    apply (ih (step state counter)).trans
    apply max_le
    · exact (step_length state counter).trans (le_max_right _ _)
    · exact le_max_right _ _

theorem fold_bound (counters : List ℕ) (state : State) (pre suffix : List ℕ)
    (_hsplit : counters=pre++suffix) :
    (enc (pre.foldl step state)).length≤
      (3*Polynomial.X+2 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : ℕ → List Bool)) enc (counters,state)).length := by
  let inputLength := (encodePair (encodeList (enc : ℕ → List Bool)) enc (counters,state)).length
  have hs : (enc state).length≤ inputLength := by
    dsimp [inputLength]
    rw [encodePair_length]
    change (enc state).length≤ 2*(encodeList (enc : ℕ → List Bool) counters).length+1+(enc state).length
    omega
  have hc : 2*(enc state.1).length+2*state.2.1.length+2≤ inputLength := by
    rw [state_encoding_length] at hs
    omega
  apply (fold_encoding_length pre state).trans
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change max _ _≤ 3*inputLength+2
  omega

@[fun_prop] theorem fold_poly : Poly (fun input : List ℕ × State => input.1.foldl step input.2) :=
  ⟨step_poly.program.listFold 0 (3*Polynomial.X+2) fold_bound⟩

/-- The actual cache consumes the original row-major integer input. The
only preprocessing is the previously certified native orthogonalization. -/
def cached (input : List (List ℤ)) : List (List ℚ) :=
  let original := rationalColumns (transpose input)
  let gs := basisCache input
  let zeros := original.map (fun row => row.map (fun _ => (0 : ℚ)))
  ((List.range input.length).foldl step ((original,gs),(inputBudget input,zeros))).2.2

@[fun_prop] theorem cached_poly : Poly cached := by
  have hi : Poly (fun input : List (List ℤ) =>
      (List.range input.length,
        ((rationalColumns (transpose input),basisCache input),
          (inputBudget input,(rationalColumns (transpose input)).map (fun row => row.map (fun _ => (0 : ℚ))))))) := by
    fun_prop
  unfold cached
  exact Poly.comp (f:=fun state : State => state.2.2) (by fun_prop) (Poly.comp fold_poly hi)

def transposeRational (input : List (List ℚ)) : List (List ℚ) :=
  (List.range input.length).map (fun row => input.map (fun column => column[row]?.getD 0))

@[fun_prop] theorem transposeRational_poly : Poly transposeRational := by
  have hi : Poly (fun input : List (List ℚ) => List.range input.length) := Poly.list_indices
  unfold transposeRational
  exact Poly.list_map (by fun_prop) hi

/-- Native row-major output for the original integer matrix's inverse
transpose. No determinant, real dual-basis or arbitrary real oracle is
called by this program. -/
def current (input : List (List ℤ)) : List (List ℚ) := transposeRational (cached input)

@[fun_prop] theorem current_poly : Poly current := by unfold current;fun_prop

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule32

/- Helper module Solutions.RegevBridgeRationalInverseRefinement. -/
section P2MDyadicModule33

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

noncomputable section

def matrixOf {n : ℕ} (vectors : Fin n → QVector n) : List (List ℚ) :=
  List.ofFn (fun j => List.ofFn (vectors j))

def context {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Context :=
  (matrixOf (inputVectors B),matrixOf (orthogonal (inputVectors B)))

theorem term_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i row j : Fin n) :
    term ((((context B,matrixOf cache),i.val),row.val),j.val)=
      if i< j then upper (inputVectors B) i j*cache j row else 0 := by
  simp only [term,context,matrixOf,List.getElem?_ofFn,i.isLt,j.isLt,row.isLt,
    ↓reduceDIte,Option.getD_some,dot_ofFn]
  rfl

theorem column_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (cache : Fin n → QVector n) (i : Fin n) :
    column ((context B,matrixOf cache),i.val)=List.ofFn (dualStep B cache i) := by
  apply List.ext_getElem
  · simp only [column,context,matrixOf,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hr : row< n := by simpa only [List.length_ofFn] using hsecond
    let r : Fin n :=⟨row,hr⟩
    have hs : (List.range n).map (fun j => term ((((context B,matrixOf cache),i.val),row),j))=
        List.ofFn (fun j : Fin n => if i< j then upper (inputVectors B) i j*cache j r else 0) := by
      apply List.ext_getElem
      · simp
      · intro j hj hk
        have hjn : j< n := by simpa using hj
        simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using term_ofFn B cache i r ⟨j,hjn⟩
    have hi : Finset.Ioi i=Finset.univ.filter (fun j => i< j) := by ext j;simp
    have hlen : (context B).1.length=n := by simp [context,matrixOf]
    simp only [column,hlen,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change entry ((((context B,matrixOf cache),i.val),row))=dualStep B cache i r
    simp only [entry,hlen]
    rw [hs,Fin.sum_ofFn]
    simp only [context,matrixOf,List.getElem?_ofFn,i.isLt,hr,↓reduceDIte,Option.getD_some,dot_ofFn]
    simp only [dualStep,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,hi,Finset.sum_filter,squaredNorm,ite_apply,Pi.zero_apply]
    ring

theorem replaceColumn_ofFn {n : ℕ} (cache : Fin n → QVector n) (i : Fin n) (value : QVector n) :
    replaceColumn ((matrixOf cache,i.val),List.ofFn value)=matrixOf (Function.update cache i value) := by
  apply List.ext_getElem
  · simp [replaceColumn,matrixOf]
  · intro j hj hk
    have hjn : j< n := by simpa only [matrixOf,List.length_ofFn] using hk
    let k : Fin n :=⟨j,hjn⟩
    simp only [replaceColumn,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    change (if j=i.val then List.ofFn value else (List.ofFn (fun j => List.ofFn (cache j)))[j]?.getD [])=
      List.ofFn (Function.update cache i value k)
    by_cases h : k=i
    · subst k
      have hjval : j=i.val := congrArg Fin.val h
      simp only [hjval,ite_true,Function.update_self]
    · have hji : j≠i.val := by intro he;apply h;exact Fin.ext he
      simp only [hji,if_false,List.getElem?_ofFn,hjn,↓reduceDIte,Option.getD_some,Function.update_of_ne h]
      rfl

/-- The Cramer bound controls every whole reverse-substitution cache. -/
theorem dualCache_encoding_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0)
    (H : ℕ) (hentries : ∀ r c,|B r c|≤ (2 : ℤ)^H) (steps : ℕ) (hs : steps≤ n) :
    (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ cacheEncodingBound n H := by
  have he := encoded_list_length_bound (encodeList Ratio.encode) (matrixOf (dualCache B steps))
    (n*(6*coordinateHeight n H+21)) (by
      intro vector hv
      obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hv
      exact vector_encoding_height _ _ (fun row => dualCache_height B hdet H hentries steps hs j row))
  simpa only [matrixOf,List.length_ofFn,cacheEncodingBound,Nat.mul_assoc] using he

theorem step_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (steps : ℕ) (hs : steps< n)
    (hb : (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B (steps+1)))).length≤ ticks.length) :
    step (context B,(ticks,matrixOf (dualCache B steps))) steps=
      (context B,(ticks,matrixOf (dualCache B (steps+1)))) := by
  let i : Fin n :=⟨n-1-steps,by omega⟩
  have hn : replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val))=matrixOf (dualCache B (steps+1)) := by
    rw [column_ofFn,replaceColumn_ofFn]
    rw [dualCache,dif_pos hs]
  have hg : (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length := by
    rw [hn,matrixTicks_length]
    exact hb
  have hlen : (context B).1.length=n := by simp [context,matrixOf]
  simp only [step,hlen]
  change (context B,(ticks,if (matrixTicks (replaceColumn ((matrixOf (dualCache B steps),i.val),
      column ((context B,matrixOf (dualCache B steps)),i.val)))).length≤ ticks.length then _ else []))=_
  rw [if_pos hg,hn]

theorem fold_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (ticks : List Unit)
    (hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ ticks.length)
    (steps : ℕ) (hs : steps≤ n) :
    (List.range steps).foldl step (context B,(ticks,matrixOf (fun _ : Fin n => (0 : QVector n))))=
      (context B,(ticks,matrixOf (dualCache B steps))) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [List.range_succ,List.foldl_append,ih (by omega),List.foldl_cons,List.foldl_nil]
    exact step_ofFn B ticks steps (by omega) (hb (steps+1) hs)

def inputRows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) :=
  List.ofFn (fun row => List.ofFn (fun col => B row col))

theorem inputRows_dimension {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    n≤ (integerMatrixTicks (inputRows B)).length := inputColumns_dimension B.transpose

theorem inputRows_entry_height {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (row col : Fin n) :
    |B row col|≤ (2 : ℤ)^(integerMatrixTicks (inputRows B)).length :=
  inputColumns_entry_height B.transpose col row

theorem basisCache_matrix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    basisCache (inputRows B)=matrixOf (orthogonal (inputVectors B)) := by
  rw [inputRows,basisCache_correct B hdet,cache_prefix_eq _ n (le_refl n),List.map_ofFn]
  rfl

/-- Exact refinement of the guarded reverse loop for every nonsingular
original integer input; the public bit-size guard never changes its data. -/
theorem cached_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    cached (inputRows B)=matrixOf (dualVector B) := by
  have hb : ∀ steps,steps≤ n →
      (encodeList (encodeList Ratio.encode) (matrixOf (dualCache B steps))).length≤ (inputBudget (inputRows B)).length := by
    intro steps hs
    apply (dualCache_encoding_bound B hdet (integerMatrixTicks (inputRows B)).length
      (inputRows_entry_height B) steps hs).trans
    rw [inputBudget_length]
    exact cacheEncodingBound_coarse n _ _ (inputRows_dimension B) le_rfl
  have ho : rationalColumns (transpose (inputRows B))=matrixOf (inputVectors B) := by
    rw [inputRows,transpose_input_rows,rationalColumns_input]
    rfl
  have hz : (matrixOf (inputVectors B)).map (fun row => row.map (fun _ => (0 : ℚ)))=
      matrixOf (fun _ : Fin n => (0 : QVector n)) := by
    simp only [matrixOf,List.map_ofFn,Function.comp_def]
    rfl
  unfold cached
  rw [ho,basisCache_matrix B hdet]
  dsimp only
  rw [hz]
  have hl : (inputRows B).length=n := by simp [inputRows]
  rw [hl]
  change ((List.range n).foldl step
    (context B,(inputBudget (inputRows B),matrixOf (fun _ : Fin n => (0 : QVector n))))).2.2=_
  rw [fold_ofFn B _ hb n (le_refl n),dualCache_complete B hdet]

theorem transposeRational_ofFn {n : ℕ} (v : Fin n → QVector n) :
    transposeRational (matrixOf v)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => v col row)) := by
  apply List.ext_getElem
  · simp [transposeRational,matrixOf]
  · intro row hr hs
    have hrow : row< n := by simpa using hs
    simp only [transposeRational,matrixOf,List.length_ofFn,List.getElem_map,List.getElem_range,
      List.getElem_ofFn,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some]

/-- Row-major output is exactly the original matrix inverse transpose. -/
theorem current_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) :
    current (inputRows B)=List.ofFn (fun row : Fin n => List.ofFn (fun col : Fin n => dualVector B col row)) := by
  rw [current,cached_correct B hdet,transposeRational_ofFn]

end

end InfoLossLAR.WorstCase.RationalInverse.Native

end P2MDyadicModule33

/- Helper module Solutions.RegevBridgeBDDCoordinateRounding. -/
section P2MDyadicModule34

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

@[fun_prop] theorem nearestInteger_poly : Poly nearestInteger := by
  unfold nearestInteger
  exact ⟨(show Poly (fun center : ℚ => GaussianRandomizedRounding.Native.anchor (center+1/2)) by fun_prop).program.comp PolyProgram.ratNum⟩

theorem nearestInteger_eq (center : ℚ) : nearestInteger center=⌊center+1/2⌋ := by
  simp only [nearestInteger,GaussianRandomizedRounding.Native.anchor_eq,RationalNumerics.centeredGaussianAnchor,Rat.num_intCast]

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeBDDNativeArithmetic. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open scoped BigOperators

/-- Apply the actual native original inverse transpose to arbitrary signed
integer coordinates. Invalid input shapes retain total list semantics. -/
def lift (input : List (List ℤ) × List ℤ) : List ℚ :=
  (RationalInverse.Native.current input.1).map (fun row =>
    dot (row,input.2.map (fun value : ℤ => (value : ℚ))))

@[fun_prop] theorem lift_poly : Poly lift := by unfold lift;fun_prop

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeBDDNativeSemantics. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2400000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.BDDNative

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

def combination {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (coords : Fin n → ℤ) : QVector n :=
  ∑ col,(coords col : ℚ) • dualVector B col

theorem lift_ofFn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hdet : B.det≠0) (coords : Fin n → ℤ) :
    lift (RationalInverse.Native.inputRows B,List.ofFn coords)=List.ofFn (combination B coords) := by
  rw [lift,RationalInverse.Native.current_correct B hdet]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext row
  rw [dot_ofFn]
  simp only [innerQ,combination,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro col _
  ring

end

end InfoLossLAR.WorstCase.BDDNative

end P2MDyadicModule36

/- Helper module HonestResidualTables. -/
section P2MDyadicModule37

set_option exponentiation.threshold 1024

set_option autoImplicit false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch

open AFT.GaussianSource

end InfoLossLAR.WorstCase.RegevSearch

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

noncomputable section

end

end InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt

open scoped BigOperators

noncomputable section

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open scoped BigOperators

noncomputable section

private theorem poly_cap (p : Polynomial ℕ) {n : ℕ} (h1 : 1 ≤ n) (hp : p.eval 1 ≤ n) :
    p.eval n ≤ n^(p.natDegree+1) := by
  calc
    p.eval n = ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^i := p.eval_eq_sum_range n
    _ ≤ ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * n^p.natDegree :=
      Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right h1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    _ = p.eval 1 * n^p.natDegree := by
      rw [← Finset.sum_mul]; congr 1; simpa using (p.eval_eq_sum_range 1).symm
    _ ≤ n * n^p.natDegree := Nat.mul_le_mul_right _ hp
    _ = _ := by rw [pow_succ,mul_comm]

/-- At the fixed-family smoothing error, every polynomially bounded scalar row
count eventually makes the intrinsic whole-table variation at most 1/32. -/
theorem polynomial_rows_intrinsic_budget (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c ≤ p.eval n,
      let ε := 1/(2:ℝ)^(Nat.size (n+2))^2
      (c:ℝ)*(ε/(1-ε)+4*ε+16*Real.exp (-Real.pi*((n:ℝ)+2)^2/2)) ≤ 1/32 := by
  let a := p.natDegree+1
  refine ⟨max 704 (max (p.eval 1) (2^(a+1))),?_⟩
  intro n hn c hc
  have hn704 : 704 ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hn1' : 1 ≤ n+2 := by omega
  have hpa : c ≤ n^a := hc.trans (poly_cap p hn1 ((le_max_left _ _).trans ((le_max_right _ _).trans hn)))
  let s := Nat.size (n+2)
  have h2 : 2^(a+1) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hs : a+1 ≤ s := (Nat.lt_size.mpr (show 2^(a+1) ≤ n+2 by omega)).le
  have hss : s ≤ n+2 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hpc : (n+2)^(a+1) ≤ 2^(s^2) := by
    calc
      _ ≤ (2^s)^(a+1) := Nat.pow_le_pow_left (Nat.lt_size_self _).le _
      _ = 2^(s*(a+1)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simpa [pow_two] using Nat.mul_le_mul_left s hs)
  have hcap : 704*c ≤ 2^(s^2) := by
    calc
      _ ≤ (n+2)*(n+2)^a := Nat.mul_le_mul (by omega) (hpa.trans (Nat.pow_le_pow_left (by omega) a))
      _ = (n+2)^(a+1) := by rw [pow_succ (n+2) a, mul_comm]
      _ ≤ _ := hpc
  let Z := (2:ℝ)^(s^2)
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hZ : 2 ≤ Z := by
    have hz : 1 ≤ s^2 := Nat.one_le_pow _ _ (by omega)
    simpa [Z] using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hz)
  let ε := 1/Z
  have hep : 0 < ε := one_div_pos.mpr hZpos
  have hehalf : ε ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hZ
  have hratio : ε/(1-ε) ≤ 2*ε := (div_le_iff₀ (by linarith)).mpr (by nlinarith [mul_nonneg hep.le (show 0 ≤ 1-2*ε by linarith)])
  have hpow : Z ≤ Real.exp (Real.pi*((n:ℝ)+2)^2/2) := by
    calc
      Z ≤ (Real.exp 1)^(s^2) := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
      _ = Real.exp ((s:ℝ)^2) := by rw [←Real.exp_nat_mul]; push_cast; rw [mul_one]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hsr : (s:ℝ) ≤ (n:ℝ)+2 := by exact_mod_cast hss
        have hsq := (sq_le_sq₀ (Nat.cast_nonneg s) (by positivity)).mpr hsr
        nlinarith [mul_nonneg (show 0 ≤ Real.pi-2 by linarith [Real.pi_gt_three]) (sq_nonneg ((n:ℝ)+2))]
  have hexp : Real.exp (-Real.pi*((n:ℝ)+2)^2/2) ≤ ε := by
    rw [show -Real.pi*((n:ℝ)+2)^2/2 = -(Real.pi*((n:ℝ)+2)^2/2) by ring, Real.exp_neg, ←one_div]
    exact one_div_le_one_div_of_le hZpos hpow
  have hprod : 704*(c:ℝ) ≤ Z := by dsimp only [Z]; exact_mod_cast hcap
  change (c:ℝ)*(ε/(1-ε)+4*ε+16*_ ) ≤ _
  calc
    _ ≤ (c:ℝ)*(22*ε) := mul_le_mul_of_nonneg_left (by linarith [hexp,hratio]) (Nat.cast_nonneg c)
    _ = (22*(c:ℝ))/Z := by dsimp only [ε];ring
    _ ≤ _ := (div_le_iff₀ hZpos).mpr (by linarith)

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding GaussianPoissonSeries

open RegevLWE.GaussConv BDDNative RationalGramSchmidt GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

end

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule37

/- Helper module Recovery. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ShortProbe

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

abbrev Base := List (List ℤ) × ℕ

abbrev ProbeInput := (Base × List ℚ) × List (List ℤ)

abbrev Request := ProbeInput × List ℕ

/-- Recover the signed pairing from a rational prediction and an integer representative modulo q. -/
def unwrap (w : (ℕ × ℚ) × ℤ) : ℤ := w.2 + (w.1.1 : ℤ) *
  IntegerBasis.nearestInteger ((w.1.2 - (w.2:ℚ)) / (w.1.1:ℚ))

@[fun_prop] theorem unwrap_poly : Poly unwrap := by unfold unwrap;fun_prop

theorem unwrap_correct (q : ℕ) (hq : 0 < q) (x : ℚ) (s y : ℤ)
    (hs : (q:ℤ) ∣ y-s) (hx : |x-(y:ℚ)| < (q:ℚ)/2) : unwrap ((q,x),s) = y := by
  obtain ⟨k,hk⟩ := hs
  have hq' : 0 < (q:ℚ) := by exact_mod_cast hq
  have hrat : (y:ℚ)-(s:ℚ)=(q:ℚ)*(k:ℚ) := by exact_mod_cast hk
  have ha : IntegerBasis.nearestInteger ((x-s)/q) = k := by
    apply (IntegerBasis.nearestInteger_eq _).trans
    apply Int.floor_eq_iff.mpr
    obtain ⟨hlo,hhi⟩ := abs_lt.mp hx
    constructor
    · have bound := (le_div_iff₀ hq').mpr (by linarith only [hlo,hrat] :
          ((k:ℚ)-1/2)*q ≤ x-s)
      linarith only [bound]
    · have bound := (div_lt_iff₀ hq').mpr (by linarith only [hhi,hrat] :
          x-s < ((k:ℚ)+1/2)*q)
      linarith only [bound]
  unfold unwrap
  dsimp only
  rw [ha]
  omega

def measure (w : ((Base × List ℚ) × List ℕ) × List ℤ) : ℤ :=
  unwrap ((w.1.1.1.2, IntegerBasis.Native.projection ((w.1.1.1.1,w.2),w.1.1.2)),
    Integration9_9.TM2NativeAffineApply.dot (w.2,w.1.2.map (fun v : ℕ => (v:ℤ))))

@[fun_prop] theorem natListCasts_poly : Poly (fun s : List ℕ => s.map (fun v : ℕ => (v:ℤ))) := by
  exact Poly.list_map (f := fun (_ : List ℕ) (v : ℕ) => (v:ℤ)) (as := id) (by fun_prop) (by fun_prop)

@[fun_prop] theorem measure_poly : Poly measure := by
  have hc : Poly (fun w : ((Base × List ℚ) × List ℕ) × List ℤ =>
      w.1.2.map (fun v : ℕ => (v:ℤ))) := Poly.comp natListCasts_poly (by fun_prop)
  unfold measure
  exact Poly.comp unwrap_poly (Poly.pair (by fun_prop)
    (Poly.comp Integration9_9.TM2NativeAffineApply.dot_poly (Poly.pair (by fun_prop) hc)))

/-- Every saved coefficient vector is one row. Count coordinates from the original basis. -/
def columns (w : List (List ℤ) × List (List ℤ)) : List (List ℤ) :=
  (List.range w.1.length).map (fun j => w.2.map (fun v => v[j]?.getD 0))

@[fun_prop] theorem columns_poly : Poly columns := by
  have hi : Poly (fun w : List (List ℤ) × List (List ℤ) => List.range w.1.length) :=
    Poly.comp (f:=fun (l : List (List ℤ)) => List.range l.length)
      (g:=fun w : List (List ℤ) × List (List ℤ) => w.1) Poly.list_indices (by fun_prop)
  unfold columns
  exact Poly.list_map (by fun_prop) hi

def gram (w : List (List ℤ)) : List (List ℤ) :=
  w.map (fun v => w.map (fun c => Integration9_9.TM2NativeAffineApply.dot (v,c)))

@[fun_prop] theorem gram_poly : Poly gram := by unfold gram;fun_prop

def weights (w : Request) : List ℤ :=
  w.1.2.map (fun c => measure ((w.1.1,w.2),c))

@[fun_prop] theorem weights_poly : Poly weights := by unfold weights;fun_prop

def recover (w : Request) : List ℚ × List ℤ :=
  let cols := columns (w.1.1.1.1,w.1.2)
  let target := IntegerBasis.Native.matrixApply (cols,weights w)
  let z := (BDDNative.lift (gram cols,target)).map IntegerBasis.nearestInteger
  (BDDNative.lift (w.1.1.1.1,z),z)

@[fun_prop] theorem recover_poly : Poly recover := by unfold recover;fun_prop

abbrev intRows {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) :=
  List.ofFn fun i => List.ofFn (C i)

theorem columns_ofFn {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (C : Matrix (Fin m) (Fin n) ℤ) :
    columns (intRows B,intRows C) = intRows C.transpose := by
  apply List.ext_getElem
  · simp [intRows,columns]
  · intro i hi hj
    have hiN : i < n := by simpa only [intRows,List.length_ofFn] using hj
    simp [intRows,columns, List.map_ofFn, Function.comp_def]
    funext j
    simp [hiN]

theorem gram_ofFn {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) :
    gram (intRows C.transpose) = intRows (C.transpose*C) := by
  simp only [gram,intRows,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [Integration9_9.TM2NativeAffineApply.dot_ofFn]
  rfl

theorem lift_eq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (z : Fin n → ℤ) (u : Fin n → ℚ)
    (h : ∀ j, ∑ i, (B i j:ℚ)*u i=z j) :
    BDDNative.lift (intRows B,List.ofFn z) = List.ofFn u := by
  rw [show intRows B = RationalInverse.Native.inputRows B from rfl,BDDNative.lift_ofFn _ hB]
  apply congrArg List.ofFn
  apply rational_pairings_unique B hB
  intro k
  have hsum (i : Fin n) : innerQ (dualVector B i) (inputVectors B k) = if k=i then 1 else 0 :=
    dualVector_pairing B hB i k
  change (∑ j,(∑ i, (z i : ℚ) • dualVector B i) j * inputVectors B k j) = _
  simp only [Finset.sum_apply,Pi.smul_apply, smul_eq_mul,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ i,(z i:ℚ) * innerQ (dualVector B i) (inputVectors B k)) = _
  simp_rw [hsum]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simpa only [innerQ,inputVectors,mul_comm] using (h k).symm

theorem measure_correct {n q : ℕ} (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (c z : Fin n → ℤ)
    (s : Fin n → ℕ) (hs : ∀ j, (s j : ZMod q)=(z j:ZMod q))
    (hx : |IntegerBasis.projection B x c - ((c ⬝ᵥ z : ℤ):ℚ)| < (q:ℚ)/2) :
    measure ((((intRows B,q),List.ofFn x),List.ofFn s),List.ofFn c) = c ⬝ᵥ z := by
  unfold measure
  dsimp only
  rw [IntegerBasis.Native.projection_ofFn,List.map_ofFn,Integration9_9.TM2NativeAffineApply.dot_ofFn]
  apply unwrap_correct _ hq _ _ _ _ hx
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  unfold dotProduct
  simp only [Int.cast_sub,Int.cast_sum,Int.cast_mul,Function.comp_apply,Int.cast_natCast,hs,sub_self]

theorem matrixApply_rows {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) (z : Fin n → ℤ) :
    IntegerBasis.Native.matrixApply (intRows C,List.ofFn z)=List.ofFn (C.mulVec z) := by
  simp only [intRows,IntegerBasis.Native.matrixApply,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  rw [Integration9_9.TM2NativeAffineApply.dot_ofFn]
  rfl

theorem nearest_int (z : ℤ) : IntegerBasis.nearestInteger (z:ℚ)=z := by
  rw [IntegerBasis.nearestInteger_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

theorem recover_correct {n m q : ℕ} (hq : 0 < q)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (C : Matrix (Fin m) (Fin n) ℤ) (hC : (C.transpose*C).det ≠ 0)
    (x u : Fin n → ℚ) (z : Fin n → ℤ)
    (hu : ∀ j, ∑ i, (B i j:ℚ)*u i=z j)
    (s : Fin n → ℕ) (hs : ∀ j, (s j : ZMod q)=(z j:ZMod q))
    (hx : ∀ a, |IntegerBasis.projection B x (C a) - ((C.mulVec z a : ℤ):ℚ)| < (q:ℚ)/2) :
    recover ((((intRows B,q),List.ofFn x),intRows C),List.ofFn s) = (List.ofFn u,List.ofFn z) := by
  have hw : weights ((((intRows B,q),List.ofFn x),intRows C),List.ofFn s) =
      List.ofFn (C.mulVec z) := by
    simp only [weights,intRows,List.map_ofFn,Function.comp_def]
    apply congrArg List.ofFn
    funext a
    exact measure_correct hq B x (C a) z s hs (hx a)
  have hsym : (C.transpose*C).transpose=C.transpose*C := by simp
  have halg (j : Fin n) :
      ∑ i, ((C.transpose*C) i j:ℚ)*(z i:ℚ)=((C.transpose*C).mulVec z j:ℚ) := by
    have hji (i : Fin n) : (C.transpose*C) i j = (C.transpose*C) j i := by
      exact congrFun (congrFun hsym j) i
    simp only [Matrix.mulVec,dotProduct,Int.cast_sum,Int.cast_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hji i]
  unfold recover
  dsimp only
  rw [columns_ofFn,gram_ofFn,hw,matrixApply_rows,Matrix.mulVec_mulVec,lift_eq _ hC _ _ halg]
  simp only [List.map_ofFn,Function.comp_def,nearest_int]
  rw [lift_eq _ hB _ _ hu]

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule38

/- Helper module Geometry. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators

noncomputable section

theorem projection_of_dual {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℚ)
    (z c : Fin n → ℤ) (hu : ∀ j, ∑ i, (B i j:ℚ)*u i=z j) :
    IntegerBasis.projection B u c = ((c ⬝ᵥ z:ℤ):ℚ) := by
  unfold IntegerBasis.projection Matrix.mulVec dotProduct
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [←hu j,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sigma_sqrt_lt_half_q (n : ℕ) : (famσ n : ℝ)*Real.sqrt n < (famq n:ℝ)/2 := by
  have hq : 2^16*famL n^64 ≤ famq n :=
    (Nat.find_spec (Nat.exists_infinite_primes (2^16*famL n^64))).1
  have hL : 1 ≤ famL n := by simp [famL]
  have hp : famL n^2 ≤ famL n^64 := Nat.pow_le_pow_right hL (by decide)
  have hq' : 2*(famL n)^2 < famq n := by
    have hpow : 0 < famL n^2 := by positivity
    omega
  have hr : Real.sqrt n ≤ famL n := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · unfold famL
      push_cast
      nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hqrt : (2:ℝ)*(famL n:ℝ)^2 < (famq n:ℝ) := by exact_mod_cast hq'
  change (famL n : ℝ)*Real.sqrt n < _
  calc
    _ ≤ (famL n:ℝ)*(famL n:ℝ) := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)
    _ < _ := by linarith only [hqrt]

theorem probe_close {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (hR : 0<R)
    (x u : Fin n → ℚ) (z c : Fin n → ℤ)
    (hu : ∀ j, ∑ i, (B i j:ℚ)*u i=z j)
    (hd : (R:ℝ)^2 * (∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4)
    (hc : ‖latVec B c‖ ≤ 2*(R:ℝ)*Real.sqrt n) :
    |IntegerBasis.projection B x c - ((c ⬝ᵥ z:ℤ):ℚ)| < (famq n:ℚ)/2 := by
  let err := IntegerBasis.rationalPoint x - IntegerBasis.rationalPoint u
  have herr : ‖err‖^2 = ∑ i,((x i-u i:ℚ):ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change ((x i:ℝ)-(u i:ℝ))^2=_
    rw [Rat.cast_sub]
  have hd' : (R:ℝ)*‖err‖ ≤ (famσ n:ℝ)/2 := by
    rw [←herr] at hd
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hd]
  apply (Rat.cast_lt (K:=ℝ)).mp
  rw [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,
    ←projection_of_dual B u z c hu,IntegerBasis.projection_spec,IntegerBasis.projection_spec,←inner_sub_left]
  calc
    _ ≤ ‖err‖*‖latVec B c‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖err‖*(2*(R:ℝ)*Real.sqrt n) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = ((R:ℝ)*‖err‖)*(2*Real.sqrt n) := by ring
    _ ≤ ((famσ n:ℝ)/2)*(2*Real.sqrt n) := mul_le_mul_of_nonneg_right hd' (by positivity)
    _ = _ := by ring
    _ < _ := sigma_sqrt_lt_half_q n

theorem recover_from_short_pool {n m : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (C : Matrix (Fin m) (Fin n) ℤ) (hC : (C.transpose*C).det ≠ 0)
    (R : ℚ) (hR : 0<R) (x u : Fin n → ℚ) (z : Fin n → ℤ)
    (hu : ∀ j, ∑ i, (B i j:ℚ)*u i=z j)
    (hd : (R:ℝ)^2 * (∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4)
    (hc : ∀ a, ‖latVec B (C a)‖ ≤ 2*(R:ℝ)*Real.sqrt n) :
    recover ((((intRows B,famq n),List.ofFn x),intRows C),List.ofFn fun j => (z j:ZMod (famq n)).val)
      = (List.ofFn u,List.ofFn z) :=
  recover_correct (NeZero.pos _) B hB C hC x u z hu _
    (fun _ => ZMod.natCast_zmod_val _) (fun a => probe_close B R hR x u z (C a) hu hd (hc a))

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule39

/- Helper module TrialLaw. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries AFT.BinaryArithmetic

open Integration9_9.GaussianRegroupMachine QAlgorithms.Complexity

open RegevSketch

noncomputable section

theorem mix_expectation {X Y : Type*} [Fintype Y] (p : X → ℝ) (h0 : ∀ x,0≤p x)
    (hS : Summable p) (h1 : ∑' x,p x=1) (K : X → FiniteDist Y) (test : Y → ℝ) :
    (FiniteDist.countableMix p h0 hS h1 K).expectation test = ∑' x,p x*(K x).expectation test := by
  unfold FiniteDist.expectation FiniteDist.countableMix
  dsimp only
  simp_rw [←tsum_mul_right, Finset.mul_sum, ← mul_assoc]
  exact (Summable.tsum_finsetSum (fun y _ =>
    (FiniteDist.countableChannel_summable p hS K y).mul_right (test y))).symm

def observedWord {n blocks rows : ℕ} (sec : ℕ) (pp : Str)
    (B : Matrix (Fin n) (Fin n) ℤ) (values : Fin (blocks*rows) → Fin n → ℤ)
    (x : Fin n → ℚ) (q : ℕ) (v : ℚ) (cutoff bits : ℕ)
    (tape : Fin ((blocks*rows)*((bits+1)+(2*cutoff+1)+1)) → Fin 2) : Str :=
  observed ((unary sec,pp),((List.replicate blocks (),List.replicate rows ()),
      ((numericalContext B x q v cutoff bits,List.ofFn fun i => List.ofFn (values i)),
        List.ofFn fun j => digitBoolean (tape j))))

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule40

/- Helper module Coins. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open AFT GaussianPoissonSeries GaussianRandomizedRounding

noncomputable section

def single {T : Type*} [Fintype T] (x : T) : FiniteDist T where
  weight t := if x=t then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  sum_one := by simp

theorem single_expect {T : Type*} [Fintype T] (x : T) (f : T → ℝ) :
    (single x).expectation f = f x := by
  simp [single,FiniteDist.expectation,ite_mul]

theorem single_product {T : Type*} [Fintype T] (m : ℕ) (x : Fin m → T) :
    FiniteDist.independent (fun j => single (x j)) = single x := by
  ext w
  simp only [FiniteDist.independent,single,Fintype.prod_ite_zero,Finset.prod_const_one,funext_iff]

theorem pushed_coins {X : Type*} (p : X → ℝ) (p0 : ∀ x,0≤p x) (p1 : HasSum p 1)
    (b : X → Fin 2) (m : ℕ) (test : (Fin m → Fin 2) → ℝ) :
    (FiniteDist.independent (fun _ : Fin m => FiniteDist.countableMix p p0 p1.summable p1.tsum_eq
        (fun x => single (b x)))).expectation test =
      ∑' w : Fin m → X, (∏ i,p (w i))* test (fun i => b (w i)) := by
  rw [←countableProductChannel_eq]
  unfold countableProductChannel
  rw [mix_expectation]
  simp only [single_product,single_expect,finiteProductMass]

theorem biased_tape_transfer {X : Type*} (p : X → ℝ) (p0 : ∀ x,0≤p x) (p1 : HasSum p 1)
    (b : X → Fin 2) (δ : ℝ)
    (hδ : |(∑' x,if b x=1 then p x else 0) - (1/2:ℝ)| ≤ δ)
    (m : ℕ) (test : (Fin m → Fin 2) → ℝ) (ht : ∀ w,0≤test w ∧ test w≤1) :
    (FiniteDist.uniform (Fin m → Fin 2)).expectation test -
        (∑' w : Fin m → X, (∏ i,p (w i))* test (fun i => b (w i))) ≤ m*δ := by
  let B := FiniteDist.countableMix p p0 p1.summable p1.tsum_eq (fun x => single (b x))
  let fair := FiniteDist.uniform (Fin 2)
  have hB : B.weight 1=∑' x,if b x=1 then p x else 0 := by
    simp only [B,FiniteDist.countableMix,single,mul_ite,mul_one,mul_zero]
  have h1 : |B.weight 1-(1/2:ℝ)|≤δ := by rwa [hB]
  have h0 : |B.weight 0-(1/2:ℝ)|≤δ := by
    have hn := B.sum_one
    rw [Fin.sum_univ_two] at hn
    rw [show B.weight 0 - 1/2 = -(B.weight 1-1/2) by linarith only [hn], abs_neg]
    exact h1
  have hb : (∑ j, |fair.weight j-B.weight j|)≤2*δ := by
    rw [Fin.sum_univ_two]
    norm_num only [fair,FiniteDist.uniform_weight,Fintype.card_fin,Nat.cast_ofNat]
    rw [abs_sub_comm,abs_sub_comm _ (B.weight 1)]
    rw [two_mul]
    simpa only [one_div] using add_le_add h0 h1
  let first := FiniteDist.independent (fun _ : Fin m => fair)
  let second := FiniteDist.independent (fun _ : Fin m => B)
  have hprod : (∑ w,|first.weight w-second.weight w|) ≤ (m:ℝ)*(2*δ) := by
    have h := FiniteDist.l1_independent_fin_le m (fun _ => fair) (fun _ => B)
    refine h.trans ?_
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
      Finset.sum_le_sum (s:=Finset.univ) (fun (_:Fin m) _ => hb)
  have hs (w : Fin m → Fin 2) : 2*((first.weight w-second.weight w)*test w) ≤
      |first.weight w-second.weight w| + (first.weight w-second.weight w) := by
    by_cases h : 0 ≤ first.weight w-second.weight w
    · rw [abs_of_nonneg h];nlinarith only [mul_le_mul_of_nonneg_left (ht w).2 h] 
    · rw [abs_of_nonpos (le_of_not_ge h)]
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (ht w).1]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => hs w)
  simp only [← Finset.mul_sum,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,first.sum_one,second.sum_one,sub_self,add_zero] at hh
  rw [←pushed_coins p p0 p1 b m test,←Wide.independent_uniform (Index:=Fin m) (Value:=Fin 2)]
  change first.expectation test - second.expectation test ≤ _
  unfold FiniteDist.expectation
  linarith only [hh,hprod]

def parityDigit {n : ℕ} (j : Fin n) (z : Fin n → ℤ) : Fin 2 :=
  if Odd (z j) then 1 else 0

theorem parity_eq {n : ℕ} (j : Fin n) (z : Fin n → ℤ) :
    AFT.BinaryArithmetic.digitBoolean (parityDigit j z)=decide ((z j).natAbs % 2 = 1) := by
  have hh : Odd (z j) ↔ (z j).natAbs%2=1 := Int.natAbs_odd.symm.trans Nat.odd_iff
  by_cases h : Odd (z j) <;> simp [parityDigit,h,←hh,AFT.BinaryArithmetic.digitBoolean]

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule41

/- Helper module CoinJoint. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option maxHeartbeats 750000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open AFT GaussianPoissonSeries

noncomputable section

abbrev poolWeight {X : Type*} (p : X → ℝ) {m : ℕ} (pool : Fin m → X) : ℝ := ∏ i, p (pool i)

theorem parity_joint {X : Type*} (p : X → ℝ) (h0 : ∀ a,0≤p a) (h1 : HasSum p 1)
    (bit : X → Fin 2) (δ : ℝ) (hδ : |(∑' a, if bit a=1 then p a else 0) - 1/2| ≤ δ)
    (s m : ℕ) (test : (Fin s → X) → (Fin m → Fin 2) → ℝ)
    (ht : ∀ a k,0≤test a k ∧ test a k≤1)
    (hfair : (17/24:ℝ) ≤ ∑' a, poolWeight p a*(FiniteDist.uniform (Fin m → Fin 2)).expectation (test a))
    (hsmall : (m:ℝ)*δ ≤ 1/24) :
    (2/3:ℝ) ≤ ∑' ac : (Fin s → X) × (Fin m → X),
      poolWeight p ac.1 * poolWeight p ac.2 * test ac.1 (fun i => bit (ac.2 i)) := by
  let f := poolWeight p (m:=s)
  let g := poolWeight p (m:=m)
  have hf0 (a) : 0≤f a := Finset.prod_nonneg fun i _ => h0 _
  have hg0 (a) : 0≤g a := Finset.prod_nonneg fun i _ => h0 _
  have hf : HasSum f 1 := by
    have he : f = finiteProductMass s p := by funext a; rfl
    rw [he]
    simpa only [h1.tsum_eq,one_pow] using finiteProductMass_hasSum s p h0 h1.summable
  have hg : HasSum g 1 := by
    have he : g = finiteProductMass m p := by funext a; rfl
    rw [he]
    simpa only [h1.tsum_eq,one_pow] using finiteProductMass_hasSum m p h0 h1.summable
  let aTest (a : Fin s → X) (c : Fin m → X) := test a (fun i => bit (c i))
  let expFair (a : Fin s → X) := (FiniteDist.uniform (Fin m → Fin 2)).expectation (test a)
  let expCoins (a : Fin s → X) := ∑' c,g c*aTest a c
  have ec (a) : expFair a - expCoins a ≤ m*δ := biased_tape_transfer p h0 h1 bit δ hδ m (test a) (ht a)
  have hv (a) : 0 ≤ expFair a ∧ expFair a ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg fun v _ => mul_nonneg ((FiniteDist.uniform _).nonneg v) (ht a v).1
    · calc
        _ ≤ ∑ v,(FiniteDist.uniform (Fin m → Fin 2)).weight v :=
          Finset.sum_le_sum (fun v _ => mul_le_of_le_one_right ((FiniteDist.uniform _).nonneg _) (ht a v).2)
        _ = _ := (FiniteDist.uniform _).sum_one
  have heS : Summable (fun a => f a*expFair a) := hf.summable.of_nonneg_of_le
      (fun a => mul_nonneg (hf0 a) (hv a).1) (fun a => mul_le_of_le_one_right (hf0 a) (hv a).2)
  have hpair := hf.summable.mul_of_nonneg hg.summable hf0 hg0
  let join (ac : (Fin s → X) × (Fin m → X)) := f ac.1*g ac.2*aTest ac.1 ac.2
  have hjS : Summable join := hpair.of_nonneg_of_le
    (fun ac => mul_nonneg (mul_nonneg (hf0 ac.1) (hg0 ac.2)) (ht _ _).1)
    (fun ac => mul_le_of_le_one_right (mul_nonneg (hf0 ac.1) (hg0 ac.2)) (ht _ _).2)
  have heq (a) : (∑' c,join (a,c))=f a*expCoins a := by
    simp only [join,expCoins,tsum_mul_left,mul_assoc]
  have hsum : Summable (fun a => f a*expCoins a) := by
    simpa only [←heq] using hjS.prod
  have hle : (∑' a,f a*expFair a) ≤ ∑' a,(f a*expCoins a+f a*(m*δ)) := by
    apply heS.tsum_le_tsum _ (hsum.add (hf.summable.mul_right _))
    intro a
    rw [←mul_add]
    exact mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mp (ec a)) (hf0 a)
  rw [hsum.tsum_add (hf.summable.mul_right _),tsum_mul_right,hf.tsum_eq,one_mul] at hle
  have hg' : (∑' a,f a*expCoins a) = ∑' pair,join pair := by
    rw [hjS.tsum_prod];simp_rw [heq]
  have hl := hfair.trans hle
  calc
    (2/3:ℝ) = 17/24 - 1/24 := by norm_num
    _ ≤ ∑' a,f a*expCoins a := by linarith only [hl,hsmall]
    _ = _ := hg'

theorem parity_intrinsic_budget (p : Polynomial ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m, 2*m ≤ p.eval n →
      (m:ℝ)*(2*(RegevSketch.smoothingError n/(1-RegevSketch.smoothingError n))) ≤ 1/24 := by
  obtain ⟨N,hN⟩ := IntegerBasis.Native.polynomial_rows_intrinsic_budget p
  refine ⟨N,?_⟩
  intro n hn m hm
  have hb := hN n hn (2*m) hm
  dsimp only at hb
  change (m:ℝ)*(2*((1/(2:ℝ)^(n+2).size^2)/(1-1/(2:ℝ)^(n+2).size^2))) ≤ 1/24
  push_cast at hb
  have hε : 0 ≤ 1/(2:ℝ)^(n+2).size^2 := by positivity
  have hm' : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hex := (Real.exp_pos (-Real.pi*((n:ℝ)+2)^2/2)).le
  nlinarith only [hb,mul_nonneg hε hm',mul_nonneg hex hm']

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule42

/- Helper module Error. -/
section P2MDyadicModule43

set_option autoImplicit false

open scoped Classical BigOperators Topology

namespace InfoLossLAR.WorstCase.ShortProbePlan

open Filter

noncomputable section

theorem trial_budget (p : Polynomial ℕ) :
    ∃ L : Polynomial ℕ, ∀ n, rows p n ≤ L.eval n ∧ 2*(rows p n*coinWidth p n) ≤ L.eval n := by
  obtain ⟨P,hP⟩ := pool_budget p
  refine ⟨Polynomial.C (2*trialSize p 0)+Polynomial.C 2*P,fun n => ?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  by_cases hn : n=0
  · subst n; unfold trialSize; omega
  · have ht : trialSize p n ≤ n*trialSize p n := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn)
    have h := (hP n).1
    unfold used at h
    unfold trialSize at h ht ⊢
    omega

def totalError (n : ℕ) : ℝ := 18*((n:ℝ)+1)^2*(1/2:ℝ)^n

theorem final_error (n : ℕ) :
    (1/2:ℝ)^n + 16*((n:ℝ)+1)^2*(1/4:ℝ)^n + (1/3:ℝ)^n ≤ totalError n := by
  have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1/2) n
  have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)≤1/2) n
  let a : ℝ := ((n:ℝ)+1)^2
  have ha : 1 ≤ a := by dsimp [a]; nlinarith [Nat.cast_nonneg (α:=ℝ) n,sq_nonneg (n:ℝ)]
  have hb := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 16*a by positivity)
  have hc := mul_le_mul_of_nonneg_right ha (show 0≤(1/2:ℝ)^n by positivity)
  change (1/2:ℝ)^n+16*a*(1/4:ℝ)^n+(1/3:ℝ)^n ≤ 18*a*(1/2:ℝ)^n
  linarith only [hb,h3,hc]

theorem totalError_negligible : Negligible totalError := by
  refine ⟨fun n => by unfold totalError; positivity, ?_⟩
  intro c _
  let d : ℕ := ⌈c⌉₊
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one (d+2) (r:=1/2) (by norm_num) (by norm_num)
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((ht.eventually_lt_const (by norm_num : (0:ℝ)<1/72)).and
    (eventually_ge_atTop 1))
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨hh,hn'⟩ := hN n hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn'
  have hscale : 18*((n:ℝ)+1)^2 ≤ 72*(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hprod := mul_le_mul_of_nonneg_right hscale (show 0≤ (1/2:ℝ)^n*(n:ℝ)^d by positivity)
  change (n:ℝ)^(d+2)*(1/2:ℝ)^n < 1/72 at hh
  rw [pow_add] at hh
  calc
    totalError n ≤ 1 / (n:ℝ)^d := by
      apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le h1) _)).mpr
      unfold totalError
      nlinarith only [hprod,hh]
    _ = (n:ℝ)^(-(d:ℝ)) := by rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg (Nat.le_ceil c))

end

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule43

/- Helper module Product. -/
section P2MDyadicModule44

set_option autoImplicit false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

noncomputable section

abbrev density {X : Type*} (μ : X → ℝ) {s : ℕ} (v : Fin s → X) : ℝ := ∏ i, μ (v i)

theorem iid_mass {X : Type} (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (h : HasSum μ 1) (s : ℕ) :
    HasSum (fun v : Fin s → X => density μ v) 1 := by
  have t := iid_product_hasSum μ (fun _ => 1) hμ (by simp) (by simpa using h.summable) s
  simpa [density,h.tsum_eq] using t

/-- A disjoint held-out pool and independent trials control the whole algorithm even
when the other, unused-width requests are arbitrarily correlated with those trials. -/
theorem joint_failure {H X : Type} (ρ : H → ℝ) (μ : X → ℝ)
    (hρ : ∀ h, 0 ≤ ρ h) (hμ : ∀ x, 0 ≤ μ x) (hρ1 : HasSum ρ 1) (hμ1 : HasSum μ 1)
    (good : H → Prop) (fail : X → ℝ) (hf : ∀ x, 0 ≤ fail x ∧ fail x ≤ 1)
    (n : ℕ) (loss : H × (Fin n → X) → ℝ) (hl : ∀ y, 0 ≤ loss y)
    (hbound : ∀ y, loss y ≤ (if good y.1 then 0 else 1) + ∏ i, fail (y.2 i)) :
    (∑' y : H × (Fin n → X), ρ y.1 * density μ y.2 * loss y) ≤
      (∑' h, ρ h * (if good h then 0 else 1)) + (∑' x, μ x * fail x)^n := by
  classical
  let bad (h : H) : ℝ := ρ h * (if good h then 0 else 1)
  have hb0 (h) : 0 ≤ bad h := by unfold bad; split_ifs <;> simp [hρ]
  have hb : Summable bad := hρ1.summable.of_nonneg_of_le hb0 (by intro h; unfold bad; split_ifs <;> simp [hρ])
  let f (x) := μ x * fail x
  have hs : Summable f := hμ1.summable.of_nonneg_of_le (fun x => mul_nonneg (hμ x) (hf x).1)
    (fun x => mul_le_of_le_one_right (hμ x) (hf x).2)
  have hv := iid_mass μ hμ hμ1 n
  have hp := iid_product_hasSum μ fail hμ (fun x => (hf x).1) hs n
  let v (xs : Fin n → X) := density μ xs
  let t (xs : Fin n → X) := density μ xs * ∏ i, fail (xs i)
  have hv0 (xs) : 0 ≤ v xs := Finset.prod_nonneg (fun _ _ => hμ _)
  have ht0 (xs) : 0 ≤ t xs := mul_nonneg (hv0 xs) (Finset.prod_nonneg (fun _ _ => (hf _).1))
  have h1 := hb.hasSum.mul hv (hb.mul_of_nonneg hv.summable hb0 hv0)
  have h2 := hρ1.mul hp (hρ1.summable.mul_of_nonneg hp.summable hρ ht0)
  let upper (y : H × (Fin n → X)) := bad y.1 * v y.2 + ρ y.1 * t y.2
  have hu : HasSum upper ((∑' h, bad h) + (∑' x, μ x*fail x)^n) := by
    simpa only [one_mul,mul_one] using h1.add h2
  have hlo (y : H × (Fin n → X)) : 0 ≤ ρ y.1*density μ y.2*loss y :=
    mul_nonneg (mul_nonneg (hρ _) (hv0 _)) (hl _)
  have hh (y : H × (Fin n → X)) : ρ y.1*density μ y.2*loss y ≤ upper y := by
    calc
      _ ≤ ρ y.1*density μ y.2*((if good y.1 then 0 else 1) + ∏ i,fail (y.2 i)) :=
        mul_le_mul_of_nonneg_left (hbound y) (mul_nonneg (hρ _) (hv0 _))
      _ = _ := by unfold upper bad t v; ring
  exact ((hu.summable.of_nonneg_of_le hlo hh).tsum_le_tsum hh hu.summable).trans_eq hu.tsum_eq

end

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

end P2MDyadicModule44

/- Helper module PoolProduct. -/
section P2MDyadicModule45

set_option autoImplicit false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

noncomputable section

def rectangle (X : Type) (n t : ℕ) : (Fin n → Fin t → X) ≃ (Fin (n*t) → X) where
  toFun v i := v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  invFun v i j := v (finProdFinEquiv (i,j))
  left_inv _ := by funext i j; simp
  right_inv f := funext fun i => congrArg f (finProdFinEquiv.apply_symm_apply i)

def joinPool (X : Type) (s n t : ℕ) :
    ((Fin s → X) × (Fin n → Fin t → X)) ≃ (Fin (s+n*t) → X) :=
  (Equiv.prodCongr (Equiv.refl _) (rectangle X n t)).trans (Fin.appendEquiv (α:=X) s (n*t))

theorem join_hold {X : Type} {s n t} (h : Fin s → X) (v : Fin n → Fin t → X) (i : Fin s) :
    joinPool X s n t (h,v) (Fin.castAdd _ i) = h i := by simp [joinPool,Fin.appendEquiv]

theorem join_trial {X : Type} {s n t} (h : Fin s → X) (v : Fin n → Fin t → X) (i : Fin n) (j : Fin t) :
    joinPool X s n t (h,v) (Fin.natAdd s (finProdFinEquiv (i,j))) = v i j := by
  have ha : joinPool X s n t (h,v) (Fin.natAdd s (finProdFinEquiv (i,j))) =
      rectangle X n t v (finProdFinEquiv (i,j)) := by simp [joinPool,Fin.appendEquiv]
  rw [ha]
  change v (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem join_mass {X : Type} {s n t : ℕ} (μ : X → ℝ) (h : Fin s → X) (v : Fin n → Fin t → X) :
    density μ (joinPool X s n t (h,v)) = density μ h * density (fun b : Fin t → X => density μ b) v := by
  unfold density
  rw [Fin.prod_univ_add]
  simp only [join_hold]
  congr 1
  rw [← finProdFinEquiv.prod_comp (fun i : Fin (n*t) => μ (joinPool X s n t (h,v) (Fin.natAdd s i)))]
  simp only [Fintype.prod_prod_type,join_trial]

/-- Marginalize the unused suffix of any polynomially padded discrete input pool. -/
theorem strip_pad {X : Type} (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (h1 : HasSum μ 1) {u v : ℕ}
    (f : (Fin u → X) → ℝ) (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) :
    (∑' b : Fin (u+v) → X, density μ b * f (fun i => b (Fin.castAdd v i))) =
      ∑' b : Fin u → X, density μ b * f b := by
  let g := fun b : Fin u → X => density μ b*f b
  have hn (b) : 0 ≤ g b := mul_nonneg (Finset.prod_nonneg (fun _ _ => hμ _)) (hf _).1
  have hs : Summable g := (iid_mass μ hμ h1 u).summable.of_nonneg_of_le hn
    (fun b => mul_le_of_le_one_right (Finset.prod_nonneg (fun _ _ => hμ _)) (hf _).2)
  have ht := iid_mass μ hμ h1 v
  have h := hs.hasSum.mul ht (hs.mul_of_nonneg ht.summable hn (fun _ => Finset.prod_nonneg (fun _ _ => hμ _)))
  let e := Fin.appendEquiv (α:=X) u v
  have he : (fun ab : (Fin u → X) × (Fin v → X) => g ab.1 * density μ ab.2) =
      (fun b : Fin (u+v) → X => density μ b * f (fun i => b (Fin.castAdd v i))) ∘ e := by
    funext ab
    simp [g,e,Fin.appendEquiv,density,Fin.prod_univ_add]
    ring
  rw [he] at h
  simpa only [g,mul_one] using (e.hasSum_iff.mp h).tsum_eq

end

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

end P2MDyadicModule45

/- Helper module Experiment. -/
section P2MDyadicModule46

set_option autoImplicit false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

noncomputable section

/-- Project an arbitrary padded-pool circuit experiment onto the held-out rows and
the marked, disjoint fresh trials. Only the conditional success of these calls is needed. -/
theorem pool_experiment {X : Type} {s n t a : ℕ} (ha : s+n*t ≤ a) (μ : X → ℝ)
    (hn : ∀ x, 0 ≤ μ x) (h1 : HasSum μ 1)
    (good : (Fin s → X) → Prop) (fail : (Fin t → X) → ℝ)
    (hf : ∀ x, 0 ≤ fail x ∧ fail x ≤ 1)
    (loss : (Fin a → X) → ℝ) (hl : ∀ y, 0 ≤ loss y ∧ loss y ≤ 1)
    (point : ∀ y,
      good (fun i => y ⟨i.val,by omega⟩) →
      loss y ≤ ∏ j : Fin n, fail (fun k : Fin t =>
        y ⟨s+(finProdFinEquiv (j,k)).val,by have := (finProdFinEquiv (j,k)).isLt; omega⟩)) :
    (∑' y : Fin a → X, density μ y * loss y) ≤
      (∑' h : Fin s → X, density μ h * (if good h then 0 else 1)) +
      (∑' x : Fin t → X, density μ x * fail x)^n := by
  classical
  obtain ⟨pad,hpad⟩ := Nat.exists_eq_add_of_le ha
  subst a
  let e := joinPool X s n t
  let proj (v : Fin (s+n*t) → X) := e.symm v
  let upper (v : Fin (s+n*t) → X) := if good (proj v).1 then ∏ i, fail ((proj v).2 i) else 1
  have hproj (v : Fin (s+n*t) → X) :
      proj v = (fun i => v (Fin.castAdd (n*t) i), fun i j => v (Fin.natAdd s (finProdFinEquiv (i,j)))) := rfl
  have hu (v) : 0 ≤ upper v ∧ upper v ≤ 1 := by
    unfold upper
    split_ifs
    · exact ⟨Finset.prod_nonneg (fun _ _ => (hf _).1),
        Finset.prod_le_one (fun _ _ => (hf _).1) (fun _ _ => (hf _).2)⟩
    · norm_num
  have hup (y : Fin (s+n*t+pad) → X) : loss y ≤ upper (fun i => y (Fin.castAdd pad i)) := by
    unfold upper; rw [hproj]; split_ifs with hg
    · exact point y hg
    · exact (hl _).2
  have hv (v : Fin (s+n*t+pad) → X) : 0 ≤ density μ v := Finset.prod_nonneg fun _ _ => hn _
  have hS : Summable (fun v : Fin (s+n*t+pad) → X => density μ v * upper (fun i => v (Fin.castAdd pad i))) :=
    (iid_mass μ hn h1 _).summable.of_nonneg_of_le
      (fun v => mul_nonneg (hv _) (hu _).1)
      (fun v => mul_le_of_le_one_right (hv _) (hu _).2)
  calc
    _ ≤ ∑' v : Fin (s+n*t+pad) → X, density μ v * upper (fun i => v (Fin.castAdd pad i)) := by
      have hh (v : Fin (s+n*t+pad) → X) := mul_le_mul_of_nonneg_left (hup v) (hv v)
      exact (hS.of_nonneg_of_le (fun v => mul_nonneg (hv _) (hl _).1) hh).tsum_le_tsum hh hS
    _ = ∑' v : Fin (s+n*t) → X, density μ v * upper v := strip_pad μ hn h1 upper hu
    _ = ∑' y : (Fin s → X) × (Fin n → Fin t → X),
          density μ y.1 * density (fun z : Fin t → X => density μ z) y.2 * upper (e y) := by
      rw [← e.tsum_eq]
      apply tsum_congr
      intro y
      rw [show density μ (e y) = _ from join_mass μ y.1 y.2]
    _ ≤ _ := by
      apply joint_failure (fun v : Fin s → X => density μ v) (fun v : Fin t → X => density μ v)
        (fun v => Finset.prod_nonneg fun i _ => hn _) (fun v => Finset.prod_nonneg fun i _ => hn _)
        (iid_mass μ hn h1 s) (iid_mass μ hn h1 t) good fail hf n (fun y => upper (e y)) (fun _ => (hu _).1)
      intro y
      unfold upper proj
      rw [Equiv.symm_apply_apply]
      by_cases hh : good y.1
      · simp [hh]
      · simp [hh,Finset.prod_nonneg (s:=Finset.univ) (f:=fun i => fail (y.2 i)) (fun _ _ => (hf _).1)]

end

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

end P2MDyadicModule46

/- Helper module Family. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbePlan

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

def qBound : Polynomial ℕ := Polynomial.C (2^17) * (Polynomial.X + 2)^64 + 1

theorem qBound_eval (n : ℕ) : qBound.eval n = 2^17*(n+2)^64+1 := by simp [qBound]

def indices (p : Polynomial ℕ) (w : Str) := List.range (RepeatedQuery.repeatSlots p w).length

@[fun_prop] theorem indices_poly (p : Polynomial ℕ) : Poly (indices p) :=
  Poly.comp (f:=fun a : List Unit => List.range a.length) (g:=RepeatedQuery.repeatSlots p)
    Poly.list_indices (RepeatedQuery.repeatSlots_poly p)

theorem indices_eq (p : Polynomial ℕ) (w : Str) : indices p w = List.range (p.eval w.length) := by
  simp [indices,RepeatedQuery.repeatSlots]

def nontrivialDivisor (w : ℕ × ℕ) : Bool :=
  decide (2 ≤ w.2) && decide (w.2 < w.1) && decide (w.1 % w.2 = 0)

@[fun_prop] theorem divisor_poly : Poly nontrivialDivisor := by unfold nontrivialDivisor; fun_prop

def testPrime (w : Str × ℕ) : Bool :=
  decide (2 ≤ w.2) && decide (((indices qBound w.1).filter
    (fun d => nontrivialDivisor (w.2,d))).length = 0)

@[fun_prop] theorem testPrime_poly : Poly testPrime := by unfold testPrime; fun_prop

theorem testPrime_iff (w : Str) (a : ℕ) (ha : a < qBound.eval w.length) :
    testPrime (w,a) = true ↔ a.Prime := by
  simp only [testPrime, Bool.and_eq_true,decide_eq_true_eq, List.length_eq_zero_iff,
    List.filter_eq_nil_iff, indices_eq, List.mem_range,nontrivialDivisor, Nat.prime_def_lt',
    Nat.dvd_iff_mod_eq_zero]
  exact and_congr_right fun _ => by
    constructor
    · intro h m hm2 hma hm
      exact h m (hma.trans ha) ⟨⟨hm2,hma⟩,hm⟩
    · rintro h m _ ⟨⟨hm,hl⟩,hd⟩
      exact h m hm hl hd

attribute [local irreducible] testPrime indices

def threshold (w : Str) : ℕ := (2^16) * (w.length+2)^64

private theorem threshold_generic (k d : ℕ) : Poly (fun w : Str => k * (w.length+2)^d) := by
  have hp : Poly (fun w : Str => (w.length+2)^d) :=
    Poly.comp (f:=fun a : ℕ => a^d) (g:=fun w : Str => w.length+2)
      (Integration9_9.LARCoinLayout.layoutNatPower_poly d) (by fun_prop)
  fun_prop

@[fun_prop] theorem threshold_poly : Poly threshold := threshold_generic _ _

attribute [local irreducible] threshold

def admitted (w : Str × ℕ) : Bool := decide (threshold w.1 ≤ w.2) && testPrime w

@[fun_prop] theorem admitted_poly : Poly admitted :=
  Poly.comp (f:=fun x : Bool × Bool => x.1 && x.2)
    (g:=fun w : Str × ℕ => (decide (threshold w.1 ≤ w.2), testPrime w)) Poly.bool_and
    (Poly.pair (Poly.nat_le_comp (Poly.comp threshold_poly Poly.fst) Poly.snd) testPrime_poly)

attribute [local irreducible] admitted

def modulus (w : Str) : ℕ :=
  (((indices qBound w).filter (fun a => admitted (w,a))).head?).getD 0

@[fun_prop] theorem modulus_poly : Poly modulus := by
  have hf : Poly (fun w : Str => (indices qBound w).filter (fun a => admitted (w,a))) :=
    Poly.list_filter admitted_poly (indices_poly qBound)
  exact Poly.comp (f:=fun xs : List ℕ => xs.head?.getD 0) (by fun_prop) hf

private theorem first_hit (l : List ℕ) (bound q : ℕ) (p : ℕ → Bool) (hl : l = List.range bound)
    (hfound : q < bound) (hit : p q = true) (hmin : ∀ j < q, p j ≠ true) :
    ((l.filter p).head?).getD 0 = q := by
  subst l
  have he : (List.range bound).find? p = some q := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hit,q,by simpa only [List.length_range] using hfound, List.getElem_range _, ?_⟩
    intro j hj
    simp only [List.getElem_range,Bool.not_eq_true']
    exact Bool.eq_false_iff.mpr (hmin j hj)
  rw [List.head?_filter,he]
  rfl

private theorem admissible_iff (w : Str) (a : ℕ) (ha : a < qBound.eval w.length) :
    admitted (w,a) = true ↔ 2^16*famL w.length^64 ≤ a ∧ a.Prime :=
  by simp only [admitted,Bool.and_eq_true,decide_eq_true_eq,threshold,famL,testPrime_iff _ _ ha]

private theorem found_spec (n : ℕ) : 2^16*famL n^64 ≤ famq n ∧ (famq n).Prime :=
  Nat.find_spec (Nat.exists_infinite_primes (2^16*famL n^64))

private theorem found_min (n a : ℕ) (h : 2^16*famL n^64 ≤ a ∧ a.Prime) : famq n ≤ a :=
  Nat.find_min' (Nat.exists_infinite_primes (2^16*famL n^64)) h

private theorem inside (n : ℕ) : famq n < qBound.eval n := by
  rw [qBound_eval]; exact Nat.lt_succ_of_le (famq_le_explicit_polynomial _)

theorem modulus_eq (w : Str) : modulus w = famq w.length :=
  first_hit (indices qBound w) (qBound.eval w.length) (famq w.length) (fun a => admitted (w,a))
    (indices_eq _ _) (inside _) ((admissible_iff _ _ (inside _)).2 (found_spec _))
    (fun j hj he => (Nat.not_le_of_gt hj) (found_min _ j ((admissible_iff _ _ (hj.trans (inside _))).1 he)))

attribute [local irreducible] modulus

def rowCount (w : Str) : ℕ := modulus w*(w.length+2)^96 + 2*(w.length+2)^128

@[fun_prop] theorem rowCount_poly : Poly rowCount := by unfold rowCount; fun_prop

theorem rowCount_eq (w : Str) : rowCount w = famd w.length := by simp [rowCount,famd,famL,modulus_eq]

def pp (w : Str) : Str := encB (modulus w) ++ encB w.length ++ encB (rowCount w) ++ encB (w.length+2)

@[fun_prop] theorem pp_poly : Poly pp := by unfold pp; fun_prop

theorem pp_eq (w : Str) : pp w = famPP w.length := by simp [pp,famPP,famN,famσ,famL,rowCount_eq,modulus_eq]

end

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule47

/- Helper module Flatten. -/
section P2MDyadicModule48

set_option autoImplicit false

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

noncomputable section

theorem complement_mass {X : Type} (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (h1 : HasSum ρ 1)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    (∑' x,ρ x*(1-f x)) = 1-(∑' x,ρ x*f x) := by
  have hs : Summable (fun x => ρ x*f x) := h1.summable.of_nonneg_of_le
    (fun x => mul_nonneg (hρ _) (hf _).1) (fun x => mul_le_of_le_one_right (hρ _) (hf _).2)
  simp_rw [mul_sub,mul_one]
  rw [h1.summable.tsum_sub hs,h1.tsum_eq]

theorem good_complement {X : Type} (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (h1 : HasSum ρ 1)
    (good : X → Prop) :
    (∑' x, ρ x*(if good x then 0 else 1)) = 1-(∑' x,ρ x*(if good x then 1 else 0)) := by
  classical
  convert complement_mass ρ hρ h1 (fun x => if good x then 1 else 0) (fun x => by split <;> norm_num) using 1
  apply tsum_congr
  intro x
  split <;> simp

end

end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit

end P2MDyadicModule48

/- Helper module ResidueNative. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch.Holdout

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

private theorem inputLattice_eq_inputModule {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) :
    inputLattice D hD = inputModule D := by
  unfold inputLattice inputModule
  congr 1
  apply congrArg Set.range
  funext i
  rw [realBasis_apply]
  simp [latVec, Matrix.mulVec_single]

private theorem odd_iff_mod_two {z : ℤ} : Odd z ↔ (z : ZMod 2) = 1 := by
  rw [Int.odd_iff]
  constructor
  · intro h
    simpa [h] using (ZMod.intCast_mod z 2).symm
  · intro h
    have ha : (z % 2 : ℤ) = 0 ∨ z % 2 = 1 := by omega
    rcases ha with ha | ha
    · have hbad : (0 : ZMod 2) = 1 := by simpa [ha, h] using ZMod.intCast_mod z 2
      exact (zero_ne_one hbad).elim
    · exact ha

private theorem mod_two_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  have hn : v.val = 0 ∨ v.val = 1 := by have := ZMod.val_lt v; omega
  rw [← ZMod.natCast_zmod_val v]
  rcases hn with h | h <;> simp [h]

private theorem uniform_mod_two_coordinate {n : ℕ} (i : Fin n) :
    ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1),
      (FiniteDist.uniform (Fin n → ZMod 2)).weight c = (1/2 : ℝ) := by
  classical
  let e : (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) := Equiv.addRight (Pi.single i 1)
  let f := (FiniteDist.uniform (Fin n → ZMod 2)).weight
  have hs : ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1), f c =
      ∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => ¬ c i = 1), f c := by
    apply Finset.sum_equiv e
    · intro c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have he : (e c) i = c i + 1 := by simp [e, Equiv.addRight]
      rw [he]
      rcases mod_two_cases (c i) with h | h <;> simp [h]
    · intro c _
      rfl
  have hup := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → ZMod 2))
    (fun c => c i = 1) f
  rw [(FiniteDist.uniform (Fin n → ZMod 2)).sum_one, ← hs] at hup
  exact (by linarith : (∑ c ∈ Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1), f c) = 1/2)

private theorem smoothingError_pos_small (n : ℕ) (hn : 2 ≤ n) :
    0 < smoothingError n ∧ smoothingError n ≤ 1/256 := by
  unfold smoothingError
  refine ⟨by positivity, ?_⟩
  have hsize : 2 < Nat.size (n+2) := Nat.lt_size.mpr (by omega)
  have hs : 8 ≤ (Nat.size (n+2))^2 := by
    have ha : 3 ≤ Nat.size (n+2) := hsize
    have hb := Nat.pow_le_pow_left ha 2
    exact (by decide : 8 ≤ 3^2) |>.trans hb
  calc
    1/(2 : ℝ) ^ (Nat.size (n+2))^2 ≤ 1/(2:ℝ)^8 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hs)
    _ = _ := by norm_num

theorem residue_event {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (r : ℝ) (hr : 0 < r)
    (hs : 2 * smoothingParam (inputModule D) (smoothingError n) ≤ r)
    (t : Finset (Fin n → ZMod 2)) :
    (∀ z, 0 ≤ coefficientMass D r z) ∧ HasSum (coefficientMass D r) 1 ∧
    |(∑' z : Fin n → ℤ, if (fun j => (z j : ZMod 2)) ∈ t then coefficientMass D r z else 0) -
      ∑ c ∈ t, (FiniteDist.uniform (Fin n → ZMod 2)).weight c| ≤
      2 * (smoothingError n / (1 - smoothingError n)) := by
  classical
  let L := inputLattice D hD
  let b := integerBasis D hD
  let e : (Fin n → ℤ) ≃ L := b.equivFun.symm.toEquiv
  let ε := smoothingError n
  obtain ⟨hε, hεsmall⟩ : 0 < ε ∧ ε ≤ 1/256 := smoothingError_pos_small n hn
  have hε1 : ε < 1 := by linarith
  have hL : smoothingParam L ε ≤ r/2 := by
    rw [← inputLattice_eq_inputModule D hD] at hs
    change 2 * smoothingParam L ε ≤ r at hs
    linarith
  have hLr : smoothingParam L ε ≤ r := by linarith
  have hr2 : 0 < r/2 := by positivity
  have hM : smoothingParam (modulusLattice 2 L) ε ≤ r := by
    simpa [modulusLattice, show 2 * (r / 2) = r by ring] using
      (dilation_smoothing_le L 2 (r/2) ε (by norm_num) hr2 hε hL)
  let source := cosetPMF L 0 hr hε hε1 hLr
  let actual := coefficientLaw 2 L b hr hε hε1 hLr
  let reference := FiniteDist.uniform (Fin n → ZMod 2)
  have he (z : Fin n → ℤ) : (e z : EuclideanSpace ℝ (Fin n)) = latVec D z := coefficient_point D hD z
  have hz : (∑' z : Fin n → ℤ, rho r (latVec D z)) = rhoCoset r L 0 := by
    have h := e.tsum_eq (fun x : L => rho r (x : EuclideanSpace ℝ (Fin n)))
    simpa only [rhoCoset, add_zero, he] using h
  have hm (z : Fin n → ℤ) : coefficientMass D r z = (source (e z)).toReal := by
    rw [show (source (e z)).toReal = _ from cosetPMF_toReal L 0 hr hε hε1 hLr (e z)]
    rw [cosetMass_formula, add_zero]
    change rho r (latVec D z) / (∑' y : Fin n → ℤ, rho r (latVec D y)) = _
    rw [hz, he]
  have hm0 (z) : 0 ≤ coefficientMass D r z := hm z ▸ ENNReal.toReal_nonneg
  have hms : HasSum (coefficientMass D r) 1 := by
    have hx := (pmf_realMass_summable source).hasSum
    rw [pmf_realMass_sum] at hx
    rw [show coefficientMass D r = (fun x => (source x).toReal) ∘ e from funext hm]
    exact e.hasSum_iff.mpr hx
  refine ⟨hm0, hms, ?_⟩
  have hTV : (∑ c, |actual.weight c - reference.weight c|) / 2 ≤ ε/(1-ε) :=
    coefficientLaw_uniform 2 L b hr hε hε1 hLr hM
  have hbound : |(∑ c ∈ t, actual.weight c) - (∑ c ∈ t, reference.weight c)| ≤ 2*(ε/(1-ε)) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c ∈ t, |actual.weight c - reference.weight c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, |actual.weight c - reference.weight c| := Finset.sum_le_univ_sum_of_nonneg (fun _ => abs_nonneg _)
      _ ≤ _ := by linarith
  suffices h : (∑ c ∈ t, actual.weight c) =
      (∑' z : Fin n → ℤ, if (fun j => (z j : ZMod 2)) ∈ t then coefficientMass D r z else 0) by
    rwa [← h]
  let fn : (Fin n → ZMod 2) → L → ℝ := fun c x =>
    if publicCoordinates 2 L b x = c then (source x).toReal else 0
  have hf (c) : Summable (fn c) := by
    apply (pmf_realMass_summable source).of_nonneg_of_le
    · intro x; dsimp [fn]; split <;> positivity
    · intro x; dsimp [fn]; split <;> simp [ENNReal.toReal_nonneg]
  have hw (c) : actual.weight c = ∑' x, fn c x := by
    change (AFT.GaussianSource.finiteLaw (source.map (publicCoordinates 2 L b))).weight c = _
    rw [Integration.finiteLaw_map_weight]
    apply tsum_congr; intro x
    by_cases h : publicCoordinates 2 L b x = c <;> simp [fn, h]
  simp_rw [hw]
  rw [← Summable.tsum_finsetSum (fun c _ => hf c)]
  rw [← e.tsum_eq (fun x : L => ∑ c ∈ t, fn c x)]
  apply tsum_congr
  intro z
  dsimp only [fn]
  have hsingle : ∑ c ∈ t, (if publicCoordinates 2 L b (e z) = c then (source (e z)).toReal else 0) =
      if publicCoordinates 2 L b (e z) ∈ t then (source (e z)).toReal else 0 := by
    rw [Finset.sum_ite_eq]
  rw [hsingle, ← hm]
  congr 1
  have hpc : publicCoordinates 2 L b (e z) = fun j => (z j : ZMod 2) := publicCoordinates_coefficient_point 2 D hD z
  rw [hpc]

theorem odd_coordinate {n : ℕ} (hn : 2 ≤ n)
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (r : ℝ) (hr : 0 < r)
    (hs : 2 * smoothingParam (inputModule D) (smoothingError n) ≤ r) (i : Fin n) :
    |(∑' z : Fin n → ℤ, if Odd (z i) then coefficientMass D r z else 0) - (1/2:ℝ)| ≤
      2 * (smoothingError n / (1 - smoothingError n)) := by
  classical
  let t := Finset.univ.filter (fun c : Fin n → ZMod 2 => c i = 1)
  have H := (residue_event hn D hD r hr hs t).2.2
  rw [show (∑ c ∈ t, (FiniteDist.uniform (Fin n → ZMod 2)).weight c) = 1/2 from uniform_mod_two_coordinate i] at H
  convert H using 3
  apply tsum_congr
  intro z
  simp only [t, Finset.mem_filter, Finset.mem_univ, true_and, odd_iff_mod_two]

end InfoLossLAR.WorstCase.RegevSketch.Holdout

end P2MDyadicModule49

/- Helper module RankNative. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch.Holdout

open RegevLWE.GaussConv

def gramDet {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) : ℤ := (C.transpose*C).det

theorem threshold {n : ℕ} (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℝ) (hr : 0 < r) (hs : dgsThreshold B ≤ r) :
    2*smoothingParam (inputModule B) (smoothingError n) ≤ r := by
  let η := smoothingParam (inputModule B) (smoothingError n)
  change 2*η ≤ r
  by_cases heta : η ≤ 0
  · linarith
  have hq : n+2 ≤ famq n := by
    have h := (Nat.find_spec (Nat.exists_infinite_primes (2^16 * famL n ^64))).1
    change 2^16 * famL n^64 ≤ famq n at h
    have hx : (famL n)^1 ≤ (famL n)^64 := Nat.pow_le_pow_right (by unfold famL; omega) (by decide)
    simp only [pow_one,famL] at hx
    unfold famL at h
    omega
  have hq' : (n:ℝ)+2 ≤ (famq n:ℝ) := by exact_mod_cast hq
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hss : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn'
  have hfactor : 2 ≤ 16*(famq n:ℝ)*Real.sqrt n/(famσ n:ℝ) := by
    rw [le_div_iff₀ (by unfold famσ famL; positivity)]
    have hprod := mul_le_mul_of_nonneg_left hss (show 0 ≤ 16*(famq n:ℝ) by positivity)
    simp [famσ,famL] at *
    linarith
  exact (mul_le_mul_of_nonneg_right hfactor (le_of_not_ge heta)).trans hs

theorem gram_of_minor {n m : ℕ} (C : Matrix (Fin m) (Fin n) ℤ)
    (pick : Fin n → Fin m) (hdet : (C.submatrix pick id).det ≠ 0) :
    (C.transpose*C).det ≠ 0 := by
  classical
  let X := C.map (Int.castRingHom ℚ)
  have hminor : (X.submatrix pick id).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix (C.submatrix pick id)).det ≠ 0
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr hdet
  have hinj : Function.Injective X.mulVec := by
    intro a b hab
    apply Matrix.mulVec_injective_of_det_ne_zero hminor
    exact funext (fun i => congrFun hab (pick i))
  have hg : Function.Injective (X.transpose * X).mulVecLin := by
    rw [←LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_transpose_mul_self]
    exact LinearMap.ker_eq_bot.mpr hinj
  have hg' := ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hg)).ne_zero
  intro h
  apply hg'
  have heq : (Int.castRingHom ℚ).mapMatrix (C.transpose*C) = X.transpose*X := Matrix.map_mul
  rw [←heq,←RingHom.map_det,h,map_zero]

theorem sivp_coeff_det_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (Z : Matrix (Fin n) (Fin n) ℤ) :
    Z.det ≠ 0 ↔ LinearIndependent ℝ (fun i => latVec B (Z i)) := by
  let R : Matrix (Fin n) (Fin n) ℝ := Z.map (Int.castRingHom ℝ)
  let e := (IntegerBasis.coordinateEquiv B hB).toLinearEquiv
  have he (i : Fin n) : e (R i) = latVec B (Z i) := by
    change IntegerBasis.coordinateEquiv B hB (R i) = latVec B (Z i)
    rw [IntegerBasis.coordinateEquiv_apply]
    apply congrArg (WithLp.toLp 2)
    ext j
    unfold Matrix.mulVec dotProduct IntegerBasis.realMatrix R
    push_cast
    simp
  have hd : R.det = (Z.det : ℝ) := (RingHom.map_det (Int.castRingHom ℝ) Z).symm
  have hdet : R.det ≠ 0 ↔ Z.det ≠ 0 := by rw [hd, Int.cast_ne_zero]
  constructor
  · intro hz
    have hR : LinearIndependent ℝ (fun i => R i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (hdet.mpr hz)
    rw [← funext he]
    exact hR.map' e.toLinearMap e.ker
  · intro hv
    have hR : LinearIndependent ℝ (fun i => R i) := by
      apply LinearIndependent.of_comp (f := e.toLinearMap)
      simpa only [Function.comp_def, LinearEquiv.coe_coe, he] using hv
    exact hdet.mp ((Matrix.isUnit_iff_isUnit_det R).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hR)).ne_zero

theorem public_gram_failure : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
  ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
   (∑' C : Fin (16*(n+1)^2) → Fin n → ℤ,
     (∏ i, coefficientMass B r (C i))*(if gramDet C = 0 then 1 else 0)) ≤ (1/2:ℝ)^n := by
  classical
  obtain ⟨N,hN⟩ := dgs_pool_rank_failure
  refine ⟨max N 2,?_⟩
  intro n hn hn' B hB r hr hR
  let m := 16*(n+1)^2
  let mass (C : Fin m → Fin n → ℤ) := ∏ i, coefficientMass B r (C i)
  have hlo := (residue_event (by omega : 2 ≤ n) B hB r hr (threshold hn' B r hr hR) ∅).1
  have hnorm := (residue_event (by omega : 2 ≤ n) B hB r hr (threshold hn' B r hr hR) ∅).2.1
  have h0 C : 0 ≤ mass C := Finset.prod_nonneg (fun i _ => hlo (C i))
  have hs' := GaussianPoissonSeries.finiteProductMass_hasSum m (coefficientMass B r) hlo hnorm.summable
  let bad (C : Fin m → Fin n → ℤ) := ¬ ∃ pick : Fin n → Fin m, LinearIndependent ℝ (fun i => latVec B (C (pick i)))
  have himp (C : Fin m → Fin n → ℤ) (hg : gramDet C=0) : bad C := by
    rintro ⟨pick,hp⟩
    exact gram_of_minor C pick ((sivp_coeff_det_iff B hB (Matrix.submatrix C pick id)).mpr hp) hg
  let restricted (P : (Fin m → Fin n → ℤ) → Prop) C := mass C*(if P C then 1 else 0)
  have hsum (P) : Summable (restricted P) := hs'.summable.of_nonneg_of_le
    (fun C => by dsimp only [restricted]; split <;> simp [h0])
    (fun C => by change restricted P C ≤ mass C; dsimp only [restricted]; split <;> simp [h0])
  have hle : ∀ C, restricted (fun C => gramDet C = 0) C ≤ restricted bad C := by
    intro C
    by_cases h : gramDet C=0
    · simp [restricted,h,himp C h]
    · by_cases hb : bad C <;>simp [restricted,h,hb,h0]
  refine le_trans ?_ (hN n (by omega) hn' B hB r hr hR)
  have h := (hsum _).tsum_le_tsum hle (hsum _)
  convert h using 1 <;> apply tsum_congr <;> intro C <;> dsimp only [restricted,mass,bad] <;>
    split_ifs <;> rfl

end InfoLossLAR.WorstCase.RegevSketch.Holdout

end P2MDyadicModule50

/- Helper module HoldoutNative. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 900000

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch.Holdout

open RegevLWE.GaussConv

def cutoffGood {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℝ) (C : Fin m → Fin n → ℤ) : Prop :=
  gramDet C ≠ 0 ∧ ∀ i, ‖latVec B (C i)‖ ≤ 2*r*Real.sqrt n

theorem threshold_of_wide {n : ℕ} (hn : 256 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℝ) (hr : 0 < r)
    (hwide : Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < r) :
    dgsThreshold B ≤ r := by
  let η := smoothingParam (inputModule B) (smoothingError n)
  change 16*(famq n : ℝ) * Real.sqrt n / (famσ n:ℝ) * η ≤ r
  change Real.sqrt 2 * (famq n:ℝ) * η < r at hwide
  by_cases heta : η ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) heta).trans hr.le
  have hn' : (256:ℝ) ≤ n := by exact_mod_cast hn
  have h16 : 16 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; linarith)
  have hmul := mul_le_mul_of_nonneg_right h16 (Real.sqrt_nonneg n)
  rw [Real.mul_self_sqrt (by positivity)] at hmul
  have hs : 16*Real.sqrt n ≤ (famσ n:ℝ) := by simp [famσ,famL]; linarith
  have qs : 16*(famq n:ℝ)*Real.sqrt n/(famσ n:ℝ) ≤ (famq n:ℝ) := by
    rw [div_le_iff₀ (by unfold famσ famL; positivity)]
    simpa [mul_left_comm,mul_assoc,mul_comm] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (famq n))
  have hsqrt : (1:ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  exact (mul_le_mul_of_nonneg_right (qs.trans (le_mul_of_one_le_left (by positivity) hsqrt)) (le_of_not_ge heta)).trans hwide.le

theorem short_spanning : ∃ N : ℕ, ∀ n ≥ N, ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
    ∀ r : ℝ, 0 < r → dgsThreshold B ≤ r →
    let m := 16*(n+1)^2
    HasSum (fun C : Fin m → Fin n → ℤ => ∏ i, coefficientMass B r (C i)) 1 ∧
    1 - ((1/2:ℝ)^n + (16*((n:ℝ)+1)^2)*(1/4:ℝ)^n) ≤
      ∑' C : Fin m → Fin n → ℤ, (∏ i, coefficientMass B r (C i)) * (if cutoffGood B r C then 1 else 0) := by
  classical
  obtain ⟨N,hN⟩ := dgs_pool_gaussian_tail
  obtain ⟨K,hK⟩ := public_gram_failure
  refine ⟨max K (max N 2),?_⟩
  intro n hn B hB r hr hR
  let m := 16*(n+1)^2
  let μ (C : Fin m → Fin n → ℤ) := ∏ i, coefficientMass B r (C i)
  let rankBad (C : Fin m → Fin n → ℤ) := gramDet C = 0
  let tailBad (C : Fin m → Fin n → ℤ) := ∃ i, 2*Real.sqrt n*r < ‖latVec B (C i)‖
  let cut (P : (Fin m → Fin n → ℤ) → Prop) C := μ C * (if P C then (1:ℝ) else 0)
  have hn2 : 2 ≤ n := by omega
  have hs := threshold (by omega : 1 ≤ n) B r hr hR
  obtain ⟨hS,hTail⟩ := hN n (by omega) (by omega) B hB r hr hR
  refine ⟨hS,?_⟩
  have h0 := (residue_event hn2 B hB r hr hs ∅).1
  have hμ (C) : 0 ≤ μ C := Finset.prod_nonneg (fun i _ => h0 (C i))
  have hcut (P) : Summable (cut P) := hS.summable.of_nonneg_of_le
    (fun C => by dsimp [cut]; split <;> simp [hμ]) (fun C => by change cut P C ≤ μ C; dsimp only [cut]; split <;> simp [hμ])
  have hpoint (C) : μ C ≤ cut (cutoffGood B r) C + cut rankBad C + cut tailBad C := by
    by_cases hh : cutoffGood B r C
    · have hR' : ¬ rankBad C := hh.1
      have hT' : ¬ tailBad C := by rintro ⟨i,hi⟩; linarith [hh.2 i]
      simp [cut,hh,hR',hT']
    · by_cases ha : rankBad C
      · by_cases hb : tailBad C <;> simp [cut,hh,ha,hb,hμ]
      · have hb : tailBad C := by
          by_contra! hno
          apply hh
          refine ⟨ha,fun i => ?_⟩
          have hi : ¬2*Real.sqrt n*r < ‖latVec B (C i)‖ := fun h => hno ⟨i,h⟩
          linarith
        simp [cut,hh,ha,hb]
  have htotal := hS.summable.tsum_le_tsum hpoint (((hcut _).add (hcut _)).add (hcut _))
  rw [hS.tsum_eq, ((hcut _).add (hcut _)).tsum_add (hcut _), (hcut _).tsum_add (hcut _)] at htotal
  have hRank := hK n (by omega) (by omega) B hB r hr hR
  have hR' : (∑' C, cut rankBad C) ≤ (1/2:ℝ)^n := by
    refine le_trans (le_of_eq (tsum_congr (fun C => ?_))) hRank
    dsimp only [cut,rankBad,μ]
    split_ifs <;> rfl
  have hT' : (∑' C, cut tailBad C) ≤ 16*((n:ℝ)+1)^2*(1/4:ℝ)^n := by
    refine le_trans (le_of_eq (tsum_congr (fun C => ?_))) hTail
    dsimp only [cut,tailBad,μ]
    split_ifs <;> first | rfl | contradiction
  change _ ≤ ∑' C, cut (cutoffGood B r) C
  linarith

end InfoLossLAR.WorstCase.RegevSketch.Holdout

end P2MDyadicModule51

/- Helper module PoolInput. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbePlan

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.LARPlatformEncoding (readS readS_append readB_rest_length readBinaryList readBinaryList_poly readBinaryList_append_mapped encB_length_pos)

open Integration9_9.TM2NativeAffineEncoding (readMatrix readMatrix_append readInteger_rest_length)

open GaussianRandomizedRounding.Wide.Coherent (readRational readRational_poly readRational_append)

abbrev Data := (List (List ℤ) × List ℚ) × List (List ℤ)

def parts (a : Str) := ((readS a).2,(readS (readS a).1).2)

@[fun_prop] theorem parts_poly : Poly parts := by unfold parts; fun_prop

@[simp] theorem parts_pair (a b : Str) : parts (encPair a b) = (a,b) := by
  have h : readS (encS b) = ([],b) := by simpa using readS_append b []
  simp [parts,encPair,readS_append,h]

def ratVector : Str → Str × List ℚ := readBinaryList readRational

@[fun_prop] theorem ratVector_poly : Poly ratVector :=
  readBinaryList_poly _ readRational_poly (fun a => (readB_rest_length _).trans (readInteger_rest_length a))

theorem ratVector_append (vs : List ℚ) (a : Str) : ratVector (encL encQ vs ++ a)=(a,vs) := by
  have h := readBinaryList_append_mapped readRational encQ id
    (fun v => (encB_length_pos v.den).trans_le (by simp [encQ])) readRational_append vs a
  simpa only [ratVector,List.map_id] using h

def parse (w : Str) : Data :=
  let ab := parts w
  let cx := parts (parts (parts ab.2).2).2
  (((readMatrix ab.1).2, (ratVector cx.2).2), (readMatrix cx.1).2)

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

theorem parse_correct {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (pool : Fin m → Fin n → ℤ) (x : Fin n → ℚ) :
    parse (encPair (encMat encI B) (encPair (encQ R) (encPair (unary k)
      (encPair (encVec (encVec encI) pool) (encVec encQ x))))) =
      ((List.ofFn fun i => List.ofFn (B i), List.ofFn x),List.ofFn fun i => List.ofFn (pool i)) := by
  simp only [parse,parts_pair]
  rw [←List.append_nil (encMat encI B),readMatrix_append, ←List.append_nil (encVec encQ x)]
  rw [show ratVector (encVec encQ x ++ [])=([],List.ofFn x) from ratVector_append (List.ofFn x) []]
  rw [←List.append_nil (encVec (encVec encI) pool)]
  have hp : (readMatrix (encVec (encVec encI) pool ++ [])).2 = List.ofFn (fun i => List.ofFn (pool i)) :=
    congrArg (fun p : Str × List (List ℤ) => p.2) (readMatrix_append (Matrix.of pool) [])
  rw [hp]

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule52

/- Helper module Plan. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbePlan

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

noncomputable section

def security (d : Data) : Str := d.1.1.map (fun _ => true)

@[fun_prop] theorem security_poly : Poly security := by unfold security; fun_prop

def scalarRows (p : Polynomial ℕ) (d : Data) : ℕ := p.eval d.1.1.length * rowCount (security d)

@[fun_prop] theorem scalarRows_poly (p : Polynomial ℕ) : Poly (scalarRows p) := by unfold scalarRows; fun_prop

def grid (p : Polynomial ℕ) (d : Data) : ℕ := 768 * (scalarRows p d + 1)

@[fun_prop] theorem grid_poly (p : Polynomial ℕ) : Poly (grid p) := by unfold grid; fun_prop

def hold (n : ℕ) := 16*((n+1)*(n+1))

@[fun_prop] theorem hold_poly : Poly hold := by unfold hold; fun_prop

def tapeBits (p : Polynomial ℕ) (d : Data) : ℕ :=
  let m := grid p d
  (m+1) + (2*((d.1.1.length+2)*m)+1) + 1

@[fun_prop] theorem tapeBits_poly (p : Polynomial ℕ) : Poly (tapeBits p) := by unfold tapeBits; fun_prop

def slice (z : (List (List ℤ) × ℕ) × ℕ) := (z.1.1.drop z.1.2).take z.2

@[fun_prop] theorem slice_poly : Poly slice := by
  unfold slice
  exact Poly.comp parser_take_poly (Poly.pair (Poly.comp parser_drop_poly (by fun_prop)) (by fun_prop))

def slots (z : List (List ℤ) × ℕ) := (z.1.take z.2).map (fun _ => ())

@[fun_prop] theorem slots_poly : Poly slots := by
  unfold slots
  exact Poly.list_map (by fun_prop) parser_take_poly

def oddBit (a : List ℤ) : Bool := decide ((a.head?.getD 0).natAbs % 2 = 1)

@[fun_prop] theorem oddBit_poly : Poly oddBit := by unfold oddBit; fun_prop

def variance (a : (ℕ × ℕ) × ℕ) : ℚ :=
  let s : ℚ := a.1.1
  (s*s) - ((s*s)/2)*(a.2:ℚ)/(a.1.2:ℚ)

@[fun_prop] theorem variance_poly : Poly variance := by unfold variance; fun_prop

attribute [local irreducible] rowCount modulus pp scalarRows grid security hold tapeBits slots slice variance

def observedRequest (p : Polynomial ℕ) (z : Data × ℕ) : NativeLWETableLoader.ObservedRequest :=
  let d := z.1
  let n := d.1.1.length
  let s := n+2
  let m := grid p d
  let rawRows := scalarRows p d
  let coinCount := rawRows*tapeBits p d
  let offset := hold n + (z.2 % n)*(rawRows+coinCount)
  let entries := slice ((d.2,offset),rawRows)
  let tape := (slice ((d.2,offset+rawRows),coinCount)).map oddBit
  let ctx : NativeLWETableLoader.Context :=
    (d.1,(modulus (security d), (variance ((s,m),z.2/n),(slots (d.2,s*m),slots (d.2,m)))))
  ((security d,pp (security d)), ((slots (d.2,p.eval n),slots (d.2,rowCount (security d))),
    ((ctx,entries),tape)))

@[fun_prop] theorem observedRequest_poly (p : Polynomial ℕ) : Poly (observedRequest p) := by
  unfold observedRequest; fun_prop

def requests (p : Polynomial ℕ) (w : Str) : List Str :=
  let d := parse w
  let tasks := slots (d.2,(grid p d+1)*d.1.1.length)
  (List.range tasks.length).map (fun i => NativeLWETableLoader.observed (observedRequest p (d,i)))

@[fun_prop] theorem requests_poly (p : Polynomial ℕ) : Poly (requests p) := by
  unfold requests
  apply Poly.list_map
  · exact Poly.comp NativeLWETableLoader.observed_poly
      (Poly.comp (observedRequest_poly p) (by fun_prop))
  · exact Poly.comp (f:=fun xs : List Unit => List.range xs.length) Poly.list_indices (by fun_prop)

end

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule53

/- Helper module PlanSemantics. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option maxHeartbeats 1500000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbePlan

open QAlgorithms.Complexity NativeLWETableLoader

noncomputable section

def data {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (C : Fin a → Fin n → ℤ) : Data :=
  ((List.ofFn (fun i => List.ofFn (B i)),List.ofFn x),List.ofFn fun i => List.ofFn (C i))

theorem sec_data {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (C : Fin a → Fin n → ℤ) :
    security (data B x C) = unary n := by simp [security,data,unary]

@[simp] theorem data_basis {n a} (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (C : Fin a → Fin n → ℤ) :
    (data B x C).1.1 = List.ofFn (fun i => List.ofFn (B i)) := rfl

@[simp] theorem data_pool {n a} (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (C : Fin a → Fin n → ℤ) :
    (data B x C).2 = List.ofFn (fun i => List.ofFn (C i)) := rfl

theorem slots_exact {n k : ℕ} (C : Fin n → List ℤ) (h : k ≤ n) :
    slots (List.ofFn C,k) = List.replicate k () := by
  unfold slots
  rw [List.map_const']
  simp [h]

theorem slice_exact {a n start len : ℕ} (C : Fin a → Fin n → ℤ) (h : start+len ≤ a) :
    slice ((List.ofFn (fun i => List.ofFn (C i)),start),len) =
      List.ofFn (fun i : Fin len => List.ofFn (C ⟨start+i.val,by omega⟩)) := by
  apply List.ext_getElem
  · simp [slice]; omega
  · intro i hi hj
    simp [slice]

abbrev gridVar (p : Polynomial ℕ) (n idx : ℕ) : ℚ :=
  ((n+2:ℕ):ℚ)^2 - (((n+2:ℕ):ℚ)^2/2)*(idx:ℚ)/(widths p n:ℚ)

def localRequest {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ)
    (C : Fin a → Fin n → ℤ) (idx trial : ℕ)
    (h : saved n + trial*trialSize p n + trialSize p n ≤ a) : ObservedRequest :=
  let off := saved n + trial*trialSize p n
  let r := rows p n
  let w := widths p n
  let c := cutoffSize p n
  have bound : off+r+r*coinWidth p n ≤ a := by simpa only [off,r,trialSize,add_assoc] using h
  let entries : Fin r → Fin n → ℤ := fun j : Fin r => C ⟨off+j.val, by omega⟩
  let coins := fun j : Fin (r*coinWidth p n) =>
    oddBit (List.ofFn (C ⟨off+r+j.val, by omega⟩))
  ((unary n,famPP n),((List.replicate (p.eval n) (),List.replicate (famd n) ()),
    ((numericalContext B x (famq n) (gridVar p n idx) c w,List.ofFn fun j => List.ofFn (entries j)), List.ofFn coins)))

theorem observedRequest_at {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℚ) (C : Fin a → Fin n → ℤ) (idx : ℕ) (j : Fin n)
    (huse : used p n ≤ a) (hcut : cutoffSize p n ≤ a) (hwidth : widths p n ≤ a)
    (hrows : famd n ≤ a) (hblocks : p.eval n ≤ a) :
    let h : saved n + j.val*trialSize p n + trialSize p n ≤ a := by
      have hm := Nat.mul_le_mul_right (trialSize p n) j.isLt
      dsimp only [used] at huse
      rw [Nat.succ_mul] at hm
      omega
    observedRequest p (data B x C, idx*n+j.val) = localRequest p B x C idx j.val h := by
  intro h
  have hn : 0<n := Nat.zero_lt_of_lt j.isLt
  have hn' : (unary n).length = n := by simp [unary]
  have hs : scalarRows p (data B x C) = rows p n := by
    simp only [scalarRows,sec_data,rowCount_eq,hn',data_basis,List.length_ofFn,rows]
  have hm : grid p (data B x C) = widths p n := by simp only [grid,hs,widths]
  have hb : tapeBits p (data B x C) = coinWidth p n := by
    simp only [tapeBits,hm,data_basis,List.length_ofFn,coinWidth,cutoffSize]
  have hmod : (idx*n+j.val)%n=j.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have hdiv : (idx*n+j.val)/n=idx := by rw [Nat.mul_comm idx n,Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt,add_zero]
  have h1 : saved n+j.val*trialSize p n+rows p n ≤ a := by dsimp [trialSize] at h ⊢; omega
  have h2 : saved n+j.val*trialSize p n+rows p n+rows p n*coinWidth p n ≤ a := by
    simpa only [trialSize,add_assoc] using h
  have hsave : hold n = saved n := by simp [hold,saved,pow_two]
  unfold observedRequest
  simp only [hm,hs,hb,sec_data,pp_eq,modulus_eq,rowCount_eq,hn',data_basis,data_pool,List.length_ofFn, hsave,hmod,hdiv]
  change _ = localRequest p B x C idx j.val h
  unfold localRequest numericalContext
  simp only [show (n+2)*widths p n = cutoffSize p n from rfl,slots_exact _ hcut,slots_exact _ hwidth,slots_exact _ hrows,slots_exact _ hblocks]
  simp only [trialSize] at h1 h2
  rw [slice_exact _ h1,slice_exact _ h2]
  simp only [List.map_ofFn,Function.comp_def,variance,gridVar,pow_two]
  rfl

end

end InfoLossLAR.WorstCase.ShortProbePlan

end P2MDyadicModule54

/- Helper module Post. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option maxHeartbeats 1200000

namespace InfoLossLAR.WorstCase.ShortProbe

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

noncomputable section

abbrev Candidate := List ℚ × List ℤ

abbrev PostInput := ProbeInput × List Str

def probeCount (n : ℕ) : ℕ := 16*(n+1)^2

def probes (w : ProbeInput) : ProbeInput :=
  (w.1,w.2.take (probeCount w.1.1.1.length))

@[fun_prop] theorem probes_poly : Poly probes := by
  unfold probes
  refine Poly.pair (by fun_prop) ?_
  exact Poly.comp (f := fun p : List (List ℤ) × ℕ => p.1.take p.2)
      ⟨PolyProgram.listTake enc []⟩ (Poly.pair (by fun_prop) (by fun_prop))

def candidates (w : PostInput) : List Candidate :=
  w.2.map (fun raw => recover (probes w.1,(readVector raw).2))

@[fun_prop] theorem candidates_poly : Poly candidates := by unfold candidates;fun_prop

def pairCode (p : Candidate) : Str := encPair (encL encQ p.1) (encL encI p.2)

theorem encL_poly {α : Type} [Coding α] [Inhabited α] (f : α → Str)
    (h : Poly f) : Poly (encL f) := by
  have h' : Poly (fun vs : List α => serializeBinaryWords (vs.map f)) :=
    Poly.comp serializeBinaryWords_poly (Poly.list_map (Poly.comp h Poly.snd) Poly.identity)
  simpa only [serializeBinaryWords_map] using h'

@[fun_prop] theorem ratCode_poly : Poly encQ := by unfold encQ;fun_prop

@[fun_prop] theorem pairCode_poly : Poly pairCode := by
  have hQ : Poly (fun a : Candidate => encL encQ a.1) :=
    Poly.comp (f:=encL encQ) (g:=Prod.fst) (encL_poly _ ratCode_poly) Poly.fst
  have hI : Poly (fun a : Candidate => encL encI a.2) :=
    Poly.comp (f:=encL encI) (g:=Prod.snd) (encL_poly _ Integration9_9.TM2NativeAffineEmitter.encI_poly) Poly.snd
  exact Poly.comp (f:=fun p : Str × Str => encPair p.1 p.2)
    (g:=fun a : Candidate => (encL encQ a.1,encL encI a.2)) encPair_poly (Poly.pair hQ hI)

def post (w : PostInput) : Str := encL pairCode (candidates w)

@[fun_prop] theorem post_poly : Poly post := Poly.comp (f:=encL pairCode) (g:=candidates) (encL_poly _ pairCode_poly) candidates_poly

theorem probes_ofFn {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (q : ℕ) (x : Fin n → ℚ)
    (C : Matrix (Fin m) (Fin n) ℤ) (h : probeCount n ≤ m) :
    probes (((intRows B,q),List.ofFn x),intRows C) =
      (((intRows B,q),List.ofFn x),intRows fun i : Fin (probeCount n) => C (Fin.castLE h i)) := by
  unfold probes
  simp only [intRows,List.length_ofFn,Prod.mk.injEq,true_and]
  apply List.ext_getElem
  · simp [h]
  · intros;simp

theorem post_contains (w : ProbeInput) (ys : List Str) (raw : Str) (residue : List ℕ)
    (p : Candidate) (hraw : raw ∈ ys) (hs : (readVector raw).2=residue)
    (h : recover (probes w,residue)=p) (padding : Str) :
    ∃ vs : List (List ℚ × List ℤ),
      encL (fun a : List ℚ × List ℤ => encPair (encL encQ a.1) (encL encI a.2)) vs
          <+: post (w,ys)++padding ∧ p∈vs := by
  refine ⟨candidates (w,ys),⟨padding,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨raw,hraw,by simpa only [hs] using h⟩

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule55

/- Helper module Present. -/
section P2MDyadicModule56

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.ShortProbe

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding

open scoped BigOperators

theorem post_of_short_pool {n m : ℕ}
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (full : Matrix (Fin m) (Fin n) ℤ) (hm : probeCount n ≤ m)
    (R : ℚ) (hR : 0 < R) (x u : Fin n → ℚ) (z : Fin n → ℤ)
    (hu : ∀ j, ∑ i, (B i j : ℚ)*u i=z j)
    (hd : (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2)<(famσ n:ℝ)^2/4)
    (C : Matrix (Fin (probeCount n)) (Fin n) ℤ := fun a => full (Fin.castLE hm a))
    (hrows : C = fun a => full (Fin.castLE hm a) := by rfl)
    (hC : (C.transpose*C).det ≠ 0)
    (hc : ∀ a, ‖latVec B (C a)‖ ≤ 2*(R:ℝ)*Real.sqrt n)
    (ys : List Str) (hs : ∃ raw ∈ ys,
        (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val) (padding : Str) :
    ∃ vs : List (List ℚ × List ℤ),
      encL (fun a : List ℚ × List ℤ => encPair (encL encQ a.1) (encL encI a.2)) vs <+:
        post ((((intRows B,famq n),List.ofFn x),intRows full),ys)++padding ∧
        (List.ofFn u,List.ofFn z)∈vs := by
  obtain ⟨raw,hw,hs⟩ := hs
  apply post_contains _ _ raw _ _ hw hs _ padding
  rw [probes_ofFn _ _ _ _ hm, ←hrows]
  exact recover_from_short_pool B hB C hC R hR x u z hu hd hc

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule56

/- Helper module TrialCore. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

set_option maxRecDepth 20000

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open QAlgorithms.Complexity Integration9_9.LARPlatformEncoding Integration9_9.LoadedBatch.Schedule

open GaussianProjection GaussianProjection.CosetGeometry IntegerBasis RegevLWE.GaussConv AFT

open NativeLWETableLoader GaussianPoissonSeries RegevSketch RegevSearch

noncomputable section

attribute [local irreducible] famq famd larObservedRealTableLaw FiniteDist.map FiniteDist.expectation

theorem born_range (T : MFamily) (w : Str) (event : Str → Prop) :
    0 ≤ outputProb T w event ∧ outputProb T w event ≤ 1 := by
  unfold outputProb
  have hn := (runLayered_mass (T.circ w.length) (basisInput (a := T.anc w.length) (toBits w))).trans
    (basisInput_mass (a := T.anc w.length) (toBits w))
  simp only [Complex.normSq_eq_norm_sq] at hn
  constructor
  · exact Finset.sum_nonneg fun j _ => by split <;> positivity
  · rw [←hn]
    apply Finset.sum_le_sum
    intro j _
    split <;> first | exact le_rfl | positivity

abbrev window (samples : Polynomial ℕ) (n : ℕ) : ℕ := 768*(samples.eval n*famd n+1)

def variance (n M i : ℕ) : ℚ := (famσ n:ℚ)^2-((famσ n:ℚ)^2/2)*(i:ℚ)/M

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule57

/- Helper module TrialParity. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option maxHeartbeats 1200000

set_option maxRecDepth 20000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.ShortProbe

open scoped BigOperators Classical

open AFT QAlgorithms.Complexity RegevLWE.GaussConv RegevSketch RegevSearch

open Integration9_9.LARPlatformEncoding

noncomputable section

attribute [local irreducible] famq famd outputProb NativeLWETableLoader.observed

abbrev blockRows (samples : Polynomial ℕ) (n : ℕ) := samples.eval n * famd n

abbrev trialBits (samples : Polynomial ℕ) (n : ℕ) :=
  blockRows samples n * ((window samples n+1)+(2*(famσ n*window samples n)+1)+1)

theorem good_parity_trial (p coinPoly samples : Polynomial ℕ)
    (hp : ∀ n, blockRows samples n ≤ p.eval n) (hc : ∀ n, 2*trialBits samples n ≤ coinPoly.eval n)
    (A : MFamily) (cutoff : ℕ) (S : Set ℕ) (hsearch : SearchOn A samples cutoff S) :
    ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 →
    ∀ (R : ℚ), 0 < R →
      Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n) < (R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j,∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2) < (famσ n:ℝ)^2/4 →
    ∀ (j : Fin n), (∀ a,0≤coefficientMass B (R:ℝ) a) → HasSum (coefficientMass B (R:ℝ)) 1 →
      |(∑' a : Fin n → ℤ, if Odd (a j) then coefficientMass B (R:ℝ) a else 0) - (1/2:ℝ)| ≤
          2*(smoothingError n/(1-smoothingError n)) →
    ∃ i : Fin (window samples n + 1),
      let M := window samples n
      let v := variance n M i.val
      (2/3:ℝ) ≤ ∑' ac : (Fin (blockRows samples n) → Fin n → ℤ) × (Fin (trialBits samples n) → Fin n → ℤ),
        poolWeight (coefficientMass B (R:ℝ)) ac.1 * poolWeight (coefficientMass B (R:ℝ)) ac.2 *
        outputProb A (observedWord (blocks:=samples.eval n) (rows:=famd n) n (famPP n) B ac.1 x (famq n)
          v (famσ n*M) M (fun k => parityDigit j (ac.2 k)))
          (fun raw => (readVector raw).2=List.ofFn fun j => (z j:ZMod (famq n)).val) := by
  obtain ⟨N,hN⟩ := good_real_trial p samples hp A cutoff S hsearch
  obtain ⟨K,hK⟩ := parity_intrinsic_budget coinPoly
  refine ⟨max N K,?_⟩
  intro n hn ht B hB R hR hsm x u z hu hd j h0 h1 hb
  obtain ⟨i,hgood⟩ := hN n hn (by omega) B hB R hR hsm x u z hu hd
  refine ⟨i,?_⟩
  let δ := 2*(smoothingError n/(1-smoothingError n))
  have hδ : |(∑' a,if parityDigit j a=1 then coefficientMass B (R:ℝ) a else 0)-1/2|≤δ := by
    convert hb using 2
    congr 1
    apply tsum_congr
    intro a
    by_cases h : Odd (a j) <;> simp [parityDigit,h]
  exact parity_joint (coefficientMass B (R:ℝ)) h0 h1 (parityDigit j) δ hδ
    (blockRows samples n) (trialBits samples n)
    (fun vals tape => outputProb A (observedWord (blocks:=samples.eval n) (rows:=famd n)
        n (famPP n) B vals x (famq n) (variance n (window samples n) i.val) (famσ n*window samples n)
        (window samples n) tape) (fun raw => (readVector raw).2=List.ofFn fun i => (z i:ZMod (famq n)).val))
    (fun _ _ => born_range _ _ _) hgood ((hK n (by omega) _ (hc n)).trans (by norm_num))

end

end InfoLossLAR.WorstCase.ShortProbe

end P2MDyadicModule58

section
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit
open QAlgorithms.Complexity
set_option maxRecDepth 20000
open QAlgorithms
noncomputable section
def QueryTranscript (G : MFamily) (q : Str → List Str) : Prop :=
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
              (basisInput (toBits (requests.get i))) (xs i)‖^2 else 0

abbrev width (A : MFamily) (w : Str) := w.length + (A.anc w.length+1)

def readout (A : MFamily) (w : Str) (y : Bits (width A w)) : Str := List.ofFn fun j => y (A.outW w.length j)

def weight (A : MFamily) (w : Str) (y : Bits (width A w)) : ℝ :=
  ‖runLayered (A.circ w.length) (basisInput (toBits w)) y‖^2

theorem weight_one (A : MFamily) (w : Str) : ∑ y, weight A w y = 1 := by
  have h := (runLayered_mass (A.circ w.length) (basisInput (a:=A.anc w.length) (toBits w))).trans
    (basisInput_mass (a:=A.anc w.length) (toBits w))
  simpa only [weight,Complex.normSq_eq_norm_sq] using h


end

theorem split_pool_sum {X : Type} (μ : X → ℝ) (a b : ℕ) (f : (Fin (a+b) → X) → ℝ) :
    (∑' v : Fin (a+b) → X, density μ v * f v) =
      ∑' y : (Fin a → X) × (Fin b → X), density μ y.1 * density μ y.2 *
        f (Fin.appendEquiv (α:=X) a b y) := by
  rw [← (Fin.appendEquiv (α:=X) a b).tsum_eq]
  apply tsum_congr
  intro y
  simp only [density,Fin.prod_univ_add,Fin.appendEquiv,Equiv.coe_fn_mk,
    Fin.append_left,Fin.append_right]

theorem output_range (A : MFamily) (w : Str) (f : Str → Prop) :
    0 ≤ outputProb A w f ∧ outputProb A w f ≤ 1 := by
  unfold outputProb
  constructor
  · exact Finset.sum_nonneg fun _ _ => by split <;> positivity
  · rw [← weight_one A w]
    exact Finset.sum_le_sum fun _ _ => by split <;> first | rfl | exact sq_nonneg _

theorem output_complement (A : MFamily) (w : Str) (f : Str → Prop) :
    outputProb A w (fun s => ¬f s) = 1-outputProb A w f := by
  rw [← weight_one A w,eq_sub_iff_add_eq]
  unfold outputProb
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by split_ifs <;> simp_all [weight])


end InfoLossLAR.WorstCase.RegevSearch.ShortProbeCircuit


section

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace InfoLossLAR.WorstCase.ShortProbePlan
open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
noncomputable section

def finish (ws : Str × List Str) : Str :=
  let d := parse ws.1
  ShortProbe.post (((((d.1.1,modulus (security d)), d.1.2),d.2),ws.2))
@[fun_prop] theorem finish_poly : Poly finish := by unfold finish; fun_prop
end
end InfoLossLAR.WorstCase.ShortProbePlan
end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.ShortProbePlan
open QAlgorithms.Complexity
noncomputable section

def poolWord {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) : Str :=
  encPair (encMat encI B) (encPair (encQ R) (encPair (unary k) (encPair (encVec (encVec encI) C) (encVec encQ x))))

theorem parse_pool {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) : parse (poolWord B R k C x) = data B x C := parse_correct _ _ _ _ _

theorem finish_pool {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (os : List Str) :
    finish (poolWord B R k C x,os) = ShortProbe.post
      ((((ShortProbe.intRows B,famq n),List.ofFn x),ShortProbe.intRows (Matrix.of C)),os) := by
  simp only [finish,parse_pool,sec_data,modulus_eq,unary,List.length_replicate]
  rfl

theorem requests_pool {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (hjobs : jobCount p n ≤ a) :
    requests p (poolWord B R k C x) = (List.range (jobCount p n)).map
      (fun i => NativeLWETableLoader.observed (observedRequest p (data B x C,i))) := by
  have hs : grid p (data B x C) = widths p n := by
    simp only [grid,scalarRows,sec_data,rowCount_eq,unary,List.length_replicate,data_basis,List.length_ofFn,widths,rows]
  unfold requests
  simp only [parse_pool,hs,data_basis,data_pool,List.length_ofFn,show (widths p n+1)*n=jobCount p n from rfl,slots_exact _ hjobs,List.length_replicate]

def picker {n c : ℕ} (i : Fin c) {l : ℕ} (hl : l = c*n) : Fin n ↪ Fin l where
  toFun j := ⟨i.val*n+j.val,by have := (finProdFinEquiv (i,j)).isLt; simpa [hl,finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using this⟩
  inj' a b h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

def trialBlock {n a : ℕ} {X : Type} (p : Polynomial ℕ) (C : Fin a → X) (j : Fin n) (h : used p n ≤ a) :
    Fin (trialSize p n) → X :=
  fun i => C ⟨saved n+j.val*trialSize p n+i.val,by
    have hm := Nat.mul_le_mul_right (trialSize p n) j.isLt
    rw [Nat.succ_mul] at hm
    dsimp only [used] at h
    omega⟩

def wordFor {n : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ)
    (idx : ℕ) (j0 : Fin n)
    (v : Fin (trialSize p n) → Fin n → ℤ) : Str :=
  ShortProbe.observedWord (blocks:=p.eval n) (rows:=famd n) n (famPP n) B
    (fun i => v (Fin.castAdd _ i)) x (famq n) (gridVar p n idx) (cutoffSize p n) (widths p n)
    (fun i => ShortProbe.parityDigit j0 (v (Fin.natAdd (rows p n) i)))


end
end InfoLossLAR.WorstCase.ShortProbePlan
end

section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.ShortProbePlan
open scoped BigOperators Classical
open QAlgorithms.Complexity RegevSketch RegevSearch RegevLWE.GaussConv
open RegevSearch.ShortProbeCircuit Integration9_9.LARPlatformEncoding
noncomputable section
attribute [local irreducible] famq famd outputProb ShortProbe.observedWord

theorem wordFor_append {n : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ)
    (idx : ℕ) (j : Fin n)
    (ac : (Fin (rows p n) → Fin n → ℤ) × (Fin (rows p n*coinWidth p n) → Fin n → ℤ)) :
    wordFor p B x idx j (Fin.appendEquiv (rows p n) (rows p n*coinWidth p n) ac) =
    ShortProbe.observedWord (blocks:=p.eval n) (rows:=famd n) n (famPP n) B ac.1 x (famq n)
       (gridVar p n idx) (cutoffSize p n) (widths p n) (fun k => ShortProbe.parityDigit j (ac.2 k)) := by
  simp only [wordFor,Fin.appendEquiv,Equiv.coe_fn_mk,Fin.append_left,Fin.append_right]

theorem flat_failure {n : ℕ} (p : Polynomial ℕ) (A : MFamily)
    (B : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℚ) (idx : ℕ) (j : Fin n) (event : Str → Prop)
    (μ : (Fin n → ℤ) → ℝ) (h0 : ∀ z,0≤μ z) (h1 : HasSum μ 1)
    (hit : (2/3 : ℝ) ≤ ∑' ac : (Fin (rows p n) → Fin n → ℤ) × (Fin (rows p n*coinWidth p n) → Fin n → ℤ),
       density μ ac.1 * density μ ac.2 *
       outputProb A (ShortProbe.observedWord (blocks:=p.eval n) (rows:=famd n) n (famPP n) B ac.1 x (famq n)
         (gridVar p n idx) (cutoffSize p n) (widths p n) (fun k => ShortProbe.parityDigit j (ac.2 k))) event) :
    (∑' v : Fin (trialSize p n) → Fin n → ℤ, density μ v *
       outputProb A (wordFor p B x idx j v) (fun a => ¬event a)) ≤ 1/3 := by
  let f (v : Fin (trialSize p n) → Fin n → ℤ) := outputProb A (wordFor p B x idx j v) event
  have split := split_pool_sum μ (rows p n) (rows p n*coinWidth p n) f
  simp only [f,wordFor_append] at split
  have H := hit.trans_eq split.symm
  simp_rw [output_complement A _ event]
  rw [complement_mass _ (fun v => Finset.prod_nonneg fun i _ => h0 (v i)) (iid_mass μ h0 h1 _) f
    (fun v => output_range A (wordFor p B x idx j v) event)]
  calc
    _ ≤ 1 - (2/3 : ℝ) := sub_le_sub_left H 1
    _ = _ := by norm_num

theorem one_trial_missing (p coinPoly samples : Polynomial ℕ)
    (hp : ∀ n, rows samples n ≤ p.eval n) (hc : ∀ n, 2*(rows samples n*coinWidth samples n) ≤ coinPoly.eval n)
    (A : MFamily) (cutoff : ℕ) (S : Set ℕ) (hs : SearchOn A samples cutoff S) :
    ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ (B : Matrix (Fin n) (Fin n) ℤ), B.det≠0 →
    ∀ (R : ℚ), 0<R → Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ) →
    ∀ (x u : Fin n → ℚ) (z : Fin n → ℤ), (∀ j, ∑ i,(B i j:ℚ)*u i=z j) →
      (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2)<(famσ n:ℝ)^2/4 →
    ∀ (j0 : Fin n), (∀ a, 0≤coefficientMass B (R:ℝ) a) → HasSum (coefficientMass B (R:ℝ)) 1 →
      |(∑' a : Fin n → ℤ,if Odd (a j0) then coefficientMass B (R:ℝ) a else 0)-(1/2:ℝ)|≤
        2*(smoothingError n/(1-smoothingError n)) →
    ∃ i : Fin (widths samples n + 1),
      (∑' v : Fin (trialSize samples n) → Fin n → ℤ,
        density (coefficientMass B (R:ℝ)) v * outputProb A (wordFor samples B x i.val j0 v)
          (fun raw => ¬ (readVector raw).2 = List.ofFn fun j => (z j:ZMod (famq n)).val)) ≤ 1/3 := by
  obtain ⟨N,hN⟩ := ShortProbe.good_parity_trial p coinPoly samples hp hc A cutoff S hs
  refine ⟨N,?_⟩
  intro n hn ht B hB R hR hw x u z hu hd j0 h0 h1 hδ
  obtain ⟨i,hi⟩ := hN n hn ht B hB R hR hw x u z hu hd j0 h0 h1 hδ
  exact ⟨i,flat_failure samples A B x i.val j0
    (fun raw => (readVector raw).2 = List.ofFn fun j => (z j:ZMod (famq n)).val)
    (coefficientMass B (R:ℝ)) h0 h1 hi⟩

end
end InfoLossLAR.WorstCase.ShortProbePlan
end
end

section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.ShortProbePlan
open QAlgorithms.Complexity RegevSketch RegevSearch.ShortProbeCircuit
open Integration9_9.LARPlatformEncoding
noncomputable section

def loss {n : ℕ} (u : Fin n → ℚ) (z : Fin n → ℤ) (o : Str) : Prop := ¬∃ vs : List (List ℚ × List ℤ),
    encL (fun p : List ℚ × List ℤ => encPair (encL encQ p.1) (encL encI p.2)) vs <+: o ∧ (List.ofFn u,List.ofFn z)∈vs
def hit {n : ℕ} (z : Fin n → ℤ) (o : Str) : Prop := (readVector o).2=List.ofFn fun j => (z j:ZMod (famq n)).val

abbrev Bound (A T : MFamily) (p : Polynomial ℕ) : Prop :=
  ∀ w : Str, ∀ n : ℕ, ∀ pick : Fin n ↪ Fin (requests p w).length, ∀ (ok fail : Str → Prop),
    (∀ os tail, (∃ o ∈ os, ok o) → ¬fail (finish (w,os) ++ tail)) →
    outputProb T w fail ≤ ∏ j, outputProb A ((requests p w).get (pick j)) (fun o => ¬ok o)

theorem length_jobs {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (hjobs : jobCount p n ≤ a) :
    (requests p (poolWord B R k C x)).length = (widths p n+1)*n := by
  rw [requests_pool p B R k C x hjobs]
  simp [jobCount]

theorem fixed_pool {n a : ℕ} (p : Polynomial ℕ) (A T : MFamily) (ht : Bound A T p)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℚ) (hR : 0 < R) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x u : Fin n → ℚ) (z : Fin n → ℤ)
    (hu : ∀ j, ∑ i,(B i j:ℚ)*u i=(z j:ℚ))
    (hd : (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2)<(famσ n:ℝ)^2/4)
    (huse : used p n ≤ a) (hjobs : jobCount p n ≤ a) (idx : Fin (widths p n+1)) (j0 : Fin n)
    (hqs : ∀ j, (requests p (poolWord B R k C x)).get (picker idx (length_jobs p B R k C x hjobs) j) =
      wordFor p B x idx.val j0 (trialBlock p C j huse))
    (hg : Holdout.cutoffGood B R (fun i : Fin (saved n) => C ⟨i.val,by unfold used at huse; omega⟩)) :
    outputProb T (poolWord B R k C x) (loss u z) ≤ ∏ j, outputProb A
      (wordFor p B x idx.val j0 (trialBlock p C j huse)) (fun o => ¬hit z o) := by
  let w := poolWord B R k C x
  let pick := picker idx (length_jobs p B R k C x hjobs)
  have hm : ShortProbe.probeCount n ≤ a := by
    change saved n ≤ a; dsimp only [used] at huse; omega
  have hpost (os : List Str) (tail : Str) (hh : ∃ o ∈ os, hit z o) :
      ¬loss u z (finish (w,os)++tail) := by
    rw [show finish (w,os) = _ from finish_pool B R k C x os]
    intro hbad
    apply hbad
    apply ShortProbe.post_of_short_pool B hB (Matrix.of C) hm R hR x u z hu hd
      (fun i => C (Fin.castLE hm i)) rfl hg.1 hg.2 os hh tail
  have h := ht w n pick (hit z) (loss u z) hpost
  calc
    _ ≤ _ := h
    _ = _ := Finset.prod_congr rfl (fun j _ => congrArg (fun w => outputProb A w (fun o => ¬ hit z o)) (hqs j))

attribute [local irreducible] coefficientMass wordFor outputProb poolWord requests finish Holdout.cutoffGood famq
private theorem offset_eq {n t : ℕ} (s : ℕ) (j : Fin n) (i : Fin t) :
    s+j.val*t+i.val = s+(finProdFinEquiv (j,i)).val := by
  change s+j.val*t+i.val = s+(i.val+t*j.val)
  ac_rfl

private theorem trialBlock_addr {n a : ℕ} {X : Type} (p : Polynomial ℕ) (C : Fin a → X) (j : Fin n) (h : used p n ≤ a) :
    trialBlock p C j h = fun k : Fin (trialSize p n) =>
      C ⟨saved n+(finProdFinEquiv (j,k)).val,by have := (finProdFinEquiv (j,k)).isLt; dsimp only [used] at h; omega⟩ := by
  funext k
  apply congrArg C
  exact Fin.ext (offset_eq (saved n) j k)

theorem pooled {n a : ℕ} (p : Polynomial ℕ) (A T : MFamily) (ht : Bound A T p)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℚ) (hR : 0 < R) (k : ℕ)
    (x u : Fin n → ℚ) (z : Fin n → ℤ) (hu : ∀ j, ∑ i,(B i j:ℚ)*u i=(z j:ℚ))
    (hd : (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2)<(famσ n:ℝ)^2/4)
    (huse : used p n ≤ a) (hjobs : jobCount p n ≤ a) (idx : Fin (widths p n+1)) (j0 : Fin n)
    (hqs : ∀ (C : Fin a → Fin n → ℤ) (j : Fin n), (requests p (poolWord B R k C x)).get (picker idx (length_jobs p B R k C x hjobs) j) =
      wordFor p B x idx.val j0 (trialBlock p C j huse))
    (hμ : ∀ y, 0 ≤ coefficientMass B R y) (h1 : HasSum (coefficientMass B R) 1) :
    (∑' C : Fin a → Fin n → ℤ, density (coefficientMass B R) C *
        outputProb T (poolWord B R k C x) (loss u z)) ≤
        (∑' H : Fin (saved n) → Fin n → ℤ, density (coefficientMass B R) H *
          (if Holdout.cutoffGood B R H then 0 else 1)) +
        (∑' v : Fin (trialSize p n) → Fin n → ℤ, density (coefficientMass B R) v *
          outputProb A (wordFor p B x idx.val j0 v) (fun o => ¬hit z o))^n := by
  let f := fun v : Fin (trialSize p n) → Fin n → ℤ => outputProb A (wordFor p B x idx.val j0 v) (fun o => ¬hit z o)
  let g := fun C : Fin a → Fin n → ℤ => outputProb T (poolWord B R k C x) (loss u z)
  apply pool_experiment (s:=saved n) (t:=trialSize p n) (n:=n) huse (coefficientMass B R)
    hμ h1 (Holdout.cutoffGood B R) f (fun _ => output_range A _ _) g (fun _ => output_range T _ _)
  intro C hg
  have h := fixed_pool p A T ht B hB R hR k C x u z hu hd huse hjobs idx j0 (hqs C) hg
  exact h.trans_eq (Finset.prod_congr rfl (fun j _ => congrArg f (trialBlock_addr p C j huse)))

end
end InfoLossLAR.WorstCase.ShortProbePlan
end

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace InfoLossLAR.WorstCase.ShortProbePlan
open QAlgorithms.Complexity RegevSketch RegevSearch RegevLWE.GaussConv
open RegevSearch.ShortProbeCircuit
noncomputable section
attribute [local irreducible] famq famd outputProb wordFor coefficientMass requests finish poolWord

abbrev QueryAt (p : Polynomial ℕ) : Prop :=
  ∀ {n a : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ) (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ)
    (huse : used p n ≤ a) (hjobs : jobCount p n ≤ a) (hcut : cutoffSize p n ≤ a)
    (hwidth : widths p n ≤ a) (hrows : famd n ≤ a) (hblocks : p.eval n ≤ a)
    (idx : Fin (widths p n+1)) (j : Fin n),
    (requests p (poolWord B R k C x)).get (picker idx (length_jobs p B R k C x hjobs) j) =
      wordFor p B x idx.val ⟨0,Nat.zero_lt_of_lt j.isLt⟩ (trialBlock p C j huse)

private theorem holdout_failure {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ)
    (hμ : ∀ y, 0 ≤ coefficientMass B R y)
    (hH : HasSum (fun H : Fin (saved n) → Fin n → ℤ => density (coefficientMass B R) H) 1)
    (hgood : 1-((1/2:ℝ)^n+16*((n:ℝ)+1)^2*(1/4:ℝ)^n) ≤
      ∑' H : Fin (saved n) → Fin n → ℤ, density (coefficientMass B R) H * (if Holdout.cutoffGood B R H then 1 else 0)) :
    (∑' H : Fin (saved n) → Fin n → ℤ, density (coefficientMass B R) H *
      (if Holdout.cutoffGood B R H then 0 else 1)) ≤ (1/2:ℝ)^n+16*((n:ℝ)+1)^2*(1/4:ℝ)^n := by
  rw [good_complement _ (fun _ => Finset.prod_nonneg fun _ _ => hμ _) hH (Holdout.cutoffGood B R)]
  linarith

theorem certified (S : Set ℕ) (A : MFamily) (p : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A p cutoff S)
    (hq : QueryTranscript A (requests p)) (hat : QueryAt p) :
    ∃ T : MFamily, IsMQPT T ∧ ∃ P : Polynomial ℕ, ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ R : ℚ, 0<R → Real.sqrt 2*(famq n:ℝ)*smoothingParam (inputModule B) (smoothingError n)<(R:ℝ) →
      ∀ (k : ℕ) (x u : Fin n → ℚ) (z : Fin n → ℤ),
        (∀ j, ∑ i,(B i j:ℚ)*u i=(z j:ℚ)) →
        (R:ℝ)^2*(∑ i,((x i-u i:ℚ):ℝ)^2)<(famσ n:ℝ)^2/4 →
        (∑' C : Fin (P.eval n) → Fin n → ℤ, (∏ i,coefficientMass B R (C i)) *
          outputProb T (poolWord B R k C x) (loss u z)) ≤ e n + 1 / ((k:ℝ)+1) := by
  obtain ⟨T,hT,hC⟩ := compiled A (requests p) finish finish_poly hq
  obtain ⟨P,hP⟩ := pool_budget p
  obtain ⟨L,hL⟩ := trial_budget p
  obtain ⟨U,hU⟩ := one_trial_missing L L p (fun n => (hL n).1) (fun n => (hL n).2) A cutoff S hsearch
  obtain ⟨V,hV⟩ := Holdout.short_spanning
  refine ⟨T,hT,P,totalError,totalError_negligible,max 256 (max U V),?_⟩
  intro n hn ht B hB R hR hwide k x u z hu hd
  have hn256 : 256 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hthreshold := Holdout.threshold_of_wide hn256 B (R:ℝ) (Rat.cast_pos.mpr hR) hwide
  have hsm := Holdout.threshold (by omega) B (R:ℝ) (Rat.cast_pos.mpr hR) hthreshold
  obtain ⟨hμ,h1,_⟩ := Holdout.residue_event hn2 B hB (R:ℝ) (Rat.cast_pos.mpr hR) hsm ∅
  let j0 : Fin n := ⟨0,by omega⟩
  obtain ⟨i,hm⟩ := hU n hn (by omega) B hB R hR hwide x u z hu hd j0 hμ h1
    (Holdout.odd_coordinate hn2 B hB _ (Rat.cast_pos.mpr hR) hsm j0)
  obtain ⟨huse,hjobs,hcut,hwidth,hrows,hblocks⟩ := hP n
  obtain ⟨hH,hgood⟩ := hV n (by omega) B hB R (Rat.cast_pos.mpr hR) hthreshold
  have hbad := holdout_failure B (R:ℝ) hμ hH hgood
  have hpooled := pooled p A T hC B hB R hR k x u z hu hd huse hjobs i j0
    (fun C j => hat B R k C x huse hjobs hcut hwidth hrows hblocks i j) hμ h1
  let Z := ∑' v : Fin (trialSize p n) → Fin n → ℤ, density (coefficientMass B R) v *
    outputProb A (wordFor p B x i.val j0 v) (fun o => ¬hit z o)
  have hZ : 0 ≤ Z := tsum_nonneg (fun v => mul_nonneg (Finset.prod_nonneg (fun _ _ => hμ _)) (output_range A _ _).1)
  have hZ' : Z ≤ 1/3 := hm
  have hp := pow_le_pow_left₀ hZ hZ' n
  exact hpooled.trans ((add_le_add hbad hp).trans ((final_error n).trans (le_add_of_nonneg_right (by positivity))))

end
end InfoLossLAR.WorstCase.ShortProbePlan
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.ShortProbePlan
open QAlgorithms.Complexity
noncomputable section
attribute [local irreducible] famq famd NativeLWETableLoader.observed NativeLWETableLoader.numericalContext famPP

private theorem observations_congr (header : Str × Str) (blocks : List Unit × List Unit)
    (ctx : NativeLWETableLoader.Context)
    (left right : List (List ℤ)) (first second : Str) (he : left=right) (hc : first=second) :
    NativeLWETableLoader.observed (header,(blocks,((ctx,left),first))) =
      NativeLWETableLoader.observed (header,(blocks,((ctx,right),second))) := by rw [he,hc]

private theorem rows_segment {a n off r m : ℕ} (C : Fin a→Fin n→ℤ)
    (h : off+r+m ≤ a) :
    (List.ofFn fun i : Fin r => List.ofFn (C ⟨off+i.val,by omega⟩)) =
    (List.ofFn fun i : Fin r => List.ofFn ((fun k : Fin (r+m) =>
      C ⟨off+k.val,by omega⟩) (Fin.castAdd m i))) := rfl

private theorem coins_segment {a n off r m : ℕ} (C : Fin a→Fin n→ℤ)
    (h : off+r+m ≤ a) (hn : 0<n) :
    (List.ofFn fun i : Fin m => oddBit (List.ofFn (C ⟨off+r+i.val,by omega⟩))) =
    (List.ofFn fun i : Fin m => AFT.BinaryArithmetic.digitBoolean (ShortProbe.parityDigit ⟨0,hn⟩
        ((fun k : Fin (r+m) => C ⟨off+k.val,by omega⟩) (Fin.natAdd r i)))) := by
  apply congrArg List.ofFn
  funext i
  rw [ShortProbe.parity_eq]
  simp [oddBit,List.head?_eq_getElem?,hn,Nat.add_assoc]

private theorem local_observed {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (huse : used p n ≤ a)
    (idx : ℕ) (j : Fin n) (h : saved n + j.val*trialSize p n + trialSize p n ≤ a) :
    NativeLWETableLoader.observed (localRequest p B x C idx j.val h) =
      wordFor p B x idx ⟨0,Nat.zero_lt_of_lt j.isLt⟩ (trialBlock p C j huse) := by
  have hn : 0<n := Nat.zero_lt_of_lt j.isLt
  let off := saved n+j.val*trialSize p n
  have hs : off+rows p n + rows p n*coinWidth p n ≤ a := by
    simpa only [off,trialSize,Nat.add_assoc] using h
  unfold localRequest wordFor ShortProbe.observedWord
  dsimp only
  apply observations_congr
  · exact rows_segment C hs
  · exact coins_segment C hs hn

private theorem range_request {α : Type} {n c : ℕ} {xs : List α} (f : ℕ → α)
    (hx : xs=(List.range (c*n)).map f) (idx : Fin c) (j : Fin n) (h : xs.length=c*n) :
    xs.get (picker idx h j)=f (idx.val*n+j.val) := by
  subst xs
  simp [picker,List.get_eq_getElem]

private theorem select_request {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (hjobs : jobCount p n ≤ a)
    (idx : Fin (widths p n + 1)) (j : Fin n) :
    let w := poolWord B R k C x
    let h : (requests p w).length = (widths p n+1)*n := by
      dsimp only [w]; rw [requests_pool p B R k C x hjobs]; simp [jobCount]
    (requests p w).get (picker idx h j) =
      NativeLWETableLoader.observed (observedRequest p (data B x C,idx.val*n+j.val)) := by
  intro w h
  exact range_request (fun k => NativeLWETableLoader.observed (observedRequest p (data B x C,k)))
    (requests_pool p B R k C x hjobs) idx j h

theorem observed_local {n a : ℕ} (p : Polynomial ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) (k : ℕ)
    (C : Fin a → Fin n → ℤ) (x : Fin n → ℚ) (huse : used p n ≤ a) (hjobs : jobCount p n ≤ a)
    (hcut : cutoffSize p n ≤ a) (hwidth : widths p n ≤ a) (hrows : famd n ≤ a) (hblocks : p.eval n ≤ a)
    (idx : Fin (widths p n + 1)) (j : Fin n) :
    let w := poolWord B R k C x
    let h : (requests p w).length = (widths p n+1)*n := by
      dsimp only [w]; rw [requests_pool p B R k C x hjobs]; simp [jobCount]
    (requests p w).get (picker idx h j) =
      wordFor p B x idx.val ⟨0,Nat.zero_lt_of_lt j.isLt⟩ (trialBlock p C j huse) := by
  intro w h
  apply (select_request p B R k C x hjobs idx j).trans
  exact (congrArg NativeLWETableLoader.observed (observedRequest_at p B x C idx.val j huse hcut hwidth hrows hblocks)).trans
    (local_observed p B C x huse idx.val j _)

end
end InfoLossLAR.WorstCase.ShortProbePlan
end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 20000
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open RegevLWE.GaussConv
open scoped BigOperators Classical
open InfoLossLAR.WorstCase.RegevSearch InfoLossLAR.WorstCase.ShortProbePlan

theorem solution
    (hgrid : ∀ (s q M : ℕ), 2 ≤ s → 2 ≤ q → 0 < M → ∀ E : ℝ, 0 ≤ E → E ≤ (s : ℝ)^2 / 2 →
    ∃ i : Fin (M + 1), ∀ j : ℕ,
      let den : ℚ := (q : ℚ)^(2*j)
      let v : ℚ := (s : ℚ)^2 - ((s : ℚ)^2/2) * (i.val : ℚ) / M / den
      let total := E / (den : ℝ) + (v : ℝ)
      let mass := fun (width : ℝ) (z : ℤ) => AFT.GaussianSource.weight width z /
        AFT.GaussianSource.realNormalizer width
      (s : ℚ)^2/2 ≤ v ∧ v ≤ (s : ℚ)^2 ∧
      0 ≤ (s : ℝ)^2 - total ∧
      (s : ℝ)^2 - total ≤ (s : ℝ)^2 / (2 * M * (den : ℝ)) ∧
      (∑' z : ℤ, |mass (Real.sqrt total) z - mass (s : ℝ) z|)/2 ≤
        1 / ((M : ℝ) * (den : ℝ)))
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (A : MFamily) (hA : IsMQPT A) (samples : Polynomial ℕ) (cutoff : ℕ)
    (hsearch : SearchOn A samples cutoff S) :
    ∃ T : MFamily, IsMQPT T ∧ ∃ P : Polynomial ℕ, ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N : ℕ, ∀ n ∈ S, N ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ R : ℚ, 0 < R →
        Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
      ∀ (k : ℕ) (x u : Fin n → ℚ) (z : Fin n → ℤ),
        (∀ j, ∑ i, (B i j : ℚ) * u i = (z j : ℚ)) →
        (R : ℝ)^2 * (∑ i, (((x i-u i : ℚ) : ℝ))^2) < (famσ n : ℝ)^2 / 4 →
        (∑' pool : Fin (P.eval n) → Fin n → ℤ,
          (∏ j, coefficientMass B (R : ℝ) (pool j)) *
          outputProb T (poolBDDInput B R k pool x) (fun out => ¬ ∃ vs : List (List ℚ × List ℤ),
            encL (fun p : List ℚ × List ℤ => encPair (encL encQ p.1) (encL encI p.2)) vs <+: out ∧
              (List.ofFn u,List.ofFn z) ∈ vs)) ≤ e n + 1 / ((k : ℝ)+1) := by
  have hAt : QueryAt samples := by
    intro n a B R k C x huse hjobs hcut hwidth hrows hblocks idx j
    exact observed_local samples B R k C x huse hjobs hcut hwidth hrows hblocks idx j
  have hq := mqpt_encoded_query_transcript A hA (requests samples) (requests_poly samples)
  have H := certified S A samples cutoff hsearch hq hAt
  exact H
