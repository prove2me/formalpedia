-- Prove2me | solution 1 for OAI.InvariantIsing.haarPolynomialMoment_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:59:18.999762+00:00
-- url     : https://prove2.me/submissions/7196314a-d2c0-40fa-a42b-e0745c9011c2

import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Induction
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticMinimumCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Necessary derivative signs at minima, for the inverse-coordinate
parabolic comparison on the closed mean-spin interval. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma second_derivative_nonneg_at_local_min {f f' : ℝ → ℝ} {a c : ℝ}
    (hm : IsLocalMin f a)
    (hf : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' c a) : 0 ≤ c := by
  have hfa := hf.self_of_nhds
  have hz : f' a = 0 := hm.hasDerivAt_eq_zero hfa
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp hf').2
  have hd' : Tendsto (fun x : ℝ => f' x / (2 * (x - a)))
      (𝓝[>] a) (𝓝 (c / 2)) := by
    have hh := hd.div_const 2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    rw [slope_def_field, hz, sub_zero, mul_comm (2 : ℝ) (x - a), div_mul_eq_div_div]
  have hnum : ∀ᶠ x in 𝓝[>] a, HasDerivAt (fun y => f y - f a) (f' x) x := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds] with x hx
    exact hx.sub_const (f a)
  have hden : ∀ᶠ x in 𝓝[>] a,
      HasDerivAt (fun y : ℝ => (y - a) ^ 2) (2 * (x - a)) x := by
    filter_upwards [] with x
    refine (((hasDerivAt_id x).sub_const a).pow 2).congr_deriv (Eq.symm ?_)
    · simp
  have hne : ∀ᶠ x in 𝓝[>] a, 2 * (x - a) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx.ne')
  have hn0 : Tendsto (fun x => f x - f a) (𝓝[>] a) (𝓝 0) := by
    simpa only [sub_self] using (hfa.continuousAt.sub_const (f a)).mono_left
      nhdsWithin_le_nhds
  have hd0 : Tendsto (fun x : ℝ => (x - a) ^ 2) (𝓝[>] a) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => (x - a) ^ 2) a := by fun_prop
    simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      hh.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := HasDerivAt.lhopital_zero_nhdsGT hnum hden hne hn0 hd0 hd'
  have hnon : ∀ᶠ x in 𝓝[>] a, 0 ≤ (f x - f a) / (x - a) ^ 2 := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds] with x hx
    exact div_nonneg (sub_nonneg.mpr hx) (sq_nonneg _)
  have : 0 ≤ c / 2 := ge_of_tendsto hlim hnon
  linarith

lemma derivative_nonpos_at_left_min {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hm : ∀ᶠ x in 𝓝[<] a, f a ≤ f x) : d ≤ 0 := by
  have hl := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  apply le_of_tendsto hl
  filter_upwards [hm, self_mem_nhdsWithin] with x hx hxa
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hxa.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_CompactParabolicMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar minimum argument on a compact spatial state space. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma compact_parabolic_nonneg {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {T : ℝ} (hT : 0 ≤ T) (W : ℝ → K → ℝ) (Wt : ℝ × K → ℝ) (B : ℝ → K → ℝ)
    (hc : ContinuousOn (fun z : ℝ × K => W z.1 z.2) (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ x, 0 ≤ W 0 x)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, HasDerivAt (fun s => W s x) (Wt (t,x)) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, B t x-W t x ≤ Wt (t,x))
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, (∀ y, W t x ≤ W t y) → 0 ≤ B t x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ W t x := by
  intro t ht x
  by_contra hn
  have hneg : W t x < 0 := lt_of_not_ge hn
  let x₀ : K := Classical.choice inferInstance
  obtain ⟨q,hq,hm⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set K))).exists_isMinOn
    ⟨(0,x₀),⟨⟨le_rfl,hT⟩,Set.mem_univ x₀⟩⟩ hc
  have hqneg : W q.1 q.2 < 0 := (hm (show (t,x) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨ht,Set.mem_univ x⟩)).trans_lt hneg
  have hqt : 0 < q.1 := by
    by_contra h
    have he : q.1=0 := le_antisymm (le_of_not_gt h) hq.1.1
    rw [he] at hqneg
    exact (not_lt_of_ge (hi q.2)) hqneg
  have hleft : ∀ᶠ s in 𝓝[<] q.1, W q.1 q.2 ≤ W s q.2 := by
    have hpos : ∀ᶠ s in 𝓝[<] q.1, 0 < s :=
      (show ∀ᶠ s : ℝ in 𝓝 q.1, 0 < s from Ioi_mem_nhds hqt).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with s hs hs'
    exact hm (show (s,q.2) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨⟨hs.le,hs'.le.trans hq.1.2⟩,Set.mem_univ q.2⟩)
  have htime := derivative_nonpos_at_left_min (hd q.1 ⟨hqt,hq.1.2⟩ q.2) hleft
  have hsp := hspace q.1 hq.1 q.2 (fun y => hm (show (q.1,y) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
    ⟨hq.1,Set.mem_univ y⟩))
  have hp := hpde q.1 ⟨hqt,hq.1.2⟩ q.2
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_CompactNegativeMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact parabolic minimum test restricted to negative minima. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma compact_nonneg_of_negative_min_derivative {K : Type*}
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {T : ℝ} (hT : 0 ≤ T) (W : ℝ → K → ℝ) (Wt : ℝ × K → ℝ)
    (hc : ContinuousOn (fun z : ℝ × K => W z.1 z.2) (Icc (0:ℝ) T ×ˢ Set.univ))
    (hi : ∀ x, 0 ≤ W 0 x)
    (hd : ∀ t ∈ Ioc (0:ℝ) T, ∀ x, HasDerivAt (fun s => W s x) (Wt (t,x)) t)
    (hmin : ∀ t ∈ Ioc (0:ℝ) T, ∀ x, W t x < 0 →
      (∀ y, W t x ≤ W t y) → 0 < Wt (t,x)) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ x, 0 ≤ W t x := by
  intro t ht x
  by_contra hn
  have hneg : W t x < 0 := lt_of_not_ge hn
  let x₀ : K := Classical.choice inferInstance
  obtain ⟨q,hq,hm⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set K))).exists_isMinOn
    ⟨(0,x₀),⟨⟨le_rfl,hT⟩,Set.mem_univ x₀⟩⟩ hc
  have hqneg : W q.1 q.2 < 0 := (hm (show (t,x) ∈ Icc (0:ℝ) T ×ˢ (Set.univ : Set K) from
    ⟨ht,Set.mem_univ x⟩)).trans_lt hneg
  have hqt : 0 < q.1 := by
    by_contra h
    have he : q.1=0 := le_antisymm (le_of_not_gt h) hq.1.1
    rw [he] at hqneg
    exact (not_lt_of_ge (hi q.2)) hqneg
  have hleft : ∀ᶠ s in 𝓝[<] q.1, W q.1 q.2 ≤ W s q.2 := by
    have hpos : ∀ᶠ s in 𝓝[<] q.1, 0 < s :=
      (show ∀ᶠ s : ℝ in 𝓝 q.1, 0 < s from Ioi_mem_nhds hqt).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with s hs hs'
    exact hm (show (s,q.2) ∈ Icc (0:ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨⟨hs.le,hs'.le.trans hq.1.2⟩,Set.mem_univ q.2⟩)
  have htime := derivative_nonpos_at_left_min (hd q.1 ⟨hqt,hq.1.2⟩ q.2) hleft
  have hsp := hmin q.1 ⟨hqt,hq.1.2⟩ q.2 hqneg
    (fun y => hm (show (q.1,y) ∈ Icc (0:ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨hq.1,Set.mem_univ y⟩))
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneSandwich
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite matrix contraction behind the orthogonal-group curvature calculation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_sandwich {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    planeGenerator i j*A*planeGenerator i j =
      Matrix.single i j (A j i)-Matrix.single j j (A i i)-
        Matrix.single i i (A j j)+Matrix.single j i (A i j) := by
  simp only [planeGenerator,sub_mul,mul_sub,Matrix.single_mul_mul_single,one_mul,mul_one]
  abel

lemma sum_single_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, Matrix.single i j (A j i)) = A.transpose := by
  classical
  ext k l
  simp [Matrix.sum_apply,Matrix.single_apply,ite_and]

lemma sum_single_trace_diagonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, Matrix.single i i (A j j)) = A.trace • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  classical
  ext k l
  by_cases h : k=l
  · subst l
    simp [Matrix.sum_apply,Matrix.single_apply,Matrix.trace,Matrix.diag_apply]
  · simp [Matrix.sum_apply,Matrix.single_apply,h,ite_and]

theorem sum_planeGenerator_sandwich {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, planeGenerator i j*A*planeGenerator i j) =
      (2 : ℝ) • A.transpose-(2*A.trace) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  simp_rw [planeGenerator_sandwich,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hs : (∑ i : Fin N, ∑ j : Fin N, Matrix.single j i (A i j)) = A.transpose := by
    rw [Finset.sum_comm]
    exact sum_single_transpose A
  have hd : (∑ i : Fin N, ∑ j : Fin N, Matrix.single j j (A i i)) =
      A.trace • (1 : Matrix (Fin N) (Fin N) ℝ) := by
    rw [Finset.sum_comm]
    exact sum_single_trace_diagonal A
  rw [sum_single_transpose,sum_single_trace_diagonal,hs,hd]
  module

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneCasimir
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact orthogonal Lie-algebra contractions in the unnormalized Frobenius convention. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma sum_planeGenerator_sq {N : ℕ} :
    (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j) =
      (-2*((N : ℝ)-1)) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  have h := sum_planeGenerator_sandwich (1 : Matrix (Fin N) (Fin N) ℝ)
  simp only [mul_one,transpose_one,trace_one,Fintype.card_fin] at h
  rw [h]
  module

lemma skew_matrix_trace_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.transpose = -A) : A.trace = 0 := by
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose,Matrix.trace_neg] at h
  linarith

theorem sum_planeGenerator_double_commutator {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i : Fin N, ∑ j : Fin N,
      (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
        (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) =
      (-4*((N : ℝ)-2)) • A := by
  have he (i j : Fin N) :
      planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
        (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j =
      (planeGenerator i j*planeGenerator i j)*A-
        (2 : ℝ) • (planeGenerator i j*A*planeGenerator i j)+
        A*(planeGenerator i j*planeGenerator i j) := by
    simp only [two_smul]
    noncomm_ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hl : (∑ i : Fin N, ∑ j : Fin N, (planeGenerator i j*planeGenerator i j)*A) =
      (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j)*A := by
    simp only [Finset.sum_mul]
  have hr : (∑ i : Fin N, ∑ j : Fin N, A*(planeGenerator i j*planeGenerator i j)) =
      A*(∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*planeGenerator i j) := by
    simp only [Finset.mul_sum]
  have hm : (∑ i : Fin N, ∑ j : Fin N, (2 : ℝ) • (planeGenerator i j*A*planeGenerator i j)) =
      (2 : ℝ) • (∑ i : Fin N, ∑ j : Fin N, planeGenerator i j*A*planeGenerator i j) := by
    simp only [Finset.smul_sum]
  rw [hl,hr,hm,sum_planeGenerator_sq,sum_planeGenerator_sandwich,hA,skew_matrix_trace_zero hA]
  simp only [mul_zero,zero_smul,sub_zero,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  module

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFrobeniusBracket
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Frobenius bracket contraction for the special orthogonal algebra. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma matrixFrobeniusPair_self {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A A = ∑ i, ∑ j, (A i j)^2 := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply,pow_two]
  exact Finset.sum_comm

lemma planeGenerator_transpose {N : ℕ} (i j : Fin N) :
    (planeGenerator i j).transpose = -planeGenerator i j := by
  simp [planeGenerator,Matrix.transpose_sub,Matrix.transpose_single,neg_sub]

lemma matrixFrobeniusPair_bracket {N : ℕ}
    (E A B : Matrix (Fin N) (Fin N) ℝ) (hE : E.transpose = -E) :
    matrixFrobeniusPair (E*A-A*E) B = -matrixFrobeniusPair A (E*B-B*E) := by
  simp only [matrixFrobeniusPair,Matrix.transpose_sub,Matrix.transpose_mul,hE,
    Matrix.mul_neg,Matrix.neg_mul,Matrix.sub_mul,Matrix.mul_sub,Matrix.trace_sub,
    Matrix.trace_neg]
  rw [← mul_assoc A.transpose E B,Matrix.trace_mul_cycle E A.transpose B]
  rw [Matrix.trace_mul_cycle B E A.transpose]
  simp only [mul_assoc]
  ring

/-- Ordered coordinate planes count each orthogonal tangent direction twice. -/
theorem sum_planeGenerator_bracket_norm_sq {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i : Fin N, ∑ j : Fin N,
      matrixFrobeniusPair (planeGenerator i j*A-A*planeGenerator i j)
        (planeGenerator i j*A-A*planeGenerator i j)) =
      (4*((N : ℝ)-2))*matrixFrobeniusPair A A := by
  simp_rw [matrixFrobeniusPair_bracket _ _ _ (planeGenerator_transpose _ _)]
  simp only [Finset.sum_neg_distrib]
  have hs : (∑ i : Fin N, ∑ j : Fin N,
      matrixFrobeniusPair A
        (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
          (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) =
      matrixFrobeniusPair A (∑ i : Fin N, ∑ j : Fin N,
        (planeGenerator i j*(planeGenerator i j*A-A*planeGenerator i j)-
          (planeGenerator i j*A-A*planeGenerator i j)*planeGenerator i j)) := by
    simp only [matrixFrobeniusPair,Matrix.mul_sum,Matrix.trace_sum]
  rw [hs,sum_planeGenerator_double_commutator A hA]
  simp only [matrixFrobeniusPair,Matrix.mul_smul,Matrix.trace_smul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneFrame
attribute [-simp] _root_.OAI.InvariantIsing.matrixPolynomialDerivation_plane_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-plane frame identities in the skew matrix space. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_swap {N : ℕ} (i j : Fin N) :
    planeGenerator j i = -planeGenerator i j := by
  simp only [planeGenerator,neg_sub]

lemma sum_entry_planeGenerator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (∑ i, ∑ j, A i j • planeGenerator i j) = A-A.transpose := by
  classical
  ext k l
  simp only [Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    planeGenerator,Matrix.single_apply,mul_sub,Finset.sum_sub_distrib]
  simp [ite_and,Matrix.transpose_apply]

lemma matrixFrobeniusPair_eq_sum {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixFrobeniusPair A B = ∑ i, ∑ j, A i j*B i j := by
  simp only [matrixFrobeniusPair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.transpose_apply]
  exact Finset.sum_comm

lemma matrixFrobeniusPair_plane {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixFrobeniusPair A (planeGenerator i j) = A i j-A j i := by
  classical
  rw [matrixFrobeniusPair_eq_sum]
  simp [planeGenerator,Matrix.single_apply,Matrix.sub_apply,mul_sub,
    Finset.sum_sub_distrib,ite_and]

lemma skew_matrix_bracket {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.transpose = -A) (hB : B.transpose = -B) :
    (A*B-B*A).transpose = -(A*B-B*A) := by
  simp only [Matrix.transpose_sub,Matrix.transpose_mul,hA,hB,neg_mul_neg,neg_sub]

lemma matrixFrobeniusPair_plane_skew {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (i j : Fin N) :
    matrixFrobeniusPair A (planeGenerator i j) = 2*A i j := by
  have h : A j i = -A i j := congrFun (congrFun hA i) j
  rw [matrixFrobeniusPair_plane,h]
  ring

lemma sum_matrixFrobeniusPair_plane_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) :
    (∑ i, ∑ j, (matrixFrobeniusPair A (planeGenerator i j))^2) =
      4*matrixFrobeniusPair A A := by
  simp_rw [matrixFrobeniusPair_plane_skew A hA]
  rw [matrixFrobeniusPair_self]
  simp only [mul_pow,show (2:ℝ)^2=4 by norm_num,Finset.mul_sum]

/-- A linear functional on skew matrices is represented by its plane coordinates. -/
lemma plane_functional_representation {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.transpose = -B) :
    matrixFrobeniusPair (Matrix.of fun i j => ell (planeGenerator i j)) B = 2*ell B := by
  have h := congrArg ell (sum_entry_planeGenerator B)
  simp only [map_sum,map_smul,map_sub,hB,map_neg,smul_eq_mul] at h
  rw [matrixFrobeniusPair_eq_sum]
  calc
    (∑ i, ∑ j, ell (planeGenerator i j)*B i j) =
        ∑ i, ∑ j, B i j*ell (planeGenerator i j) := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    _ = 2*ell B := by linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPlaneAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the adjoint action in the redundant coordinate-plane frame. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeGenerator_adjoint_expansion {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (i j : Fin N) :
    A*planeGenerator i j-planeGenerator i j*A =
      (∑ k, A k i • planeGenerator k j)+(∑ k, A k j • planeGenerator i k) := by
  classical
  have hskew (k l : Fin N) : A k l = -A l k := congrFun (congrFun hA l) k
  ext k l
  simp only [planeGenerator,Matrix.mul_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    Matrix.sum_apply,Matrix.single_apply,smul_eq_mul,mul_sub,sub_mul,
    Finset.sum_sub_distrib]
  simp only [ite_and,mul_ite,ite_mul,mul_one,one_mul,mul_zero,zero_mul,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.sum_const_zero,Finset.mem_univ,ite_true, if_true]
  rw [hskew l i,hskew l j]
  split_ifs <;> ring

lemma sum_skew_symmetric_coeff {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (T : Fin N → Fin N → V) (hT : ∀ i j, T i j = T j i) :
    (∑ i, ∑ j, A i j • T i j) = 0 := by
  have hskew (i j : Fin N) : A j i = -A i j := congrFun (congrFun hA i) j
  have hs : (∑ i, ∑ j, A i j • T i j) = -(∑ i, ∑ j, A i j • T i j) := by
    calc
      (∑ i, ∑ j, A i j • T i j) = ∑ i, ∑ j, A j i • T j i := Finset.sum_comm
      _ = ∑ i, ∑ j, -(A i j • T i j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hskew i j,hT j i,neg_smul]
      _ = -(∑ i, ∑ j, A i j • T i j) := by
        simp only [Finset.sum_neg_distrib]
  have hz : (2 : ℝ) • (∑ i, ∑ j, A i j • T i j) = 0 := by
    rw [two_smul]
    nth_rw 1 [hs]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCasimirAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adjoint invariance of the quadratic orthogonal Casimir in any representation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma sum_skew_symmetric_coeff_swap {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (T : Fin N → Fin N → V) (hT : ∀ i j, T i j = T j i) :
    (∑ i, ∑ j, A j i • T i j) = 0 := by
  rw [Finset.sum_comm]
  exact sum_skew_symmetric_coeff A hA (fun i j => T j i) (fun i j => hT j i)

/-- The coefficient cancellation uses only skew symmetry, with no analytic premise. -/
theorem plane_adjoint_jordan_sum {N : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (F : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] Module.End ℝ V)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    (∑ i, ∑ j,
      (F (planeGenerator i j)*F (A*planeGenerator i j-planeGenerator i j*A)+
       F (A*planeGenerator i j-planeGenerator i j*A)*F (planeGenerator i j))) = 0 := by
  let x := fun i j => F (planeGenerator i j)
  have he (i j : Fin N) :
      F (planeGenerator i j)*F (A*planeGenerator i j-planeGenerator i j*A)+
        F (A*planeGenerator i j-planeGenerator i j*A)*F (planeGenerator i j) =
      (∑ k, A k i • (x i j*x k j+x k j*x i j))+
        ∑ k, A k j • (x i j*x i k+x i k*x i j) := by
    rw [planeGenerator_adjoint_expansion A hA i j,map_add,map_sum,map_sum]
    simp only [map_smul,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
      smul_mul_assoc,mul_smul_comm,smul_add]
    dsimp only [x]
    simp only [Finset.sum_add_distrib]
    abel
  simp_rw [he,Finset.sum_add_distrib]
  have h₁ : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      A k i • (x i j*x k j+x k j*x i j)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    exact sum_skew_symmetric_coeff_swap A hA _ (fun i k => add_comm _ _)
  have h₂ : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      A k j • (x i j*x i k+x i k*x i j)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact sum_skew_symmetric_coeff_swap A hA _ (fun j k => add_comm _ _)
  rw [h₁,h₂,zero_add]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_SpecialPlaneRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine coordinate-plane rotations and infinitesimal Haar invariance on
`SO(N)`, the rotation group used by the actual enriched model. -/

noncomputable section

open MeasureTheory Filter IsingPerceptron
open scoped Topology Matrix Matrix.Norms.Frobenius

namespace InvariantIsing

/-- A dominated infinitesimal left rotation has Haar mean zero. -/
lemma integral_special_rotation_derivative_eq_zero {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [μ.IsMulLeftInvariant] (R : ℝ → SpecialOrthogonal N) (hR : R 0 = 1)
    (f : SpecialOrthogonal N → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (f' : ℝ → SpecialOrthogonal N → ℝ) (hf' : AEStronglyMeasurable (f' 0) μ)
    (B : SpecialOrthogonal N → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ B U)
    (hderiv : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t) :
    ∫ U, f' 0 U ∂μ = 0 := by
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun U => f (R t * U)) μ := by
    apply Filter.Eventually.of_forall
    intro t
    have hmul : Measurable (fun U : SpecialOrthogonal N => R t * U) := by
      apply Measurable.subtype_mk
      change Measurable (fun U : SpecialOrthogonal N =>
        (R t : Matrix (Fin N) (Fin N) ℝ) * (U : Matrix (Fin N) (Fin N) ℝ))
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      simp only [Matrix.mul_apply]
      exact Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply j).comp
          ((measurable_pi_apply k).comp measurable_subtype_coe))
    exact (hf.comp hmul).aestronglyMeasurable
  have hi : Integrable (fun U => f (R 0 * U)) μ := by simpa only [hR, one_mul] using hfi
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hf'
    hbound hB hderiv
  have he : (fun t => ∫ U, f (R t * U) ∂μ) = fun _ : ℝ => ∫ U, f U ∂μ := by
    funext t
    exact integral_mul_left_eq_self f (R t)
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (∫ U, f U ∂μ))


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialDerivation
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial directional derivatives for left matrix multiplication. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma matrixPolynomialDerivation_mul_X {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    matrixPolynomialDerivation A (matrixPolynomialDerivation B (X (i,j))) =
      matrixPolynomialDerivation (B*A) (X (i,j)) := by
  simp only [matrixPolynomialDerivation_X,map_sum,Derivation.map_smul_of_tower,Finset.smul_sum,
    smul_smul,Matrix.mul_apply,Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Left matrix vector fields give the opposite matrix Lie bracket. -/
theorem matrixPolynomialDerivation_commutator {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) :
    ⁅matrixPolynomialDerivation A,matrixPolynomialDerivation B⁆ =
      matrixPolynomialDerivation (B*A-A*B) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i,j⟩
  rw [Derivation.commutator_apply,matrixPolynomialDerivation_mul_X,
    matrixPolynomialDerivation_mul_X,map_sub,Derivation.sub_apply]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurve
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixPolynomialOperator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation of polynomial Lie derivatives on genuine matrix curves. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

theorem hasDerivAt_matrixPolynomialEval {N : ℕ}
    (p : MatrixPolynomial N) (M : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) ((A*M t) i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (M s) p)
      (matrixPolynomialEval (M t) (matrixPolynomialDerivation A p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const t c
  | add p q hp hq =>
    convert hp.add hq using 1
    all_goals try with_reducible_and_instances rfl
    all_goals simp only [map_add]
    all_goals rfl
  | mul_X p ij hp =>
    rcases ij with ⟨i,j⟩
    have hx : matrixPolynomialEval (M t)
        (matrixPolynomialDerivation A (X (i,j))) = (A*M t) i j := by
      simp only [matrixPolynomialDerivation_X,map_sum,map_smul,
        matrixPolynomialEval_X,smul_eq_mul,Matrix.mul_apply]
    convert hp.mul (hM i j) using 1
    all_goals try with_reducible_and_instances rfl
    · simp only [map_mul,matrixPolynomialEval_X]
      rfl
    · rw [Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,
        hx,matrixPolynomialEval_X]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialRotation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial differentiation along the actual special-orthogonal rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
namespace InvariantIsing

lemma hasDerivAt_specialPlaneRotation_entry {N : ℕ}
    (i j k l : Fin N) (U : SpecialOrthogonal N) (t : ℝ) :
    HasDerivAt (fun s => ((specialPlaneRotation i j s*U : SpecialOrthogonal N) :
        Matrix (Fin N) (Fin N) ℝ) k l)
      ((planeGenerator i j*((specialPlaneRotation i j t*U : SpecialOrthogonal N) :
        Matrix (Fin N) (Fin N) ℝ)) k l) t := by
  let A := planeGenerator i j
  let ev := haarMatrixCoordinate k l
  have hd := ev.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const' A t).mul_const (U : Matrix (Fin N) (Fin N) ℝ))
  refine hd.congr_deriv (Eq.symm ?_)
  · change (A*(NormedSpace.exp (t • A)*(U : Matrix (Fin N) (Fin N) ℝ))) k l =
      (A*NormedSpace.exp (t • A)*(U : Matrix (Fin N) (Fin N) ℝ)) k l
    rw [mul_assoc]

theorem hasDerivAt_specialPlaneRotation_polynomial {N : ℕ}
    (p : MatrixPolynomial N) (i j : Fin N) (U : SpecialOrthogonal N) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval
        ((specialPlaneRotation i j s*U : SpecialOrthogonal N) :
          Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval
        ((specialPlaneRotation i j t*U : SpecialOrthogonal N) :
          Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation (planeGenerator i j) p)) t :=
  hasDerivAt_matrixPolynomialEval p _ _ t
    (fun k l => hasDerivAt_specialPlaneRotation_entry i j k l U t)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialValue
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded continuous polynomial observables on the physical rotation group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

/-- Infinitesimal Haar invariance, with the domination supplied by compactness. -/
theorem integral_haarPolynomialDerivation {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (i j : Fin N) :
    (∫ U, haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U ∂μ) = 0 := by
  let q := matrixPolynomialDerivation (planeGenerator i j) p
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound q
  have he := integral_special_rotation_derivative_eq_zero μ
    (specialPlaneRotation i j) (specialPlaneRotation_zero i j)
    (haarPolynomialValue p) (continuous_haarPolynomialValue p).measurable
    (haarPolynomialValue_integrable p μ)
    (fun t U => haarPolynomialValue q (specialPlaneRotation i j t*U))
    (by simpa only [specialPlaneRotation_zero,one_mul] using
      (continuous_haarPolynomialValue q).measurable.aestronglyMeasurable)
    (fun _ => B) (integrable_const B)
    (ae_of_all μ fun U t _ => hB (specialPlaneRotation i j t*U))
    (ae_of_all μ fun U t _ => hasDerivAt_specialPlaneRotation_polynomial p i j U t)
  simpa only [specialPlaneRotation_zero,one_mul] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarContinuousDerivative
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.forestVertexCountable _root_.OAI.IsingPerceptron.labeledLeafCountable _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact domination for continuous derivatives along actual Haar rotations. -/
noncomputable section
open Matrix MeasureTheory
namespace InvariantIsing

lemma continuous_haar_integrable {N : ℕ} (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (f : SpecialOrthogonal N → ℝ) (hf : Continuous f) : Integrable f μ := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable B
    (ae_of_all μ fun U => hB U (Set.mem_univ U))

lemma integral_haar_continuous_derivative {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (i j : Fin N)
    (f q : SpecialOrthogonal N → ℝ) (hf : Continuous f) (hq : Continuous q)
    (hd : ∀ U : SpecialOrthogonal N, ∀ t : ℝ,
      HasDerivAt (fun s => f (specialPlaneRotation i j s*U))
        (q (specialPlaneRotation i j t*U)) t) :
    (∫ U, q U ∂μ) = 0 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  have he := integral_special_rotation_derivative_eq_zero μ
    (specialPlaneRotation i j) (specialPlaneRotation_zero i j) f hf.measurable
    (continuous_haar_integrable μ f hf) (fun t U => q (specialPlaneRotation i j t*U))
    (by simpa only [specialPlaneRotation_zero,one_mul] using hq.measurable.aestronglyMeasurable)
    (fun _ => B) (integrable_const B)
    (ae_of_all μ fun U t _ => hB (specialPlaneRotation i j t*U) (Set.mem_univ _))
    (ae_of_all μ fun U t _ => hd U t)
  simpa only [specialPlaneRotation_zero,one_mul] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarFunctionalCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum of squared Lie brackets, with the precise dimension factor. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma planeFunctionalMatrix_skew {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (planeFunctionalMatrix ell).transpose = -planeFunctionalMatrix ell := by
  ext i j
  change ell (planeGenerator j i) = -ell (planeGenerator i j)
  rw [planeGenerator_swap,map_neg]

lemma sum_plane_functional_bracket_sq {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (E : Matrix (Fin N) (Fin N) ℝ) (hE : E.transpose = -E) :
    (∑ i, ∑ j, (ell (E*planeGenerator i j-planeGenerator i j*E))^2) =
      matrixFrobeniusPair (E*planeFunctionalMatrix ell-planeFunctionalMatrix ell*E)
        (E*planeFunctionalMatrix ell-planeFunctionalMatrix ell*E) := by
  let A := planeFunctionalMatrix ell
  have hA : A.transpose = -A := planeFunctionalMatrix_skew ell
  have hs (i j : Fin N) :
      4*(ell (E*planeGenerator i j-planeGenerator i j*E))^2 =
        (matrixFrobeniusPair (E*A-A*E) (planeGenerator i j))^2 := by
    have hr := plane_functional_representation ell
      (E*planeGenerator i j-planeGenerator i j*E)
      (skew_matrix_bracket hE (planeGenerator_transpose i j))
    have hb := matrixFrobeniusPair_bracket E A (planeGenerator i j) hE
    change matrixFrobeniusPair A _ = _ at hr
    rw [hr] at hb
    rw [hb]
    ring
  have ht := sum_matrixFrobeniusPair_plane_sq (E*A-A*E) (skew_matrix_bracket hE hA)
  simp_rw [← hs] at ht
  simp only [← Finset.mul_sum] at ht
  change _ = matrixFrobeniusPair (E*A-A*E) (E*A-A*E)
  linarith

/-- The ordered-plane convention has curvature factor `N - 2`. The factor
four here becomes one after the antisymmetric Hessian estimate. -/
theorem sum_plane_functional_double_bracket_sq {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (ell (planeGenerator i j*planeGenerator k l-
        planeGenerator k l*planeGenerator i j))^2) =
      (4*((N : ℝ)-2))*(∑ i, ∑ j, (ell (planeGenerator i j))^2) := by
  simp_rw [sum_plane_functional_bracket_sq ell _ (planeGenerator_transpose _ _)]
  rw [sum_planeGenerator_bracket_norm_sq _ (planeFunctionalMatrix_skew ell),
    matrixFrobeniusPair_self]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHessianBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The antisymmetric part of a finite Hessian controls the curvature term. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

theorem sum_antisymmetric_square_le {J : Type*} [Fintype J] (H : J → J → ℝ) :
    (∑ i, ∑ j, (H i j-H j i)^2) ≤ 4*(∑ i, ∑ j, (H i j)^2) := by
  calc
    (∑ i, ∑ j, (H i j-H j i)^2) ≤
        ∑ i, ∑ j, 2*((H i j)^2+(H j i)^2) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      nlinarith [sq_nonneg (H i j+H j i)]
    _ = 4*(∑ i, ∑ j, (H i j)^2) := by
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2*(H j i)^2)]
      simp only [← Finset.mul_sum]
      ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialLaplacian
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial Laplacian on the orthogonal group commutes with rotations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma matrixPolynomialOperator_commutator {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialOperator A*matrixPolynomialOperator B-
      matrixPolynomialOperator B*matrixPolynomialOperator A =
      matrixPolynomialOperator (B*A-A*B) := by
  apply LinearMap.ext
  intro p
  exact Derivation.congr_fun (matrixPolynomialDerivation_commutator A B) p

lemma commutator_square_identity {R : Type*} [Ring R] (X Y : R) :
    X*(Y*Y)-(Y*Y)*X = -(Y*(Y*X-X*Y)+(Y*X-X*Y)*Y) := by
  noncomm_ring

theorem haarPolynomialLaplacian_commutes {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) :
    matrixPolynomialOperator A*haarPolynomialLaplacian N =
      haarPolynomialLaplacian N*matrixPolynomialOperator A := by
  apply sub_eq_zero.mp
  have he (i j : Fin N) :
      matrixPolynomialOperator A*
          (matrixPolynomialOperator (planeGenerator i j)*matrixPolynomialOperator (planeGenerator i j))-
        (matrixPolynomialOperator (planeGenerator i j)*matrixPolynomialOperator (planeGenerator i j))*
          matrixPolynomialOperator A =
      -(matrixPolynomialOperator (planeGenerator i j)*
            matrixPolynomialOperator (A*planeGenerator i j-planeGenerator i j*A)+
        matrixPolynomialOperator (A*planeGenerator i j-planeGenerator i j*A)*
            matrixPolynomialOperator (planeGenerator i j)) := by
    rw [← matrixPolynomialOperator_commutator (planeGenerator i j) A]
    exact commutator_square_identity _ _
  simp only [haarPolynomialLaplacian,Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  simp_rw [he]
  simp only [Finset.sum_neg_distrib]
  rw [plane_adjoint_jordan_sum matrixPolynomialOperator A hA,neg_zero]

lemma haarPolynomialLaplacian_derivation {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A) (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (matrixPolynomialDerivation A p) =
      matrixPolynomialDerivation A (haarPolynomialLaplacian N p) := by
  exact (LinearMap.congr_fun (haarPolynomialLaplacian_commutes A hA) p).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialGamma
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Product and second-order identities for the actual polynomial rotation operator. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma derivation_double_product {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (p q : A) :
    D (D (p*q)) = p*D (D q)+q*D (D p)+2*(D p*D q) := by
  simp only [Derivation.leibniz,map_add,smul_eq_mul]
  ring

lemma haarPolynomialLaplacian_mul {N : ℕ} (p q : MatrixPolynomial N) :
    haarPolynomialLaplacian N (p*q) = p*haarPolynomialLaplacian N q+
      q*haarPolynomialLaplacian N p+2*haarPolynomialGamma p q := by
  simp only [haarPolynomialLaplacian_apply,derivation_double_product,
    haarPolynomialGamma,Finset.sum_add_distrib,Finset.mul_sum]

lemma haarPolynomialLaplacian_sq {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (p^2) =
      2*(p*haarPolynomialLaplacian N p+haarPolynomialGamma p p) := by
  rw [pow_two,haarPolynomialLaplacian_mul]
  ring

/-- The exact Bochner identity before the nonnegative Hessian estimate. -/
theorem haarPolynomial_bochner_identity {N : ℕ} (p : MatrixPolynomial N) :
    haarPolynomialLaplacian N (haarPolynomialGamma p p) =
      2*(haarPolynomialGamma p (haarPolynomialLaplacian N p)+
        ∑ i, ∑ j, ∑ k, ∑ l,
          (matrixPolynomialDerivation (planeGenerator k l)
            (matrixPolynomialDerivation (planeGenerator i j) p))^2) := by
  unfold haarPolynomialGamma
  simp only [map_sum]
  simp_rw [← pow_two,haarPolynomialLaplacian_sq,
    haarPolynomialLaplacian_derivation _ (planeGenerator_transpose _ _)]
  simp only [haarPolynomialGamma,pow_two,mul_add,Finset.mul_sum,Finset.sum_add_distrib]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialCurvature
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature inequality for polynomial observables, proved by finite algebra. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma matrixPolynomial_hessian_bound {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    ((N : ℝ)-2)*(matrixPolynomialEval M (haarPolynomialGamma p p)) ≤
      ∑ i, ∑ j, ∑ k, ∑ l,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l)
          (matrixPolynomialDerivation (planeGenerator i j) p)))^2 := by
  let ell := matrixPolynomialDifferential p M
  let H : (Fin N × Fin N) → (Fin N × Fin N) → ℝ := fun a b =>
    matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))
  have hd (a b : Fin N × Fin N) : H a b-H b a =
      ell (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
        planeGenerator b.1 b.2*planeGenerator a.1 a.2) := by
    change matrixPolynomialEval M
        (matrixPolynomialDerivation (planeGenerator b.1 b.2)
          (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      matrixPolynomialEval M
        (matrixPolynomialDerivation (planeGenerator a.1 a.2)
          (matrixPolynomialDerivation (planeGenerator b.1 b.2) p)) =
      matrixPolynomialEval M (matrixPolynomialDerivation
        (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
          planeGenerator b.1 b.2*planeGenerator a.1 a.2) p)
    rw [← map_sub]
    exact congrArg (matrixPolynomialEval M) (Derivation.congr_fun
      (matrixPolynomialDerivation_commutator
        (planeGenerator b.1 b.2) (planeGenerator a.1 a.2)) p)
  have hb := sum_antisymmetric_square_le H
  simp_rw [hd] at hb
  simp only [Fintype.sum_prod_type] at hb
  rw [sum_plane_functional_double_bracket_sq ell] at hb
  have hg : (∑ i : Fin N, ∑ j : Fin N, (ell (planeGenerator i j))^2) =
      matrixPolynomialEval M (haarPolynomialGamma p p) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  rw [hg] at hb
  dsimp only [H] at hb
  linarith

/-- With the ordered-plane Laplacian, the Ricci lower bound is `N - 2`. -/
theorem matrixPolynomial_curvature {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) :
    ((N : ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
        matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p)) := by
  have h := congrArg (matrixPolynomialEval M) (haarPolynomial_bochner_identity p)
  simp only [map_mul,map_ofNat,map_add,map_sum,map_pow] at h
  have hb := matrixPolynomial_hessian_bound p M
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCorrectedHessian
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature estimate survives a symmetric gradient-square correction. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma matrixPolynomial_corrected_hessian_bound {N : ℕ}
    (p : MatrixPolynomial N) (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      ∑ i, ∑ j, ∑ k, ∑ l,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l)
          (matrixPolynomialDerivation (planeGenerator i j) p))-
          c*matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p)*
            matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator k l) p))^2 := by
  let ell := matrixPolynomialDifferential p M
  let H : (Fin N × Fin N) → (Fin N × Fin N) → ℝ := fun a b =>
    matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      c*ell (planeGenerator a.1 a.2)*ell (planeGenerator b.1 b.2)
  have hd (a b : Fin N × Fin N) : H a b-H b a =
      ell (planeGenerator a.1 a.2*planeGenerator b.1 b.2-
        planeGenerator b.1 b.2*planeGenerator a.1 a.2) := by
    have he := congrArg (matrixPolynomialEval M) (Derivation.congr_fun
      (matrixPolynomialDerivation_commutator
        (planeGenerator b.1 b.2) (planeGenerator a.1 a.2)) p)
    change matrixPolynomialEval M (_-_) = _ at he
    rw [map_sub] at he
    change matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
        (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))-
      matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2)
        (matrixPolynomialDerivation (planeGenerator b.1 b.2) p)) = _ at he
    dsimp only [H,ell,matrixPolynomialDifferential,LinearMap.coe_mk,AddHom.coe_mk]
    linear_combination he
  have hb := sum_antisymmetric_square_le H
  simp_rw [hd] at hb
  simp only [Fintype.sum_prod_type] at hb
  rw [sum_plane_functional_double_bracket_sq ell] at hb
  have hg : (∑ i : Fin N, ∑ j : Fin N, (ell (planeGenerator i j))^2) =
      matrixPolynomialEval M (haarPolynomialGamma p p) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  rw [hg] at hb
  dsimp only [H,ell,matrixPolynomialDifferential,LinearMap.coe_mk,AddHom.coe_mk] at hb
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarDirectionBound
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Directional control by coordinate-plane derivatives. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma plane_functional_abs_bound {N : ℕ}
    (ell : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.transpose = -A)
    (δ : ℝ) (hδ : ∀ i j, |ell (planeGenerator i j)| ≤ δ) :
    2*|ell A| ≤ (∑ i, ∑ j, |A i j|)*δ := by
  have hr := plane_functional_representation ell A hA
  rw [matrixFrobeniusPair_eq_sum] at hr
  change (∑ i, ∑ j, ell (planeGenerator i j)*A i j) = 2*ell A at hr
  have hs : |∑ i, ∑ j, ell (planeGenerator i j)*A i j| ≤
      (∑ i, ∑ j, |A i j|)*δ := by
    calc
      |∑ i, ∑ j, ell (planeGenerator i j)*A i j| ≤
          ∑ i, |∑ j, ell (planeGenerator i j)*A i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |ell (planeGenerator i j)*A i j| := by
        apply Finset.sum_le_sum; intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |A i j| * δ := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_left (hδ i j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |A i j|)*δ := by simp only [Finset.sum_mul]
  rw [hr,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hs
  exact hs

lemma matrixPolynomial_direction_bound {N : ℕ}
    (p : MatrixPolynomial N) (M A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.transpose = -A) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : matrixPolynomialEval M (haarPolynomialGamma p p) ≤ δ^2) :
    2*|matrixPolynomialEval M (matrixPolynomialDerivation A p)| ≤
      (∑ i, ∑ j, |A i j|)*δ := by
  apply plane_functional_abs_bound (matrixPolynomialDifferential p M) A hA δ
  intro i j
  change |matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p)| ≤ δ
  have hpos (i j : Fin N) :
      0 ≤ (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 :=
    sq_nonneg _
  have htotal : matrixPolynomialEval M (haarPolynomialGamma p p) =
      ∑ i : Fin N, ∑ j : Fin N,
        (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 := by
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
  have hs : (matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator i j) p))^2 ≤ δ^2 := by
    apply le_trans _ hp
    rw [htotal]
    exact (Finset.single_le_sum (fun k _ => hpos i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hpos k l)) (Finset.mem_univ i))
  exact (sq_le_sq₀ (abs_nonneg _) hδ).mp (by simpa only [sq_abs] using hs)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCurveTangent
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The velocity of an actual orthogonal curve is a skew left tangent. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma orthogonalCurve_tangent_skew {N : ℕ} (U : ℝ → SpecialOrthogonal N)
    (B : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hB : ∀ i j, HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B i j) t) :
    (B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose).transpose =
      -(B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) := by
  have hm (s : ℝ) := (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp (U s).property).1
  have hz (i j : Fin N) :
      (∑ k, (B i k*(U t : Matrix (Fin N) (Fin N) ℝ) j k+
        (U t : Matrix (Fin N) (Fin N) ℝ) i k*B j k)) = 0 := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hB i k).mul (hB j k)
    have he : (fun s => ∑ k, (U s : Matrix (Fin N) (Fin N) ℝ) i k*
        (U s : Matrix (Fin N) (Fin N) ℝ) j k) =
        fun _ : ℝ => (1 : Matrix (Fin N) (Fin N) ℝ) i j := by
      funext s
      exact congrFun (congrFun (hm s) i) j
    change HasDerivAt (fun s => ∑ k, (U s : Matrix (Fin N) (Fin N) ℝ) i k*
      (U s : Matrix (Fin N) (Fin N) ℝ) j k) _ t at hd
    rw [he] at hd
    exact hd.unique (hasDerivAt_const t _)
  have hadd : B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose+
      (U t : Matrix (Fin N) (Fin N) ℝ)*B.transpose=0 := by
    ext i j
    simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.zero_apply,Finset.sum_add_distrib] using hz i j
  rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hadd

lemma orthogonalCurve_tangent_mul {N : ℕ} (U : SpecialOrthogonal N)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    (B*(U : Matrix (Fin N) (Fin N) ℝ).transpose)*(U : Matrix (Fin N) (Fin N) ℝ) = B := by
  rw [mul_assoc,(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp
    (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1,mul_one]

lemma orthogonalCurve_polynomial_derivative {N : ℕ} (p : MatrixPolynomial N)
    (U : ℝ → SpecialOrthogonal N) (B : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (hB : ∀ i j, HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B i j) t) :
    HasDerivAt (fun s => matrixPolynomialEval (U s : Matrix (Fin N) (Fin N) ℝ) p)
      (matrixPolynomialEval (U t : Matrix (Fin N) (Fin N) ℝ)
        (matrixPolynomialDerivation (B*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) p)) t := by
  apply hasDerivAt_matrixPolynomialEval
  intro i j
  rw [orthogonalCurve_tangent_mul]
  exact hB i j

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarCurveBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrating the coordinate-plane gradient bound along an orthogonal curve. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomial_curve_bound {N : ℕ} (p : MatrixPolynomial N)
    (U : ℝ → SpecialOrthogonal N) (B : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (K δ : ℝ) (hδ : 0 ≤ δ)
    (hB : ∀ t ∈ Icc (0:ℝ) 1, ∀ i j,
      HasDerivAt (fun s => (U s : Matrix (Fin N) (Fin N) ℝ) i j) (B t i j) t)
    (hK : ∀ t ∈ Icc (0:ℝ) 1,
      (∑ i, ∑ j, |(B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) i j|) ≤ K)
    (hp : ∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) :
    |haarPolynomialValue p (U 1)-haarPolynomialValue p (U 0)| ≤ K*δ/2 := by
  let f' := fun t => matrixPolynomialEval (U t : Matrix (Fin N) (Fin N) ℝ)
    (matrixPolynomialDerivation (B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose) p)
  have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun s => haarPolynomialValue p (U s)) (f' t) t :=
    orthogonalCurve_polynomial_derivative p U (B t) t (hB t ht)
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ‖f' t‖ ≤ K*δ/2 := by
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hx := matrixPolynomial_direction_bound p
      (U t : Matrix (Fin N) (Fin N) ℝ)
      (B t*(U t : Matrix (Fin N) (Fin N) ℝ).transpose)
      (orthogonalCurve_tangent_skew U (B t) t (hB t ht')) δ hδ (hp (U t))
    have hy := mul_le_mul_of_nonneg_right (hK t ht') hδ
    change |f' t| ≤ K*δ/2
    dsimp [f'] at *
    linarith
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hd t ht).hasDerivWithinAt) hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarDifferentiableCurve
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafNonempty _root_.OAI.IsingPerceptron.labeledTreeNonempty _root_.OAI.IsingPerceptron.markForestNonempty _root_.OAI.IsingPerceptron.noiseLeafNonempty _root_.OAI.IsingPerceptron.noiseTreeNonempty _root_.OAI.IsingPerceptron.rawLeafNonempty _root_.OAI.IsingPerceptron.rawTreeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-coordinate differentiable curves and their polynomial oscillation bounds. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

namespace HaarDifferentiableCurve

lemma polynomial_bound {N : ℕ} (γ : HaarDifferentiableCurve N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : MatrixPolynomial N) (δ : ℝ), 0 ≤ δ →
      (∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) →
      |haarPolynomialValue p (γ.value 1)-haarPolynomialValue p (γ.value 0)| ≤ K*δ := by
  let F := fun t => ∑ i : Fin N, ∑ j : Fin N,
    |(γ.velocity t*(γ.value t : Matrix (Fin N) (Fin N) ℝ).transpose) i j|
  have hF : ContinuousOn F (Icc (0:ℝ) 1) := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply ContinuousOn.abs
    change ContinuousOn (fun t => ∑ k, γ.velocity t i k*
      (γ.value t : Matrix (Fin N) (Fin N) ℝ) j k) _
    exact continuousOn_finsetSum _ fun k _ =>
      (γ.continuous_velocity i k).mul (γ.continuous_entry j k)
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hF
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro p δ hδ hp
  have hk (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : F t ≤ max C 0 :=
    (hC (mem_image_of_mem F ht)).trans (le_max_left _ _)
  have hb := haarPolynomial_curve_bound p γ.value γ.velocity (max C 0) δ hδ γ.hasDeriv hk hp
  exact hb.trans (by nlinarith [mul_nonneg (le_max_right C 0) hδ])

end HaarDifferentiableCurve
end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial spaces, padded by the constant atom, for the rotation semigroup. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialSpace_le_succ (N d : ℕ) :
    haarPolynomialSpace N d ≤ haarPolynomialSpace N (d+1) := by
  intro p hp
  simpa only [haarPolynomialAtom,one_mul] using
    haarPolynomialSpace_atom_mul (none : Option (Fin N × Fin N)) hp

lemma haarPolynomialSpace_mono (N : ℕ) : Monotone (haarPolynomialSpace N) :=
  monotone_nat_of_le_succ (haarPolynomialSpace_le_succ N)

/-- Every multivariate polynomial belongs to one of the finite spaces. -/
theorem exists_mem_haarPolynomialSpace {N : ℕ} (p : MatrixPolynomial N) :
    ∃ d : ℕ, p ∈ haarPolynomialSpace N d := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0,?_⟩
    rw [MvPolynomial.C_eq_smul_one]
    exact (haarPolynomialSpace N 0).smul_mem c (one_mem_haarPolynomialSpace N 0)
  | add p q hp hq =>
    obtain ⟨d,hd⟩ := hp
    obtain ⟨e,he⟩ := hq
    exact ⟨max d e,(haarPolynomialSpace N (max d e)).add_mem
      (haarPolynomialSpace_mono N (le_max_left d e) hd)
      (haarPolynomialSpace_mono N (le_max_right d e) he)⟩
  | mul_X p ij hp =>
    obtain ⟨d,hd⟩ := hp
    refine ⟨d+1,?_⟩
    simpa only [haarPolynomialAtom,mul_comm] using
      haarPolynomialSpace_atom_mul (some ij) hd

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialHeat
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine finite-dimensional heat flow on each invariant polynomial space. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialHeat_zero (N d : ℕ) (p : haarPolynomialSpace N d) :
    haarPolynomialHeat N d 0 p = p := by
  simp [haarPolynomialHeat]

lemma haarPolynomialCoordinates_heat (N d : ℕ) (t : ℝ)
    (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinates N d (haarPolynomialHeat N d t p) =
      NormedSpace.exp (t • haarPolynomialCoordinateLaplacian N d)
        (haarPolynomialCoordinates N d p) := by
  simp only [haarPolynomialHeat,LinearMap.comp_apply,LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe,LinearEquiv.apply_symm_apply]

lemma haarPolynomialCoordinateLaplacian_apply (N d : ℕ)
    (p : haarPolynomialSpace N d) :
    haarPolynomialCoordinateLaplacian N d (haarPolynomialCoordinates N d p) =
      haarPolynomialCoordinates N d (haarPolynomialRestrictedLaplacian N d p) := by
  change haarPolynomialCoordinates N d
    (haarPolynomialRestrictedLaplacian N d
      ((haarPolynomialCoordinates N d).symm (haarPolynomialCoordinates N d p))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The finite matrix exponential satisfies the actual heat equation under evaluation. -/
theorem haarPolynomialHeat_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N))
      (matrixPolynomialEval M (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N))) t := by
  let L := haarPolynomialCoordinateLaplacian N d
  let v := haarPolynomialCoordinates N d p
  let ev := (haarPolynomialCoordinateEval M).comp
    (ContinuousLinearMap.apply ℝ (HaarPolynomialCoordinates N d) v)
  have h := ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' L t)
  have he (s : ℝ) : ev (NormedSpace.exp (s • L)) =
      matrixPolynomialEval M
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) := rfl
  change HasDerivAt (fun s => ev (NormedSpace.exp (s • L)))
    (ev (L*NormedSpace.exp (t • L))) t at h
  simp_rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change matrixPolynomialEval M _ =
    haarPolynomialCoordinateEval M (L (NormedSpace.exp (t • L) v))
  rw [← haarPolynomialCoordinates_heat,haarPolynomialCoordinateLaplacian_apply]
  exact (haarPolynomialCoordinateEval_apply M (haarPolynomialRestrictedLaplacian N d
    (haarPolynomialHeat N d t p))).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating linear observables of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

lemma haarPolynomialLinearCoordinates_apply {N d : ℕ}
    (F : MatrixPolynomial N →ₗ[ℝ] ℝ) (p : haarPolynomialSpace N d) :
    haarPolynomialLinearCoordinates F (haarPolynomialCoordinates N d p) = F (p : MatrixPolynomial N) := by
  change F (((haarPolynomialCoordinates N d).symm (haarPolynomialCoordinates N d p) :
    haarPolynomialSpace N d) : MatrixPolynomial N) = _
  rw [LinearEquiv.symm_apply_apply]

lemma haarPolynomialHeat_linear_hasDerivAt {N d : ℕ}
    (F : MatrixPolynomial N →ₗ[ℝ] ℝ) (p : haarPolynomialSpace N d) (t : ℝ) :
    HasDerivAt (fun s => F ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N))
      (F (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N))) t := by
  let L := haarPolynomialCoordinateLaplacian N d
  let v := haarPolynomialCoordinates N d p
  let ev := (haarPolynomialLinearCoordinates F).comp
    (ContinuousLinearMap.apply ℝ (HaarPolynomialCoordinates N d) v)
  have h := ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' L t)
  change HasDerivAt (fun s => ev (NormedSpace.exp (s • L)))
    (ev (L*NormedSpace.exp (t • L))) t at h
  have he (s : ℝ) : ev (NormedSpace.exp (s • L)) =
      F ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) := rfl
  simp_rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change F _ = haarPolynomialLinearCoordinates F (L (NormedSpace.exp (t • L) v))
  rw [← haarPolynomialCoordinates_heat,haarPolynomialCoordinateLaplacian_apply]
  exact (haarPolynomialLinearCoordinates_apply F (haarPolynomialRestrictedLaplacian N d
    (haarPolynomialHeat N d t p))).symm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatGammaDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time differentiation of the squared gradient along the actual polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialHeat_direction_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (A M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M (matrixPolynomialDerivation A
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)))
      (matrixPolynomialEval M (matrixPolynomialDerivation A (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)))) t :=
  haarPolynomialHeat_linear_hasDerivAt
    ((matrixPolynomialEval M).toLinearMap.comp (matrixPolynomialDerivation A).toLinearMap) p t

lemma haarPolynomialHeat_gamma_hasDerivAt {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    HasDerivAt (fun s => matrixPolynomialEval M (haarPolynomialGamma
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)))
      (2*matrixPolynomialEval M (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        (haarPolynomialLaplacian N
          ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)))) t := by
  have hd (i j : Fin N) := (haarPolynomialHeat_direction_hasDerivAt p (planeGenerator i j) M t).pow 2
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hd i j
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp only [haarPolynomialGamma,map_sum,map_mul,pow_two]
    rfl
  · simp only [haarPolynomialGamma,map_sum,map_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_ofNat]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatContinuity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the finite polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialEval_eq_coordinates {N d : ℕ}
    (p : haarPolynomialSpace N d) (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (p : MatrixPolynomial N) =
      ∑ i, haarPolynomialCoordinates N d p i*
        matrixPolynomialEval M (haarPolynomialBasis N d i) := by
  have hp : p = ∑ i, haarPolynomialCoordinates N d p i •
      (Module.finBasis ℝ (haarPolynomialSpace N d)) i := by
    simpa only [haarPolynomialCoordinates,LinearEquiv.symm_apply_apply] using
      ((Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun_symm_apply
        (haarPolynomialCoordinates N d p))
  conv_lhs => rw [hp]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
    haarPolynomialBasis]

lemma continuous_haarPolynomialHeat_coordinates {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun t : ℝ => haarPolynomialCoordinates N d (haarPolynomialHeat N d t p)) := by
  let L := haarPolynomialCoordinateLaplacian N d
  have hc : Continuous (fun t : ℝ => NormedSpace.exp (t • L)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_exp_smul_const' L t).continuousAt
  have hh := hc.clm_apply (continuous_const (y := haarPolynomialCoordinates N d p))
  simpa only [haarPolynomialCoordinates_heat] using hh

lemma continuous_haarPolynomialHeat_value {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N) z.2) := by
  have hc := continuous_haarPolynomialHeat_coordinates p
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i, haarPolynomialCoordinates N d (haarPolynomialHeat N d z.1 p) i*
        haarPolynomialValue (haarPolynomialBasis N d i) z.2) := by
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp hc).comp continuous_fst).mul
      ((continuous_haarPolynomialValue _).comp continuous_snd)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact haarPolynomialEval_eq_coordinates _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatOperator
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of differentiated heat polynomials and their squared gradient. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialOperator_eval_coordinates {N d : ℕ}
    (A : Module.End ℝ (MatrixPolynomial N)) (p : haarPolynomialSpace N d)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (A (p : MatrixPolynomial N)) =
      ∑ i, haarPolynomialCoordinates N d p i*
        matrixPolynomialEval M (A (haarPolynomialBasis N d i)) := by
  have hp : p = ∑ i, haarPolynomialCoordinates N d p i •
      (Module.finBasis ℝ (haarPolynomialSpace N d)) i := by
    simpa only [haarPolynomialCoordinates,LinearEquiv.symm_apply_apply] using
      (Module.finBasis ℝ (haarPolynomialSpace N d)).equivFun_symm_apply
        (haarPolynomialCoordinates N d p)
  conv_lhs => rw [hp]
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul,smul_eq_mul,
    haarPolynomialBasis]

lemma continuous_haarPolynomialHeat_operator_value {N d : ℕ}
    (A : Module.End ℝ (MatrixPolynomial N)) (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      (A ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2) := by
  have hc := continuous_haarPolynomialHeat_coordinates p
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i, haarPolynomialCoordinates N d (haarPolynomialHeat N d z.1 p) i*
        haarPolynomialValue (A (haarPolynomialBasis N d i)) z.2) := by
    apply continuous_finsetSum
    intro i _
    exact (((continuous_apply i).comp hc).comp continuous_fst).mul
      ((continuous_haarPolynomialValue _).comp continuous_snd)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact haarPolynomialOperator_eval_coordinates _ _ _

lemma continuous_haarPolynomialHeat_gamma {N d : ℕ} (p : haarPolynomialSpace N d) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue
      (haarPolynomialGamma
        ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2) := by
  have hs : Continuous (fun z : ℝ × SpecialOrthogonal N =>
      ∑ i : Fin N, ∑ j : Fin N,
        (haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j)
          ((haarPolynomialHeat N d z.1 p : haarPolynomialSpace N d) : MatrixPolynomial N)) z.2)^2) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (continuous_haarPolynomialHeat_operator_value
      (matrixPolynomialDerivation (planeGenerator i j)).toLinearMap p).pow 2
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [haarPolynomialValue,haarPolynomialGamma,map_sum,map_mul,pow_two]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarGammaCalculus
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-order product and square-gradient identities for the rotation carré du champ. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialGamma_mul {N : ℕ} (p q r : MatrixPolynomial N) :
    haarPolynomialGamma p (q*r) = q*haarPolynomialGamma p r+r*haarPolynomialGamma p q := by
  simp only [haarPolynomialGamma,Derivation.leibniz,smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma haarPolynomialGamma_sq {N : ℕ} (p q : MatrixPolynomial N) :
    haarPolynomialGamma p (q^2) = 2*q*haarPolynomialGamma p q := by
  rw [pow_two,haarPolynomialGamma_mul]
  ring

lemma haarPolynomialGamma_sub {N : ℕ} (p q r : MatrixPolynomial N) :
    haarPolynomialGamma p (q-r) = haarPolynomialGamma p q-haarPolynomialGamma p r := by
  simp only [haarPolynomialGamma,map_sub,mul_sub,Finset.sum_sub_distrib]

lemma haarPolynomialGamma_smul {N : ℕ} (p q : MatrixPolynomial N) (c : ℝ) :
    haarPolynomialGamma p (c • q) = c • haarPolynomialGamma p q := by
  simp only [haarPolynomialGamma,Derivation.map_smul_of_tower,mul_smul_comm,
    Finset.smul_sum]

lemma haarPolynomialDerivation_gamma_sq {N : ℕ} (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialDerivation A (haarPolynomialGamma p p) =
      ∑ i, ∑ j, 2*(matrixPolynomialDerivation (planeGenerator i j) p*
        matrixPolynomialDerivation A (matrixPolynomialDerivation (planeGenerator i j) p)) := by
  simp only [haarPolynomialGamma,map_sum,Derivation.leibniz,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHessianExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite square completion in the logarithmic Bochner calculation. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma sum_gradient_outer_sq {J : Type*} [Fintype J] (g : J → ℝ) :
    (∑ i, ∑ j, (g i*g j)^2) = (∑ i, (g i)^2)^2 := by
  simp only [mul_pow]
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma sum_corrected_hessian_sq {J : Type*} [Fintype J]
    (H : J → J → ℝ) (g : J → ℝ) (c : ℝ) :
    (∑ i, ∑ j, (H i j-c*g i*g j)^2) =
      (∑ i, ∑ j, (H i j)^2)-2*c*(∑ i, ∑ j, H i j*g i*g j)+
        c^2*(∑ i, (g i)^2)^2 := by
  have hs (i j : J) : (H i j-c*g i*g j)^2 =
      (H i j)^2-2*c*(H i j*g i*g j)+c^2*(g i*g j)^2 := by ring
  simp_rw [hs]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [sum_gradient_outer_sq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLogCurvature
attribute [-instance] _root_.OAI.InvariantIsing.haarPolynomialSpace_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise curvature inequality with a logarithmic gradient correction. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarGradientValue_sq_sum {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    (∑ a, (haarGradientValue p M a)^2) = matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [Fintype.sum_prod_type,haarGradientValue,haarPolynomialGamma,map_sum,map_mul,pow_two]

lemma haarGammaGammaValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) =
      2*(∑ a, ∑ b, haarHessianValue p M a b*haarGradientValue p M a*haarGradientValue p M b) := by
  have hd (a : Fin N × Fin N) : matrixPolynomialEval M
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) (haarPolynomialGamma p p)) =
      2*(∑ b, haarGradientValue p M b*haarHessianValue p M b a) := by
    rw [haarPolynomialDerivation_gamma_sq]
    simp only [map_sum,map_mul,map_ofNat,Fintype.sum_prod_type,Finset.mul_sum,
      haarGradientValue,haarHessianValue]
  have hex : matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) =
      ∑ a : Fin N × Fin N, haarGradientValue p M a*
        matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2)
          (haarPolynomialGamma p p)) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,Fintype.sum_prod_type,haarGradientValue]
  rw [hex]
  simp_rw [hd]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma haarLogCurvature {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
      matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))-
      c*matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p))+
      c^2*(matrixPolynomialEval M (haarPolynomialGamma p p))^2 := by
  have hc := matrixPolynomial_corrected_hessian_bound p M c
  have he := congrArg (matrixPolynomialEval M) (haarPolynomial_bochner_identity p)
  simp only [map_mul,map_ofNat,map_add,map_sum,map_pow] at he
  have hc' : ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
    ∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      (haarHessianValue p M a b-c*haarGradientValue p M a*haarGradientValue p M b)^2 := by
    simpa only [Fintype.sum_prod_type,haarHessianValue,haarGradientValue] using hc
  rw [sum_corrected_hessian_sq,haarGradientValue_sq_sum] at hc'
  rw [haarGammaGammaValue]
  have he' : matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p)) =
    2*(matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))+
      ∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N, (haarHessianValue p M a b)^2) := by
    simpa only [Fintype.sum_prod_type,haarHessianValue] using he
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMinimum
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Maximum-principle signs for the genuine rotation Laplacian. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

lemma haarPolynomialLaplacian_nonneg_at_min {N : ℕ}
    (p : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V) :
    0 ≤ haarPolynomialValue (haarPolynomialLaplacian N p) U := by
  unfold haarPolynomialValue
  rw [haarPolynomialLaplacian_apply,map_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [map_sum]
  apply Finset.sum_nonneg
  intro j _
  let q := matrixPolynomialDerivation (planeGenerator i j) p
  have hm : IsLocalMin (fun t => haarPolynomialValue p (specialPlaneRotation i j t*U)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [specialPlaneRotation_zero,one_mul] using hmin (specialPlaneRotation i j t*U)
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt
      (fun s => haarPolynomialValue p (specialPlaneRotation i j s*U))
      (haarPolynomialValue q (specialPlaneRotation i j t*U)) t :=
    Filter.Eventually.of_forall fun t => hasDerivAt_specialPlaneRotation_polynomial p i j U t
  have hdd := hasDerivAt_specialPlaneRotation_polynomial q i j U 0
  simp only [specialPlaneRotation_zero,one_mul] at hdd
  exact second_derivative_nonneg_at_local_min hm hd hdd

/-- Compact-space parabolic comparison, with the spatial sign proved above. -/
theorem haarPolynomial_parabolic_nonneg {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ → MatrixPolynomial N) (Wt : ℝ × SpecialOrthogonal N → ℝ)
    (hc : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (p z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p 0) U)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      HasDerivAt (fun s => haarPolynomialValue (p s) U) (Wt (t,U)) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialLaplacian N (p t)) U-
        haarPolynomialValue (p t) U ≤ Wt (t,U)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue (p t) U := by
  apply compact_parabolic_nonneg hT
    (fun t U => haarPolynomialValue (p t) U) Wt
    (fun t U => haarPolynomialValue (haarPolynomialLaplacian N (p t)) U)
    hc hi hd hpde
  intro t _ U hm
  exact haarPolynomialLaplacian_nonneg_at_min (p t) U hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarMinimumGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every coordinate-plane derivative vanishes at a global polynomial minimum. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology BigOperators
namespace InvariantIsing

lemma haarPolynomialDerivation_zero_at_min {N : ℕ}
    (p : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V)
    (i j : Fin N) :
    haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U = 0 := by
  have hm : IsLocalMin (fun t => haarPolynomialValue p (specialPlaneRotation i j t*U)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [specialPlaneRotation_zero,one_mul] using hmin (specialPlaneRotation i j t*U)
  have hd := hasDerivAt_specialPlaneRotation_polynomial p i j U 0
  simp only [specialPlaneRotation_zero,one_mul] at hd
  exact hm.hasDerivAt_eq_zero hd

lemma haarPolynomialGamma_zero_at_min {N : ℕ}
    (p q : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V) :
    haarPolynomialValue (haarPolynomialGamma q p) U = 0 := by
  change matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) _ = 0
  simp only [haarPolynomialGamma,map_sum,map_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  change _*haarPolynomialValue (matrixPolynomialDerivation (planeGenerator i j) p) U = 0
  rw [haarPolynomialDerivation_zero_at_min p U hmin i j,mul_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLogBarrier
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialCoordinateEval_apply _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.rotationMatrix_specialRotation _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise minimum inequality for a logarithmic heat-gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

lemma haarLogBarrier_eval {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarLogBarrier p a) =
      a*(matrixPolynomialEval M p)^2-matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [haarLogBarrier,map_sub,map_smul,map_pow,smul_eq_mul]

lemma haarLogBarrier_laplacian {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialLaplacian N (haarLogBarrier p a)) =
      2*a*(matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialLaplacian N p)+
        matrixPolynomialEval M (haarPolynomialGamma p p))-
        matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p)) := by
  simp only [haarLogBarrier,map_sub,map_smul,haarPolynomialLaplacian_sq,
    map_mul,map_ofNat,map_add,smul_eq_mul]
  ring

lemma haarLogBarrier_gamma {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma p (haarLogBarrier p a)) =
      2*a*matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialGamma p p)-
        matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) := by
  simp only [haarLogBarrier,haarPolynomialGamma_sub,haarPolynomialGamma_smul,
    haarPolynomialGamma_sq,map_sub,map_smul,map_mul,map_ofNat,smul_eq_mul]
  ring

lemma haarLogBarrier_min_derivative_lower {N : ℕ} (p : MatrixPolynomial N) (a : ℝ)
    (U : SpecialOrthogonal N) (hu : haarPolynomialValue p U ≠ 0)
    (hmin : ∀ V : SpecialOrthogonal N,
      haarPolynomialValue (haarLogBarrier p a) U ≤ haarPolynomialValue (haarLogBarrier p a) V) :
    -2*((N:ℝ)-2)*a*(haarPolynomialValue p U)^2+
        2*a*haarPolynomialValue p U*haarPolynomialValue (haarPolynomialLaplacian N p) U-
        2*haarPolynomialValue (haarPolynomialGamma p (haarPolynomialLaplacian N p)) U ≥
      (-2*((N:ℝ)-2)+2*haarPolynomialValue (haarPolynomialGamma p p) U/
        (haarPolynomialValue p U)^2)*haarPolynomialValue (haarLogBarrier p a) U := by
  let M : Matrix (Fin N) (Fin N) ℝ := U
  have hc := haarLogCurvature p M (1/matrixPolynomialEval M p)
  have hl := haarPolynomialLaplacian_nonneg_at_min (haarLogBarrier p a) U hmin
  have hg := haarPolynomialGamma_zero_at_min (haarLogBarrier p a) p U hmin
  change 0 ≤ matrixPolynomialEval M (haarPolynomialLaplacian N (haarLogBarrier p a)) at hl
  change matrixPolynomialEval M (haarPolynomialGamma p (haarLogBarrier p a)) = 0 at hg
  rw [haarLogBarrier_laplacian] at hl
  rw [haarLogBarrier_gamma] at hg
  change matrixPolynomialEval M p ≠ 0 at hu
  change -2*((N:ℝ)-2)*a*(matrixPolynomialEval M p)^2+
      2*a*matrixPolynomialEval M p*matrixPolynomialEval M (haarPolynomialLaplacian N p)-
      2*matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p)) ≥ _
  rw [show haarPolynomialValue (haarLogBarrier p a) U =
    matrixPolynomialEval M (haarLogBarrier p a) from rfl,haarLogBarrier_eval]
  have hq : matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) /
      matrixPolynomialEval M p = 2*a*matrixPolynomialEval M (haarPolynomialGamma p p) := by
    rw [div_eq_iff hu]
    linear_combination -hg
  rw [div_eq_mul_inv] at hq
  have hce : ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
      matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))-
      2*a*matrixPolynomialEval M (haarPolynomialGamma p p)+
      (matrixPolynomialEval M (haarPolynomialGamma p p))^2/(matrixPolynomialEval M p)^2 := by
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    simp only [one_div]
    rw [mul_comm ((matrixPolynomialEval M p)⁻¹),hq]
    ring
  have hid :
      (-2*((N:ℝ)-2)+2*matrixPolynomialEval M (haarPolynomialGamma p p)/(matrixPolynomialEval M p)^2)*
          (a*(matrixPolynomialEval M p)^2-matrixPolynomialEval M (haarPolynomialGamma p p)) =
      -2*((N:ℝ)-2)*a*(matrixPolynomialEval M p)^2+
        2*((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p)+
        2*a*matrixPolynomialEval M (haarPolynomialGamma p p)-
        2*(matrixPolynomialEval M (haarPolynomialGamma p p))^2/(matrixPolynomialEval M p)^2 := by
    field_simp
    ring
  change _ ≥ (-2*((N:ℝ)-2)+2*matrixPolynomialEval M (haarPolynomialGamma p p)/
    (matrixPolynomialEval M p)^2)*(a*(matrixPolynomialEval M p)^2-
      matrixPolynomialEval M (haarPolynomialGamma p p))
  rw [hid]
  linear_combination hl+2*hce

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatLogBarrier
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Time differentiation and continuity of the logarithmic gradient barrier. -/
noncomputable section
open Matrix MvPolynomial
namespace InvariantIsing

lemma continuous_haarHeatLogBarrier {N d : ℕ} (p : haarPolynomialSpace N d) (C : ℝ) :
    Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (haarHeatLogBarrier p C z.1) z.2) := by
  have he (t : ℝ) (U : SpecialOrthogonal N) : haarPolynomialValue (haarHeatLogBarrier p C t) U =
      C*Real.exp (-2*((N:ℝ)-2)*t)*
        (haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)^2-
      haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U :=
    haarLogBarrier_eval _ _ _
  simp_rw [he]
  exact ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
    ((continuous_haarPolynomialHeat_value p).pow 2)).sub (continuous_haarPolynomialHeat_gamma p)

lemma haarHeatLogBarrier_hasDerivAt {N d : ℕ} (p : haarPolynomialSpace N d)
    (C t : ℝ) (U : SpecialOrthogonal N) :
    HasDerivAt (fun s => haarPolynomialValue (haarHeatLogBarrier p C s) U)
      (let q : MatrixPolynomial N := (haarPolynomialHeat N d t p : haarPolynomialSpace N d);
       let a := C*Real.exp (-2*((N:ℝ)-2)*t);
       -2*((N:ℝ)-2)*a*(haarPolynomialValue q U)^2+
        2*a*haarPolynomialValue q U*haarPolynomialValue (haarPolynomialLaplacian N q) U-
        2*haarPolynomialValue (haarPolynomialGamma q (haarPolynomialLaplacian N q)) U) t := by
  have ha : HasDerivAt (fun s => C*Real.exp (-2*((N:ℝ)-2)*s))
      (-2*((N:ℝ)-2)*(C*Real.exp (-2*((N:ℝ)-2)*t))) t := by
    convert (((hasDerivAt_id t).const_mul (-2*((N:ℝ)-2))).exp).const_mul C using 1
    all_goals try with_reducible_and_instances rfl
    all_goals simp only [id_eq]
    all_goals ring
  have hu := haarPolynomialHeat_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) t
  have hg := haarPolynomialHeat_gamma_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) t
  refine (((ha.mul (hu.pow 2)).sub hg).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact haarLogBarrier_eval _ _ _
  · dsimp only [haarPolynomialValue]
    simp only [Nat.cast_ofNat,Pi.pow_apply]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatPositivity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the actual finite polynomial heat flow, by compact comparison. -/
noncomputable section
open Matrix MvPolynomial Set
open scoped BigOperators
namespace InvariantIsing

theorem haarPolynomialHeat_nonneg {N d : ℕ} (p : haarPolynomialSpace N d)
    (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    0 ≤ haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U := by
  let q (s : ℝ) : MatrixPolynomial N := Real.exp (-s) •
    ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
  let Wt (z : ℝ × SpecialOrthogonal N) :=
    haarPolynomialValue (haarPolynomialLaplacian N (q z.1)) z.2-
      haarPolynomialValue (q z.1) z.2
  have hq (s : ℝ) (V : SpecialOrthogonal N) : haarPolynomialValue (q s) V =
      Real.exp (-s)*haarPolynomialValue
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (Real.exp (-s) • _) = _
    rw [map_smul]
    rfl
  have hL (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V =
      Real.exp (-s)*haarPolynomialValue (haarPolynomialLaplacian N
        ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (haarPolynomialLaplacian N (Real.exp (-s) • _)) = _
    rw [map_smul,map_smul,smul_eq_mul]
    rfl
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (q z.1) z.2) := by
    simp_rw [hq]
    exact (Real.continuous_exp.comp continuous_fst.neg).mul (continuous_haarPolynomialHeat_value p)
  have hi : ∀ V : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (q 0) V := by
    intro V
    simpa only [hq,neg_zero,Real.exp_zero,one_mul,haarPolynomialHeat_zero] using hp V
  have hd (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => haarPolynomialValue (q r) V) (Wt (s,V)) s := by
    have he : HasDerivAt (fun r : ℝ => Real.exp (-r)) (-Real.exp (-s)) s := by
      convert ((hasDerivAt_id s).fun_neg).exp using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [id_eq,mul_neg,mul_one]
    have hv := haarPolynomialHeat_hasDerivAt p (V : Matrix (Fin N) (Fin N) ℝ) s
    refine ((he.mul hv).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      exact hq r V
    · change haarPolynomialValue (haarPolynomialLaplacian N (q s)) V-
        haarPolynomialValue (q s) V = _
      rw [hL,hq]
      simp only [haarPolynomialValue]
      ring
  have hz := haarPolynomial_parabolic_nonneg ht q Wt hc.continuousOn hi hd
    (fun _ _ _ => le_rfl) t ⟨ht,le_rfl⟩ U
  rw [hq] at hz
  exact nonneg_of_mul_nonneg_right hz (Real.exp_pos (-t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preservation of constants by the constructed polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma continuousLinearMap_exp_apply_of_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (v : E) (hv : A v=0) :
    NormedSpace.exp A v = v := by
  have hp (n : ℕ) : (A^(n+1)) v=0 := by
    induction n with
    | zero => simpa only [zero_add,pow_one] using hv
    | succ n ih =>
      rw [show n+1+1=(n+1)+1 by omega,pow_succ',mul_apply_eq_comp,ih,map_zero]
  have hn (n : ℕ) : ((n.factorial⁻¹ : ℝ) • A^n) v = if n=0 then v else 0 := by
    cases n with
    | zero => simp
    | succ n => simp only [_root_.smul_apply,hp,smul_zero,
        Nat.succ_ne_zero,ite_false, if_false]
  have hs := (ContinuousLinearMap.apply ℝ E v).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A)
  have ht : HasSum (fun n : ℕ => if n=0 then v else 0) (NormedSpace.exp A v) := by
    simpa only [ContinuousLinearMap.apply_apply,hn] using hs
  exact ht.unique (hasSum_ite_eq 0 v)

lemma haarPolynomialHeat_eq_of_laplacian_zero {N d : ℕ}
    (p : haarPolynomialSpace N d) (hp : haarPolynomialLaplacian N (p : MatrixPolynomial N)=0)
    (t : ℝ) : haarPolynomialHeat N d t p = p := by
  have hr : haarPolynomialRestrictedLaplacian N d p=0 := by
    apply Subtype.ext
    exact hp
  have hc : haarPolynomialCoordinateLaplacian N d (haarPolynomialCoordinates N d p)=0 := by
    rw [haarPolynomialCoordinateLaplacian_apply,hr,map_zero]
  apply (haarPolynomialCoordinates N d).injective
  rw [haarPolynomialCoordinates_heat]
  apply continuousLinearMap_exp_apply_of_zero
  simp only [_root_.smul_apply,hc,smul_zero]

lemma haarPolynomialLaplacian_one (N : ℕ) :
    haarPolynomialLaplacian N (1 : MatrixPolynomial N) = 0 := by
  simp only [haarPolynomialLaplacian_apply,Derivation.map_one_eq_zero,map_zero,
    Finset.sum_const_zero]

lemma haarPolynomialHeat_one (N d : ℕ) (t : ℝ) :
    haarPolynomialHeat N d t ⟨1,one_mem_haarPolynomialSpace N d⟩ =
      ⟨1,one_mem_haarPolynomialSpace N d⟩ :=
  haarPolynomialHeat_eq_of_laplacian_zero _ (haarPolynomialLaplacian_one N) t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatOrder
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform order bounds for the polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_bounds {N d : ℕ} (p : haarPolynomialSpace N d)
    (a b : ℝ)
    (ha : ∀ U : SpecialOrthogonal N, a ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hb : ∀ U : SpecialOrthogonal N, haarPolynomialValue (p : MatrixPolynomial N) U ≤ b)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∈ Icc a b := by
  let onep : haarPolynomialSpace N d := ⟨1,one_mem_haarPolynomialSpace N d⟩
  have h1 : haarPolynomialHeat N d t onep = onep := haarPolynomialHeat_one N d t
  have hscalar (c : ℝ) (V : SpecialOrthogonal N) :
      matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
        ((c • onep : haarPolynomialSpace N d) : MatrixPolynomial N) = c := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (c • (1 : MatrixPolynomial N)) = c
    rw [map_smul,map_one]
    exact mul_one c
  have hl : ∀ V : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue ((p-a • onep : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    intro V
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_)
    rw [map_sub,hscalar]
    exact sub_nonneg.mpr (ha V)
  have hu : ∀ V : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue ((b • onep-p : haarPolynomialSpace N d) : MatrixPolynomial N) V := by
    intro V
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_)
    rw [map_sub,hscalar]
    exact sub_nonneg.mpr (hb V)
  have hlow := haarPolynomialHeat_nonneg (p-a • onep) hl ht U
  have hupp := haarPolynomialHeat_nonneg (b • onep-p) hu ht U
  rw [map_sub,map_smul,h1] at hlow hupp
  change 0 ≤ matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (_-_) at hlow hupp
  rw [map_sub,hscalar] at hlow hupp
  exact ⟨sub_nonneg.mp hlow,sub_nonneg.mp hupp⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatLogGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential decay of the logarithmic gradient of a positive polynomial heat orbit. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_log_gradient_bound {N d : ℕ} (p : haarPolynomialSpace N d)
    (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2)
    {T : ℝ} (hT : 0 ≤ T) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤
      C*Real.exp (-2*((N:ℝ)-2)*T)*
        (haarPolynomialValue ((haarPolynomialHeat N d T p : haarPolynomialSpace N d) : MatrixPolynomial N) U)^2 := by
  let q (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let a (s : ℝ) := C*Real.exp (-2*((N:ℝ)-2)*s)
  let H (s : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue (haarHeatLogBarrier p C s) V
  let G (s : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue (haarPolynomialGamma (q s) (q s)) V
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hlow (s : ℝ) (hs : 0 ≤ s) (V : SpecialOrthogonal N) : ε ≤ haarPolynomialValue (q s) V :=
    (haarPolynomialHeat_bounds p ε P hp (fun W => (le_abs_self _).trans (hP W)) hs V).1
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn
    (continuous_haarPolynomialHeat_gamma p).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (0,1) ⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  have hGB (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) (V : SpecialOrthogonal N) : G s V ≤ B :=
    (le_abs_self _).trans (hB (s,V) ⟨hs,mem_univ _⟩)
  let A := 2*|((N:ℝ)-2)|+2*B/ε^2+1
  let W (s : ℝ) (V : SpecialOrthogonal N) := Real.exp (-A*s)*H s V
  let D (s : ℝ) (V : SpecialOrthogonal N) :=
    -2*((N:ℝ)-2)*a s*(haarPolynomialValue (q s) V)^2+
      2*a s*haarPolynomialValue (q s) V*haarPolynomialValue (haarPolynomialLaplacian N (q s)) V-
      2*haarPolynomialValue (haarPolynomialGamma (q s) (haarPolynomialLaplacian N (q s))) V
  let Wt (z : ℝ × SpecialOrthogonal N) := Real.exp (-A*z.1)*(D z.1 z.2-A*H z.1 z.2)
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => W z.1 z.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (continuous_haarHeatLogBarrier p C)
  have hi (V : SpecialOrthogonal N) : 0 ≤ W 0 V := by
    simp only [W,H,haarHeatLogBarrier,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,mul_one,one_mul]
    change 0 ≤ matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (haarLogBarrier p C)
    rw [haarLogBarrier_eval]
    exact sub_nonneg.mpr (hC V)
  have hd (s : ℝ) (_ : s ∈ Ioc (0:ℝ) T) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => W r V) (Wt (s,V)) s := by
    have he : HasDerivAt (fun r => Real.exp (-A*r)) (-A*Real.exp (-A*s)) s := by
      convert ((hasDerivAt_id s).const_mul (-A)).exp using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [id_eq,mul_one]
      all_goals ring
    have hh := haarHeatLogBarrier_hasDerivAt p C s V
    convert he.mul hh using 1
    all_goals try with_reducible_and_instances rfl
    all_goals dsimp only [Wt,D,H,q,a]
    all_goals ring
  have hmin (s : ℝ) (hs : s ∈ Ioc (0:ℝ) T) (V : SpecialOrthogonal N)
      (hneg : W s V < 0) (hm : ∀ Z, W s V ≤ W s Z) : 0 < Wt (s,V) := by
    have hHneg : H s V < 0 := by
      have he := Real.exp_pos (-A*s)
      dsimp only [W] at hneg
      nlinarith
    have hHmin (Z : SpecialOrthogonal N) : H s V ≤ H s Z :=
      (mul_le_mul_iff_right₀ (Real.exp_pos (-A*s))).mp (hm Z)
    have hu : 0 < haarPolynomialValue (q s) V := hε.trans_le (hlow s hs.1.le V)
    have hD : (-2*((N:ℝ)-2)+2*G s V/(haarPolynomialValue (q s) V)^2)*H s V ≤ D s V :=
      haarLogBarrier_min_derivative_lower (q s) (a s) V hu.ne' hHmin
    have hw : G s V/(haarPolynomialValue (q s) V)^2 ≤ B/ε^2 := by
      calc
        _ ≤ B/(haarPolynomialValue (q s) V)^2 :=
          div_le_div_of_nonneg_right (hGB s ⟨hs.1.le,hs.2⟩ V) (sq_nonneg _)
        _ ≤ B/ε^2 := div_le_div_of_nonneg_left hB0 (sq_pos_of_pos hε)
          ((sq_le_sq₀ hε.le hu.le).mpr (hlow s hs.1.le V))
    have hcoef : -2*((N:ℝ)-2)+2*G s V/(haarPolynomialValue (q s) V)^2 ≤ A-1 := by
      dsimp only [A]
      linear_combination 2*hw+2*(neg_le_abs ((N:ℝ)-2))
    have hmulf := mul_le_mul_of_nonpos_right hcoef hHneg.le
    have hstrict : 0 < D s V-A*H s V := by nlinarith
    exact mul_pos (Real.exp_pos (-A*s)) hstrict
  have hz := compact_nonneg_of_negative_min_derivative hT W Wt hc.continuousOn hi hd hmin
    T ⟨hT,le_rfl⟩ U
  have hH : 0 ≤ H T U := (mul_nonneg_iff_of_pos_left (Real.exp_pos (-A*T))).mp hz
  change 0 ≤ matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ)
    (haarLogBarrier (q T) (a T)) at hH
  rw [haarLogBarrier_eval] at hH
  exact sub_nonneg.mp hH

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatMean
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact preservation of Haar means by the polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialMean_laplacian {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : MatrixPolynomial N) :
    haarPolynomialMean μ (haarPolynomialLaplacian N p) = 0 := by
  rw [haarPolynomialLaplacian_apply,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact integral_haarPolynomialDerivation μ (matrixPolynomialDerivation (planeGenerator i j) p) i j

theorem haarPolynomialHeat_mean {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d) (t : ℝ) :
    (∫ U, haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ) =
      ∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ := by
  let f (s : ℝ) := haarPolynomialMean μ
    ((haarPolynomialHeat N d s p : haarPolynomialSpace N d) : MatrixPolynomial N)
  have hd (s : ℝ) : HasDerivAt f 0 s := by
    have h := haarPolynomialHeat_linear_hasDerivAt (haarPolynomialMean μ) p s
    rw [haarPolynomialMean_laplacian] at h
    exact h
  have he : f t=f 0 := is_const_of_deriv_eq_zero
    (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  change haarPolynomialMean μ _ = haarPolynomialMean μ _
  simpa only [f,haarPolynomialHeat_zero] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialEvolution
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity comparison for polynomial supersolutions of the rotation heat equation. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomial_evolution_nonneg {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ → MatrixPolynomial N) (dp : ℝ → SpecialOrthogonal N → ℝ)
    (hc : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (p z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p 0) U)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      HasDerivAt (fun s => haarPolynomialValue (p s) U) (dp t U) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialLaplacian N (p t)) U ≤ dp t U) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue (p t) U := by
  let W (t : ℝ) (U : SpecialOrthogonal N) := Real.exp (-t)*haarPolynomialValue (p t) U
  let D (z : ℝ × SpecialOrthogonal N) :=
    Real.exp (-z.1)*(dp z.1 z.2-haarPolynomialValue (p z.1) z.2)
  let B (t : ℝ) (U : SpecialOrthogonal N) :=
    Real.exp (-t)*haarPolynomialValue (haarPolynomialLaplacian N (p t)) U
  have hcW : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => W z.1 z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ) :=
    (Real.continuous_exp.comp continuous_fst.neg).continuousOn.mul hc
  have hiW : ∀ U, 0 ≤ W 0 U := by simpa only [W,neg_zero,Real.exp_zero,one_mul] using hi
  have hdW (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (U : SpecialOrthogonal N) :
      HasDerivAt (fun s => W s U) (D (t,U)) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      convert ((hasDerivAt_id t).fun_neg).exp using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [id_eq,mul_neg,mul_one]
    convert he.mul (hd t ht U) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [D]
    ring
  have hP (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (U : SpecialOrthogonal N) :
      B t U-W t U ≤ D (t,U) := by
    dsimp only [B,W,D]
    nlinarith [mul_le_mul_of_nonneg_left (hpde t ht U) (Real.exp_pos (-t)).le]
  have hS (t : ℝ) (_ : t ∈ Icc (0 : ℝ) T) (U : SpecialOrthogonal N)
      (hm : ∀ V, W t U ≤ W t V) : 0 ≤ B t U := by
    apply mul_nonneg (Real.exp_pos (-t)).le
    apply haarPolynomialLaplacian_nonneg_at_min
    intro V
    exact (mul_le_mul_iff_right₀ (Real.exp_pos (-t))).mp (hm V)
  have hz := compact_parabolic_nonneg hT W D B hcW hiW hdW hP hS
  intro t ht U
  exact nonneg_of_mul_nonneg_right (hz t ht U) (Real.exp_pos (-t))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential squared-gradient decay for the actual orthogonal polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomialHeat_gradient_bound {N d : ℕ}
    (p : haarPolynomialSpace N d) (C : ℝ)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (U : SpecialOrthogonal N) :
    Real.exp (2*((N : ℝ)-2)*t)*haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤ C := by
  let u (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let g (s : ℝ) := haarPolynomialGamma (u s) (u s)
  let k : ℝ := 2*((N : ℝ)-2)
  let q (s : ℝ) : MatrixPolynomial N := C • 1-Real.exp (k*s) • g s
  let dq (s : ℝ) (V : SpecialOrthogonal N) :=
    -Real.exp (k*s)*(k*haarPolynomialValue (g s) V+
      2*haarPolynomialValue (haarPolynomialGamma (u s) (haarPolynomialLaplacian N (u s))) V)
  have heval (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (q s) V = C-Real.exp (k*s)*haarPolynomialValue (g s) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ) (_-_) = _
    simp only [map_sub,map_smul,map_one,smul_eq_mul,mul_one,haarPolynomialValue]
  have hL (s : ℝ) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V =
        -Real.exp (k*s)*haarPolynomialValue (haarPolynomialLaplacian N (g s)) V := by
    change matrixPolynomialEval (V : Matrix (Fin N) (Fin N) ℝ)
      (haarPolynomialLaplacian N (C • 1-Real.exp (k*s) • g s)) = _
    rw [map_sub,map_smul,map_smul,haarPolynomialLaplacian_one,smul_zero,zero_sub,
      map_neg,map_smul,smul_eq_mul]
    simp only [haarPolynomialValue,neg_mul]
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (q z.1) z.2) := by
    simp_rw [heval]
    exact continuous_const.sub
      ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (continuous_haarPolynomialHeat_gamma p))
  have hi : ∀ V : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (q 0) V := by
    intro V
    rw [heval]
    simpa only [g,u,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,one_mul] using
      sub_nonneg.mpr (hC V)
  have hd (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      HasDerivAt (fun r => haarPolynomialValue (q r) V) (dq s V) s := by
    have he : HasDerivAt (fun r => Real.exp (k*r)) (k*Real.exp (k*s)) s := by
      convert ((hasDerivAt_id s).const_mul k).exp using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [id_eq]
      all_goals ring
    have hg := haarPolynomialHeat_gamma_hasDerivAt p (V : Matrix (Fin N) (Fin N) ℝ) s
    refine (((hasDerivAt_const s C).sub (he.mul hg)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      exact heval r V
    · dsimp only [dq,haarPolynomialValue,g,u]
      ring
  have hpde (s : ℝ) (_ : s ∈ Ioc (0 : ℝ) t) (V : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialLaplacian N (q s)) V ≤ dq s V := by
    have hb := matrixPolynomial_curvature (u s) (V : Matrix (Fin N) (Fin N) ℝ)
    have hh : k*haarPolynomialValue (g s) V+
        2*haarPolynomialValue (haarPolynomialGamma (u s) (haarPolynomialLaplacian N (u s))) V ≤
        haarPolynomialValue (haarPolynomialLaplacian N (g s)) V := by
      dsimp only [k,g,haarPolynomialValue]
      linarith
    rw [hL]
    dsimp only [dq]
    nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_pos (k*s)).le]
  have hz := haarPolynomial_evolution_nonneg ht q dq hc.continuousOn hi hd hpde t ⟨ht,le_rfl⟩ U
  rw [heval] at hz
  exact sub_nonneg.mp hz

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatVanishingGradient
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single decaying gradient envelope for each polynomial heat orbit. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialHeat_gradient_envelope {N d : ℕ} (p : haarPolynomialSpace N d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤
      (M*Real.exp (-((N:ℝ)-2)*t))^2 := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound (haarPolynomialGamma (p : MatrixPolynomial N) p)
  let M := max B 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  have hC (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤ M^2 := by
    have hb := (le_abs_self _).trans (hB U)
    have hm : B ≤ M := le_max_left _ _
    nlinarith
  refine ⟨M,hM,?_⟩
  intro t ht U
  have hg := haarPolynomialHeat_gradient_bound p (M^2) hC ht U
  have he : Real.exp (2*((N:ℝ)-2)*t)*(M*Real.exp (-((N:ℝ)-2)*t))^2 = M^2 := by
    calc
      _ = M^2*Real.exp (2*((N:ℝ)-2)*t+
          (-((N:ℝ)-2)*t+-((N:ℝ)-2)*t)) := by
        rw [Real.exp_add,Real.exp_add]
        ring
      _ = M^2 := by
        rw [show 2*((N:ℝ)-2)*t+(-((N:ℝ)-2)*t+-((N:ℝ)-2)*t)=0 by ring,
          Real.exp_zero,mul_one]
  have hpos := Real.exp_pos (2*((N:ℝ)-2)*t)
  nlinarith

lemma tendsto_haar_gradient_envelope {N : ℕ} (hN : 3 ≤ N) (M : ℝ) :
    Tendsto (fun t : ℝ => M*Real.exp (-((N:ℝ)-2)*t)) atTop (𝓝 0) := by
  have hρ : 0 < (N:ℝ)-2 := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have ht : Tendsto (fun t : ℝ => -((N:ℝ)-2)*t) atTop atBot := by
    simpa only [Function.comp_def,neg_mul,id_eq] using
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hρ)
  simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_atBot.comp ht).const_mul M

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_RotationMatrix
attribute [-instance] _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix coordinates for Euclidean isometries and hyperplane reflections. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma rotationMatrix_mul {N : ℕ} (R S : Rotation N) :
    rotationMatrix (R*S) = rotationMatrix R*rotationMatrix S := by
  exact LinearMap.toMatrix_mul _ _ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionPairCurve
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine special-orthogonal curve for a pair of hyperplane reflections. -/
noncomputable section
open Matrix Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma reflectionPairCurve_zero {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) : reflectionPairCurve v w hw 0 = reflectionPair v w hv hw := by
  simp only [reflectionPairCurve,reflectionNormalSegment,sub_zero,one_smul,zero_smul,add_zero,
    dite_eq_left hv]

lemma reflectionPairCurve_one {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hw : w ≠ 0) : reflectionPairCurve v w hw 1 = 1 := by
  apply Subtype.ext
  simp only [reflectionPairCurve,reflectionNormalSegment,sub_self,zero_smul,one_smul,zero_add,
    dite_eq_left hw,reflectionPair]
  rw [← rotationMatrix_mul,show hyperplaneReflection w*hyperplaneReflection w = 1 from
    Submodule.reflection_mul_reflection _,rotationMatrix_one]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionPairPath
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nonzero reflection pair admits a differentiable curve to the identity. -/
noncomputable section
open Matrix Set
open scoped BigOperators
namespace InvariantIsing

lemma hyperplaneReflection_neg {N : ℕ} (v : EuclideanSpace ℝ (Fin N)) :
    hyperplaneReflection (-v) = hyperplaneReflection v := by
  have hs : (ℝ ∙ (-v)) = (ℝ ∙ v) := by
    simpa only [Set.neg_singleton] using (Submodule.span_neg (R := ℝ) ({v} : Set _))
  unfold hyperplaneReflection
  simp only [hs]

lemma reflectionPair_exists_path {N : ℕ} (v w : EuclideanSpace ℝ (Fin N))
    (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ γ : HaarDifferentiableCurve N,
      γ.value 0 = reflectionPair v w hv hw ∧ γ.value 1 = 1 := by
  by_cases h : 0 ≤ inner ℝ v w
  · exact ⟨reflectionPairPath v w hv hw h,reflectionPairCurve_zero v w hv hw,
      reflectionPairCurve_one v w hw⟩
  · have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
    have h' : 0 ≤ inner ℝ v (-w) := by rw [inner_neg_right]; linarith
    refine ⟨reflectionPairPath v (-w) hv hw' h',?_,reflectionPairCurve_one v (-w) hw'⟩
    change reflectionPairCurve v (-w) hw' 0 = _
    rw [reflectionPairCurve_zero v (-w) hv hw']
    apply Subtype.ext
    change rotationMatrix (hyperplaneReflection v)*rotationMatrix (hyperplaneReflection (-w)) = _
    rw [hyperplaneReflection_neg]
    rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_ReflectionParity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_compactSpace _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.matrixRotation_specialToOrthogonal _root_.OAI.InvariantIsing.specialPlaneRotation_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero _root_.OAI.InvariantIsing.specialToOrthogonal_planeRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even nonzero reflection factorizations of special orthogonal matrices. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma reflectionList_remove_zero {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N))) :
    ((l.filter (fun v => v ≠ 0)).map hyperplaneReflection).prod =
      (l.map hyperplaneReflection).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [ne_eq,decide_not] at ih
    by_cases ha : a = 0
    · simp [ha,ih]
    · simp [ha,ih]

lemma reflectionList_det {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N)))
    (hl : ∀ v ∈ l, v ≠ 0) :
    (rotationMatrix ((l.map hyperplaneReflection).prod)).det = (-1 : ℝ)^l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have htail : ∀ v ∈ l, v ≠ 0 := fun v hv => hl v (by simp [hv])
    simp only [List.map_cons,List.prod_cons,rotationMatrix_mul,Matrix.det_mul,
      rotationMatrix_reflection_det a ha,ih htail,List.length_cons,pow_succ]
    ring

lemma specialRotation_even_reflections {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ l : List (EuclideanSpace ℝ (Fin N)),
      (∀ v ∈ l, v ≠ 0) ∧ Even l.length ∧
      specialRotation U = (l.map hyperplaneReflection).prod := by
  obtain ⟨l,_,hl⟩ := (specialRotation U).reflections_generate_dim
  let l' := l.filter (fun v => v ≠ 0)
  have hnonzero : ∀ v ∈ l', v ≠ 0 := by
    intro v hv
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  have heq : specialRotation U = (l'.map hyperplaneReflection).prod := by
    rw [reflectionList_remove_zero]
    exact hl
  have hdet : (-1 : ℝ)^l'.length = 1 := by
    rw [← reflectionList_det l' hnonzero,← heq,rotationMatrix_specialRotation]
    exact (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).2
  exact ⟨l',hnonzero,(neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hdet,heq⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarReflectionConnectivity
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.InvariantIsing.tensorLabeledLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiable connection of every special orthogonal matrix to the identity. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma evenReflectionList_exists_curve {N : ℕ} (l : List (EuclideanSpace ℝ (Fin N)))
    (hl : ∀ v ∈ l, v ≠ 0) (heven : Even l.length) :
    ∃ γ : HaarDifferentiableCurve N,
      (γ.value 0 : Matrix (Fin N) (Fin N) ℝ) =
        rotationMatrix ((l.map hyperplaneReflection).prod) ∧ γ.value 1 = 1 := by
  induction l using List.twoStepInduction with
  | nil =>
    refine ⟨HaarDifferentiableCurve.constant 1,?_,rfl⟩
    simp [HaarDifferentiableCurve.constant]
  | singleton v => simp at heven
  | cons_cons v w l ih _ =>
    have hv := hl v (by simp)
    have hw := hl w (by simp)
    have hl' : ∀ x ∈ l, x ≠ 0 := fun x hx => hl x (by simp [hx])
    have heven' : Even l.length := by
      simpa only [List.length_cons,Nat.even_add_one,Nat.odd_add_one,not_not] using heven
    obtain ⟨γ,hγ0,hγ1⟩ := ih hl' heven'
    obtain ⟨η,hη0,hη1⟩ := reflectionPair_exists_path v w hv hw
    refine ⟨η.mul γ,?_,?_⟩
    · change (η.value 0 : Matrix (Fin N) (Fin N) ℝ)*
        (γ.value 0 : Matrix (Fin N) (Fin N) ℝ) = _
      rw [hη0,hγ0]
      simp only [List.map_cons,List.prod_cons,rotationMatrix_mul,reflectionPair]
      exact mul_assoc _ _ _
    · change η.value 1*γ.value 1 = 1
      rw [hη1,hγ1,mul_one]

theorem specialOrthogonal_exists_differentiableCurve {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ γ : HaarDifferentiableCurve N, γ.value 0 = U ∧ γ.value 1 = 1 := by
  obtain ⟨l,hl,heven,heq⟩ := specialRotation_even_reflections U
  obtain ⟨γ,hγ0,hγ1⟩ := evenReflectionList_exists_curve l hl heven
  refine ⟨γ,?_,hγ1⟩
  apply Subtype.ext
  rw [hγ0,← heq,rotationMatrix_specialRotation]

theorem haarPolynomial_global_oscillation_bound {N : ℕ} (U : SpecialOrthogonal N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : MatrixPolynomial N) (δ : ℝ), 0 ≤ δ →
      (∀ V : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) V ≤ δ^2) →
      |haarPolynomialValue p U-haarPolynomialValue p 1| ≤ K*δ := by
  obtain ⟨γ,hγ0,hγ1⟩ := specialOrthogonal_exists_differentiableCurve U
  obtain ⟨K,hK,hbound⟩ := γ.polynomial_bound
  refine ⟨K,hK,?_⟩
  intro p δ hδ hp
  simpa only [hγ0,hγ1,abs_sub_comm] using hbound p δ hδ hp

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatOscillation
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise decay of spatial oscillations under the actual polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology
namespace InvariantIsing

theorem haarPolynomialHeat_difference_tendsto {N d : ℕ} (hN : 3 ≤ N)
    (p : haarPolynomialSpace N d) (U V : SpecialOrthogonal N) :
    Tendsto (fun t : ℝ =>
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U-
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) V)
      atTop (𝓝 0) := by
  obtain ⟨M,hM,hgrad⟩ := haarPolynomialHeat_gradient_envelope p
  have hpoint (W : SpecialOrthogonal N) : Tendsto (fun t : ℝ =>
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) W-
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) 1)
      atTop (𝓝 0) := by
    obtain ⟨K,_,hK⟩ := haarPolynomial_global_oscillation_bound W
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using
      (tendsto_haar_gradient_envelope hN M).const_mul K)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [Real.norm_eq_abs]
    exact hK _ _ (mul_nonneg hM (Real.exp_pos _).le) (hgrad t ht)
  have hh := (hpoint U).sub (hpoint V)
  convert (config := {transparency := .instances, preTransparency := .instances}) hh using 1
  · funext t
    ring
  · norm_num

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatMixing
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convergence of the actual orthogonal polynomial heat flow to its Haar mean. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter
open scoped Topology
namespace InvariantIsing

theorem haarPolynomialHeat_tendsto_mean {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (U : SpecialOrthogonal N) :
    Tendsto (fun t : ℝ => haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)
      atTop (𝓝 (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)) := by
  let u (t : ℝ) (V : SpecialOrthogonal N) := haarPolynomialValue
    ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) V
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hub (t : ℝ) (ht : 0 ≤ t) (V : SpecialOrthogonal N) : |u t V| ≤ B := by
    apply abs_le.mpr
    apply haarPolynomialHeat_bounds p (-B) B
    · intro W
      exact (abs_le.mp (hB W)).1
    · intro W
      exact (abs_le.mp (hB W)).2
    · exact ht
  have hlim : Tendsto (fun t : ℝ => ∫ V, u t V-u t U ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := fun t V => u t V-u t U) (f := fun _ => (0:ℝ)) (fun _ => 2*B)
    simp only [integral_zero] at h
    apply h
    · exact Eventually.of_forall fun t =>
        ((continuous_haarPolynomialValue _).sub continuous_const).measurable.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      exact ae_of_all μ fun V => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hub t ht V,hub t ht U])
    · exact integrable_const _
    · exact ae_of_all μ fun V => haarPolynomialHeat_difference_tendsto hN p V U
  have he (t : ℝ) : (∫ V, u t V-u t U ∂μ) =
      (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-u t U := by
    rw [integral_sub (haarPolynomialValue_integrable _ μ) (integrable_const _),
      integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [haarPolynomialHeat_mean]
  simp_rw [he] at hlim
  have hh : Tendsto (fun t : ℝ => (∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-
      ((∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-u t U)) atTop
      (𝓝 ((∫ V, haarPolynomialValue (p : MatrixPolynomial N) V ∂μ)-0)) :=
    tendsto_const_nhds.sub hlim
  simpa only [sub_sub_cancel,sub_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatTestLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous tests of the polynomial heat flow and their Haar limits. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialHeat_test_bound {N d : ℕ} (p : haarPolynomialSpace N d)
    (F : ℝ → ℝ) (hF : Continuous F) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ U : SpecialOrthogonal N,
      ‖F (haarPolynomialValue
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U)‖ ≤ B := by
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨B,?_⟩
  intro t ht U
  apply hB
  exact haarPolynomialHeat_bounds p (-P) P
    (fun V => (abs_le.mp (hP V)).1) (fun V => (abs_le.mp (hP V)).2) ht U

theorem haarPolynomialHeat_test_tendsto_mean {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (F : ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun t : ℝ => ∫ U, F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ)
      atTop (𝓝 (F (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ))) := by
  obtain ⟨B,hB⟩ := haarPolynomialHeat_test_bound p F hF
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun t U => F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U))
    (f := fun _ => F (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)) (fun _ => B)
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  apply h
  · exact Eventually.of_forall fun t =>
      (hF.comp (continuous_haarPolynomialValue _)).measurable.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact ae_of_all μ (hB t ht)
  · exact integrable_const _
  · exact ae_of_all μ fun U => hF.continuousAt.tendsto.comp (haarPolynomialHeat_tendsto_mean hN μ p U)

theorem continuousOn_haarPolynomialHeat_test_integral {N d : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsFiniteMeasure μ]
    (p : haarPolynomialSpace N d) (F : ℝ → ℝ) (hF : Continuous F) :
    ContinuousOn (fun t : ℝ => ∫ U, F (haarPolynomialValue
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U) ∂μ) (Ici 0) := by
  obtain ⟨B,hB⟩ := haarPolynomialHeat_test_bound p F hF
  intro t _
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun s =>
      (hF.comp (continuous_haarPolynomialValue _)).measurable.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ae_of_all μ (hB s hs)
  · exact integrable_const _
  · exact ae_of_all μ fun U => ((hF.comp
      ((continuous_haarPolynomialHeat_value p).comp (continuous_id.prodMk continuous_const))).continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarLogIntegration
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.haarPolynomialSpace_finite _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integration by parts for the logarithm of a positive polynomial on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

theorem integral_haar_laplacian_log {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : MatrixPolynomial N)
    (hp : ∀ U : SpecialOrthogonal N, 0 < haarPolynomialValue p U) :
    (∫ U, haarPolynomialValue (haarPolynomialLaplacian N p) U*Real.log (haarPolynomialValue p U) ∂μ) =
      -(∫ U, haarPolynomialValue (haarPolynomialGamma p p) U/haarPolynomialValue p U ∂μ) := by
  let D (i j : Fin N) := matrixPolynomialDerivation (planeGenerator i j)
  let R (i j : Fin N) (U : SpecialOrthogonal N) :=
    haarPolynomialValue (D i j (D i j p)) U*Real.log (haarPolynomialValue p U)+
      (haarPolynomialValue (D i j p) U)^2/haarPolynomialValue p U
  have hlog : Continuous (fun U : SpecialOrthogonal N => Real.log (haarPolynomialValue p U)) :=
    (continuous_haarPolynomialValue p).log (fun U => (hp U).ne')
  have hR (i j : Fin N) : Continuous (R i j) :=
    ((continuous_haarPolynomialValue _).mul hlog).add
      (((continuous_haarPolynomialValue _).pow 2).div (continuous_haarPolynomialValue p)
        (fun U => (hp U).ne'))
  have hz (i j : Fin N) : (∫ U, R i j U ∂μ) = 0 := by
    apply integral_haar_continuous_derivative μ i j
      (fun U => haarPolynomialValue (D i j p) U*Real.log (haarPolynomialValue p U))
      (R i j) ((continuous_haarPolynomialValue _).mul hlog) (hR i j)
    intro U t
    have hq := hasDerivAt_specialPlaneRotation_polynomial (D i j p) i j U t
    have hpp := hasDerivAt_specialPlaneRotation_polynomial p i j U t
    convert (config := {transparency := .instances, preTransparency := .instances}) hq.mul (hpp.log (hp (specialPlaneRotation i j t*U)).ne') using 1
    · rfl
    · dsimp only [R,D,haarPolynomialValue]
      ring
  have hs : (∫ U, ∑ i, ∑ j, R i j U ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => continuous_haar_integrable μ _ (hR i j)))]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_finsetSum _ (fun j _ => continuous_haar_integrable μ _ (hR i j))]
    simp only [hz,Finset.sum_const_zero]
  have he (U : SpecialOrthogonal N) : (∑ i, ∑ j, R i j U) =
      haarPolynomialValue (haarPolynomialLaplacian N p) U*Real.log (haarPolynomialValue p U)+
        haarPolynomialValue (haarPolynomialGamma p p) U/haarPolynomialValue p U := by
    simp only [R,D,haarPolynomialValue,haarPolynomialLaplacian_apply,haarPolynomialGamma,
      map_sum,map_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_div,pow_two]
  simp_rw [he] at hs
  have hi1 : Integrable (fun U => haarPolynomialValue (haarPolynomialLaplacian N p) U*
      Real.log (haarPolynomialValue p U)) μ :=
    continuous_haar_integrable μ _ ((continuous_haarPolynomialValue _).mul hlog)
  have hi2 : Integrable (fun U => haarPolynomialValue (haarPolynomialGamma p p) U/
      haarPolynomialValue p U) μ := continuous_haar_integrable μ _
    ((continuous_haarPolynomialValue _).div (continuous_haarPolynomialValue _) (fun U => (hp U).ne'))
  rw [integral_add hi1 hi2] at hs
  exact eq_neg_of_add_eq_zero_left hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatEntropy
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entropy dissipation along the actual positive polynomial heat flow. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haarHeatEntropy_hasDerivAt {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d)
    (ε : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (haarHeatEntropy μ p)
      (-(∫ U, haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
        haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ)) t := by
  let q (s : ℝ) : MatrixPolynomial N := (haarPolynomialHeat N d s p : haarPolynomialSpace N d)
  let u (s : ℝ) (U : SpecialOrthogonal N) := haarPolynomialValue (q s) U
  let L (s : ℝ) (U : SpecialOrthogonal N) := haarPolynomialValue (haarPolynomialLaplacian N (q s)) U
  let F' (s : ℝ) (U : SpecialOrthogonal N) := L s U*(Real.log (u s U)+1)
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hpos (s : ℝ) (hs : 0 ≤ s) (U : SpecialOrthogonal N) : 0 < u s U :=
    hε.trans_le ((haarPolynomialHeat_bounds p ε P hp (fun V => (le_abs_self _).trans (hP V)) hs U).1)
  have hcont : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => F' z.1 z.2)
      (Icc (t/2) (t+1) ×ˢ (Set.univ : Set (SpecialOrthogonal N))) := by
    apply ((continuous_haarPolynomialHeat_operator_value (haarPolynomialLaplacian N) p).continuousOn).mul
    apply ContinuousOn.add _ continuousOn_const
    apply (continuous_haarPolynomialHeat_value p).continuousOn.log
    intro z hz
    exact (hpos z.1 (by linarith [hz.1.1]) z.2).ne'
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn hcont
  have hnb : Ioo (t/2) (t+1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hlog : Continuous (fun U : SpecialOrthogonal N => Real.log (u t U)) :=
    (continuous_haarPolynomialValue _).log (fun U => (hpos t ht.le U).ne')
  have hdi : HasDerivAt (haarHeatEntropy μ p) (∫ U, F' t U ∂μ) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (s := Ioo (t/2) (t+1)) (F' := F') (bound := fun _ => B) hnb
      (Eventually.of_forall fun s => (Real.continuous_mul_log.comp (continuous_haarPolynomialValue (q s))).measurable.aestronglyMeasurable)
      (continuous_haar_integrable μ _ (Real.continuous_mul_log.comp (continuous_haarPolynomialValue (q t))))
      (((continuous_haarPolynomialValue _).mul (hlog.add continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all μ fun U s hs => hB (s,U) ⟨⟨hs.1.le,hs.2.le⟩,mem_univ U⟩)
      (integrable_const B) ?_).2
    apply ae_of_all
    intro U s hs
    have hu := haarPolynomialHeat_hasDerivAt p (U : Matrix (Fin N) (Fin N) ℝ) s
    have hh := (Real.hasDerivAt_mul_log (hpos s (by linarith [hs.1]) U).ne').comp s hu
    refine hh.congr_deriv (Eq.symm ?_)
    · dsimp only [F',L,u,haarPolynomialValue,q]
      ring
  apply hdi.congr_deriv
  have hmul (U : SpecialOrthogonal N) : F' t U = L t U*Real.log (u t U)+L t U := by
    dsimp only [F']
    ring
  simp_rw [hmul]
  have hi1 : Integrable (fun U => L t U*Real.log (u t U)) μ :=
    continuous_haar_integrable μ _ ((continuous_haarPolynomialValue _).mul hlog)
  have hi2 : Integrable (L t) μ := haarPolynomialValue_integrable _ μ
  rw [integral_add hi1 hi2]
  rw [integral_haar_laplacian_log μ (q t) (hpos t ht.le)]
  change _+haarPolynomialMean μ (haarPolynomialLaplacian N (q t)) = _
  rw [haarPolynomialMean_laplacian,add_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarHeatFisherBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated logarithmic-gradient control for a positive heat orbit. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
namespace InvariantIsing

theorem haarHeat_fisher_bound {N d : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (p : haarPolynomialSpace N d)
    (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ U, haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
      haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ) ≤
      C*Real.exp (-2*((N:ℝ)-2)*t)*(∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ) := by
  let q : MatrixPolynomial N := (haarPolynomialHeat N d t p : haarPolynomialSpace N d)
  let a := C*Real.exp (-2*((N:ℝ)-2)*t)
  obtain ⟨P,hP⟩ := haarPolynomialValue_bound (p : MatrixPolynomial N)
  have hpos (U : SpecialOrthogonal N) : 0 < haarPolynomialValue q U :=
    hε.trans_le ((haarPolynomialHeat_bounds p ε P hp (fun V => (le_abs_self _).trans (hP V)) ht U).1)
  have hiG : Integrable (fun U => haarPolynomialValue (haarPolynomialGamma q q) U/
      haarPolynomialValue q U) μ := continuous_haar_integrable μ _
    ((continuous_haarPolynomialValue _).div (continuous_haarPolynomialValue _) (fun U => (hpos U).ne'))
  have hiu : Integrable (fun U => a*haarPolynomialValue q U) μ :=
    (haarPolynomialValue_integrable q μ).const_mul a
  have hb : (∫ U, haarPolynomialValue (haarPolynomialGamma q q) U/haarPolynomialValue q U ∂μ) ≤
      ∫ U, a*haarPolynomialValue q U ∂μ := by
    apply integral_mono hiG hiu
    intro U
    apply (div_le_iff₀ (hpos U)).mpr
    have hh := haarPolynomialHeat_log_gradient_bound p ε C hε hp hC ht U
    change haarPolynomialValue (haarPolynomialGamma q q) U ≤ a*(haarPolynomialValue q U)^2 at hh
    nlinarith [hh]
  rw [integral_const_mul,haarPolynomialHeat_mean] at hb
  exact hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialEntropyBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero _root_.OAI.InvariantIsing.specialSkewRotation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entropy inequality for positive polynomials with bounded logarithmic gradient. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem haarPolynomial_entropy_bound {N d : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : haarPolynomialSpace N d) (ε C : ℝ) (hε : 0 < ε)
    (hp : ∀ U : SpecialOrthogonal N, ε ≤ haarPolynomialValue (p : MatrixPolynomial N) U)
    (hC : ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤
        C*(haarPolynomialValue (p : MatrixPolynomial N) U)^2) :
    (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U*
      Real.log (haarPolynomialValue (p : MatrixPolynomial N) U) ∂μ)-
      (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)*
        Real.log (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ) ≤
    C*(∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ)/(2*((N:ℝ)-2)) := by
  let ρ := (N:ℝ)-2
  let m := ∫ U, haarPolynomialValue (p : MatrixPolynomial N) U ∂μ
  let k := m*C/(2*ρ)
  let I (t : ℝ) := ∫ U, haarPolynomialValue (haarPolynomialGamma
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
      ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U/
    haarPolynomialValue ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N) U ∂μ
  let J (t : ℝ) := haarHeatEntropy μ p t-k*Real.exp (-2*ρ*t)
  have hρ : 0 < ρ := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [ρ]
    linarith
  have hkc : k*(2*ρ)=m*C := by
    dsimp only [k]
    field_simp
  have hD (t : ℝ) (ht : 0 < t) :
      HasDerivAt J (-I t+m*C*Real.exp (-2*ρ*t)) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-2*ρ*s))
        (-2*ρ*Real.exp (-2*ρ*t)) t := by
      convert ((hasDerivAt_id t).const_mul (-2*ρ)).exp using 1
      all_goals try with_reducible_and_instances rfl
      all_goals simp only [id_eq]
      all_goals ring
    have hd := (haarHeatEntropy_hasDerivAt μ p ε hε hp ht).sub (he.const_mul k)
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    change -I t+m*C*Real.exp (-2*ρ*t) = -I t-k*(-2*ρ*Real.exp (-2*ρ*t))
    rw [← hkc]
    ring
  have hnon (t : ℝ) (ht : 0 < t) : 0 ≤ -I t+m*C*Real.exp (-2*ρ*t) := by
    have hb := haarHeat_fisher_bound μ p ε C hε hp hC ht.le
    change I t ≤ C*Real.exp (-2*ρ*t)*m at hb
    nlinarith
  have hcont : ContinuousOn J (Ici 0) :=
    (continuousOn_haarPolynomialHeat_test_integral μ p (fun x => x*Real.log x)
      Real.continuous_mul_log).sub
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)
  have hmono : MonotoneOn J (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont
      (f' := fun t => -I t+m*C*Real.exp (-2*ρ*t))
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici,mem_Ioi] using ht
      exact (hD t ht').hasDerivWithinAt
    · intro t ht
      exact hnon t (by simpa only [interior_Ici,mem_Ioi] using ht)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2*ρ*t)) atTop (𝓝 0) := by
    have he := (tendsto_haar_gradient_envelope hN 1).comp
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    simp only [one_mul,Function.comp_def,id_eq]
    congr 1
    dsimp only [ρ]
    ring
  have hE : Tendsto (haarHeatEntropy μ p) atTop (𝓝 (m*Real.log m)) :=
    haarPolynomialHeat_test_tendsto_mean hN μ p (fun x => x*Real.log x) Real.continuous_mul_log
  have hJ : Tendsto J atTop (𝓝 (m*Real.log m)) := by
    simpa only [mul_zero,sub_zero] using hE.sub (hexp.const_mul k)
  have h0 : J 0 ≤ m*Real.log m := ge_of_tendsto hJ (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact hmono (by simp) ht ht)
  have hz : J 0 = (∫ U, haarPolynomialValue (p : MatrixPolynomial N) U*
      Real.log (haarPolynomialValue (p : MatrixPolynomial N) U) ∂μ)-k := by
    simp only [J,haarHeatEntropy,haarPolynomialHeat_zero,mul_zero,Real.exp_zero,mul_one]
  rw [hz] at h0
  change _-m*Real.log m ≤ C*m/(2*ρ)
  dsimp only [k] at h0
  linear_combination h0

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarExponentialPolynomial
attribute [-simp] _root_.OAI.InvariantIsing.haarPolynomialMomentDerivative_zero _root_.OAI.InvariantIsing.haarPolynomialMoment_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive polynomial truncations of an exponential observable. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarExpPolynomial_eval {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarExpPolynomial n p) =
      ∑ k ∈ Finset.range (n+1), (matrixPolynomialEval M p)^k/(Nat.factorial k : ℝ) := by
  simp only [haarExpPolynomial,map_sum,map_smul,map_pow,smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma haarExpPolynomial_derivation {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (A : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialDerivation A (haarExpPolynomial (n+1) p) =
      haarExpPolynomial n p*matrixPolynomialDerivation A p := by
  unfold haarExpPolynomial
  rw [Finset.sum_range_succ']
  simp only [map_add,map_sum,Derivation.map_smul_of_tower,pow_zero,
    Derivation.map_one_eq_zero,smul_zero,add_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hcoef : ((Nat.factorial (k+1) : ℝ)⁻¹)*((k+1:ℕ):ℝ) =
      (Nat.factorial k : ℝ)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  rw [Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  change (Nat.factorial (k+1) : ℝ)⁻¹ •
    (((k+1:ℕ):ℝ) • (p^k*matrixPolynomialDerivation A p)) = _
  rw [smul_smul,hcoef,smul_mul_assoc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_PositiveExponentialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotone positive truncations of the scalar exponential series. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

lemma positiveExpSum_one_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 1 ≤ positiveExpSum n x := by
  have h := Finset.single_le_sum
    (f := fun k => x^k/(Nat.factorial k : ℝ))
    (fun k (_ : k ∈ Finset.range (n+1)) => div_nonneg (pow_nonneg hx k) (Nat.cast_nonneg _))
    (show 0 ∈ Finset.range (n+1) by simp)
  simpa only [positiveExpSum,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using h

lemma positiveExpSum_mono (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    positiveExpSum n x ≤ positiveExpSum (n+1) x := by
  unfold positiveExpSum
  conv_rhs => rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))

lemma positiveExpSum_le_exp (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    positiveExpSum n x ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx (n+1)

lemma positiveExpSum_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => positiveExpSum n x) atTop (𝓝 (Real.exp x)) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).tendsto_sum_nat
  have hh := h.comp (tendsto_add_atTop_nat 1)
  simpa only [positiveExpSum,Function.comp_def,smul_eq_mul,div_eq_mul_inv,mul_comm,
    Real.exp_eq_exp_ℝ] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarExponentialGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform logarithmic-gradient bounds for positive exponential truncations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarExpPolynomial_gamma {N : ℕ} (n : ℕ) (p : MatrixPolynomial N) :
    haarPolynomialGamma (haarExpPolynomial (n+1) p) (haarExpPolynomial (n+1) p) =
      (haarExpPolynomial n p)^2*haarPolynomialGamma p p := by
  simp only [haarPolynomialGamma,haarExpPolynomial_derivation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma haarExpPolynomial_positive {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (hp : 0 ≤ matrixPolynomialEval M p) :
    1 ≤ matrixPolynomialEval M (haarExpPolynomial n p) := by
  rw [haarExpPolynomial_eval]
  exact positiveExpSum_one_le n hp

lemma haarExpPolynomial_log_gradient_bound {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (hp : 0 ≤ matrixPolynomialEval M p)
    (C : ℝ) (hC : 0 ≤ C) (hG : matrixPolynomialEval M (haarPolynomialGamma p p) ≤ C) :
    matrixPolynomialEval M (haarPolynomialGamma (haarExpPolynomial (n+1) p) (haarExpPolynomial (n+1) p)) ≤
      C*(matrixPolynomialEval M (haarExpPolynomial (n+1) p))^2 := by
  have h0 := haarExpPolynomial_positive n p M hp
  have h1 := haarExpPolynomial_positive (n+1) p M hp
  have hm : matrixPolynomialEval M (haarExpPolynomial n p) ≤
      matrixPolynomialEval M (haarExpPolynomial (n+1) p) := by
    simp only [haarExpPolynomial_eval]
    exact positiveExpSum_mono n hp
  rw [haarExpPolynomial_gamma,map_mul,map_pow]
  calc
    _ ≤ (matrixPolynomialEval M (haarExpPolynomial n p))^2*C :=
      mul_le_mul_of_nonneg_left hG (sq_nonneg _)
    _ ≤ C*(matrixPolynomialEval M (haarExpPolynomial (n+1) p))^2 := by
      rw [mul_comm _ C]
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by linarith) (by linarith)).mpr hm) hC

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarExponentialLimit
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dominated transport from positive polynomial truncations to exponential observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarExpPolynomial_test_integral_tendsto {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (p : MatrixPolynomial N)
    (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (F : ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun n : ℕ => ∫ U, F (haarPolynomialValue (haarExpPolynomial (n+1) p) U) ∂μ)
      atTop (𝓝 (∫ U, F (Real.exp (haarPolynomialValue p U)) ∂μ)) := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn F (Icc 1 (Real.exp B)) from hF.continuousOn)
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => (hF.comp (continuous_haarPolynomialValue _)).aestronglyMeasurable)
    (integrable_const K)
  · intro n
    apply ae_of_all
    intro U
    apply hK
    refine ⟨haarExpPolynomial_positive (n+1) p _ (hp U),?_⟩
    rw [haarPolynomialValue,haarExpPolynomial_eval]
    exact (positiveExpSum_le_exp (n+1) (hp U)).trans
      (Real.exp_le_exp.mpr ((le_abs_self _).trans (hB U)))
  · apply ae_of_all
    intro U
    apply hF.continuousAt.tendsto.comp
    have h := (positiveExpSum_tendsto (haarPolynomialValue p U)).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,haarPolynomialValue,haarExpPolynomial_eval,positiveExpSum] using h

theorem haar_exp_polynomial_entropy_bound {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C) :
    (∫ U, Real.exp (haarPolynomialValue p U)*Real.log (Real.exp (haarPolynomialValue p U)) ∂μ)-
      (∫ U, Real.exp (haarPolynomialValue p U) ∂μ)*
        Real.log (∫ U, Real.exp (haarPolynomialValue p U) ∂μ) ≤
      C*(∫ U, Real.exp (haarPolynomialValue p U) ∂μ)/(2*((N:ℝ)-2)) := by
  have hn (n : ℕ) :
      (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U*
        Real.log (haarPolynomialValue (haarExpPolynomial (n+1) p) U) ∂μ)-
      (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ)*
        Real.log (∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ) ≤
      C*(∫ U, haarPolynomialValue (haarExpPolynomial (n+1) p) U ∂μ)/(2*((N:ℝ)-2)) := by
    obtain ⟨d,hd⟩ := exists_mem_haarPolynomialSpace (haarExpPolynomial (n+1) p)
    exact haarPolynomial_entropy_bound hN μ ⟨_,hd⟩ 1 C zero_lt_one
      (fun U => haarExpPolynomial_positive (n+1) p _ (hp U))
      (fun U => haarExpPolynomial_log_gradient_bound n p _ (hp U) C hC (hG U))
  have hm := haarExpPolynomial_test_integral_tendsto μ p hp id continuous_id
  simp only [id_eq] at hm
  have he := haarExpPolynomial_test_integral_tendsto μ p hp (fun x => x*Real.log x) Real.continuous_mul_log
  exact le_of_tendsto_of_tendsto (he.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hm))
    ((hm.const_mul C).div_const (2*((N:ℝ)-2))) (Eventually.of_forall hn)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HerbstDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-variable entropy-to-exponential-moment argument. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

theorem log_moment_le_of_entropy (M M' : ℝ → ℝ) (A : ℝ)
    (hM : ∀ t, 0 < M t) (h0 : M 0 = 1) (hD : ∀ t, HasDerivAt M (M' t) t)
    (hE : ∀ t, 0 < t → t*M' t-M t*Real.log (M t) ≤ A*t^2*M t)
    {t : ℝ} (ht : 0 < t) : Real.log (M t) ≤ M' 0*t+A*t^2 := by
  let K (s : ℝ) := Real.log (M s)/s-A*s
  let K' (s : ℝ) := (M' s/M s*s-Real.log (M s))/s^2-A
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt K (K' s) s := by
    convert (((hD s).log (hM s).ne').div (hasDerivAt_id s) hs.ne').sub
      ((hasDerivAt_id s).const_mul A) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | simp only [K',id_eq,mul_one]
  have hn (s : ℝ) (hs : 0 < s) : K' s ≤ 0 := by
    have heq : M' s/M s*s-Real.log (M s) =
        (s*M' s-M s*Real.log (M s))/M s := by
      field_simp [(hM s).ne']
    have hb : (M' s/M s*s-Real.log (M s))/s^2 ≤ A := by
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      rw [heq]
      apply (div_le_iff₀ (hM s)).mpr
      exact hE s hs
    exact sub_nonpos.mpr hb
  have hanti : AntitoneOn K (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ioi,mem_Ioi] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ioi,mem_Ioi] using hs
      rw [(hd s hs').deriv]
      exact hn s hs'
  have hlog := ((hD 0).log (hM 0).ne').tendsto_slope_zero_right
  have hl : Tendsto (fun s : ℝ => Real.log (M s)/s) (𝓝[>] (0:ℝ)) (𝓝 (M' 0)) := by
    simpa only [zero_add,h0,Real.log_one,sub_zero,div_one,smul_eq_mul,div_eq_mul_inv,mul_comm,
      inv_one,mul_one] using hlog
  have hK : Tendsto K (𝓝[>] (0:ℝ)) (𝓝 (M' 0)) := by
    have hz : Tendsto (fun s : ℝ => A*s) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [mul_zero] using hid.const_mul A
    simpa only [sub_zero] using hl.sub hz
  have hb : K t ≤ M' 0 := ge_of_tendsto hK (by
    have hu : ∀ᶠ s : ℝ in 𝓝[>] (0:ℝ), s < t :=
      (show ∀ᶠ s : ℝ in 𝓝 (0:ℝ), s < t from Iio_mem_nhds ht).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hu] with s hs hst
    exact hanti hs ht hst.le)
  have hh : Real.log (M t)/t ≤ M' 0+A*t := by
    change Real.log (M t)/t-A*t ≤ M' 0 at hb
    linarith
  have hf := (div_le_iff₀ ht).mp hh
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMoment
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential moments and their derivatives for polynomial observables on SO(N). -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialMoment_pos {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    0 < haarPolynomialMoment μ p t :=
  integral_exp_pos (continuous_haar_integrable μ _
    (Real.continuous_exp.comp (continuous_const.mul (continuous_haarPolynomialValue p))))

lemma haarPolynomialMoment_hasDerivAt {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (p : MatrixPolynomial N) (t : ℝ) :
    HasDerivAt (haarPolynomialMoment μ p) (haarPolynomialMomentDerivative μ p t) t := by
  let F' (s : ℝ) (U : SpecialOrthogonal N) :=
    haarPolynomialValue p U*Real.exp (s*haarPolynomialValue p U)
  have hc : Continuous (fun z : ℝ × SpecialOrthogonal N => F' z.1 z.2) := by
    have hp := (continuous_haarPolynomialValue p).comp (continuous_snd : Continuous fun z : ℝ × SpecialOrthogonal N => z.2)
    exact hp.mul (Real.continuous_exp.comp (continuous_fst.mul hp))
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set (SpecialOrthogonal N)))).exists_bound_of_continuousOn
    (show ContinuousOn (fun z => F' z.1 z.2) (Icc (t-1) (t+1) ×ˢ Set.univ) from hc.continuousOn)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (s := Ioo (t-1) (t+1)) (F' := F') (bound := fun _ => B)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun s => (Real.continuous_exp.comp
      (continuous_const.mul (continuous_haarPolynomialValue p))).measurable.aestronglyMeasurable)
    (continuous_haar_integrable μ _ (Real.continuous_exp.comp
      (continuous_const.mul (continuous_haarPolynomialValue p))))
    ((hc.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
    (ae_of_all μ fun U s hs => hB (s,U) ⟨⟨hs.1.le,hs.2.le⟩,mem_univ _⟩)
    (integrable_const B) ?_).2
  apply ae_of_all
  intro U s _
  convert ((hasDerivAt_id s).mul_const (haarPolynomialValue p U)).exp using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp only [F',id_eq,Function.comp_apply,Pi.mul_apply]
  all_goals ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarExponentialMomentBound
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian exponential-moment bounds for nonnegative polynomial observables. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

lemma haarPolynomialGamma_scaled_value {N : ℕ} (p : MatrixPolynomial N) (c : ℝ)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma (c • p) (c • p)) =
      c^2*matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [haarPolynomialGamma,Derivation.map_smul_of_tower,map_sum,map_mul,map_smul,
    smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem haarPolynomialMoment_log_bound_of_nonneg {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (hp : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue p U)
    (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Real.log (haarPolynomialMoment μ p t) ≤
      (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2 := by
  have hE (s : ℝ) (hs : 0 < s) :
      s*haarPolynomialMomentDerivative μ p s-
        haarPolynomialMoment μ p s*Real.log (haarPolynomialMoment μ p s) ≤
      (C/(2*((N:ℝ)-2)))*s^2*haarPolynomialMoment μ p s := by
    have hscaled (U : SpecialOrthogonal N) : haarPolynomialValue (s • p) U = s*haarPolynomialValue p U := by
      simp only [haarPolynomialValue,map_smul,smul_eq_mul]
    have hp' (U : SpecialOrthogonal N) : 0 ≤ haarPolynomialValue (s • p) U := by
      rw [hscaled]
      exact mul_nonneg hs.le (hp U)
    have hG' (U : SpecialOrthogonal N) :
        haarPolynomialValue (haarPolynomialGamma (s • p) (s • p)) U ≤ C*s^2 := by
      rw [haarPolynomialValue,haarPolynomialGamma_scaled_value]
      have hh := mul_le_mul_of_nonneg_left (hG U) (sq_nonneg s)
      simpa only [haarPolynomialValue,mul_comm] using hh
    have he := haar_exp_polynomial_entropy_bound hN μ (s • p) hp' (C*s^2)
      (mul_nonneg hC (sq_nonneg s)) hG'
    simp_rw [hscaled,Real.log_exp] at he
    have hi : (∫ U, Real.exp (s*haarPolynomialValue p U)*(s*haarPolynomialValue p U) ∂μ) =
        s*haarPolynomialMomentDerivative μ p s := by
      rw [haarPolynomialMomentDerivative,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all μ fun U => by ring
    rw [hi] at he
    change s*haarPolynomialMomentDerivative μ p s-
      haarPolynomialMoment μ p s*Real.log (haarPolynomialMoment μ p s) ≤
      C*s^2*haarPolynomialMoment μ p s/(2*((N:ℝ)-2)) at he
    linear_combination he
  have hh := log_moment_le_of_entropy (haarPolynomialMoment μ p)
    (haarPolynomialMomentDerivative μ p) (C/(2*((N:ℝ)-2)))
    (haarPolynomialMoment_pos μ p) (haarPolynomialMoment_zero μ p)
    (haarPolynomialMoment_hasDerivAt μ p) hE ht
  simpa only [haarPolynomialMomentDerivative_zero] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Haar_HaarPolynomialMomentShift
attribute [-instance] _root_.OAI.InvariantIsing.cavityOrientedBaseLaw_probability _root_.OAI.InvariantIsing.instIsMarkovKernelProdMatrixRealEuclideanSpaceCavityGaussianKernel _root_.OAI.InvariantIsing.priorFrozenLaw_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.specialOrthogonal_topologicalGroup _root_.OAI.InvariantIsing.tensorFrozenLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the positivity normalization from polynomial exponential-moment bounds. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
namespace InvariantIsing

lemma haarPolynomialDerivation_C {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    matrixPolynomialDerivation A (MvPolynomial.C c) = 0 :=
  (matrixPolynomialDerivation A).map_algebraMap c

lemma haarPolynomialGamma_add_C {N : ℕ} (p : MatrixPolynomial N) (c : ℝ) :
    haarPolynomialGamma (p+MvPolynomial.C c) (p+MvPolynomial.C c) = haarPolynomialGamma p p := by
  simp only [haarPolynomialGamma,map_add,haarPolynomialDerivation_C,add_zero]

lemma haarPolynomialMoment_add_C {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (p : MatrixPolynomial N) (c t : ℝ) :
    haarPolynomialMoment μ (p+MvPolynomial.C c) t = Real.exp (t*c)*haarPolynomialMoment μ p t := by
  unfold haarPolynomialMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all μ fun U => by
    simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    rw [← Real.exp_add]
    congr 1
    ring

theorem haarPolynomialMoment_log_bound_oai {N : ℕ} (hN : 3 ≤ N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (p : MatrixPolynomial N) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ U : SpecialOrthogonal N, haarPolynomialValue (haarPolynomialGamma p p) U ≤ C)
    {t : ℝ} (ht : 0 < t) :
    Real.log (haarPolynomialMoment μ p t) ≤
      (∫ U, haarPolynomialValue p U ∂μ)*t+C/(2*((N:ℝ)-2))*t^2 := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound p
  have hpq (U : SpecialOrthogonal N) : 0 ≤ haarPolynomialValue (p+MvPolynomial.C B) U := by
    simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    have hh := hB U
    rw [Real.norm_eq_abs] at hh
    dsimp only [haarPolynomialValue] at hh
    linarith [(abs_le.mp hh).1]
  have hGq (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p+MvPolynomial.C B) (p+MvPolynomial.C B)) U ≤ C := by
    rw [haarPolynomialGamma_add_C]
    exact hG U
  have h := haarPolynomialMoment_log_bound_of_nonneg hN μ (p+MvPolynomial.C B) hpq C hC hGq ht
  rw [haarPolynomialMoment_add_C,Real.log_mul (Real.exp_ne_zero _) (haarPolynomialMoment_pos μ p t).ne',
    Real.log_exp] at h
  have hm : (∫ U, haarPolynomialValue (p+MvPolynomial.C B) U ∂μ) =
      (∫ U, haarPolynomialValue p U ∂μ)+B := by
    have he (U : SpecialOrthogonal N) : haarPolynomialValue (p+MvPolynomial.C B) U = haarPolynomialValue p U+B := by
      simp only [haarPolynomialValue,map_add,matrixPolynomialEval_C]
    simp_rw [he]
    rw [integral_add (haarPolynomialValue_integrable p μ) (integrable_const B)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rw [hm] at h
  nlinarith

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.haarPolynomialMoment_log_bound_oai := @OAI.InvariantIsing.haarPolynomialMoment_log_bound_oai
