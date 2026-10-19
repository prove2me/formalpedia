-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:21:57.114991+00:00
-- url     : https://prove2.me/submissions/ba787caf-3d28-4c21-9a79-fd2c18df21e3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B192
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_native_chart_partition_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositivePartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_weighted_partition_score {Ω ι : Type*} [Fintype Ω] [Fintype ι] [Nonempty ι]
    (a : Ω → ℝ) (w : ι → Ω → ℝ) (hsum : ∀ x, ∑ i, w i x = 1)
    {S : ℝ} (hS : S ≤ 𝔼 x, a x) :
    ∃ i, S / Fintype.card ι ≤ 𝔼 x, a x * w i x := by
  have htotal : (∑ i, 𝔼 x, a x * w i x) = 𝔼 x, a x := by
    rw [← Finset.expect_sum_comm]
    apply Finset.expect_congr rfl
    intro x _
    rw [← Finset.mul_sum, hsum, mul_one]
  have hmean : (𝔼 i, 𝔼 x, a x * w i x) = (𝔼 x, a x) / Fintype.card ι := by
    rw [Fintype.expect_eq_sum_div_card, htotal]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show S / Fintype.card ι ≤ 𝔼 i, 𝔼 x, a x * w i x from
      hmean.symm ▸ div_le_div_of_nonneg_right hS (Nat.cast_nonneg _))
  exact ⟨i, hi⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

theorem positiveLocalization_unit_interval :
    (T.positiveLocalization hT psi hpsi K hLip).UnitIntervalValued := by
  intro z
  exact ⟨rfl, mul_nonneg (hT z).2.1 (hpsi z).1,
    (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2⟩

theorem positiveLocalization_eval_re (x : σ → ℤ) :
    ((T.positiveLocalization hT psi hpsi K hLip).eval x).re =
      (T.eval x).re * psi (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x T.orbit)) := rfl

theorem positiveLocalization_support :
    tsupport (T.positiveLocalization hT psi hpsi K hLip).observable ⊆ tsupport psi := by
  apply closure_mono
  intro z hz
  change psi z ≠ 0
  intro hzero
  apply hz
  change (((T.observable z).re * psi z : ℝ) : ℂ) = 0
  rw [hzero, mul_zero, Complex.ofReal_zero]

theorem positiveLocalization_complexity {p : ℝ} (hp : 0 ≤ p)
    (hcomplexity : T.ComplexityLE p) (hK : (K : ℝ) ≤ Real.exp p) :
    (T.positiveLocalization hT psi hpsi K hLip).ComplexityLE (p + 4) := by
  refine ⟨hcomplexity.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + ((T.lipBound + K : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [NNReal.coe_add, Real.exp_add]
  have hbudget := observable_budget hcomplexity
  have hnorm := T.normBound.coe_nonneg
  have hone := Real.one_le_exp hp
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg p)
  nlinarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.IntegralScoredKernel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

theorem exists_scored_native_chart_s2_oai (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ X L : Type*} [Fintype X]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      (a : X → ℝ) (u : X → σ → ℤ) {p : ℝ},
      0 ≤ p → T.ComplexityLE p → T.UnitIntervalValued →
      Real.exp (-p) ≤ (𝔼 x, a x * (T.eval (u x)).re) →
      letI := D.metricSpace
      ∃ (r : ℝ≥0) (z : D.RealGroup) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space),
        0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ i, |(D.basis.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ C)) ∧
        (∀ v, phi v = QuotientGroup.mk
          (z * (NilpotentLieBCHGroup.basisHomeomorph (D.basis.baseChange ℝ)).symm v)) ∧
        phi.source = {v | ∀ i, |v i| < (r : ℝ)} ∧
        ∃ U : D.Niltest w, U.orbit = T.orbit ∧ U.UnitIntervalValued ∧
          U.ComplexityLE ((p + 2) ^ C) ∧ HasCompactSupport U.observable ∧
          tsupport U.observable ⊆ phi.target ∧
          (Real.exp (-((p + 2) ^ C)) ≤ 𝔼 x, a x * (U.eval (u x)).re) ∧
          tsupport U.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4) ∧
          ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
            LipschitzOnWith K phi phi.source := by
  obtain ⟨A, hA, hpartition⟩ := exists_native_chart_partition_s2 s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Polynomial.X + (Polynomial.X + 2) ^ A + 4)
  refine ⟨C, hC, ?_⟩
  intro σ X L _ _ _ d _ _ _ _ D w T a u p hp hT hpositive hscore
  let := D.metricSpace
  obtain ⟨r, hr, hr1, hri, n, hn, hnb, centers, phi, hcenters, hphi, hsource,
    P, hP, f, hfrange, hfsum, hfsupport, hfLip, hfInner, K, hK, hForward⟩ := hpartition D hp hT.1
  let q : ℝ := (p + 2) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hb : p + q + 4 ≤ (p + 2) ^ C := by
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  let point : X → D.Space := fun x => QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (u x) T.orbit)
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_weighted_partition_score
    (fun x => a x * (T.eval (u x)).re) (fun j x => f j (point x))
    (fun x => hfsum (point x)) hscore
  let U := T.positiveLocalization hpositive (f j) (hfrange j) P (hfLip j)
  have hU : U.ComplexityLE ((p + 2) ^ C) :=
    (T.positiveLocalization_complexity hpositive (f j) (hfrange j) P (hfLip j)
      hq (hT.mono hpq) hP).mono (by linarith)
  have hsupp : tsupport U.observable ⊆ tsupport (f j) :=
    T.positiveLocalization_support hpositive (f j) (hfrange j) P (hfLip j)
  refine ⟨r, centers j, phi j, hr, hr1, hri.trans (Real.exp_le_exp.mpr hqC),
    fun i => (hcenters j i).trans (Real.exp_le_exp.mpr hqC), hphi j, hsource j,
    U, rfl, T.positiveLocalization_unit_interval hpositive (f j) (hfrange j) P (hfLip j),
    hU, (hfsupport j).1.of_isClosed_subset isClosed_closure hsupp,
    hsupp.trans (hfsupport j).2, ?_, hsupp.trans (hfInner j), K,
    hK.trans (Real.exp_le_exp.mpr hqC), hForward j⟩
  have hnj : (0 : ℝ) < n := by exact_mod_cast hn
  have hscoreU : Real.exp (-p) / n ≤ 𝔼 x, a x * (U.eval (u x)).re := by
    simpa only [Fintype.card_fin, U, Niltest.positiveLocalization_eval_re,
      point, mul_assoc] using hj
  calc
    _ ≤ Real.exp (-p - q) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-p) / Real.exp q := Real.exp_sub _ _
    _ ≤ Real.exp (-p) / n := div_le_div_of_nonneg_left (Real.exp_nonneg _) hnj hnb
    _ ≤ _ := hscoreU

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.RationalFilteredNilmanifold.exists_scored_native_chart_s2_oai.{u_1, u_2, u_3}
