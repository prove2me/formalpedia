-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:34:17.219364+00:00
-- url     : https://prove2.me/submissions/828fff10-7437-4eda-ab25-610ac18c71c3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B159
import Definitions.Def_OAIE3v2B164

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem same_side_of_cut_of_small_displacement {x y c ρ : ℝ}
    (hxy : |x - y| ≤ ρ) (hgap : ρ < |x - c|) : (c ≤ x ↔ c ≤ y) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  by_cases hcx : c ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hcx)] at hgap
    have hcy : c ≤ y := by linarith
    simp only [hcx, hcy]
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hcx))] at hgap
    have hcy : ¬c ≤ y := by linarith
    simp only [hcx, hcy]

end Erdos3

end

section

namespace Erdos3

theorem cyclic_wrap_branch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hd := good_circle_observations_control_representatives h x y hρ hx hy hdist
  rw [← sub_div, abs_div, abs_of_pos hN] at hd
  have hdiff : |(x.val : ℝ) - y.val| ≤ (N : ℝ) * ρ := by
    have h := (div_le_iff₀ hN).mp hd
    nlinarith
  have hgap := (outside_cyclicWrapExceptional h x hx).2.2
  have hb := same_side_of_cut_of_small_displacement hdiff hgap
  exact_mod_cast hb

theorem cyclic_representative_difference_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  rw [cyclic_representative_add h x, cyclic_representative_add h y]
  simp only [← hb]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicOrdinaryShiftBranches
namespace OAI

section

namespace Erdos3

theorem ordinaryShiftBranch_bound {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    |ordinaryShiftBranch h b x| ≤ 1 := by
  have hb := b.isLt
  unfold ordinaryShiftBranch
  rw [abs_le]
  split_ifs <;> omega

theorem ordinary_shift_from_cyclic_representative {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    (x.val : ℤ) + h.val - (b.val : ℤ) * N =
      ((h + x).val : ℤ) + ordinaryShiftBranch h b x * N := by
  rw [cyclic_representative_add h x]
  unfold ordinaryShiftBranch
  split_ifs <;> ring

theorem ordinaryShiftBranch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ordinaryShiftBranch h b x = ordinaryShiftBranch h b y := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  simp only [ordinaryShiftBranch, ← hb]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicAlternativePathRecovery
namespace OAI

section

namespace Erdos3

theorem ordinary_shift_path_dist_le {X : Type*} [PseudoMetricSpace X]
    (P : ℤ → X) {N : ℕ} [NeZero N] (h : ZMod N) (b : Fin 2) (x y : ZMod N)
    {ρ δ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hcircle : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ t : ℤ, |t| ≤ 1 →
      dist (P (((h + x).val : ℤ) + t * N)) (P (((h + y).val : ℤ) + t * N)) ≤ δ) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hb := ordinaryShiftBranch_eq_of_good_circle h b x y hρ hx hy hcircle
  rw [ordinary_shift_from_cyclic_representative h b x,
    ordinary_shift_from_cyclic_representative h b y, ← hb]
  exact hobs _ (ordinaryShiftBranch_bound h b x)

theorem positive_cell_ordinary_shift_recovery {I J X : Type*} [PseudoMetricSpace X]
    {N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (P : ℤ → X) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ j x y, 0 < B j x → 0 < B j y → ∀ t : ℤ, |t| ≤ 1 →
      dist (P ((x.val : ℤ) + t * N)) (P ((y.val : ℤ) + t * N)) ≤ δ)
    (h : ZMod N) (b : Fin 2) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hpos (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z ∧ 0 < B j (z + h) := by
    rcases mul_pos_iff.mp hz with h | h
    · exact h
    · linarith [hA i z]
  obtain ⟨hAx, hBx⟩ := hpos x hxy
  obtain ⟨hAy, hBy⟩ := hpos y hyy
  apply ordinary_shift_path_dist_le P h b x y hρ hx hy (hcircle i x y hAx hAy)
  intro t ht
  simpa only [add_comm h x, add_comm h y] using hobs j (x + h) (y + h) hBx hBy t ht

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_product_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [DecidableEq ι]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : (pi D).filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → (pi D).Niltest w,
            (∀ j, (A j).orbit = g) ∧
            (∀ j, (A j).UnitIntervalValued) ∧
            (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ j, ((A j).observable z).re = 1) ∧
            (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
             ∀ j x y, 0 < ((A j).observable x).re → 0 < ((A j).observable y).re →
               ∀ i, dist (productProjection D i x) (productProjection D i y) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_niltest_partition s 1
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ 2 + (X + 4) ^ 4 + (X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ L _ _ _ _ _ _ _ _ _ _ d D w p ρ hp hι hD hρ hρinv g
  let t := p + (p + 2) ^ 2 + (p + 4) ^ 4 + (p + 2) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hgeom : (p + 2) ^ 2 ≤ t := by
    dsimp [t]
    linarith [show 0 ≤ (p + 4) ^ 4 from by positivity,
      show 0 ≤ (p + 2) ^ a from by positivity]
  let ε := ρ / Real.exp ((p + 4) ^ 4)
  have hε : 0 < ε := div_pos hρ (Real.exp_pos _)
  have hεinv : 1 / ε ≤ Real.exp ((t + 2) ^ 1) := by
    calc
      _ = Real.exp ((p + 4) ^ 4) * (1 / ρ) := by dsimp [ε]; field_simp
      _ ≤ Real.exp ((p + 4) ^ 4) * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hρinv (Real.exp_pos _).le
      _ = Real.exp ((p + 4) ^ 4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; simp only [pow_one]; nlinarith [sq_nonneg (p + 2)])
  obtain ⟨n, hn, hnb, A, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition (pi D) w ht ((pi_geometry D hp hι hD).mono (pi D) hgeom) hε hεinv g
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, horbit, hunit,
    fun j => (hcomplexity j).mono hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro j x y hx hy i
  have hxy := hdiam j x y hx hy
  have hprod := (productSpaceEquiv_lipschitz D).dist_le_mul x y
  have hcoord := dist_le_pi_dist (productSpaceEquiv D x) (productSpaceEquiv D y) i
  change dist (productProjection D i x) (productProjection D i y) ≤
    dist (productSpaceEquiv D x) (productSpaceEquiv D y) at hcoord
  calc
    _ ≤ (productMetricBound d : ℝ) * dist x y := hcoord.trans hprod
    _ ≤ (productMetricBound d : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hxy (productMetricBound d).coe_nonneg
    _ ≤ Real.exp ((p + 4) ^ 4) * ε :=
      mul_le_mul_of_nonneg_right (productMetricBound_le_exp d hp hι (fun i => (hD i).1)) hε.le
    _ = ρ := by dsimp [ε]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedShiftTesting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_refined_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
      (A : I → ZMod N → ℝ) {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} s N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (I × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (I × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → 0 < A j.1 x) ∧
          (∀ j x y, 0 < U j x → 0 < U j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          ∀ h j x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
            0 < U j x → 0 < U j y →
            |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ ∧
              (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) ∧
              ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  obtain ⟨B, _, hinterval⟩ := exists_interval_circle_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let R := T + (T + 2) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * T + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ s N _ A p ρ hs hp hcard hA hsum hρ hρinv
  obtain ⟨n, hn, hnb, V, hV, hVsum, hdiam⟩ := hinterval N hp hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : 2 * t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [T, X, R, Q, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hQ0 : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  let U : (I × Fin n) → ZMod N → ℝ := fun j x => A j.1 x * V j.2 x
  have hpositive (j : I × Fin n) (x : ZMod N) (hx : 0 < U j x) :
      0 < A j.1 x ∧ 0 < V j.2 x := by
    change 0 < A j.1 x * V j.2 x at hx
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hA j.1).unit_interval x).1]
  refine ⟨n, hn, ?_, U, ?_, ?_, fun j x hx => (hpositive j x hx).1,
    fun j x y hx hy => hdiam j.2 x y (hpositive j x hx).2 (hpositive j y hy).2,
    fun h => cyclicWrapExceptional_density_le h hρ.le, ?_⟩
  · calc
      _ = (Fintype.card I : ℝ) * n := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      _ ≤ Real.exp p * Real.exp ((p + B) ^ B) :=
        mul_le_mul hcard hnb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp t := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr htC
  · intro j
    exact (((hA j.1).mono le_rfl hpt).mul ((hV j.2).mono hs hBt) ht).mono le_rfl hproduct
  · intro x
    simp only [U, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hVsum, mul_one]
    exact hsum x
  · intro h j x y hx hy hUx hUy
    have hxy := hdiam j.2 x y (hpositive j x hUx).2 (hpositive j y hUy).2
    exact ⟨good_circle_observations_control_representatives h x y hρ hx hy hxy,
      cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hxy,
      cyclic_representative_difference_of_good_circle h x y hρ hx hy hxy⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedObservationRefinement
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type v} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{max u v} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
               ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ) := by
  obtain ⟨C, hC, hpartition⟩ := exists_native_product_partition s a
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let G := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) g
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) hp hι hD hρ hρinv G
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      ((pi D).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  have hpoint (i : ι) (x : ZMod N) :
      productProjection D i ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x)) =
        (D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x) := by
    exact congrArg (fun z : (D i).RealGroup => (QuotientGroup.mk z : (D i).Space))
      (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) g
        (fun _ : Unit => (x.val : ℤ)) i)
  refine ⟨n, hn, hnb, A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test (pi D) le_rfl (tests j) (hunit j) (hcomplexity j) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy) i
    simpa only [hpoint] using hd

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition.{0, 0} s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * X + 3 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let E := fun k : ι × Fin 3 => D k.1
  let G := fun k : ι × Fin 3 =>
    (g k.1).translate (fun _ => Nat.zero_lt_one) (fun _ => ((k.2.val : ℤ) - 1) * N)
  let : FiniteDimensional ℚ (∀ k : ι × Fin 3, L k.1) :=
    (productFinBasis E).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    realification_moduleTopology_t2 (productFinBasis E)
  let r := 3 * p + 3
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcount : (Fintype.card (ι × Fin 3) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ :=
    hpartition E G N hr hcount (fun k => (hD k.1).mono (D k.1) hpr) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  intro j x y hx hy i t ht
  have ht' := abs_le.mp ht
  let k : Fin 3 := ⟨(t + 1).toNat, by omega⟩
  have hk : (k.val : ℤ) - 1 = t := by dsimp [k]; omega
  simpa only [E, G, cyclicOrbitPoint_translate, hk] using hdiam j x y hx hy (i, k)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_residue_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ ((n * q : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod q) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.2) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_observation_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_controlled_residue_refinement
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  obtain ⟨U, hcount, hU, hUsum, hsupport⟩ := hrefine (q := q) A ht hs
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hBt))
    (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hA j).mono le_rfl hBt) hsum
  have hsumcost : t + (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsumcost
  refine ⟨n, hn, ?_, U, fun j => (hU j).mono le_rfl hcost, hUsum,
    fun j x hx => (hsupport j x hx).2, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card] using
      hcount.trans (Real.exp_le_exp.mpr hcost)
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i t ht
    exact hdiam j.1 x y (hsupport j x hx).1 (hsupport j y hy).1 i t ht

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoSitePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_two_site_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_residue_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_interval_refined_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, U, hU, hUsum, hres, hobs⟩ :=
    hpartition D g q N hs hp hι hD hq hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hinv : 1 / ρ ≤ Real.exp ((t + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨m, hm, hcount, A, hA, hsum, hsupport, hcircle, hexception, _⟩ :=
    hrefine U hs ht
      (by simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul] using
        hnb.trans (Real.exp_le_exp.mpr hBt))
      (fun j => (hU j).mono le_rfl hBt) hUsum hρ hinv
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum,
    fun j x hx => hres j.1 x (hsupport j x hx), hcircle, hexception, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  have hdiam j x y (hx : 0 < A j x) (hy : 0 < A j y) (i : ι) (k : ℤ) (hk : |k| ≤ 1) :
      dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + k * N))
        ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + k * N)) ≤ ρ :=
    hobs j.1 x y (hsupport j x hx) (hsupport j y hy) i k hk
  refine ⟨hdiam, ?_⟩
  intro h b j k x y hx hy hxy hyy i
  exact positive_cell_ordinary_shift_recovery A A ((D i).integerOrbitPoint (g i)) hρ
    (fun j x => ((hA j).unit_interval x).1) hcircle
    (fun j x y hx hy t ht => hdiam j x y hx hy i t ht) h b j k x y hx hy hxy hyy

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AnchoredObservationPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_anchored_observation_partition_s2_oai (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (E : ∀ i, Bool → RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i b, (E i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ι → ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i b, (E i b).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((E i false).integerOrbitPoint (g i false) ((x.val : ℤ) + c i))
               ((E i false).integerOrbitPoint (g i false) ((y.val : ℤ) + c i)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((E i true).integerOrbitPoint (g i true) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((E i true).integerOrbitPoint (g i true) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_two_site_partition s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((2 * X + 2 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d E g c q N _ _ p ρ hs hp hι hE hq hρ hρinv
  let D := fun k : ι × Bool => E k.1 k.2
  let G : ∀ k : ι × Bool, (D k).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun | (i, false) => (g i false).translate (fun _ => Nat.zero_lt_one) (fun _ => c i)
        | (i, true) => g i true
  let r := 2 * p + 2
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcard : (Fintype.card (ι × Bool) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, m, hn, hm, hcount, A, hA, hsum, hres, hcircle, hexception, hobs, hmove⟩ :=
    hpartition D G q N hs hr hcard (fun k => (hE k.1 k.2).mono (E k.1 k.2) hpr)
      (hq.trans (Real.exp_le_exp.mpr hpr)) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
  constructor
  · intro j x y hx hy i
    have h := hobs j x y hx hy (i, false) 0 (by norm_num)
    simpa only [D, G, zero_mul, add_zero, integerOrbitPoint_translate] using h
  · intro h b j k x y hx hy hxy hyy i
    exact hmove h b j k x y hx hy hxy hyy (i, true)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition_s2_oai := @OAI.Erdos3.RationalFilteredNilmanifold.exists_anchored_observation_partition_s2_oai
