-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_partition_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:54:16.361011+00:00
-- url     : https://prove2.me/submissions/b1bda93e-16fa-4e3f-8917-64ff51167721

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B124
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_square_image_partition

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RefilteredExpansionErrorBudget
namespace OAI

section

namespace Erdos3

theorem refiltered_expansion_error_budget {cost metric ε R : ℝ}
    (hc : 0 ≤ cost) (hm : 0 ≤ metric) (hε : 0 ≤ ε)
    (hbudget : cost + metric + 10 ≤ R) :
    Real.exp cost * (Real.exp metric + 2) * ε + 6 * ε ≤ Real.exp R * ε := by
  have hE : 1 ≤ Real.exp cost := Real.one_le_exp hc
  have hK : 1 ≤ Real.exp metric := Real.one_le_exp hm
  have hEK : 1 ≤ Real.exp cost * Real.exp metric := by nlinarith
  have hEE : Real.exp cost ≤ Real.exp cost * Real.exp metric := by nlinarith [Real.exp_pos cost]
  have hsmall : Real.exp cost * (Real.exp metric + 2) + 6 ≤
      9 * (Real.exp cost * Real.exp metric) := by nlinarith
  have h9 : (9 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have hlarge : Real.exp cost * (Real.exp metric + 2) + 6 ≤ Real.exp R := by
    calc
      _ ≤ 9 * (Real.exp cost * Real.exp metric) := hsmall
      _ ≤ Real.exp 10 * (Real.exp cost * Real.exp metric) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = Real.exp (cost + metric + 10) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hbudget
  nlinarith [mul_le_mul_of_nonneg_right hlarge hε]

end Erdos3

end

end OAI

end

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

theorem cyclicCutNeighborhood_mono (N : ℕ) [NeZero N] (a : ℤ)
    {ρ δ : ℝ} (h : ρ ≤ δ) : cyclicCutNeighborhood N a ρ ⊆ cyclicCutNeighborhood N a δ := by
  intro x hx
  exact (mem_cyclicCutNeighborhood N a δ x).mpr
    (((mem_cyclicCutNeighborhood N a ρ x).mp hx).trans h)

theorem cyclicWrapExceptional_mono {N : ℕ} [NeZero N] (h : ZMod N)
    {ρ δ : ℝ} (hscale : ρ ≤ δ) : cyclicWrapExceptional h ρ ⊆ cyclicWrapExceptional h δ := by
  have hmul := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  exact Finset.union_subset_union
    (Finset.union_subset_union (cyclicCutNeighborhood_mono N 0 hmul)
      (cyclicCutNeighborhood_mono N N hmul))
    (cyclicCutNeighborhood_mono N ((N - h.val : ℕ) : ℤ) hmul)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

end Erdos3.MultidegreeLieFiltration

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
  (F : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.NilpotentLieFiltration

theorem piRealOrbit_eval_eq_of_log_eq
    {ι σ : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F G : ∀ i, NilpotentLieFiltration (L i) s) {w : σ → ℕ}
    (p : ∀ i, (F i).realification.PolynomialOrbit w)
    (q : ∀ i, (G i).realification.PolynomialOrbit w)
    (hlog : ∀ i, (p i).log = (q i).log) (x : σ → ℤ) :
    (pi F).realification.polynomialOrbitEval w x (piRealOrbit F p) =
      (pi G).realification.polynomialOrbitEval w x (piRealOrbit G q) := by
  apply NilpotentLieBCHGroup.ext
  simp only [polynomialOrbitEval_coord, piRealOrbit, polynomialOrbitOfLog_log]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => congrArg _ (hlog i))

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

theorem pi_basis_eq_of_basis_eq {ι : Type*} [Fintype ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D E : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (h : ∀ i, (D i).basis = (E i).basis) : (pi D).basis = (pi E).basis := by
  change (Pi.basis (fun i => (D i).basis)).reindex (Fintype.equivFin _) =
    (Pi.basis (fun i => (E i).basis)).reindex (Fintype.equivFin _)
  rw [show (fun i => (D i).basis) = (fun i => (E i).basis) from funext h]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι σ : Type*} [Fintype ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {w : σ → ℕ} (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
  (N : ℕ) [NeZero N]

theorem productProjection_cyclicOrbitPoint (x : σ → ZMod N) (i : ι) :
    productProjection D i ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x) =
        (D i).cyclicOrbitPoint (g i) N x :=
  congrArg (fun z : (D i).RealGroup => (QuotientGroup.mk z : (D i).Space))
    (NilpotentLieFiltration.piRealOrbit_eval (fun j => (D j).filtration) g
      (fun j => ((x j).val : ℤ)) i)

variable [DecidableEq ι]

theorem productSpaceEquiv_cyclicOrbitPoint (x : σ → ZMod N) :
    productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x) =
        fun i => (D i).cyclicOrbitPoint (g i) N x :=
  funext (productProjection_cyclicOrbitPoint D g N x)

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem pi_cyclicOrbitPoint_dist_le (x y : σ → ZMod N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    (∀ i, dist ((D i).cyclicOrbitPoint (g i) N x)
      ((D i).cyclicOrbitPoint (g i) N y) ≤ ρ) →
    dist ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x)
      ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y) ≤
          (productMetricBound d : ℝ) * ρ := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro hxy
  have hc : dist
      (productSpaceEquiv D ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x))
      (productSpaceEquiv D ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y)) ≤ ρ := by
    simp only [productSpaceEquiv_cyclicOrbitPoint]
    exact (dist_pi_le_iff hρ).mpr hxy
  have h := (productSpaceEquiv_symm_lipschitz D).dist_le_mul
    (productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x))
    (productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y))
  simp only [Equiv.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left hc (productMetricBound d).coe_nonneg)

theorem pi_cyclicOrbitPoint_dist_le_exp (x y : σ → ZMod N) {p ρ : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) (hρ : 0 ≤ ρ) :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    (∀ i, dist ((D i).cyclicOrbitPoint (g i) N x)
      ((D i).cyclicOrbitPoint (g i) N y) ≤ ρ) →
    dist ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x)
      ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y) ≤
          Real.exp ((p + 4) ^ 4) * ρ := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro hxy
  exact (pi_cyclicOrbitPoint_dist_le D g N x y hρ hxy).trans
    (mul_le_mul_of_nonneg_right (productMetricBound_le_exp d hp hι hd) hρ)

end Erdos3.RationalFilteredNilmanifold

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

end Erdos3

end

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

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

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_refinement (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι I : Type} [Fintype ι] [DecidableEq ι] [Fintype I]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      {degree N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) {p ρ : ℝ},
      s ≤ degree → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      (∀ j, PositiveCyclicNiltest.{0} degree N p (A j)) → (∀ x, ∑ j, A j x = 1) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (I × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (I × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → 0 < A j.1 x) ∧
          (∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
            0 < A j.1 x * A k.1 (x + h)) ∧
          letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
          ∀ j x y, 0 < U j x → 0 < U j y → ∀ i,
            dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
              ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition s a
  let X : Polynomial ℕ := Polynomial.X
  let V := X + (X + Polynomial.C B) ^ B
  let R := V + (V + 2) ^ 2 + 3
  let P := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + P)
  refine ⟨C, hC, ?_⟩
  intro ι I _ _ _ L _ _ _ _ _ _ d D g degree N _ A p ρ hs hp hι hD hcard hA hsum hρ hρinv
  let : FiniteDimensional ℚ (∀ i, L i) := (productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) := realification_moduleTopology_t2 (productFinBasis D)
  obtain ⟨n, hn, hnb, W, hW, hWsum, hWdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [X, V, R, P, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hP : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right hP).trans hcost
  have hPC : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let U : (I × Fin n) → ZMod N → ℝ := fun j x => A j.1 x * W j.2 x
  have hpositive j x (hx : 0 < U j x) : 0 < A j.1 x ∧ 0 < W j.2 x := by
    change 0 < A j.1 x * W j.2 x at hx
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hA j.1).unit_interval x).1]
  have hU j : PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j) :=
    (((hA j.1).mono le_rfl hpt).mul ((hW j.2).mono hs hBt) ht).mono le_rfl hPC
  refine ⟨n, hn, ?_, U, hU, ?_, fun j x hx => (hpositive j x hx).1, ?_, ?_⟩
  · calc
      _ = (Fintype.card I : ℝ) * n := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      _ ≤ Real.exp p * Real.exp ((p + B) ^ B) :=
        mul_le_mul hcard hnb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp t := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr htC
  · intro x
    simp only [U, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hWsum, mul_one]
    exact hsum x
  · intro h j k x hx
    have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
      rcases mul_pos_iff.mp hx with h | h
      · exact h
      · linarith [((hU j).unit_interval x).1]
    exact mul_pos (hpositive j x hpos.1).1 (hpositive k (x + h) hpos.2).1
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    exact hWdiam j.2 x y (hpositive j x hx).2 (hpositive j y hy).2 i

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonPositivePartitionRefinement
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

universe u

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct

theorem prod {ι : Type} [Fintype ι] {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ι → ZMod N → ℝ} (hf : ∀ i, PositiveCyclicNiltest.{u} degree N p (f i))
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) :
    PositiveCyclicNiltest.{u} degree N (productNiltestBudget (raisedNiltestBudget p))
      (fun x => ∏ i, f i x) := by
  classical
  let R := fun i => Classical.choice ((hf i).model_nonempty hp)
  let L := fun i => (R i).L
  let : ∀ i, LieRing (L i) := fun i => (R i).lie
  let : ∀ i, LieAlgebra ℚ (L i) := fun i => (R i).algebra
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i) := fun i => (R i).topology
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i) := fun i => (R i).topologicalAdd
  let : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i) := fun i => (R i).continuousSMul
  let : ∀ i, T2Space (ℝ ⊗[ℚ] L i) := fun i => (R i).hausdorff
  let D := fun i => (R i).model
  let T := fun i => (R i).test
  let : FiniteDimensional ℚ (∀ i, L i) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, L i)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  have hι' : (Fintype.card ι : ℝ) ≤ raisedNiltestBudget p := hι.trans (le_raisedNiltestBudget p)
  let S := RationalFilteredNilmanifold.piNiltest D T hp' hι' (fun i => (R i).complexity)
  refine .of_test (RationalFilteredNilmanifold.pi D) le_rfl S
    (RationalFilteredNilmanifold.piNiltest_unit_interval D T hp' hι'
      (fun i => (R i).complexity) (fun i => (R i).positive))
    (RationalFilteredNilmanifold.piNiltest_complexity D T hp' hι' (fun i => (R i).complexity)) ?_
  intro x
  have he (i : ι) : (T i).eval (fun _ : Unit => (x.val : ℤ)) = (f i x : ℂ) := by
    apply Complex.ext
    · change ((R i).test.evalCyclic N (fun _ : Unit => x)).re = f i x
      exact ((R i).eval x).symm
    · simpa only [Complex.ofReal_im] using ((T i).unit_interval_eval (R i).positive _).1
  change (∏ i, f i x) = ((RationalFilteredNilmanifold.piNiltest D T hp' hι'
    (fun i => (R i).complexity)).eval (fun _ : Unit => (x.val : ℤ))).re
  rw [RationalFilteredNilmanifold.piNiltest_eval]
  simp_rw [he]
  rw [← Complex.ofReal_prod]
  rfl

end Erdos3.PositiveCyclicNiltest

end

section

universe u

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem exists_common_positive_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {I : ι → Type} [∀ i, Fintype (I i)] {degree N : ℕ} [NeZero N]
      (A : ∀ i, I i → ZMod N → ℝ) {p : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (Fintype.card (I i) : ℝ) ≤ Real.exp p) →
      (∀ i j, PositiveCyclicNiltest.{0} degree N p (A i j)) →
      (∀ i x, ∑ j, A i j x = 1) →
      ∃ U : (∀ i, I i) → ZMod N → ℝ,
        (Fintype.card (∀ i, I i) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
        (∀ x, ∑ j, U j x = 1) ∧
        (∀ j x, 0 < U j x → ∀ i, 0 < A i (j i) x) ∧
        ∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
          ∀ i, 0 < A i (j i) x * A i (k i) (x + h) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 2 + 3
  let P := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X ^ 2 + P)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ I _ degree N _ A p hp hι hcard hA hsum
  classical
  have hcost : p ^ 2 + productNiltestBudget (raisedNiltestBudget p) ≤ (p + C) ^ C := by
    simpa [X, R, P, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hP : 0 ≤ productNiltestBudget (raisedNiltestBudget p) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget p) ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (sq_nonneg p)).trans hcost
  have hsquare : p ^ 2 ≤ (p + C) ^ C := (le_add_of_nonneg_right hP).trans hcost
  let U : (∀ i, I i) → ZMod N → ℝ := fun j x => ∏ i, A i (j i) x
  have hU (j : ∀ i, I i) : PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j) :=
    ((PositiveCyclicNiltest.prod (fun i => hA i (j i)) hp hι)).mono le_rfl hproduct
  have hsupport (j : ∀ i, I i) (x : ZMod N) (hx : 0 < U j x) (i : ι) :
      0 < A i (j i) x := by
    have hne : A i (j i) x ≠ 0 := by
      intro hz
      have hzero : U j x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      linarith
    exact lt_of_le_of_ne ((hA i (j i)).unit_interval x).1 (Ne.symm hne)
  refine ⟨U, ?_, hU, ?_, hsupport, ?_⟩
  · rw [Fintype.card_pi, Nat.cast_prod]
    calc
      _ ≤ ∏ _i : ι, Real.exp p :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hcard i)
      _ = Real.exp (Fintype.card ι * p) := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]
      _ ≤ Real.exp (p ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ _ := Real.exp_le_exp.mpr hsquare
  · intro x
    change (∑ j : ∀ i, I i, ∏ i, A i (j i) x) = 1
    rw [← Fintype.prod_sum (fun i (j : I i) => A i j x)]
    simp only [hsum, Finset.prod_const_one]
  · intro h j k x hx i
    have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
      rcases mul_pos_iff.mp hx with h | h
      · exact h
      · linarith [((hU j).unit_interval x).1]
    exact mul_pos (hsupport j x hpos.1 i) (hsupport k (x + h) hpos.2 i)

end Erdos3

end

section

namespace Erdos3

theorem exists_common_positive_partition_refinement (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {I : ι → Type} [∀ i, Fintype (I i)] {degree q N : ℕ} [NeZero q] [NeZero N]
      (A : ∀ i, I i → ZMod N → ℝ) {p ρ : ℝ},
      1 ≤ degree → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (Fintype.card (I i) : ℝ) ≤ Real.exp p) →
      (∀ i j, PositiveCyclicNiltest.{0} degree N p (A i j)) →
      (∀ i x, ∑ j, A i j x = 1) → (q : ℝ) ≤ Real.exp p →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (((∀ i, I i) × ZMod q) × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (((∀ i, I i) × ZMod q) × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} degree N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < U j x → 0 < U j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (∀ j x, 0 < U j x → ∀ i, 0 < A i (j.1.1 i) x) ∧
          ∀ (h : ZMod N) j k x, 0 < U j x * U k (x + h) →
            ∀ i, 0 < A i (j.1.1 i) x * A i (k.1.1 i) (x + h) := by
  obtain ⟨B, _, hcommon⟩ := exists_common_positive_partition
  obtain ⟨R, _, hresidue⟩ := exists_controlled_residue_refinement
  obtain ⟨S, _, hinterval⟩ := exists_interval_refined_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let V := T + (T + Polynomial.C R) ^ R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (V + Polynomial.C S) ^ S)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ I _ degree q N _ _ A p ρ hdegree hp hι hcard hA hsum hq hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  let r := t + (t + R) ^ R
  have htr : t ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := ht.trans htr
  have hRr : (t + R) ^ R ≤ r := le_add_of_nonneg_left ht
  have htotal : r + (r + S) ^ S ≤ (p + C) ^ C := by
    simpa [X, T, V, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hSC : (r + S) ^ S ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans htotal
  obtain ⟨U₀, hcount₀, hU₀, hsum₀, hsupport₀, _⟩ := hcommon A hp hι hcard hA hsum
  obtain ⟨U₁, hcount₁, hU₁, hsum₁, hsupport₁⟩ :=
    hresidue U₀ ht hdegree (hcount₀.trans (Real.exp_le_exp.mpr hBt))
      (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hU₀ j).mono le_rfl hBt) hsum₀
  obtain ⟨n, hn, hcount, U, hU, hUsum, hsupport₂, hcircle, hbad, _⟩ :=
    hinterval U₁ hdegree hr (hcount₁.trans (Real.exp_le_exp.mpr hRr))
      (fun j => (hU₁ j).mono le_rfl hRr) hsum₁ hρ
      (hρinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  have hsupport j x (hx : 0 < U j x) : ∀ i, 0 < A i (j.1.1 i) x :=
    hsupport₀ j.1.1 x (hsupport₁ j.1 x (hsupport₂ j x hx)).1
  refine ⟨n, hn, hcount.trans (Real.exp_le_exp.mpr hSC), U,
    fun j => (hU j).mono le_rfl hSC, hUsum,
    fun j x hx => (hsupport₁ j.1 x (hsupport₂ j x hx)).2,
    hcircle, hbad, hsupport, ?_⟩
  intro h j k x hx i
  have hpos : 0 < U j x ∧ 0 < U k (x + h) := by
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hU j).unit_interval x).1]
  exact mul_pos (hsupport j x hpos.1 i) (hsupport k (x + h) hpos.2 i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OptionComplementCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : Option ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L (some i)))]
  [T2Space (ℝ ⊗[ℚ] (∀ i, L (some i)))]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [LieRing H] [LieAlgebra ℚ H]
  {L : Option ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {r t : ℕ} {d : Option ι → ℕ} (F : NilpotentLieFiltration H r)
  (D : ∀ i, RationalFilteredNilmanifold (L i) t (d i))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (E : RationalFilteredNilmanifold L s d)

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Unit → L))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Unit → L))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Unit → L))] [T2Space (ℝ ⊗[ℚ] (Unit → L))]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type v} {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

namespace RationalFilteredNilmanifold

variable [Fintype ι] [DecidableEq ι] {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

omit [DecidableEq ι] in
theorem optionComplementMap_logHeight
    (i : Fin (Fintype.card (Σ j : {j : Option ι // j ≠ none}, Fin (optionDimension d₀ d j.val))))
    (j : Fin (Fintype.card (Σ i, Fin (d i)))) :
    rationalLogHeight ((pi (optionComplementFactors D₀ D)).basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) = 0 := by
  rw [productFinBasis_repr]
  generalize heq : (Fintype.equivFin
    (Σ j : {j : Option ι // j ≠ none}, Fin (optionDimension d₀ d j.val))).symm i = z
  rcases z with ⟨⟨z, hz⟩, k⟩
  cases z with
  | none => exact False.elim (hz rfl)
  | some a =>
    change Fin (d a) at k
    change rationalLogHeight ((D a).basis.repr (((pi D).basis j) a) k) = 0
    rw [productFinBasis_repr_component D, Basis.repr_self]
    by_cases h : j = Fintype.equivFin (Σ i, Fin (d i)) ⟨a, k⟩ <;> simp [h, rationalLogHeight]

theorem optionComplementMap_piRealOrbit_eval {σ : Type*} {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    realificationMap (hnil := (pi D).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi (optionComplementFactors D₀ D)).filtration.lowerCentralSeries_eq_bot)
      (optionComplementMap (L₀ := L₀))
      ((pi D).filtration.realification.polynomialOrbitEval w x
        (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) g)) =
      (pi (optionComplementFactors D₀ D)).filtration.realification.polynomialOrbitEval w x
        (NilpotentLieFiltration.piRealOrbit
          (fun j => ((optionComplementFactors D₀ D) j).filtration) (optionComplementOrbits D₀ D g)) := by
  apply (realBCHPiEquiv (fun j => ((optionComplementFactors D₀ D) j).filtration)).injective
  funext j
  change productProjectionHom (optionComplementFactors D₀ D) j
      (realificationMap (optionComplementMap (L₀ := L₀)) _) = _
  rw [optionComplementMap, productProjectionHom_realificationMap]
  rcases j with ⟨j, hj⟩
  cases j with
  | none => exact False.elim (hj rfl)
  | some i =>
    exact (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) g x i).trans
      (NilpotentLieFiltration.piRealOrbit_eval
        (fun j => ((optionComplementFactors D₀ D) j).filtration) (optionComplementOrbits D₀ D g) x
        ⟨some i, hj⟩).symm

end RationalFilteredNilmanifold
end Erdos3

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

theorem exists_option_complement_cover :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
      {L₀ : Type u} {L : ι → Type u}
      [LieRing L₀] [LieAlgebra ℚ L₀] [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {s d₀ : ℕ} {d : ι → ℕ}
      (D₀ : RationalFilteredNilmanifold L₀ s d₀)
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)),
      let Z₀ := pi (optionComplementFactors D₀ D)
      ∀ (Λ : Subgroup Z₀.filtration.Group) (n : ℕ) (hn : 0 < n)
        (hin : scaledIntegerGrid n ⊆ bchSubgroupCoordinates Z₀.basis Λ)
        (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid n),
      let V := Z₀.withLattice Λ n hn hin hout
      ∀ {p : ℝ}, 0 ≤ p → (pi D).GeometryComplexityLE p → V.GeometryComplexityLE p →
      ∃ Γ : Subgroup (pi D).filtration.Group,
        Γ ≤ (pi D).lattice ∧ (Γ.subgroupOf (pi D).lattice).Characteristic ∧
        (Γ.subgroupOf (pi D).lattice).Normal ∧ (Γ.subgroupOf (pi D).lattice).FiniteIndex ∧
        (Γ.relIndex (pi D).lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hmin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (pi D).basis Γ)
          (hmout : bchSubgroupCoordinates (pi D).basis Γ ⊆ denominatorGrid m),
          let W := (pi D).withLattice Γ m hm hmin hmout
          W.GeometryComplexityLE ((p + C) ^ C) ∧
          Γ ≤ V.lattice.comap (mapOfSteps (hL := W.filtration.lowerCentralSeries_eq_bot)
            (hM := V.filtration.lowerCentralSeries_eq_bot) (optionComplementMap (L₀ := L₀))) ∧
          ∀ [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))]
            [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
            [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))]
            [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
            [TopologicalSpace (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))]
            [T2Space (ℝ ⊗[ℚ] (∀ j : {j : Option ι // j ≠ none}, optionLieSpace L₀ L j.val))],
          letI := W.metricSpace
          letI := V.metricSpace
          ∀ {σ : Type*} {w : σ → ℕ}
            (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) (x y : σ → ℤ),
            dist (QuotientGroup.mk (Z₀.filtration.realification.polynomialOrbitEval w x
                (piRealOrbit (fun j => ((optionComplementFactors D₀ D) j).filtration)
                  (optionComplementOrbits D₀ D g))) : V.Space)
              (QuotientGroup.mk (Z₀.filtration.realification.polynomialOrbitEval w y
                (piRealOrbit (fun j => ((optionComplementFactors D₀ D) j).filtration)
                  (optionComplementOrbits D₀ D g)))) ≤
                Real.exp ((p + C) ^ C) *
                  dist (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w x
                    (piRealOrbit (fun i => (D i).filtration) g)) : W.Space)
                    (QuotientGroup.mk ((pi D).filtration.realification.polynomialOrbitEval w y
                      (piRealOrbit (fun i => (D i).filtration) g))) := by
  obtain ⟨F, _, hcover⟩ := exists_native_source_cover
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C F) ^ F
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  dsimp only
  intro ι _ _ L₀ L _ _ _ _ s d₀ d D₀ D Λ n hn hin hout p hp hD hV
  let V := (pi (optionComplementFactors D₀ D)).withLattice Λ n hn hin hout
  have hφ (i j) : rationalLogHeight (V.basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) ≤ p := by
    change rationalLogHeight ((pi (optionComplementFactors D₀ D)).basis.repr
      (optionComplementMap (L₀ := L₀) ((pi D).basis j)) i) ≤ p
    rw [optionComplementMap_logHeight]
    exact hp
  obtain ⟨Γ, hΓ, hchar, hnormal, hfinite, hindex, m, hm, hmin, hmout, hW, hmap⟩ :=
    hcover (pi D) V (optionComplementMap (L₀ := L₀)) hp hD hV hφ
  let W := (pi D).withLattice Γ m hm hmin hmout
  let t := p + (p + F) ^ F
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hFt : (p + F) ^ F ≤ t := le_add_of_nonneg_left hp
  have htotal : t + (t + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by nlinarith [sq_nonneg (t + 3)]
  have hmetric : (t + 3) ^ 2 ≤ (p + C) ^ C := by linarith
  refine ⟨Γ, hΓ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr (hFt.trans htC)), m, hm, hmin, hmout,
    hW.mono W (hFt.trans htC), hmap, ?_⟩
  intro _ _ _ _ _ _ _ _
  let := W.metricSpace
  let := V.metricSpace
  intro σ w g x y
  have hh := nativeMap_dist_le W V (optionComplementMap (L₀ := L₀)) hmap ht
    (hW.mono W hFt) (hV.mono V hpt) (fun i j => (hφ i j).trans hpt)
    ((pi D).filtration.realification.polynomialOrbitEval w x
      (piRealOrbit (fun i => (D i).filtration) g))
    ((pi D).filtration.realification.polynomialOrbitEval w y
      (piRealOrbit (fun i => (D i).filtration) g))
  rw [optionComplementMap_piRealOrbit_eval, optionComplementMap_piRealOrbit_eval] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) dist_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem squarePairMap_matrix_logHeight (b : Basis κ ℚ L) (w : κ → ℕ)
    (h : D.filtration.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ w i}))
    {p : ℝ} (hp : 0 ≤ p) (hb : ∀ i j, rationalLogHeight (D.basis.repr (b j) i) ≤ p)
    (i : Fin (Fintype.card (Σ _ : Bool, Fin d)))
    (j : Fin (Fintype.card (κ ⊕ {i // 2 ≤ w i}))) :
    rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
      (D.filtration.squarePairMap (D.filtration.squareFinBasis b w h j)) i) ≤ p + 1 := by
  rw [productFinBasis_repr]
  let z := (Fintype.equivFin (Σ _ : Bool, Fin d)).symm i
  have H := D.filtration.squareFinBasis_projection_height D.basis b w h
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hb i j)) j z.2
  apply rationalLogHeight_le_of_height _ (ceil_exp_le_exp_add_one hp)
  change RationalHeightLE (D.basis.repr
    (D.filtration.squarePairMap (D.filtration.squareFinBasis b w h j) z.1) z.2) _
  cases hz : z.1
  · exact H.2
  · exact H.1

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedCoveredInputPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_prescribed_covered_input_partition (s k₀ a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedCoveredInputPartitionSpec s k₀ a C := by
  obtain ⟨J, _, hsingle⟩ := exists_prescribed_square_image_partition (s + 1) s k₀ a
  obtain ⟨R, _, hcommon⟩ := exists_common_positive_partition_refinement a
  obtain ⟨H, _, hrefine⟩ := exists_fixed_observation_refinement s a
  let X : Polynomial ℕ := Polynomial.X
  let R₀ := X + 2
  let U₀ := R₀ + (R₀ + Polynomial.C J) ^ J + 2
  let V₀ := U₀ + (U₀ + Polynomial.C R) ^ R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V₀ + (V₀ + Polynomial.C H) ^ H)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedCoveredInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout Λ hΛ l hl hlin hlout E g g₀ c q N _ _ p ε
    hp hι hκ hD hV hQ' hb hE hq hε hε1 hεinv
  classical
  let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
  let Z := sumFactors E Q'
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  let := (pi Z).metricSpace
  have hp0 : 0 ≤ p := by linarith
  let r := p + 2
  let u := r + (r + J) ^ J + 2
  let w := u + (u + R) ^ R
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hru : r ≤ u := by
    have hn : 0 ≤ (r + J) ^ J := by positivity
    dsimp [u]
    linarith
  have hJu : (r + J) ^ J ≤ u := by dsimp [u]; linarith
  have hu : 0 ≤ u := hr.trans hru
  have huw : u ≤ w := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hRw : (u + R) ^ R ≤ w := le_add_of_nonneg_left hu
  have hw : 0 ≤ w := hu.trans huw
  have hpu : p ≤ u := hpr.trans hru
  have hpw : p ≤ w := hpu.trans huw
  have hcomplex : (w + H) ^ H ≤ (p + C) ^ C := by
    have hh : w + (w + H) ^ H ≤ (p + C) ^ C := by
      simpa [V₀, U₀, R₀, X, r, u, w, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  let φ := fun i => lieQuotientMap ((D i).filtration.squareFiltration.layerIdeal (s + 1))
  have hpair (i : ι) : ∀ j k, rationalLogHeight ((pi (fun _ : Bool => D i)).basis.repr
      ((D i).filtration.squarePairMap ((V i).basis k)) j) ≤ r := by
    intro j k
    exact ((D i).squarePairMap_matrix_logHeight (b i) (v i) (hF i 2) hp0
      (fun j k => hb i k j) j k).trans (by dsimp [r]; linarith)
  have hφ (i : ι) : ∀ j k, rationalLogHeight ((Q' i).basis.repr (φ i ((V i).basis k)) j) ≤ r := by
    intro j k
    apply rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareFiltration.layerIdeal (s + 1))
        {j | s + 1 ≤ squareFinWeight (v i) j}
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i) (s + 1)) k j)
    simpa only [Nat.cast_one] using Real.one_le_exp hr
  choose δ _ hδε _ n k _ _ hcount A₀ hA₀ hsum₀ _ _ _ hblocks using fun i =>
    hsingle (D i) (V i) (Q' i) (φ i) (g₀ i) (c i) q N (by omega) (hp.trans hpr)
      ((hD i).mono _ hpr) ((hV i).mono _ hpr) ((hQ' i).mono _ hpr) (hpair i) (hφ i)
      (hq.trans (Real.exp_le_exp.mpr hpr)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  obtain ⟨r₀, _, hWcount, A₁, hA₁, hA₁sum, hA₁res, hA₁circle, _, _, hA₁support⟩ :=
    hcommon (q := q) A₀ (by omega) hu (hι.trans hpu)
      (fun i => (hcount i).trans (Real.exp_le_exp.mpr hJu))
      (fun i j => (hA₀ i j).mono le_rfl hJu) hsum₀
      (hq.trans (Real.exp_le_exp.mpr hpu)) hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  obtain ⟨t₁, _, hUcount, A, hA, hAsum, hAsupport, hApairs, hobs⟩ :=
    hrefine E g A₁ (by omega) hw (hκ.trans hpw)
      (fun i => (hE i).mono _ hpw) (hWcount.trans (Real.exp_le_exp.mpr hRw))
      (fun j => (hA₁ j).mono le_rfl hRw) hA₁sum hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I := ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin r₀) × Fin t₁)
  refine ⟨I, inferInstance, hUcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    (fun j => j.1.1.2), fun j => (hA j).mono le_rfl hcomplex, hAsum,
    fun j x hx => hA₁res j.1 x (hAsupport j x hx),
    fun j x y hx hy => hA₁circle j.1 x y (hAsupport j x hx) (hAsupport j y hy), ?_⟩
  let : ∀ i, MetricSpace (Q' i).Space := fun i => (Q' i).metricSpace
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hcell (i : ι) (j b : I) (x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hAx : 0 < A j x * A b (x + h)) (hAy : 0 < A j y * A b (y + h)) :
      dist ((Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => x))
        ((Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => y)) ≤ ε := by
    have hηr (b) : |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((r + 2) ^ k₀) :=
      (hη i b).trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
    have hbound := hblocks i h (branch i) (η i) (γ i) (rSq i) (hγ i) hηr (hnorm i)
      (j.1.1.1 i) (b.1.1.1 i) x y
      (fun hbad => hx (cyclicWrapExceptional_mono h (hδε i) hbad))
      (fun hbad => hy (cyclicWrapExceptional_mono h (hδε i) hbad))
      (hA₁support h j.1 b.1 x (hApairs h j b x hAx) i)
      (hA₁support h j.1 b.1 y (hApairs h j b y hAy) i)
    have hpoint (z : ZMod N) : (Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => z) =
        QuotientGroup.mk (realificationMap
          (hnil := (D i).filtration.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := (Q' i).filtration.lowerCentralSeries_eq_bot) (φ i)
          ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) (rSq i))) := by
      apply (congrArg (fun g => (Q' i).cyclicOrbitPoint g N (fun _ : Unit => z)) (hqSq i)).trans
      exact congrArg (QuotientGroup.mk : (Q' i).RealGroup → (Q' i).Space)
        ((D i).filtration.squareFiltration.realQuotientPolynomialOrbit_eval
          ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)
          (fun _ => (z.val : ℤ)))
    exact (congrArg₂ (fun x y : (Q' i).Space => dist x y) (hpoint x) (hpoint y)).trans_le hbound
  intro j b x y hx hy hAx hAy
  have hpositive (z : ZMod N) (hz : 0 < A j z * A b (z + h)) : 0 < A j z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA j).unit_interval z).1]
  let : ∀ i, MetricSpace (Z i).Space := fun i => (Z i).metricSpace
  have hinputs : ∀ i, dist ((Z i).cyclicOrbitPoint (sumOrbits E Q' g qSq i) N (fun _ : Unit => x))
      ((Z i).cyclicOrbitPoint (sumOrbits E Q' g qSq i) N (fun _ : Unit => y)) ≤ ε := by
    intro i
    cases i with
    | inl i => exact hobs j x y (hpositive x hAx) (hpositive y hAy) i
    | inr i => exact hcell i j b x y hx hy hAx hAy
  have hcountZ : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hZgeom (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ (by linarith)
    | inr i => exact (hQ' i).mono _ (by linarith)
  exact pi_cyclicOrbitPoint_dist_le_exp Z (sumOrbits E Q' g qSq) N
    (fun _ : Unit => x) (fun _ : Unit => y) (by positivity : (0 : ℝ) ≤ 2 * p)
    hcountZ (fun i => (hZgeom i).1) hε.le hinputs

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedComplementInputPartition
namespace OAI

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_prescribed_ambient_input_partition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧ PrescribedAmbientInputPartitionSpec s k₀ a B C := by
  obtain ⟨F, _, hcover⟩ := exists_native_factorwise_covers
  let X : Polynomial ℕ := Polynomial.X
  let T₀ := X + (2 * X + Polynomial.C F) ^ F
  obtain ⟨B, hB, hmetricBudget⟩ := exists_natPolynomial_eval_budget (T₀ + (2 * T₀ + 4) ^ 4)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := exists_prescribed_covered_input_partition s k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T₀ + (T₀ + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedAmbientInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E Γ mΓ hmΓ hinΓ houtΓ g g₀ c q N _ _ p ε
    hp hι hκ hD hV hb hE hmΓb hq hε hε1 hεinv
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  let := W.metricSpace
  have hp0 : 0 ≤ p := by linarith
  have hp2p : p ≤ 2 * p := by linarith
  have hQ (i : ι) : (Q i).GeometryComplexityLE p :=
    (D i).filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _ hp0 (hV i)
  have hZ (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ hp2p
    | inr i => exact (hQ i).mono _ hp2p
  have hcard : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hgeom, _, hsub⟩ :=
    hcover Z Γ mΓ hmΓ hinΓ (by positivity) hcard hZ
      (hmΓb.trans (Real.exp_le_exp.mpr hp2p))
  let E' := fun i => (E i).withLattice (Δ (.inl i)) (l (.inl i)) (hl (.inl i))
    (hlin (.inl i)) (hlout (.inl i))
  let Q' := fun i => (Q i).withLattice (Δ (.inr i)) (l (.inr i)) (hl (.inr i))
    (hlin (.inr i)) (hlout (.inr i))
  let Z' := sumFactors E' Q'
  have hZ' : Z' = fun i => (Z i).withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i) := by
    funext i
    cases i <;> rfl
  have hsub' : (pi Z').lattice ≤ Γ := by
    rw [hZ']
    exact hsub
  have hbase : (pi Z').basis = W.basis :=
    pi_basis_eq_of_basis_eq Z' Z (by intro i; cases i <;> rfl)
  let t := p + (2 * p + F) ^ F
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp0.trans hpt
  have hFt : (2 * p + F) ^ F ≤ t := le_add_of_nonneg_left hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by
    have hh : t + (t + J) ^ J ≤ (p + C) ^ C := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  have hmetric : (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
    have hh : t + (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hmetricBudget p hp0
    linarith
  have hΛ (i : ι) : Δ (.inr i) ≤ (Q i).lattice := (hindex (.inr i)).1
  have hE' (i : κ) : (E' i).GeometryComplexityLE t := (hgeom (.inl i)).mono _ hFt
  have hQ' (i : ι) : (Q' i).GeometryComplexityLE t := (hgeom (.inr i)).mono _ hFt
  obtain ⟨I, inst, hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ :=
    hpartition D b v hF M hM hin hout (fun i => Δ (.inr i)) hΛ
      (fun i => l (.inr i)) (fun i => hl (.inr i))
      (fun i => hlin (.inr i)) (fun i => hlout (.inr i)) E' g g₀ c q N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hD i).mono _ hpt)
      (fun i => (hV i).mono _ hpt) hQ' (fun i j k => (hb i j k).trans hpt)
      hE' (hq.trans (Real.exp_le_exp.mpr hpt)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    label, fun j => (hA j).mono le_rfl hcomplex, hsum, hres, hcircle, ?_⟩
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hηt (i : ι) (j) : |((D i).basis.baseChange ℝ).repr (η i).coord j| ≤
      Real.exp ((t + 2) ^ k₀) :=
    (hη i j).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hglobal := hshifts h branch η γ rSq qSq hγ hηt hnorm hqSq
  let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g qSq)
  let G' := piRealOrbit (fun i => (Z' i).filtration) (sumOrbits E' Q' g qSq)
  let := (pi Z').metricSpace
  have heval (x : Unit → ℤ) :
      (pi Z).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G =
        (pi Z').filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G' :=
    piRealOrbit_eval_eq_of_log_eq (fun i => (Z i).filtration) (fun i => (Z' i).filtration)
      (sumOrbits E Q g qSq) (sumOrbits E' Q' g qSq)
      (by intro i; cases i <;> rfl) x
  have hpoint (x : ZMod N) : W.cyclicOrbitPoint G N (fun _ : Unit => x) =
      (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space) :=
    congrArg (QuotientGroup.mk : W.RealGroup → W.Space) (heval (fun _ => (x.val : ℤ)))
  intro j b x y hx hy hAx hAy
  have hprod := hglobal j b x y hx hy hAx hAy
  have hproject := (sublatticeProjection_lipschitz W (pi Z') hsub' hbase).dist_le_mul
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y))
  change dist (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space)
    (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) G')) ≤
      (1 : ℝ) * dist ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
        ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y)) at hproject
  have hdist := congrArg₂ (dist : W.Space → W.Space → ℝ) (hpoint x) (hpoint y)
  exact ((hdist.le.trans (hproject.trans_eq (one_mul _))).trans hprod).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) hε.le)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

theorem exists_prescribed_complement_input_partition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedComplementInputPartitionSpec s k₀ a B C := by
  obtain ⟨F, _, hcover⟩ := exists_option_complement_cover
  obtain ⟨B₀, _, hpartition⟩ := exists_prescribed_ambient_input_partition s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (2 * X + 2) ^ 2
  let U := T + (T + Polynomial.C F) ^ F
  obtain ⟨B, hB, hmetricBudget⟩ :=
    exists_natPolynomial_eval_budget ((T + Polynomial.C F) ^ F + (U + Polynomial.C B₀) ^ B₀)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedComplementInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ Λ n hn hnin hnout g g₀ c q N _ _ p ε
    hp hι hκ hD hV hb hE htarget hq hε hε1 hεinv
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let Z₀ := pi (optionComplementFactors D₀ Z)
  let W := Z₀.withLattice Λ n hn hnin hnout
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let KC := ∀ j : {j : Option (κ ⊕ ι) // j ≠ none}, optionLieSpace L₀ KL j.val
  let := moduleTopology ℝ (ℝ ⊗[ℚ] KC)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] KC)
  let := realification_moduleTopology_t2 Z₀.basis
  let := W.metricSpace
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  have hp0 : 0 ≤ p := by linarith
  have hp2p : p ≤ 2 * p := by linarith
  have hQ (i : ι) : (Q i).GeometryComplexityLE p :=
    (D i).filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _ hp0 (hV i)
  have hZ (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ hp2p
    | inr i => exact (hQ i).mono _ hp2p
  have hcard : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hprod := pi_geometry Z (p := 2 * p) (by positivity) hcard hZ
  let t := p + (2 * p + 2) ^ 2
  have hpt : p ≤ t := le_add_of_nonneg_right (sq_nonneg _)
  have ht : 0 ≤ t := hp0.trans hpt
  have hprodT : (2 * p + 2) ^ 2 ≤ t := le_add_of_nonneg_left hp0
  obtain ⟨Γ, _, _, _, _, _, l, hl, hlin, hlout, hsource, _, htransfer⟩ :=
    hcover D₀ Z Λ n hn hnin hnout ht (hprod.mono _ hprodT) (htarget.mono W hpt)
  let V := (pi Z).withLattice Γ l hl hlin hlout
  let u := t + (t + F) ^ F
  have htu : t ≤ u := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hpu : p ≤ u := hpt.trans htu
  have hu : 0 ≤ u := hp0.trans hpu
  have hFu : (t + F) ^ F ≤ u := le_add_of_nonneg_left ht
  have hlbound : (l : ℝ) ≤ Real.exp u := hsource.2.1.trans (Real.exp_le_exp.mpr hFu)
  have hcomplex : (u + J) ^ J ≤ (p + C) ^ C := by
    have hh : u + (u + J) ^ J ≤ (p + C) ^ C := by
      simpa [T, U, X, t, u, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  have hmetric : (t + F) ^ F + (u + B₀) ^ B₀ ≤ (p + B) ^ B := by
    simpa [T, U, X, t, u, Polynomial.eval₂_pow] using hmetricBudget p hp0
  obtain ⟨I, inst, hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ :=
    hpartition D b v hF M hM hin hout E Γ l hl hlin hlout g g₀ c q N
      (hp.trans hpu) (hι.trans hpu) (hκ.trans hpu) (fun i => (hD i).mono _ hpu)
      (fun i => (hV i).mono _ hpu) (fun i j k => (hb i j k).trans hpu)
      (fun j => (hE j).mono _ hpu) hlbound (hq.trans (Real.exp_le_exp.mpr hpu))
      hε hε1 (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A, label,
    fun j => (hA j).mono le_rfl hcomplex, hsum, hres, hcircle, ?_⟩
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hηu (i : ι) (j) : |((D i).basis.baseChange ℝ).repr (η i).coord j| ≤
      Real.exp ((u + 2) ^ k₀) :=
    (hη i j).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hglobal := hshifts h branch η γ rSq qSq hγ hηu hnorm hqSq
  let := V.metricSpace
  intro j k x y hx hy hAx hAy
  have hsmall := hglobal j k x y hx hy hAx hAy
  have hmap := htransfer (sumOrbits E Q g qSq)
    (fun _ : Unit => (x.val : ℤ)) (fun _ : Unit => (y.val : ℤ))
  calc
    _ ≤ Real.exp ((t + F) ^ F) *
        dist (V.cyclicOrbitPoint (piRealOrbit (fun i => (Z i).filtration)
          (sumOrbits E Q g qSq)) N (fun _ : Unit => x))
          (V.cyclicOrbitPoint (piRealOrbit (fun i => (Z i).filtration)
            (sumOrbits E Q g qSq)) N (fun _ : Unit => y)) := hmap
    _ ≤ Real.exp ((t + F) ^ F) * (Real.exp ((u + B₀) ^ B₀) * ε) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = Real.exp ((t + F) ^ F + (u + B₀) ^ B₀) * ε := by rw [Real.exp_add, mul_assoc]
    _ ≤ Real.exp ((p + B) ^ B) * ε :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) hε.le

end Erdos3.RationalFilteredNilmanifold

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TrivialPolynomialData
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) : F.PolynomialSlowBound b w T M 1 := by
  intro α i
  change |(b.baseChange ℝ).repr (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT α).le

theorem polynomialRationalGrid_one (q : ℕ) : F.PolynomialRationalGrid b w q 1 := by
  refine ⟨fun _ => 0, ?_⟩
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_zero]
  change (0 : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
    (coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  simp only [map_zero, Finsupp.zero_apply, mul_zero]

theorem piRealOrbit_one {κ : Type*} [Fintype κ] {L : κ → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ}
    (F : ∀ i, NilpotentLieFiltration (L i) s) {σ : Type*} (w : σ → ℕ) :
    piRealOrbit F (fun _ => (1 : (F _).realification.PolynomialOrbit w)) = 1 := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (∑ i, VectorPolynomial.map ((realProductSingle i).restrictScalars ℚ)
    (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L i))) = 0
  simp only [map_zero, Finset.sum_const_zero]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem const_zero_complexity_of {T : D.Niltest w} {p : ℝ} (hT : T.ComplexityLE p) :
    (const D w 0).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
  exact (Real.log_le_log (by norm_num)
    (show (2 : ℝ) ≤ 2 + T.normBound + T.lipBound by
      linarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg])).trans hT.2

theorem const_zero_unit_interval (D : RationalFilteredNilmanifold L s d) (w : σ → ℕ) :
    (const D w 0).UnitIntervalValued := by
  intro x
  simp only [const, Complex.zero_im, Complex.zero_re, le_refl, zero_le_one, and_self]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem selected_refiltered_product_expansion
    {p cost : ℝ} {q r : ℕ} (hbase : RefilteredProductExpansionSpec D a W E Q p q r cost) :
    SelectedRefilteredProductExpansionSpec D a W E Q p q r cost := by
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, hbase⟩ := hbase
  refine ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant Hsh g horbit slow middle rat κ hκ hfactor hslow hrat hcoeff hzero hinput
  let w := fun _ : Unit => 1
  let S' := fun h => if h ∈ Hsh then S h else Niltest.const (D a) w 0
  let g' := fun h i => if h ∈ Hsh then g h i else (1 : (D i).filtration.realification.PolynomialOrbit w)
  let slow' := fun h => if h ∈ Hsh then slow h else 1
  let middle' := fun h => if h ∈ Hsh then middle h else 1
  let rat' := fun h => if h ∈ Hsh then rat h else 1
  let κ' := fun h => if h ∈ Hsh then κ h else 1
  have hS' (h) : (S' h).ComplexityLE p := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hS h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_complexity_of (hS h)
  have hpositive' (h) : (S' h).UnitIntervalValued := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hpositive h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_unit_interval (D a) w
  have hinvariant' (h : ZMod N) (z : (D a).RealGroup)
      (hz : z ∈ (D a).filtration.realification.subgroup (s + 1))
      (hfreqz : ∀ j, realifyFunctional (freq j a) z.coord = 0) (x : (D a).Space) :
      (S' h).observable (z • x) = (S' h).observable x := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hinvariant h z hz hfreqz x
    · simp only [S', hh, ite_false, Niltest.const]
  have horbit' (h) : g' h a = (S' h).orbit := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', S', hh, ite_true] using horbit h hh
    · simp only [g', S', hh, ite_false, Niltest.const]
  have hκ' (h) : κ' h ∈ (pi D).realLattice := by
    by_cases hh : h ∈ Hsh
    · simpa only [κ', hh, ite_true] using hκ h hh
    · simp only [κ', hh, ite_false, Subgroup.one_mem]
  have hfactor' (h) : slow' h * middle' h * rat' h *
      (pi D).filtration.realification.adaptedConstantGroupHom w (κ' h) =
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g' h)).log,
          (piRealOrbit (fun i => (D i).filtration) (g' h)).property⟩⟩ := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', middle', rat', κ', g', hh, ite_true] using hfactor h hh
    · simp only [slow', middle', rat', κ', g', hh, ite_false, map_one, one_mul, piRealOrbit_one]
      rfl
  have hslow' (h) : (pi D).filtration.PolynomialSlowBound (pi D).basis w
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', hh, ite_true] using hslow h hh
    · simpa only [slow', hh, ite_false] using
        (pi D).filtration.polynomialSlowBound_one (pi D).basis w (fun _ => (N : ℝ))
          (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le
  have hrat' (h) : (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [rat', hh, ite_true] using hrat h hh
    · simpa only [rat', hh, ite_false] using
        (pi D).filtration.polynomialRationalGrid_one (pi D).basis w q
  have hcoeff' (h α) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hcoeff h hh α
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈ _
      simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  have hzero' (h) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hzero h hh
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  have hinput' (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hAx : 0 < A i x * B j (x + h)) (hAy : 0 < A i y * B j (y + h)) :
      dist (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
        (fun i : I₀ => g' h i.val)) N (fun _ : Unit => x))
        (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
          (fun i : I₀ => g' h i.val)) N (fun _ : Unit => y)) ≤ K * ρ := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', hh, ite_true] using hinput i j h hh x y hx hy hAx hAy
    · simp only [g', hh, ite_false, piRealOrbit_one]
      change dist (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
        (fun _ : Unit => (x.val : ℤ)) 1) : V.Space)
        (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
          (fun _ : Unit => (y.val : ℤ)) 1)) ≤ K * ρ
      rw [map_one, map_one, dist_self]
      exact mul_nonneg hK hρ.le
  obtain ⟨U, hU, hUc, hUempty, err, heval, hmean⟩ :=
    hbase freq hfreq N A B label hρ hK hA hB hAsum hBsum hres hcircle S' hS' hpositive'
      hinvariant' g' horbit' slow' middle' rat' κ' hκ' hfactor' hslow' hrat' hcoeff' hzero' hinput'
  refine ⟨U, hU, hUc, hUempty, err, ?_, hmean⟩
  intro h hh x
  simpa only [S', hh, ite_true] using heval h x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

theorem prescribed_partition_expansion_from_partition (s r b₀ k₀ a B C B₀ J : ℕ)
    (hpartition : PrescribedComplementInputPartitionSpec (s + 1) k₀ a B₀ J)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      (p + (p + b₀) ^ b₀ + 2) + (p + (p + b₀) ^ b₀ + 2 + J) ^ J ≤ (p + C) ^ C)
    (hmetricBudget : ∀ p : ℝ, 0 ≤ p →
      (p + b₀) ^ b₀ + (p + (p + b₀) ^ b₀ + 2 + B₀) ^ B₀ + 10 ≤ (p + B) ^ B) :
    PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  dsimp only [PrescribedPartitionExpansionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ W dR dQ R Q₀ _ _ _ _ p cost q
    hp hι hκ hD hV hb hE hcost hcostb hbase
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let T := optionFactors D₀ Z
  let H := (pi T).filtration.gradedRefiltrationSubalgebra W
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))
  let I₀ := {i : Option (κ ⊕ ι) // i ≠ none}
  let Z₀ := pi (optionComplementFactors D₀ Z)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q₀.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  have hselected : SelectedRefilteredProductExpansionSpec T none W R Q₀ p q r cost :=
    selected_refiltered_product_expansion T none W R Q₀ hbase
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
      hfinite, hindex, l, hl, hlin, hlout, hV₀, hbase⟩ :=
    hselected
  refine ⟨Q', hQF, hQb, hQle, hQ, ?_⟩
  intro g g₀ c N _ ε hε hε1 hεinv
  let V₀ := Z₀.withLattice Λ l hl hlin hlout
  let := V₀.metricSpace
  let : NeZero P := ⟨Nat.ne_of_gt hP⟩
  let t := p + (p + b₀) ^ b₀ + 2
  have hp0 : 0 ≤ p := by linarith
  have hpt : p ≤ t := by
    dsimp [t]
    have hh : 0 ≤ (p + b₀) ^ b₀ := by positivity
    linarith
  have ht : 0 ≤ t := hp0.trans hpt
  have hcostt : cost + 2 ≤ t := by dsimp [t]; linarith
  have hcostt' : cost ≤ t := by linarith
  have htotal : t + (t + J) ^ J ≤ (p + C) ^ C := by
    exact hbudget p hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by
    have hh : 0 ≤ (t + J) ^ J := by positivity
    linarith
  have hmetric : cost + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
    have hh : (p + b₀) ^ b₀ + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
      exact hmetricBudget p hp0
    linarith
  have hpart := hpartition D b v hF M hM hin hout E D₀ Λ l hl hlin hlout g g₀ c P N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hD i).mono _ hpt)
      (fun i => (hV i).mono _ hpt) (fun i j k => (hb i j k).trans hpt)
      (fun j => (hE j).mono _ hpt) (hV₀.mono V₀ hcostt')
      (hPb.trans (Real.exp_le_exp.mpr hcostt')) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I : Type := Classical.choose hpart
  have hpartI := Classical.choose_spec hpart
  let inst : Fintype I := Classical.choose hpartI
  have hpartInst := Classical.choose_spec hpartI
  obtain ⟨hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ := hpartInst
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    fun i => (hA i).mono le_rfl hcomplex, hsum, hcircle, ?_⟩
  intro J₀ freq hfreq S hS hpositive hinvariant Hsh gT branch η γ rSq qSq
    horbit hother hγ hη hnorm hqSq slow middle rat δ hδ hfactor hslow hrat hcoeff hzero
  have hinput (i j : I) (h : ZMod N) (hh : h ∈ Hsh) (x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hAx : 0 < A i x * A j (x + h)) (hAy : 0 < A i y * A j (y + h)) :
      dist (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
        (fun i : I₀ => gT h i.val)) N (fun _ : Unit => x))
        (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
          (fun i : I₀ => gT h i.val)) N (fun _ : Unit => y)) ≤ Real.exp ((t + B₀) ^ B₀) * ε := by
    have hgo : (fun i : I₀ => gT h i.val) = optionComplementOrbits D₀ Z (sumOrbits E Q g (qSq h)) := by
      funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | none => exact False.elim (hi rfl)
      | some i => exact hother h hh i
    rw [hgo]
    apply hshifts h (branch h) (η h) (γ h) (rSq h) (qSq h) (hγ h hh) _
      (hnorm h hh) (hqSq h hh) i j x y hx hy hAx hAy
    intro i k
    exact (hη h hh i k).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hAnonneg (i x) : 0 ≤ A i x := ((hA i).unit_interval x).1
  have hexp := hbase (J₀ := J₀) freq hfreq N (I := I) (J := I) A A label
    (ρ := ε) (K := Real.exp ((t + B₀) ^ B₀)) hε (Real.exp_pos _).le hAnonneg hAnonneg hsum hsum hres hcircle
      S hS hpositive hinvariant Hsh gT horbit slow middle rat δ hδ hfactor hslow hrat hcoeff hzero hinput
  let U := Classical.choose hexp
  have hUdata := Classical.choose_spec hexp
  obtain ⟨hU, hUc, hUempty, err, heval, hmean⟩ := hUdata
  refine ⟨U, hU, fun i j h => (hUc i j h).mono (hcostt.trans htC), hUempty, err, heval, ?_⟩
  intro h
  have herr := refiltered_expansion_error_budget hcost
    (by positivity : 0 ≤ (t + B₀) ^ B₀) hε.le hmetric
  linarith [hmean h]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FactoredPositiveShiftContradiction
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_prescribed_partition_expansion (s r b₀ : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  obtain ⟨B₀, _, hpartition⟩ := exists_prescribed_complement_input_partition (s + 1)
  let X : Polynomial ℕ := Polynomial.X
  let R₀ := (X + Polynomial.C b₀) ^ b₀
  let T₀ := X + R₀ + 2
  obtain ⟨B, hB, hmetricBudget⟩ :=
    exists_natPolynomial_eval_budget (R₀ + (T₀ + Polynomial.C B₀) ^ B₀ + 10)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T₀ + (T₀ + Polynomial.C J) ^ J)
  refine ⟨C, hC, prescribed_partition_expansion_from_partition s r b₀ k₀ a B C B₀ J hpartition ?_ ?_⟩
  · intro p hp
    simpa [R₀, T₀, X, Polynomial.eval₂_pow] using hbudget p hp
  · intro p hp
    simpa [R₀, T₀, X, Polynomial.eval₂_pow] using hmetricBudget p hp

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

section

universe u v

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

end Erdos3.PositiveShiftBasis

end OAI

end

theorem solution : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_partition_expansion := @OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_partition_expansion
