-- Prove2me | solution 1 for OAI.SignedSweeps.signed_occurrence_moment_bound_proved_ranges
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T00:29:40.049376+00:00
-- url     : https://prove2.me/submissions/2051c42e-0060-4735-8f34-2070085956e1

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

section
-- module OAI.Probability.SignedSweeps.Model
namespace TensorProduct

end TensorProduct

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

end SignedSweeps
end

noncomputable section
namespace SignedSweeps.Partition
open scoped BigOperators TensorProduct
open Module

end SignedSweeps.Partition
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma positive_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsPositive) :
    ∀ r : ℕ, (T ^ r).IsPositive
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hT
  | r + 2 => by
    have h := (positive_pow hT r).adjoint_conj T
    rw [hT.adjoint_eq] at h
    simpa only [← Module.End.mul_eq_comp, ← pow_succ', ← pow_succ] using h

lemma adjoint_mul_positive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) : (positiveSquare T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

lemma sweepSquare_positive {d : ℕ} (lam : Partition (2 ^ d)) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam) := by
  exact adjoint_mul_positive (E := Specht lam) (sweepOperator lam)

lemma sweepSquare_pow_positive {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := Specht lam) (sweepSquare lam ^ r) :=
  positive_pow (sweepSquare_positive lam) r

lemma weightedMoment_nonneg {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    0 ≤ weightedMoment lam r := by
  have h := (sweepSquare_pow_positive lam r).trace_nonneg
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.nonneg_iff.mp h).1

@[simp]
lemma logMoment_zero : logMoment 0 = ⊥ := by simp [logMoment]

lemma logMoment_pos {x : ℝ} (hx : 0 < x) : logMoment x = (Real.log x : EReal) := by
  simp [logMoment, ne_of_gt hx]

lemma logMoment_le_iff {x y : ℝ} (hx : 0 ≤ x) :
    logMoment x ≤ (y : EReal) ↔ x ≤ Real.exp y := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    simp [logMoment, (Real.exp_pos y).le]
  · rw [logMoment_pos h, EReal.coe_le_coe_iff, Real.log_le_iff_le_exp h]

lemma row_part_le_size {n a : ℕ} (lam : Partition n) (ha : a ∈ lam.1.rowLens) : a ≤ n := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  rw [YoungDiagram.rowLen_eq_card]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2

lemma signedEntropy_nonneg {u v : ℕ} (α : Partition u) (β : Partition v) :
    0 ≤ signedEntropy α β := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hp : 0 < a := by
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens _ ha
    · exact β.1.pos_of_mem_rowLens _ ha
  have hs : a ≤ u + v := by
    rcases List.mem_append.mp ha with ha | ha
    · exact (row_part_le_size α ha).trans (Nat.le_add_right _ _)
    · exact (row_part_le_size β ha).trans (Nat.le_add_left _ _)
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  rw [le_div_iff₀ (show (0 : ℝ) < a by exact_mod_cast hp), one_mul]
  exact_mod_cast hs

lemma coefficient_bounds {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    a / 2 ≤ coefficient a d ∧ coefficient a d ≤ a := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt d := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg d), Real.sqrt_nonneg (d : ℝ)]
  have hdiv : 0 ≤ 1 / (2 * Real.sqrt d) := by positivity
  have hdiv' : 1 / (2 * Real.sqrt d) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  constructor <;> unfold coefficient <;> nlinarith

lemma coefficient_nonneg {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ coefficient a d :=
  (div_nonneg ha (by norm_num)).trans (coefficient_bounds ha hd).1

@[simp]
lemma remainderBudget_zero (κ : ℝ) (d : ℕ) : remainderBudget κ d 0 = 0 := by
  simp [remainderBudget]

lemma remainderBudget_nonneg (κ : ℝ) (d l : ℕ) : 0 ≤ remainderBudget κ d l := by
  unfold remainderBudget
  split_ifs <;> simp

lemma spechtRepresentation_norm {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (x : Specht lam) : ‖spechtRepresentation lam g x‖ = ‖x‖ := by
  let x' : (spechtSubrepresentation lam).toSubmodule := x
  change ‖regularIsometry g (x' : RegularSpace n)‖ = ‖(x' : RegularSpace n)‖
  exact (regularIsometry g).norm_map _

lemma finite_average_contraction {I E : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (A : I → E →ₗ[ℂ] E)
    (hA : ∀ i x, ‖A i x‖ ≤ ‖x‖) (x : E) :
    ‖((Fintype.card I : ℂ)⁻¹ • ∑ i, A i) x‖ ≤ ‖x‖ := by
  classical
  have hc : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  calc
    ‖((Fintype.card I : ℂ)⁻¹ • ∑ i, A i) x‖ =
        (Fintype.card I : ℝ)⁻¹ * ‖∑ i, A i x‖ := by
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, norm_smul, norm_inv,
        Complex.norm_natCast]
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, ‖A i x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _ : I, ‖x‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hA i x)) (inv_nonneg.mpr hc.le)
    _ = ‖x‖ := by simp [ne_of_gt hc]

lemma layerOperator_contraction {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d)
    (x : Specht lam) : ‖layerOperator lam i x‖ ≤ ‖x‖ := by
  classical
  apply finite_average_contraction
  intro g y
  exact (spechtRepresentation_norm lam g.1 y).le

lemma list_prod_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E →ₗ[ℂ] E)) (hL : ∀ A ∈ L, ∀ x, ‖A x‖ ≤ ‖x‖) (x : E) :
    ‖L.prod x‖ ≤ ‖x‖ := by
  induction L with
  | nil => simp
  | cons A L ih =>
    simp only [List.prod_cons, Module.End.mul_apply]
    exact (hL A (by simp) _).trans (ih (fun B hB y => hL B (by simp [hB]) y))

lemma sweepOperator_contraction {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam) :
    ‖sweepOperator lam x‖ ≤ ‖x‖ := by
  apply list_prod_contraction
  intro A hA y
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact layerOperator_contraction lam i y

lemma adjoint_contraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (x : E) :
    ‖T.adjoint x‖ ≤ ‖x‖ := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hnorm : ‖T.toContinuousLinearMap‖ ≤ 1 :=
    T.toContinuousLinearMap.opNorm_le_bound (by norm_num) (by simpa using hT)
  calc
    ‖T.adjoint x‖ ≤ ‖T.adjoint.toContinuousLinearMap‖ * ‖x‖ :=
      T.adjoint.toContinuousLinearMap.le_opNorm x
    _ = ‖T.toContinuousLinearMap‖ * ‖x‖ := by
      rw [LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖x‖ := one_mul _

lemma contraction_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) (r : ℕ) (x : E) :
    ‖(T ^ r) x‖ ≤ ‖x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hT _).trans ih

lemma sweepSquare_contraction {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam) :
    ‖sweepSquare lam x‖ ≤ ‖x‖ := by
  change ‖(positiveSquare (sweepOperator lam)) x‖ ≤ ‖x‖
  exact (adjoint_contraction (sweepOperator lam) (sweepOperator_contraction lam) _).trans
    (sweepOperator_contraction lam x)

lemma contraction_trace_le_dim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    (LinearMap.trace ℂ E T).re ≤ finrank ℂ E := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have h : ∀ i, (inner ℂ (b i) (T (b i))).re ≤ 1 := by
    intro i
    calc
      (inner ℂ (b i) (T (b i))).re ≤ ‖inner ℂ (b i) (T (b i))‖ := Complex.re_le_norm _
      _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * ‖b i‖ := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = 1 := by simp only [b.norm_eq_one, one_mul]
  rw [LinearMap.trace_eq_sum_inner T b, Complex.re_sum]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

lemma weightedMoment_le_dimension_squared {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 := by
  unfold weightedMoment
  rw [pow_two]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact contraction_trace_le_dim _ (contraction_pow _ (sweepSquare_contraction lam) r)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.GroupAverage
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def groupAverage {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) : E →ₗ[ℂ] E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

lemma groupAverage_invariant {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    ρ g (groupAverage ρ x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma groupAverage_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : groupAverage ρ x = x := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma groupAverage_idempotent {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) :
    IsIdempotentElem (groupAverage ρ) := by
  ext x
  exact groupAverage_fixed ρ _ (fun g => groupAverage_invariant ρ g x)

lemma representation_inner_inverse {G E : Type*} [Group G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (g : G) (x y : E) :
    inner ℂ (ρ g x) y = inner ℂ x (ρ g⁻¹ y) := by
  let e : E →ₗᵢ[ℂ] E := ⟨ρ g, hρ g⟩
  have he : ρ g (ρ g⁻¹ y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc
    inner ℂ (ρ g x) y = inner ℂ (ρ g x) (ρ g (ρ g⁻¹ y)) := congrArg _ he.symm
    _ = inner ℂ x (ρ g⁻¹ y) := e.inner_map_map x (ρ g⁻¹ y)

lemma groupAverage_symmetric {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) : (groupAverage ρ).IsSymmetric := by
  intro x y
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, inner_smul_left,
    inner_smul_right, inner_sum, sum_inner, map_inv₀, map_natCast]
  congr 1
  simp_rw [representation_inner_inverse ρ hρ]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)

lemma symmetricProjection_norm_eq_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P : E →ₗ[ℂ] E) (hP : P.IsSymmetricProjection) (x : E) :
    ‖P x‖ = ‖x‖ ↔ P x = x := by
  constructor
  · intro he
    have hi : inner ℂ (P x) (x - P x) = 0 := by
      rw [inner_sub_right, ← hP.isSymmetric]
      have hid : P (P x) = P x := congrArg (fun T : E →ₗ[ℂ] E => T x) hP.isIdempotentElem
      rw [hid, sub_self]
    have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) hi
    have hz : ‖x - P x‖ = 0 := by
      rw [add_sub_cancel, he] at hn
      nlinarith [norm_nonneg (x - P x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · rintro h; rw [h]

lemma groupAverage_norm_eq_iff {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (x : E) :
    ‖groupAverage ρ x‖ = ‖x‖ ↔ ∀ g, ρ g x = x := by
  rw [symmetricProjection_norm_eq_iff _ ⟨groupAverage_idempotent ρ, groupAverage_symmetric ρ hρ⟩]
  constructor
  · intro h g
    simpa [h] using groupAverage_invariant ρ g x
  · exact groupAverage_fixed ρ x

lemma layerOperator_symmetricProjection {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) :
    (layerOperator lam i).IsSymmetricProjection := by
  classical
  let ρ := (spechtRepresentation lam).comp (coordinateSubgroup d i).subtype
  exact ⟨groupAverage_idempotent ρ,
    groupAverage_symmetric ρ (fun g => spechtRepresentation_norm lam g.1)⟩

lemma layerOperator_norm_eq_iff {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d)
    (x : Specht lam) : ‖layerOperator lam i x‖ = ‖x‖ ↔
      ∀ g : coordinateSubgroup d i, spechtRepresentation lam g.1 x = x := by
  classical
  let ρ := (spechtRepresentation lam).comp (coordinateSubgroup d i).subtype
  exact groupAverage_norm_eq_iff ρ (fun g => spechtRepresentation_norm lam g.1) x

lemma list_prod_norm_eq_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E →ₗ[ℂ] E))
    (hL : ∀ A ∈ L, ∀ x, ‖A x‖ ≤ ‖x‖ ∧ (‖A x‖ = ‖x‖ → A x = x))
    (x : E) (hn : ‖L.prod x‖ = ‖x‖) : L.prod x = x ∧ ∀ A ∈ L, A x = x := by
  induction L with
  | nil => simp
  | cons A L ih =>
    have ht : ‖L.prod x‖ ≤ ‖x‖ := list_prod_contraction L (fun A hA y => (hL A (by simp [hA]) y).1) x
    have hh := (hL A (by simp) (L.prod x)).1
    rw [List.prod_cons, Module.End.mul_apply] at hn
    have het : ‖L.prod x‖ = ‖x‖ := le_antisymm ht (hn ▸ hh)
    obtain ⟨hprod, htail⟩ := ih (fun A hA => hL A (by simp [hA])) het
    rw [hprod] at hn
    have hAf := (hL A (by simp) x).2 hn
    constructor
    · simpa [List.prod_cons, Module.End.mul_apply, hprod] using hAf
    · intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · exact hAf
      · exact htail B hB

lemma sweep_norm_eq_implies_layer_fixed {d : ℕ} (lam : Partition (2 ^ d))
    (x : Specht lam) (hn : ‖sweepOperator lam x‖ = ‖x‖) :
    ∀ i (g : coordinateSubgroup d i), spechtRepresentation lam g.1 x = x := by
  have hL : ∀ A ∈ (List.ofFn (layerOperator lam)).reverse,
      ∀ x, ‖A x‖ ≤ ‖x‖ ∧ (‖A x‖ = ‖x‖ → A x = x) := by
    intro A hA y
    simp only [List.mem_reverse, List.mem_ofFn] at hA
    obtain ⟨i, rfl⟩ := hA
    exact ⟨layerOperator_contraction lam i y,
      (symmetricProjection_norm_eq_iff _ (layerOperator_symmetricProjection lam i) y).mp⟩
  have hf := (list_prod_norm_eq_fixed _ hL x hn).2
  intro i g
  have hi := hf (layerOperator lam i) (by simp)
  exact (layerOperator_norm_eq_iff lam i x).mp (congrArg norm hi) g

lemma opNorm_lt_one_of_pointwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (hT : ∀ x, x ≠ 0 → ‖T x‖ < ‖x‖) : ‖T.toContinuousLinearMap‖ < 1 := by
  rcases subsingleton_or_nontrivial E with h | h
  · have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero]
  · have hne : (Metric.sphere (0 : E) 1).Nonempty := by
      obtain ⟨x⟩ := NormedSpace.sphere_nonempty_rclike ℂ (E := E) (show (0 : ℝ) ≤ 1 by norm_num)
      exact ⟨x.1, x.2⟩
    obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
      T.toContinuousLinearMap.continuous.norm.continuousOn
    have hnx : ‖x‖ = 1 := by simpa using hx
    have hx0 : x ≠ 0 := by intro hx0; simp [hx0] at hnx
    have ht : ‖T x‖ < 1 := (hT x hx0).trans_eq hnx
    apply lt_of_le_of_lt _ ht
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro y hy
    exact hmax (by simpa using hy)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SwitchGeneration
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma swap_mem_fiberSubgroup {A C : Type*} [DecidableEq A] (f : A → C)
    {x y : A} (hxy : f x = f y) : Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  by_cases hx : z = x
  · subst z; simpa using hxy.symm
  by_cases hy : z = y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma top_of_coordinate_swaps {I A X : Type*} [Fintype I] [Finite X] [DecidableEq I] [DecidableEq X]
    (e : (I → A) ≃ X) (H : Subgroup (Equiv.Perm X))
    (hH : ∀ (i : I) (x : I → A) (a : A),
      Equiv.swap (e x) (e (Function.update x i a)) ∈ H) : H = ⊤ := by
  classical
  have aux : ∀ s : Finset I, ∀ x y : I → A,
      (∀ i, i ∉ s → x i = y i) → Equiv.swap (e x) (e y) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y hxy
      have he : x = y := funext (fun i => hxy i (by simp))
      rw [he, Equiv.swap_self]
      exact H.one_mem
    | @insert i s hi ih =>
      intro x y hxy
      refine SubmonoidClass.swap_mem_trans H (hH i x (y i)) (ih _ y ?_)
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · rw [Function.update_of_ne hji]
        exact hxy j (by simp [hj, hji])
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro g ⟨x, y, _, rfl⟩
  simpa using aux Finset.univ (e.symm x) (e.symm y) (by simp)

lemma coordinateSubgroups_generate (d : ℕ) (H : Subgroup (SymmetricGroup (2 ^ d)))
    (hH : ∀ i, coordinateSubgroup d i ≤ H) : H = ⊤ := by
  classical
  apply top_of_coordinate_swaps (positionsEquiv d) H
  intro i x a
  apply hH i
  apply swap_mem_fiberSubgroup
  funext j
  simp only [Equiv.symm_apply_apply]
  exact (Function.update_of_ne j.2 _ _).symm

def vectorStabilizer {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (x : E) : Subgroup G where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) x = x
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ x = x
    have hh := congrArg (fun y => ρ g⁻¹ y) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

lemma fixed_by_layers_fixed_by_all {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam)
    (hx : ∀ i (g : coordinateSubgroup d i), spechtRepresentation lam g.1 x = x) :
    ∀ g, spechtRepresentation lam g x = x := by
  have ht := coordinateSubgroups_generate d (vectorStabilizer (spechtRepresentation lam) x)
    (fun i g hg => hx i ⟨g, hg⟩)
  intro g
  have hg : g ∈ vectorStabilizer (spechtRepresentation lam) x := ht ▸ Subgroup.mem_top _
  exact hg

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.Invariants
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def complexSign (n : ℕ) : SymmetricGroup n →* ℂ where
  toFun g := (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ)
  map_one' := by simp
  map_mul' g h := by simp

lemma colSubgroup_has_odd {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0) :
    ∃ g : colSubgroup lam, complexSign n g.1 = -1 := by
  classical
  have h0 : (0, 0) ∈ lam.1.cells := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have h1 : (1, 0) ∈ lam.1.cells := YoungDiagram.mem_iff_lt_colLen.mpr hl
  let a := lam.tableau ⟨(0, 0), h0⟩
  let b := lam.tableau ⟨(1, 0), h1⟩
  have hab : a ≠ b := by
    intro he
    have he' := lam.tableau.injective he
    have hc := congrArg (fun c : {c // c ∈ lam.1.cells} => c.1.1) he'
    norm_num at hc
  have hm : Equiv.swap a b ∈ colSubgroup lam := by
    apply swap_mem_fiberSubgroup
    simp [Partition.colOf, a, b]
  refine ⟨⟨Equiv.swap a b, hm⟩, ?_⟩
  simp [complexSign, Equiv.Perm.sign_swap hab]

lemma colSubgroup_sum_sign_eq_zero {n : ℕ} (lam : Partition n)
    (hl : 1 < lam.1.colLen 0) : ∑ g : colSubgroup lam, complexSign n g.1 = 0 := by
  classical
  obtain ⟨g, hg⟩ := colSubgroup_has_odd lam hl
  have hh := Fintype.sum_equiv (Equiv.mulLeft g)
    (fun h => complexSign n (g * h).1) (fun h => complexSign n h.1) (fun _ => rfl)
  simp only [Subgroup.coe_mul, map_mul, hg, ← Finset.mul_sum] at hh
  have htwo : (2 : ℂ) * (∑ h : colSubgroup lam, complexSign n h.1) = 0 := by
    linear_combination -hh
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

def regularSum (n : ℕ) : RegularSpace n →ₗ[ℂ] ℂ where
  toFun f := ∑ g, f g
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

lemma regularSum_single {n : ℕ} (g : SymmetricGroup n) (z : ℂ) :
    regularSum n (EuclideanSpace.single g z) = z := by
  classical
  simp [regularSum, PiLp.single_apply]

lemma regularSum_invariant {n : ℕ} (g : SymmetricGroup n) (f : RegularSpace n) :
    regularSum n (regularRepresentation n g f) = regularSum n f := by
  classical
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun _ => rfl)

lemma polytabloid_sum_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0) :
    regularSum n (polytabloid lam) = 0 := by
  classical
  have he : regularSum n (polytabloid lam) =
      ∑ c : colSubgroup lam, (Fintype.card (rowSubgroup lam) : ℂ) * complexSign n c.1 := by
    simp [polytabloid, regularSum_single, complexSign]
  rw [he, ← Finset.mul_sum, colSubgroup_sum_sign_eq_zero lam hl, mul_zero]

def spechtInclusion {n : ℕ} (lam : Partition n) : Specht lam →ₗ[ℂ] RegularSpace n :=
  (spechtSubrepresentation lam).toSubmodule.subtype

lemma spechtSum_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0)
    (x : Specht lam) : regularSum n (spechtInclusion lam x) = 0 := by
  have hle : (spechtSubrepresentation lam).toSubmodule ≤ (regularSum n).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change regularSum n (regularRepresentation n g (polytabloid lam)) = 0
    rw [regularSum_invariant, polytabloid_sum_eq_zero lam hl]
  exact hle x.property

lemma specht_invariant_eq_zero {n : ℕ} (lam : Partition n) (hl : 1 < lam.1.colLen 0)
    (x : Specht lam) (hx : ∀ g, spechtRepresentation lam g x = x) : x = 0 := by
  classical
  let f : RegularSpace n := spechtInclusion lam x
  have hfixed (g : SymmetricGroup n) : regularRepresentation n g f = f := by
    exact congrArg (spechtInclusion lam) (hx g)
  have hc (g : SymmetricGroup n) : f g = f 1 := by
    have h := congrArg (fun y : RegularSpace n => y 1) (hfixed g⁻¹)
    simpa using h
  have hs := spechtSum_eq_zero lam hl x
  change ∑ g, f g = 0 at hs
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hn : (Fintype.card (SymmetricGroup n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf : f 1 = 0 := (mul_eq_zero.mp hs).resolve_left hn
  have hinj : Function.Injective (spechtInclusion lam) := Subtype.val_injective
  apply hinj
  rw [map_zero]
  change f = 0
  ext g
  exact (hc g).trans hf

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SpectralGap
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma sweepOperator_norm_lt_one {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) : ‖(sweepOperator lam).toContinuousLinearMap‖ < 1 := by
  apply opNorm_lt_one_of_pointwise
  intro x hx
  apply lt_of_le_of_ne (sweepOperator_contraction lam x)
  intro he
  have hf := sweep_norm_eq_implies_layer_fixed lam x he
  exact hx (specht_invariant_eq_zero lam hl x (fixed_by_layers_fixed_by_all lam x hf))

lemma linear_pow_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ[ℂ] E) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ x, ‖T x‖ ≤ c * ‖x‖)
    (r : ℕ) (x : E) : ‖(T ^ r) x‖ ≤ c ^ r * ‖x‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ']
    exact (hT _).trans ((mul_le_mul_of_nonneg_left ih hc).trans_eq (mul_assoc _ _ _).symm)

lemma linear_trace_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) {c : ℝ}
    (hT : ∀ x, ‖T x‖ ≤ c * ‖x‖) :
    (LinearMap.trace ℂ E T).re ≤ (finrank ℂ E : ℝ) * c := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have h : ∀ i, (inner ℂ (b i) (T (b i))).re ≤ c := by
    intro i
    calc
      (inner ℂ (b i) (T (b i))).re ≤ ‖inner ℂ (b i) (T (b i))‖ := Complex.re_le_norm _
      _ ≤ ‖b i‖ * ‖T (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * (c * ‖b i‖) := mul_le_mul_of_nonneg_left (hT _) (norm_nonneg _)
      _ = c := by simp only [b.norm_eq_one, one_mul, mul_one]
  rw [LinearMap.trace_eq_sum_inner T b, Complex.re_sum]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)

lemma positiveSquare_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) :
    ‖(positiveSquare T).toContinuousLinearMap‖ = ‖T.toContinuousLinearMap‖ ^ 2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  change ‖T.adjoint.toContinuousLinearMap.comp T.toContinuousLinearMap‖ = _
  rw [LinearMap.adjoint_toContinuousLinearMap]
  simpa only [pow_two] using ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap

lemma weightedMoment_le_opNorm {d : ℕ} (lam : Partition (2 ^ d)) (r : ℕ) :
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 *
      ‖(sweepOperator lam).toContinuousLinearMap‖ ^ (2 * r) := by
  have hbound (x : Specht lam) : ‖sweepSquare lam x‖ ≤
      (‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2) * ‖x‖ := by
    rw [← positiveSquare_norm (sweepOperator lam)]
    exact (sweepSquare lam).toContinuousLinearMap.le_opNorm x
  have ht := linear_trace_bound (sweepSquare lam ^ r)
    (linear_pow_bound _ (sq_nonneg _) hbound r)
  unfold weightedMoment
  calc
    _ ≤ (spechtDimension lam : ℝ) *
        ((finrank ℂ (Specht lam) : ℝ) * (‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2) ^ r) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ = _ := by rw [← pow_mul]; simp [spechtDimension, pow_two, mul_assoc]

lemma weightedMoment_tendsto_zero {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) :
    Filter.Tendsto (weightedMoment lam) Filter.atTop (nhds 0) := by
  have hsq : ‖(sweepOperator lam).toContinuousLinearMap‖ ^ 2 < 1 := by
    nlinarith [sweepOperator_norm_lt_one lam hl, norm_nonneg (sweepOperator lam).toContinuousLinearMap]
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hsq).const_mul
    ((spechtDimension lam : ℝ) ^ 2)
  simp only [mul_zero, ← pow_mul] at ht
  exact squeeze_zero (weightedMoment_nonneg lam) (weightedMoment_le_opNorm lam) ht

lemma eventually_weightedMoment_le_one {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 1 < lam.1.colLen 0) :
    ∀ᶠ r in Filter.atTop, weightedMoment lam r ≤ 1 :=
  (weightedMoment_tendsto_zero lam hl).eventually_le_const (by norm_num)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BaseCases
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma rowOf_eq_zero {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1)
    (x : Fin n) : lam.rowOf x = 0 := by
  have hc := (lam.tableau.symm x).property
  have hb := YoungDiagram.mem_iff_lt_colLen.mp hc
  have ha := lam.1.colLen_anti 0 (lam.colOf x) (Nat.zero_le _)
  change lam.rowOf x < lam.1.colLen (lam.colOf x) at hb
  omega

lemma rowSubgroup_eq_top {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    rowSubgroup lam = ⊤ := by
  apply top_unique
  intro g _ x
  simp only [rowOf_eq_zero lam hl]

lemma colSubgroup_eq_bot {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    colSubgroup lam = ⊥ := by
  apply bot_unique
  intro g hg
  change g = 1
  apply Equiv.ext
  intro x
  change g x = x
  apply lam.tableau.symm.injective
  apply Subtype.ext
  apply Prod.ext
  · change lam.rowOf (g x) = lam.rowOf x
    rw [rowOf_eq_zero lam hl, rowOf_eq_zero lam hl]
  · exact hg x

def regularOnes (n : ℕ) : RegularSpace n := WithLp.toLp 2 (fun _ => 1)

@[simp]
lemma regularOnes_apply {n : ℕ} (g : SymmetricGroup n) : regularOnes n g = 1 := rfl

lemma regularOnes_ne_zero (n : ℕ) : regularOnes n ≠ 0 := by
  intro he
  have hh := congrArg (fun f : RegularSpace n => f 1) he
  simp at hh

lemma regularOnes_invariant {n : ℕ} (g : SymmetricGroup n) :
    regularRepresentation n g (regularOnes n) = regularOnes n := by
  ext x
  rfl

lemma polytabloid_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    polytabloid lam = regularOnes n := by
  classical
  have : Subsingleton (colSubgroup lam) := by
    rw [colSubgroup_eq_bot lam hl]
    infer_instance
  let : Unique (colSubgroup lam) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  simp only [polytabloid, Fintype.sum_unique]
  rw [(Subsingleton.elim (default : colSubgroup lam) 1)]
  simp only [OneMemClass.coe_one, map_one, Units.val_one, Int.cast_one, one_smul, one_mul]
  have he : (∑ a : rowSubgroup lam, EuclideanSpace.single (a : SymmetricGroup n) (1 : ℂ)) =
      ∑ a : SymmetricGroup n, EuclideanSpace.single a (1 : ℂ) := by
    let e : rowSubgroup lam ≃ SymmetricGroup n :=
      { toFun := Subtype.val
        invFun := fun g => ⟨g, by rw [rowSubgroup_eq_top lam hl]; trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [he]
  ext x
  simp [regularOnes]

lemma spechtSubrepresentation_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    (spechtSubrepresentation lam).toSubmodule = Submodule.span ℂ {regularOnes n} := by
  change Submodule.span ℂ _ = _
  congr 1
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    simp [polytabloid_row lam hl, regularOnes_invariant]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, by simp [hx, polytabloid_row lam hl]⟩

lemma spechtDimension_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1) :
    spechtDimension lam = 1 := by
  change finrank ℂ (spechtSubrepresentation lam).toSubmodule = 1
  rw [spechtSubrepresentation_row lam hl]
  exact finrank_span_singleton (regularOnes_ne_zero n)

lemma spechtRepresentation_row {n : ℕ} (lam : Partition n) (hl : lam.1.colLen 0 ≤ 1)
    (g : SymmetricGroup n) : spechtRepresentation lam g = 1 := by
  ext x
  have hx : spechtInclusion lam x ∈ Submodule.span ℂ {regularOnes n} := by
    rw [← spechtSubrepresentation_row lam hl]
    exact x.property
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  change regularRepresentation n g (spechtInclusion lam x) = spechtInclusion lam x
  rw [← hc, map_smul, regularOnes_invariant]

lemma layerOperator_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1)
    (i : Fin d) : layerOperator lam i = 1 := by
  classical
  ext x
  exact groupAverage_fixed ((spechtRepresentation lam).comp (coordinateSubgroup d i).subtype)
    x (fun g => by simpa using LinearMap.congr_fun (spechtRepresentation_row lam hl g.1) x)

lemma sweepOperator_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1) :
    sweepOperator lam = 1 := by
  have he : layerOperator lam = fun _ => 1 := funext (layerOperator_row lam hl)
  simp [sweepOperator, he, List.ofFn_const]

lemma weightedMoment_row {d : ℕ} (lam : Partition (2 ^ d)) (hl : lam.1.colLen 0 ≤ 1)
    (r : ℕ) : weightedMoment lam r = 1 := by
  simp [weightedMoment, sweepSquare, positiveSquare, sweepOperator_row lam hl,
    LinearMap.trace_one, spechtDimension_row lam hl]
  exact spechtDimension_row lam hl

lemma finite_base_moments (d₀ : ℕ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d ≤ d₀, ∀ lam : Partition (2 ^ d),
      weightedMoment lam r ≤ 1 := by
  let I := Σ d : Fin (d₀ + 1), Partition (2 ^ (d : ℕ))
  have he : ∀ i : I, ∀ᶠ r in Filter.atTop, weightedMoment i.2 r ≤ 1 := by
    intro ⟨d, lam⟩
    by_cases hl : 1 < lam.1.colLen 0
    · exact eventually_weightedMoment_le_one lam hl
    · exact Filter.Eventually.of_forall (fun r => by rw [weightedMoment_row lam (by omega)])
  have hh : ∀ᶠ r in Filter.atTop, ∀ i : I, weightedMoment i.2 r ≤ 1 :=
    Filter.eventually_all.mpr he
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp hh
  refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
  intro r hr d hd lam
  exact hr₀ r ((le_max_right _ _).trans hr) ⟨⟨d, by omega⟩, lam⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BudgetAbsorption
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped Topology
open Filter

lemma nat_two_pow_log (d : ℕ) : Real.log ((2 ^ d : ℕ) : ℝ) = (d : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColumnAnnihilation
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

lemma groupAverage_apply_action {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E) :
    groupAverage ρ (ρ g x) = groupAverage ρ x := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

lemma groupAverage_anti_fixed {G E : Type*} [Group G] [Fintype G]
    [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ G E) (g : G) (x : E)
    (hx : ρ g x = -x) : groupAverage ρ x = 0 := by
  have hh := groupAverage_apply_action ρ g x
  rw [hx, map_neg] at hh
  have hz : (2 : ℂ) • groupAverage ρ x = 0 := by
    rw [two_smul, ← hh]
    exact neg_add_eq_zero.mpr hh.symm
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

lemma regularRepresentation_single {n : ℕ} (g h : SymmetricGroup n) (z : ℂ) :
    regularRepresentation n g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  classical
  ext k
  simp only [regularRepresentation_apply, PiLp.single_apply, inv_mul_eq_iff_eq_mul]

lemma complexSign_mul_self {n : ℕ} (g : SymmetricGroup n) :
    complexSign n g * complexSign n g = 1 := by
  change (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign g : ℤˣ) : ℤ) : ℂ) = 1
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

lemma polytabloid_column_action {n : ℕ} (lam : Partition n) (g : colSubgroup lam) :
    regularRepresentation n g.1 (polytabloid lam) = complexSign n g.1 • polytabloid lam := by
  classical
  change regularRepresentation n g.1 (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
    complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1) = complexSign n g.1 •
    (∑ c : colSubgroup lam, ∑ a : rowSubgroup lam,
      complexSign n c.1 • EuclideanSpace.single (c.1 * a.1) 1)
  simp only [map_sum, map_smul, regularRepresentation_single, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft g)
  intro c
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, smul_smul, ← mul_assoc,
    complexSign_mul_self, one_mul]

lemma long_column_coordinate_pair {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) (g : SymmetricGroup (2 ^ d)) :
    ∃ a b : Fin (2 ^ d), a ≠ b ∧ lam.colOf a = lam.colOf b ∧
      Equiv.swap (g a) (g b) ∈ coordinateSubgroup d i := by
  classical
  let B := {j : Fin d // j ≠ i} → Fin 2
  have hcard : 2 ^ d = 2 * Fintype.card B := by
    simpa [B, Fintype.card_fun] using Fintype.card_congr (Equiv.funSplitAt i (Fin 2))
  let a : Fin (lam.1.colLen 0) → Fin (2 ^ d) := fun c =>
    lam.tableau ⟨(c.1, 0), YoungDiagram.mem_iff_lt_colLen.mpr c.2⟩
  have hai : Function.Injective a := by
    intro c e hce
    have ht := lam.tableau.injective hce
    exact Fin.ext (congrArg (fun c : {c // c ∈ lam.1.cells} => c.1.1) ht)
  let f : Fin (lam.1.colLen 0) → B :=
    fun c j => (positionsEquiv d).symm (g (a c)) j.1
  obtain ⟨c, e, hce, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simp only [Fintype.card_fin]
    omega)
  refine ⟨a c, a e, fun he => hce (hai he), ?_, ?_⟩
  · simp [Partition.colOf, a]
  · apply swap_mem_fiberSubgroup
    exact hfe

lemma regular_layer_annihilates_generator {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) (g : SymmetricGroup (2 ^ d)) :
    groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
      (regularRepresentation (2 ^ d) g (polytabloid lam)) = 0 := by
  classical
  obtain ⟨a, b, hab, hc, hm⟩ := long_column_coordinate_pair lam hl i g
  apply groupAverage_anti_fixed _ ⟨Equiv.swap (g a) (g b), hm⟩
  change regularRepresentation _ (Equiv.swap (g a) (g b))
    (regularRepresentation _ g (polytabloid lam)) = _
  rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_eq_mul_swap]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [map_mul, Module.End.mul_apply]
  have ha := polytabloid_column_action lam ⟨Equiv.swap a b, swap_mem_fiberSubgroup _ hc⟩
  have hs : complexSign _ (Equiv.swap a b) = -1 := by
    simp [complexSign, Equiv.Perm.sign_swap hab]
  rw [ha, hs, neg_one_smul, map_neg]

lemma layerOperator_eq_zero_of_long_column {d : ℕ} (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) (i : Fin d) : layerOperator lam i = 0 := by
  classical
  let A := groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
  have ha : (spechtSubrepresentation lam).toSubmodule ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact regular_layer_annihilates_generator lam hl i g
  ext x
  have hx := ha x.property
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  rw [LinearMap.zero_apply, map_zero]
  change A (spechtInclusion lam x) = 0 at hx
  simp only [layerOperator, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have he (g : coordinateSubgroup d i) : spechtInclusion lam (spechtRepresentation lam g.1 x) =
      regularRepresentation _ g.1 (spechtInclusion lam x) := rfl
  simp only [he]
  simpa only [A, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply] using hx

lemma sweepOperator_eq_zero_of_long_column {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) : sweepOperator lam = 0 := by
  apply List.prod_eq_zero
  have hi := layerOperator_eq_zero_of_long_column lam hl ⟨0, hd⟩
  rw [← hi]
  simp

lemma weightedMoment_eq_zero_of_long_column {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (hl : 2 ^ d / 2 < lam.1.colLen 0) {r : ℕ} (hr : 1 ≤ r) :
    weightedMoment lam r = 0 := by
  simp [weightedMoment, sweepSquare, positiveSquare,
    sweepOperator_eq_zero_of_long_column hd lam hl, zero_pow (by omega : r ≠ 0)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PartitionGeometry
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma polytabloid_right_row {n : ℕ} (lam : Partition n)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    polytabloid lam (g * a.1) = polytabloid lam g := by
  classical
  simp only [polytabloid, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight a)
  intro b
  have h : (g * a.1 = c.1 * (b * a).1) ↔ g = c.1 * b.1 := by
    simp only [Subgroup.coe_mul, ← mul_assoc, mul_left_inj]
  simp only [Equiv.coe_mulRight, PiLp.single_apply, h]

lemma specht_right_row {n : ℕ} (lam : Partition n) (x : Specht lam)
    (a : rowSubgroup lam) (g : SymmetricGroup n) :
    (spechtInclusion lam x) (g * a.1) = (spechtInclusion lam x) g := by
  have haux : ∀ y ∈ (spechtSubrepresentation lam).toSubmodule,
      y (g * a.1) = y g := by
    intro y hy
    change y ∈ Submodule.span ℂ _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      simp only [regularRepresentation_apply, ← mul_assoc]
      exact polytabloid_right_row lam a _
    | zero => rfl
    | add y z _ _ hy hz => simpa only [PiLp.add_apply] using congrArg₂ (· + ·) hy hz
    | smul c y _ hy => simpa only [PiLp.smul_apply] using congrArg (c • ·) hy
  exact haux _ x.property

def OffFirstRow {n : ℕ} (lam : Partition n) := {x : Fin n // lam.rowOf x ≠ 0}

instance offFirstRowFintype {n : ℕ} (lam : Partition n) : Fintype (OffFirstRow lam) := by
  classical
  unfold OffFirstRow
  infer_instance

lemma card_offFirstRow {n : ℕ} (lam : Partition n) :
    Fintype.card (OffFirstRow lam) = n - lam.1.rowLen 0 := by
  classical
  let e : {x : Fin n // lam.rowOf x = 0} ≃ Fin (lam.1.rowLen 0) := {
    toFun := fun x => ⟨lam.colOf x.1, by
      have h := (lam.tableau.symm x.1).property
      have hr := x.property
      change ((lam.tableau.symm x.1).1.1) = 0 at hr
      rw [← Prod.mk.eta (p := (lam.tableau.symm x.1).1), hr] at h
      exact YoungDiagram.mem_iff_lt_rowLen.mp h⟩
    invFun := fun j => ⟨lam.tableau ⟨(0, j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,
      by simp [Partition.rowOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext x.property.symm rfl
    right_inv := by
      intro j
      apply Fin.ext
      simp [Partition.colOf] }
  have he : Fintype.card {x : Fin n // lam.rowOf x = 0} = lam.1.rowLen 0 := by
    simpa using Fintype.card_congr e
  have hs := Fintype.card_subtype_compl (fun x : Fin n => lam.rowOf x = 0)
  simpa only [OffFirstRow, Fintype.card_fin, he] using hs

lemma restrict_offFirstRow_eq {n : ℕ} (lam : Partition n)
    (g h : SymmetricGroup n) (he : ∀ x : OffFirstRow lam, g x.1 = h x.1) :
    g⁻¹ * h ∈ rowSubgroup lam := by
  have hf : ∀ x, lam.rowOf x ≠ 0 → (g⁻¹ * h) x = x := by
    intro x hx
    change g⁻¹ (h x) = x
    rw [← he ⟨x, hx⟩]; simp
  intro x
  by_cases hx : lam.rowOf x = 0
  · by_contra hn
    have hy : lam.rowOf ((g⁻¹ * h) x) ≠ 0 := by simpa only [hx] using hn
    have ht := hf ((g⁻¹ * h) x) hy
    have heq := (g⁻¹ * h).injective ht
    exact hy ((congrArg lam.rowOf heq).trans hx)
  · rw [hf x hx]

lemma spechtDimension_le_pow_level {n : ℕ} (lam : Partition n) :
    spechtDimension lam ≤ n ^ (n - lam.1.rowLen 0) := by
  classical
  let restrict := fun g : SymmetricGroup n => fun x : OffFirstRow lam => g x.1
  let repr := fun f : OffFirstRow lam → Fin n =>
    if h : ∃ g, restrict g = f then Classical.choose h else 1
  have hrepr (g : SymmetricGroup n) : restrict (repr (restrict g)) = restrict g := by
    dsimp only [repr]
    rw [dif_pos (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)]
    exact Classical.choose_spec (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)
  let ev : Specht lam →ₗ[ℂ] ((OffFirstRow lam → Fin n) → ℂ) := {
    toFun := fun x f => (spechtInclusion lam x) (repr f)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro x y hxy
    apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
    apply PiLp.ext
    intro g
    have hx : (spechtInclusion lam x) g = (spechtInclusion lam x) (repr (restrict g)) := by
      let a : rowSubgroup lam := ⟨(repr (restrict g))⁻¹ * g,
        restrict_offFirstRow_eq lam _ _ (fun c => congrFun (hrepr g) c)⟩
      simpa [a] using specht_right_row lam x a (repr (restrict g))
    have hy : (spechtInclusion lam y) g = (spechtInclusion lam y) (repr (restrict g)) := by
      let a : rowSubgroup lam := ⟨(repr (restrict g))⁻¹ * g,
        restrict_offFirstRow_eq lam _ _ (fun c => congrFun (hrepr g) c)⟩
      simpa [a] using specht_right_row lam y a (repr (restrict g))
    rw [hx, hy]
    exact congrFun hxy (restrict g)
  change finrank ℂ (Specht lam) ≤ _
  have h := LinearMap.finrank_le_finrank_of_injective hev
  simpa [Module.finrank_pi, Fintype.card_fun, card_offFirstRow] using h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ColumnSubgroup
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
attribute [local instance] Classical.propDecidable

def oneCardRepresentation (n : ℕ) :
    Representation ℂ (SymmetricGroup n) (Fin n → ℂ) where
  toFun g := {
    toFun := fun f x => f (g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext f x; rfl
  map_mul' := by intros; ext f x; rfl

@[simp]
lemma oneCardRepresentation_apply {n : ℕ} (g : SymmetricGroup n) (f : Fin n → ℂ) (x : Fin n) :
    oneCardRepresentation n g f x = f (g⁻¹ x) := rfl

def binaryFlip (d : ℕ) (i : Fin d) : Equiv.Perm (BinaryPositions d) where
  toFun x := Function.update x i (x i).rev
  invFun x := Function.update x i (x i).rev
  left_inv x := by simp
  right_inv x := by simp

def flipPermutation (d : ℕ) (i : Fin d) : SymmetricGroup (2 ^ d) :=
  (positionsEquiv d).permCongr (binaryFlip d i)

@[simp]
lemma binaryFlip_apply (d : ℕ) (i : Fin d) (x : BinaryPositions d) :
    binaryFlip d i x = Function.update x i (x i).rev := rfl

@[simp]
lemma flipPermutation_inv (d : ℕ) (i : Fin d) :
    (flipPermutation d i)⁻¹ = flipPermutation d i := by
  apply Equiv.ext
  intro x
  rfl

@[simp]
lemma flipPermutation_twice (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    flipPermutation d i (flipPermutation d i x) = x := by
  have h := (flipPermutation d i).symm_apply_apply x
  change (flipPermutation d i)⁻¹ ((flipPermutation d i) x) = x at h
  rwa [flipPermutation_inv] at h

lemma flipPermutation_mem (d : ℕ) (i : Fin d) :
    flipPermutation d i ∈ coordinateSubgroup d i := by
  intro x
  funext j
  simp [flipPermutation, Equiv.permCongr_apply, Function.update_of_ne j.2]

lemma flipPermutation_commute (d : ℕ) (i j : Fin d) :
    Commute (flipPermutation d i) (flipPermutation d j) := by
  change _ * _ = _ * _
  apply Equiv.ext
  intro x
  apply (positionsEquiv d).symm.injective
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, flipPermutation,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  by_cases h : i = j
  · rw [h]
  · simp only [binaryFlip_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
    exact Function.update_comm (Ne.symm h) _ _ _

lemma binary_eq_or_flip {d : ℕ} (i : Fin d) (x y : BinaryPositions d)
    (h : ∀ j, j ≠ i → y j = x j) : y = x ∨ y = binaryFlip d i x := by
  by_cases hi : y i = x i
  · left
    funext j
    exact if hji : j = i then hji ▸ hi else h j hji
  · right
    have hf : y i = (x i).rev := by
      generalize hxi : x i = a at hi ⊢
      generalize hyi : y i = b at hi ⊢
      fin_cases a <;> fin_cases b <;> simp_all
    funext j
    by_cases hji : j = i
    · simpa [hji] using hf
    · simpa [Function.update_of_ne hji] using h j hji

lemma coordinate_or_flip {d : ℕ} (i : Fin d) {g : SymmetricGroup (2 ^ d)}
    (hg : g ∈ coordinateSubgroup d i) (x : Fin (2 ^ d)) :
    g x = x ∨ g x = flipPermutation d i x := by
  have hb := binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm (g x))
    (fun j hj => congrFun (hg x) ⟨j, hj⟩)
  rcases hb with hb | hb
  · exact Or.inl ((positionsEquiv d).symm.injective hb)
  · right
    apply (positionsEquiv d).symm.injective
    simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using hb

lemma oneCard_average_eq {d : ℕ} (i : Fin d) :
    groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) =
      (1 / 2 : ℂ) • (1 + oneCardRepresentation (2 ^ d) (flipPermutation d i)) := by
  classical
  let ρ := (oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype
  let T : (Fin (2 ^ d) → ℂ) →ₗ[ℂ] (Fin (2 ^ d) → ℂ) :=
    (1 / 2 : ℂ) • (1 + oneCardRepresentation (2 ^ d) (flipPermutation d i))
  have hTf (g : coordinateSubgroup d i) (f : Fin (2 ^ d) → ℂ) : ρ g (T f) = T f := by
    ext x
    change (1 / 2 : ℂ) * (f (g.1⁻¹ x) + f ((flipPermutation d i)⁻¹ (g.1⁻¹ x))) =
      (1 / 2 : ℂ) * (f x + f ((flipPermutation d i)⁻¹ x))
    rw [flipPermutation_inv]
    rcases coordinate_or_flip i ((coordinateSubgroup d i).inv_mem g.property) x with hx | hx
    · rw [hx]
    · rw [hx, flipPermutation_twice, add_comm]
  apply LinearMap.ext
  intro f
  funext x
  have hfixed := groupAverage_fixed ρ (T f) (fun g => hTf g f)
  have ha : groupAverage ρ (T f) = groupAverage ρ f := by
    show groupAverage ρ ((1 / 2 : ℂ) • (f + ρ ⟨flipPermutation d i, flipPermutation_mem d i⟩ f)) = _
    rw [map_smul, map_add, groupAverage_apply_action]
    module
  exact congrFun (ha.symm.trans hfixed) x

lemma oneCard_averages_commute {d : ℕ} (i j : Fin d) :
    Commute (groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))
      (groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d j).subtype)) := by
  rw [oneCard_average_eq, oneCard_average_eq]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (Commute.one_left _)
  apply Commute.add_right (Commute.one_right _)
  exact (flipPermutation_commute d i j).map (oneCardRepresentation (2 ^ d))

lemma prod_absorbs_commuting_idempotent {M : Type*} [Monoid M] (L : List M) (P : M)
    (hm : P ∈ L) (hc : ∀ A ∈ L, Commute P A) (hP : IsIdempotentElem P) :
    P * L.prod = L.prod := by
  induction L with
  | nil => simp at hm
  | cons A L ih =>
    simp only [List.prod_cons]
    rcases List.mem_cons.mp hm with h | h
    · rw [← h, ← mul_assoc, hP]
    · calc
        P * (A * L.prod) = A * (P * L.prod) := by rw [← mul_assoc, hc A (by simp), mul_assoc]
        _ = A * L.prod := by rw [ih h (fun B hB => hc B (by simp [hB]))]

def oneCardSweep (d : ℕ) : (Fin (2 ^ d) → ℂ) →ₗ[ℂ] (Fin (2 ^ d) → ℂ) :=
  ((List.ofFn (fun i : Fin d =>
    groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).reverse).prod

lemma oneCardSweep_invariant {d : ℕ} (f : Fin (2 ^ d) → ℂ) (g : SymmetricGroup (2 ^ d)) :
    oneCardRepresentation (2 ^ d) g (oneCardSweep d f) = oneCardSweep d f := by
  have hfixed (i : Fin d) :
      groupAverage ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) *
        oneCardSweep d = oneCardSweep d := by
    unfold oneCardSweep
    apply prod_absorbs_commuting_idempotent _ _ (by
      simp only [List.mem_reverse, List.mem_ofFn]
      exact ⟨i, rfl⟩)
    · intro A hA
      simp only [List.mem_reverse, List.mem_ofFn] at hA
      obtain ⟨j, rfl⟩ := hA
      exact oneCard_averages_commute i j
    · exact groupAverage_idempotent _
  have ht := coordinateSubgroups_generate d
    (vectorStabilizer (oneCardRepresentation (2 ^ d)) (oneCardSweep d f)) (fun i h hh => by
      change oneCardRepresentation (2 ^ d) h (oneCardSweep d f) = oneCardSweep d f
      have hi := congrArg (fun T : _ →ₗ[ℂ] _ => T f) (hfixed i)
      rw [← hi]
      exact groupAverage_invariant
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype) ⟨h, hh⟩ (oneCardSweep d f))
  exact (show g ∈ vectorStabilizer (oneCardRepresentation (2 ^ d)) (oneCardSweep d f) from ht ▸ Subgroup.mem_top _)

lemma oneCard_sum_invariant {n : ℕ} (g : SymmetricGroup n) (f : Fin n → ℂ) :
    ∑ b, oneCardRepresentation n g f b = ∑ b, f b := by
  exact Equiv.sum_comp g⁻¹ f

lemma oneCard_average_sum {n : ℕ} (H : Subgroup (SymmetricGroup n)) (f : Fin n → ℂ) :
    ∑ b, groupAverage ((oneCardRepresentation n).comp H.subtype) f b = ∑ b, f b := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [oneCard_sum_invariant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

lemma oneCardSweep_sum {d : ℕ} (f : Fin (2 ^ d) → ℂ) :
    ∑ b, oneCardSweep d f b = ∑ b, f b := by
  have hp : ∀ L : List (Fin d), ∀ f : Fin (2 ^ d) → ℂ,
      ∑ b, ((L.map (fun i => groupAverage
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).prod f) b =
        ∑ b, f b := by
    intro L
    induction L with
    | nil => simp
    | cons i L ih =>
      intro f
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [oneCard_average_sum, ih]
  simpa [oneCardSweep, List.ofFn_eq_map] using hp (List.finRange d).reverse f

lemma oneCardSweep_uniform {d : ℕ} (f : Fin (2 ^ d) → ℂ) (x : Fin (2 ^ d)) :
    oneCardSweep d f x = (∑ b, f b) / (2 ^ d : ℕ) := by
  have hc (y : Fin (2 ^ d)) : oneCardSweep d f y = oneCardSweep d f x := by
    have h := congrFun (oneCardSweep_invariant f (Equiv.swap x y)) x
    simpa using h
  have hs := oneCardSweep_sum f
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn : (((2 ^ d) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero d (by norm_num : (2 : ℕ) ≠ 0))
  apply (eq_div_iff hn).mpr
  rwa [mul_comm]

def oneCardLift {n : ℕ} (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] RegularSpace n where
  toFun f := WithLp.toLp 2 (fun g => f (g a))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma oneCardLift_intertwines {n : ℕ} (a : Fin n) (f : Fin n → ℂ) (g : SymmetricGroup n) :
    oneCardLift a (oneCardRepresentation n g f) = regularRepresentation n g (oneCardLift a f) := by
  ext h
  rfl

lemma oneCardLift_groupAverage {n : ℕ} (a : Fin n) (f : Fin n → ℂ) (H : Subgroup (SymmetricGroup n)) :
    oneCardLift a (groupAverage ((oneCardRepresentation n).comp H.subtype) f) =
      groupAverage ((regularRepresentation n).comp H.subtype) (oneCardLift a f) := by
  classical
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    MonoidHom.comp_apply, Subgroup.subtype_apply, oneCardLift_intertwines]

lemma spechtInclusion_layer {d : ℕ} (lam : Partition (2 ^ d)) (i : Fin d) (x : Specht lam) :
    spechtInclusion lam (layerOperator lam i x) =
      groupAverage ((regularRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype)
        (spechtInclusion lam x) := by
  classical
  simp only [layerOperator, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  rfl

lemma specht_function_of_one_card {n : ℕ} (lam : Partition n) (hk : n - lam.1.rowLen 0 = 1)
    (x : Specht lam) : ∃ a : Fin n, ∃ f : Fin n → ℂ, spechtInclusion lam x = oneCardLift a f := by
  classical
  have hc : Fintype.card (OffFirstRow lam) = 1 := (card_offFirstRow lam).trans hk
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hc
  let f := fun b : Fin n => spechtInclusion lam x (Equiv.swap a.1 b)
  refine ⟨a.1, f, ?_⟩
  ext g
  let h := Equiv.swap a.1 (g a.1)
  have he (b : OffFirstRow lam) : h b.1 = g b.1 := by
    rw [ha b]
    exact Equiv.swap_apply_left _ _
  let t : rowSubgroup lam := ⟨h⁻¹ * g, restrict_offFirstRow_eq lam h g he⟩
  change spechtInclusion lam x g = spechtInclusion lam x h
  simpa [t] using specht_right_row lam x t h

lemma oneCardLift_sweep {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam)
    {a : Fin (2 ^ d)} {f : Fin (2 ^ d) → ℂ} (hx : spechtInclusion lam x = oneCardLift a f) :
    spechtInclusion lam (sweepOperator lam x) = oneCardLift a (oneCardSweep d f) := by
  have hh : ∀ (L : List (Fin d)) (x : Specht lam) (f : Fin (2 ^ d) → ℂ),
      spechtInclusion lam x = oneCardLift a f →
      spechtInclusion lam ((L.map (layerOperator lam)).prod x) =
      oneCardLift a ((L.map (fun i => groupAverage
        ((oneCardRepresentation (2 ^ d)).comp (coordinateSubgroup d i).subtype))).prod f) := by
    intro L
    induction L with
    | nil => intros; simpa
    | cons i L ih =>
      intro x f hx
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [spechtInclusion_layer, ih x f hx, ← oneCardLift_groupAverage]
  simpa [sweepOperator, oneCardSweep, List.ofFn_eq_map] using hh (List.ofFn (fun i : Fin d => i)).reverse x f hx

lemma sweepOperator_eq_zero_of_level_one {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 1) : sweepOperator lam = 0 := by
  have hl : 1 < lam.1.colLen 0 := by
    by_contra h
    have hc : Fintype.card (OffFirstRow lam) = 1 := (card_offFirstRow lam).trans hk
    obtain ⟨a, _⟩ := Fintype.card_eq_one_iff.mp hc
    exact a.property (rowOf_eq_zero lam (by omega) a.1)
  ext x
  apply specht_invariant_eq_zero lam hl
  intro g
  obtain ⟨a, f, hx⟩ := specht_function_of_one_card lam hk x
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  change regularRepresentation _ g (spechtInclusion lam (sweepOperator lam x)) = _
  rw [oneCardLift_sweep lam x hx, ← oneCardLift_intertwines, oneCardSweep_invariant]

lemma weightedMoment_eq_zero_of_level_one {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 1) {r : ℕ} (hr : 1 ≤ r) :
    weightedMoment lam r = 0 := by
  simp [weightedMoment, sweepSquare, positiveSquare,
    sweepOperator_eq_zero_of_level_one lam hk, zero_pow (by omega : r ≠ 0)]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WeightedGraph
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {A : Type*} [Fintype A] [DecidableEq A]
attribute [local instance] Classical.propDecidable

def edgeEnds (e : A × A) : Finset A := {e.1, e.2}

def matchingVertices (M : Finset (A × A)) : Finset A := M.biUnion edgeEnds

def DisjointEdgeMatching (G : SimpleGraph A) (S : Finset A) (M : Finset (A × A)) : Prop :=
  (∀ e ∈ M, G.Adj e.1 e.2 ∧ e.1 ∈ S ∧ e.2 ∈ S) ∧
    (M : Set (A × A)).PairwiseDisjoint edgeEnds

def neighborUnion (G : SimpleGraph A) (S : Finset A) : Finset A :=
  Finset.univ.filter (fun y => ∃ x ∈ S, G.Adj x y)

omit [Fintype A] [DecidableEq A] in
lemma mem_neighborUnion [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {y : A} :
    y ∈ neighborUnion G S ↔ ∃ x ∈ S, G.Adj x y := by simp [neighborUnion]

omit [Fintype A] [DecidableEq A] in
lemma matching_vertices_sub [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) : matchingVertices M ⊆ S := by
  intro x hx
  obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · exact hx ▸ (hM.1 e he).2.1
  · exact (Finset.mem_singleton.mp hx) ▸ (hM.1 e he).2.2

omit [Fintype A] [DecidableEq A] in
lemma matching_augment [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) {u v : A} (hu : u ∈ S) (hv : v ∈ S)
    (huM : u ∉ matchingVertices M) (hvM : v ∉ matchingVertices M) (huv : G.Adj u v) :
    DisjointEdgeMatching G S (insert (u,v) M) := by
  have hd : Disjoint (edgeEnds (u,v)) (matchingVertices M) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxM
    rcases (show x = u ∨ x = v by simpa [edgeEnds] using hx) with rfl | rfl
    · exact huM hxM
    · exact hvM hxM
  refine ⟨?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨huv, hu, hv⟩
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · have hf : f ∈ M := (Finset.mem_insert.mp hf).resolve_left (Ne.symm hef)
      exact (Finset.disjoint_biUnion_right _ _ _).mp hd f hf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ((Finset.disjoint_biUnion_right _ _ _).mp hd e he).symm
      · exact hM.2 he hf hef

lemma exists_dominating_matching (G : SimpleGraph A) (S : Finset A)
    (hS : ∀ x ∈ S, ∃ y ∈ S, G.Adj x y) :
    ∃ M : Finset (A × A), DisjointEdgeMatching G S M ∧
      S \ matchingVertices M ⊆ neighborUnion G (matchingVertices M) := by
  let F : Finset (Finset (A × A)) := Finset.univ.filter (DisjointEdgeMatching G S)
  have hne : F.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨by simp, by simp [Set.PairwiseDisjoint]⟩
  obtain ⟨M, hMF, hmax⟩ := F.exists_max_image Finset.card hne
  have hM : DisjointEdgeMatching G S M := (Finset.mem_filter.mp hMF).2
  refine ⟨M, hM, ?_⟩
  intro x hx
  obtain ⟨hxS, hxM⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨y, hyS, hxy⟩ := hS x hxS
  have hyM : y ∈ matchingVertices M := by
    by_contra hyM
    have hnew := matching_augment hM hxS hyS hxM hyM hxy
    have hneM : (x,y) ∉ M := by
      intro hxyM
      exact hxM (Finset.mem_biUnion.mpr ⟨(x,y), hxyM, by simp [edgeEnds]⟩)
    have h := hmax (insert (x,y) M) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩)
    rw [Finset.card_insert_of_notMem hneM] at h
    omega
  exact mem_neighborUnion.mpr ⟨y, hyM, hxy.symm⟩

omit [Fintype A] [DecidableEq A] in
lemma matching_weight_factorization [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) (w : A → ℝ) :
    (∏ x ∈ matchingVertices M, w x) = ∏ e ∈ M, (w e.1 * w e.2) := by
  rw [matchingVertices, Finset.prod_biUnion hM.2]
  apply Finset.prod_congr rfl
  intro e he
  have hne : e.1 ≠ e.2 := (hM.1 e he).1.ne
  simp [edgeEnds, hne]

omit [Fintype A] [DecidableEq A] in
lemma matching_vertices_card [Fintype A] [DecidableEq A]
    {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hM : DisjointEdgeMatching G S M) : (matchingVertices M).card = 2 * M.card := by
  rw [matchingVertices, Finset.card_biUnion hM.2]
  simp only [edgeEnds]
  have hc (e : A × A) (he : e ∈ M) : ({e.1, e.2} : Finset A).card = 2 := by
    have hne : e.1 ≠ e.2 := (hM.1 e he).1.ne
    simp [hne]
  rw [Finset.sum_congr rfl hc]
  simp [mul_comm]

lemma neighborUnion_weight_bound (G : SimpleGraph A) (S : Finset A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) {Δ : ℝ}
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    (∑ y ∈ neighborUnion G S, w y) ≤ (S.card : ℝ) * Δ := by
  calc
    _ ≤ ∑ y ∈ neighborUnion G S, ∑ x ∈ S, if G.Adj x y then w y else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_neighborUnion.mp hy
      exact (Finset.single_le_sum (fun z _ => by split_ifs; exact hw _; exact le_refl 0) hx).trans'
        (by simp only [if_pos hxy]; exact le_refl _)
    _ = ∑ x ∈ S, ∑ y ∈ neighborUnion G S, if G.Adj x y then w y else 0 := Finset.sum_comm
    _ ≤ ∑ x ∈ S, ∑ y, if G.Adj x y then w y else 0 := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intros; split_ifs; exact hw _; exact le_refl 0)
    _ ≤ ∑ x ∈ S, Δ := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Finset.sum_filter] using hdeg x
    _ = _ := by simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.WeightedNoIsolates
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finite_sum_le_of_injective {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : I → ℝ) (h : J → ℝ)
    (hg : ∀ i, g i ≤ h (f i)) (hh : ∀ j, 0 ≤ h j) :
    (∑ i, g i) ≤ ∑ j, h j := by
  classical
  calc
    _ ≤ ∑ i, h (f i) := Finset.sum_le_sum (fun i _ => hg i)
    _ = ∑ j ∈ Finset.univ.image f, h j := (Finset.sum_image (fun _ _ _ _ he => hf he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hh j)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

def NoIsolatedVertex (G : SimpleGraph A) (S : Finset A) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, G.Adj x y

def noIsolatesWeight (G : SimpleGraph A) (w : A → ℝ) : ℝ :=
  ∑ S : {S : Finset A // NoIsolatedVertex G S}, ∏ x ∈ S.1, w x

lemma matching_univ {G : SimpleGraph A} {S : Finset A} {M : Finset (A × A)}
    (hm : DisjointEdgeMatching G S M) : DisjointEdgeMatching G Finset.univ M :=
  ⟨fun e he => ⟨(hm.1 e he).1, Finset.mem_univ _, Finset.mem_univ _⟩, hm.2⟩

lemma noIsolatesWeight_le_matching_sum (G : SimpleGraph A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    noIsolatesWeight G w ≤ ∑ M : Finset (A × A),
      if DisjointEdgeMatching G Finset.univ M then
        (∏ e ∈ M, w e.1 * w e.2) *
          ∏ y ∈ neighborUnion G (matchingVertices M), (1 + w y)
      else 0 := by
  classical
  let I := {S : Finset A // NoIsolatedVertex G S}
  let m (S : I) := (exists_dominating_matching G S.1 S.2).choose
  have hm (S : I) := (exists_dominating_matching G S.1 S.2).choose_spec
  let phi (S : I) : Finset (A × A) × Finset A := (m S, S.1 \ matchingVertices (m S))
  have hsub (S : I) : matchingVertices (m S) ⊆ S.1 := matching_vertices_sub (hm S).1
  have hu (S : I) : matchingVertices (phi S).1 ∪ (phi S).2 = S.1 :=
    Finset.union_sdiff_of_subset (hsub S)
  have hinj : Function.Injective phi := by
    intro S T h
    apply Subtype.ext
    rw [← hu S, ← hu T, h]
  let W (z : Finset (A × A) × Finset A) : ℝ :=
    if DisjointEdgeMatching G Finset.univ z.1 ∧ z.2 ⊆ neighborUnion G (matchingVertices z.1) then
      (∏ x ∈ matchingVertices z.1, w x) * ∏ y ∈ z.2, w y
    else 0
  have hW (z) : 0 ≤ W z := by
    dsimp [W]
    split_ifs
    · exact mul_nonneg (Finset.prod_nonneg (fun x _ => hw x)) (Finset.prod_nonneg (fun x _ => hw x))
    · exact le_rfl
  have hp (S : I) : (∏ x ∈ S.1, w x) ≤ W (phi S) := by
    dsimp only [W, phi]
    rw [if_pos ⟨matching_univ (hm S).1, (hm S).2⟩]
    rw [← Finset.prod_union (Finset.disjoint_left.mpr (fun x hx hx' =>
      (Finset.mem_sdiff.mp hx').2 hx))]
    exact le_of_eq (congrArg (fun U : Finset A => ∏ x ∈ U, w x) (hu S).symm)
  have h := finite_sum_le_of_injective phi hinj (fun S => ∏ x ∈ S.1, w x) W hp hW
  change noIsolatesWeight G w ≤ _ at h
  apply h.trans_eq
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro M _
  dsimp only [W]
  by_cases hM : DisjointEdgeMatching G Finset.univ M
  · simp only [hM, true_and, ↓reduceIte]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have he : (Finset.univ.filter (fun T => T ⊆ neighborUnion G (matchingVertices M))) =
        (neighborUnion G (matchingVertices M)).powerset := by ext T; simp
    rw [he, ← Finset.prod_one_add, matching_weight_factorization hM]
  · simp [hM]

omit [Fintype A] [DecidableEq A] in
lemma product_one_add_le_exp_sum [Fintype A] [DecidableEq A]
    (S : Finset A) (w : A → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∏ x ∈ S, (1 + w x)) ≤ Real.exp (∑ x ∈ S, w x) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun x _ => by linarith [hw x])
    (fun x _ => by simpa [add_comm] using Real.add_one_le_exp (w x))

lemma noIsolatesWeight_bound (G : SimpleGraph A) (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) {Δ : ℝ}
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    noIsolatesWeight G w ≤ Real.exp (Real.exp (2 * Δ) * (∑ x, w x) * Δ) := by
  classical
  let eWeight (e : A × A) : ℝ := if G.Adj e.1 e.2 then Real.exp (2 * Δ) * (w e.1 * w e.2) else 0
  have hepos (e) : 0 ≤ eWeight e := by
    dsimp [eWeight]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw _) (hw _))
    · exact le_rfl
  calc
    _ ≤ ∑ M : Finset (A × A), if DisjointEdgeMatching G Finset.univ M then
        (∏ e ∈ M, w e.1 * w e.2) * ∏ y ∈ neighborUnion G (matchingVertices M), (1 + w y)
        else 0 := noIsolatesWeight_le_matching_sum G w hw
    _ ≤ ∑ M : Finset (A × A), ∏ e ∈ M, eWeight e := by
      apply Finset.sum_le_sum
      intro M _
      by_cases hM : DisjointEdgeMatching G Finset.univ M
      · rw [if_pos hM]
        calc
          _ ≤ (∏ e ∈ M, w e.1 * w e.2) *
              Real.exp ((matchingVertices M).card * Δ) := by
            apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun e _ => mul_nonneg (hw _) (hw _)))
            exact (product_one_add_le_exp_sum _ w hw).trans
              (Real.exp_le_exp.mpr (neighborUnion_weight_bound G _ w hw hdeg))
          _ = _ := by
            rw [matching_vertices_card hM]
            rw [Nat.cast_mul, Nat.cast_ofNat]
            have hh : Real.exp ((2 : ℝ) * M.card * Δ) = ∏ e ∈ M, Real.exp (2 * Δ) := by
              rw [← Real.exp_sum]
              simp only [Finset.sum_const, nsmul_eq_mul]
              congr 1
              ring
            rw [hh, ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro e he
            simp only [eWeight, if_pos (hM.1 e he).1]
            ring
      · rw [if_neg hM]
        exact Finset.prod_nonneg (fun e _ => hepos e)
    _ = ∏ e : A × A, (1 + eWeight e) := by
      rw [Finset.prod_one_add]
      have he : (Finset.univ : Finset (A × A)).powerset = Finset.univ := by ext; simp
      rw [he]
    _ ≤ Real.exp (∑ e, eWeight e) := product_one_add_le_exp_sum _ _ hepos
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [Fintype.sum_prod_type]
      calc
        (∑ u, ∑ v, eWeight (u,v)) = Real.exp (2 * Δ) * ∑ u, w u *
            (∑ v ∈ Finset.univ.filter (G.Adj u), w v) := by
          simp only [eWeight, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          split_ifs <;> ring
        _ ≤ Real.exp (2 * Δ) * ∑ u, w u * Δ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hdeg u) (hw u))
        _ = _ := by rw [← Finset.sum_mul]; ring

def fixedNoIsolatesWeight (G : SimpleGraph A) (w : A → ℝ) (k : ℕ) : ℝ :=
  ∑ S : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k}, ∏ x ∈ S.1, w x

omit [Fintype A] [DecidableEq A] in
lemma fixedNoIsolatesWeight_le [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) : fixedNoIsolatesWeight G w k ≤ noIsolatesWeight G w := by
  classical
  let f : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k} →
      {S : Finset A // NoIsolatedVertex G S} := fun S => ⟨S.1, S.2.1⟩
  have hf : Function.Injective f := fun S T h => Subtype.ext (congrArg (fun U : {S : Finset A // NoIsolatedVertex G S} => U.1) h)
  exact finite_sum_le_of_injective f hf _ _ (fun _ => le_rfl)
    (fun S => Finset.prod_nonneg (fun x _ => hw x))

omit [Fintype A] [DecidableEq A] in
lemma fixedNoIsolatesWeight_smul [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (w : A → ℝ) (k : ℕ) (t : ℝ) :
    fixedNoIsolatesWeight G (fun x => t * w x) k = t ^ k * fixedNoIsolatesWeight G w k := by
  classical
  unfold fixedNoIsolatesWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib]
  simp [S.2.2]

lemma weighted_noIsolates_fixed_card (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (∑ x, w x) = k) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ) :
    fixedNoIsolatesWeight G w k ≤ (Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k) := by
  classical
  let t := Real.sqrt Δ
  have ht : 0 < t := Real.sqrt_pos.2 hΔ
  have ht0 := ht.ne'
  have htt : t * t = Δ := Real.mul_self_sqrt hΔ.le
  have ht1 : t ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hΔ1
  have hw' (x) : 0 ≤ w x / t := div_nonneg (hw x) ht.le
  have hdeg' (x) : (∑ y ∈ Finset.univ.filter (G.Adj x), w y / t) ≤ t := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ ht).2
    rw [htt]
    exact hdeg x
  have htotal' : (∑ x, w x / t) = (k : ℝ) / t := by rw [← Finset.sum_div, htotal]
  have hb := (fixedNoIsolatesWeight_le G (fun x => w x / t) k hw').trans
    (noIsolatesWeight_bound G _ hw' hdeg')
  have hh : (fun x => t * (w x / t)) = w := by ext x; field_simp
  calc
    fixedNoIsolatesWeight G w k = t ^ k * fixedNoIsolatesWeight G (fun x => w x / t) k := by
      rw [← fixedNoIsolatesWeight_smul, hh]
    _ ≤ t ^ k * Real.exp (Real.exp (2 * t) * (∑ x, w x / t) * t) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ht.le _)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
      apply Real.exp_le_exp.mpr
      rw [htotal', mul_assoc, div_mul_cancel₀ _ ht0]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg k)

theorem noIsolates_probability_bound (G : SimpleGraph A) (w : A → ℝ) (k : ℕ)
    (μ : Finset A → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hcard : ∀ S, S.card ≠ k → μ S = 0)
    (hw : ∀ x, 0 ≤ w x) (htotal : (∑ x, w x) = k) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hdeg : ∀ x, (∑ y ∈ Finset.univ.filter (G.Adj x), w y) ≤ Δ)
    (hinc : ∀ T, (∑ S : Finset A, if T ⊆ S then μ S else 0) ≤ ∏ x ∈ T, w x) :
    (∑ S : {S : Finset A // NoIsolatedVertex G S}, μ S.1) ≤
      (Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k) := by
  classical
  have hexact (S : Finset A) : μ S ≤ ∏ x ∈ S, w x := by
    apply le_trans _ (hinc S)
    calc
      μ S = if S ⊆ S then μ S else 0 := by simp
      _ ≤ ∑ T : Finset A, if S ⊆ T then μ T else 0 :=
        Finset.single_le_sum (f := fun T => if S ⊆ T then μ T else 0) (fun T _ => by split_ifs; exact hμ T; exact le_rfl) (Finset.mem_univ S)
  have he : (∑ S : {S : Finset A // NoIsolatedVertex G S}, μ S.1) =
      ∑ S : {S : Finset A // NoIsolatedVertex G S ∧ S.card = k}, μ S.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (NoIsolatedVertex G)) (by simp) μ,
      ← Finset.sum_subtype (Finset.univ.filter (fun S => NoIsolatedVertex G S ∧ S.card = k)) (by simp) μ]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hp : NoIsolatedVertex G S <;> by_cases hc : S.card = k <;>
      simp [hp, hc, hcard S]
  rw [he]
  apply le_trans _ (weighted_noIsolates_fixed_card G w k hw htotal hΔ hΔ1 hdeg)
  exact Finset.sum_le_sum (fun S _ => hexact S.1)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EncounterGraph
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def encounterGraph (state : J → Fin d → SymmetricGroup (2 ^ d)) : SimpleGraph (J × Fin (2 ^ d)) where
  Adj v w := v ≠ w ∧ ∃ i : Fin d,
    state w.1 i w.2 = state v.1 i v.2 ∨
    state w.1 i w.2 = flipPermutation d i (state v.1 i v.2)
  symm := ⟨by
    rintro v w ⟨hvw, i, hi⟩
    refine ⟨hvw.symm, i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl hi.symm
    · exact Or.inr (by rw [hi, flipPermutation_twice])⟩
  loopless := ⟨by rintro v ⟨hvv, _⟩; exact hvv rfl⟩

def encounterCandidate (state : J → Fin d → SymmetricGroup (2 ^ d))
    (v : J × Fin (2 ^ d)) (a : Fin d × J × Fin 2) : J × Fin (2 ^ d) :=
  (a.2.1, (state a.2.1 a.1).symm
    (if a.2.2 = 0 then state v.1 a.1 v.2 else flipPermutation d a.1 (state v.1 a.1 v.2)))

lemma encounter_neighbor_cover (state : J → Fin d → SymmetricGroup (2 ^ d)) (v : J × Fin (2 ^ d)) :
    Finset.univ.filter ((encounterGraph state).Adj v) ⊆
      Finset.univ.image (encounterCandidate state v) := by
  classical
  intro w hw
  obtain ⟨_, i, hi⟩ := (Finset.mem_filter.mp hw).2
  rcases hi with hi | hi
  · refine Finset.mem_image.mpr ⟨(i, w.1, 0), Finset.mem_univ _, ?_⟩
    simp only [encounterCandidate, ↓reduceIte]
    rw [← hi, Equiv.symm_apply_apply]
  · refine Finset.mem_image.mpr ⟨(i, w.1, 1), Finset.mem_univ _, ?_⟩
    simp only [encounterCandidate, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]
    rw [← hi, Equiv.symm_apply_apply]

lemma encounter_weighted_degree (state : J → Fin d → SymmetricGroup (2 ^ d))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (v : J × Fin (2 ^ d)) :
    (∑ w ∈ Finset.univ.filter ((encounterGraph state).Adj v), p w.1) ≤
      2 * d * ∑ j, p j := by
  classical
  calc
    _ ≤ ∑ w ∈ Finset.univ.image (encounterCandidate state v), p w.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (encounter_neighbor_cover state v) (fun w _ _ => hp w.1)
    _ ≤ ∑ a : Fin d × J × Fin 2, p (encounterCandidate state v a).1 :=
      Finset.sum_image_le_of_nonneg (fun w _ => hp w.1)
    _ = _ := by
      simp only [Fintype.sum_prod_type, encounterCandidate, Fin.sum_univ_two]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

omit [DecidableEq J] in
lemma network_weights_total [DecidableEq J] (p : J → ℝ) :
    (∑ w : J × Fin (2 ^ d), p w.1) = (2 ^ d : ℕ) * ∑ j, p j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]

theorem network_noIsolates_probability_bound
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (k : ℕ)
    (hmass : (2 ^ d : ℕ) * ∑ j, p j = k)
    (μ : Finset (J × Fin (2 ^ d)) → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hcard : ∀ S, S.card ≠ k → μ S = 0)
    (hinc : ∀ T, (∑ S : Finset (J × Fin (2 ^ d)), if T ⊆ S then μ S else 0) ≤ ∏ w ∈ T, p w.1)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ)) (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    (∑ S : {S : Finset (J × Fin (2 ^ d)) // NoIsolatedVertex (encounterGraph state) S}, μ S.1) ≤
      (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  have hn : (2 ^ d : ℕ) ≠ 0 := ne_of_gt (pow_pos (by omega : 0 < (2 : ℕ)) _)
  have hmass' : (∑ j, p j) = (k : ℝ) / (2 ^ d : ℕ) :=
    (eq_div_iff (by exact_mod_cast hn)).2 (by rwa [mul_comm])
  apply noIsolates_probability_bound (encounterGraph state) (fun w => p w.1) k
    μ hμ hcard (fun w => hp w.1) (by rw [network_weights_total, hmass]) hΔ hΔ1 _ hinc
  intro v
  have h := encounter_weighted_degree state p hp v
  rwa [hmass', ← mul_div_assoc] at h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SubsetInclusion
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
variable {A : Type*} [DecidableEq A]

def fairSwapWeights (a b : A) (p : A → ℝ) (x : A) : ℝ :=
  (p x + p (Equiv.swap a b x)) / 2

lemma fairSwapWeights_nonneg (a b : A) {p : A → ℝ} (hp : ∀ x, 0 ≤ p x) (x : A) :
    0 ≤ fairSwapWeights a b p x := by
  exact div_nonneg (add_nonneg (hp x) (hp _)) (by norm_num)

lemma fairSwapWeights_fixed (a b : A) (p : A → ℝ) {x : A} (ha : x ≠ a) (hb : x ≠ b) :
    fairSwapWeights a b p x = p x := by
  simp only [fairSwapWeights, Equiv.swap_apply_of_ne_of_ne ha hb]
  ring

lemma fairSwapWeights_left (a b : A) (p : A → ℝ) :
    fairSwapWeights a b p a = (p a + p b) / 2 := by
  simp [fairSwapWeights]

lemma fairSwapWeights_right (a b : A) (p : A → ℝ) :
    fairSwapWeights a b p b = (p a + p b) / 2 := by
  simp only [fairSwapWeights, Equiv.swap_apply_right, add_comm]

lemma prod_swap_fixed (a b : A) (p : A → ℝ) (T : Finset A) (ha : a ∉ T) (hb : b ∉ T) :
    (∏ x ∈ T, p (Equiv.swap a b x)) = ∏ x ∈ T, p x := by
  apply Finset.prod_congr rfl
  intro x hx
  rw [Equiv.swap_apply_of_ne_of_ne (by rintro rfl; exact ha hx)
    (by rintro rfl; exact hb hx)]

lemma prod_fairSwapWeights_fixed (a b : A) (p : A → ℝ) (T : Finset A)
    (ha : a ∉ T) (hb : b ∉ T) :
    (∏ x ∈ T, fairSwapWeights a b p x) = ∏ x ∈ T, p x := by
  apply Finset.prod_congr rfl
  intro x hx
  exact fairSwapWeights_fixed a b p (fun h => ha (h ▸ hx)) (fun h => hb (h ▸ hx))

lemma fair_swap_product_le (a b : A) (p : A → ℝ) (hp : ∀ x, 0 ≤ p x) (T : Finset A) :
    ((∏ x ∈ T, p x) + (∏ x ∈ T, p (Equiv.swap a b x))) / 2 ≤
      ∏ x ∈ T, fairSwapWeights a b p x := by
  by_cases hab : a = b
  · subst b
    have he : fairSwapWeights a a p = p := by funext x; simp [fairSwapWeights]
    simp only [he, Equiv.swap_self, Equiv.refl_apply]
    linarith
  have hs (T : Finset A) (ha : a ∈ T) (hb : b ∉ T) :
      ((∏ x ∈ T, p x) + (∏ x ∈ T, p (Equiv.swap a b x))) / 2 =
        ∏ x ∈ T, fairSwapWeights a b p x := by
    rw [← T.mul_prod_erase p ha, ← T.mul_prod_erase (fun x => p (Equiv.swap a b x)) ha,
      ← T.mul_prod_erase (fairSwapWeights a b p) ha]
    rw [prod_swap_fixed a b p (T.erase a) (by simp) (by simp [hb]),
      prod_fairSwapWeights_fixed a b p (T.erase a) (by simp) (by simp [hb]),
      fairSwapWeights_left, Equiv.swap_apply_left]
    ring
  by_cases ha : a ∈ T
  · by_cases hb : b ∈ T
    · have hb' : b ∈ T.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
      have he (f : A → ℝ) : (∏ x ∈ T, f x) =
          f a * (f b * ∏ x ∈ (T.erase a).erase b, f x) := by
        rw [← T.mul_prod_erase f ha, ← (T.erase a).mul_prod_erase f hb']
      rw [he p, he (fun x => p (Equiv.swap a b x)), he (fairSwapWeights a b p),
        prod_swap_fixed a b p ((T.erase a).erase b) (by simp) (by simp),
        prod_fairSwapWeights_fixed a b p ((T.erase a).erase b) (by simp) (by simp),
        fairSwapWeights_left, fairSwapWeights_right, Equiv.swap_apply_left, Equiv.swap_apply_right]
      have hr := Finset.prod_nonneg (s := (T.erase a).erase b) (f := p) (fun x _ => hp x)
      nlinarith [mul_nonneg (sq_nonneg (p a - p b)) hr]
    · exact (hs T ha hb).le
  · by_cases hb : b ∈ T
    · have hs' := hs (T.image (Equiv.swap a b))
      have hi : a ∈ T.image (Equiv.swap a b) := Finset.mem_image.mpr ⟨b, hb, Equiv.swap_apply_right a b⟩
      have hn : b ∉ T.image (Equiv.swap a b) := by
        intro ht
        obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
        have hx' : x = a := (Equiv.swap a b).injective (he.trans (Equiv.swap_apply_left a b).symm)
        exact ha (hx' ▸ hx)
      have he := hs' hi hn
      rw [Finset.prod_image (Equiv.swap a b).injective.injOn,
        Finset.prod_image (Equiv.swap a b).injective.injOn,
        Finset.prod_image (Equiv.swap a b).injective.injOn] at he
      simp only [Equiv.swap_apply_self] at he
      have hweights (x : A) : fairSwapWeights a b p (Equiv.swap a b x) =
          fairSwapWeights a b p x := by simp [fairSwapWeights, add_comm]
      simp only [hweights] at he
      linarith [he]
    · rw [prod_swap_fixed a b p T ha hb, prod_fairSwapWeights_fixed a b p T ha hb]
      linarith

def fairSwapInclusion (a b : A) (M : Finset A → ℝ) (T : Finset A) : ℝ :=
  (M T + M (T.image (Equiv.swap a b))) / 2

lemma fairSwapInclusion_bound (a b : A) (M : Finset A → ℝ) (p : A → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) (T : Finset A) :
    fairSwapInclusion a b M T ≤ ∏ x ∈ T, fairSwapWeights a b p x := by
  calc
    _ ≤ ((∏ x ∈ T, p x) + ∏ x ∈ T.image (Equiv.swap a b), p x) / 2 := by
      exact div_le_div_of_nonneg_right (add_le_add (hM T) (hM _)) (by norm_num)
    _ = ((∏ x ∈ T, p x) + ∏ x ∈ T, p (Equiv.swap a b x)) / 2 := by
      rw [Finset.prod_image (Equiv.swap a b).injective.injOn]
    _ ≤ _ := fair_swap_product_le a b p hp T

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SwitchAverages
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℝ E]

def realGroupAverage (ρ : Representation ℝ G E) : E →ₗ[ℝ] E :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g, ρ g

lemma realGroupAverage_fixed (ρ : Representation ℝ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : realGroupAverage ρ x = x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma realGroupAverage_apply_action (ρ : Representation ℝ G E) (g : G) (x : E) :
    realGroupAverage ρ (ρ g x) = realGroupAverage ρ x := by
  classical
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℝ E]

def fairAction (ρ : Representation ℝ G E) (g : G) : E →ₗ[ℝ] E :=
  (1 / 2 : ℝ) • (1 + ρ g)

lemma fairAction_apply (ρ : Representation ℝ G E) (g : G) (x : E) :
    fairAction ρ g x = (1 / 2 : ℝ) • (x + ρ g x) := rfl

lemma action_absorbs_fairAction (ρ : Representation ℝ G E) (g : G) (hg : g * g = 1) :
    ρ g * fairAction ρ g = fairAction ρ g := by
  ext x
  have hh : ρ g (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, hg, map_one, Module.End.one_apply]
  simp only [Module.End.mul_apply, fairAction_apply, map_smul, map_add, hh, add_comm]

lemma fairAction_idempotent (ρ : Representation ℝ G E) (g : G) (hg : g * g = 1) :
    IsIdempotentElem (fairAction ρ g) := by
  have he := action_absorbs_fairAction ρ g hg
  change fairAction ρ g * fairAction ρ g = fairAction ρ g
  conv_lhs => lhs; unfold fairAction
  rw [smul_mul_assoc, add_mul, one_mul, he]
  ext x
  simp only [LinearMap.smul_apply, LinearMap.add_apply]
  module

lemma fairActions_commute (ρ : Representation ℝ G E) {g h : G} (hgh : Commute g h) :
    Commute (fairAction ρ g) (fairAction ρ h) := by
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (Commute.one_left _)
  apply Commute.add_right (Commute.one_right _)
  exact hgh.map ρ

def realVectorStabilizer (ρ : Representation ℝ G E) (x : E) : Subgroup G where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) x = x
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ x = x
    have hh := congrArg (fun y => ρ g⁻¹ y) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

lemma fairAction_prod_fixed (ρ : Representation ℝ G E) (L : List G)
    (hL : ∀ g ∈ L, g * g = 1) (hcomm : ∀ g ∈ L, ∀ h ∈ L, Commute g h)
    {g : G} (hg : g ∈ L) :
    ρ g * (L.map (fairAction ρ)).prod = (L.map (fairAction ρ)).prod := by
  have hf : fairAction ρ g * (L.map (fairAction ρ)).prod = (L.map (fairAction ρ)).prod := by
    apply prod_absorbs_commuting_idempotent
    · exact List.mem_map.mpr ⟨g, hg, rfl⟩
    · intro A hA
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hA
      exact fairActions_commute ρ (hcomm g hg h hh)
    · exact fairAction_idempotent ρ g (hL g hg)
  rw [← hf, ← mul_assoc, action_absorbs_fairAction ρ g (hL g hg)]

lemma realGroupAverage_fairAction [Fintype G] (ρ : Representation ℝ G E) (g : G) (x : E) :
    realGroupAverage ρ (fairAction ρ g x) = realGroupAverage ρ x := by
  rw [fairAction_apply, map_smul, map_add, realGroupAverage_apply_action]
  module

lemma realGroupAverage_eq_fairAction_prod [Fintype G] (ρ : Representation ℝ G E) (L : List G)
    (hL : ∀ g ∈ L, g * g = 1) (hcomm : ∀ g ∈ L, ∀ h ∈ L, Commute g h)
    (hgen : ∀ H : Subgroup G, (∀ g ∈ L, g ∈ H) → H = ⊤) :
    realGroupAverage ρ = (L.map (fairAction ρ)).prod := by
  have ha (L : List G) (x : E) :
      realGroupAverage ρ ((L.map (fairAction ρ)).prod x) = realGroupAverage ρ x := by
    induction L with
    | nil => simp
    | cons g L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [realGroupAverage_fairAction, ih]
  ext x
  rw [← ha L x]
  apply realGroupAverage_fixed
  have hg := hgen (realVectorStabilizer ρ ((L.map (fairAction ρ)).prod x)) (by
    intro g hg
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) (fairAction_prod_fixed ρ L hL hcomm hg))
  intro g
  exact (show g ∈ realVectorStabilizer ρ ((L.map (fairAction ρ)).prod x) from hg ▸ Subgroup.mem_top _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A C : Type*} [Fintype A] [DecidableEq A]

lemma fiberSubgroup_le_of_swaps (f : A → C) (H : Subgroup (Equiv.Perm A))
    (hH : ∀ a b, f a = f b → Equiv.swap a b ∈ H) : fiberSubgroup f ≤ H := by
  intro g hg
  have haux : ∀ n : ℕ, ∀ g : Equiv.Perm A, g.support.card = n → g ∈ fiberSubgroup f → g ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hn hg
      by_cases he : g = 1
      · subst g; exact H.one_mem
      obtain ⟨a, ha⟩ : ∃ a, g a ≠ a := by
        by_contra hf
        push Not at hf
        exact he (Equiv.ext hf)
      let t := Equiv.swap a (g a) * g
      have hs : Equiv.swap a (g a) ∈ fiberSubgroup f := swap_mem_fiberSubgroup f (hg a).symm
      have ht : t ∈ fiberSubgroup f := (fiberSubgroup f).mul_mem hs hg
      have hsub : t.support ⊂ g.support := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨fun y hy => (Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne hy).1, ?_⟩
        intro heq
        have ha' : a ∈ t.support := heq ▸ Equiv.Perm.mem_support.mpr ha
        exact (Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne ha').2 rfl
      have hlt : t.support.card < n := (Finset.card_lt_card hsub).trans_eq hn
      have htH := ih t.support.card hlt t rfl ht
      have hsH := hH a (g a) (hg a).symm
      have hx := H.mul_mem hsH htH
      simpa only [t, ← mul_assoc, Equiv.swap_mul_self, one_mul] using hx
  exact haux _ g rfl hg

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma flipPermutation_ne (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    flipPermutation d i x ≠ x := by
  intro h
  have hi := congrFun (congrArg (positionsEquiv d).symm h) i
  simp only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply, binaryFlip_apply,
    Function.update_self] at hi
  generalize (positionsEquiv d).symm x i = a at hi
  fin_cases a <;> simp at hi

lemma coordinate_edge_swap_mem (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    Equiv.swap x (flipPermutation d i x) ∈ coordinateSubgroup d i := by
  apply swap_mem_fiberSubgroup
  exact (flipPermutation_mem d i x).symm

lemma coordinateSubgroup_le_of_edge_swaps (d : ℕ) (i : Fin d)
    (H : Subgroup (SymmetricGroup (2 ^ d)))
    (hH : ∀ x, Equiv.swap x (flipPermutation d i x) ∈ H) : coordinateSubgroup d i ≤ H := by
  apply fiberSubgroup_le_of_swaps
  intro x y hxy
  rcases binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm y)
      (fun j hj => (congrFun hxy ⟨j, hj⟩).symm) with he | he
  · have hy : y = x := (positionsEquiv d).symm.injective he
    rw [hy, Equiv.swap_self]
    exact H.one_mem
  · have hy : y = flipPermutation d i x := by
      apply (positionsEquiv d).symm.injective
      simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using he
    rw [hy]; exact hH x

lemma coordinate_edge_swaps_commute (d : ℕ) (i : Fin d) (x y : Fin (2 ^ d)) :
    Commute (Equiv.swap x (flipPermutation d i x)) (Equiv.swap y (flipPermutation d i y)) := by
  by_cases hy : y = x
  · subst y; exact Commute.refl _
  by_cases hf : y = flipPermutation d i x
  · subst y
    rw [flipPermutation_twice, Equiv.swap_comm (flipPermutation d i x) x]
  have hxy' : x ≠ flipPermutation d i y := by
    intro he
    have he' := congrArg (flipPermutation d i) he
    rw [flipPermutation_twice] at he'
    exact hf he'.symm
  apply Equiv.Perm.Disjoint.commute
  apply Equiv.Perm.disjoint_swap_swap
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_false_eq_true,
    not_or, List.nodup_nil, and_true]
  exact ⟨⟨(flipPermutation_ne d i x).symm, Ne.symm hy, hxy'⟩,
    ⟨⟨Ne.symm hf, fun h => hy ((flipPermutation d i).injective h).symm⟩,
      (flipPermutation_ne d i y).symm⟩⟩

lemma coordinate_real_average_as_switches {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : ℕ) (i : Fin d) (ρ : Representation ℝ (SymmetricGroup (2 ^ d)) E) :
    realGroupAverage (ρ.comp (coordinateSubgroup d i).subtype) =
      ((List.ofFn fun x : Fin (2 ^ d) => fairAction ρ
        (Equiv.swap x (flipPermutation d i x)))).prod := by
  let L : List (coordinateSubgroup d i) := List.ofFn (fun x =>
    ⟨Equiv.swap x (flipPermutation d i x), coordinate_edge_swap_mem d i x⟩)
  have hl := realGroupAverage_eq_fairAction_prod (ρ.comp (coordinateSubgroup d i).subtype) L
  suffices he : realGroupAverage (ρ.comp (coordinateSubgroup d i).subtype) =
      (L.map (fairAction (ρ.comp (coordinateSubgroup d i).subtype))).prod by
    simpa only [L, List.map_ofFn, Function.comp_def, fairAction, MonoidHom.comp_apply, Subgroup.subtype_apply] using he
  apply hl
  · intro g hg
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hg
    apply Subtype.ext
    exact Equiv.swap_mul_self _ _
  · intro g hg h hh
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨y, rfl⟩ := List.mem_ofFn.mp hh
    apply Subtype.ext
    exact coordinate_edge_swaps_commute d i x y
  · intro H hH
    have hr : coordinateSubgroup d i ≤ H.map (coordinateSubgroup d i).subtype := by
      apply coordinateSubgroup_le_of_edge_swaps
      intro x
      exact ⟨⟨_, coordinate_edge_swap_mem d i x⟩, hH _ (List.mem_ofFn.mpr ⟨x, rfl⟩), rfl⟩
    apply top_unique
    intro g hg
    obtain ⟨q, hq, he⟩ := hr g.property
    exact (Subtype.ext he : q = g) ▸ hq

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SubsetSweep
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (A : Type*) [DecidableEq A]

def realSiteRepresentation : Representation ℝ (Equiv.Perm A) (A → ℝ) where
  toFun g := {
    toFun p x := p (g⁻¹ x)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext p x; rfl
  map_mul' := by intros; ext p x; rfl

def subsetRepresentation : Representation ℝ (Equiv.Perm A) (Finset A → ℝ) where
  toFun (g : Equiv.Perm A) := {
    toFun M T := M (T.image (g⁻¹ : Equiv.Perm A))
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by ext M T; simp
  map_mul' := by intros; ext M T; simp [Finset.image_image, Function.comp_def]

lemma fairAction_site (a b : A) (p : A → ℝ) :
    fairAction (realSiteRepresentation A) (Equiv.swap a b) p = fairSwapWeights a b p := by
  ext x
  simp only [fairAction_apply, realSiteRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, Equiv.swap_inv,
    smul_eq_mul, fairSwapWeights]
  ring

lemma fairAction_subset (a b : A) (M : Finset A → ℝ) :
    fairAction (subsetRepresentation A) (Equiv.swap a b) M = fairSwapInclusion a b M := by
  ext T
  simp only [fairAction_apply, subsetRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, Pi.add_apply, Equiv.swap_inv,
    smul_eq_mul, fairSwapInclusion]
  ring

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [DecidableEq A]

lemma switch_product_inclusion_bound (L : List (A × A)) (M : Finset A → ℝ) (p : A → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ (L.map (fun e => fairAction (realSiteRepresentation A) (Equiv.swap e.1 e.2))).prod p x) ∧
      (∀ T, (L.map (fun e => fairAction (subsetRepresentation A) (Equiv.swap e.1 e.2))).prod M T ≤
        ∏ x ∈ T, (L.map (fun e => fairAction (realSiteRepresentation A) (Equiv.swap e.1 e.2))).prod p x) := by
  induction L with
  | nil => simpa using And.intro hp hM
  | cons e L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      fairAction_site, fairAction_subset]
    exact ⟨fairSwapWeights_nonneg e.1 e.2 ih.1,
      fairSwapInclusion_bound e.1 e.2 _ _ ih.1 ih.2⟩

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma coordinate_inclusion_bound {d : ℕ} (i : Fin d) (M : Finset (Fin (2 ^ d)) → ℝ)
    (p : Fin (2 ^ d) → ℝ) (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
      (coordinateSubgroup d i).subtype) p x) ∧
      (∀ T, realGroupAverage ((subsetRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype) M T ≤
        ∏ x ∈ T, realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
          (coordinateSubgroup d i).subtype) p x) := by
  rw [coordinate_real_average_as_switches, coordinate_real_average_as_switches]
  simpa only [List.map_ofFn, Function.comp_def] using
    switch_product_inclusion_bound (List.ofFn (fun x : Fin (2 ^ d) => (x, flipPermutation d i x))) M p hp hM

def realSiteSweep (d : ℕ) : (Fin (2 ^ d) → ℝ) →ₗ[ℝ] (Fin (2 ^ d) → ℝ) :=
  ((List.ofFn (fun i : Fin d => realGroupAverage
    ((realSiteRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).reverse).prod

def subsetSweep (d : ℕ) : (Finset (Fin (2 ^ d)) → ℝ) →ₗ[ℝ] (Finset (Fin (2 ^ d)) → ℝ) :=
  ((List.ofFn (fun i : Fin d => realGroupAverage
    ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).reverse).prod

lemma subsetSweep_inclusion_bound {d : ℕ} (M : Finset (Fin (2 ^ d)) → ℝ)
    (p : Fin (2 ^ d) → ℝ) (hp : ∀ x, 0 ≤ p x) (hM : ∀ T, M T ≤ ∏ x ∈ T, p x) :
    (∀ x, 0 ≤ realSiteSweep d p x) ∧
      (∀ T, subsetSweep d M T ≤ ∏ x ∈ T, realSiteSweep d p x) := by
  have hh (L : List (Fin d)) :
      (∀ x, 0 ≤ ((L.map fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype)).prod p) x) ∧
      (∀ T, ((L.map fun i => realGroupAverage ((subsetRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype)).prod M) T ≤
          ∏ x ∈ T, ((L.map fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
            (coordinateSubgroup d i).subtype)).prod p) x) := by
    induction L with
    | nil => simpa using And.intro hp hM
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact coordinate_inclusion_bound i _ _ ih.1 ih.2
  simpa [realSiteSweep, subsetSweep, List.ofFn_eq_map] using hh (List.finRange d).reverse

lemma realSiteAverage_complexify {n : ℕ} (H : Subgroup (SymmetricGroup n)) (p : Fin n → ℝ) (x : Fin n) :
    ((realGroupAverage ((realSiteRepresentation (Fin n)).comp H.subtype) p x : ℝ) : ℂ) =
      groupAverage ((oneCardRepresentation n).comp H.subtype) (fun y => (p y : ℂ)) x := by
  classical
  simp only [realGroupAverage, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    realSiteRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, oneCardRepresentation_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_sum, Complex.ofReal_inv, Complex.ofReal_natCast]

lemma realSiteSweep_complexify {d : ℕ} (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
    ((realSiteSweep d p x : ℝ) : ℂ) = oneCardSweep d (fun y => (p y : ℂ)) x := by
  have hh (L : List (Fin d)) (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
      (((L.map (fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype))).prod p x : ℝ) : ℂ) =
      (L.map (fun i => groupAverage ((oneCardRepresentation (2 ^ d)).comp
        (coordinateSubgroup d i).subtype))).prod (fun y => (p y : ℂ)) x := by
    induction L generalizing p x with
    | nil => rfl
    | cons i L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [realSiteAverage_complexify]
      rw [show (fun y => (((L.map (fun i => realGroupAverage ((realSiteRepresentation (Fin (2 ^ d))).comp
        (coordinateSubgroup d i).subtype))).prod p y : ℝ) : ℂ)) =
        (L.map (fun i => groupAverage ((oneCardRepresentation (2 ^ d)).comp
        (coordinateSubgroup d i).subtype))).prod (fun y => (p y : ℂ)) from funext (fun y => ih p y)]
  simpa [realSiteSweep, oneCardSweep, List.ofFn_eq_map] using hh (List.finRange d).reverse p x

lemma realSiteSweep_uniform {d : ℕ} (p : Fin (2 ^ d) → ℝ) (x : Fin (2 ^ d)) :
    realSiteSweep d p x = (∑ y, p y) / (2 ^ d : ℕ) := by
  apply Complex.ofReal_injective
  rw [realSiteSweep_complexify, oneCardSweep_uniform]
  simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [DecidableEq A]

lemma subset_indicator_product (S T : Finset A) :
    (if T ⊆ S then (1 : ℝ) else 0) = ∏ x ∈ T, if x ∈ S then (1 : ℝ) else 0 := by
  by_cases h : T ⊆ S
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro x hx
    exact if_pos (h hx)
  · rw [if_neg h]
    obtain ⟨x, hx, hxn⟩ := Finset.not_subset.mp h
    symm
    exact Finset.prod_eq_zero hx (if_neg hxn)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma subsetSweep_upper_inclusion (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    subsetSweep d (fun U => if U ⊆ S then 1 else 0) T ≤
      ((S.card : ℝ) / (2 ^ d : ℕ)) ^ T.card := by
  have hp (x : Fin (2 ^ d)) : (0 : ℝ) ≤ if x ∈ S then 1 else 0 := by split_ifs <;> norm_num
  have h := (subsetSweep_inclusion_bound (fun U => if U ⊆ S then 1 else 0)
    (fun x => if x ∈ S then 1 else 0) hp (fun U => (subset_indicator_product S U).le)).2 T
  simp only [realSiteSweep_uniform] at h
  simpa [div_pow] using h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SubsetLaw
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]

def upperInclusionMap : (Finset A → ℝ) →ₗ[ℝ] (Finset A → ℝ) where
  toFun μ T := ∑ S : Finset A, if T ⊆ S then μ S else 0
  map_add' := by
    intro μ ν
    ext T
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp
  map_smul' := by
    intro a μ
    ext T
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> simp

lemma upperInclusion_permutation (g : Equiv.Perm A) :
    Commute (upperInclusionMap (A := A)) (subsetRepresentation A g) := by
  change upperInclusionMap * subsetRepresentation A g = subsetRepresentation A g * upperInclusionMap
  apply LinearMap.ext
  intro μ
  funext T
  change (∑ S : Finset A, if T ⊆ S then μ (S.image (g⁻¹ : Equiv.Perm A)) else 0) =
    ∑ S : Finset A, if T.image (g⁻¹ : Equiv.Perm A) ⊆ S then μ S else 0
  apply Fintype.sum_equiv g.symm.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding, Equiv.Perm.coe_inv]
  simp only [Finset.image_subset_image_iff g.symm.injective]

lemma upperInclusion_average (H : Subgroup (Equiv.Perm A)) :
    Commute (upperInclusionMap (A := A)) (realGroupAverage ((subsetRepresentation A).comp H.subtype)) := by
  unfold realGroupAverage
  apply Commute.smul_right
  apply Commute.sum_right
  intro g _
  exact upperInclusion_permutation g.1

lemma subsetAverage_apply (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) (T : Finset A) :
    realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T =
      (Fintype.card H : ℝ)⁻¹ * ∑ g : H, μ (T.image ((g.1)⁻¹ : Equiv.Perm A)) := by
  classical
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
    subsetRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul]

lemma subsetAverage_nonneg (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (T : Finset A) :
    0 ≤ realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T := by
  classical
  rw [subsetAverage_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun g _ => hμ _))

lemma subsetAverage_card_support (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) (k : ℕ)
    (hμ : ∀ S, S.card ≠ k → μ S = 0) (T : Finset A) (hT : T.card ≠ k) :
    realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T = 0 := by
  classical
  rw [subsetAverage_apply]
  have hs : ∀ g : H, μ (T.image ((g.1)⁻¹ : Equiv.Perm A)) = 0 := by
    intro g
    apply hμ
    rwa [Finset.card_image_of_injective _ (g.1⁻¹).injective]
  simp only [hs, Finset.sum_const_zero, mul_zero]

lemma subsetAverage_mass (H : Subgroup (Equiv.Perm A)) (μ : Finset A → ℝ) :
    (∑ T, realGroupAverage ((subsetRepresentation A).comp H.subtype) μ T) = ∑ T, μ T := by
  classical
  simp only [subsetAverage_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hs (g : H) : (∑ T : Finset A, μ (T.image ((g.1)⁻¹ : Equiv.Perm A))) = ∑ T, μ T := by
    simpa only [Equiv.finsetCongr_apply, Finset.map_eq_image, Equiv.coe_toEmbedding, Equiv.Perm.coe_inv]
      using g.1.symm.finsetCongr.sum_comp μ
  simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma upperInclusion_pointMass (S : Finset A) :
    upperInclusionMap (fun U => if U = S then 1 else 0) =
      (fun T => if T ⊆ S then 1 else 0) := by
  ext T
  change (∑ U : Finset A, if T ⊆ U then (if U = S then (1 : ℝ) else 0) else 0) = _
  have he (U : Finset A) :
      (if T ⊆ U then (if U = S then (1 : ℝ) else 0) else 0) =
      (if U = S then (if T ⊆ U then 1 else 0) else 0) := by split_ifs <;> rfl
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sweptSubsetLaw (d : ℕ) (S T : Finset (Fin (2 ^ d))) : ℝ :=
  subsetSweep d (fun U => if U = S then 1 else 0) T

lemma upperInclusion_sweep (d : ℕ) :
    Commute (upperInclusionMap (A := Fin (2 ^ d))) (subsetSweep d) := by
  unfold subsetSweep
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
  exact upperInclusion_average _

lemma subsetSweep_law_properties (d : ℕ) (μ : Finset (Fin (2 ^ d)) → ℝ) (k : ℕ)
    (hμ : ∀ S, 0 ≤ μ S) (hcard : ∀ S, S.card ≠ k → μ S = 0) :
    (∀ T, 0 ≤ subsetSweep d μ T) ∧
      (∀ T, T.card ≠ k → subsetSweep d μ T = 0) ∧
      (∑ T, subsetSweep d μ T) = ∑ T, μ T := by
  have h (L : List (Fin d)) (μ : Finset (Fin (2 ^ d)) → ℝ)
      (hμ : ∀ S, 0 ≤ μ S) (hcard : ∀ S, S.card ≠ k → μ S = 0) :
      (∀ T, 0 ≤ (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T) ∧
      (∀ T, T.card ≠ k → (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T = 0) ∧
      (∑ T, (L.map (fun i => realGroupAverage
        ((subsetRepresentation (Fin (2 ^ d))).comp (coordinateSubgroup d i).subtype))).prod μ T) = ∑ T, μ T := by
    induction L with
    | nil => exact ⟨hμ, hcard, rfl⟩
    | cons i L ih =>
      obtain ⟨ihp, ihc, ihm⟩ := ih
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact ⟨subsetAverage_nonneg _ _ ihp, subsetAverage_card_support _ _ _ ihc,
        (subsetAverage_mass _ _).trans ihm⟩
  simpa only [subsetSweep, List.ofFn_eq_map, List.map_reverse] using
    h (List.finRange d).reverse μ hμ hcard

lemma sweptSubsetLaw_nonneg (d : ℕ) (S T : Finset (Fin (2 ^ d))) : 0 ≤ sweptSubsetLaw d S T := by
  apply (subsetSweep_law_properties d (fun U => if U = S then 1 else 0) S.card _ _).1
  · intro U; split_ifs <;> norm_num
  · intro U hU; rw [if_neg (fun he => hU (congrArg Finset.card he))]

lemma sweptSubsetLaw_card_support (d : ℕ) (S T : Finset (Fin (2 ^ d))) (hT : T.card ≠ S.card) :
    sweptSubsetLaw d S T = 0 := by
  apply (subsetSweep_law_properties d (fun U => if U = S then 1 else 0) S.card _ _).2.1 T hT
  · intro U; split_ifs <;> norm_num
  · intro U hU; rw [if_neg (fun he => hU (congrArg Finset.card he))]

lemma sweptSubsetLaw_upper_inclusion (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    (∑ U : Finset (Fin (2 ^ d)), if T ⊆ U then sweptSubsetLaw d S U else 0) ≤
      ((S.card : ℝ) / (2 ^ d : ℕ)) ^ T.card := by
  change upperInclusionMap (subsetSweep d (fun U => if U = S then 1 else 0)) T ≤ _
  have h := congrArg (fun F : Module.End ℝ (Finset (Fin (2 ^ d)) → ℝ) =>
    F (fun U => if U = S then 1 else 0) T) (upperInclusion_sweep d).eq
  change upperInclusionMap (subsetSweep d (fun U => if U = S then 1 else 0)) T =
    subsetSweep d (upperInclusionMap (fun U => if U = S then 1 else 0)) T at h
  rw [h, upperInclusion_pointMass]
  exact subsetSweep_upper_inclusion d S T

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.IndependentNetworks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]

def subsetFiber (S : Finset (J × A)) (j : J) : Finset A :=
  Finset.univ.filter (fun x => (j,x) ∈ S)

omit [Fintype J] in
@[simp]
lemma mem_subsetFiber (S : Finset (J × A)) (j : J) (x : A) :
    x ∈ subsetFiber S j ↔ (j,x) ∈ S := by simp [subsetFiber]

def subsetFiberEquiv : Finset (J × A) ≃ (J → Finset A) where
  toFun := subsetFiber
  invFun S := Finset.univ.filter (fun v => v.2 ∈ S v.1)
  left_inv S := by ext v; simp
  right_inv S := by ext j x; simp

omit [Fintype J] in
lemma subset_iff_fibers {S T : Finset (J × A)} :
    S ⊆ T ↔ ∀ j, subsetFiber S j ⊆ subsetFiber T j := by
  constructor
  · intro h j x hx
    exact (mem_subsetFiber T j x).mpr (h ((mem_subsetFiber S j x).mp hx))
  · intro h v hv
    exact (mem_subsetFiber T v.1 v.2).mp (h v.1 ((mem_subsetFiber S v.1 v.2).mpr hv))

lemma card_subset_fibers (S : Finset (J × A)) : S.card = ∑ j, (subsetFiber S j).card := by
  calc
    S.card = ∑ v : J × A, if v ∈ S then 1 else 0 := by simp
    _ = ∑ j, ∑ x : A, if (j,x) ∈ S then 1 else 0 := Fintype.sum_prod_type _
    _ = _ := by simp only [subsetFiber, Finset.card_filter]

def independentSubsetLaw (μ : J → Finset A → ℝ) (S : Finset (J × A)) : ℝ :=
  ∏ j, μ j (subsetFiber S j)

lemma independentSubsetLaw_nonneg (μ : J → Finset A → ℝ) (hμ : ∀ j S, 0 ≤ μ j S)
    (T : Finset (J × A)) : 0 ≤ independentSubsetLaw μ T :=
  Finset.prod_nonneg (fun j _ => hμ j _)

lemma independentSubsetLaw_card_support (μ : J → Finset A → ℝ) (k : J → ℕ)
    (hμ : ∀ j S, S.card ≠ k j → μ j S = 0) (T : Finset (J × A))
    (hT : T.card ≠ ∑ j, k j) : independentSubsetLaw μ T = 0 := by
  have hex : ∃ j, (subsetFiber T j).card ≠ k j := by
    by_contra h
    push Not at h
    exact hT ((card_subset_fibers T).trans (Finset.sum_congr rfl (fun j _ => h j)))
  obtain ⟨j, hj⟩ := hex
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hμ j _ hj)

lemma independentSubsetLaw_upper_inclusion (μ : J → Finset A → ℝ) (T : Finset (J × A)) :
    (∑ U : Finset (J × A), if T ⊆ U then independentSubsetLaw μ U else 0) =
      ∏ j, ∑ U : Finset A, if subsetFiber T j ⊆ U then μ j U else 0 := by
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv subsetFiberEquiv
  intro S
  simp only [Finset.prod_ite_zero, Finset.mem_univ, forall_true_left]
  change (if T ⊆ S then independentSubsetLaw μ S else 0) =
    if ∀ j, subsetFiber T j ⊆ subsetFiber S j then (∏ j, μ j (subsetFiber S j)) else 0
  simp only [subset_iff_fibers, independentSubsetLaw]

lemma network_weight_product (T : Finset (J × A)) (p : J → ℝ) :
    (∏ v ∈ T, p v.1) = ∏ j, p j ^ (subsetFiber T j).card := by
  calc
    (∏ v ∈ T, p v.1) = ∏ v : J × A, if v ∈ T then p v.1 else 1 := by simp
    _ = ∏ j, ∏ x : A, if (j,x) ∈ T then p j else 1 := Fintype.prod_prod_type _
    _ = ∏ j, ∏ _ ∈ subsetFiber T j, p j := by
      apply Finset.prod_congr rfl
      intro j _
      simp only [subsetFiber, Finset.prod_filter]
    _ = _ := by simp

lemma independentSubsetLaw_inclusion_bound (μ : J → Finset A → ℝ) (p : J → ℝ)
    (hμ : ∀ j S, 0 ≤ μ j S) (_hp : ∀ j, 0 ≤ p j)
    (hinc : ∀ j T, (∑ U : Finset A, if T ⊆ U then μ j U else 0) ≤ (p j) ^ T.card)
    (T : Finset (J × A)) :
    (∑ U : Finset (J × A), if T ⊆ U then independentSubsetLaw μ U else 0) ≤
      ∏ v ∈ T, p v.1 := by
  rw [independentSubsetLaw_upper_inclusion, network_weight_product]
  apply Finset.prod_le_prod
  · intro j _
    exact Finset.sum_nonneg (fun U _ => by split_ifs; exact hμ j U; exact le_rfl)
  · intro j _; exact hinc j _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def independentSweptLaw (S : J → Finset (Fin (2 ^ d))) : Finset (J × Fin (2 ^ d)) → ℝ :=
  independentSubsetLaw (fun j => sweptSubsetLaw d (S j))

lemma independentSweptLaw_nonneg (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    0 ≤ independentSweptLaw S T :=
  independentSubsetLaw_nonneg _ (fun j U => sweptSubsetLaw_nonneg d (S j) U) T

lemma independentSweptLaw_card_support (S : J → Finset (Fin (2 ^ d)))
    (T : Finset (J × Fin (2 ^ d))) (hT : T.card ≠ ∑ j, (S j).card) :
    independentSweptLaw S T = 0 :=
  independentSubsetLaw_card_support _ (fun j => (S j).card)
    (fun j U => sweptSubsetLaw_card_support d (S j) U) T hT

lemma independentSweptLaw_upper_inclusion (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    (∑ U : Finset (J × Fin (2 ^ d)), if T ⊆ U then independentSweptLaw S U else 0) ≤
      ∏ w ∈ T, ((S w.1).card : ℝ) / (2 ^ d : ℕ) :=
  independentSubsetLaw_inclusion_bound _ _ (fun j U => sweptSubsetLaw_nonneg d (S j) U)
    (fun index => div_nonneg (Nat.cast_nonneg (S index).card) (Nat.cast_nonneg _))
    (fun j T => sweptSubsetLaw_upper_inclusion d (S j) T) T

theorem swept_network_noIsolates_bound
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (S : J → Finset (Fin (2 ^ d)))
    (k : ℕ) (hk : k = ∑ j, (S j).card)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    (∑ T : {T : Finset (J × Fin (2 ^ d)) // NoIsolatedVertex (encounterGraph state) T}, independentSweptLaw S T.1) ≤
      (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  have hn : (2 ^ d : ℕ) ≠ 0 := ne_of_gt (pow_pos (by omega : 0 < (2 : ℕ)) _)
  have hnR : ((2 ^ d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn
  apply network_noIsolates_probability_bound state (fun j => (S j).card / (2 ^ d : ℕ))
    (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) k _
    (independentSweptLaw S) (independentSweptLaw_nonneg S)
    (fun T hT => independentSweptLaw_card_support S T (hk ▸ hT))
    (independentSweptLaw_upper_inclusion S) hΔ hΔ1
  rw [← Finset.sum_div, mul_div_cancel₀ _ hnR, hk, Nat.cast_sum]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.InvariantObstruction
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def supportedSubgroup {n : ℕ} (S : Finset (Fin n)) : Subgroup (SymmetricGroup n) where
  carrier := {g | ∀ x, x ∉ S → g x = x}
  one_mem' := by intro x hx; rfl
  mul_mem' := by
    intro g h hg hh x hx
    change g (h x) = x
    rw [hh x hx, hg x hx]
  inv_mem' := by
    intro g hg x hx
    exact g.injective (by simpa using (hg x hx).symm)

lemma swap_mem_supportedSubgroup {n : ℕ} (S : Finset (Fin n))
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) : Equiv.swap a b ∈ supportedSubgroup S := by
  classical
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb))

lemma Partition.colOf_lt_firstRow {n : ℕ} (lam : Partition n) (x : Fin n) :
    lam.colOf x < lam.1.rowLen 0 := by
  have h := (lam.tableau.symm x).property
  have hle := lam.1.rowLen_anti 0 (lam.rowOf x) (Nat.zero_le _)
  exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_rowLen.mp h) hle

lemma large_set_column_pair {n : ℕ} (lam : Partition n) (S : Finset (Fin n))
    (hS : lam.1.rowLen 0 < S.card) (g : SymmetricGroup n) :
    ∃ a b : Fin n, a ≠ b ∧ lam.colOf a = lam.colOf b ∧ g a ∈ S ∧ g b ∈ S := by
  classical
  let f : S → Fin (lam.1.rowLen 0) := fun x =>
    ⟨lam.colOf (g⁻¹ x.1), lam.colOf_lt_firstRow _⟩
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hS)
  refine ⟨g⁻¹ x.1, g⁻¹ y.1, ?_, congrArg Fin.val hf, ?_, ?_⟩
  · intro h
    exact hxy (Subtype.ext (g.symm.injective h))
  · simp
  · simp

lemma supportedAverage_annihilates_generator {n : ℕ} (lam : Partition n)
    (S : Finset (Fin n)) (hS : lam.1.rowLen 0 < S.card) (g : SymmetricGroup n) :
    groupAverage ((regularRepresentation n).comp (supportedSubgroup S).subtype)
      (regularRepresentation n g (polytabloid lam)) = 0 := by
  classical
  obtain ⟨a, b, hab, hc, haS, hbS⟩ := large_set_column_pair lam S hS g
  apply groupAverage_anti_fixed _ ⟨Equiv.swap (g a) (g b),
    swap_mem_supportedSubgroup S haS hbS⟩
  change regularRepresentation _ (Equiv.swap (g a) (g b))
    (regularRepresentation _ g (polytabloid lam)) = _
  rw [← Module.End.mul_apply, ← map_mul, Equiv.swap_mul_eq_mul_swap]
  simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
  rw [map_mul, Module.End.mul_apply]
  have ha := polytabloid_column_action lam ⟨Equiv.swap a b, swap_mem_fiberSubgroup _ hc⟩
  have hs : complexSign _ (Equiv.swap a b) = -1 := by
    simp [complexSign, Equiv.Perm.sign_swap hab]
  rw [ha, hs, neg_one_smul, map_neg]

lemma supportedAverage_eq_zero {n : ℕ} (lam : Partition n) (S : Finset (Fin n))
    (hS : lam.1.rowLen 0 < S.card) :
    groupAverage ((spechtRepresentation lam).comp (supportedSubgroup S).subtype) = 0 := by
  classical
  let A := groupAverage ((regularRepresentation n).comp (supportedSubgroup S).subtype)
  have ha : (spechtSubrepresentation lam).toSubmodule ≤ A.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact supportedAverage_annihilates_generator lam S hS g
  ext x
  apply (show Function.Injective (spechtInclusion lam) from Subtype.val_injective)
  have hx := ha x.property
  rw [LinearMap.zero_apply, map_zero]
  change A (spechtInclusion lam x) = 0 at hx
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have he (g : supportedSubgroup S) : spechtInclusion lam (spechtRepresentation lam g.1 x) =
      regularRepresentation _ g.1 (spechtInclusion lam x) := rfl
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, he]
  simpa only [A, groupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply] using hx

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TupleRealization
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev InjectiveTuple (I : Type*) (n : ℕ) := I ↪ Fin n

def tupleEquiv {I : Type*} {n : ℕ} (g : SymmetricGroup n) :
    InjectiveTuple I n ≃ InjectiveTuple I n where
  toFun x := x.trans g.toEmbedding
  invFun x := x.trans g⁻¹.toEmbedding
  left_inv x := by apply Function.Embedding.ext; intro i; exact g.symm_apply_apply (x i)
  right_inv x := by apply Function.Embedding.ext; intro i; exact g.apply_symm_apply (x i)

@[simp] lemma tupleEquiv_apply {I : Type*} {n : ℕ} (g : SymmetricGroup n)
    (x : InjectiveTuple I n) (i : I) : tupleEquiv g x i = g (x i) := rfl

@[simp] lemma tupleEquiv_one {I : Type*} {n : ℕ} (x : InjectiveTuple I n) :
    tupleEquiv 1 x = x := by ext i; rfl

@[simp] lemma tupleEquiv_mul {I : Type*} {n : ℕ} (g h : SymmetricGroup n)
    (x : InjectiveTuple I n) : tupleEquiv (g * h) x = tupleEquiv g (tupleEquiv h x) := rfl

abbrev TupleSpace (I : Type*) [Fintype I] (n : ℕ) :=
  EuclideanSpace ℂ (InjectiveTuple I n)

def tupleIsometry {I : Type*} [Fintype I] {n : ℕ} (g : SymmetricGroup n) :
    TupleSpace I n ≃ₗᵢ[ℂ] TupleSpace I n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (tupleEquiv g)

def tupleRepresentation (I : Type*) [Fintype I] (n : ℕ) :
    Representation ℂ (SymmetricGroup n) (TupleSpace I n) where
  toFun g := (tupleIsometry (I := I) g).toLinearEquiv.toLinearMap
  map_one' := by
    ext f x
    change f (tupleEquiv (1 : SymmetricGroup n) x) = f x
    rw [tupleEquiv_one]
  map_mul' := by
    intro g h
    ext f x
    change f (tupleEquiv (g * h)⁻¹ x) = f (tupleEquiv h⁻¹ (tupleEquiv g⁻¹ x))
    simp

@[simp] lemma tupleRepresentation_apply {I : Type*} [Fintype I] {n : ℕ}
    (g : SymmetricGroup n) (f : TupleSpace I n) (x : InjectiveTuple I n) :
    tupleRepresentation I n g f x = f (tupleEquiv g⁻¹ x) := rfl

def extendOffFirstRow {n : ℕ} (lam : Partition n)
    (x : InjectiveTuple (OffFirstRow lam) n) : SymmetricGroup n :=
  Classical.choose (Equiv.Perm.exists_extending_pair Subtype.val x Subtype.val_injective x.injective)

lemma extendOffFirstRow_apply {n : ℕ} (lam : Partition n)
    (x : InjectiveTuple (OffFirstRow lam) n) (i : OffFirstRow lam) :
    extendOffFirstRow lam x i.1 = x i :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    Subtype.val x Subtype.val_injective x.injective) i

def tupleRealization {n : ℕ} (lam : Partition n) :
    Specht lam →ₗ[ℂ] TupleSpace (OffFirstRow lam) n where
  toFun v := WithLp.toLp 2 (fun x => spechtInclusion lam v (extendOffFirstRow lam x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma tupleRealization_apply_perm {n : ℕ} (lam : Partition n) (v : Specht lam)
    (x : InjectiveTuple (OffFirstRow lam) n) (g : SymmetricGroup n)
    (hg : ∀ i : OffFirstRow lam, g i.1 = x i) :
    tupleRealization lam v x = spechtInclusion lam v g := by
  let a : rowSubgroup lam := ⟨(extendOffFirstRow lam x)⁻¹ * g,
    restrict_offFirstRow_eq lam _ _ (fun i => (extendOffFirstRow_apply lam x i).trans (hg i).symm)⟩
  change spechtInclusion lam v (extendOffFirstRow lam x) = spechtInclusion lam v g
  symm
  simpa [a] using specht_right_row lam v a (extendOffFirstRow lam x)

lemma tupleRealization_intertwines {n : ℕ} (lam : Partition n) (g : SymmetricGroup n)
    (v : Specht lam) :
    tupleRealization lam (spechtRepresentation lam g v) =
      tupleRepresentation (OffFirstRow lam) n g (tupleRealization lam v) := by
  apply PiLp.ext
  intro x
  change spechtInclusion lam v (g⁻¹ * extendOffFirstRow lam x) =
    tupleRealization lam v (tupleEquiv g⁻¹ x)
  symm
  apply tupleRealization_apply_perm
  intro i
  change g⁻¹ (extendOffFirstRow lam x i.1) = g⁻¹ (x i)
  rw [extendOffFirstRow_apply]

lemma tuple_intertwiner_eq_zero_of_fewer_labels {n : ℕ} (lam : Partition n)
    (I : Type*) [Fintype I] (hI : lam.1.rowLen 0 + Fintype.card I < n)
    (T : Specht lam →ₗ[ℂ] TupleSpace I n)
    (hT : ∀ g v, T (spechtRepresentation lam g v) = tupleRepresentation I n g (T v)) :
    T = 0 := by
  classical
  ext v x
  let S : Finset (Fin n) := Finset.univ \ Finset.univ.map x
  have hS : lam.1.rowLen 0 < S.card := by
    simp only [S, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_map]
    omega
  have hfix (g : supportedSubgroup S) : tupleEquiv g.1 x = x := by
    apply Function.Embedding.ext
    intro i
    change g.1 (x i) = x i
    apply g.property
    simp only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and, not_not]
    exact ⟨i, rfl⟩
  have hz := congrArg (fun A : Specht lam →ₗ[ℂ] Specht lam => T (A v) x)
    (supportedAverage_eq_zero lam S hS)
  simp only [groupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    MonoidHom.comp_apply, Subgroup.subtype_apply, hT, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply, tupleRepresentation_apply, LinearMap.zero_apply, map_zero,
    PiLp.zero_apply] at hz
  have hi (g : supportedSubgroup S) : tupleEquiv g.1⁻¹ x = x := hfix g⁻¹
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul] at hz
  have hu : (Fintype.card (supportedSubgroup S) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa only [← mul_assoc, inv_mul_cancel₀ hu, one_mul, LinearMap.zero_apply, PiLp.zero_apply] using hz

def tupleMarginal {I J : Type*} [Fintype I] [Fintype J] {n : ℕ} (e : J ↪ I) :
    TupleSpace I n →ₗ[ℂ] TupleSpace J n where
  toFun f := WithLp.toLp 2 (fun x => ∑ y : InjectiveTuple I n,
    if e.trans y = x then f y else 0)
  map_add' f g := by
    ext x
    change (∑ y, if e.trans y = x then f y + g y else 0) = _
    simp only [ite_add_zero, Finset.sum_add_distrib]
    rfl
  map_smul' c f := by
    ext x
    change (∑ y, if e.trans y = x then c • f y else 0) =
      c • ∑ y, if e.trans y = x then f y else 0
    simp only [Finset.smul_sum, smul_ite, smul_zero]

lemma tupleMarginal_intertwines {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (e : J ↪ I) (g : SymmetricGroup n) (f : TupleSpace I n) :
    tupleMarginal e (tupleRepresentation I n g f) =
      tupleRepresentation J n g (tupleMarginal e f) := by
  classical
  apply PiLp.ext
  intro x
  change (∑ y, if e.trans y = x then f (tupleEquiv g⁻¹ y) else 0) =
    ∑ y, if e.trans y = tupleEquiv g⁻¹ x then f y else 0
  apply Fintype.sum_equiv (tupleEquiv g⁻¹)
  intro y
  have h : (e.trans y = x) ↔ (e.trans (tupleEquiv g⁻¹ y) = tupleEquiv g⁻¹ x) :=
    (tupleEquiv g⁻¹).injective.eq_iff.symm
  simp only [h]

lemma tupleRealization_marginal_eq_zero {n : ℕ} (lam : Partition n)
    {J : Type*} [Fintype J] (e : J ↪ OffFirstRow lam)
    (he : Fintype.card J < n - lam.1.rowLen 0) (v : Specht lam) :
    tupleMarginal e (tupleRealization lam v) = 0 := by
  have hz := tuple_intertwiner_eq_zero_of_fewer_labels lam J (by omega)
    ((tupleMarginal e).comp (tupleRealization lam)) (by
      intro g x
      simp only [LinearMap.comp_apply, tupleRealization_intertwines, tupleMarginal_intertwines])
  exact LinearMap.congr_fun hz v

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KernelBounds
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I J L : Type*} [Fintype I] [Fintype J] [Fintype L]

def kernelOperator (K : I → J → ℝ) : EuclideanSpace ℂ J →ₗ[ℂ] EuclideanSpace ℂ I where
  toFun f := WithLp.toLp 2 (fun i => ∑ j, (K i j : ℂ) * f j)
  map_add' f g := by ext i; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    change (∑ j, (K i j : ℂ) * (c * f j)) = c * ∑ j, (K i j : ℂ) * f j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype I] in
@[simp] lemma kernelOperator_apply (K : I → J → ℝ) (f : EuclideanSpace ℂ J) (i : I) :
    kernelOperator K f i = ∑ j, (K i j : ℂ) * f j := rfl

omit [Fintype I] in
lemma kernelOperator_comp (K : I → J → ℝ) (M : J → L → ℝ) :
    (kernelOperator K).comp (kernelOperator M) =
      kernelOperator (fun i l => ∑ j, K i j * M j l) := by
  ext f i
  simp only [LinearMap.comp_apply, kernelOperator_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

lemma kernelOperator_adjoint (K : I → J → ℝ) :
    (kernelOperator K).adjoint = kernelOperator (fun j i => K i j) := by
  apply LinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [LinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply, kernelOperator_apply, RCLike.inner_apply, map_sum,
    map_mul, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_left_comm, mul_assoc]

lemma nonnegative_symmetric_kernel_quadratic_bound (K : I → I → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    {p : ℝ} (hrow : ∀ i, (∑ j, K i j) ≤ p) (f : EuclideanSpace ℂ I) :
    (inner ℂ f (kernelOperator K f)).re ≤ p * ‖f‖ ^ 2 := by
  have ht (i j : I) : ((star (f i)) * ((K i j : ℂ) * f j)).re ≤
      K i j * ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) := by
    calc
      _ ≤ ‖star (f i) * ((K i j : ℂ) * f j)‖ := Complex.re_le_norm _
      _ = K i j * (‖f i‖ * ‖f j‖) := by
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK i j)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (‖f i‖ - ‖f j‖)]) (hK i j)
  calc
    _ = ∑ i, ∑ j, ((star (f i)) * ((K i j : ℂ) * f j)).re := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, kernelOperator_apply, Finset.sum_mul,
        Complex.re_sum, Complex.star_def]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    _ ≤ ∑ i, ∑ j, K i j * ((‖f i‖ ^ 2 + ‖f j‖ ^ 2) / 2) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = ∑ i, (∑ j, K i j) * ‖f i‖ ^ 2 := by
      simp_rw [mul_div, mul_add, add_div]
      simp only [Finset.sum_add_distrib]
      have he : (∑ i, ∑ j, K i j * ‖f j‖ ^ 2 / 2) =
          ∑ i, ∑ j, K i j * ‖f i‖ ^ 2 / 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym]
      rw [he]
      simp_rw [← Finset.sum_div, ← Finset.sum_mul]
      ring
    _ ≤ ∑ i, p * ‖f i‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
    _ = _ := by rw [← Finset.mul_sum, EuclideanSpace.norm_sq_eq]

theorem nonnegative_kernel_opNorm_sq_le (K : I → J → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) {p : ℝ} (hp : 0 ≤ p)
    (hrow : ∀ i, (∑ i', ∑ j, K i j * K i' j) ≤ p) :
    ‖(kernelOperator K).toContinuousLinearMap‖ ^ 2 ≤ p := by
  let T := kernelOperator K
  have hq (f : EuclideanSpace ℂ I) : ‖T.adjoint f‖ ^ 2 ≤ p * ‖f‖ ^ 2 := by
    have he : (inner ℂ (T.adjoint f) (T.adjoint f)).re = ‖T.adjoint f‖ ^ 2 := by
      simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [← he, LinearMap.adjoint_inner_left]
    have hc : T (T.adjoint f) = kernelOperator (fun i i' => ∑ j, K i j * K i' j) f := by
      rw [show T = kernelOperator K from rfl, kernelOperator_adjoint,
        ← LinearMap.comp_apply, kernelOperator_comp]
    rw [hc]
    apply nonnegative_symmetric_kernel_quadratic_bound
    · intro i i'; exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK i j) (hK i' j))
    · intro i i'; simp only [mul_comm]
    · exact hrow
  have hn : ‖T.adjoint.toContinuousLinearMap‖ ≤ Real.sqrt p := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg p)
    intro f
    change ‖T.adjoint f‖ ≤ Real.sqrt p * ‖f‖
    have hh := hq f
    have hs : (Real.sqrt p * ‖f‖) ^ 2 = p * ‖f‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp]
    nlinarith [norm_nonneg (T.adjoint f), norm_nonneg f,
      mul_nonneg (Real.sqrt_nonneg p) (norm_nonneg f)]
  rw [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map] at hn
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hp)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TupleNorm
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def firstRowStabilizer {n : ℕ} (lam : Partition n) : Subgroup (SymmetricGroup n) :=
  supportedSubgroup (Finset.univ.filter fun i => lam.rowOf i = 0)

lemma firstRowStabilizer_fixes {n : ℕ} (lam : Partition n)
    (h : firstRowStabilizer lam) (i : OffFirstRow lam) : h.1 i.1 = i.1 := by
  apply h.property
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using i.property

def restrictToTuple {n : ℕ} (lam : Partition n) (g : SymmetricGroup n) :
    InjectiveTuple (OffFirstRow lam) n := (Function.Embedding.subtype _).trans g.toEmbedding

@[simp] lemma restrictToTuple_apply {n : ℕ} (lam : Partition n)
    (g : SymmetricGroup n) (i : OffFirstRow lam) : restrictToTuple lam g i = g i.1 := rfl

lemma extendDifference_mem {n : ℕ} (lam : Partition n) (g : SymmetricGroup n) :
    (extendOffFirstRow lam (restrictToTuple lam g))⁻¹ * g ∈ firstRowStabilizer lam := by
  intro i hi
  have hr : lam.rowOf i ≠ 0 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  change (extendOffFirstRow lam (restrictToTuple lam g)).symm (g i) = i
  rw [← Equiv.eq_symm_apply]
  have ht := (extendOffFirstRow_apply lam (restrictToTuple lam g) ⟨i, hr⟩).symm
  change g i = (extendOffFirstRow lam (restrictToTuple lam g)) i at ht
  exact ht

def permutationTupleEquiv {n : ℕ} (lam : Partition n) :
    SymmetricGroup n ≃ InjectiveTuple (OffFirstRow lam) n × firstRowStabilizer lam where
  toFun g := (restrictToTuple lam g,
    ⟨(extendOffFirstRow lam (restrictToTuple lam g))⁻¹ * g, extendDifference_mem lam g⟩)
  invFun p := extendOffFirstRow lam p.1 * p.2.1
  left_inv g := by simp only [mul_inv_cancel_left]
  right_inv p := by
    have he : restrictToTuple lam (extendOffFirstRow lam p.1 * p.2.1) = p.1 := by
      apply Function.Embedding.ext
      intro i
      change extendOffFirstRow lam p.1 (p.2.1 i.1) = p.1 i
      rw [firstRowStabilizer_fixes, extendOffFirstRow_apply]
    apply Prod.ext he
    apply Subtype.ext
    dsimp
    rw [he, inv_mul_cancel_left]

lemma tupleRealization_norm_sq {n : ℕ} (lam : Partition n) (v : Specht lam) :
    ‖v‖ ^ 2 = (Fintype.card (firstRowStabilizer lam) : ℝ) * ‖tupleRealization lam v‖ ^ 2 := by
  change ‖spechtInclusion lam v‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ p : InjectiveTuple (OffFirstRow lam) n × firstRowStabilizer lam,
        ‖tupleRealization lam v p.1‖ ^ 2 := by
      apply Fintype.sum_equiv (permutationTupleEquiv lam)
      intro g
      change ‖spechtInclusion lam v g‖ ^ 2 = ‖tupleRealization lam v (restrictToTuple lam g)‖ ^ 2
      rw [tupleRealization_apply_perm lam v (restrictToTuple lam g) g (fun _ => rfl)]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

def tupleSweep (I : Type*) [Fintype I] (d : ℕ) : TupleSpace I (2 ^ d) →ₗ[ℂ] TupleSpace I (2 ^ d) :=
  ((List.ofFn fun i : Fin d => groupAverage
    ((tupleRepresentation I (2 ^ d)).comp (coordinateSubgroup d i).subtype)).reverse).prod

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.FiniteSampling
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable (𝕜 : Type*) [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {A B : Type*} [Fintype A] [Fintype B]

def finiteMean (f : A → E) : E := (Fintype.card A : 𝕜)⁻¹ • ∑ x, f x

lemma finiteMean_congr {f g : A → E} (h : ∀ x, f x = g x) :
    finiteMean 𝕜 f = finiteMean 𝕜 g := by unfold finiteMean; simp only [h]

lemma finiteMean_equiv (e : A ≃ B) (f : B → E) :
    finiteMean 𝕜 (fun x => f (e x)) = finiteMean 𝕜 f := by
  rw [finiteMean, finiteMean, Fintype.card_congr e, e.sum_comp]

lemma finiteMean_const [CharZero 𝕜] [Nonempty A] (x : E) : finiteMean 𝕜 (fun _ : A => x) = x := by
  rw [finiteMean, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

lemma finiteMean_prod (f : A × B → E) :
    finiteMean 𝕜 f = finiteMean 𝕜 (fun a => finiteMean 𝕜 (fun b => f (a,b))) := by
  simp only [finiteMean, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type,
    ← Finset.smul_sum, smul_smul, mul_comm]

lemma linearMap_finiteMean {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (T : E →ₗ[𝕜] F) (f : A → E) :
    T (finiteMean 𝕜 f) = finiteMean 𝕜 (fun a => T (f a)) := by
  simp only [finiteMean, map_smul, map_sum]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {𝕜 R : Type*} [Field 𝕜] [CharZero 𝕜] [Ring R] [Algebra 𝕜 R]

lemma finiteMean_reverse_prod (t : ℕ) (A : Fin t → Type*) [∀ i, Fintype (A i)]
    [∀ i, Nonempty (A i)] (f : ∀ i, A i → R) :
    finiteMean 𝕜 (fun a : ∀ i, A i => ((List.ofFn fun i => f i (a i)).reverse).prod) =
      ((List.ofFn fun i => finiteMean 𝕜 (f i)).reverse).prod := by
  induction t with
  | zero =>
    simp only [List.ofFn_zero, List.reverse_nil, List.prod_nil]
    exact finiteMean_const 𝕜 1
  | succ t ih =>
    rw [← finiteMean_equiv 𝕜 (Fin.consEquiv A), finiteMean_prod]
    have hc (a : A 0) (b : ∀ i : Fin t, A i.succ) :
        ((List.ofFn fun i => f i (Fin.consEquiv A (a,b) i)).reverse).prod =
          ((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod * f 0 a := by
      rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    simp only [hc]
    have hr (a : A 0) :
        finiteMean 𝕜 (fun b : ∀ i : Fin t, A i.succ =>
          ((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod * f 0 a) =
          ((List.ofFn fun i : Fin t => finiteMean 𝕜 (f i.succ)).reverse).prod * f 0 a := by
      change finiteMean 𝕜 (fun b : ∀ i : Fin t, A i.succ =>
        LinearMap.mulRight 𝕜 (f 0 a)
          (((List.ofFn fun i : Fin t => f i.succ (b i)).reverse).prod)) = _
      rw [← linearMap_finiteMean, ih]
      rfl
    simp only [hr]
    change finiteMean 𝕜 (fun a : A 0 =>
      LinearMap.mulLeft 𝕜
        (((List.ofFn fun i : Fin t => finiteMean 𝕜 (f i.succ)).reverse).prod)
        (f 0 a)) = _
    rw [← linearMap_finiteMean]
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton]
    rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SweepSettings (d : ℕ) := ∀ i : Fin d, coordinateSubgroup d i

def sampleSweep (d : ℕ) (a : SweepSettings d) : SymmetricGroup (2 ^ d) :=
  ((List.ofFn fun i => (a i).1).reverse).prod

lemma representation_sampleSweep_average {𝕜 E : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (d : ℕ) (ρ : Representation 𝕜 (SymmetricGroup (2 ^ d)) E) :
    finiteMean 𝕜 (fun a : SweepSettings d => ρ (sampleSweep d a)) =
      ((List.ofFn fun i : Fin d => (Fintype.card (coordinateSubgroup d i) : 𝕜)⁻¹ •
        ∑ g : coordinateSubgroup d i, ρ g.1).reverse).prod := by
  have he (a : SweepSettings d) : ρ (sampleSweep d a) =
      ((List.ofFn fun i : Fin d => ρ (a i).1).reverse).prod := by
    simp only [sampleSweep, map_list_prod, List.map_reverse, List.map_ofFn, Function.comp_def]
  simp only [he]
  exact finiteMean_reverse_prod d (fun i => coordinateSubgroup d i) (fun i g => ρ g.1)

lemma sweepOperator_eq_sampleMean {d : ℕ} (lam : Partition (2 ^ d)) :
    sweepOperator lam = finiteMean ℂ (fun a : SweepSettings d => spechtRepresentation lam (sampleSweep d a)) :=
  (representation_sampleSweep_average d (spechtRepresentation lam)).symm

lemma tupleSweep_eq_sampleMean (I : Type*) [Fintype I] (d : ℕ) :
    tupleSweep I d = finiteMean ℂ (fun a : SweepSettings d => tupleRepresentation I (2 ^ d) (sampleSweep d a)) :=
  (representation_sampleSweep_average d (tupleRepresentation I (2 ^ d))).symm

lemma subsetSweep_eq_sampleMean (d : ℕ) :
    subsetSweep d = finiteMean ℝ (fun a : SweepSettings d => subsetRepresentation (Fin (2 ^ d)) (sampleSweep d a)) :=
  (representation_sampleSweep_average d (subsetRepresentation (Fin (2 ^ d)))).symm

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.BinaryNetworks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A B C : Type*} (e : C × B ≃ A)

def fiberPiece (g : fiberSubgroup (fun x : A => (e.symm x).1)) (c : C) : Equiv.Perm B where
  toFun b := (e.symm (g.1 (e (c,b)))).2
  invFun b := (e.symm (g.1⁻¹ (e (c,b)))).2
  left_inv b := by
    have hk : (e.symm (g.1 (e (c,b)))).1 = c := by
      simpa using g.property (e (c,b))
    change (e.symm (g.1⁻¹ (e (c, (e.symm (g.1 (e (c,b)))).2)))).2 = b
    have ht : (c, (e.symm (g.1 (e (c,b)))).2) = e.symm (g.1 (e (c,b))) :=
      Prod.ext hk.symm rfl
    rw [ht, Equiv.apply_symm_apply]
    simp
  right_inv b := by
    have hk : (e.symm (g.1⁻¹ (e (c,b)))).1 = c := by
      simpa using ((fiberSubgroup _).inv_mem g.property) (e (c,b))
    change (e.symm (g.1 (e (c, (e.symm (g.1⁻¹ (e (c,b)))).2)))).2 = b
    have ht : (c, (e.symm (g.1⁻¹ (e (c,b)))).2) = e.symm (g.1⁻¹ (e (c,b))) :=
      Prod.ext hk.symm rfl
    rw [ht, Equiv.apply_symm_apply]
    simp

def fiberSettingsEquiv : (C → Equiv.Perm B) ≃ fiberSubgroup (fun x : A => (e.symm x).1) where
  toFun p := ⟨e.permCongr (Equiv.prodCongrRight p), by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl⟩
  invFun g := fiberPiece e g
  left_inv p := by
    funext c
    apply Equiv.ext
    intro b
    change (e.symm ((e.permCongr (Equiv.prodCongrRight p)) (e (c,b)))).2 = _
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongrRight_apply]
  right_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply e.symm.injective
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change ((e.symm x).1, (e.symm (g.1 (e ((e.symm x).1, (e.symm x).2)))).2) = _
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
    have hg : (e.symm (g.1 x)).1 = (e.symm x).1 := g.property x
    rw [← hg, Prod.mk.eta]

@[simp] lemma fiberSettingsEquiv_apply (p : C → Equiv.Perm B) (c : C) (b : B) :
    (fiberSettingsEquiv e p).1 (e (c,b)) = e (c, p c b) := by
  change (e.permCongr (Equiv.prodCongrRight p)) (e (c,b)) = _
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongrRight_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SwitchAddress (d : ℕ) (i : Fin d) := {j : Fin d // j ≠ i} → Fin 2

def switchCoordinates (d : ℕ) (i : Fin d) : SwitchAddress d i × Fin 2 ≃ Fin (2 ^ d) :=
  ((Equiv.prodComm _ _).trans (Equiv.funSplitAt i (Fin 2)).symm).trans (positionsEquiv d)

@[simp] lemma switchCoordinates_symm (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    (switchCoordinates d i).symm x =
      ((fun j => (positionsEquiv d).symm x j.1), (positionsEquiv d).symm x i) := rfl

abbrev LayerSettings (d : ℕ) (i : Fin d) := SwitchAddress d i → Equiv.Perm (Fin 2)

def layerSettingsEquiv (d : ℕ) (i : Fin d) : LayerSettings d i ≃ coordinateSubgroup d i :=
  fiberSettingsEquiv (switchCoordinates d i)

abbrev PhysicalSettings (d : ℕ) := ∀ i : Fin d, LayerSettings d i

def physicalSettingsEquiv (d : ℕ) : PhysicalSettings d ≃ SweepSettings d :=
  Equiv.piCongrRight (layerSettingsEquiv d)

lemma layerSettings_key (d : ℕ) (i : Fin d) (p : LayerSettings d i) (x : Fin (2 ^ d))
    (j : Fin d) (hji : j ≠ i) :
    (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) j =
      (positionsEquiv d).symm x j :=
  congrFun ((layerSettingsEquiv d i p).property x) ⟨j, hji⟩

lemma layerSettings_bit (d : ℕ) (i : Fin d) (p : LayerSettings d i) (x : Fin (2 ^ d)) :
    (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) i =
      p (fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)
        ((positionsEquiv d).symm x i) := by
  have h := fiberSettingsEquiv_apply (switchCoordinates d i) p
    ((switchCoordinates d i).symm x).1 ((switchCoordinates d i).symm x).2
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun y => ((switchCoordinates d i).symm y).2) h
  rw [Equiv.symm_apply_apply] at h'
  change (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) i =
    p (fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)
      ((positionsEquiv d).symm x i) at h'
  exact h'

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.UniquePaths
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sweepPrefix (d : ℕ) (a : SweepSettings d) (t : ℕ) : SymmetricGroup (2 ^ d) :=
  (((List.ofFn fun i => (a i).1).take t).reverse).prod

@[simp] lemma sweepPrefix_zero (d : ℕ) (a : SweepSettings d) : sweepPrefix d a 0 = 1 := by
  simp [sweepPrefix]

@[simp] lemma sweepPrefix_full (d : ℕ) (a : SweepSettings d) :
    sweepPrefix d a d = sampleSweep d a := by
  unfold sweepPrefix sampleSweep
  rw [List.take_of_length_le (by simp)]

lemma sweepPrefix_succ (d : ℕ) (a : SweepSettings d) (t : ℕ) (ht : t < d) :
    sweepPrefix d a (t+1) = (a ⟨t,ht⟩).1 * sweepPrefix d a t := by
  unfold sweepPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using ht), List.reverse_append, List.prod_append]
  simp

lemma coordinateSubgroup_bit {d : ℕ} {i : Fin d} (g : coordinateSubgroup d i)
    (x : Fin (2 ^ d)) (j : Fin d) (hji : j ≠ i) :
    (positionsEquiv d).symm (g.1 x) j = (positionsEquiv d).symm x j :=
  congrFun (g.property x) ⟨j,hji⟩

lemma sweepPrefix_before (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d)) (t : ℕ)
    (ht : t ≤ d) (j : Fin d) (hjt : t ≤ j.1) :
    (positionsEquiv d).symm (sweepPrefix d a t x) j = (positionsEquiv d).symm x j := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sweepPrefix_succ d a t (by omega), Equiv.Perm.mul_apply,
      coordinateSubgroup_bit _ _ j (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)]
    exact ih (by omega) (by omega)

lemma sweepPrefix_after (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d))
    (s t : ℕ) (hts : t ≤ s) (hs : s ≤ d) (j : Fin d) (hjt : j.1 < t) :
    (positionsEquiv d).symm (sweepPrefix d a s x) j =
      (positionsEquiv d).symm (sweepPrefix d a t x) j := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases he : t = s+1
    · simp only [he]
    rw [sweepPrefix_succ d a s (by omega), Equiv.Perm.mul_apply,
      coordinateSubgroup_bit _ _ j (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)]
    exact ih (by omega) (by omega)

def endpointPath (d t : ℕ) (x y : Fin (2 ^ d)) : Fin (2 ^ d) :=
  positionsEquiv d (fun j => if j.1 < t then (positionsEquiv d).symm y j else (positionsEquiv d).symm x j)

@[simp] lemma endpointPath_zero (d : ℕ) (x y : Fin (2 ^ d)) : endpointPath d 0 x y = x := by
  simp [endpointPath]

@[simp] lemma endpointPath_full (d : ℕ) (x y : Fin (2 ^ d)) : endpointPath d d x y = y := by
  simp [endpointPath, Fin.is_lt]

@[simp] lemma endpointPath_bit (d t : ℕ) (x y : Fin (2 ^ d)) (j : Fin d) :
    (positionsEquiv d).symm (endpointPath d t x y) j =
      if j.1 < t then (positionsEquiv d).symm y j else (positionsEquiv d).symm x j := by
  simp [endpointPath]

lemma sweepPrefix_eq_endpointPath (d : ℕ) (a : SweepSettings d) (x : Fin (2 ^ d))
    (t : ℕ) (ht : t ≤ d) :
    sweepPrefix d a t x = endpointPath d t x (sampleSweep d a x) := by
  apply (positionsEquiv d).symm.injective
  funext j
  rw [endpointPath_bit]
  split_ifs with hj
  · rw [← sweepPrefix_full]
    exact (sweepPrefix_after d a x d t ht le_rfl j hj).symm
  · exact sweepPrefix_before d a x t ht j (by omega)

def pathAddress (d : ℕ) (i : Fin d) (x y : Fin (2 ^ d)) : SwitchAddress d i :=
  fun j => (positionsEquiv d).symm (endpointPath d i.1 x y) j.1

lemma layerSettings_endpointPath (d : ℕ) (i : Fin d) (p : LayerSettings d i)
    (x y : Fin (2 ^ d))
    (h : p (pathAddress d i x y) ((positionsEquiv d).symm x i) = (positionsEquiv d).symm y i) :
    (layerSettingsEquiv d i p).1 (endpointPath d i.1 x y) = endpointPath d (i.1+1) x y := by
  apply (positionsEquiv d).symm.injective
  funext j
  by_cases hji : j = i
  · subst j
    rw [layerSettings_bit, endpointPath_bit, endpointPath_bit]
    simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one]
    change p (pathAddress d i x y) ((positionsEquiv d).symm x i) =
      (positionsEquiv d).symm y i
    exact h
  · rw [layerSettings_key d i p _ j hji, endpointPath_bit, endpointPath_bit]
    have hv : j.1 ≠ i.1 := fun he => hji (Fin.ext he)
    by_cases hj : j.1 < i.1 <;> simp only [if_pos, hj, show (j.1 < i.1+1) ↔ (j.1 < i.1) by omega]

lemma sampleSweep_endpoints_iff (d : ℕ) (p : PhysicalSettings d) (x y : Fin (2 ^ d)) :
    sampleSweep d (physicalSettingsEquiv d p) x = y ↔
      ∀ i : Fin d, p i (pathAddress d i x y) ((positionsEquiv d).symm x i) =
        (positionsEquiv d).symm y i := by
  constructor
  · intro h i
    have hpath := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d p) x i.1 (Nat.le_of_lt i.2)
    rw [h] at hpath
    have hnext := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d p) x (i.1+1) i.2
    rw [h, sweepPrefix_succ d (physicalSettingsEquiv d p) i.1 i.2, Equiv.Perm.mul_apply, hpath] at hnext
    have hi := congrArg (fun z => (positionsEquiv d).symm z i) hnext
    change (positionsEquiv d).symm ((layerSettingsEquiv d i (p i)).1 (endpointPath d i.1 x y)) i = _ at hi
    rw [layerSettings_bit, endpointPath_bit, endpointPath_bit] at hi
    simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one] at hi
    change p i (pathAddress d i x y) ((positionsEquiv d).symm x i) =
      (positionsEquiv d).symm y i at hi
    exact hi
  · intro h
    have hp : ∀ t, t ≤ d → sweepPrefix d (physicalSettingsEquiv d p) t x = endpointPath d t x y := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        intro ht
        rw [sweepPrefix_succ d (physicalSettingsEquiv d p) t (by omega), Equiv.Perm.mul_apply,
          ih (by omega)]
        exact layerSettings_endpointPath d ⟨t,by omega⟩ (p _) x y (h _)
    simpa using hp d le_rfl

def endpointEncounter {I : Type*} (d : ℕ) (x y : I → Fin (2 ^ d)) : SimpleGraph I where
  Adj a b := a ≠ b ∧ ∃ i : Fin d, pathAddress d i (x a) (y a) = pathAddress d i (x b) (y b)
  symm := ⟨by rintro a b ⟨hab,i,hi⟩; exact ⟨hab.symm,i,hi.symm⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.FiniteProbability
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def finiteProb {A : Type*} [Fintype A] (P : A → Prop) : ℝ :=
  finiteMean ℝ (fun a => if P a then 1 else 0)

lemma finiteProb_congr {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a ↔ Q a) : finiteProb P = finiteProb Q := by
  unfold finiteProb
  apply finiteMean_congr
  intro a
  simp only [h a]

@[simp] lemma finiteProb_true (A : Type*) [Fintype A] [Nonempty A] :
    finiteProb (fun _ : A => True) = 1 := by
  simp only [finiteProb, ↓reduceIte]
  exact finiteMean_const ℝ 1

@[simp] lemma finiteProb_false (A : Type*) [Fintype A] :
    finiteProb (fun _ : A => False) = 0 := by
  simp [finiteProb, finiteMean]

lemma finiteProb_nonneg {A : Type*} [Fintype A] (P : A → Prop) : 0 ≤ finiteProb P := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> norm_num)

lemma finiteProb_mono {A : Type*} [Fintype A] {P Q : A → Prop}
    (h : ∀ a, P a → Q a) : finiteProb P ≤ finiteProb Q := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : P a
  · simp only [if_pos hp, if_pos (h a hp), le_refl]
  · simp only [if_neg hp]
    split_ifs <;> norm_num

lemma finiteProb_pi_forall {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)]
    (P : ∀ i, A i → Prop) :
    finiteProb (fun a : ∀ i, A i => ∀ i, P i (a i)) = ∏ i, finiteProb (P i) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, Fintype.card_pi, Nat.cast_prod]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ∀ i, P i (a i)
  · simp [h]
  · rw [if_neg h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma univ_perms_fin_two : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
    {1, Equiv.swap 0 1} := by
  symm
  apply Finset.eq_univ_of_card
  have hs : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hz := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) h
    norm_num at hz
  simp [hs, Fintype.card_perm]

lemma finiteProb_bit_switch (a b : Fin 2) :
    finiteProb (fun p : Equiv.Perm (Fin 2) => p a = b) = 1 / 2 := by
  unfold finiteProb finiteMean
  rw [univ_perms_fin_two]
  have hs : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro h
    have hz := congrArg (fun p : Equiv.Perm (Fin 2) => p 0) h
    norm_num at hz
  fin_cases a <;> fin_cases b <;> norm_num [hs, Fintype.card_perm]

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarginalKernels
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}

lemma marginal_kernel_eq_zero (e : J ↪ I)
    (K : InjectiveTuple I n → InjectiveTuple J n → ℝ)
    (f : TupleSpace I n) (hf : tupleMarginal e f = 0) :
    kernelOperator (fun x y : InjectiveTuple I n => K x (e.trans y)) f = 0 := by
  apply PiLp.ext
  intro x
  change (∑ y, (K x (e.trans y) : ℂ) * f y) = 0
  calc
    _ = ∑ z : InjectiveTuple J n, (K x z : ℂ) * tupleMarginal e f z := by
      change _ = ∑ z : InjectiveTuple J n, (K x z : ℂ) *
        ∑ y, if e.trans y = z then f y else 0
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = 0 := by simp only [hf, PiLp.zero_apply, mul_zero, Finset.sum_const_zero]

lemma specht_marginal_kernel_eq_zero {n : ℕ} (lam : Partition n)
    {J : Type*} [Fintype J] (e : J ↪ OffFirstRow lam)
    (he : Fintype.card J < n - lam.1.rowLen 0)
    (K : InjectiveTuple (OffFirstRow lam) n → InjectiveTuple J n → ℝ)
    (f : Specht lam) :
    kernelOperator (fun x y => K x (e.trans y)) (tupleRealization lam f) = 0 :=
  marginal_kernel_eq_zero e K _ (tupleRealization_marginal_eq_zero lam e he f)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma alternating_subsets_cancel (F : Finset I → ℝ) (i : I)
    (hF : ∀ A : Finset I, i ∉ A → F (insert i A) = F A) :
    (∑ A : Finset I, (-1 : ℝ) ^ A.card * F A) = 0 := by
  have hu : (Finset.univ : Finset (Finset I)) = (insert i ((Finset.univ : Finset I).erase i)).powerset := by
    simp only [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro A hA
  have hi : i ∉ A := by
    exact fun h => (Finset.notMem_erase i Finset.univ) ((Finset.mem_powerset.mp hA) h)
  rw [Finset.card_insert_of_notMem hi, pow_succ, hF A hi]
  ring

def differenceKernel {X Y : Type*} (K : Finset I → X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  (-1 : ℝ) ^ Fintype.card I * ∑ A : Finset I, (-1 : ℝ) ^ A.card * K A x y

lemma differenceKernel_vanishes_of_isolate {X Y : Type*}
    (K : Finset I → X → Y → ℝ) (x : X) (y : Y) (i : I)
    (hi : ∀ A : Finset I, i ∉ A → K (insert i A) x y = K A x y) :
    differenceKernel K x y = 0 := by
  rw [differenceKernel, alternating_subsets_cancel (fun A => K A x y) i hi, mul_zero]

omit [DecidableEq I] in
lemma differenceKernel_action {X : Type*} [Fintype X]
    (K : Finset I → X → X → ℝ) (f : EuclideanSpace ℂ X)
    (hproper : ∀ A : Finset I, A ≠ Finset.univ → kernelOperator (K A) f = 0) :
    kernelOperator (differenceKernel K) f = kernelOperator (K Finset.univ) f := by
  apply PiLp.ext
  intro x
  change (∑ y, (differenceKernel K x y : ℂ) * f y) = _
  simp only [differenceKernel, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (A : Finset I) :
      (∑ y : X, ((-1 : ℂ) ^ Fintype.card I * ((-1) ^ A.card * (K A x y : ℂ))) * f y) =
      (-1 : ℂ) ^ Fintype.card I * (-1) ^ A.card * kernelOperator (K A) f x := by
    rw [kernelOperator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [he]
  rw [Finset.sum_eq_single Finset.univ]
  · have hs : (-1 : ℂ) ^ Fintype.card I * (-1) ^ (Finset.univ : Finset I).card = 1 := by
      rw [Finset.card_univ, ← mul_pow]
      norm_num
    rw [hs, one_mul]
  · intro A _ hA
    rw [hproper A hA]
    simp
  · simp

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.EndpointKernels
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ)

def sweepEndpointProb (A : Finset I) (x y : I → Fin (2 ^ d)) : ℝ :=
  finiteProb (fun p : PhysicalSettings d => ∀ a ∈ A,
    sampleSweep d (physicalSettingsEquiv d p) (x a) = y a)

def switchConstraintProb (i : Fin d) (c : SwitchAddress d i) (A : Finset I)
    (x y : I → Fin (2 ^ d)) : ℝ :=
  finiteProb (fun p : Equiv.Perm (Fin 2) => ∀ a ∈ A,
    pathAddress d i (x a) (y a) = c → p ((positionsEquiv d).symm (x a) i) =
      (positionsEquiv d).symm (y a) i)

omit [Fintype I] [DecidableEq I] in
lemma sweepEndpointProb_eq_product (A : Finset I) (x y : I → Fin (2 ^ d)) :
    sweepEndpointProb d A x y =
      ∏ i : Fin d, ∏ c : SwitchAddress d i, switchConstraintProb d i c A x y := by
  unfold sweepEndpointProb
  have he : finiteProb (fun p : PhysicalSettings d => ∀ a ∈ A,
      sampleSweep d (physicalSettingsEquiv d p) (x a) = y a) =
      finiteProb (fun p : PhysicalSettings d => ∀ i : Fin d, ∀ c : SwitchAddress d i,
        ∀ a ∈ A, pathAddress d i (x a) (y a) = c →
          p i c ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i) := by
    apply finiteProb_congr
    intro p
    constructor
    · intro h i c a ha hc
      rw [← hc]
      exact (sampleSweep_endpoints_iff d p (x a) (y a)).mp (h a ha) i
    · intro h a ha
      apply (sampleSweep_endpoints_iff d p (x a) (y a)).mpr
      intro i
      exact h i _ a ha rfl
  refine he.trans ((finiteProb_pi_forall (fun i : Fin d => LayerSettings d i)
    (fun i p => ∀ c : SwitchAddress d i, ∀ a ∈ A,
      pathAddress d i (x a) (y a) = c →
        p c ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i)).trans ?_)
  apply Finset.prod_congr rfl
  intro i _
  exact finiteProb_pi_forall (fun _ : SwitchAddress d i => Equiv.Perm (Fin 2))
    (fun c p => ∀ a ∈ A, pathAddress d i (x a) (y a) = c →
      p ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i)

omit [Fintype I] in
lemma switchConstraintProb_insert (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I) (i : Fin d) (c : SwitchAddress d i)
    (hiso : ∀ b ∈ A, pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    switchConstraintProb d i c (insert a A) x y =
      (if c = pathAddress d i (x a) (y a) then (1 / 2 : ℝ) else 1) *
        switchConstraintProb d i c A x y := by
  by_cases hc : c = pathAddress d i (x a) (y a)
  · subst c
    have hb : switchConstraintProb d i (pathAddress d i (x a) (y a)) A x y = 1 := by
      calc
        _ = finiteProb (fun _ : Equiv.Perm (Fin 2) => True) := by
          apply finiteProb_congr
          intro p
          constructor
          · intro _; trivial
          · intro _ b hb hab
            exact False.elim (hiso b hb hab.symm)
        _ = 1 := finiteProb_true _
    have ha : switchConstraintProb d i (pathAddress d i (x a) (y a)) (insert a A) x y = 1 / 2 := by
      calc
        _ = finiteProb (fun p : Equiv.Perm (Fin 2) =>
            p ((positionsEquiv d).symm (x a) i) = (positionsEquiv d).symm (y a) i) := by
          apply finiteProb_congr
          intro p
          constructor
          · intro h
            exact h a (Finset.mem_insert_self _ _) rfl
          · intro h b hb hab
            rcases Finset.mem_insert.mp hb with rfl | hb
            · exact h
            · exact False.elim (hiso b hb hab.symm)
        _ = 1 / 2 := finiteProb_bit_switch _ _
    rw [ha, hb, if_pos rfl, mul_one]
  · rw [if_neg hc, one_mul]
    apply finiteProb_congr
    intro p
    constructor
    · intro h b hb
      exact h b (Finset.mem_insert_of_mem hb)
    · intro h b hb hab
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact False.elim (hc hab.symm)
      · exact h b hb hab

omit [Fintype I] in
theorem sweepEndpointProb_insert_isolated (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I)
    (hiso : ∀ b ∈ A, ∀ i : Fin d,
      pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    sweepEndpointProb d (insert a A) x y = ((2 ^ d : ℕ) : ℝ)⁻¹ * sweepEndpointProb d A x y := by
  rw [sweepEndpointProb_eq_product, sweepEndpointProb_eq_product]
  have hi (i : Fin d) :
      (∏ c : SwitchAddress d i, switchConstraintProb d i c (insert a A) x y) =
        (1 / 2 : ℝ) * ∏ c : SwitchAddress d i, switchConstraintProb d i c A x y := by
    simp_rw [switchConstraintProb_insert d A x y a i _ (fun b hb => hiso b hb i)]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  simp only [one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]

def normalizedEndpointProb (A : Finset I) (x y : I → Fin (2 ^ d)) : ℝ :=
  (2 ^ d : ℕ) ^ A.card * sweepEndpointProb d A x y

omit [Fintype I] in
lemma normalizedEndpointProb_insert_isolated (A : Finset I) (x y : I → Fin (2 ^ d))
    (a : I) (ha : a ∉ A)
    (hiso : ∀ b ∈ A, ∀ i : Fin d,
      pathAddress d i (x a) (y a) ≠ pathAddress d i (x b) (y b)) :
    normalizedEndpointProb d (insert a A) x y = normalizedEndpointProb d A x y := by
  unfold normalizedEndpointProb
  rw [Finset.card_insert_of_notMem ha, pow_succ, sweepEndpointProb_insert_isolated d A x y a hiso]
  have hn : ((2 ^ d : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

def subsetEndpointKernel (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) : ℝ :=
  ((2 ^ d : ℕ) ^ Fintype.card I : ℝ)⁻¹ * normalizedEndpointProb d A x y

omit [DecidableEq I] in
lemma subsetEndpointKernel_nonneg (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    0 ≤ subsetEndpointKernel d A x y := by
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (finiteProb_nonneg _))

omit [DecidableEq I] in
lemma subsetEndpointKernel_full (x y : InjectiveTuple I (2 ^ d)) :
    subsetEndpointKernel d Finset.univ x y = sweepEndpointProb d Finset.univ x y := by
  unfold subsetEndpointKernel normalizedEndpointProb
  rw [Finset.card_univ, ← mul_assoc, inv_mul_cancel₀, one_mul]
  positivity

theorem sweep_differenceKernel_vanishes_of_isolate
    (x y : InjectiveTuple I (2 ^ d)) (a : I)
    (hiso : ∀ b, ¬(endpointEncounter d x y).Adj a b) :
    differenceKernel (subsetEndpointKernel d) x y = 0 := by
  apply differenceKernel_vanishes_of_isolate _ x y a
  intro A ha
  unfold subsetEndpointKernel
  rw [normalizedEndpointProb_insert_isolated d A x y a ha]
  intro b hb i hab
  apply hiso b
  exact ⟨fun hab => ha (hab ▸ hb), i, hab⟩

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.KernelTransition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma unitary_representation_adjoint {G : Type*} [Group G] (ρ : Representation ℂ G E)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  exact representation_inner_inverse ρ hρ g y x

lemma adjoint_finiteMean {A : Type*} [Fintype A] (T : A → E →ₗ[ℂ] E) :
    (finiteMean ℂ T).adjoint = finiteMean ℂ (fun a => (T a).adjoint) := by
  simp only [finiteMean, map_smulₛₗ, map_sum, map_inv₀, map_natCast]

lemma unitary_finiteMean_adjoint {G A : Type*} [Group G] [Fintype A]
    (ρ : Representation ℂ G E) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (f : A → G) :
    (finiteMean ℂ (fun a => ρ (f a))).adjoint = finiteMean ℂ (fun a => ρ ((f a)⁻¹)) := by
  rw [adjoint_finiteMean]
  apply finiteMean_congr
  intro a
  exact unitary_representation_adjoint ρ hρ _

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_kernel_apply {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (f : X → ℂ) :
    (∑ y, (finiteProb (fun a => s a = y) : ℂ) * f y) = finiteMean ℂ (fun a => f (s a)) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma tupleRepresentation_norm {I : Type*} [Fintype I] {n : ℕ}
    (g : SymmetricGroup n) (f : TupleSpace I n) :
    ‖tupleRepresentation I n g f‖ = ‖f‖ := (tupleIsometry g).norm_map f

theorem tupleSweep_adjoint_eq_endpointKernel {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) :
    (tupleSweep I d).adjoint = kernelOperator (subsetEndpointKernel (I := I) d Finset.univ) := by
  rw [tupleSweep_eq_sampleMean, ← finiteMean_equiv ℂ (physicalSettingsEquiv d)
    (fun a => tupleRepresentation I (2 ^ d) (sampleSweep d a))]
  rw [unitary_finiteMean_adjoint (tupleRepresentation I (2 ^ d))
    (fun g f => tupleRepresentation_norm g f)]
  ext f x
  change (finiteMean ℂ (fun p : PhysicalSettings d =>
      tupleRepresentation I (2 ^ d) (sampleSweep d (physicalSettingsEquiv d p))⁻¹) f) x = _
  have hk (y : InjectiveTuple I (2 ^ d)) : subsetEndpointKernel d Finset.univ x y =
      finiteProb (fun p : PhysicalSettings d =>
        tupleEquiv (sampleSweep d (physicalSettingsEquiv d p)) x = y) := by
    rw [subsetEndpointKernel_full]
    apply finiteProb_congr
    intro p
    simp only [Finset.mem_univ, forall_true_left]
    constructor
    · intro h
      exact Function.Embedding.ext h
    · intro h a
      exact congrArg (fun t : InjectiveTuple I (2 ^ d) => t a) h
  rw [kernelOperator_apply]
  simp only [hk]
  rw [finiteProb_kernel_apply]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, PiLp.smul_apply,
    WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul, tupleRepresentation_apply, inv_inv]

lemma tupleRealization_intertwines_adjoint_sweep {d : ℕ} (lam : Partition (2 ^ d))
    (v : Specht lam) :
    tupleRealization lam ((sweepOperator lam).adjoint v) =
      (tupleSweep (OffFirstRow lam) d).adjoint (tupleRealization lam v) := by
  rw [sweepOperator_eq_sampleMean, tupleSweep_eq_sampleMean,
    unitary_finiteMean_adjoint (spechtRepresentation lam)
      (fun g f => spechtRepresentation_norm lam g f),
    unitary_finiteMean_adjoint (tupleRepresentation (OffFirstRow lam) (2 ^ d))
      (fun g f => tupleRepresentation_norm g f)]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    tupleRealization_intertwines]

theorem sweep_norm_le_of_adjoint_tuple_bound {d : ℕ} (lam : Partition (2 ^ d))
    {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ v : Specht lam, ‖(tupleSweep (OffFirstRow lam) d).adjoint (tupleRealization lam v)‖ ≤
      a * ‖tupleRealization lam v‖) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤ a := by
  have hn : ‖(sweepOperator lam).adjoint.toContinuousLinearMap‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_bound _ ha
    intro v
    change ‖(sweepOperator lam).adjoint v‖ ≤ a * ‖v‖
    have hh := h v
    rw [← tupleRealization_intertwines_adjoint_sweep] at hh
    have hc : (0 : ℝ) < Fintype.card (firstRowStabilizer lam) := by exact_mod_cast Fintype.card_pos
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hc.le
    rw [mul_pow, ← mul_assoc, mul_comm (Fintype.card (firstRowStabilizer lam) : ℝ) (a ^ 2),
      mul_assoc, ← tupleRealization_norm_sq, ← tupleRealization_norm_sq] at hs
    nlinarith [norm_nonneg ((sweepOperator lam).adjoint v), norm_nonneg v,
      mul_nonneg ha (norm_nonneg v)]
  rwa [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map] at hn

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MaskedKernels
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma proper_endpointKernel_annihilates {d : ℕ} (lam : Partition (2 ^ d))
    (A : Finset (OffFirstRow lam)) (hA : A ≠ Finset.univ) (v : Specht lam) :
    kernelOperator (subsetEndpointKernel d A) (tupleRealization lam v) = 0 := by
  let e : A ↪ OffFirstRow lam := Function.Embedding.subtype _
  let K := fun (x : InjectiveTuple (OffFirstRow lam) (2 ^ d)) (z : InjectiveTuple A (2 ^ d)) =>
    ((2 ^ d : ℕ) ^ Fintype.card (OffFirstRow lam) : ℝ)⁻¹ *
      ((2 ^ d : ℕ) ^ A.card * finiteProb (fun p : PhysicalSettings d =>
        ∀ a : A, sampleSweep d (physicalSettingsEquiv d p) (x a.1) = z a))
  have hcard : Fintype.card A < 2 ^ d - lam.1.rowLen 0 := by
    rw [Fintype.card_coe, ← card_offFirstRow]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  have hK : subsetEndpointKernel d A = fun x y => K x (e.trans y) := by
    funext x y
    unfold subsetEndpointKernel normalizedEndpointProb sweepEndpointProb K
    congr 2
    apply finiteProb_congr
    intro p
    exact ⟨fun h a => h a.1 a.2, fun h a ha => h ⟨a,ha⟩⟩
  rw [hK]
  exact specht_marginal_kernel_eq_zero lam e hcard K v

lemma differenceKernel_apply_eq_sum {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (K : Finset I → X → X → ℝ) (f : EuclideanSpace ℂ X) :
    kernelOperator (differenceKernel K) f = ∑ A : Finset I,
      (((-1 : ℝ) ^ Fintype.card I * (-1) ^ A.card : ℝ) : ℂ) • kernelOperator (K A) f := by
  apply PiLp.ext
  intro x
  simp only [kernelOperator_apply, differenceKernel, Complex.ofReal_mul, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_mul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro y _
  ring

def maskedEndpointKernel {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) (A : Finset I)
    (x y : InjectiveTuple I (2 ^ d)) : ℝ :=
  if NoIsolatedVertex (endpointEncounter d x y) Finset.univ then subsetEndpointKernel d A x y else 0

lemma maskedEndpointKernel_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (d : ℕ) (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    0 ≤ maskedEndpointKernel d A x y := by
  unfold maskedEndpointKernel
  split_ifs
  · exact subsetEndpointKernel_nonneg d A x y
  · exact le_rfl

lemma differenceKernel_masked {I : Type*} [Fintype I] [DecidableEq I] (d : ℕ) :
    differenceKernel (maskedEndpointKernel (I := I) d) = differenceKernel (subsetEndpointKernel d) := by
  funext x y
  by_cases h : NoIsolatedVertex (endpointEncounter d x y) Finset.univ
  · simp only [differenceKernel, maskedEndpointKernel, if_pos h]
  · have hx : ∃ a, ∀ b, ¬ (endpointEncounter d x y).Adj a b := by
      simpa only [NoIsolatedVertex, Finset.mem_univ, true_and, forall_true_left,
        not_forall, not_exists] using h
    obtain ⟨a,ha⟩ := hx
    rw [sweep_differenceKernel_vanishes_of_isolate d x y a ha]
    simp only [differenceKernel, maskedEndpointKernel, if_neg h, mul_zero, Finset.sum_const_zero]

theorem sweep_norm_le_of_masked_rows {d : ℕ} (lam : Partition (2 ^ d))
    {p : ℝ} (hp : 0 ≤ p)
    (hrow : ∀ A : Finset (OffFirstRow lam), ∀ x : InjectiveTuple (OffFirstRow lam) (2 ^ d),
      (∑ z, ∑ y, maskedEndpointKernel d A x y * maskedEndpointKernel d A z y) ≤ p) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
      2 ^ (2 ^ d - lam.1.rowLen 0) * Real.sqrt p := by
  apply sweep_norm_le_of_adjoint_tuple_bound lam (by positivity)
  intro v
  rw [tupleSweep_adjoint_eq_endpointKernel,
    ← differenceKernel_action (subsetEndpointKernel d) _ (fun A hA => proper_endpointKernel_annihilates lam A hA v),
    ← differenceKernel_masked d, differenceKernel_apply_eq_sum]
  have hn (A : Finset (OffFirstRow lam)) :
      ‖(kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap‖ ≤ Real.sqrt p := by
    have hs := nonnegative_kernel_opNorm_sq_le (maskedEndpointKernel d A)
      (maskedEndpointKernel_nonneg d A) hp (hrow A)
    nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg p, norm_nonneg (kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap]
  calc
    _ ≤ ∑ A : Finset (OffFirstRow lam),
        ‖((((-1 : ℝ) ^ Fintype.card (OffFirstRow lam) * (-1) ^ A.card : ℝ) : ℂ) •
          kernelOperator (maskedEndpointKernel d A) (tupleRealization lam v))‖ := norm_sum_le _ _
    _ = ∑ A : Finset (OffFirstRow lam), ‖kernelOperator (maskedEndpointKernel d A) (tupleRealization lam v)‖ := by
      apply Finset.sum_congr rfl
      intro A _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
      norm_num
    _ ≤ ∑ _A : Finset (OffFirstRow lam), Real.sqrt p * ‖tupleRealization lam v‖ := by
      apply Finset.sum_le_sum
      intro A _
      exact ((kernelOperator (maskedEndpointKernel d A)).toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hn A) (norm_nonneg _))
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_finset, card_offFirstRow]
      push_cast
      ring

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.PermutationRows
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_real_kernel_apply {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (f : X → ℝ) :
    (∑ y, finiteProb (fun a => s a = y) * f y) = finiteMean ℝ (fun a => f (s a)) := by
  simp only [finiteProb, finiteMean, smul_eq_mul, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma finiteMean_comm {A B : Type*} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    finiteMean ℝ (fun a => finiteMean ℝ (fun b => f a b)) =
      finiteMean ℝ (fun b => finiteMean ℝ (fun a => f a b)) := by
  simp only [finiteMean, smul_eq_mul, ← Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  ring

lemma finiteMean_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    finiteMean ℝ f ≤ finiteMean ℝ g := by
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a))
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A X : Type*} [Fintype A] [Fintype X]

def maskedPermutationKernel (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) : ℝ :=
  if R x y then finiteProb (fun a => f a x = y) else 0

omit [Fintype X] in
lemma maskedPermutationKernel_nonneg [Fintype X] (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) :
    0 ≤ maskedPermutationKernel f R x y := by
  unfold maskedPermutationKernel
  split_ifs
  · exact finiteProb_nonneg _
  · exact le_rfl

omit [Fintype X] in
lemma maskedPermutationKernel_le [Fintype X] (f : A → Equiv.Perm X) (R : X → X → Prop) (x y : X) :
    maskedPermutationKernel f R x y ≤ finiteProb (fun a => f a x = y) := by
  unfold maskedPermutationKernel
  split_ifs
  · exact le_rfl
  · exact finiteProb_nonneg _

lemma maskedPermutationKernel_transpose_sum (f : A → Equiv.Perm X) (R : X → X → Prop) (y : X) :
    (∑ z, maskedPermutationKernel f R z y) =
      finiteProb (fun a => R ((f a).symm y) y) := by
  have he (z : X) : finiteProb (fun a => f a z = y) =
      finiteProb (fun a => (f a).symm y = z) := by
    apply finiteProb_congr
    intro a
    exact ⟨fun h => by rw [← h, Equiv.symm_apply_apply], fun h => by rw [← h, Equiv.apply_symm_apply]⟩
  have hz (z : X) : maskedPermutationKernel f R z y =
      finiteProb (fun a => (f a).symm y = z) * (if R z y then 1 else 0) := by
    unfold maskedPermutationKernel
    rw [he]
    split_ifs <;> ring
  simp only [hz]
  exact finiteProb_real_kernel_apply (fun a => (f a).symm y) (fun z => if R z y then 1 else 0)

theorem maskedPermutationKernel_square_row_le
    (f : A → Equiv.Perm X) (R : X → X → Prop) (x : X) :
    (∑ z, ∑ y, maskedPermutationKernel f R x y * maskedPermutationKernel f R z y) ≤
      finiteMean ℝ (fun b => finiteProb (fun a => R ((f b).symm (f a x)) (f a x))) := by
  calc
    _ ≤ ∑ z, ∑ y, finiteProb (fun a => f a x = y) * maskedPermutationKernel f R z y := by
      apply Finset.sum_le_sum
      intro z _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_right (maskedPermutationKernel_le f R x y)
        (maskedPermutationKernel_nonneg f R z y)
    _ = ∑ y, finiteProb (fun a => f a x = y) * finiteProb (fun b => R ((f b).symm y) y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, maskedPermutationKernel_transpose_sum]
    _ = finiteMean ℝ (fun a => finiteProb (fun b => R ((f b).symm (f a x)) (f a x))) :=
      finiteProb_real_kernel_apply _ _
    _ = _ := finiteMean_comm _

lemma nonnegative_kernel_restricted_row_le {Y : Type*} [Fintype Y]
    (e : Y ↪ X) (K : X → X → ℝ) (hK : ∀ x y, 0 ≤ K x y) (x : Y) :
    (∑ z : Y, ∑ y : Y, K (e x) (e y) * K (e z) (e y)) ≤
      ∑ z : X, ∑ y : X, K (e x) y * K z y := by
  apply finite_sum_le_of_injective e e.injective
  · intro z
    apply finite_sum_le_of_injective e e.injective
    · intro y
      exact le_rfl
    · intro y
      exact mul_nonneg (hK _ _) (hK _ _)
  · intro z
    exact Finset.sum_nonneg (fun y _ => mul_nonneg (hK _ _) (hK _ _))

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MixedNetworks
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma sampleSweep_uniform (d : ℕ) (x y : Fin (2 ^ d)) :
    finiteProb (fun p : PhysicalSettings d => sampleSweep d (physicalSettingsEquiv d p) x = y) =
      ((2 ^ d : ℕ) : ℝ)⁻¹ := by
  have h := sweepEndpointProb_insert_isolated (I := Unit) d ∅ (fun _ => x) (fun _ => y)
    () (by simp)
  have hz : sweepEndpointProb d (∅ : Finset Unit) (fun _ => x) (fun _ => y) = 1 := by
    simp [sweepEndpointProb]
  rw [hz, mul_one] at h
  convert h using 1
  unfold sweepEndpointProb
  apply finiteProb_congr
  intro p
  simp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SubsetNetwork (A : Finset I) := Option {a : I // a ∉ A}

def labelNetwork (A : Finset I) (i : I) : SubsetNetwork A :=
  if h : i ∈ A then none else some ⟨i,h⟩

omit [Fintype I] in
@[simp] lemma labelNetwork_of_mem (A : Finset I) {i : I} (hi : i ∈ A) : labelNetwork A i = none := by
  simp only [labelNetwork, dif_pos hi]

omit [Fintype I] in
@[simp] lemma labelNetwork_of_notMem (A : Finset I) {i : I} (hi : i ∉ A) :
    labelNetwork A i = some ⟨i,hi⟩ := by simp only [labelNetwork, dif_neg hi]

def mixedNetworkPermutation (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) : Equiv.Perm (I → Fin (2 ^ d)) :=
  Equiv.piCongrRight (fun i => sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))))

omit [Fintype I] in
@[simp] lemma mixedNetworkPermutation_apply (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) (x : I → Fin (2 ^ d)) (i : I) :
    mixedNetworkPermutation d A p x i =
      sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))) (x i) := rfl

omit [Fintype I] in
@[simp] lemma mixedNetworkPermutation_symm_apply (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) (x : I → Fin (2 ^ d)) (i : I) :
    (mixedNetworkPermutation d A p).symm x i =
      (sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i)))).symm (x i) := rfl

theorem subsetEndpointKernel_eq_mixedProb (d : ℕ) (A : Finset I)
    (x y : InjectiveTuple I (2 ^ d)) :
    subsetEndpointKernel d A x y = finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      mixedNetworkPermutation d A p x = y) := by
  let P : SubsetNetwork A → PhysicalSettings d → Prop := fun j p => match j with
    | none => ∀ i ∈ A, sampleSweep d (physicalSettingsEquiv d p) (x i) = y i
    | some i => sampleSweep d (physicalSettingsEquiv d p) (x i.1) = y i.1
  have he : finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      mixedNetworkPermutation d A p x = y) = ∏ j : SubsetNetwork A, finiteProb (P j) := by
    calc
      _ = finiteProb (fun p : SubsetNetwork A → PhysicalSettings d => ∀ j, P j (p j)) := by
        apply finiteProb_congr
        intro p
        constructor
        · intro h j
          have h' := congrFun h
          cases j with
          | none =>
            intro i hi
            simpa only [mixedNetworkPermutation_apply, labelNetwork_of_mem A hi] using h' i
          | some a =>
            change sampleSweep d (physicalSettingsEquiv d (p (some a))) (x a.1) = y a.1
            simpa only [mixedNetworkPermutation_apply, labelNetwork_of_notMem A a.2] using h' a.1
        · intro h
          funext i
          by_cases hi : i ∈ A
          · simpa only [mixedNetworkPermutation_apply, labelNetwork_of_mem A hi] using h none i hi
          · simpa only [mixedNetworkPermutation_apply, labelNetwork_of_notMem A hi] using h (some ⟨i,hi⟩)
      _ = _ := finiteProb_pi_forall (fun _ => PhysicalSettings d) P
  rw [he, Fintype.prod_option]
  change _ = sweepEndpointProb d A x y * ∏ i : {a : I // a ∉ A},
    finiteProb (fun p : PhysicalSettings d => sampleSweep d (physicalSettingsEquiv d p) (x i.1) = y i.1)
  simp only [sampleSweep_uniform, Finset.prod_const, Finset.card_univ]
  have hc : Fintype.card {a : I // a ∉ A} = Fintype.card I - A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun a => a ∈ A)
  rw [hc]
  unfold subsetEndpointKernel normalizedEndpointProb
  have hn : (((2 ^ d : ℕ) : ℝ)) ≠ 0 := by positivity
  have hp : (((2 ^ d : ℕ) : ℝ)) ^ Fintype.card I =
      (((2 ^ d : ℕ) : ℝ)) ^ A.card * (((2 ^ d : ℕ) : ℝ)) ^ (Fintype.card I - A.card) := by
    rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_univ A)]
  rw [hp, inv_pow]
  field_simp

lemma maskedEndpointKernel_eq_mixed (d : ℕ) (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    maskedEndpointKernel d A x y =
      maskedPermutationKernel (mixedNetworkPermutation d A)
        (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ) x y := by
  unfold maskedEndpointKernel maskedPermutationKernel
  rw [subsetEndpointKernel_eq_mixedProb]

def networkInitialSubsets {n : ℕ} (A : Finset I) (x : InjectiveTuple I n) : SubsetNetwork A → Finset (Fin n)
  | none => A.image x
  | some i => {x i.1}

lemma networkInitialSubsets_total {n : ℕ} (A : Finset I) (x : InjectiveTuple I n) :
    (∑ j : SubsetNetwork A, (networkInitialSubsets A x j).card) = Fintype.card I := by
  rw [Fintype.sum_option]
  change (A.image x).card + (∑ _ : {a : I // a ∉ A}, ({x _} : Finset (Fin n)).card) = _
  simp only [Finset.card_image_of_injective A x.injective, Finset.card_singleton,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have hc : Fintype.card {a : I // a ∉ A} = Fintype.card I - A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun a => a ∈ A)
  rw [hc]
  exact Nat.add_sub_of_le (Finset.card_le_univ A)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.NetworkSampling
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma sweptSubsetLaw_eq_sampleProb (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    sweptSubsetLaw d S T = finiteProb (fun p : PhysicalSettings d =>
      S.image (sampleSweep d (physicalSettingsEquiv d p)) = T) := by
  unfold sweptSubsetLaw
  rw [subsetSweep_eq_sampleMean, ← finiteMean_equiv ℝ (physicalSettingsEquiv d)
    (fun a => subsetRepresentation (Fin (2 ^ d)) (sampleSweep d a))]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, subsetRepresentation, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  unfold finiteProb finiteMean
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have h : T.image ((sampleSweep d (physicalSettingsEquiv d p))⁻¹ : SymmetricGroup (2 ^ d)) = S ↔
      S.image (sampleSweep d (physicalSettingsEquiv d p)) = T := by
    constructor
    · intro h
      rw [← h, Finset.image_image]
      simp only [Function.comp_def, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Finset.image_id']
    · intro h
      rw [← h, Finset.image_image]
      simp only [Function.comp_def, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Finset.image_id']
  simp only [h]
  split_ifs <;> rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def independentSampleSubset (S : J → Finset (Fin (2 ^ d))) (p : J → PhysicalSettings d) :
    Finset (J × Fin (2 ^ d)) :=
  subsetFiberEquiv.symm (fun j => (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))))

lemma fiber_independentSampleSubset (S : J → Finset (Fin (2 ^ d))) (p : J → PhysicalSettings d) (j : J) :
    subsetFiber (independentSampleSubset S p) j =
      (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))) := by
  exact congrFun (subsetFiberEquiv.apply_symm_apply _) j

lemma independentSampleSubset_law (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    finiteProb (fun p : J → PhysicalSettings d => independentSampleSubset S p = T) = independentSweptLaw S T := by
  calc
    _ = finiteProb (fun p : J → PhysicalSettings d => ∀ j,
        (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))) = subsetFiber T j) := by
      apply finiteProb_congr
      intro p
      constructor
      · intro h j
        rw [← fiber_independentSampleSubset, h]
      · intro h
        apply subsetFiberEquiv.injective
        funext j
        rw [show subsetFiberEquiv (independentSampleSubset S p) j = _ from fiber_independentSampleSubset S p j]
        exact h j
    _ = ∏ j, finiteProb (fun p : PhysicalSettings d =>
        (S j).image (sampleSweep d (physicalSettingsEquiv d p)) = subsetFiber T j) :=
      finiteProb_pi_forall (fun _ : J => PhysicalSettings d) (fun j p =>
        (S j).image (sampleSweep d (physicalSettingsEquiv d p)) = subsetFiber T j)
    _ = _ := by
      simp only [← sweptSubsetLaw_eq_sampleProb, independentSweptLaw, independentSubsetLaw]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_eq_sum_fibers {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (R : X → Prop) :
    finiteProb (fun a => R (s a)) = ∑ x : {x : X // R x}, finiteProb (fun a => s a = x.1) := by
  have h := finiteProb_real_kernel_apply s (fun x => if R x then 1 else 0)
  change _ = finiteProb (fun a => R (s a)) at h
  rw [← h, ← Finset.sum_subtype (Finset.univ.filter R) (by simp) (fun x => finiteProb (fun a => s a = x))]
  simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem independentSampleSubset_noIsolates_bound {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (S : J → Finset (Fin (2 ^ d)))
    (k : ℕ) (hk : k = ∑ j, (S j).card)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    finiteProb (fun p : J → PhysicalSettings d => NoIsolatedVertex (encounterGraph state)
      (independentSampleSubset S p)) ≤
        (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  rw [finiteProb_eq_sum_fibers]
  simp only [independentSampleSubset_law]
  exact swept_network_noIsolates_bound state S k hk hΔ hΔ1

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ReverseEncounters
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma labelNetwork_eq_none_iff (A : Finset I) (i : I) : labelNetwork A i = none ↔ i ∈ A := by
  unfold labelNetwork
  split_ifs with hi <;> simp [hi]

omit [Fintype I] in
lemma labelNetwork_eq_some_iff (A : Finset I) (i : I) (b : {a : I // a ∉ A}) :
    labelNetwork A i = some b ↔ i = b.1 := by
  constructor
  · intro h
    unfold labelNetwork at h
    split_ifs at h with hi
    exact congrArg Subtype.val (Option.some.inj h)
  · intro h
    subst i
    exact labelNetwork_of_notMem A b.2

omit [Fintype I] in
lemma mem_networkInitialSubsets {n : ℕ} (A : Finset I) (x : InjectiveTuple I n)
    (j : SubsetNetwork A) (t : Fin n) :
    t ∈ networkInitialSubsets A x j ↔ ∃ i, labelNetwork A i = j ∧ x i = t := by
  cases j with
  | none =>
    simp only [networkInitialSubsets, Finset.mem_image, labelNetwork_eq_none_iff]
  | some b =>
    simp only [networkInitialSubsets, Finset.mem_singleton, labelNetwork_eq_some_iff,
      exists_eq_left, eq_comm]

def labelLocation {n : ℕ} (A : Finset I) (y : I → Fin n) (i : I) : SubsetNetwork A × Fin n :=
  (labelNetwork A i, y i)

def labelOccupancy {n : ℕ} (A : Finset I) (y : I → Fin n) : Finset (SubsetNetwork A × Fin n) :=
  Finset.univ.image (labelLocation A y)

omit [Fintype I] in
lemma labelLocation_injective_sampled {d : ℕ} (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p : SubsetNetwork A → PhysicalSettings d) :
    Function.Injective (labelLocation A (mixedNetworkPermutation d A p x)) := by
  intro i j h
  have hj : labelNetwork A i = labelNetwork A j := congrArg Prod.fst h
  have hs : sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))) (x i) =
      sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A j))) (x j) := congrArg Prod.snd h
  rw [hj] at hs
  exact x.injective ((sampleSweep d _).injective hs)

lemma labelOccupancy_eq_sampleSubset {d : ℕ} (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p : SubsetNetwork A → PhysicalSettings d) :
    labelOccupancy A (mixedNetworkPermutation d A p x) =
      independentSampleSubset (networkInitialSubsets A x) p := by
  apply subsetFiberEquiv.injective
  funext j
  apply Finset.ext
  intro t
  rw [show subsetFiberEquiv (independentSampleSubset (networkInitialSubsets A x) p) j =
      _ from fiber_independentSampleSubset _ p j]
  change t ∈ subsetFiber (labelOccupancy A (mixedNetworkPermutation d A p x)) j ↔ _
  rw [mem_subsetFiber]
  simp only [labelOccupancy, Finset.mem_image, Finset.mem_univ, true_and,
    labelLocation, Prod.mk.injEq, mixedNetworkPermutation_apply]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨x i, (mem_networkInitialSubsets A x j (x i)).mpr ⟨i,hi,rfl⟩, ?_⟩
    simpa only [hi] using ht
  · rintro ⟨u,hu,ht⟩
    obtain ⟨i,hi,he⟩ := (mem_networkInitialSubsets A x j u).mp hu
    refine ⟨i,hi,?_⟩
    simpa only [hi, he] using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def reverseNetworkState {J : Type*} (d : ℕ) (p : J → PhysicalSettings d)
    (j : J) (i : Fin d) : SymmetricGroup (2 ^ d) :=
  sweepPrefix d (physicalSettingsEquiv d (p j)) i.1 *
    (sampleSweep d (physicalSettingsEquiv d (p j)))⁻¹

lemma reverseNetworkState_eq_endpointPath {J : Type*} (d : ℕ) (p : J → PhysicalSettings d)
    (j : J) (i : Fin d) (y : Fin (2 ^ d)) :
    reverseNetworkState d p j i y = endpointPath d i.1
      ((sampleSweep d (physicalSettingsEquiv d (p j))).symm y) y := by
  have h := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d (p j))
    ((sampleSweep d (physicalSettingsEquiv d (p j))).symm y) i.1 (Nat.le_of_lt i.2)
  simpa only [reverseNetworkState, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h

lemma same_switch_eq_or_flip {d : ℕ} (i : Fin d) (x y : Fin (2 ^ d))
    (h : ∀ j, j ≠ i → (positionsEquiv d).symm y j = (positionsEquiv d).symm x j) :
    y = x ∨ y = flipPermutation d i x := by
  rcases binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm y) h with he | he
  · exact Or.inl ((positionsEquiv d).symm.injective he)
  · right
    apply (positionsEquiv d).symm.injective
    simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using he

lemma endpointEncounter_maps_to_network {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (p : SubsetNetwork A → PhysicalSettings d) (y : I → Fin (2 ^ d))
    (hy : Function.Injective (labelLocation A y)) (a b : I)
    (hab : (endpointEncounter d ((mixedNetworkPermutation d A p).symm y) y).Adj a b) :
    (encounterGraph (reverseNetworkState d p)).Adj (labelLocation A y a) (labelLocation A y b) := by
  obtain ⟨hne,i,hi⟩ := hab
  refine ⟨fun he => hne (hy he), i, ?_⟩
  change reverseNetworkState d p (labelNetwork A b) i (y b) =
      reverseNetworkState d p (labelNetwork A a) i (y a) ∨
    reverseNetworkState d p (labelNetwork A b) i (y b) =
      flipPermutation d i (reverseNetworkState d p (labelNetwork A a) i (y a))
  apply same_switch_eq_or_flip
  intro j hj
  rw [reverseNetworkState_eq_endpointPath, reverseNetworkState_eq_endpointPath]
  exact (congrFun hi ⟨j,hj⟩).symm

lemma NoIsolatedVertex_image {I X : Type*} [DecidableEq I] [DecidableEq X]
    (G : SimpleGraph I) (H : SimpleGraph X) (S : Finset I) (f : I → X)
    (h : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) (hS : NoIsolatedVertex G S) :
    NoIsolatedVertex H (S.image f) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,hab⟩ := hS a ha
  exact ⟨f b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,h a b hab⟩

lemma reverse_endpoint_noIsolates_implies_network {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p b : SubsetNetwork A → PhysicalSettings d)
    (h : NoIsolatedVertex (endpointEncounter d
      ((mixedNetworkPermutation d A b).symm (mixedNetworkPermutation d A p x))
      (mixedNetworkPermutation d A p x)) Finset.univ) :
    NoIsolatedVertex (encounterGraph (reverseNetworkState d b))
      (independentSampleSubset (networkInitialSubsets A x) p) := by
  rw [← labelOccupancy_eq_sampleSubset]
  exact NoIsolatedVertex_image _ _ _ _ (endpointEncounter_maps_to_network A b _
    (labelLocation_injective_sampled A x p)) h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SparseBridge
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem conditional_reverse_encounter_bound {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (b : SubsetNetwork A → PhysicalSettings d)
    (hΔ : 0 < 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ) ≤ 1) :
    finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      NoIsolatedVertex (endpointEncounter d
        ((mixedNetworkPermutation d A b).symm (mixedNetworkPermutation d A p x))
        (mixedNetworkPermutation d A p x)) Finset.univ) ≤
    (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
      Real.exp (Real.exp 2 * Fintype.card I) := by
  exact (finiteProb_mono (fun p hp => reverse_endpoint_noIsolates_implies_network A x p b hp)).trans
    (independentSampleSubset_noIsolates_bound (reverseNetworkState d b)
      (networkInitialSubsets A x) (Fintype.card I) (networkInitialSubsets_total A x).symm hΔ hΔ1)

theorem maskedEndpointKernel_square_row_bound {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (hΔ : 0 < 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ) ≤ 1) :
    (∑ z, ∑ y, maskedEndpointKernel d A x y * maskedEndpointKernel d A z y) ≤
      (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
        Real.exp (Real.exp 2 * Fintype.card I) := by
  let e : InjectiveTuple I (2 ^ d) ↪ (I → Fin (2 ^ d)) :=
    ⟨fun x => x, fun x y h => Function.Embedding.ext (congrFun h)⟩
  let K := maskedPermutationKernel (mixedNetworkPermutation d A)
    (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ)
  have he (x y : InjectiveTuple I (2 ^ d)) : maskedEndpointKernel d A x y = K (e x) (e y) :=
    maskedEndpointKernel_eq_mixed d A x y
  simp only [he]
  refine (nonnegative_kernel_restricted_row_le e K (maskedPermutationKernel_nonneg _ _) x).trans ?_
  refine (maskedPermutationKernel_square_row_le (mixedNetworkPermutation d A)
    (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ) (e x)).trans ?_
  calc
    _ ≤ finiteMean ℝ (fun _b : SubsetNetwork A → PhysicalSettings d =>
        (Real.sqrt (2 * (d : ℝ) * Fintype.card I / (2 ^ d : ℕ))) ^ Fintype.card I *
          Real.exp (Real.exp 2 * Fintype.card I)) :=
      finiteMean_mono (fun b => conditional_reverse_encounter_bound A x b hΔ hΔ1)
    _ = _ := finiteMean_const ℝ _

theorem sparse_sweep_operator_bound {d : ℕ} (lam : Partition (2 ^ d))
    (hΔ : 0 < 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ) ≤ 1) :
    ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
      2 ^ (2 ^ d - lam.1.rowLen 0 : ℕ) *
        Real.sqrt ((Real.sqrt (2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ))) ^
          (2 ^ d - lam.1.rowLen 0 : ℕ) * Real.exp (Real.exp 2 * (2 ^ d - lam.1.rowLen 0 : ℕ))) := by
  apply sweep_norm_le_of_masked_rows lam (by positivity)
  intro A x
  have h := maskedEndpointKernel_square_row_bound A x
  simp only [card_offFirstRow] at h
  exact h hΔ hΔ1

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.SparseUniform
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Topology
open Filter

lemma sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma sparse_kernel_exponential_bound {t Δ : ℝ} (hΔ : Δ ≤ Real.exp (-t)) (k : ℕ) :
    (2 : ℝ) ^ k * Real.sqrt ((Real.sqrt Δ) ^ k * Real.exp (Real.exp 2 * k)) ≤
      Real.exp (((Real.log 2 + Real.exp 2 / 2) - t / 4) * k) := by
  have hroot : Real.sqrt Δ ≤ Real.exp (-t / 2) := by
    simpa only [sqrt_exp_half] using Real.sqrt_le_sqrt hΔ
  calc
    _ ≤ (2 : ℝ) ^ k * Real.sqrt ((Real.exp (-t / 2)) ^ k * Real.exp (Real.exp 2 * k)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg Δ) hroot k) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, sqrt_exp_half]
      nth_rw 1 [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

lemma sparse_depth_prefactors {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀,
      2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) ≤ 1 ∧
      Real.log 2 + Real.exp 2 / 2 ≤ δ / 16 * Real.log ((2 ^ d : ℕ) : ℝ) := by
  have hb : 0 < δ / 2 * Real.log 2 := mul_pos (half_pos hδ) (Real.log_pos (by norm_num))
  have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1
    (δ / 2 * Real.log 2) hb).comp tendsto_natCast_atTop_atTop).const_mul 2
  have ht' : Tendsto (fun d : ℕ =>
      2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))) atTop (𝓝 0) := by
    convert ht using 1
    · funext d
      simp only [Function.comp_apply, Real.rpow_one, nat_two_pow_log]
      rw [mul_assoc]
      congr 2
      ring_nf
    · norm_num
  have ht'' : Tendsto (fun d : ℕ => δ / 16 * Real.log ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
    have hh := tendsto_natCast_atTop_atTop.const_mul_atTop
      (by positivity : 0 < δ / 16 * Real.log 2)
    convert hh using 1
    funext d
    rw [nat_two_pow_log]
    ring
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    ((ht'.eventually_le_const (by norm_num : (0 : ℝ) < 1)).and
      (ht''.eventually_ge_atTop (Real.log 2 + Real.exp 2 / 2)))
  exact ⟨max D 1, le_max_right _ _, fun d hd => hD d ((le_max_left _ _).trans hd)⟩

lemma sparse_delta_le_exp {δ : ℝ} {d k : ℕ}
    (hk : (k : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ))
    (hsmall : 2 * (d : ℝ) * Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) ≤ 1) :
    2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤
      Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  let c := Real.exp (-δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))
  have he : (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) = c * c * (2 ^ d : ℕ) := by
    conv_rhs => rhs; rw [← Real.exp_log hn]
    dsimp [c]
    rw [← Real.exp_add, ← Real.exp_add, Real.rpow_def_of_pos hn]
    congr 1
    ring
  calc
    _ ≤ 2 * (d : ℝ) * (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / (2 ^ d : ℕ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by positivity)) hn.le
    _ = (2 * (d : ℝ) * c) * c := by rw [he]; field_simp
    _ ≤ 1 * c := mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
    _ = _ := one_mul c

theorem eventually_sparse_sweep_norm {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      1 ≤ 2 ^ d - lam.1.rowLen 0 →
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      ‖(sweepOperator lam).toContinuousLinearMap‖ ≤
        Real.exp (-(δ / 16) * (2 ^ d - lam.1.rowLen 0 : ℕ) *
          Real.log ((2 ^ d : ℕ) : ℝ)) := by
  obtain ⟨d₀, hd₀, hsmall⟩ := sparse_depth_prefactors hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hk hkbound
  obtain ⟨hpref, hlog⟩ := hsmall d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d from hd₀.trans hd)
  have hkpos : (0 : ℝ) < (2 ^ d - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hΔ := sparse_delta_le_exp hkbound hpref
  have hnlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  have hΔ1 : 2 * (d : ℝ) * (2 ^ d - lam.1.rowLen 0 : ℕ) / (2 ^ d : ℕ) ≤ 1 := by
    apply hΔ.trans
    apply Real.exp_le_one_iff.mpr
    nlinarith
  apply (sparse_sweep_operator_bound lam (by positivity) hΔ1).trans
  have hb := sparse_kernel_exponential_bound (t := δ / 2 * Real.log ((2 ^ d : ℕ) : ℝ))
    (by simpa only [neg_mul, neg_div] using hΔ) (2 ^ d - lam.1.rowLen 0)
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  have hh := mul_le_mul_of_nonneg_right hlog hkpos.le
  nlinarith

theorem eventually_sparse_moments {δ : ℝ} (hδ : 0 < δ) :
    ∃ d₀ r₀ : ℕ, 1 ≤ d₀ ∧ 1 ≤ r₀ ∧ ∀ d ≥ d₀, ∀ r ≥ r₀,
      ∀ lam : Partition (2 ^ d),
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      weightedMoment lam r ≤ 1 := by
  obtain ⟨d₀, hd₀, hnorm⟩ := eventually_sparse_sweep_norm hδ
  obtain ⟨R, hR⟩ := exists_nat_ge (16 / δ)
  refine ⟨d₀, max R 1, hd₀, le_max_right _ _, ?_⟩
  intro d hd r hr lam hk
  let k := 2 ^ d - lam.1.rowLen 0
  have hdim : (spechtDimension lam : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ k := by
    exact_mod_cast spechtDimension_le_pow_level lam
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hnlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  by_cases hk0 : k = 0
  · have hdim1 : (spechtDimension lam : ℝ) ≤ 1 := by simpa [hk0] using hdim
    exact (weightedMoment_le_dimension_squared lam r).trans (by
      simpa using pow_le_pow_left₀ (Nat.cast_nonneg (spechtDimension lam)) hdim1 2)
  have hs := hnorm d hd lam (by omega) hk
  calc
    weightedMoment lam r ≤ (spechtDimension lam : ℝ) ^ 2 *
        ‖(sweepOperator lam).toContinuousLinearMap‖ ^ (2 * r) := weightedMoment_le_opNorm lam r
    _ ≤ (((2 ^ d : ℕ) : ℝ) ^ k) ^ 2 *
        (Real.exp (-(δ / 16) * k * Real.log ((2 ^ d : ℕ) : ℝ))) ^ (2 * r) := by
      exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hdim 2)
        (pow_le_pow_left₀ (norm_nonneg _) hs (2 * r)) (by positivity) (by positivity)
    _ = Real.exp (((2 : ℝ) - δ / 8 * r) * k * Real.log ((2 ^ d : ℕ) : ℝ)) := by
      nth_rw 1 [← Real.exp_log hn]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hRr : (R : ℝ) ≤ r := by exact_mod_cast (le_max_left R 1).trans hr
      have : 16 ≤ δ * r := by
        have hh := (div_le_iff₀ hδ).mp (hR.trans hRr)
        nlinarith
      have hh : 2 - δ / 8 * r ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hh (Nat.cast_nonneg k)) hnlog

theorem uniform_sparse_moments {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, ∀ lam : Partition (2 ^ d),
      ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
      weightedMoment lam r ≤ 1 := by
  obtain ⟨d₀, r₀, _hd₀, hr₀, hlarge⟩ := eventually_sparse_moments hδ
  obtain ⟨R, _hR, hfinite⟩ := finite_base_moments d₀
  refine ⟨max r₀ R, hr₀.trans (le_max_left _ _), ?_⟩
  intro r hr d lam hk
  by_cases hd : d₀ ≤ d
  · exact hlarge d hd r ((le_max_left _ _).trans hr) lam hk
  · exact hfinite r ((le_max_right _ _).trans hr) d (by omega) lam

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MomentMonotonicity
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma moment_bound_of_le_one {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (r : ℕ) (hr : weightedMoment lam r ≤ 1)
    {u v : ℕ} (α : Partition u) (β : Partition v) {η : ℝ} (hη : 0 ≤ η)
    (κ : ℝ) (l : ℕ) :
    logMoment (weightedMoment lam r) ≤
      ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  rw [logMoment_le_iff (weightedMoment_nonneg lam r)]
  apply hr.trans
  apply Real.one_le_exp
  exact add_nonneg (mul_nonneg (coefficient_nonneg hη hd) (signedEntropy_nonneg α β))
    (remainderBudget_nonneg κ d l)

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.ProvedRanges
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

theorem signed_occurrence_moment_bound_proved_ranges_oai (D : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (κ : ℝ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2 ^ d),
        (d ≤ D ∨
          ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ∨
          2 ^ d - lam.1.rowLen 0 = 1 ∨
          2 ^ d / 2 < lam.1.colLen 0) →
        ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam →
          logMoment (weightedMoment lam r) ≤
            ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨r₀, hr₀, hsparse⟩ := uniform_sparse_moments hδ
  obtain ⟨R, _hR, hfinite⟩ := finite_base_moments D
  refine ⟨max r₀ R, hr₀.trans (le_max_left _ _), ?_⟩
  intro r hr d hd lam hcases u v l h α β γ _occ
  apply moment_bound_of_le_one hd lam r _ α β hη κ l
  have hrpos : 1 ≤ r := hr₀.trans ((le_max_left _ _).trans hr)
  rcases hcases with hsmall | hk | hkone | htall
  · exact hfinite r ((le_max_right _ _).trans hr) d hsmall lam
  · exact hsparse r ((le_max_left _ _).trans hr) d lam hk
  · rw [weightedMoment_eq_zero_of_level_one lam hkone hrpos]
    exact zero_le_one
  · rw [weightedMoment_eq_zero_of_long_column hd lam htall hrpos]
    exact zero_le_one

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

@[simp] lemma finiteRegularRepresentation_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    finiteRegularRepresentation g f h = f (g⁻¹ * h) := rfl

omit [FiniteDimensional ℂ E] in
@[simp] lemma coefficientAction_apply (ρ : Representation ℂ G E) (f : G → ℂ) (x : E) :
    coefficientAction ρ f x = ∑ g, f g • ρ g x := by
  simp [coefficientAction]

end SignedSweeps
end

end OAI
end

theorem solution : type_of% @OAI.SignedSweeps.signed_occurrence_moment_bound_proved_ranges_oai := @OAI.SignedSweeps.signed_occurrence_moment_bound_proved_ranges_oai
