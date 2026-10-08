-- Prove2me | solution 1 for OAI.Erdos3.containedProgressionKernel_explicit_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:31:17.204308+00:00
-- url     : https://prove2.me/submissions/76ddf9ce-6871-4e32-8aae-e4cc793811a6

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016
import Theorems.Thm_OAI_Erdos3_scalarCube_largeCokernel_probability_le_of_card_le

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

theorem eventProbability_mono {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E F : Ω → Prop) (hEF : ∀ x, E x → F x) : p.eventProbability E ≤ p.eventProbability F := by
  classical
  apply p.mean_mono
  intro x
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · simp only [hE, ite_false]
    split_ifs <;> norm_num

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem uniform_condition_weight_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (G : Finset Ω) (hG : 0 < (uniform Ω).mass G) (c : ℝ) (hc : 0 < c)
    (hmass : c ≤ (uniform Ω).mass G) (x : Ω) :
    ((uniform Ω).condition G hG).weight x ≤ c⁻¹ * (Fintype.card Ω : ℝ)⁻¹ := by
  have hcard : (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹ := by positivity
  change (if x ∈ G then (Fintype.card Ω : ℝ)⁻¹ else 0) / (uniform Ω).mass G ≤ _
  by_cases hx : x ∈ G
  · rw [if_pos hx, div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hc hmass) hcard
  · rw [if_neg hx, zero_div]
    positivity

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_le_of_weight_le {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (C : ℝ)
    (hw : ∀ x, p.weight x ≤ C * q.weight x) (E : Ω → Prop) :
    p.eventProbability E ≤ C * q.eventProbability E := by
  classical
  unfold eventProbability mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x <;> simp [hx, hw x]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

theorem dependent_fin_cons_map {n : ℕ} {X E : Fin (n + 1) → Type*}
    (a : ∀ i, X i → E i) (x : X 0) (y : ∀ i : Fin n, X i.succ) :
    (fun i => a i (Fin.cons x y i)) = Fin.cons (a 0 x) (fun i => a i.succ (y i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem complexMean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (F : (∀ i, X i) → ℂ) :
    p.complexMean F = F (fun i => Fin.elim0 i) := by
  have hF : F = fun _ => F (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg F (Subsingleton.elim _ _)
  rw [hF, p.complexMean_const]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem integerMatrixImage_natAbs_smul {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (y : I → ℤ) : (A.det.natAbs : ℤ) • y ∈ A.mulVecLin.range :=
  integerMatrixImage_multiple_smul A Int.dvd_natAbs_self y

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix ENNReal

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerCokernelExponent
namespace OAI

section

namespace Erdos3

theorem integerCokernel_finite {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Finite ((I → ℤ) ⧸ L.toAddSubgroup) := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hindex : L.toAddSubgroup.index ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h
    exact (pow_ne_zero _ (NeZero.ne m)) h.symm
  let : L.toAddSubgroup.FiniteIndex := ⟨hindex⟩
  infer_instance

theorem integerCokernelExponent_pos {I : Type*} (L : Submodule ℤ (I → ℤ))
    [Finite ((I → ℤ) ⧸ L.toAddSubgroup)] : 0 < integerCokernelExponent L :=
  AddMonoid.ExponentExists.of_finite.exponent_pos

theorem integerCokernelExponent_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) :
    integerScalarLattice I (integerCokernelExponent L : ℤ) ≤ L := by
  rintro y ⟨z, rfl⟩
  change (integerCokernelExponent L : ℤ) • z ∈ L
  rw [natCast_zsmul]
  have h := AddMonoid.exponent_nsmul_eq_zero (QuotientAddGroup.mk' L.toAddSubgroup z)
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h
  exact h

theorem integerCokernelExponent_dvd_period {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    integerCokernelExponent L ∣ m := by
  apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.toAddSubgroup x
  rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  change m • z ∈ L
  have h := hperiod ((integerScalarLattice_mem (m : ℤ) _).mpr ⟨z, rfl⟩)
  simpa only [natCast_zsmul] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CokernelCharacterWitness
namespace OAI

section

namespace Erdos3

theorem integerLattice_pivot_period {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hAin : A.mulVecLin.range ≤ L) :
    integerScalarLattice I (A.det.natAbs : ℤ) ≤ L := by
  rintro y ⟨z, rfl⟩
  change (A.det.natAbs : ℤ) • z ∈ L
  exact hAin (integerMatrixImage_natAbs_smul A z)

theorem integerCokernelExponent_le_det {I : Type*} [Fintype I] [DecidableEq I]
    (L : Submodule ℤ (I → ℤ)) (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (hAin : A.mulVecLin.range ≤ L) :
    0 < integerCokernelExponent L ∧ integerCokernelExponent L ≤ A.det.natAbs := by
  let : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hA⟩
  have hp := integerLattice_pivot_period L A hAin
  let : Finite ((I → ℤ) ⧸ L.toAddSubgroup) := integerCokernel_finite L A.det.natAbs hp
  exact ⟨integerCokernelExponent_pos L,
    Nat.le_of_dvd (Int.natAbs_pos.mpr hA) (integerCokernelExponent_dvd_period L A.det.natAbs hp)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerColumnMinor
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

theorem integerColumnMinor_range_le {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I → J) :
    (A.submatrix id s).mulVecLin.range ≤ A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨s i, rfl⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RectangularCellGeometry
namespace OAI

section

namespace Erdos3

theorem rectangularLatticePoint_mem_cell {I : Type*}
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (k : I → ℤ) :
    rectangularLatticePoint a S k ∈ rectangularLatticeCell a S k := by
  intro i _
  change ((k i : ℝ) - a i) / S i ∈
    Set.Ico (((k i : ℝ) - a i) / S i) (((k i : ℝ) + 1 - a i) / S i)
  exact ⟨le_rfl, (div_lt_div_iff_of_pos_right (hS i)).mpr (by linarith)⟩

theorem integerBoxCell_unit_bound {I : Type*} (L : ℕ) (hL : 0 < L) (k : I → ℤ)
    (hk : ∀ i, -(L : ℤ) ≤ k i ∧ k i < L) (x : I → ℝ)
    (hx : x ∈ rectangularLatticeCell (fun _ => 0) (fun _ => (L : ℝ)) k) :
    ∀ i, |x i| ≤ 1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  intro i
  have hi := hx i (Set.mem_univ i)
  change ((k i : ℝ) - 0) / (L : ℝ) ≤ x i ∧
    x i < ((k i : ℝ) + 1 - 0) / (L : ℝ) at hi
  simp only [sub_zero] at hi
  have hlo : -(L : ℝ) ≤ (k i : ℝ) := by exact_mod_cast (hk i).1
  have hhi : (k i : ℝ) + 1 ≤ L := by exact_mod_cast (show k i + 1 ≤ (L : ℤ) by have := (hk i).2; omega)
  have h1 := (div_le_iff₀ hL').mp hi.1
  have h2 := (lt_div_iff₀ hL').mp hi.2
  apply abs_le.mpr
  constructor <;> nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

theorem coordinateDeterminantVariation_nonneg (I X : Type*) [Fintype I] [Fintype X] :
    0 ≤ coordinateDeterminantVariation I X := by
  unfold coordinateDeterminantVariation
  positivity

theorem coordinateMatrixPolynomial_derivative {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (index : I → I → X) (x : X → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    ‖fderiv ℝ (fun x => MvPolynomial.eval x (coordinateMatrixPolynomial index).det) x‖ ≤
      coordinateDeterminantVariation I X := by
  have h := polynomial_det_fderiv_norm_le (coordinateMatrixPolynomial index) x
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (fun a b => by simpa only [coordinateMatrixPolynomial, MvPolynomial.eval_X] using hx (index a b))
    (fun a b j => by
      simp only [coordinateMatrixPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
      split_ifs <;> norm_num)
  rw [polynomial_det_eval_function] at h
  simpa only [one_pow, mul_one, coordinateDeterminantVariation] using h

theorem coordinateMatrixPolynomial_variation {I X : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (index : I → I → X) (x y : X → ℝ) (hx : ∀ j, |x j| ≤ 1) (hy : ∀ j, |y j| ≤ 1) :
    |MvPolynomial.eval x (coordinateMatrixPolynomial index).det -
        MvPolynomial.eval y (coordinateMatrixPolynomial index).det| ≤
      coordinateDeterminantVariation I X * ‖x - y‖ := by
  let S : Set (X → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hmem (z : X → ℝ) : z ∈ S ↔ ∀ j, |z j| ≤ 1 := by
    simp only [S, Set.mem_Icc, Pi.le_def, abs_le, forall_and]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (mvPolynomial_contDiff_eval (coordinateMatrixPolynomial index).det).differentiable
      (by norm_num) z)
    (fun z hz => coordinateMatrixPolynomial_derivative index z ((hmem z).mp hz))
    (convex_Icc _ _) ((hmem y).mpr hy) ((hmem x).mpr hx)
  simpa only [Real.norm_eq_abs] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem polynomial_grid_sublevel_transfer {Ω : Type*} [Fintype Ω] {N : ℕ}
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (L : ℕ) (hL : 0 < L) (hgrid : ∀ ω i, -(L : ℤ) ≤ grid ω i ∧ grid ω i < L)
    (P : MvPolynomial (Fin N) ℝ) (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hw : ∀ ω, p.weight ω ≤ M * ((L : ℝ) ^ N)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 1) → (∀ i, |y i| ≤ 1) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖) :
    p.eventProbability (fun ω => |MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P| ≤ u) ≤
      M * volume.real (boxMvPolynomialSublevel P 1 (u + K / L)) := by
  let cell := fun ω => rectangularLatticeCell (fun _ => 0) (fun _ => (L : ℝ)) (grid ω)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  apply finite_cell_event_probability_le p _ volume cell _ M (((L : ℝ) ^ N)⁻¹) hM
    (fun a b hab => rectangularLatticeCell_disjoint _ _ (fun _ => hL') (hinj.ne hab))
    (fun ω => rectangularLatticeCell_measurable _ _ _)
    (fun ω => rectangularLatticeCell_volume_ne_top _ _ _) _ hw _
    (boxMvPolynomialSublevel_volume_ne_top P (by norm_num) _)
  · intro ω
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      rectangularLatticeCell_volume (fun _ : Fin N => 0) (fun _ => (L : ℝ)) (fun _ => hL') (grid ω)
  · intro ω hω x hx
    have hxbox := integerBoxCell_unit_bound L hL (grid ω) (hgrid ω) x hx
    have hycell := rectangularLatticePoint_mem_cell (fun _ : Fin N => 0) (fun _ => (L : ℝ))
      (fun _ => hL') (grid ω)
    have hybox := integerBoxCell_unit_bound L hL (grid ω) (hgrid ω) _ hycell
    have hdist := rectangularLatticeCell_point_distance (fun _ : Fin N => 0) (fun _ => (L : ℝ))
      (fun _ => hL') (1 / (L : ℝ)) (by positivity) (fun _ => le_rfl) (grid ω) x hx
    have h := hLip x _ hxbox hybox
    have hpoint : rectangularLatticePoint (fun _ : Fin N => 0) (fun _ => (L : ℝ)) (grid ω) =
        (fun i => (grid ω i : ℝ) / L) := by
      funext i
      simp only [rectangularLatticePoint, sub_zero]
    rw [hpoint] at h hdist
    refine ⟨hxbox, ?_⟩
    have hchange : |MvPolynomial.eval x P - MvPolynomial.eval
        (fun i => (grid ω i : ℝ) / L) P| ≤ K / L := by
      simpa only [mul_one_div] using
        h.trans (mul_le_mul_of_nonneg_left hdist hK)
    have ht := abs_sub_abs_le_abs_sub (MvPolynomial.eval x P)
      (MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P)
    nlinarith

theorem polynomial_grid_sublevel_bound_of_value {Ω : Type*} [Fintype Ω] {N d : ℕ}
    (hN : 0 < N) (hd : 0 < d)
    (p : FiniteProbabilityWeights Ω) (grid : Ω → Fin N → ℤ) (hinj : Function.Injective grid)
    (L : ℕ) (hL : 0 < L) (hgrid : ∀ ω i, -(L : ℤ) ≤ grid ω i ∧ grid ω i < L)
    (P : MvPolynomial (Fin N) ℝ) (hdeg : ∀ i, P.degreeOf i ≤ d)
    (M K u : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hu : 0 < u)
    (hw : ∀ ω, p.weight ω ≤ M * ((L : ℝ) ^ N)⁻¹)
    (hLip : ∀ x y : Fin N → ℝ, (∀ i, |x i| ≤ 1) → (∀ i, |y i| ≤ 1) →
      |MvPolynomial.eval x P - MvPolynomial.eval y P| ≤ K * ‖x - y‖)
    (x₀ : Fin N → ℝ) (hx₀ : ∀ i, |x₀ i| ≤ 1) (hval : 1 ≤ |MvPolynomial.eval x₀ P|) :
    p.eventProbability (fun ω => |MvPolynomial.eval (fun i => (grid ω i : ℝ) / L) P| ≤ u) ≤
      M * (multivariateSublevelConstant N d *
        ((u + K / L) * (d + 1 : ℝ) ^ N) ^ (((N * d : ℕ) : ℝ)⁻¹)) := by
  apply (polynomial_grid_sublevel_transfer p grid hinj L hL hgrid P M K u hM hK hw hLip).trans
  apply mul_le_mul_of_nonneg_left _ hM
  obtain ⟨m, hm⟩ := exists_coefficient_of_unit_box_value P hdeg x₀ hx₀ zero_lt_one hval
  have h := polynomial_sublevel_box_bound hN hd P hdeg (by norm_num : (1 : ℝ) ≤ 1)
    (add_pos_of_pos_of_nonneg hu (div_nonneg hK (Nat.cast_nonneg L)))
    (by positivity : (0 : ℝ) < 1 / (d + 1 : ℝ) ^ N) m hm
  simpa only [one_pow, one_mul, div_div_eq_mul_div, div_one] using h

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {n N : ℕ}

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductDomination
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem pi_weight_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (x : ∀ j, Ω j) :
    (pi p).weight x ≤ (∏ j, C j) * (pi q).weight x := by
  change (∏ j, (p j).weight (x j)) ≤ (∏ j, C j) * (∏ j, (q j).weight (x j))
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _ => (p j).nonneg (x j)) (fun j _ => hw j (x j))

theorem pi_eventProbability_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) (C : J → ℝ)
    (hw : ∀ j x, (p j).weight x ≤ C j * (q j).weight x) (E : (∀ j, Ω j) → Prop) :
    (pi p).eventProbability E ≤ (∏ j, C j) * (pi q).eventProbability E :=
  eventProbability_le_of_weight_le _ _ _ (pi_weight_le p q C hw) E

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

theorem integerScalarCubeSet_card_lower (I : Type*) [Fintype I] [DecidableEq I] (L H : ℕ)
    (hH : 0 < H) (hHL : (Fintype.card I + 1) * H ≤ L) :
    H ^ (Fintype.card I + 1) ≤ (integerScalarCubeSet I L).card := by
  classical
  have hHL' : H ≤ L := by nlinarith
  let point (x : Option I → Fin H) : IntegerScalarCubeBox I L := fun i =>
    ⟨((x i).val : ℤ), Finset.mem_Ico.mpr ⟨by omega, by have := (x i).isLt; omega⟩⟩
  have hpoint (x : Option I → Fin H) : point x ∈ integerScalarCubeSet I L :=
    (mem_integerScalarCubeSet L _).mpr (integerScalarCube_small_positive hH hHL x)
  let e : (Option I → Fin H) → ↥(integerScalarCubeSet I L) := fun x => ⟨point x, hpoint x⟩
  have he : Function.Injective e := by
    intro x y h
    funext i
    apply Fin.ext
    have hi := congrArg (fun z : ↥(integerScalarCubeSet I L) => (z.val i : ℤ)) h
    change ((x i).val : ℤ) = ((y i).val : ℤ) at hi
    exact_mod_cast hi
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_coe] using hc

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity

theorem integerScalarCubeReference_mass_lower (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) :
    (integerScalarCubeDensityCap I)⁻¹ ≤
      (integerScalarCubeReference I L hL).mass (integerScalarCubeSet I L) := by
  let n := Fintype.card I + 1
  let H := L / n
  have hn : 0 < n := by dsimp [n]; omega
  have hH : 0 < H := Nat.div_pos hsize hn
  have hHL : n * H ≤ L := Nat.mul_div_le L n
  have hc := integerScalarCubeSet_card_lower I L H hH hHL
  have hfloor : (L : ℝ) ≤ 2 * (n : ℝ) * (H : ℝ) := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hratio : 1 / (4 * (n : ℝ)) ≤ (H : ℝ) / (2 * (L : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  calc
    _ = (1 / (4 * (n : ℝ))) ^ n := by
      simp only [integerScalarCubeDensityCap, n, one_div, inv_pow]
    _ ≤ ((H : ℝ) / (2 * (L : ℝ))) ^ n := pow_le_pow_left₀ (by positivity) hratio n
    _ = (H : ℝ) ^ n / (2 * (L : ℝ)) ^ n := div_pow _ _ _
    _ ≤ _ := by
      rw [integerScalarCubeReference_mass, integerScalarCubeBox_card]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

theorem integerScalarCubeWeights_weight_le (I : Type*) [Fintype I] [DecidableEq I] (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (x : IntegerScalarCubeBox I L) :
    (integerScalarCubeWeights I L hL).weight x ≤
      integerScalarCubeDensityCap I * (Fintype.card (IntegerScalarCubeBox I L) : ℝ)⁻¹ := by
  classical
  let : Nonempty (IntegerScalarCubeBox I L) := ⟨integerScalarCubeBoxZero I L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_weight_le (integerScalarCubeSet I L)
    (integerScalarCubeReference_mass_pos I L hL) ((integerScalarCubeDensityCap I)⁻¹)
    (inv_pos.mpr (integerScalarCubeDensityCap_pos I))
    (integerScalarCubeReference_mass_lower I L hL hsize) x
  simpa only [integerScalarCubeWeights, integerScalarCubeReference, inv_inv] using h

open scoped BigOperators Classical

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScalarCubeGridCoordinates
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeGrid_injective {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N) :
    Function.Injective (scalarCubeGrid (L := L) e) := by
  intro x y h
  funext j i
  apply Subtype.ext
  have hi := congrFun h (e (j, i))
  simpa only [scalarCubeGrid, e.symm_apply_apply] using hi

theorem scalarCubeGrid_bounds {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N)
    (x : J → IntegerScalarCubeBox I L) (i : Fin N) :
    -(L : ℤ) ≤ scalarCubeGrid e x i ∧ scalarCubeGrid e x i < L :=
  Finset.mem_Ico.mp (x (e.symm i).1 (e.symm i).2).property

theorem scalarCubeGrid_weight_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {N : ℕ}
    (e : J × Option I ≃ Fin N) (L : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L)
    (x : J → IntegerScalarCubeBox I L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).weight x ≤
      (integerScalarCubeDensityCap I) ^ Fintype.card J * ((L : ℝ) ^ N)⁻¹ := by
  have hN : (Fintype.card I + 1) * Fintype.card J = N := by
    simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.mul_comm] using
      Fintype.card_congr e
  have hs (j : J) : (integerScalarCubeWeights I L hL).weight (x j) ≤
      integerScalarCubeDensityCap I * ((L : ℝ) ^ (Fintype.card I + 1))⁻¹ := by
    have h := integerScalarCubeWeights_weight_le I L hL hsize (x j)
    rw [integerScalarCubeBox_card] at h
    push_cast at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (integerScalarCubeDensityCap_pos I).le
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (Nat.cast_nonneg L)
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  change (∏ j, (integerScalarCubeWeights I L hL).weight (x j)) ≤ _
  calc
    _ ≤ ∏ _j : J, integerScalarCubeDensityCap I * ((L : ℝ) ^ (Fintype.card I + 1))⁻¹ :=
      Finset.prod_le_prod (fun j _ => (integerScalarCubeWeights I L hL).nonneg (x j))
        (fun j _ => hs j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, mul_pow, ← inv_pow, ← pow_mul, hN]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarCubeMinorPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCubeMinorTestPoint_bound {I J : Type*} [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (k : Fin N) :
    |scalarCubeMinorTestPoint e s k| ≤ 1 := by
  unfold scalarCubeMinorTestPoint
  split
  · norm_num
  · split_ifs <;> norm_num

theorem scalarCubeMinorPolynomial_test_value {I J : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq J] {N : ℕ}
    (e : J × Option I ≃ Fin N) (s : I → J) (hs : Function.Injective s) :
    MvPolynomial.eval (scalarCubeMinorTestPoint e s) (scalarCubeMinorPolynomial e s) = 1 := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  have hm : ((fun i j => scalarCubeMinorTestPoint e s (e (s j, some i))) : Matrix I I ℝ) =
      (1 : Matrix I I ℝ) := by
    ext i j
    simp [scalarCubeMinorTestPoint, Matrix.one_apply, hs.eq_iff, eq_comm]
  rw [hm, Matrix.det_one]

theorem scalarCubeMinorPolynomial_grid_eval {I J : Type*} [Fintype I] [DecidableEq I]
    {N L : ℕ} (e : J × Option I ≃ Fin N) (s : I → J) (x : J → IntegerScalarCubeBox I L) :
    MvPolynomial.eval (fun i => (scalarCubeGrid e x i : ℝ) / L) (scalarCubeMinorPolynomial e s) =
      normalizedScalarCubeMinor s x := by
  rw [scalarCubeMinorPolynomial, coordinateMatrixPolynomial_eval]
  let A := (scalarCubeDifferenceMatrix x).submatrix id s
  have hm : ((fun i j => (scalarCubeGrid e x (e (s j, some i)) : ℝ) / L) : Matrix I I ℝ) =
      (L : ℝ)⁻¹ • A.map (Int.castRingHom ℝ) := by
    ext i j
    simp [A, scalarCubeGrid, scalarCubeDifferenceMatrix, sampledColumnMatrix,
      Matrix.submatrix_apply, div_eq_mul_inv, mul_comm]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    ((Int.castRingHom ℝ).map_det A).symm
  rw [hm, Matrix.det_smul, hcast, inv_pow]
  change ((L : ℝ) ^ Fintype.card I)⁻¹ * (A.det : ℝ) = (A.det : ℝ) / (L : ℝ) ^ Fintype.card I
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiscreteMinorThreshold
namespace OAI

namespace Erdos3

theorem discrete_scalarCube_minor_probability_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (hN : 0 < N)
    (s : I → J) (hs : Function.Injective s) (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (u : ℝ) (hu : 0 < u) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ u) ≤
      (integerScalarCubeDensityCap I) ^ Fintype.card J *
        (multivariateSublevelConstant N (Fintype.card I) *
          ((u + coordinateDeterminantVariation I (Fin N) / L) *
            (Fintype.card I + 1 : ℝ) ^ N) ^ (((N * Fintype.card I : ℕ) : ℝ)⁻¹)) := by
  have h := polynomial_grid_sublevel_bound_of_value hN Fintype.card_pos
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL))
    (scalarCubeGrid e) (scalarCubeGrid_injective e) L hL (scalarCubeGrid_bounds e)
    (scalarCubeMinorPolynomial e s)
    (coordinateMatrixPolynomial_degree (fun i j => e (s j, some i)))
    ((integerScalarCubeDensityCap I) ^ Fintype.card J)
    (coordinateDeterminantVariation I (Fin N)) u
    (pow_nonneg (integerScalarCubeDensityCap_pos I).le _) (coordinateDeterminantVariation_nonneg I (Fin N)) hu
    (scalarCubeGrid_weight_le e L hL hsize)
    (coordinateMatrixPolynomial_variation (fun i j => e (s j, some i)))
    (scalarCubeMinorTestPoint e s) (scalarCubeMinorTestPoint_bound e s)
    (by rw [scalarCubeMinorPolynomial_test_value e s hs]; norm_num)
  simpa only [scalarCubeMinorPolynomial_grid_eval] using h

theorem discreteScalarMinorThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    0 < discreteScalarMinorThreshold I J N η := by
  apply polynomialSublevelThreshold_pos
  · exact mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
      (multivariateSublevelConstant_pos hN _).le
  · positivity
  · exact hη

theorem discrete_minor_threshold_probability {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {N : ℕ} (e : J × Option I ≃ Fin N) (hN : 0 < N)
    (s : I → J) (hs : Function.Injective s) (L : ℕ) (hL : 0 < L)
    (hsize : Fintype.card I + 1 ≤ L) (η : ℝ) (hη : 0 < η)
    (hmesh : coordinateDeterminantVariation I (Fin N) / L ≤ discreteScalarMinorThreshold I J N η) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ discreteScalarMinorThreshold I J N η) ≤ η / 2 := by
  let C := (integerScalarCubeDensityCap I) ^ Fintype.card J * multivariateSublevelConstant N (Fintype.card I)
  let S := (Fintype.card I + 1 : ℝ) ^ N
  let κ := discreteScalarMinorThreshold I J N η
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    (multivariateSublevelConstant_pos hN _).le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hκ : 0 < κ := discreteScalarMinorThreshold_pos I J hN hη
  have h := discrete_scalarCube_minor_probability_le e hN s hs L hL hsize κ hκ
  calc
    _ ≤ C * ((κ + coordinateDeterminantVariation I (Fin N) / L) * S) ^
        (((N * Fintype.card I : ℕ) : ℝ)⁻¹) := by simpa only [C, S, mul_assoc] using h
    _ ≤ C * (2 * κ * S) ^ (((N * Fintype.card I : ℕ) : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow
      · exact mul_nonneg (add_nonneg hκ.le
          (div_nonneg (coordinateDeterminantVariation_nonneg I (Fin N)) (Nat.cast_nonneg L))) hS
      · apply mul_le_mul_of_nonneg_right _ hS
        dsimp [κ]
        linarith
      · positivity
    _ ≤ η / 2 := by
      have ht := polynomialSublevelThreshold_total_bound (m := 1)
        (Nat.mul_pos hN (Fintype.card_pos (α := I))) hC hS hη
      simpa only [Nat.cast_one, one_mul, κ, discreteScalarMinorThreshold, C, S] using ht

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEventUnion
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem eventProbability_or_le {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (E F : Ω → Prop) :
    p.eventProbability (fun x => E x ∨ F x) ≤ p.eventProbability E + p.eventProbability F := by
  classical
  unfold eventProbability
  calc
    _ ≤ p.mean (fun x => (if E x then 1 else 0) + (if F x then 1 else 0)) := by
      apply p.mean_mono
      intro x
      by_cases hE : E x <;> by_cases hF : F x <;> simp [hE, hF]
    _ = _ := p.mean_add _ _

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeCokernelCutoff
namespace OAI

namespace Erdos3

open scoped Matrix

end Erdos3

namespace Erdos3

theorem hasBoundedScalarPeriod_iff {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (hL : 0 < integerCokernelExponent L) (B : ℕ) :
    HasBoundedScalarPeriod L B ↔ integerCokernelExponent L ≤ B := by
  constructor
  · rintro ⟨a, ha, haB, hperiod⟩
    exact (Nat.le_of_dvd ha (integerCokernelExponent_dvd_period L a hperiod)).trans haB
  · intro hB
    exact ⟨integerCokernelExponent L, hL, hB, integerCokernelExponent_period L⟩

theorem scalarCube_no_bounded_period_iff {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {L : ℕ}
    (B : ℕ) (x : J → IntegerScalarCubeBox I L) :
    ((∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) ∧
      ¬ HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B) ↔
        scalarCubeLargeCokernelEvent B x := by
  have hpos (h : ∃ s : I → J, ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0) :
      0 < integerCokernelExponent (scalarCubeDifferenceMatrix x).mulVecLin.range := by
    obtain ⟨s, hs⟩ := h
    exact (integerCokernelExponent_le_det _ _ hs (integerColumnMinor_range_le _ s)).1
  constructor
  · rintro ⟨hminor, hperiod⟩
    exact ⟨hminor, Nat.lt_of_not_ge (hperiod ∘ (hasBoundedScalarPeriod_iff _ (hpos hminor) B).mpr)⟩
  · rintro ⟨hminor, hB⟩
    exact ⟨hminor, fun hp => (Nat.not_le_of_lt hB) ((hasBoundedScalarPeriod_iff _ (hpos hminor) B).mp hp)⟩

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI

namespace Erdos3

theorem jointKernelCutoff_bounds (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    0 < jointKernelCutoff n b K T ε κ ∧
    n ≤ jointKernelCutoff n b K T ε κ ∧
    b ≤ jointKernelCutoff n b K T ε κ ∧
    1 / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    K / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    2 * T / ε ≤ (jointKernelCutoff n b K T ε κ : ℝ) := by
  have h1 : 0 < 1 / κ := one_div_pos.mpr hκ
  have h2 : 0 ≤ K / κ := div_nonneg hK hκ.le
  have h3 : 0 ≤ 2 * T / ε := div_nonneg (by positivity) hε.le
  have hc := Nat.le_ceil (1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε)
  change 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε ≤
    (jointKernelCutoff n b K T ε κ : ℝ) at hc
  rw [add_div] at hc
  have hn : (n : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hb : (b : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hp : (0 : ℝ) < jointKernelCutoff n b K T ε κ := by
    have := Nat.cast_nonneg n (α := ℝ)
    have := Nat.cast_nonneg b (α := ℝ)
    linarith
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hn, by exact_mod_cast hb,
    by linarith, by linarith, by linarith⟩

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI

namespace Erdos3

theorem scalarKernel_bad_event_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {L : ℕ}
    (p : FiniteProbabilityWeights (J → IntegerScalarCubeBox I L))
    (s : I → J) (κ : ℝ) (B : ℕ) (hκ : 0 < κ) :
    p.eventProbability (fun x => ¬ GoodScalarKernelTuple s κ B x) ≤
      p.eventProbability (fun x => |normalizedScalarCubeMinor s x| ≤ κ) +
        p.eventProbability (scalarCubeLargeCokernelEvent B) := by
  apply (p.eventProbability_mono _
    (fun x => |normalizedScalarCubeMinor s x| ≤ κ ∨ scalarCubeLargeCokernelEvent B x) ?_).trans
    (p.eventProbability_or_le _ _)
  intro x hx
  by_cases hsmall : |normalizedScalarCubeMinor s x| ≤ κ
  · exact Or.inl hsmall
  · apply Or.inr
    have hminor : ((scalarCubeDifferenceMatrix x).submatrix id s).det ≠ 0 := by
      intro hz
      apply hsmall
      simpa only [normalizedScalarCubeMinor, hz, Int.cast_zero, zero_div, abs_zero] using hκ.le
    have hp : ¬ HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range B :=
      fun hp => hx ⟨lt_of_not_ge hsmall, hp⟩
    exact (scalarCube_no_bounded_period_iff B x).mp ⟨⟨s, hminor⟩, hp⟩

theorem scalarKernelConditioningConstant_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D) : 0 < scalarKernelConditioningConstant I J M D :=
  pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _

theorem scalarKernelTailConstant_pos (I J : Type*) [Fintype I] [Fintype J] :
    0 < scalarKernelTailConstant I J := by
  unfold scalarKernelTailConstant
  exact pow_pos (mul_pos (integerScalarCubeDensityCap_pos I) (by positivity)) _

theorem scalarKernelAdjustedAccuracy_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelAdjustedAccuracy I J M D η :=
  div_pos hη (scalarKernelConditioningConstant_pos I J hM hD)

theorem scalarKernelThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelThreshold I J M D η := by
  unfold scalarKernelThreshold discreteScalarMinorThreshold
  apply polynomialSublevelThreshold_pos
  · apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  · positivity
  · exact scalarKernelAdjustedAccuracy_pos I J hM hD hη

theorem scalarKernelCutoff_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelCutoff I J M D η ∧
    Fintype.card I + 1 ≤ scalarKernelCutoff I J M D η ∧
    D * ((Fintype.card I + 1) * M) ≤ scalarKernelCutoff I J M D η ∧
    1 / scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) /
        scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    2 * scalarKernelTailConstant I J / scalarKernelAdjustedAccuracy I J M D η ≤
      (scalarKernelCutoff I J M D η : ℝ) :=
  jointKernelCutoff_bounds _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le (scalarKernelAdjustedAccuracy_pos I J hM hD hη)
    (scalarKernelThreshold_pos I J hM hD hη)

end Erdos3

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeWindowLaw
namespace OAI

section

namespace Erdos3

theorem scalarCubeWindow_size {D n L K : ℕ} (hD : 0 < D)
    (hlarge : D * n ≤ L) (hDK : L ≤ D * K) : n ≤ K := by
  nlinarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound
namespace OAI

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

section

namespace Erdos3

theorem scalarKernelCutoff_window_size (I J : Type*) [Fintype I] [Fintype J]
    {M D L K : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) (hDK : L ≤ D * K) :
    (Fintype.card I + 1) * M ≤ K :=
  scalarCubeWindow_size hD ((scalarKernelCutoff_bounds I J hM hD hη).2.2.1.trans hlarge) hDK

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productComplexMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℂ) :
    (FiniteProbabilityWeights.pi μ).complexMean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).complexMean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change ((∏ i, (μ i).weight (x i) : ℝ) : ℂ) * g (fun j => x (e j)) =
    ((∏ j, (μ (e j)).weight (x (e j)) : ℝ) : ℂ) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedSliceFamilyLaw
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_pi_transport {n : ℕ} {X Y Z : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  induction n with
  | zero =>
      rw [complexMean_empty_tuple, complexMean_empty_tuple]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [complexMean_pi_fin_cons, complexMean_pi_fin_cons]
      simp only [dependent_fin_cons_map]
      calc
        _ = (p 0).complexMean (fun a => (pi (fun i : Fin n => q i.succ)).complexMean
            (fun y => f (Fin.cons (F 0 a) (fun i => G i.succ (y i))))) := by
          congr 1
          funext a
          exact ih (fun i => p i.succ) (fun i => q i.succ)
            (fun i => F i.succ) (fun i => G i.succ) (fun i => h i.succ) (fun z => f (Fin.cons (F 0 a) z))
        _ = _ := h 0 (fun z => (pi (fun i : Fin n => q i.succ)).complexMean
          (fun y => f (Fin.cons z (fun i => G i.succ (y i)))))

theorem complexMean_pi_transport_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {X Y Z : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (q : ∀ i, FiniteProbabilityWeights (Y i))
    (F : ∀ i, X i → Z i) (G : ∀ i, Y i → Z i)
    (h : ∀ i (f : Z i → ℂ), (p i).complexMean (fun x => f (F i x)) =
      (q i).complexMean (fun y => f (G i y))) (f : (∀ i, Z i) → ℂ) :
    (pi p).complexMean (fun x => f (fun i => F i (x i))) =
      (pi q).complexMean (fun y => f (fun i => G i (y i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : (∀ j, Z (e j)) → ℂ := fun z => f ((Equiv.piCongrLeft Z e) z)
  have hp := productComplexMean_reindex p e
    (fun x => f' (fun j => F (e j) (x j)))
  have hq := productComplexMean_reindex q e
    (fun x => f' (fun j => G (e j) (x j)))
  have ht := complexMean_pi_transport (fun j => p (e j)) (fun j => q (e j))
    (fun j => F (e j)) (fun j => G (e j)) (fun j => h (e j)) f'
  have hcomp (z : ∀ i, Z i) : f' (fun j => z (e j)) = f z := by
    change f ((Equiv.piCongrLeft Z e) ((Equiv.piCongrLeft Z e).symm z)) = f z
    rw [Equiv.apply_symm_apply]
  calc
    _ = (pi p).complexMean (fun x => f' (fun j => F (e j) (x (e j)))) := by
      congr 1
      funext x
      exact (hcomp (fun i => F i (x i))).symm
    _ = (pi q).complexMean (fun x => f' (fun j => G (e j) (x (e j)))) :=
      hp.trans (ht.trans hq.symm)
    _ = _ := by
      congr 1
      funext x
      exact hcomp (fun i => G i (x i))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D]
variable [Fintype α] [DecidableEq α] [IsEmpty α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_subset_le_card_ratio {X : Type*} [DecidableEq X]
    (A B : Finset X) (hA : A.Nonempty) (hAB : A ⊆ B)
    (f : X → ℝ) (hf : ∀ x ∈ B, 0 ≤ f x) :
    (𝔼 x ∈ A, f x) ≤ ((B.card : ℝ) / A.card) * (𝔼 x ∈ B, f x) := by
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast (hA.mono hAB).card_ne_zero
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  calc
    _ ≤ (∑ x ∈ B, f x) / (A.card : ℝ) := div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x hx _ => hf x hx)) (Nat.cast_nonneg _)
    _ = _ := by field_simp

theorem expect_injective_le_card_ratio {X Y : Type*} [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (g : X → Y)
    (hg : Set.InjOn g A) (hB : ∀ x ∈ A, g x ∈ B)
    (f : Y → ℝ) (hf : ∀ y ∈ B, 0 ≤ f y) :
    (𝔼 x ∈ A, f (g x)) ≤ ((B.card : ℝ) / A.card) * (𝔼 y ∈ B, f y) := by
  have h := expect_subset_le_card_ratio (A.image g) B (hA.image g)
    (Finset.image_subset_iff.mpr hB) f hf
  simpa only [Finset.expect_image hg, Finset.card_image_of_injOn hg] using h

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {I K : Type*} [Fintype I] [Fintype K]
variable (root : K → ℤ) (stride : I → ℕ)
variable (T : Finset (ColumnResiduePattern (Option K) I stride))
variable (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
variable (D : (Option K × I → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
variable (hD : 0 < selectedResidueDensityMass stride T W D) {C ε : ℝ}

end Erdos3.BooleanCubeKernel

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

theorem containedProgressionCubeMap_cube (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) :
    IntegerScalarCube L (fun i => (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ)) := by
  by_cases hz : IntegerScalarCube H (fun i => (z i : ℤ))
  · simp_rw [containedProgressionCubeMap_value I L H step c hL hsubset z hz]
    exact integerScalarCube_progression c hsubset _ hz
  · simp only [containedProgressionCubeMap, dif_neg hz]
    intro t
    simp only [integerScalarCubeValue, Finset.sum_const_zero, add_zero]
    exact ⟨le_rfl, Nat.cast_pos.mpr hL⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarKernel_explicit_probability_le_of_card_le (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ scalarKernelAdjustedAccuracy I J M D η := by
  let B := scalarKernelCutoff I J M D η
  let κ := scalarKernelThreshold I J M D η
  let ε := scalarKernelAdjustedAccuracy I J M D η
  obtain ⟨hB, hsize, _, hinv, hmesh, htail⟩ := scalarKernelCutoff_bounds I J hM hD hη
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hκ : 0 < κ := scalarKernelThreshold_pos I J hM hD hη
  have hε : 0 < ε := scalarKernelAdjustedAccuracy_pos I J hM hD hη
  have hsizeL : Fintype.card I + 1 ≤ L := hsize.trans hlarge
  have hsmall : 1 / (B : ℝ) ≤ κ := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hκ).mp hinv
    nlinarith
  have hmeshL : coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) / L ≤ κ := by
    apply (div_le_iff₀ hL').mpr
    have hBL : (scalarKernelCutoff I J M D η : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlarge
    have h := (div_le_iff₀ hκ).mp (hmesh.trans hBL)
    nlinarith
  have htailB : scalarKernelTailConstant I J / B ≤ ε / 2 := by
    apply (div_le_iff₀ hB').mpr
    have h := (div_le_iff₀ hε).mp htail
    nlinarith
  have hJpos : 0 < Fintype.card J := by
    exact lt_of_lt_of_le (Nat.mul_pos Fintype.card_pos (by omega)) hJ
  have hN : 0 < Fintype.card (J × Option I) := by
    rw [Fintype.card_prod, Fintype.card_option]
    exact Nat.mul_pos hJpos (by omega)
  have hreal := discrete_minor_threshold_probability (Fintype.equivFin (J × Option I)) hN
    s s.injective L hL hsizeL ε hε hmeshL
  have hminor : (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => |normalizedScalarCubeMinor s x| ≤ 1 / (B : ℝ)) ≤ ε / 2 := by
    apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans hreal
    intro x hx
    exact hx.trans hsmall
  have hcoker := scalarCube_largeCokernel_probability_le_of_card_le (I := I) (J := J) L B hL hsizeL hB hJ
  apply (scalarKernel_bad_event_le _ s (1 / (B : ℝ)) B (one_div_pos.mpr hB')).trans
  exact (add_le_add hminor (hcoker.trans htailB)).trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

variable (selection : Fin dim ↪ G) (M : ℕ)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)

include hbases htest

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedRowsProjectedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {L H step : ℕ} (c : ℤ) (hL : 0 < L) (hH : 0 < H) (hstep : 0 < step)
variable (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))

include hstep in
theorem containedProgressionCubeMap_injOn :
    Set.InjOn (containedProgressionCubeMap α L H step c hL hsubset) (integerScalarCubeSet α H) := by
  intro x hx y hy hxy
  have hx' := (mem_integerScalarCubeSet H x).mp hx
  have hy' := (mem_integerScalarCubeSet H y).mp hy
  funext i
  apply Subtype.ext
  have hi := congrArg (fun z : IntegerScalarCubeBox α L => (z i : ℤ)) hxy
  rw [containedProgressionCubeMap_value α L H step c hL hsubset x hx',
    containedProgressionCubeMap_value α L H step c hL hsubset y hy'] at hi
  have hs : (step : ℤ) ≠ 0 := by exact_mod_cast hstep.ne'
  exact mul_left_cancel₀ hs (add_left_cancel hi)

theorem integerScalarCubeWeights_mean_finset (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox α L → ℝ) :
    (integerScalarCubeWeights α L hL).mean f = 𝔼 x ∈ integerScalarCubeSet α L, f x := by
  let : Nonempty (IntegerScalarCubeBox α L) := ⟨integerScalarCubeBoxZero α L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet α L)
    (integerScalarCubeReference_mass_pos α L hL) f
  simpa only [integerScalarCubeWeights, integerScalarCubeReference,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    Finset.sum_coe_sort, Finset.card_univ, Fintype.card_coe] using h

include hstep in
theorem containedScalarProgression_mean_le_card_ratio
    (f : IntegerScalarCubeBox α L → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).mean f ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).mean f := by
  rw [FiniteProbabilityWeights.fiberLaw_mean,
    integerScalarCubeWeights_mean_finset, integerScalarCubeWeights_mean_finset]
  apply expect_injective_le_card_ratio _ _ (integerScalarCubeSet_nonempty α H hH)
    _ (containedProgressionCubeMap_injOn c hL hstep hsubset)
  · intro x _
    exact (mem_integerScalarCubeSet L _).mpr (containedProgressionCubeMap_cube α L H step c hL hsubset x)
  · intro y _
    exact hf y

include hstep in
theorem containedScalarProgression_weight_le_card_ratio (y : IntegerScalarCubeBox α L) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).weight y ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).weight y := by
  have h := containedScalarProgression_mean_le_card_ratio c hL hH hstep hsubset
    (fun z => if z = y then 1 else 0) (fun z => by split <;> norm_num)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

theorem integerScalarCubeSet_card_ratio_le {L H D : ℕ}
    (hH : 0 < H) (hsize : Fintype.card α + 1 ≤ H) (hLH : L ≤ D * H) :
    ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card ≤
      scalarCubeResidueDensityCap α D := by
  let n := Fintype.card α + 1
  let h := H / n
  have hn : 0 < n := Nat.succ_pos _
  have hh : 0 < h := Nat.div_pos hsize hn
  have hlow := integerScalarCubeSet_card_lower α H h hh (Nat.mul_div_le H n)
  have hfloor : (H : ℝ) ≤ 2 * (n : ℝ) * h := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hLH' : (L : ℝ) ≤ D * (H : ℝ) := by exact_mod_cast hLH
  have hscale : 2 * (L : ℝ) ≤ (4 * (n : ℝ) * D) * h := by
    nlinarith only [hLH', mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg D)]
  have hpow := pow_le_pow_left₀ (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) hscale n
  rw [mul_pow (4 * (n : ℝ) * D) (h : ℝ)] at hpow
  have hupper : ((integerScalarCubeSet α L).card : ℝ) ≤ (2 * (L : ℝ)) ^ n := by
    have h := Finset.card_le_univ (integerScalarCubeSet α L)
    rw [integerScalarCubeBox_card] at h
    exact_mod_cast h
  have hcard : 0 < ((integerScalarCubeSet α H).card : ℝ) := by
    exact_mod_cast (integerScalarCubeSet_nonempty α H hH).card_pos
  apply (div_le_iff₀ hcard).mpr
  apply (hupper.trans hpow).trans
  change (4 * (n : ℝ) * D) ^ n * (h : ℝ) ^ n ≤ _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlow)
    (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Nat.cast_nonneg D)) n)

theorem containedProgressionCubeLaw_eventProbability_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hstep : ∀ k, 0 < step k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (E : (∀ k, IntegerScalarCubeBox α (L k)) → Prop) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E ≤
      (∏ k, ((integerScalarCubeSet α (L k)).card : ℝ) / (integerScalarCubeSet α (H k)).card) *
        (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (L k) (hL k))).eventProbability E := by
  let p := fun k => integerScalarCubeWeights α (H k) (hH k)
  let F := fun k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k)
  let q := fun k => (p k).fiberLaw (F k)
  have ht := FiniteProbabilityWeights.complexMean_pi_transport_fintype p q F (fun _ y => y)
    (fun k φ => ((p k).fiberLaw_complexMean (F k) φ).symm)
    (fun y => ((if E y then 1 else 0 : ℝ) : ℂ))
  have he := congrArg Complex.re ht
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re] at he
  have hlaw : (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E =
      (FiniteProbabilityWeights.pi q).eventProbability E := by
    unfold FiniteProbabilityWeights.eventProbability containedProgressionCubeLaw
    rw [FiniteProbabilityWeights.fiberLaw_mean]
    exact he
  rw [hlaw]
  exact FiniteProbabilityWeights.pi_eventProbability_le q
    (fun k => integerScalarCubeWeights α (L k) (hL k)) _
    (fun k y => containedScalarProgression_weight_le_card_ratio
      (c k) (hL k) (hH k) (hstep k) (hsubset k) y) E

theorem containedProgressionKernel_explicit_probability_le
    {K : Type*} [Fintype K] [DecidableEq K] [Nonempty α]
    (hK : Fintype.card α * (Fintype.card α + 2) ≤ Fintype.card K) (selection : α ↪ K)
    {L D : ℕ} {η : ℝ} (hL : 0 < L) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff α K 1 D η ≤ L)
    (H step : K → ℕ) (c : K → ℤ) (hH : ∀ k, 0 < H k) (hstep : ∀ k, 0 < step k)
    (hLH : ∀ k, L ≤ D * H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ)) :
    (containedProgressionCubeLaw (α := α) (fun _ => L) H step c (fun _ => hL) hH hsubset).eventProbability
      (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
        (scalarKernelCutoff α K 1 D η) x) ≤ η := by
  let C := scalarKernelConditioningConstant α K 1 D
  have hC : 0 < C := scalarKernelConditioningConstant_pos α K (by norm_num) hD
  have hsize (k) : Fintype.card α + 1 ≤ H k := by
    simpa only [Nat.mul_one] using scalarKernelCutoff_window_size α K
      (show 0 < 1 by norm_num) hD hη hlarge (hLH k)
  have hcap : (∏ k, ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α (H k)).card) ≤ C := by
    calc
      _ ≤ ∏ _k : K, scalarCubeResidueDensityCap α D := Finset.prod_le_prod
        (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (fun k _ => integerScalarCubeSet_card_ratio_le (hH k) (hsize k) (hLH k))
      _ = C := by simp only [C, scalarKernelConditioningConstant, Nat.one_mul,
          Finset.prod_const, Finset.card_univ]
  have h := containedProgressionCubeLaw_eventProbability_le (fun _ => L) H step c
    (fun _ => hL) hH hstep hsubset
    (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
      (scalarKernelCutoff α K 1 D η) x)
  apply h.trans
  calc
    _ ≤ C * (FiniteProbabilityWeights.pi (fun _ : K => integerScalarCubeWeights α L hL)).eventProbability
        (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
          (scalarKernelCutoff α K 1 D η) x) := mul_le_mul_of_nonneg_right hcap
            (FiniteProbabilityWeights.eventProbability_nonneg _ _)
    _ ≤ C * scalarKernelAdjustedAccuracy α K 1 D η := mul_le_mul_of_nonneg_left
      (scalarKernel_explicit_probability_le_of_card_le α K hK selection (by norm_num) hD hη hL hlarge) hC.le
    _ = η := by
      change C * (η / C) = η
      exact mul_div_cancel₀ η hC.ne'

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

variable (step : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)

variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.containedProgressionKernel_explicit_probability_le.{u_1, u_2} := @OAI.Erdos3.containedProgressionKernel_explicit_probability_le.{u_1, u_2}
