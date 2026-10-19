-- Prove2me | solution 1 for OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:15.140712+00:00
-- url     : https://prove2.me/submissions/c326e309-6b7b-47bb-b6d2-d13aae7199cb

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B084
import Definitions.Def_OAIE3v2B086
import Definitions.Def_OAIE3v2B093
import Theorems.Thm_OAI_Erdos3_scalarCube_largeCokernel_probability_le_of_card_le_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.EmbeddedMatrixDeterminantPolynomial
namespace OAI

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


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


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarKernel_explicit_probability_le_of_card_le_s2_oai (I J : Type*)
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
  have hcoker := scalarCube_largeCokernel_probability_le_of_card_le_s2 (I := I) (J := J) L B hL hsizeL hB hJ
  apply (scalarKernel_bad_event_le _ s (1 / (B : ℝ)) B (one_div_pos.mpr hB')).trans
  exact (add_le_add hminor (hcoker.trans htailB)).trans_eq (by ring)

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le_s2_oai.{u_1, u_2} := @OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le_s2_oai.{u_1, u_2}
