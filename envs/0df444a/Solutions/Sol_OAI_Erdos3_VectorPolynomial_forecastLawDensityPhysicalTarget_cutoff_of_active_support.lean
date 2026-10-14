-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_cutoff_of_active_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T03:20:55.158341+00:00
-- url     : https://prove2.me/submissions/ca201d78-aee9-42b4-ae8a-e24bdce0ed39

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

end Erdos3

end

section

namespace Erdos3

open MeasureTheory _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

theorem restrictedComplexChartDensity_apply (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) (hinj : Set.InjOn q S) {x : X} (hx : x ∈ S) :
    restrictedComplexChartDensity q S c f (q x) = (c : ℂ) * f x := by
  have he : Function.Injective (fun x : S => q x.val) := fun a b h => Subtype.ext (hinj a.property b.property h)
  exact congrArg (fun z : ℂ => (c : ℂ) * z) (he.extend_apply (fun x => f x.val) (fun _ => 0) ⟨x, hx⟩)

theorem restrictedComplexChartDensity_zero (q : X → Y) (S : Set X) (c : ℝ)
    (f : X → ℂ) {y : Y} (hy : y ∉ q '' S) :
    restrictedComplexChartDensity q S c f y = 0 := by
  have hy' : y ∉ Set.range (fun x : S => q x.val) := by
    rintro ⟨x, rfl⟩
    exact hy ⟨x.val, x.property, rfl⟩
  simp only [restrictedComplexChartDensity, Function.extend_apply' _ _ _ hy', mul_zero]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_abs_le {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) {M : ℝ}
    (hf : ∀ t ∈ s.powerset, |f t| ≤ M) :
    |booleanCoefficient f s| ≤ (2 : ℝ) ^ s.card * M := by
  unfold booleanCoefficient
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ) ^ (s \ t).card * f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hf t ht
    _ = _ := by simp

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realAffineCube_abs_le {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (t : Finset α) (k : K) :
    |realAffineCube root difference t k| ≤ (Fintype.card α : ℝ) + 1 := by
  unfold realAffineCube
  calc
    _ ≤ |root k| + |∑ r ∈ t, difference r k| := abs_add_le _ _
    _ ≤ 1 + ∑ r ∈ t, |difference r k| :=
      add_le_add (hroot k) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ _r ∈ t, (1 : ℝ) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun r _ => hd r k))
    _ = 1 + t.card := by simp
    _ ≤ (Fintype.card α : ℝ) + 1 := by
      have hc : (t.card : ℝ) ≤ Fintype.card α := by exact_mod_cast Finset.card_le_univ t
      linarith

theorem real_monomial_eval_abs_le {K : Type*} (e : K →₀ ℕ) (x : K → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hx : ∀ k, |x k| ≤ C) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    |MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ))| ≤ C ^ h := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul]
  change |∏ k ∈ e.support, x k ^ e k| ≤ _
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ k ∈ e.support, C ^ e k := by
      apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _
    _ = C ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ C ^ h := pow_le_pow_right₀ hC he

theorem boundedDegreeRealJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ)
    (hroot : ∀ k, |root k| ≤ 1) (hd : ∀ r k, |difference r k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |boundedDegreeRealJetMatrix root difference h rows o e| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  have hb := booleanCoefficient_abs_le
    (fun t => MvPolynomial.eval (realAffineCube root difference t)
      (MvPolynomial.monomial e.val (1 : ℝ))) (rows o)
    (fun t _ => real_monomial_eval_abs_le e.val _ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      (realAffineCube_abs_le root difference hroot hd t) e.property)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_entry (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (i : I) (j : J) : normalizedIntegerColumns B T P i j = (P i)⁻¹ * B i j * T j := by
  simp [normalizedIntegerColumns, Matrix.diagonal_mul, Matrix.mul_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

end Erdos3

end

section

namespace Erdos3

theorem normalizedIntegerColumns_entry_div {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) (i : I) (j : J) :
    normalizedIntegerColumns A T P i j = (A i j : ℝ) * T j / P i := by
  rw [normalizedIntegerColumns_entry]
  simp only [div_eq_mul_inv]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

variable {I J R : Type*} [Fintype I] (s : I ↪ J)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerNormalizedJetColumns
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem real_monomial_eval_div_scale {K : Type*} (e : K →₀ ℕ) (x T : K → ℝ) :
    MvPolynomial.eval (fun k => x k / T k) (MvPolynomial.monomial e (1 : ℝ)) =
      MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℝ)) / monomialScale T e := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, monomialScale, Finsupp.prod,
    div_pow, Finset.prod_div_distrib]

theorem integer_monomial_eval_cast {K : Type*} (e : K →₀ ℕ) (x : K → ℤ) :
    (MvPolynomial.eval x (MvPolynomial.monomial e (1 : ℤ)) : ℝ) =
      MvPolynomial.eval (fun k => (x k : ℝ)) (MvPolynomial.monomial e (1 : ℝ)) := by
  classical
  simp only [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, Int.cast_prod, Int.cast_pow]

theorem normalizedIntegerMonomialJetMatrix_eq {α K O J : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (e : J → K →₀ ℕ) (vertices : Finset α → K → ℤ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun j => MvPolynomial.monomial (e j) 1) vertices rows)
      (fun j => H / monomialScale T (e j)) (fun _ => H) =
    realJetMatrix (fun j => MvPolynomial.monomial (e j) 1)
      (fun t k => (vertices t k : ℝ) / T k) rows := by
  ext o j
  rw [normalizedIntegerColumns_entry_div]
  change ((booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
    (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o) : ℤ) : ℝ) *
      (H / monomialScale T (e j)) / H =
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => (vertices t k : ℝ) / T k)
      (MvPolynomial.monomial (e j) (1 : ℝ))) (rows o)
  have hcast := booleanCoefficient_map (Int.castRingHom ℝ)
    (fun t => MvPolynomial.eval (vertices t) (MvPolynomial.monomial (e j) (1 : ℤ))) (rows o)
  change ((booleanCoefficient _ (rows o) : ℤ) : ℝ) =
    booleanCoefficient (fun t => (MvPolynomial.eval (vertices t)
      (MvPolynomial.monomial (e j) (1 : ℤ)) : ℝ)) (rows o) at hcast
  rw [hcast]
  simp only [real_monomial_eval_div_scale, integer_monomial_eval_cast]
  rw [booleanCoefficient_div]
  simp [div_eq_mul_inv, hH, mul_assoc, mul_comm]

theorem realAffineCube_normalized_integer {α K : Type*}
    (root : K → ℤ) (difference : α → K → ℤ) (T : K → ℝ) (t : Finset α) (k : K) :
    realAffineCube (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) t k =
        (integerAffineCube root difference t k : ℝ) / T k := by
  simp only [realAffineCube, integerAffineCube, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]

theorem normalizedBoundedIntegerJetMatrix_eq {α K O : Type*}
    [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α)
    (T : K → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (boundedDegreeIntegerJetMatrix root difference h rows)
      (fun e => H / monomialScale T e.val) (fun _ => H) =
    boundedDegreeRealJetMatrix (fun k => (root k : ℝ) / T k)
      (fun r k => (difference r k : ℝ) / T k) h rows := by
  have hv : (fun t k => (integerAffineCube root difference t k : ℝ) / T k) =
      realAffineCube (fun k => (root k : ℝ) / T k)
        (fun r k => (difference r k : ℝ) / T k) := by
    funext t k
    exact (realAffineCube_normalized_integer root difference T t k).symm
  have he := normalizedIntegerMonomialJetMatrix_eq
    (fun e : BoundedIntegerExponent K h => e.val) (integerAffineCube root difference) rows T hH
  rw [hv] at he
  exact he

end Erdos3

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedRealCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedRealPoint_coordinates (x : EuclideanSpace ℝ D) :
    mixedRealPoint W b o (mixedRealCoordinates W b o x) = x := by
  change (normalizedOrthogonalChart W b).symm
    ((orthonormalChart o) ((orthonormalChart o).symm ((normalizedOrthogonalChart W b) x).1),
      ((normalizedOrthogonalChart W b) x).2) = x
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

omit [Fintype D] in
theorem smallBoxTorusKernel_local (H : (D → ℝ) → ℝ)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ)
    (hx : ∀ i, |x i| < 1/2) :
    smallBoxTorusKernel H (fun i => (x i : UnitAddCircle)) = H x := by
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact positiveIntegerPeriodization_local H hs x hx

end Erdos3

end

section

namespace Erdos3
open scoped Classical

variable {D : Type*} [Fintype D]

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelLiftChart
namespace OAI

section

namespace Erdos3

variable {G H X : Type*} [AddCommGroup G] [AddCommGroup H]
variable (C : G →+ H) (s : X → G) (q : X → H)

theorem kernelLiftChart_injOn (hproj : ∀ x, C (s x) = q x)
    {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × C.ker => s p.1 + p.2.val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  change s x.1 + x.2.val = s y.1 + y.2.val at he
  have hkx : C x.2.val = 0 := x.2.property
  have hky : C y.2.val = 0 := y.2.property
  have hb : q x.1 = q y.1 := by
    have ht := congrArg C he
    simpa only [map_add, hproj, hkx, hky, add_zero] using ht
  have hxy : x.1 = y.1 := hq hx.1 hy.1 hb
  apply Prod.ext hxy
  apply Subtype.ext
  rw [hxy] at he
  exact add_left_cancel he

theorem kernelLiftChart_relabel_injOn {R : Type*} (e : R ≃ C.ker)
    (hproj : ∀ x, C (s x) = q x) {S : Set X} (hq : Set.InjOn q S) :
    Set.InjOn (fun p : X × R => s p.1 + (e p.2).val) (S ×ˢ Set.univ) := by
  intro x hx y hy he
  have hp := kernelLiftChart_injOn C s q hproj hq
    (show (x.1, e x.2) ∈ S ×ˢ Set.univ from ⟨hx.1, Set.mem_univ _⟩)
    (show (y.1, e y.2) ∈ S ×ˢ Set.univ from ⟨hy.1, Set.mem_univ _⟩) he
  exact Prod.ext (congrArg (fun z : X × C.ker => z.1) hp)
    (e.injective (congrArg (fun z : X × C.ker => z.2) hp))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_injOn
    {Ω : Set (EuclideanSpace ℝ D)} (hΩ : Ω ⊆ standardLatticeSmallBox D) :
    Set.InjOn (normalizedCoveredChart W b hb bW d)
      ((normalizedLatticePoint W b ⁻¹' Ω) ×ˢ Set.univ) :=
  kernelLiftChart_relabel_injOn _ _ _
    (coverKernelBasisEquiv _ bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
    (normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)))
    (normalizedLatticeQuotient_injOn W b hb hΩ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) := by
  intro x hx y hy he
  funext j t
  exact normalizedCoveredChart_injOn _ (b j) (hb j) (bW j) d (hΩ j t)
    (hx j (Set.mem_univ j) t (Set.mem_univ t)) (hy j (Set.mem_univ j) t (Set.mem_univ t))
    (congrFun (congrFun he j) t)

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoveredChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [∀ j, Fintype (E j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem mixedCoveredJetChart_injOn (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j)) :
    Set.InjOn (mixedCoveredJetChart U o b hb bW d) (mixedCoveredJetRegion U o b d Ω) := by
  intro z hz w hw he
  apply (mixedCoveredJetCoordinatesEquiv U o d).injective
  exact coveredJetChart_injOn U b hb bW d Ω hΩ hz hw he

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedJetChartSupport
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem boundedCoefficientJetMatrix_scaled_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (A : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hA : ∀ i k, |(A i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    |(boundedCoefficientJetMatrix root A h rows o e : ℝ)| / monomialScale T e.val ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  let e' := boundedCoefficientIntegerExponentEquiv K h e
  have he := congrFun (congrFun (normalizedBoundedIntegerJetMatrix_eq root A h rows T
    (H := 1) one_ne_zero) o) e'
  rw [normalizedIntegerColumns_entry_div] at he
  have hb := boundedDegreeRealJetMatrix_entry_bound _ _ hroot hA h rows o e'
  rw [← he] at hb
  change |(boundedDegreeIntegerJetMatrix root A h rows o e' : ℝ)| / monomialScale T e'.val ≤ _
  simpa only [div_one, mul_one_div, abs_div, abs_of_pos (monomialScale_pos T hT e'.val)] using hb

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedPhysicalChartBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootAllowance_zero :
    allocatedPhysicalRootAllowance B U b S (fun _ => 0) = 1 := by
  simp [allocatedPhysicalRootAllowance]

variable {α : Type*} (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))

theorem allocatedPhysicalCube_tuple_coordinate_bound (a : Option α) (k : LayerSamplerVariables G I n B) :
    |((Sum.elim (fun g => (x g a : ℤ)) (fun j => (y j a : ℤ)) k : ℤ) : ℝ)| ≤ layerSamplerBox B U b S k := by
  cases k with
  | inl g =>
    have hx := Finset.mem_Ico.mp (x g a).property
    change |((x g a : ℤ) : ℝ)| ≤ (S.value : ℝ)
    exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
  | inr j =>
    have hy := Finset.mem_Ico.mp (y j a).property
    change |((y j a : ℤ) : ℝ)| ≤ (allocatedPrincipalSides B U b S j : ℝ)
    exact_mod_cast abs_le.mpr ⟨hy.1, hy.2.le⟩

theorem allocatedPhysicalCube_directions_normalized (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U b S x y i k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  rw [abs_div, abs_of_pos hT, div_le_one hT]
  exact allocatedPhysicalCube_tuple_coordinate_bound B U b S x y (some i) k

theorem allocatedPhysicalCube_root_normalized (c : LayerSamplerVariables G I n B → ℤ)
    (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ) / layerSamplerBox B U b S k| ≤
      allocatedPhysicalRootAllowance B U b S c := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  have hsum : |(c k : ℝ)| / layerSamplerBox B U b S k ≤
      ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k :=
    Finset.single_le_sum (fun v _ => div_nonneg (abs_nonneg (c v : ℝ))
      (zero_le_one.trans (layerSamplerBox_one_le B U b S v))) (Finset.mem_univ k)
  have hx := allocatedPhysicalCube_tuple_coordinate_bound B U b S x y none k
  rw [abs_div, abs_of_pos hT]
  have hr : |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ)| ≤
      |(c k : ℝ)| + layerSamplerBox B U b S k := by
    unfold allocatedPhysicalCubeRoot
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hx)
  calc
    _ ≤ (|(c k : ℝ)| + layerSamplerBox B U b S k) / layerSamplerBox B U b S k :=
      div_le_div_of_nonneg_right hr hT.le
    _ = |(c k : ℝ)| / layerSamplerBox B U b S k + 1 := by rw [add_div, div_self hT.ne']
    _ ≤ allocatedPhysicalRootAllowance B U b S c := by
      dsimp [allocatedPhysicalRootAllowance]
      linarith

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerIntegerCoefficient_scaled_bound (j : Fin m) (hσ1 : σ j ≤ 1)
    (i : Fin (n j)) (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (z : ℤ) (hz : z ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i e).support) :
    |(z : ℝ) / basisAxisScale (b j) i| * monomialScale (layerSamplerBox B U b S) e.val ≤ R j := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  exact (allocatedIntegerCoefficient_bound (layerIntegerPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (j.val + 1) (basisAxisScale (b j) i) S.value (layerTailDegree m) (Nat.zero_lt_succ _) (basisAxisScale_pos (b j) i)
    S.positive (layerSamplerBox B U b S) hT (layerSamplerBox_le B U b S) Subtype.val
    (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) hσ1 (S.gap j i) (S.width j)
    (layerIntegerPrincipalSlots_not_constant B j i) rfl
    (layerSamplerSides_integer_principal B U b R S.value j i) e hz).trans (by linarith [hR j])

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)


variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "degree" => j.val + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.StandardJetFourier
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical

theorem euclideanAmbientTorus_normalized {D : Type*} [Fintype D]
    (U : Submodule ℝ (D → ℝ)) {n : ℕ}
    (b : Basis (Fin n) ℝ (euclideanSubspace U)ᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice (euclideanSubspace U))
    (x : euclideanSubspace U × (Fin n → ℤ)) (i : D) :
    subspaceAmbientTorus U (euclideanSubspaceTorusEquiv U
      (normalizedLatticeQuotient (euclideanSubspace U) b hb x)) i =
        (normalizedLatticePoint (euclideanSubspace U) b x i : UnitAddCircle) := by
  let u := normalizedLatticeRepresentative (euclideanSubspace U) b hb x
  have hu : QuotientAddGroup.mk' _ u = normalizedLatticeQuotient (euclideanSubspace U) b hb x :=
    normalizedLatticeRepresentative_mk (euclideanSubspace U) b hb x
  rw [← hu, euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk, euclideanSubspaceArrayEquiv_apply]
  apply sub_eq_zero.mp
  rw [← AddCircle.coe_sub]
  obtain ⟨z, hz⟩ := (mem_standardEuclideanLattice D _).mp
    (normalizedLatticePoint_sub_mem_of_mk_eq (euclideanSubspace U) b hb u x hu) i
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨z, by simpa only [zsmul_eq_mul, mul_one, PiLp.sub_apply] using hz⟩

theorem normalizedCoveredChart_projection {D Q : Type*} [Fintype D] [Fintype Q]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) {n : ℕ} (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (bW : Basis Q ℤ (latticeSection (standardEuclideanLattice D) W))
    (d : ℕ) [NeZero d] (x : (W × (Fin n → ℤ)) × (Q → ZMod d)) :
    quotientIntegerCover (latticeSection (standardEuclideanLattice D) W).toAddSubgroup d
      (normalizedCoveredChart W b hb bW d x) = normalizedLatticeQuotient W b hb x.1 := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (Nat.pos_of_ne_zero (NeZero.ne d))
  have hk : quotientIntegerCover Γ d (e x.2).val = 0 := (e x.2).property
  change quotientIntegerCover Γ d (normalizedCoverLift W b hb d x.1 + (e x.2).val) = _
  rw [map_add,
    normalizedCoverLift_projection W b hb d (Nat.pos_of_ne_zero (NeZero.ne d)), hk, add_zero]

namespace VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (O j)] in
theorem coveredJetAmbientTorus_chart
    {I Q : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Q j)] {n : Fin m → ℕ}
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d) :
    coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z) =
      fun a => (mixedJetAmbientPoint U b o z.1 a : UnitAddCircle) := by
  funext a
  change subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
    (quotientIntegerCover _ d (normalizedCoveredChart _ (b a.1) (hb a.1) (bW a.1) d
      (mixedCoveredJetCoordinates U o d z a.1 a.2.1)))) a.2.2 = _
  rw [normalizedCoveredChart_projection]
  exact euclideanAmbientTorus_normalized (U a.1) (b a.1) (hb a.1) _ a.2.2

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ}
variable {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical Matrix

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalSingleSiteAmbient
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {X : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ) [NeZero d]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem physicalSingleSiteValue_ambient (w : X → ℝ) :
    coveredJetAmbientTorus U d (physicalSingleSiteValue U d p hm w) =
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
        ((eval w (p a.1)) a.2.2 : UnitAddCircle) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  funext a
  rcases a with ⟨j, t, i⟩
  cases t
  change subspaceAmbientTorus (U j) (euclideanSubspaceTorusEquiv (U j)
    (d • (euclideanSubspaceTorusEquiv (U j)).symm
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
        (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j)))))) i = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  change subspaceAmbientTorus (U j) (quotientIntegerCover _ d
    (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U j))
      (fun _ => (d : ℝ)⁻¹ • eval w (restrictCoefficients (U j) (p j) (hm j))))) i = _
  rw [quotientIntegerCover_mk, subspaceAmbientTorus_mk]
  simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [eval_restrictCoefficients]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalCoveredDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical

theorem standardLatticeClosedQuarterBox_subset_smallBox (J : Type*) [Fintype J] :
    standardLatticeClosedQuarterBox J ⊆ standardLatticeSmallBox J := by
  intro x hx i
  exact (hx i).trans_lt (by norm_num)

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))

local notation "root" => allocatedPhysicalCubeRoot B U b S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoordinateCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem normalizedCoordinateCutoff_spec (D : Type*) [Fintype D]
    (r : ℝ≥0) (hr : 0 < r) :
    ContDiff ℝ ∞ (normalizedCoordinateCutoff D r hr) ∧
      HasCompactSupport (normalizedCoordinateCutoff D r hr) ∧
      (∀ v, 0 ≤ normalizedCoordinateCutoff D r hr v ∧ normalizedCoordinateCutoff D r hr v ≤ 1) ∧
      (∀ v, (∀ d, |v d| ≤ (r : ℝ)) → normalizedCoordinateCutoff D r hr v = 1) ∧
      (∀ v, normalizedCoordinateCutoff D r hr v ≠ 0 → ∀ d, |v d| ≤ 2 * (r : ℝ)) ∧
      LipschitzWith (Fintype.card D * normalizedSiteCutoffBound / (2 * r))
        (normalizedCoordinateCutoff D r hr) :=
  Classical.choose_spec (exists_normalized_site_cutoff (D := D) r hr)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

variable {α : Type*} [Fintype α] [DecidableEq α]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (r : ℝ≥0) (hr : 0 < r) (f : (LayerSamplerAxis I n → ℝ) → ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)

theorem allocatedFullAmbientSiteCoordinates_point
    (z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ)) :
    allocatedFullAmbientSiteCoordinates (R := R) U b o (mixedJetAmbientPoint U b o z) =
      allocatedFullMixedSiteValue (R := R) U b (fun j => mixedArrayRegroup _ _ _ (z j) ()) := by
  have hp (j : Fin m) : (EuclideanSpace.equiv (J j) ℝ).symm
      (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
      normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ())) := by
    have hv : (fun k => mixedJetAmbientPoint U b o z ⟨j, (), k⟩) =
        (EuclideanSpace.equiv (J j) ℝ) (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) ()))) := by
      funext k
      rfl
    rw [hv, ContinuousLinearEquiv.symm_apply_apply]
  funext a
  rcases a with ⟨j, i | i⟩ <;>
    dsimp only [allocatedFullAmbientSiteCoordinates, allocatedFullMixedSiteValue] <;>
    rw [hp, mixedRealCoordinates_integer] <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

variable {α : Type*} [Fintype α] [DecidableEq α]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedBufferedAmbientCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

theorem allocatedFullAmbientSiteCoordinates_norm_bound
    (hR : ∀ j, 0 < R j) (z : ambient → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ a, |allocatedFullAmbientSiteCoordinates (R := R) U b o z a| ≤ T)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (j : Fin m) :
    ‖(EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)‖ ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * (T * R j)) := by
  let v := (EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)
  let w := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j) v
  have hu (i : I j) : |w.1 i| ≤ T * R j := by
    have h := hz ⟨j, .inl i⟩
    change |w.1 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have hv (i : Fin (n j)) : |w.2 i| ≤ T * R j := by
    have h := hz ⟨j, .inr i⟩
    change |w.2 i / R j| ≤ T at h
    rw [abs_div, abs_of_pos (hR j)] at h
    exact (div_le_iff₀ (hR j)).mp h
  have h := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg hT (hR j).le) (hchart j) w.1 w.2 hu hv
  dsimp only [w] at h
  rw [Prod.mk.eta, mixedRealPoint_coordinates] at h
  exact h

variable (r : ℝ≥0) (hr : 0 < r)

theorem allocatedBufferedAmbientCutoff_support (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : ambient → ℝ) (hz : allocatedBufferedAmbientCutoff (R := R) U b o r hr z ≠ 0) :
    ∀ a, |z a| ≤ 1 / 4 := by
  have hcoord := (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.2.1
    (allocatedFullAmbientSiteCoordinates (R := R) U b o z) hz
  rintro ⟨j, t, k⟩
  cases t
  have h := (allocatedFullAmbientSiteCoordinates_norm_bound U b o hR z (by positivity)
    hcoord C hC hchart j).trans (hbudget j)
  exact (PiLp.norm_apply_le ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, (), k⟩)) k).trans h

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR hσ in
theorem allocatedOriginalSampleInactiveCoefficients_supported
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample j)) :
    ∀ a d, allocatedOriginalSampleInactiveCoefficients B selected sample a d ∈
      (allocatedLayerIntegerPMFs B U b hR hσ S (selected a).1 (selected a).2 d).support := by
  intro a d
  exact ((mixedArraySupported_iff_rows _ _ _ (sample (selected a).1)).mp
    (hs (selected a).1)).2 (selected a).2 d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedNormalizedTorusCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
local notation "ambient" => JetAmbientIndex (fun _ : Fin m => Unit) J

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedBufferedTorusCutoff_local (z : ambient → ℝ) (hz : ∀ i, |z i| < 1 / 2) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr (fun i => (z i : UnitAddCircle)) =
      allocatedBufferedAmbientCutoff (R := R) U b o r hr z := by
  apply smallBoxTorusKernel_local _ _ z hz
  intro v hv i
  exact (allocatedBufferedAmbientCutoff_support U b o r hr hR C hC hchart hbudget v hv i).trans_lt (by norm_num)

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)

variable (r : ℝ≥0) (hr : 0 < r)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable {G : Type*} [Fintype G]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (D : Fin m → ℝ≥0)
variable (hD : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ D j * ‖v‖)
variable (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ} (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v,
  ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j,
  C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

include hR hC hchart hbudget in
theorem forecastBufferedPhysicalChartCutoff_eq
    (z : MixedCoveredJetSource I single E n d) (hz : z ∈ region) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr
        (coveredJetAmbientTorus U d (chart z)) =
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
        (allocatedFullMixedSiteValue (R := R) U b
          (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ i, |mixedJetAmbientPoint U b o z.1 i| < 1 / 2 := by
    rintro ⟨j, t, i⟩
    exact ((hz j (mem_univ j) t (mem_univ t)).1 i).trans_lt (by norm_num)
  rw [allocatedBufferedTorusCutoff_local U b o r hr hR C hC hchart hbudget _ hsmall]
  unfold allocatedBufferedAmbientCutoff
  rw [allocatedFullAmbientSiteCoordinates_point]

include hR hC hchart hbudget in
theorem forecastBufferedPhysicalChartCutoff_eq_one
    (z : MixedCoveredJetSource I single E n d) (hz : z ∈ region)
    (hcut : normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())) = 1) :
    allocatedBufferedTorusCutoff (R := R) U b o r hr
      (coveredJetAmbientTorus U d (chart z)) = 1 :=
  (forecastBufferedPhysicalChartCutoff_eq U b o r hr hR C hC hchart hbudget hb bW d z hz).trans hcut

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical Matrix

theorem integerMatrix_mulVec_scaled_bound {O K : Type*} [Fintype K]
    (A : Matrix O K ℤ) (z : K → ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    {H M R : ℝ} (hM : 0 ≤ M)
    (hA : ∀ o k, |(A o k : ℝ)| / T k ≤ M)
    (hz : ∀ k, |(z k : ℝ) / H| * T k ≤ R) (o : O) :
    |((A *ᵥ z) o : ℝ) / H| ≤ (Fintype.card K : ℝ) * M * R := by
  calc
    _ = |∑ k, (A o k : ℝ) * ((z k : ℝ) / H)| := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
        Finset.sum_div, mul_div_assoc]
    _ ≤ ∑ k, |(A o k : ℝ) * ((z k : ℝ) / H)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : K, M * R := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      calc
        _ ≤ (M * T k) * |(z k : ℝ) / H| :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ (hT k)).mp (hA o k)) (abs_nonneg _)
        _ = M * (|(z k : ℝ) / H| * T k) := by ring
        _ ≤ M * R := mul_le_mul_of_nonneg_left (hz k) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

theorem rationalInactiveForecast_eq_zero_of_not_mem_range
    {I Ω Z J : Type*} [Fintype I] [Fintype Ω] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights Ω)
    (gridPoint : I → Z) (Y : I → Ω → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (b : J → ZMod N)
    (hz : ∀ i, gridPoint i ≠ z) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  simp [rationalInactiveForecast, FiniteProbabilityWeights.fiberMean, hz,
    FiniteProbabilityWeights.mean]

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*}

theorem forecastInactiveFixedOutput_scaled_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (a : A) (row : (Finset.univ : Finset (Finset Empty))) :
    |(forecastInactiveFixedOutput B U b S selected c x y a row : ℝ) /
      basisAxisScale (b (selected a).1) (selected a).2| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) * R (selected a).1 := by
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y
  let dirs := allocatedPhysicalCubeDirections B U b S x y
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => zero_lt_one.trans_le (layerSamplerBox_one_le B U b S k)
  have hroot (k) : |(root k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
    simpa only [allocatedPhysicalRootAllowance_zero] using
      allocatedPhysicalCube_root_normalized B U b S x y (fun _ => 0) k
  have hmat : ∀ o e,
      |(boundedCoefficientJetMatrix root dirs ((selected a).1.val + 1)
        (fun t : (Finset.univ : Finset (Finset Empty)) => (t : Finset Empty)) o e : ℝ)| /
        monomialScale (layerSamplerBox B U b S) e.val ≤ 1 := by
    intro o e
    simpa using boundedCoefficientJetMatrix_scaled_entry_bound root dirs
      (layerSamplerBox B U b S) hT hroot
      (allocatedPhysicalCube_directions_normalized B U b S x y) _ _ o e
  have hbound := integerMatrix_mulVec_scaled_bound _ (c a)
    (fun e : BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) => monomialScale (layerSamplerBox B U b S) e.val)
    (fun e => monomialScale_pos _ hT e.val) zero_le_one hmat
    (fun e => allocatedLayerIntegerCoefficient_scaled_bound B U b hR hσ S
      (selected a).1 (hσ1 a) (selected a).2 e (c a e) (hc a e)) row
  simpa only [forecastInactiveFixedOutput, root, dirs, mul_one] using hbound

theorem forecastInactiveFixedOutput_normalized_bound
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S))
    (a : A) (row : (Finset.univ : Finset (Finset Empty))) :
    |(forecastInactiveFixedOutput B U b S selected c x y a row : ℝ) /
      basisAxisScale (b (selected a).1) (selected a).2 / R (selected a).1| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) := by
  rw [abs_div, abs_of_pos (hR _), div_le_iff₀ (hR _)]
  exact forecastInactiveFixedOutput_scaled_bound B U b S hR hσ selected c hc hσ1 x y a row

theorem forecastInactiveFixed_rational_eq_zero_of_outside
    (selected : A → Σ j : Fin m, Fin (n j))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (x : G → IntegerScalarCubeBox Empty S.value)
    {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
    (law : FiniteProbabilityWeights
      (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)))
    (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S) → FiniteProbabilityWeights Ω)
    (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
      (allocatedPrincipalSides B U b S) → Ω → Out → ℤ)
    (N : ℕ) [NeZero N] (volume : ℝ) (z : A → ℤ) (out : Out → ZMod N)
    (a : A)
    (hz : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
        ((selected a).1.val + 1)) : ℝ) <
      |(z a : ℝ) / basisAxisScale (b (selected a).1) (selected a).2 / R (selected a).1|) :
    rationalInactiveForecast law active (forecastInactiveFixedOutput B U b S selected c x)
      Y N volume (fun a _ => z a) out = 0 := by
  apply rationalInactiveForecast_eq_zero_of_not_mem_range
  intro y heq
  let row : (Finset.univ : Finset (Finset Empty)) := ⟨∅, Finset.mem_univ _⟩
  have hb := forecastInactiveFixedOutput_normalized_bound B U b S hR hσ
    selected c hc hσ1 x y a row
  rw [heq] at hb
  exact (not_lt_of_ge hb) hz

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

variable {A : Type*}
variable (selected : A → Σ j : Fin m, Fin (n j))

variable (c : ∀ a : A, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
  ((selected a).1.val + 1) → ℤ)
variable (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
  (selected a).1 (selected a).2 d).support)
variable (hσ1 : ∀ a : A, σ (selected a).1 ≤ 1)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S))) (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S)) → FiniteProbabilityWeights Ω)
variable (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U b S)) → Ω → Out → ℤ) (N : ℕ) [NeZero N]
variable (volume : ℝ) (out : Out → ZMod N)
variable (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))

include hR hσ hc hσ1

theorem forecastOriginalSource_coordinates_bound
    (hexhaustive : ∀ a, (allocatedShortAxis (I := I) U b S.value) a → ∃ i, (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    {r : ℝ}
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (hactive : ∀ a, ¬(allocatedShortAxis (I := I) U b S.value) a → |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r)
    (hf : (rationalInactiveForecast law active
  (forecastInactiveFixedOutput B U b S selected c x) Y N volume
  (fun a _ => Prod.snd (w (Sigma.fst (selected a))) (Sigma.snd (selected a))) out) ≠ 0) : ∀ a, |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r := by
  intro a
  by_cases ha : (allocatedShortAxis (I := I) U b S.value) a
  · obtain ⟨i, haxis⟩ := hexhaustive a ha
    rw [← haxis]
    change |((w (selected i).1).2 (selected i).2 : ℝ) /
      basisAxisScale (b (selected i).1) (selected i).2 / R (selected i).1| ≤ r
    by_contra hn
    have hlarge := lt_of_le_of_lt (hradius (selected i).1) (lt_of_not_ge hn)
    exact hf (forecastInactiveFixed_rational_eq_zero_of_outside B U b S hR hσ selected c hc
      hσ1 x law active Y N volume (fun a => (w (selected a).1).2 (selected a).2) out i hlarge)
  · exact hactive a ha

include hR hσ hc hσ1

theorem forecastOriginalSource_cutoff_eq_one
    (hexhaustive : ∀ a, (allocatedShortAxis (I := I) U b S.value) a → ∃ i, (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (r : ℝ≥0) (hr : 0 < r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (hactive : ∀ a, ¬(allocatedShortAxis (I := I) U b S.value) a → |(allocatedFullMixedSiteValue (R := R) U b w) a| ≤ r)
    (hf : (rationalInactiveForecast law active
  (forecastInactiveFixedOutput B U b S selected c x) Y N volume
  (fun a _ => Prod.snd (w (Sigma.fst (selected a))) (Sigma.snd (selected a))) out) ≠ 0) : normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr (allocatedFullMixedSiteValue (R := R) U b w) = 1 :=
  (normalizedCoordinateCutoff_spec (LayerSamplerAxis I n) r hr).2.2.2.1 (allocatedFullMixedSiteValue (R := R) U b w)
    (forecastOriginalSource_coordinates_bound B U b S hR hσ selected c hc hσ1 x law active Y N volume
      out w hexhaustive hradius hactive hf)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

variable {A : Type*}
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
variable (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
variable (hσ1 : ∀ a : A, σ (selected a).1 ≤ 1)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω)
variable (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ) (N : ℕ) [NeZero N]
variable (volume : ℝ) (out : Out → ZMod N)
variable (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
variable (y : (Σ _ : X, Unit ⊕ Empty) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)


variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)


variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))



end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawNativeRawJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

local notation "deckSource" => forecastLawDensityPhysicalDeckSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

local notation "target" => forecastLawDensityPhysicalTarget B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawDensityPhysicalDeckSource_cutoff
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (u : X → ℤ) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Eout j → ℤ)
    (hnonzero : deckSource u w deck ≠ 0) :
    normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
      (allocatedFullMixedSiteValue (R := R) U basis w) = 1 := by
  unfold forecastLawDensityPhysicalDeckSource at hnonzero
  have hparts := mul_ne_zero_iff.mp hnonzero
  have hd : density ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * physicalN a.1 / 8)),
      forecastNormalizedActiveCoordinates short (allocatedFullMixedSiteValue (R := R) U basis w)) ≠ 0 := by
    exact_mod_cast hparts.1
  apply forecastOriginalSource_cutoff_eq_one B U basis S hR hσ selected
    (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    hσ1 x law active Y N volume _ w hexhaustive r hr hradius
  · intro a ha
    exact ((hactive _ hd) ⟨⟨a, ha⟩, ()⟩).trans hr3
  · exact_mod_cast hparts.2

theorem forecastLawDensityPhysicalTarget_cutoff
    (hR : ∀ j, 0 < R j) (r : ℝ≥0) (hr : 0 < r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hsource : ∀ u w deck, deckSource u w deck ≠ 0 →
      normalizedCoordinateCutoff (LayerSamplerAxis I n) r hr
        (allocatedFullMixedSiteValue (R := R) U basis w) = 1)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  have hinj := mixedCoveredJetChart_injOn U o basis hb bW N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hmem : physicalSingleSiteValue U N poly hpoly (fun i => (u i : ℝ)) ∈ chart '' region := by
    by_contra hn
    exact hnonzero (restrictedComplexChartDensity_zero chart region 1 (chartSource u) hn)
  obtain ⟨z, hz, hvalue⟩ := hmem
  have hznonzero : chartSource u z ≠ 0 := by
    intro hzero
    apply hnonzero
    unfold forecastLawDensityPhysicalTarget
    rw [← hvalue, restrictedComplexChartDensity_apply chart region 1 (chartSource u) hinj hz,
      hzero, mul_zero]
  have hc := hsource u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ)) hznonzero
  have hcut := forecastBufferedPhysicalChartCutoff_eq_one U basis o r hr
    hR C hC hchart hbudget hb bW N z hz hc
  rw [hvalue, physicalSingleSiteValue_ambient] at hcut
  exact hcut

theorem forecastLawDensityPhysicalTarget_cutoff_of_active_support
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j v, coefficients (poly j) v ∈ U j) (u : X → ℤ)
    (hnonzero : target poly hpoly u ≠ 0) :
    allocatedBufferedTorusCutoff (R := R) U basis o r hr
      (fun a => ((eval (fun i => (u i : ℝ)) (poly a.1)) a.2.2 : UnitAddCircle)) = 1 := by
  apply forecastLawDensityPhysicalTarget_cutoff B U basis S law density selected sample x
    active Y N volume base physicalN τ o hb bW hR r hr C hC hchart hbudget
    (fun u w deck => forecastLawDensityPhysicalDeckSource_cutoff B U basis S law density selected sample x
      active Y N volume base physicalN τ hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius u w deck)
    poly hpoly u hnonzero

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (gridVolume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}


end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_cutoff_of_active_support.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.forecastLawDensityPhysicalTarget_cutoff_of_active_support.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
