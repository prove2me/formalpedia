-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:27:08.981632+00:00
-- url     : https://prove2.me/submissions/17ddea20-9a3b-4c5a-a788-a38bf8406810

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernel_residue_family_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

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

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialPivotNormalization
namespace OAI

section

namespace Erdos3

theorem normalizedPivotEquiv_inverse_eq {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap =
      (matrixSupCLM (normalizedIntegerPivot A S P)).inverse := by
  rw [← normalizedPivotEquiv_coe A hA S P hS hP, ContinuousLinearMap.inverse_equiv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J N : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]

theorem normalizedIntegerColumns_fromCols (B : Matrix I J ℤ) (C : Matrix I N ℤ)
    (T : J → ℝ) (Q : N → ℝ) (P : I → ℝ) :
    normalizedIntegerColumns (Matrix.fromCols B C) (Sum.elim T Q) P =
      Matrix.fromCols (normalizedIntegerColumns B T P) (normalizedIntegerColumns C Q P) := by
  ext i k
  cases k <;> simp [normalizedIntegerColumns_entry]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

end Erdos3


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


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetAllowances
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_pos (q h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetInterpolationAllowance q h κ := by
  unfold kernelJetInterpolationAllowance
  positivity

theorem kernelJetEntryAllowance_pos (q h : ℕ) : 0 < kernelJetEntryAllowance q h := by
  unfold kernelJetEntryAllowance
  positivity

theorem kernelJetMinorThreshold_pos (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < kernelJetMinorThreshold q n j h κ := by
  have := kernelJetInterpolationAllowance_pos q h hκ
  unfold kernelJetMinorThreshold
  positivity

theorem kernelJetInverseAllowance_nonneg (q n j h : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ kernelJetInverseAllowance q n j h κ := by
  have := kernelJetEntryAllowance_pos q h
  have := kernelJetMinorThreshold_pos q n j h hκ
  unfold kernelJetInverseAllowance
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem kernelCoefficientScale_lower {K : Type*} (T : K → ℝ)
    (hT : ∀ k, 0 < T k) {H L : ℝ} (hH : 0 ≤ H) (hL : 1 ≤ L)
    (hTL : ∀ k, T k ≤ L) (e : K →₀ ℕ) {h : ℕ}
    (he : e.sum (fun _ n => n) ≤ h) :
    H / L ^ h ≤ H / monomialScale T e :=
  div_le_div_of_nonneg_left hH (monomialScale_pos T hT e)
    (monomialScale_le_uniform_pow T (fun k => (hT k).le) hL hTL e he)

theorem boundedDegreeIntegerJetMatrix_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (difference : Matrix α K ℤ) (T : K → ℝ)
    (hT : ∀ k, 0 < T k) {L : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hentry : ∀ i k, |(difference i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : BoundedIntegerExponent K h) :
    |(boundedDegreeIntegerJetMatrix root difference h rows o e : ℝ)| ≤
      (2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h) * L ^ h := by
  have he := congrFun (congrFun
    (normalizedBoundedIntegerJetMatrix_eq root difference h rows T (H := 1) one_ne_zero) o) e
  rw [normalizedIntegerColumns_entry_div] at he
  have hbound := boundedDegreeRealJetMatrix_entry_bound _ _ hroot hentry h rows o e
  rw [← he] at hbound
  have hs := monomialScale_pos T hT e.val
  have hquot : |(boundedDegreeIntegerJetMatrix root difference h rows o e : ℝ)| /
      monomialScale T e.val ≤ 2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
    simpa only [div_one, mul_one_div, abs_div, abs_of_pos hs] using hbound
  exact ((div_le_iff₀ hs).mp hquot).trans
    (mul_le_mul_of_nonneg_left
      (monomialScale_le_uniform_pow T (fun k => (hT k).le) hL hTL e.val e.property) (by positivity))

end Erdos3


namespace Erdos3

theorem normalizedIntegerColumns_submatrix {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ) (p : I → J) :
    (normalizedIntegerColumns A S P).submatrix id p =
      normalizedIntegerPivot (A.submatrix id p) (fun i => S (p i)) P := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, normalizedIntegerColumns_entry_div,
    normalizedIntegerPivot_entry]


open scoped Matrix

end Erdos3


namespace Erdos3

theorem normalizedScalarKernelJet_eq {I J O : Type*}
    [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (h : ℕ) (rows : O → Finset I)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) =
      normalizedScalarKernelJet x h rows :=
  normalizedBoundedIntegerJetMatrix_eq _ _ _ _ _ hH

theorem kernelJetCoefficientScale_lower (J : Type*) (h : ℕ) {L H : ℝ}
    (hL : 1 ≤ L) (hH : 0 ≤ H) (e : BoundedIntegerExponent J h) :
    H / L ^ h ≤ kernelJetCoefficientScale J h L H e :=
  kernelCoefficientScale_lower _ (fun _ => zero_lt_one.trans_le hL) hH hL (fun _ => le_rfl) e.val e.property

theorem normalized_scalarKernel_pivot {I J O : Type*} [DecidableEq I] [Fintype J]
    [Fintype O] [DecidableEq O] {L : ℕ} (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (p : O → BoundedIntegerExponent J h)
    {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerPivot ((scalarKernelIntegerJet x h rows).submatrix id p)
      (fun o => kernelJetCoefficientScale J h L H (p o)) (fun _ => H) =
      (normalizedScalarKernelJet x h rows).submatrix id p := by
  have he := congrArg (fun A : Matrix O (BoundedIntegerExponent J h) ℝ => A.submatrix id p)
    (normalizedScalarKernelJet_eq x h rows hH)
  rw [normalizedIntegerColumns_submatrix] at he
  exact he

theorem fromCols_left_pivot {O J N R : Type*} (A : Matrix O J R) (C : Matrix O N R)
    (s : O ↪ J) :
    (Matrix.fromCols A C).submatrix id (s.trans Function.Embedding.inl) = A.submatrix id s := by
  ext i j
  rfl

theorem scalarKernelJet_extended_period {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    HasBoundedScalarPeriod (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range (B ^ h) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a ^ h, pow_pos ha h, Nat.pow_le_pow_left haB h, ?_⟩
  rw [integerMatrix_fromCols_range, Nat.cast_pow]
  exact (boundedDegreeIntegerJetMatrix_period _ _ (a : ℤ) hp h rows hr hrows).trans le_sup_left

theorem scalarKernelJet_extended_index {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range.toAddSubgroup.index ≤
      (B ^ h) ^ Fintype.card O :=
  hasBoundedScalarPeriod_index_le _ _ (scalarKernelJet_extended_period selection x hx h rows hr hrows C)


theorem scalarKernel_pivot_scale_independent {α J O : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] {L : ℕ}
    (hL : 0 < L) (x : J → IntegerScalarCubeBox α L) (degree : ℕ)
    (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    {H : ℝ} (hH : 0 < H) :
    normalizedPivotEquiv _ hs (fun i => kernelJetCoefficientScale J degree L H (s i))
      (fun _ => H) (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i))
      (fun _ => hH) = scalarKernelFixedPivot hL x degree rows s hs := by
  ext v i
  change ((normalizedPivotEquiv _ hs _ _ _ _).toContinuousLinearMap v) i =
    ((scalarKernelFixedPivot hL x degree rows s hs).toContinuousLinearMap v) i
  simp only [scalarKernelFixedPivot, normalizedPivotEquiv_coe,
    normalized_scalarKernel_pivot x degree rows s hH.ne',
    normalized_scalarKernel_pivot x degree rows s one_ne_zero]

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientFrontBudget
namespace OAI

section

namespace Erdos3

theorem coefficientFrontLog_nonneg (i j : ℕ) {b t e : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) : 0 ≤ coefficientFrontLog i j b t e := by
  have hB := affineCoefficientCommonBudget_nonneg j j hb ht
  unfold coefficientFrontLog coefficientLogAllowance
  positivity

theorem coefficientReplacementScale_front_bound {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (h : ℕ) {b t e ε L : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε) (hL : 0 ≤ L)
    (hεe : ε⁻¹ ≤ Real.exp e) :
    coefficientReplacementScale s b t ε L h ≤
      Real.exp (coefficientFrontLog (Fintype.card I) (Fintype.card J) b t e) *
        L^(h*(Fintype.card I+1)) := by
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ∉ Set.range s)
  have hB0 := affineCoefficientCommonBudget_nonneg
    (Fintype.card J) (Fintype.card (UnselectedColumn s)) hb ht
  have hB : affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t ≤
      affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t := by
    unfold affineCoefficientCommonBudget
    gcongr
  have hE : coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
      (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t) ≤
      coefficientLogAllowance (Fintype.card I) (Fintype.card J)
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t) := by
    unfold coefficientLogAllowance
    gcongr
  unfold coefficientReplacementScale coefficientFrontLog
  rw [Real.exp_add, Real.exp_add]
  calc
    _ ≤ Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card J)
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t)) *
          Real.exp (e+1) * L^(h*(Fintype.card I+1)) := by
      gcongr
      exact one_add_le_exp_succ he hεe
    _ = _ := by rw [Real.exp_add]; ring

theorem coefficientReplacementScale_le_power {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (h : ℕ) {b t e ε L : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε) (hL : 0 ≤ L)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hfront : Real.exp (coefficientFrontLog (Fintype.card I) (Fintype.card J) b t e) ≤ L) :
    coefficientReplacementScale s b t ε L h ≤ L^(h*(Fintype.card I+1)+1) := by
  apply (coefficientReplacementScale_front_bound s h hb ht he hε hL hεe).trans
  calc
    _ ≤ L * L^(h*(Fintype.card I+1)) := mul_le_mul_of_nonneg_right hfront (pow_nonneg hL _)
    _ = _ := by rw [pow_succ]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LayerTailDegree
namespace OAI

section

namespace Erdos3

theorem layerTailDegree_dominates {m h q r : ℕ}
    (hh : h ≤ m) (hq : q ≤ m+1) (hr : r ≤ 2^q) :
    h*(r+1) < layerTailDegree m+1 := by
  apply Nat.lt_succ_of_le
  exact Nat.mul_le_mul hh (Nat.add_le_add_right
    (hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)) 1)

theorem layerTailDegree_row_bound {m h : ℕ} {α O : Type*}
    [Fintype α] [Fintype O] (rows : O → Finset α) (hinj : Function.Injective rows)
    (hh : h ≤ m) (hq : Fintype.card α ≤ m+1) :
    h*(Fintype.card O+1) < layerTailDegree m+1 := by
  apply layerTailDegree_dominates hh hq
  simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelJetExtendedControl
namespace OAI

section

namespace Erdos3

theorem scalarKernelJet_normalized_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) {H : ℝ} (hH : H ≠ 0)
    (o : O) (e : BoundedIntegerExponent J h) :
    |normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
      (kernelJetCoefficientScale J h L H) (fun _ => H) o e| ≤
        kernelJetEntryAllowance (Fintype.card I) h := by
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  have he := congrFun (congrFun (normalizedScalarKernelJet_eq x h rows hH) o) e
  change |normalizedIntegerColumns (scalarKernelIntegerJet x h rows)
    (fun e => H / monomialScale (fun _ => (L : ℝ)) e.val) (fun _ => H) o e| ≤ _
  rw [he]
  exact boundedDegreeRealJetMatrix_entry_bound _ _ (fun j => hc j none)
    (fun i j => hc j (some i)) h rows o e

theorem scalarKernelJet_integer_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [DecidableEq O]
    {L : ℕ} (hL : 0 < L) (x : J → IntegerScalarCubeBox I L)
    (h : ℕ) (rows : O → Finset I) (o : O) (e : BoundedIntegerExponent J h) :
    |(scalarKernelIntegerJet x h rows o e : ℝ)| ≤
      kernelJetEntryAllowance (Fintype.card I) h * (L : ℝ) ^ h := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hc (j : J) (i : Option I) : |(x j i : ℝ) / L| ≤ 1 :=
    (norm_le_pi_norm (fun i => (x j i : ℝ) / L) i).trans
      (integerScalarCubeBox_normalized_norm_le hL (x j))
  exact boundedDegreeIntegerJetMatrix_entry_bound _ _ (fun _ => (L : ℝ))
    (fun _ => hLr) (by exact_mod_cast hL) (fun _ => le_rfl)
    (fun j => hc j none) (fun i j => hc j (some i)) h rows o e

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MonomialCoefficientControl
namespace OAI

section

namespace Erdos3

theorem normalizedAffineMonomialJetMatrix_eq {α V O N : Type*} [DecidableEq α]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {H : ℝ} (hH : H ≠ 0) :
    normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) =
    realJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
      (realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v)) rows := by
  have hv : (fun t v => (integerAffineCube root difference t v : ℝ) / T v) =
      realAffineCube (fun v => (root v : ℝ) / T v) (fun i v => (difference i v : ℝ) / T v) := by
    funext t v
    exact (realAffineCube_normalized_integer root difference T t v).symm
  have he := normalizedIntegerMonomialJetMatrix_eq e (integerAffineCube root difference) rows T hH
  rwa [hv] at he

theorem normalizedAffineMonomialJetMatrix_bound {α V O N : Type*}
    [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (root : V → ℤ) (difference : α → V → ℤ) (e : N → V →₀ ℕ) (rows : O → Finset α)
    (T : V → ℝ) {h : ℕ} (he : ∀ n, (e n).sum (fun _ d => d) ≤ h)
    (hroot : ∀ v, |(root v : ℝ) / T v| ≤ 1)
    (hdiff : ∀ i v, |(difference i v : ℝ) / T v| ≤ 1) {H : ℝ} (hH : H ≠ 0) :
    ∀ o n, |normalizedIntegerColumns
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerAffineCube root difference) rows)
      (fun n => H / monomialScale T (e n)) (fun _ => H) o n| ≤
        kernelJetEntryAllowance (Fintype.card α) h := by
  intro o n
  rw [normalizedAffineMonomialJetMatrix_eq root difference e rows T hH]
  exact boundedDegreeRealJetMatrix_entry_bound _ _ hroot hdiff h rows o ⟨e n, he n⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

theorem mappedPrincipal_normalized_bound {Z K D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (zi : Z → ℤ) (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1) (T : K → ℝ)
    (y : PrincipalIntegerTuples B h α L)
    (hn : ∀ k a, ((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k =
      Sum.elim zr (principalTupleNormalized L y) (input k a)) :
    ∀ k a, |((Sum.elim zi (principalTupleIntegers y) (input k a) : ℤ) : ℝ)/T k| ≤ 1 := by
  intro k a
  rw [hn]
  cases input k a with
  | inl j => exact hz j
  | inr j =>
    exact (norm_le_pi_norm (principalTupleNormalized L y) j).trans
      (principalTupleNormalized_norm_le B h L hL y)

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_normalized (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (zi : Z → ℤ) (zr : Z → ℝ) (T : G → ℝ)
    (hfixed : ∀ g a, (zi (extra g a) : ℝ)/T g = zr (extra g a))
    (L : PrincipalTupleIndex B h → ℕ)
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    ((Sum.elim (Sum.elim zi (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) : ℤ) : ℝ) /
        Sum.elim T (fun j => (L j : ℝ)) k =
      Sum.elim (Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u))
        (principalTupleNormalized (principalAxisLength (fun d => ¬P d) L) v)
        (partitionedPrincipalInput P extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · exact hfixed g a
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, principalTupleNormalized, principalAxisLength, hp]

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] in
theorem allocatedNonkernelExponent_degree (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    (allocatedNonkernelExponent B j d).sum (fun _ r => r) ≤ j.val+1 := d.val.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : I j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

omit [Fintype α] [DecidableEq α] in
theorem allocatedPartitionedInput_normalized
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (k : LayerSamplerVariables G I n B) (a : Option α) :
    ((Sum.elim fixedInteger (principalTupleIntegers v) (input k a) : ℤ) : ℝ) /
      layerSamplerBox B U basis S k =
      Sum.elim fixedReal (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
        (input k a) := by
  have hbox : layerSamplerBox B U basis S =
      Sum.elim (fun _ : G => (S.value : ℝ)) (fun d => (sides d : ℝ)) := by
    funext k
    cases k <;> rfl
  rw [hbox]
  exact partitionedPrincipalInput_normalized grid (fun g a => (g, a))
    (fun ga : G × Option α => (x ga.1 ga.2 : ℤ))
    (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ) / (S.value : ℝ))
    (fun _ => (S.value : ℝ)) (fun _ _ => rfl) sides u v k a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedInteger_replacementScale_le {α O : Type*} [Fintype α] [Fintype O]
    (j : Fin m) (i : Fin (n j)) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hq : Fintype.card α ≤ m+1) (s : O ↪ BoundedIntegerExponent G (j.val+1))
    {b t e ε : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hfront : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) b t e) ≤ S.value)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) :
    coefficientReplacementScale
      (J := BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j)
      (s.trans Function.Embedding.inl) b t ε S.value (j.val+1) ≤ (basisAxisScale (basis j) i : ℝ) := by
  have hcard := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  have hf : Real.exp (coefficientFrontLog (Fintype.card O)
      (Fintype.card (BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j))
      b t e) ≤ S.value := by simpa only [hcard] using hfront
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hd := layerTailDegree_row_bound rows hinj (Nat.succ_le_of_lt j.isLt) hq
  apply (coefficientReplacementScale_le_power (s.trans Function.Embedding.inl) (j.val+1)
    hb ht he hε (zero_le_one.trans hL) hεe hf).trans
  calc
    _ ≤ (S.value : ℝ)^(layerTailDegree m+1) :=
      pow_le_pow_right₀ hL (Nat.succ_le_of_lt hd)
    _ ≤ (basisAxisScale (basis j) i : ℝ) := by exact_mod_cast henormous.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

theorem allocatedUnitProfileWidth_inverse_exp (a : ℕ) {R σ P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R) (hσ : 0 < σ)
    (hRP : R⁻¹ ≤ Real.exp P) (hσP : σ⁻¹ ≤ Real.exp P) (haP : (a : ℝ)+1 ≤ Real.exp P) :
    (allocatedUnitProfileWidth R σ a)⁻¹ ≤ Real.exp (4*(P+8)) := by
  let X := Real.exp (P+8)
  have hPX : Real.exp P ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hX : 8 ≤ X := by dsimp [X]; linarith [Real.add_one_le_exp (P+8)]
  have hLX : ((1 : ℕ) : ℝ) ≤ X := by norm_num; linarith
  have h := allocatedWidthFloor_inverse_power_bound 1 0 0 a le_rfl hR hσ hX
    (hRP.trans hPX) (hσP.trans hPX) (haP.trans hPX) hLX
  simpa only [allocatedUnitProfileWidth, X, ← Real.exp_nat_mul, Nat.zero_add, Nat.cast_ofNat] using h

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

theorem kernelJetInterpolationAllowance_le_exp (q h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInterpolationAllowance q h κ ≤
      Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2)) := by
  have hq : (q : ℝ) ≤ Real.exp q := by linarith [Real.add_one_le_exp (q : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hterm : (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp q * (Real.exp 1 * (Real.exp ((q : ℝ)^2) * Real.exp b)) := by
        gcongr
        exact factorial_le_exp_sq q
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have he : 1 ≤ Real.exp ((q : ℝ)^2 + q + b + 1) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hbase : 1 + (q : ℝ) * (2 * (q.factorial / κ)) ≤
      Real.exp ((q : ℝ)^2 + q + b + 2) := by
    calc
      _ ≤ 2 * Real.exp ((q : ℝ)^2 + q + b + 1) := by linarith
      _ ≤ Real.exp 1 * Real.exp ((q : ℝ)^2 + q + b + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  unfold kernelJetInterpolationAllowance
  calc
    _ ≤ (Real.exp ((q : ℝ)^2 + q + b + 2)) ^ h := by gcongr
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem kernelJetEntryAllowance_le_exp (q h : ℕ) :
    kernelJetEntryAllowance q h ≤ Real.exp ((q : ℝ) * (h + 1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq := Real.add_one_le_exp (q : ℝ)
  unfold kernelJetEntryAllowance
  calc
    _ ≤ (Real.exp 1) ^ q * (Real.exp q) ^ h := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem kernelJetMinorThreshold_inv_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    (kernelJetMinorThreshold q n j h κ)⁻¹ ≤
      Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hn := Real.add_one_le_exp (n : ℝ)
  have hQ := kernelJetInterpolationAllowance_le_exp q h hκ hb hi
  have hQpos := (kernelJetInterpolationAllowance_pos q h hκ).le
  simp only [kernelJetMinorThreshold, one_div, inv_inv]
  calc
    _ ≤ ((Real.exp n) ^ h *
        Real.exp ((h : ℝ) * ((q : ℝ)^2 + q + b + 2))) ^ j := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]

theorem kernelJetInverseAllowance_le_exp (q n j h : ℕ) {κ b : ℝ}
    (hκ : 0 < κ) (hb : 0 ≤ b) (hi : κ⁻¹ ≤ Real.exp b) :
    kernelJetInverseAllowance q n j h κ ≤
      Real.exp ((j : ℝ) + (j : ℝ)^2 +
        (j - 1 : ℕ) * ((q : ℝ) * (h + 1)) +
        j * (h * n + h * ((q : ℝ)^2 + q + b + 2))) := by
  have hj : (j : ℝ) ≤ Real.exp j := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hE := kernelJetEntryAllowance_le_exp q h
  have hEin := (kernelJetEntryAllowance_pos q h).le
  have hminor := kernelJetMinorThreshold_inv_le_exp q n j h hκ hb hi
  have hminorpos := (kernelJetMinorThreshold_pos q n j h hκ).le
  unfold kernelJetInverseAllowance
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp j * ((Real.exp ((j : ℝ)^2) *
        (Real.exp ((q : ℝ) * (h + 1))) ^ (j - 1)) *
        Real.exp ((j : ℝ) * (h * n + h * ((q : ℝ)^2 + q + b + 2)))) := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem fixedKernel_mapped_control {α J O N K Z X : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    {L B : ℕ} {κ H U G : ℝ} (hL : 0 < L) (selection : α ↪ J)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hrows : ∀ i, (rows i).card ≤ degree) (s : O ↪ BoundedIntegerExponent J degree)
    (hs : ((scalarKernelIntegerJet x degree rows).submatrix id s).det ≠ 0)
    (hi : ‖(scalarKernelFixedPivot hL x degree rows s hs).symm.toContinuousLinearMap‖ ≤ U)
    (hH : 0 < H) (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (y : X → ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (hTL : ∀ k, T k ≤ (L : ℝ)) (he : ∀ n, (e n).sum (fun _ d => d) ≤ degree)
    (hn : ∀ k a, |((Sum.elim z y (input k a) : ℤ) : ℝ)/T k| ≤ 1)
    (hG : (((B^degree)^Fintype.card O : ℕ) : ℝ) ≤ G) :
    CoefficientFiberControl
      (Matrix.fromCols (scalarKernelIntegerJet x degree rows) (integerMappedJetMatrix e input z rows y))
      (s.trans Function.Embedding.inl)
      (Sum.elim (kernelJetCoefficientScale J degree L H) (fun n => H / monomialScale T (e n)))
      H L degree (kernelJetEntryAllowance (Fintype.card α) degree) U G := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fromCols_left_pivot] using hs
  · intro j
    cases j with
    | inl a => exact kernelJetCoefficientScale_lower J degree (by exact_mod_cast hL) hH.le a
    | inr n => exact kernelCoefficientScale_lower T hT hH.le (by exact_mod_cast hL) hTL (e n) (he n)
  · intro i j
    exact scalarKernelJet_integer_entry hL x degree rows i (s j)
  · intro i j
    rw [normalizedIntegerColumns_fromCols]
    cases j with
    | inl a =>
      simpa only [Matrix.fromCols_apply_inl, normalizedIntegerColumns_entry_div] using
        scalarKernelJet_normalized_entry hL x degree rows hH.ne' i a
    | inr n =>
      simpa only [Matrix.fromCols_apply_inr, normalizedIntegerColumns_entry_div,
        integerMappedJetMatrix, integerMappedCubeTuple] using
        normalizedAffineMonomialJetMatrix_bound
          (fun k => Sum.elim z y (input k none)) (fun a k => Sum.elim z y (input k (some a)))
          e rows T he (fun k => hn k none) (fun a k => hn k (some a)) hH.ne' i n
  · rw [fromCols_left_pivot]
    change ‖(matrixSupCLM (normalizedIntegerPivot ((scalarKernelIntegerJet x degree rows).submatrix id s)
      (fun i => kernelJetCoefficientScale J degree L H (s i)) (fun _ => H))).inverse‖ ≤ U
    rw [← normalizedPivotEquiv_inverse_eq _ hs
      (fun i => kernelJetCoefficientScale J degree L H (s i)) (fun _ => H)
      (fun i => kernelJetCoefficientScale_pos J degree (by exact_mod_cast hL) hH (s i)) (fun _ => hH),
      scalarKernel_pivot_scale_independent hL x degree rows s hs hH]
    exact hi
  · have hb := scalarKernelJet_extended_index selection x hx degree rows hinj hrows
      (integerMappedJetMatrix e input z rows y)
    have hb' : ((Matrix.fromCols (scalarKernelIntegerJet x degree rows)
        (integerMappedJetMatrix e input z rows y)).mulVecLin.range.toAddSubgroup.index : ℝ) ≤
        (((B^degree)^Fintype.card O : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans hG

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

theorem coefficientFiberControl_change_decidableEq {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] {d₁ d₂ : DecidableEq J}
    {A : Matrix I J ℤ} {s : I ↪ J} {S : J → ℝ} {H L C U M : ℝ} {h : ℕ}
    (hc : @CoefficientFiberControl I J _ _ _ d₁ A s S H L h C U M) :
    @CoefficientFiberControl I J _ _ _ d₂ A s S H L h C U M := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact hc

theorem layerKernelIndexBound_row {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ m+1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B^(j.val+1))^Fintype.card O ≤ layerKernelIndexBound m B := by
  have hc : Fintype.card O ≤ 2^(m+1) := by
    have hr : Fintype.card O ≤ 2^Fintype.card α := by
      simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj
    exact hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hB (Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) hc)

namespace VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

theorem allocatedPartitionedInput_bound
    (u : PrincipalAxisTuples (α := α) grid sides)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    ∀ k a, |((Sum.elim
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (principalTupleIntegers v) (input k a) : ℤ) : ℝ) / layerSamplerBox B U basis S k| ≤ 1 := by
  exact mappedPrincipal_normalized_bound
    (fun a : {a // ¬grid a} => B a.val) (fun a => layerSamplerDegree I n a.val)
    (principalAxisLength (fun a => ¬grid a) sides)
    (fun d => allocatedPrincipalSides_pos B U basis S ⟨d.1.val, d.2⟩) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (Sum.elim (fun ga : G × Option α => ((x ga.1 ga.2 : ℤ) : ℝ)/S.value)
      (principalTupleNormalized (principalAxisLength grid sides) u))
    (allocatedPartitionedInput_frozen_bound B U basis S x u) (layerSamplerBox B U basis S) v
    (allocatedPartitionedInput_normalized B U basis S x u v)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))

variable [DecidableEq G]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedFixedKernel_controls {κ : ℝ} {M : ℕ}
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) κ) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) j (i : Fin (n j)),
      CoefficientFiberControl
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        ((s j).trans Function.Embedding.inl)
        (Sum.elim (kernelJetCoefficientScale G (j.val+1) S.value (basisAxisScale (basis j) i))
          (fun d => (basisAxisScale (basis j) i : ℝ) /
            monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)))
        (basisAxisScale (basis j) i) S.value (j.val+1)
        (kernelJetEntryAllowance (Fintype.card α) (j.val+1))
        (kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1) κ)
        (layerKernelIndexBound m M) := by
  have hM : 0 < M := by
    obtain ⟨a, ha, haM, _⟩ := hx.2
    exact ha.trans_le haM
  intro u v j i
  have hH : (0 : ℝ) < basisAxisScale (basis j) i := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hcontrol := fixedKernel_mapped_control S.positive selection x hx (j.val+1) (rows j)
    (hinj j) (hrows j) (s j) (hA j) (hi j) hH (allocatedNonkernelExponent B j) input
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (layerSamplerBox B U basis S)
    (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k))
    (layerSamplerBox_le B U basis S) (allocatedNonkernelExponent_degree B j)
    (allocatedPartitionedInput_bound B U basis S x u v)
    (show (((M^(j.val+1))^Fintype.card (O j) : ℕ) : ℝ) ≤ layerKernelIndexBound m M by
      exact_mod_cast layerKernelIndexBound_row hM hq (rows j) (hinj j) j)
  exact coefficientFiberControl_change_decidableEq hcontrol

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem allocatedKernelLog_allowances (G α : Type*) [Fintype G] [Fintype α]
    {m : ℕ} (O : Fin m → Type*) [∀ j, Fintype (O j)] {P : ℝ} {M : ℕ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P) :
    (layerKernelIndexBound m M : ℝ) ≤ Real.exp (allocatedKernelLog G α O P) ∧
    ∀ j, kernelJetEntryAllowance (Fintype.card α) (j.val+1) ≤ Real.exp (allocatedKernelLog G α O P) ∧
      kernelJetInverseAllowance (Fintype.card α) (Fintype.card G) (Fintype.card (O j)) (j.val+1)
        (1/(M : ℝ)) ≤ Real.exp (allocatedKernelLog G α O P) := by
  have hb := allocatedKernelLog_bounds G α O hP
  refine ⟨(layerKernelIndexBound_le_exp m hMP).trans (Real.exp_le_exp.mpr hb.2.2.1), ?_⟩
  intro j
  constructor
  · apply (kernelJetEntryAllowance_le_exp (Fintype.card α) (j.val+1)).trans
    apply Real.exp_le_exp.mpr
    apply le_trans _ hb.2.2.2.1
    gcongr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  · have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    have hv := kernelJetInverseAllowance_le_exp (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (j.val+1) hκ hP (by simpa only [one_div, inv_inv] using hMP)
    exact hv.trans (Real.exp_le_exp.mpr (hb.2.2.2.2 j))

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedKernelReplacementLog_front_le (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P e : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (j : Fin m) :
    coefficientFrontLog (Fintype.card (O j))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O P) (4*(P+8)) e ≤ allocatedKernelReplacementLog (G := G) B α O P e := by
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro k _
  exact coefficientFrontLog_nonneg _ _ (allocatedKernelLog_bounds G α O hP).1 (by positivity) he

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedFixedKernel_replacement_s2_oai {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P e ε : ℝ} (hP : 0 ≤ P) (he : 0 ≤ e) (hε : 0 < ε)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hlarge : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
    (modulus : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) :
    ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ v, p.weight v ≠ 0 → ∀ j,
        integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) →
      ∀ j i (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i),
      (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
        allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ layerKernelIndexBound m M) ∧
      ∀ v, p.weight v ≠ 0 → ∀ z,
        |(basisAxisScale (basis j) i : ℝ)^Fintype.card (O j) *
            (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i (hσ1 j) henormous z).toReal -
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z *
            allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j)
              (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
              (fun o => (z o : ℝ)/(basisAxisScale (basis j) i : ℝ))| ≤ ε := by
  have hκ : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hcontrol := allocatedFixedKernel_controls B U basis S x rows selection hx hq hinj hrows s hA hi
  intro u p residue hr j i henormous
  have hb := allocatedKernelLog_bounds G α O hP
  have ha := allocatedKernelLog_allowances G α O hP hM hMP
  have ht : 0 ≤ 4*(P+8) := by positivity
  have hf := (Real.exp_le_exp.mpr (allocatedKernelReplacementLog_front_le (G := G) B α O hP he j)).trans hlarge
  exact allocatedIntegerKernel_residue_family_s2 B U basis hR hσ S x u rows j i (s j) (hA j) (hσ1 j)
    henormous p modulus (residue j) (hperiod j) (fun v hv => hr v hv j)
    (kernelJetEntryAllowance_pos _ _).le (kernelJetInverseAllowance_nonneg _ _ _ _ hκ)
    (Nat.cast_nonneg _) (fun v _ => hcontrol u v j i)
    hb.1 ht hε ha.1 (ha.2 j).2 (ha.2 j).1 ((hRP j).trans (Real.exp_le_exp.mpr hb.2.1))
    (allocatedUnitProfileWidth_inverse_exp _ hP (hR j) (hσ j) (hRi j) (hσi j) (hcount j))
    (allocatedInteger_replacementScale_le B U basis S j i (rows j) (hinj j) hq (s j)
      hb.1 ht he hε hεe hf henormous)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedFixedKernel_replacement_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
