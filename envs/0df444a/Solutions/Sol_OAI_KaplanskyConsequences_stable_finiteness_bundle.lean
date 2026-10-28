-- Prove2me | solution 1 for OAI.KaplanskyConsequences.stable_finiteness_bundle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:59:11.586265+00:00
-- url     : https://prove2.me/submissions/b487a850-0b2f-485b-bb36-45765008b57a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf012
import Theorems.Thm_OAI_Kaplansky_actualAlgebra_matrix_not_properlyInfinite
import Theorems.Thm_OAI_KaplanskyConsequences_actualAlgebra_tensor_properlyInfinite
import Theorems.Thm_OAI_KaplanskyConsequences_simple_stable_tensor_counterexample_exists
import Theorems.Thm_OAI_KaplanskyConsequences_trace_free_stably_finite_exists

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Basic
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive square-symmetric quasitraces with complex linearity on closed nonunital abelian subalgebras. -/

section

noncomputable section
open scoped ComplexOrder IsMulCommutative

namespace Kaplansky

variable {A : Type*} [CStarAlgebra A]

namespace OneQuasitrace

variable (τ : OneQuasitrace A)

theorem map_sub_of_mem (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (hcomm : ∀ x y : S, x * y = y * x)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) : τ (a - b) = τ a - τ b := by
  obtain ⟨f, hf⟩ := τ.linearOn S hS hcomm
  exact (hf (⟨a, ha⟩ - ⟨b, hb⟩)).symm.trans
    ((f.map_sub ⟨a, ha⟩ ⟨b, hb⟩).trans (congrArg₂ (· - ·) (hf _) (hf _)))

theorem map_smul_of_mem (S : StarSubalgebra ℂ A)
    (hS : IsClosed (S : Set A)) (hcomm : ∀ x y : S, x * y = y * x)
    (c : ℂ) {a : A} (ha : a ∈ S) : τ (c • a) = c * τ a := by
  obtain ⟨f, hf⟩ := τ.linearOn S hS hcomm
  exact (hf (c • (⟨a, ha⟩ : S))).symm.trans
    ((f.map_smul c ⟨a, ha⟩).trans (congrArg (c * ·) (hf _)))

theorem map_smul_selfAdjoint (c : ℂ) {a : A} (ha : IsSelfAdjoint a) :
    τ (c • a) = c * τ a := by
  let := ha.isStarNormal
  exact τ.map_smul_of_mem (StarAlgebra.elemental ℂ a)
    (StarAlgebra.elemental.isClosed ℂ a) (fun x y => mul_comm x y) c
    (StarAlgebra.elemental.self_mem ℂ a)

theorem map_scalar_sub (c : ℂ) {a : A} (ha : IsSelfAdjoint a) :
    τ (c • (1 : A) - a) = c * τ 1 - τ a := by
  let := ha.isStarNormal
  rw [τ.map_sub_of_mem (StarAlgebra.elemental ℂ a)
    (StarAlgebra.elemental.isClosed ℂ a) (fun x y => mul_comm x y)
    ((StarAlgebra.elemental ℂ a).smul_mem (one_mem _) c)
    (StarAlgebra.elemental.self_mem ℂ a)]
  rw [τ.map_smul_selfAdjoint c (IsSelfAdjoint.one A)]

end OneQuasitrace
end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Order
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Order preservation and pointwise bounds for normalized quasitraces. -/

section

noncomputable section
open scoped ComplexOrder
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Positivity on all positive elements follows from the square axiom. -/
theorem OneQuasitrace.map_nonneg (τ : OneQuasitrace A) {a : A} (ha : 0 ≤ a) :
    0 ≤ τ a := by
  obtain ⟨x, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  exact τ.square_nonneg x

theorem OneQuasitrace.scalar_upper_bound (τ : OneQuasitrace A) (c : ℝ)
    {a : A} (ha : 0 ≤ a) (hca : a ≤ (c : ℂ) • (1 : A)) :
    (τ a).re ≤ c * (τ 1).re := by
  have h := τ.map_nonneg (sub_nonneg.mpr hca)
  rw [τ.map_scalar_sub (c : ℂ) ha.isSelfAdjoint] at h
  have hr : 0 ≤ ((c : ℂ) * τ 1 - τ a).re := h.1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hr
  linarith

end Kaplansky

end
end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Infiniteness
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Proper infiniteness, isometry columns, and C-star matrix amplification. -/

open scoped ComplexOrder CStarAlgebra BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem not_properlyInfinite (τ : OneQuasitrace A) (hτ : τ.Normalized) :
    ¬ ProperlyInfinite A := by
  rintro ⟨s,t,hs,ht,hst⟩
  change τ 1 = 1 at hτ
  let p := s * star s
  let q := t * star t
  have hp : IsSelfAdjoint p := IsSelfAdjoint.mul_star_self s
  have hq : IsSelfAdjoint q := IsSelfAdjoint.mul_star_self t
  have hpp : p*p = p := by
    dsimp [p]
    calc
      (s*star s)*(s*star s) = s*(star s*s)*star s := by simp only [mul_assoc]
      _ = s*star s := by rw [hs]; simp
  have hqq : q*q = q := by
    dsimp [q]
    calc
      (t*star t)*(t*star t) = t*(star t*t)*star t := by simp only [mul_assoc]
      _ = t*star t := by rw [ht]; simp
  have hpq : p*q = 0 := by
    dsimp [p,q]
    calc
      (s*star s)*(t*star t) = s*(star s*t)*star t := by simp only [mul_assoc]
      _ = 0 := by rw [hst]; simp
  have hqp : q*p = 0 := by
    have h := congrArg star hpq
    simpa only [star_mul, hp.star_eq, hq.star_eq, star_zero] using h
  have hcomm : Commute p q := hpq.trans hqp.symm
  have hpqSq : (p+q)*(p+q) = p+q := by
    simp only [add_mul, mul_add, hpp, hqq, hpq, hqp, add_zero, zero_add]
  have he : star (1-(p+q))*(1-(p+q)) = 1-(p+q) := by
    rw [(IsSelfAdjoint.one A |>.sub (hp.add hq)).star_eq]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpqSq, sub_self, sub_zero]
  have hle : p+q ≤ 1 := by
    apply sub_nonneg.mp
    rw [← he]
    exact star_mul_self_nonneg _
  have hvp : τ p = 1 := by
    have h := τ.square_swap s
    simpa only [hs, hτ] using h.symm
  have hvq : τ q = 1 := by
    have h := τ.square_swap t
    simpa only [ht, hτ] using h.symm
  have hv : τ (p+q) = 2 := by rw [τ.map_add hp hq hcomm, hvp, hvq]; norm_num
  have h := τ.scalar_upper_bound 1
    (add_nonneg (mul_star_self_nonneg s) (mul_star_self_nonneg t))
    (by simpa only [Complex.ofReal_one, one_smul] using hle)
  rw [hv, hτ] at h
  norm_num at h

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Monoid
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Every class is bounded by a natural multiple of [1_A]. -/
theorem cuntzMonoid_orderUnit (x : CuntzMonoid A) : ∃ n : ℕ, x ≤ n • cuntzUnit A 1 := by
  induction x using Quotient.inductionOn with | h x =>
  refine ⟨x.size, ?_⟩
  rw [cuntzUnit_nsmul]
  exact (cuntzClass_le _ _).mpr x.le_unit

end Kaplansky

end

noncomputable section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coisometry supported on the first half of the columns gives two
orthogonal isometries in the undoubled algebra. -/
theorem properlyInfinite_of_coisometry_half
    (Y : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) (hY : Y * star Y = 1)
    (hzero : ∀ i j, Y i (Sum.inr j) = 0) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let s : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inl j) (Sum.inl i))
  let t : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inr j) (Sum.inl i))
  have hs (i j : ι) : s i j = star (Y (Sum.inl j) (Sum.inl i)) := rfl
  have ht (i j : ι) : t i j = star (Y (Sum.inr j) (Sum.inl i)) := rfl
  have he (i j : ι ⊕ ι) : (∑ k : ι, Y i (Sum.inl k) * star (Y j (Sum.inl k))) =
      if i = j then 1 else 0 := by
    have h := congrArg (fun M : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A => M i j) hY
    simpa [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Fintype.sum_sum_type, hzero, Matrix.one_apply, CStarMatrix.one_apply] using h
  refine ⟨s, t, ?_, ?_, ?_⟩
  · ext i j
    simpa [hs, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inl i) (Sum.inl j)
  · ext i j
    simpa [ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inr i) (Sum.inr j)
  · ext i j
    simpa [hs, ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply] using he (Sum.inl i) (Sum.inr j)

/-- Invertible rectangular row Gram gives a genuine coisometry by inverse
square-root normalization. The zero column block is retained. -/
theorem properlyInfinite_of_invertible_rectangular_gram
    (v : Matrix (ι ⊕ ι) ι A)
    (hv : IsUnit (CStarMatrix.ofMatrix (v * v.conjTranspose))) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  let X : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := CStarMatrix.ofMatrix (Matrix.fromCols v 0)
  let Q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := X * star X
  have hQ : Q = CStarMatrix.ofMatrix (v * v.conjTranspose) := by
    apply CStarMatrix.ext
    intro i j
    change (∑ k : ι ⊕ ι,
      (Sum.elim (v i) (fun _ => 0) k) * star (Sum.elim (v j) (fun _ => 0) k)) =
      ∑ k : ι, v i k * star (v j k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hpos : IsStrictlyPositive Q := (hQ.symm ▸ hv).isStrictlyPositive (mul_star_self_nonneg X)
  let L := Q ^ (-(1 / 2) : ℝ)
  have hL : star L = L := (CFC.rpow_nonneg (a := Q) (y := (-(1 / 2) : ℝ))).isSelfAdjoint.star_eq
  apply properlyInfinite_of_coisometry_half (L * X)
  · calc
      L * X * star (L * X) = L * Q * L := by simp only [star_mul, hL, Q, mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half Q hpos
  · intro i j
    have hX (k : ι ⊕ ι) : X k (Sum.inr j) = 0 := rfl
    simp only [CStarMatrix.mul_apply, hX, mul_zero, Finset.sum_const_zero]

/-- Approximate compression of a doubled identity already forces proper
infiniteness, using the radius-one invertibility criterion. -/
theorem properlyInfinite_of_cuntzLE_double_unit
    (h : CuntzLE (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) A) (1 : Matrix ι ι A)) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp h 1 zero_lt_one
  simp only [Matrix.mul_one] at hv
  apply properlyInfinite_of_invertible_rectangular_gram v
  let Q := CStarMatrix.ofMatrix (v * v.conjTranspose)
  have hnorm : ‖1 - Q‖ < 1 := hv
  have hu := (Units.oneSub (1 - Q) hnorm).isUnit
  simpa only [Units.val_oneSub, sub_sub_cancel] using hu

theorem properlyInfinite_of_cuntzUnit_compression (k : ℕ)
    (h : (2*k) • cuntzUnit A 1 ≤ k • cuntzUnit A 1) :
    ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A) := by
  rw [cuntzUnit_nsmul, cuntzUnit_nsmul] at h
  have hc : CuntzLE (1 : Matrix (Fin (2*k)) (Fin (2*k)) A) (1 : Matrix (Fin k) (Fin k) A) :=
    (cuntzClass_le _ _).mp h
  have hsum : CuntzLE (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) A)
      (1 : Matrix (Fin k) (Fin k) A) := by
    rw [two_mul] at hc
    have he := (cuntzEquivalent_submatrix_equiv
      (1 : Matrix (Fin (k+k)) (Fin (k+k)) A) finSumFinEquiv).1.trans hc
    simpa using he
  exact properlyInfinite_of_cuntzLE_double_unit hsum

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.OrderedStates_RationalCone
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Rational cones and extension of positive states on ordered groups. -/

namespace Kaplansky

section
variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

theorem orderedGroupRationalCone_coe {g : G} (hg : 0 ≤ g) :
    (g : DivisibleHull G) ∈ orderedGroupRationalCone := ⟨g,1,hg,rfl⟩

/-- A unit with no nonpositive positive multiple stays outside the
negative of the rational cone, even if the group has torsion elsewhere. -/
theorem orderedGroupRationalCone_neg_unit (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) :
    -(u : DivisibleHull G) ∉ orderedGroupRationalCone := by
  rintro ⟨g,d,hg,he⟩
  change DivisibleHull.mk g d = -DivisibleHull.mk u 1 at he
  rw [DivisibleHull.neg_mk] at he
  obtain ⟨k,hk⟩ := DivisibleHull.mk_eq_mk.mp he
  simp only [PNat.val_ofNat, one_nsmul, smul_neg, smul_smul] at hk
  have hp : 0 ≤ -((k.val*d.val) • u) := by
    rw [← hk]
    exact nsmul_nonneg hg _
  exact hu (k.val*d.val) (Nat.mul_pos k.pos d.pos) (neg_nonneg.mp hp)

theorem orderedGroupRationalCone_unit_ne_zero (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) : (u : DivisibleHull G) ≠ 0 := by
  intro h
  apply orderedGroupRationalCone_neg_unit u hu
  rw [h, neg_zero]
  exact (orderedGroupRationalCone (G := G)).zero_mem

/-- Nonnegativity along the rational unit ray is reflected in its scalar. -/
theorem orderedGroupRationalCone_unit_scalar (u : G)
    (hu : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0) {q : ℚ}
    (hq : q • (u : DivisibleHull G) ∈ orderedGroupRationalCone) : 0 ≤ q := by
  by_contra h
  have hn : q < 0 := lt_of_not_ge h
  have hp : 0 < -q⁻¹ := neg_pos.mpr (inv_neg''.mpr hn)
  have hc := (orderedGroupRationalCone (G := G)).smul_mem hp.le hq
  rw [smul_smul, neg_mul, inv_mul_cancel₀ hn.ne, neg_one_smul] at hc
  exact orderedGroupRationalCone_neg_unit u hu hc

/-- An order unit in G dominates every rational fraction after passage
to the cone. The dominating vector is an integer multiple of the unit. -/
theorem orderedGroupRationalCone_cofinal (u : G) (hu : 0 ≤ u)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) (x : DivisibleHull G) :
    ∃ N : ℕ, (N : ℚ) • (u : DivisibleHull G) + x ∈ orderedGroupRationalCone := by
  induction x using DivisibleHull.ind with | mk g d =>
  obtain ⟨N,hN⟩ := hb g
  refine ⟨N, ?_⟩
  have hunit : N • u ≤ d.val • (N • u) := by
    simpa only [one_nsmul] using
      nsmul_le_nsmul_left (nsmul_nonneg hu N) (Nat.one_le_iff_ne_zero.mpr d.ne_zero)
  have hnon : 0 ≤ d.val • (N • u)+g := by
    have h := (neg_le_neg hunit).trans hN
    simpa only [add_comm] using neg_le_iff_add_nonneg.mp h
  refine ⟨d.val • (N • u)+g,d,hnon,?_⟩
  rw [Nat.cast_smul_eq_nsmul ℚ N, DivisibleHull.coe, DivisibleHull.nsmul_mk,
    DivisibleHull.mk_add_mk]
  simp

end

section
open Set LinearMap
variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis

The Riesz extension declarations below are adapted from Mathlib.Analysis.Convex.Cone.Extension.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Convex/Cone/Extension.lean

This code has been modified.
-/

namespace RationalRieszExtension

open Submodule

variable (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
theorem step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x := by
  obtain ⟨y, -, hy⟩ : ∃ y ∈ ⊤, y ∉ f.domain := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hdom)
  obtain ⟨c, le_c, c_le⟩ :
      ∃ c, (∀ x : f.domain, -(x : E) - y ∈ s → f x ≤ c) ∧
        ∀ x : f.domain, (x : E) + y ∈ s → c ≤ f x := by
    set Sp := f '' { x : f.domain | (x : E) + y ∈ s }
    set Sn := f '' { x : f.domain | -(x : E) - y ∈ s }
    suffices (upperBounds Sn ∩ lowerBounds Sp).Nonempty by
      simpa only [Sp, Sn, Set.Nonempty, upperBounds, lowerBounds, forall_mem_image] using! this
    refine exists_between_of_forall_le (Nonempty.image f ?_) (Nonempty.image f (dense y)) ?_
    · rcases dense (-y) with ⟨x, hx⟩
      rw [← neg_neg x, NegMemClass.coe_neg, ← sub_eq_add_neg] at hx
      exact ⟨_, hx⟩
    rintro a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩
    have := s.add_mem hxp hxn
    rw [add_assoc, add_sub_cancel, ← sub_eq_add_neg, ← AddSubgroupClass.coe_sub] at this
    replace := nonneg _ this
    rwa [f.map_sub, sub_nonneg] at this
  refine ⟨f.supSpanSingleton y (-c) hy, ?_, ?_⟩
  · refine lt_iff_le_not_ge.2 ⟨f.left_le_sup _ _, fun H => ?_⟩
    replace H := LinearPMap.domain_mono.monotone H
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le, singleton_subset_iff] at H
    exact hy H.2
  · rintro ⟨z, hz⟩ hzs
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩
    simp only at hzs
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, smul_neg, ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · have : -(r⁻¹ • x) - y ∈ s := by
        rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_neg, smul_smul,
          mul_inv_cancel₀ hr.ne, one_smul, sub_eq_add_neg, neg_smul, neg_neg]
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this
      have hm := smul_le_smul_of_nonpos_left this hr.le
      simpa only [f.map_smul, RingHom.id_apply, smul_smul, mul_inv_cancel₀ hr.ne, one_smul] using hm
    · subst r
      simp only [zero_smul, add_zero] at hzs ⊢
      rw [RingHom.id_apply, zero_smul]
      apply nonneg
      exact hzs
    · have : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this
      have hm := smul_le_smul_of_nonneg_left this hr.le
      simpa only [f.map_smul, RingHom.id_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hm

theorem exists_top (p : E →ₗ.[ℚ] ℝ) (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
    ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x := by
  set S := { p : E →ₗ.[ℚ] ℝ | ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x }
  have hSc : ∀ c, c ⊆ S → IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcs c_chain y hy
    clear hp_nonneg hp_dense p
    have cne : c.Nonempty := ⟨y, hy⟩
    have hcd : DirectedOn (· ≤ ·) c := c_chain.directedOn
    refine ⟨LinearPMap.sSup c hcd, ?_, fun _ ↦ LinearPMap.le_sSup hcd⟩
    rintro ⟨x, hx⟩ hxs
    have hdir : DirectedOn (· ≤ ·) (LinearPMap.domain '' c) :=
      directedOn_image.2 (hcd.mono LinearPMap.domain_mono.monotone)
    rcases (mem_sSup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨f, hfc, rfl⟩, hfx⟩
    have : f ≤ LinearPMap.sSup c hcd := LinearPMap.le_sSup _ hfc
    convert! ← hcs hfc ⟨x, hfx⟩ hxs using 1
    all_goals try with_reducible_and_instances rfl
    exact this.2 rfl
  obtain ⟨q, hpq, hqs, hq⟩ := zorn_le_nonempty₀ S hSc p hp_nonneg
  refine ⟨q, hpq, ?_, hqs⟩
  contrapose! hq
  have hqd : ∀ y, ∃ x : q.domain, (x : E) + y ∈ s := fun y ↦
    let ⟨x, hx⟩ := hp_dense y
    ⟨Submodule.inclusion hpq.left x, hx⟩
  rcases step s q hqs hqd hq with ⟨r, hqr, hr⟩
  exact ⟨r, hr, hqr.le, fun hrq ↦ hqr.ne' <| hrq.antisymm hqr.le⟩

end RationalRieszExtension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem rational_riesz_extension (s : PointedCone ℚ E) (f : E →ₗ.[ℚ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℚ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x := by
  rcases RationalRieszExtension.exists_top s f nonneg dense
    with ⟨⟨g_dom, g⟩, ⟨-, hfg⟩, rfl : g_dom = ⊤, hgs⟩
  refine ⟨g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), ?_, ?_⟩
  · exact fun x => (hfg rfl).symm
  · exact fun x hx => hgs ⟨x, _⟩ hx

end

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- A normalized monotone real-valued additive state on an ordered group
with an order unit. Positive unit multiples must not be nonpositive.
Neither linear order nor unperforation of the group is assumed. -/
theorem orderedGroup_normalized_state (u : G) (hu : 0 ≤ u)
    (hn : ∀ n : ℕ, 0 < n → ¬ n • u ≤ 0)
    (hb : ∀ g : G, ∃ N : ℕ, -(N • u) ≤ g) :
    ∃ f : G →+ ℝ, Monotone f ∧ f u = 1 := by
  let v : DivisibleHull G := u
  have hv : v ≠ 0 := orderedGroupRationalCone_unit_ne_zero u hn
  let p : DivisibleHull G →ₗ.[ℚ] ℝ := LinearPMap.mkSpanSingleton v 1 hv
  have hp : ∀ x : p.domain, (x : DivisibleHull G) ∈ orderedGroupRationalCone → 0 ≤ p x := by
    rintro ⟨x,hx⟩ hxc
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hq : 0 ≤ q := orderedGroupRationalCone_unit_scalar u hn hxc
    change 0 ≤ LinearPMap.mkSpanSingleton' v (1 : ℝ) _ ⟨q • v, _⟩
    rw [LinearPMap.mkSpanSingleton'_apply]
    simpa using (smul_nonneg hq (zero_le_one : (0 : ℝ) ≤ 1))
  have hd : ∀ y : DivisibleHull G, ∃ x : p.domain, (x : DivisibleHull G)+y ∈ orderedGroupRationalCone := by
    intro y
    obtain ⟨N,hN⟩ := orderedGroupRationalCone_cofinal u hu hb y
    exact ⟨⟨(N : ℚ) • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)⟩,hN⟩
  obtain ⟨g,hg,hpos⟩ := rational_riesz_extension orderedGroupRationalCone p hp hd
  let f : G →+ ℝ := g.toAddMonoidHom.comp (DivisibleHull.coeAddMonoidHom G)
  have hfpos : ∀ x : G, 0 ≤ x → 0 ≤ f x := by
    intro x hx
    exact hpos _ (orderedGroupRationalCone_coe hx)
  refine ⟨f,?_,?_⟩
  · intro a b hab
    have h := hfpos (b-a) (sub_nonneg.mpr hab)
    rwa [map_sub,sub_nonneg] at h
  · have he := hg ⟨v,Submodule.mem_span_singleton_self v⟩
    change g v = 1
    rw [he]
    exact LinearPMap.mkSpanSingleton_apply ℚ ℚ hv (1 : ℝ)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.OrderedStates_Semigroup
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Catalytic orders, ordered group completion, and normalized semigroup states. -/

namespace Kaplansky

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- An order compression of successive multiples iterates without any
cancellation assumption. -/
theorem nsmul_compression_iterate (u : S) (m : ℕ)
    (h : (m+1) • u ≤ m • u) : ∀ k : ℕ, (m+k) • u ≤ m • u := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (m+(k+1)) • u = (m+k) • u + u := by simp only [← Nat.add_assoc, add_nsmul, one_nsmul]
        _ ≤ m • u + u := add_le_add ih le_rfl
        _ = (m+1) • u := by simp only [add_nsmul, one_nsmul]
        _ ≤ m • u := h

/-- The ordered-semigroup arithmetic used in MR Theorem 2.3: if a larger
multiple of the unit is below a smaller one, some positive multiple is
properly infinite in the semigroup sense. No Cuntz correspondence is assumed. -/
theorem nsmul_compression_doubles (u : S) (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m < n) (h : n • u ≤ m • u) :
    ∃ k : ℕ, 0 < k ∧ (2*k) • u ≤ k • u := by
  have hstep : (m+1) • u ≤ m • u :=
    (nsmul_le_nsmul_left hu (by omega)).trans h
  by_cases hm : m = 0
  · subst m
    have hu0 : u ≤ 0 := by simpa only [Nat.zero_add, one_nsmul, zero_nsmul] using hstep
    refine ⟨1,by omega,?_⟩
    simpa only [Nat.mul_one, two_nsmul, one_nsmul, add_zero] using add_le_add le_rfl hu0
  · refine ⟨m,by omega,?_⟩
    simpa [Nat.two_mul] using nsmul_compression_iterate u m hstep m

/-- Absence of a properly infinite positive multiple makes the ordinary
natural multiples of the unit order-reflecting. This is the first
semigroup step toward quasitrace existence, not that existence theorem. -/
theorem nsmul_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hfinite : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u) (m n : ℕ) :
    m • u ≤ n • u ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hmn
    obtain ⟨k,hk,hk'⟩ := nsmul_compression_doubles u hu (by omega : n < m) h
    exact hfinite k hk hk'
  · exact nsmul_le_nsmul_left hu

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- A common summand can be retained while a comparison is iterated.
There is no cancellation assumption on the monoid. -/
theorem catalytic_nsmul_le {a b c : S} (h : a + c ≤ b + c) (k : ℕ) :
    k • a + c ≤ k • b + c := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (k+1) • a + c = a + (k • a + c) := by simp only [add_nsmul, one_nsmul]; ac_rfl
      _ ≤ a + (k • b + c) := add_le_add le_rfl ih
      _ = k • b + (a + c) := by ac_rfl
      _ ≤ k • b + (b + c) := add_le_add le_rfl h
      _ = (k+1) • b + c := by simp only [add_nsmul, one_nsmul, add_assoc]

/-- A bounded nonnegative common summand cannot hide a compression of
unit multiples when every positive multiple fails to be properly infinite. -/
theorem catalytic_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    {c : S} (hc : 0 ≤ c) (hcu : ∃ N : ℕ, c ≤ N • u) (m n : ℕ) :
    m • u + c ≤ n • u + c ↔ m ≤ n := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := hcu
    have hi := catalytic_nsmul_le h (N+1)
    have hcomp : ((N+1)*m) • u ≤ ((N+1)*n+N) • u := by
      calc
        ((N+1)*m) • u ≤ ((N+1)*m) • u + c := le_add_of_nonneg_right hc
        _ ≤ ((N+1)*n) • u + c := by simpa only [← mul_nsmul, Nat.mul_comm] using hi
        _ ≤ ((N+1)*n) • u + N • u := add_le_add le_rfl hN
        _ = ((N+1)*n+N) • u := (add_nsmul _ _ _).symm
    have hn := (nsmul_unit_order_iff u hu hf _ _).mp hcomp
    by_contra hmn
    have hmn' : n+1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_left (N+1) hmn'
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · intro h
    exact add_le_add (nsmul_le_nsmul_left hu h) le_rfl

/-- Stabilization by an arbitrary common summand preserves the natural
order on the unit if every element is nonnegative and bounded by a unit multiple. -/
theorem stabilized_unit_order_iff (u : S) (hu : 0 ≤ u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (m n : ℕ) :
    (∃ c : S, m • u + c ≤ n • u + c) ↔ m ≤ n := by
  constructor
  · rintro ⟨c, hc⟩
    exact (catalytic_unit_order_iff u hu hf (hpos c) (hbound c) m n).mp hc
  · intro h
    exact ⟨0, by simpa using nsmul_le_nsmul_left hu h⟩

end

section
variable (S : Type*) [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

variable {S}

theorem semigroupDifferenceClass_le (a b : SemigroupDifference S) :
    semigroupDifferenceClass a ≤ semigroupDifferenceClass b ↔
      ∃ c : S, a.1+b.2+c ≤ b.1+a.2+c :=
  toAntisymmetrization_le_toAntisymmetrization_iff

instance instIsOrderedAddMonoidSemigroupOrderedGroup : IsOrderedAddMonoid (SemigroupOrderedGroup S) where
  add_le_add_left a b h c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact (semigroupDifferenceClass_le _ _).mpr
      (SemigroupDifference.add_le_add ((semigroupDifferenceClass_le _ _).mp h) (le_refl c))

theorem semigroupToOrderedGroup_le_iff (a b : S) :
    semigroupToOrderedGroup a ≤ semigroupToOrderedGroup b ↔ ∃ c : S, a+c ≤ b+c := by
  change semigroupDifferenceClass (a,0) ≤ semigroupDifferenceClass (b,0) ↔ _
  simpa only [add_zero] using semigroupDifferenceClass_le (a,0) (b,0)

theorem semigroupToOrderedGroup_monotone : Monotone (semigroupToOrderedGroup (S := S)) := by
  intro a b hab
  exact (semigroupToOrderedGroup_le_iff a b).mpr ⟨0, by simpa using hab⟩

end

section
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

theorem semigroupDifferenceClass_eq_sub (a b : S) :
    semigroupDifferenceClass (a,b) = semigroupToOrderedGroup a - semigroupToOrderedGroup b := by
  change semigroupDifferenceClass (a,b) = semigroupDifferenceClass ((a,0)+(0,b))
  congr 1
  exact Prod.ext (add_zero a).symm (zero_add b).symm

theorem semigroupOrderedGroup_exists_difference (x : SemigroupOrderedGroup S) :
    ∃ a b : S, x = semigroupToOrderedGroup a - semigroupToOrderedGroup b := by
  induction x using Quotient.inductionOn with | h x =>
  exact ⟨x.1,x.2,semigroupDifferenceClass_eq_sub _ _⟩

/-- The image of the unit remains order-reflecting on all natural multiples,
including after passage to the ordered group quotient. -/
theorem semigroupOrderedGroup_unit_order (u : S)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (m n : ℕ) :
    m • semigroupToOrderedGroup u ≤ n • semigroupToOrderedGroup u ↔ m ≤ n := by
  rw [← map_nsmul, ← map_nsmul, semigroupToOrderedGroup_le_iff]
  exact stabilized_unit_order_iff u (hpos u) hf hpos hbound m n

theorem semigroupOrderedGroup_unit_nonneg (u : S) (hu : 0 ≤ u) :
    0 ≤ semigroupToOrderedGroup u := by
  simpa using semigroupToOrderedGroup_monotone hu

/-- The original order-unit bound becomes a two-sided bound on every
element of the ordered group. No finite generation is needed. -/
theorem semigroupOrderedGroup_order_unit (u : S)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (x : SemigroupOrderedGroup S) :
    ∃ N : ℕ, -(N • semigroupToOrderedGroup u) ≤ x ∧
      x ≤ N • semigroupToOrderedGroup u := by
  obtain ⟨a,b,rfl⟩ := semigroupOrderedGroup_exists_difference x
  obtain ⟨m,hm⟩ := hbound a
  obtain ⟨n,hn⟩ := hbound b
  have ha := semigroupToOrderedGroup_monotone hm
  have hb := semigroupToOrderedGroup_monotone hn
  rw [map_nsmul] at ha hb
  have hza := semigroupOrderedGroup_unit_nonneg a (hpos a)
  have hzb := semigroupOrderedGroup_unit_nonneg b (hpos b)
  have hu := semigroupOrderedGroup_unit_nonneg u (hpos u)
  refine ⟨m+n, ?_, ?_⟩
  · have hb' : semigroupToOrderedGroup b ≤ (m+n) • semigroupToOrderedGroup u :=
      hb.trans (nsmul_le_nsmul_left hu (Nat.le_add_left n m))
    exact (neg_le_neg hb').trans (neg_le_sub_iff_le_add.mpr (by simpa using hza))
  · have ha' : semigroupToOrderedGroup a ≤ (m+n) • semigroupToOrderedGroup u :=
      ha.trans (nsmul_le_nsmul_left hu (Nat.le_add_right m n))
    exact (sub_le_self _ hzb).trans ha'

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

theorem semigroupOrderedGroupLift_monotone (f : S →+ G) (hf : Monotone f) :
    Monotone (semigroupOrderedGroupLift f hf) := by
  intro a b hab
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  exact semigroupDifference_value_mono f hf ((semigroupDifferenceClass_le _ _).mp hab)

theorem semigroup_state_iff_orderedGroup_state (u : S) :
    (∃ f : S →+ ℝ, Monotone f ∧ f u = 1) ↔
      ∃ g : SemigroupOrderedGroup S →+ ℝ, Monotone g ∧ g (semigroupToOrderedGroup u) = 1 := by
  constructor
  · rintro ⟨f,hf,hu⟩
    exact ⟨semigroupOrderedGroupLift f hf,semigroupOrderedGroupLift_monotone f hf,by simpa⟩
  · rintro ⟨g,hg,hu⟩
    exact ⟨g.comp semigroupToOrderedGroup,hg.comp semigroupToOrderedGroup_monotone,hu⟩

end

variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

/-- State construction on a positive ordered commutative monoid with an
order unit and no properly infinite positive unit multiple. Cancellation
and unperforation are not hypotheses. This is an abstract semigroup theorem,
not yet a quasitrace on an algebra. -/
theorem positive_orderUnit_normalized_state (u : S)
    (hpos : ∀ c : S, 0 ≤ c) (hbound : ∀ c : S, ∃ N : ℕ, c ≤ N • u)
    (hf : ∀ k : ℕ, 0 < k → ¬ (2*k) • u ≤ k • u) :
    ∃ f : S →+ ℝ, Monotone f ∧ f u = 1 := by
  apply (semigroup_state_iff_orderedGroup_state u).mpr
  apply orderedGroup_normalized_state (semigroupToOrderedGroup u)
    (semigroupOrderedGroup_unit_nonneg u (hpos u))
  · intro n hn h
    have h' : n • semigroupToOrderedGroup u ≤ 0 • semigroupToOrderedGroup u := by simpa using h
    have hle := (semigroupOrderedGroup_unit_order u hf hpos hbound n 0).mp h'
    omega
  · intro x
    obtain ⟨N,hl,_⟩ := semigroupOrderedGroup_order_unit u hpos hbound x
    exact ⟨N,hl⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_State
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Dimension states of the Cuntz monoid and positivity. -/

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem normalizedCuntzState_exists
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    ∃ f : CuntzMonoid A →+ ℝ, Monotone f ∧ f (cuntzUnit A 1) = 1 := by
  apply positive_orderUnit_normalized_state (cuntzUnit A 1)
    cuntzMonoid_nonneg cuntzMonoid_orderUnit
  intro k hk h
  exact hf k hk (properlyInfinite_of_cuntzUnit_compression k h)

theorem cuntzDimensionState_nonempty
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    Nonempty (CuntzDimensionState A) := by
  obtain ⟨f, hm, hu⟩ := normalizedCuntzState_exists hf
  exact ⟨⟨f, hm, hu⟩⟩

end Kaplansky

open scoped Matrix CStarAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Spectral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.CuntzDimensionState.spectralMeasure_finite _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Spectral candidates on squares, orthogonal elements, and complex elements. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder
open MeasureTheory

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace CuntzDimensionState

theorem complexValue_one (d : CuntzDimensionState A) (n : ℕ) :
    d.complexValue (1 : CStarMatrix (Fin n) (Fin n) A) = (n : ℂ) := by
  rw [d.complexValue_of_nonneg zero_le_one]
  change (d.spectralValue (.unit n) : ℂ) = _
  rw [d.spectralValue_unit]
  norm_cast

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Cuntz_Quasitrace
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Corner-compatible spectral quasitraces and nonunital abelian complex linearity. -/

open scoped Matrix CStarAlgebra ComplexStarModule ComplexOrder

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance] matrixRealFunctionalCalculus matrixNonUnitalRealFunctionalCalculus matrixNonnegSpectrum
variable {A : Type*} [CStarAlgebra A]

theorem spectralCorner_posPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁺ = corner i a⁺ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁺) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_negPart {n : ℕ} (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    (corner i a)⁻ = corner i a⁻ := by
  exact ((spectralCornerHom (A := A) i).map_cfcₙ (fun t : ℝ => t⁻) a
    (ha := ha) (hφa := corner_selfAdjoint i ha)).symm

theorem spectralCorner_realPart {n : ℕ} (i : Fin n) (a : A) :
    (ℜ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℜ a : A) :=
  (map_realPart (spectralCornerHom (A := A) i) a).symm

theorem spectralCorner_imaginaryPart {n : ℕ} (i : Fin n) (a : A) :
    (ℑ (corner i a) : CStarMatrix (Fin n) (Fin n) A) = corner i (ℑ a : A) :=
  (map_imaginaryPart (spectralCornerHom (A := A) i) a).symm

/-- A single rectangular entry implements equality of spectral values between
any positive corner and its one-by-one matrix. -/
theorem CuntzDimensionState.positiveValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : 0 ≤ a) :
    d.positiveValue (corner i a) (corner_nonneg i ha) =
      d.positiveValue (corner (0 : Fin 1) a) (corner_nonneg _ ha) := by
  let S := CFC.sqrt a
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  let x : Matrix (Fin n) (Fin 1) A := Matrix.single i 0 S
  have hx : x*x.conjTranspose = CStarMatrix.ofMatrix.symm (corner i a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single i i (S*star S) = Matrix.single i i a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hy : x.conjTranspose*x = CStarMatrix.ofMatrix.symm (corner (0 : Fin 1) a) := by
    dsimp only [x]
    rw [Matrix.conjTranspose_single, Matrix.single_mul_single_same]
    change Matrix.single 0 0 (star S*S) = Matrix.single 0 0 a
    rw [hS, CFC.sqrt_mul_sqrt_self a ha]
  have hp : 0 ≤ CStarMatrix.ofMatrix (x*x.conjTranspose) := by rw [hx]; exact corner_nonneg i ha
  have hq : 0 ≤ CStarMatrix.ofMatrix (x.conjTranspose*x) := by rw [hy]; exact corner_nonneg _ ha
  simpa only [hx, hy, positiveValue] using d.spectralValue_rectangular_gram x hp hq

theorem CuntzDimensionState.signedValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) {a : A} (ha : IsSelfAdjoint a) :
    d.signedValue (corner i a) = d.signedValue (corner (0 : Fin 1) a) := by
  simp only [signedValue, spectralCorner_posPart i ha, spectralCorner_negPart i ha,
    spectralCorner_posPart (0 : Fin 1) ha, spectralCorner_negPart (0 : Fin 1) ha,
    d.positiveValue_corner i (CFC.posPart_nonneg a), d.positiveValue_corner i (CFC.negPart_nonneg a)]

/-- Whole-algebra corner compatibility for the same stabilized construction. -/
theorem CuntzDimensionState.complexValue_corner (d : CuntzDimensionState A) {n : ℕ}
    (i : Fin n) (a : A) :
    d.complexValue (corner i a) = d.complexValue (corner (0 : Fin 1) a) := by
  simp only [complexValue, spectralCorner_realPart, spectralCorner_imaginaryPart,
    d.signedValue_corner i (ℜ a).property, d.signedValue_corner i (ℑ a).property]

namespace CuntzDimensionState

theorem baseValue_one (d : CuntzDimensionState A) : d.baseValue (1 : A) = 1 := by
  unfold baseValue
  have hc : corner (0 : Fin 1) (1 : A) = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [corner, entry]
  rw [hc, d.complexValue_one]
  norm_num

theorem spectralCandidate_corner (d : CuntzDimensionState A) (a : A) :
    d.spectralCandidate.2 (upperLeft a) = d.spectralCandidate.1 a := by
  change d.complexValue (upperLeft a) = d.baseValue a
  rw [upperLeft_eq_corner]
  exact d.complexValue_corner (0 : Fin 2) a

theorem normalizedTwoQuasitrace_of_spectral_linearity (d : CuntzDimensionState A)
    (hlin : ∀ S : NonUnitalStarSubalgebra ℂ A, IsClosed (S : Set A) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x)
    (hlin2 : ∀ S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) A),
      IsClosed (S : Set (CStarMatrix (Fin 2) (Fin 2) A)) →
      (∀ x y : S, x*y=y*x) → ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.complexValue (x : CStarMatrix (Fin 2) (Fin 2) A)) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo := by
  let σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A) := {
    toFun := d.complexValue
    square_nonneg := d.complexValue_square_nonneg
    square_swap := d.complexValue_square_swap
    real_imag := d.complexValue_real_imag
    abelian_linear := hlin2 }
  exact ⟨d.oneQuasitraceOfSpectralCandidate hlin, d.baseValue_one,
    σ, d.spectralCandidate_corner⟩

/-- The same axiom at size one, expressed on the original coefficient algebra. -/
theorem baseValue_abelian_linear (d : CuntzDimensionState A)
    (S : NonUnitalStarSubalgebra ℂ A) (hS : IsClosed (S : Set A))
    (hcomm : ∀ x y : S, x*y=y*x) :
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = d.baseValue x := by
  let : IsClosed (S : Set A) := hS
  let : NonUnitalCommCStarAlgebra S := { (inferInstance : NonUnitalCStarAlgebra S) with mul_comm := hcomm }
  let φ := (spectralCornerHom (A := A) (0 : Fin 1)).comp (NonUnitalStarSubalgebraClass.subtype S)
  exact ⟨d.nonunitalCommutativeValueLinearMap φ,
    fun x => d.nonunitalCommutativeValueLinearMap_apply φ x⟩

/-- A normalized two-quasitrace from a dimension state, with both original
abelian-linearity premises now discharged for the SAME spectral construction. -/
theorem normalizedTwoQuasitrace_exists (d : CuntzDimensionState A) :
    ∃ τ : OneQuasitrace A, τ.Normalized ∧ τ.IsTwo :=
  d.normalizedTwoQuasitrace_of_spectral_linearity d.baseValue_abelian_linear
    (d.complexValue_abelian_linear 2)

end CuntzDimensionState
end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Products
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded C-star products and the generated separable unital algebra. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]

/-- The coordinate column identities give the actual product identity. -/
theorem boundedProduct_column {N : ℕ} (x : Fin N → ∀ i, A i)
    (hx : ∀ k i, ‖x k i‖ ≤ 1)
    (hcol : ∀ i, ∑ k, star (x k i) * x k i = 1) :
    ∑ k, star (boundedProductLift (x k) (hx k)) * boundedProductLift (x k) (hx k) =
      (1 : BoundedProduct A) := by
  ext i
  rw [boundedProduct_sum_apply]
  change (∑ k, star (x k i) * x k i) = 1
  exact hcol i

theorem boundedProduct_row {N : ℕ} (x : Fin N → ∀ i, A i)
    (hx : ∀ k i, ‖x k i‖ ≤ 1) (c : ℝ)
    (hrow : ∀ i, ∑ k, x k i * star (x k i) ≤ (c : ℂ) • (1 : A i)) :
    ∑ k, boundedProductLift (x k) (hx k) * star (boundedProductLift (x k) (hx k)) ≤
      (c : ℂ) • (1 : BoundedProduct A) := by
  apply (boundedProduct_le_iff _ _).mpr
  intro i
  rw [boundedProduct_sum_apply]
  change (∑ k, x k i * star (x k i)) ≤ (c : ℂ) • (1 : A i)
  exact hrow i

end Kaplansky

end

noncomputable section
open TopologicalSpace
open scoped Pointwise
namespace Kaplansky

/-- Countably many letters have only countably many finite multiplicative words. -/
theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

variable {A : Type*} [CStarAlgebra A]

theorem generatedAlgebra_separable {s : Set A} (hs : s.Countable) :
    SeparableSpace (generatedAlgebra s) := by
  have hstar : (star s).Countable := by
    convert hs.image star using 1
    all_goals try with_reducible_and_instances rfl
    ext a
    simp
  have hw := countable_monoid_closure (hs.union hstar)
  have hspan := hw.isSeparable.span (R := ℂ)
  rw [← StarAlgebra.adjoin_eq_span] at hspan
  have hc := hspan.closure
  exact hc.separableSpace

instance finiteGeneratedAlgebra_separable {N : ℕ} (x : Fin N → A) :
    SeparableSpace (generatedAlgebra (Set.range x)) :=
  generatedAlgebra_separable (Set.countable_range x)

end Kaplansky

end

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder
attribute [local instance] CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

attribute [local instance] OAI.Kaplansky.closedSubalgebraLE
attribute [local instance] OAI.Kaplansky.closedSubalgebraPreorder
/-- Closed C*-subalgebras reflect positivity. The square-root witness
belongs to the subalgebra by continuous functional calculus. -/
theorem closedSubalgebra_nonneg_iff (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (a : S) : 0 ≤ a ↔ 0 ≤ (a : A) := by
  constructor
  · intro h
    obtain ⟨x,rfl⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mp h
    exact star_mul_self_nonneg (x : A)
  · intro h
    have hmem : CFC.sqrt (a : A) ∈ S := by
      rw [CFC.sqrt_eq_real_sqrt _ h]
      exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
    let b : S := ⟨CFC.sqrt (a : A),hmem⟩
    apply (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := a)).mpr
    refine ⟨b, ?_⟩
    apply Subtype.ext
    change (a : A) = star (CFC.sqrt (a : A)) * CFC.sqrt (a : A)
    rw [(CFC.sqrt_nonneg (a : A)).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ h]

theorem closedSubalgebra_le_iff (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (a b : S) : a ≤ b ↔ (a : A) ≤ (b : A) := by
  rw [← sub_nonneg, closedSubalgebra_nonneg_iff]
  exact sub_nonneg

theorem generatedGenerator_column {N : ℕ} (x : Fin N → A)
    (hx : ∑ k, star (x k) * x k = 1) :
    ∑ k, star (generatedGenerator x k) * generatedGenerator x k = 1 := by
  apply Subtype.ext
  change (generatedAlgebra (Set.range x)).subtype
      (∑ k, star (generatedGenerator x k) * generatedGenerator x k) = _
  rw [map_sum]
  exact hx

theorem generatedGenerator_row {N : ℕ} (x : Fin N → A) (c : ℝ)
    (hx : ∑ k, x k * star (x k) ≤ (c : ℂ) • (1 : A)) :
    ∑ k, generatedGenerator x k * star (generatedGenerator x k) ≤ (c : ℂ) • 1 := by
  apply (closedSubalgebra_le_iff _ _ _).mpr
  change (generatedAlgebra (Set.range x)).subtype
      (∑ k, generatedGenerator x k * star (generatedGenerator x k)) ≤ _
  rw [map_sum]
  exact hx

theorem bounded_generated_relations {I : Type*} {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
    {N : ℕ} (x : Fin N → ∀ i, A i) (hx : ∀ k i, ‖x k i‖ ≤ 1)
    (c : ℝ) (hcol : ∀ i, ∑ k, star (x k i) * x k i = 1)
    (hrow : ∀ i, ∑ k, x k i * star (x k i) ≤ (c : ℂ) • (1 : A i)) :
    let y := fun k => boundedProductLift (x k) (hx k)
    let z := generatedGenerator y
    (∑ k, star (z k) * z k = 1) ∧ (∑ k, z k * star (z k) ≤ (c : ℂ) • 1) := by
  dsimp only
  exact ⟨generatedGenerator_column _ (boundedProduct_column x hx hcol),
    generatedGenerator_row _ c (boundedProduct_row x hx c hrow)⟩

end Kaplansky

end

noncomputable section
namespace Kaplansky

/-- The closed generated algebra contains the ambient unit and is
nontrivial whenever the ambient algebra is nontrivial. -/
theorem generatedAlgebra_nontrivial {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (s : Set A) : Nontrivial (generatedAlgebra s) := by
  infer_instance

theorem boundedGeneratedAlgebra_nontrivial {I : Type*} [Nonempty I] {A : I → Type*}
    [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)] {N : ℕ}
    (x : Fin N → ∀ i, A i) (hx : ∀ k i, ‖x k i‖ ≤ 1) :
    Nontrivial (generatedAlgebra (Set.range (fun k => boundedProductLift (x k) (hx k)))) := by
  let : Nontrivial (BoundedProduct A) := boundedProduct_nontrivial
  exact generatedAlgebra_nontrivial _

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

variable [∀ j, CompleteSpace (E j)]

theorem forwardShift_single (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (j : ℕ) (v : E j) : forwardShift T hT (lp.single 2 j v) =
      lp.single 2 (j+1) (T j v) := by
  have he : lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v) =
      lp.single 2 j (T j v) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  change successorInclusion (lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v)) = _
  rw [he]
  exact OrthogonalFamily.linearIsometry_apply_single _ _

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

/-- A forward shift has zero output in degree zero. -/
theorem forwardShift_apply_zero (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) : forwardShift T hT f 0 = 0 := by
  have he : (lp.evalCLM ℂ E 2 0).comp (forwardShift T hT) = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro j
    ext v
    change forwardShift T hT (lp.single 2 j v) 0 = 0
    rw [forwardShift_single]
    simp
  exact DFunLike.congr_fun he f

/-- On degree j+1, the forward shift is exactly its j-th block. -/
theorem forwardShift_apply_succ (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) : forwardShift T hT f (j+1) = T j (f j) := by
  have he : (lp.evalCLM ℂ E 2 (j+1)).comp (forwardShift T hT) =
      (T j).comp (lp.evalCLM ℂ E 2 j) := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    ext v
    change forwardShift T hT (lp.single 2 k v) (j+1) = T j (lp.single 2 k v j)
    rw [forwardShift_single]
    by_cases hk : j = k
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (show j+1 ≠ k+1 by omega)]
  exact DFunLike.congr_fun he f

/-- The adjoint lowers degree, using the adjoint of the actual block. -/
theorem forwardShift_adjoint_apply (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) :
    (forwardShift T hT).adjoint f j = (T j).adjoint (f (j+1)) := by
  apply ext_inner_left ℂ
  intro v
  rw [← lp.inner_single_left j v, ContinuousLinearMap.adjoint_inner_right,
    forwardShift_single, lp.inner_single_left, ContinuousLinearMap.adjoint_inner_right]

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal ComplexOrder
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]
variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1))
  (hT : ∀ i j, ‖T i j‖ ≤ 1)

theorem forwardShift_column
    (hcol : ∀ j, ∑ i, (T i j).adjoint.comp (T i j) = ContinuousLinearMap.id ℂ (E j)) :
    ∑ i, (forwardShift (T i) (hT i)).adjoint * forwardShift (T i) (hT i) = 1 := by
  ext f j
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_adjoint_apply, forwardShift_apply_succ]
  simpa using DFunLike.congr_fun (hcol j) (f j)

theorem forwardShift_row_zero (f : FiberHilbertSum E) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f 0 = 0 := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_zero, Finset.sum_const_zero]

theorem forwardShift_row_succ (f : FiberHilbertSum E) (j : ℕ) :
    (∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f (j+1) =
      (∑ i, (T i j).comp (T i j).adjoint) (f (j+1)) := by
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply,
    mul_apply_eq_comp, forwardShift_apply_succ, forwardShift_adjoint_apply,
    ContinuousLinearMap.comp_apply]

theorem forwardShift_row_positive (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ j, ((c : ℂ) • ContinuousLinearMap.id ℂ (E (j+1)) -
      ∑ i, (T i j).comp (T i j).adjoint).IsPositive) :
    ((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  suffices hn : 0 ≤ inner ℂ (((c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) -
      ∑ i, forwardShift (T i) (hT i) * (forwardShift (T i) (hT i)).adjoint) f) f by
    rcases RCLike.nonneg_iff.mp hn with ⟨hre,him⟩
    exact ⟨Complex.ext rfl him.symm, hre⟩
  rw [lp.inner_eq_tsum]
  apply tsum_nonneg
  intro j
  cases j with
  | zero =>
      simp only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_zero, sub_zero, inner_smul_left]
      exact mul_nonneg (by simpa using hc) (by rw [inner_self_eq_norm_sq_to_K]; positivity)
  | succ j =>
      simpa only [sub_apply, smul_apply,
        one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        forwardShift_row_succ, ContinuousLinearMap.id_apply] using
          (hrow j).inner_nonneg_left (f (j+1))

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_ShiftAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generated Hilbert-shift algebra and its concrete realization. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hilbert-space positivity gives an actual square-root factorization. -/
theorem operator_positive_square {a : H →L[ℂ] H} (ha : a.IsPositive) :
    ∃ b : H →L[ℂ] H, a = star b * b :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr ha)

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

/-- Connect the ordinary operator order to the spectral order of the
bounded-product checkpoint. -/
theorem operator_positive_spectral {a : H →L[ℂ] H} (ha : a.IsPositive) : 0 ≤ a := by
  obtain ⟨b,rfl⟩ := operator_positive_square ha
  exact star_mul_self_nonneg b

variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]
variable {n : ℕ} (T : Fin n → ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ i j, ‖T i j‖ ≤ 1)

theorem forwardShift_row_spectral (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ j, ((c : ℂ) • ContinuousLinearMap.id ℂ (E (j+1)) -
      ∑ i, (T i j).comp (T i j).adjoint).IsPositive) :
    ∑ i, forwardShift (T i) (hT i) * star (forwardShift (T i) (hT i)) ≤
      (c : ℂ) • (1 : FiberHilbertSum E →L[ℂ] FiberHilbertSum E) := by
  exact sub_nonneg.mp (operator_positive_spectral (forwardShift_row_positive T hT c hc hrow))

theorem hilbertShift_generated_relations {I : Type*} {G : I → ℕ → Type*}
    [∀ z j, NormedAddCommGroup (G z j)] [∀ z j, InnerProductSpace ℂ (G z j)]
    [∀ z j, CompleteSpace (G z j)] [∀ z, Nontrivial (FiberHilbertSum (G z))]
    (X : Fin n → ∀ z j, G z j →L[ℂ] G z (j+1)) (hX : ∀ i z j, ‖X i z j‖ ≤ 1)
    (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∀ z j, ∑ i, (X i z j).adjoint.comp (X i z j) = ContinuousLinearMap.id ℂ (G z j))
    (hrow : ∀ z j, ((c : ℂ) • ContinuousLinearMap.id ℂ (G z (j+1)) -
      ∑ i, (X i z j).comp (X i z j).adjoint).IsPositive) :
    let x := fun i z => forwardShift (X i z) (hX i z)
    let y := fun i => boundedProductLift (x i) (fun z => forwardShift_norm_le (X i z) (hX i z))
    let b := generatedGenerator y
    (∑ i, star (b i) * b i = 1) ∧ (∑ i, b i * star (b i) ≤ (c : ℂ) • 1) := by
  exact bounded_generated_relations _ (fun i z => forwardShift_norm_le (X i z) (hX i z)) c
    (fun z => forwardShift_column (fun i => X i z) (fun i => hX i z) (hcol z))
    (fun z => forwardShift_row_spectral (fun i => X i z) (fun i => hX i z) c hc (hrow z))

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

attribute [local instance] fiberHilbertSum_nontrivial

theorem source_shift_algebra {I : Type*} [Nonempty I] {G : I → ℕ → Type*}
    [∀ z j, NormedAddCommGroup (G z j)] [∀ z j, InnerProductSpace ℂ (G z j)]
    [∀ z j, CompleteSpace (G z j)] [∀ z, Nontrivial (G z 0)] {n : ℕ}
    (X : Fin n → ∀ z j, G z j →L[ℂ] G z (j+1))
    (hcol : ∀ z j, ∑ i, (X i z j).adjoint.comp (X i z j) = ContinuousLinearMap.id ℂ (G z j))
    (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ z j, ((c : ℂ) • ContinuousLinearMap.id ℂ (G z (j+1)) -
      ∑ i, (X i z j).comp (X i z j).adjoint).IsPositive) :
    let hX := fun i z j => block_norm_le_of_column (fun k => X k z j) (hcol z j) i
    let x := fun i z => forwardShift (X i z) (hX i z)
    let y := fun i => boundedProductLift (x i) (fun z => forwardShift_norm_le (X i z) (hX i z))
    let B := generatedAlgebra (Set.range y)
    let b := generatedGenerator y
    Nontrivial B ∧ TopologicalSpace.SeparableSpace B ∧
      (∑ i, star (b i) * b i = 1) ∧ (∑ i, b i * star (b i) ≤ (c : ℂ) • 1) := by
  let : ∀ z, Nontrivial (FiberHilbertSum (G z)) := fun z => fiberHilbertSum_nontrivial
  dsimp only
  refine ⟨boundedGeneratedAlgebra_nontrivial _ _, inferInstance, ?_⟩
  exact hilbertShift_generated_relations X _ c hc hcol hrow

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Words
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word propagation through Hilbert shifts and normalized tuple operators. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace Kaplansky.NormalizedHermitianTuple
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

local instance instCompleteSpace_rf51a67_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
attribute [local instance] OAI.Kaplansky.NormalizedHermitianTuple.instCompleteSpace_1
theorem operator_row (T : NormalizedHermitianTuple E F) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ F -
      ∑ i, (T.operator i).comp (T.operator i).adjoint).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro w
  simp_rw [operator_adjoint]
  let A : F →ₗ[ℂ] F := (2/3 : ℂ) • LinearMap.id - ∑ i, (T.forward i).comp (T.reverse i)
  have h : 0 ≤ inner ℂ w (A w) := T.row w
  rcases RCLike.nonneg_iff.mp h with ⟨hre,him⟩
  change (inner ℂ w (A w)).im = 0 at him
  have he : inner ℂ (A w) w = inner ℂ w (A w) := by
    rw [← inner_conj_symm]
    apply Complex.ext
    · rfl
    · change -(inner ℂ w (A w)).im = (inner ℂ w (A w)).im
      rw [him,neg_zero]
  change (↑((inner ℂ (A w) w).re) = inner ℂ (A w) w) ∧ 0 ≤ (inner ℂ (A w) w).re
  rw [he]
  exact ⟨Complex.ext rfl him.symm,hre⟩

end Kaplansky.NormalizedHermitianTuple

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_TestAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete test operators, their C-star algebra, and its faithful representation. -/

open Bundle Topology
open scoped BigOperators ComplexOrder
namespace Kaplansky
open ComplexGrassmann

theorem actualTestOperator_column (z : ActualTestIndex) (j : ℕ) :
    ∑ i, (actualTestOperator i z j).adjoint.comp (actualTestOperator i z j) =
      ContinuousLinearMap.id ℂ (ActualTestFiber z j) :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_column
    exact h

theorem actualTestOperator_row (z : ActualTestIndex) (j : ℕ) :
    ((2/3 : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1)) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive :=
  by
    let T : NormalizedHermitianTuple (ActualTestFiber z j) (ActualTestFiber z (j+1)) :=
      (testSequenceStep (R := z.2.1.val) z.1.property j).tuple z.2.2
    have h := T.operator_row
    exact h

open scoped BigOperators

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2000] closedSubalgebraLE closedSubalgebraPreorder

theorem actual_test_shift_algebra :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra ∧
      (∑ i, star (generatedGenerator actualBoundedGenerator i) *
        generatedGenerator actualBoundedGenerator i = 1) ∧
      (∑ i, generatedGenerator actualBoundedGenerator i *
        star (generatedGenerator actualBoundedGenerator i) ≤ (2/3 : ℂ) • 1) := by
  have hrow : ∀ z j, ((((2/3 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ActualTestFiber z (j+1))) -
      ∑ i, (actualTestOperator i z j).comp (actualTestOperator i z j).adjoint).IsPositive := by
    intro z j
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using actualTestOperator_row z j
  have h := source_shift_algebra actualTestOperator actualTestOperator_column (2/3)
    (by norm_num) hrow
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
  exact h


theorem actualAlgebra_nontrivial_separable :
    Nontrivial ActualAlgebra ∧ TopologicalSpace.SeparableSpace ActualAlgebra := by
  have h := actual_test_shift_algebra
  exact ⟨h.1,h.2.1⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_FaithfulRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped InnerProductSpace ENNReal
open Kaplansky

lemma actualFaithfulRepresentation_injective : Function.Injective actualFaithfulRepresentation := by
  classical
  intro a b hab
  apply Subtype.ext
  apply lp.ext
  apply funext
  intro z
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun T : ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert =>
    T (lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) hab
  change (a.val z) ((lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) = (b.val z) ((lp.single (E:=fun z : ActualTestIndex => ActualHilbert z) 2 z v) z) at h
  simpa only [lp.single_apply_self] using h


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_QuasitraceLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder BigOperators
open Kaplansky Regular
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
attribute [local instance 2100] closedSubalgebraLE closedSubalgebraPreorder

theorem reduced_quasitrace_loss_exists : ReducedQuasitraceLoss := by
  let d : CuntzDimensionState ActualAlgebra := Classical.choice
    (cuntzDimensionState_nonempty fun k hk => actualAlgebra_matrix_not_properlyInfinite hk)
  refine ⟨ActualAlgebra,inferInstance,actualAlgebra_nontrivial_separable.1,
    actualAlgebra_nontrivial_separable.2,?_,ActualRepresentationHilbert,inferInstance,inferInstance,
    inferInstance,actualFaithfulRepresentation,actualFaithfulRepresentation_injective,
    actualAlgebra_tensor_properlyInfinite,?_⟩
  · exact d.normalizedTwoQuasitrace_exists
  · rintro ⟨τ,hτ,_⟩
    exact not_properlyInfinite τ hτ actualAlgebra_tensor_properlyInfinite


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_ScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Kaplansky.ComplexGrassmann

open Topology Set
open scoped Manifold ContDiff BigOperators
variable {ι : Type*} [Fintype ι] (K : ι → ℕ)
instance productModelRealComplexTower : IsScalarTower ℝ ℂ (ProjectiveProductModel K) where
  smul_assoc r z f := by
    ext i x j
    exact smul_assoc r z (f i x j)


end Kaplansky.ComplexGrassmann

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace KaplanskyConsequences

theorem stable_finiteness_bundle_oai : StableFinitenessBundle :=
  ⟨simple_stable_tensor_counterexample_exists,reduced_quasitrace_loss_exists,
    trace_free_stably_finite_exists⟩

end KaplanskyConsequences
end
end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.stable_finiteness_bundle_oai := @OAI.KaplanskyConsequences.stable_finiteness_bundle_oai
