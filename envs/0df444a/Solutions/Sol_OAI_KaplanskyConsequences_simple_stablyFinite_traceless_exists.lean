-- Prove2me | solution 1 for OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:58:04.903169+00:00
-- url     : https://prove2.me/submissions/80ca6e7c-bea7-4472-a7a1-682296477dbe

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf005
import Definitions.Def_OAIQ15Sf012
import Theorems.Thm_OAI_Kaplansky_actualAlgebra_matrix_not_properlyInfinite
import Theorems.Thm_OAI_KaplanskyConsequences_QuasiValue_ultra_unitary_polar
import Theorems.Thm_OAI_KaplanskyConsequences_actualAlgebra_no_tracialState

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

local instance instCompleteSpace_r933261_1 : CompleteSpace E := FiniteDimensional.complete ℂ E
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
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_MaximalClosedIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open Topology
open scoped CStarAlgebra
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma maximal_closedStarIdeal_exists [Nontrivial A] :
    ∃ I : ClosedStarIdeal A, (1:A) ∉ I.toNonUnitalStarSubalgebra ∧
      ∀ J : ClosedStarIdeal A, I.toNonUnitalStarSubalgebra ≤ J.toNonUnitalStarSubalgebra →
        (1:A) ∉ J.toNonUnitalStarSubalgebra →
        J.toNonUnitalStarSubalgebra ≤ I.toNonUnitalStarSubalgebra := by
  let s := {S : NonUnitalStarSubalgebra ℂ A | ProperClosedIdeal S}
  have hchain : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc y hy
    have : Nonempty c := ⟨⟨y,hy⟩⟩
    have hd : Directed (· ≤ ·) (fun i : c => i.val) := by
      intro i j
      rcases hc.total i.property j.property with h | h
      · exact ⟨j,h,le_rfl⟩
      · exact ⟨i,le_rfl,h⟩
    let U : NonUnitalStarSubalgebra ℂ A := ⨆ i : c, i.val
    have hU : (U : Set A) = ⋃ i : c, (i.val : Set A) :=
      NonUnitalStarSubalgebra.coe_iSup_of_directed hd
    have hleft (a b : A) (hb : b ∈ U) : a*b ∈ U := by
      change b ∈ (U : Set A) at hb
      change a*b ∈ (U : Set A)
      rw [hU] at hb ⊢
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
      exact Set.mem_iUnion.mpr ⟨i,(hcs i.property).1 a b hi⟩
    have hright (a b : A) (ha : a ∈ U) : a*b ∈ U := by
      change a ∈ (U : Set A) at ha
      change a*b ∈ (U : Set A)
      rw [hU] at ha ⊢
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨i,(hcs i.property).2.1 a b hi⟩
    have hnonunits : (U : Set A) ⊆ {a : A | ¬ IsUnit a} := by
      intro a ha
      rw [hU] at ha
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp ha
      rintro ⟨v,rfl⟩
      have hone := (hcs i.property).2.1 (v:A) (↑(v⁻¹)) hi
      simp only [Units.mul_inv] at hone
      exact (hcs i.property).2.2.2 hone
    have hclosure : closure (U : Set A) ⊆ {a : A | ¬ IsUnit a} :=
      closure_minimal hnonunits Units.isOpen.isClosed_compl
    refine ⟨U.topologicalClosure,?_,?_⟩
    · refine ⟨?_,?_,U.isClosed_topologicalClosure,?_⟩
      · intro a b hb
        exact map_mem_closure (continuous_const.mul continuous_id) hb (fun b hb => hleft a b hb)
      · intro a b ha
        exact map_mem_closure (f:=fun x : A => x*b) (show Continuous (fun x : A => x*b) from continuous_id.mul continuous_const) ha (fun x hx => hright x b hx)
      · intro h1
        exact hclosure h1 isUnit_one
    · intro z hz
      exact (le_iSup (fun i : c => i.val) ⟨z,hz⟩).trans U.le_topologicalClosure
  have hbot : (⊥ : NonUnitalStarSubalgebra ℂ A) ∈ s := by
    refine ⟨?_,?_,?_,?_⟩
    · intro a b hb
      rw [NonUnitalStarAlgebra.mem_bot] at hb ⊢
      rw [hb,mul_zero]
    · intro a b ha
      rw [NonUnitalStarAlgebra.mem_bot] at ha ⊢
      rw [ha,zero_mul]
    · simp
    · simpa only [NonUnitalStarAlgebra.mem_bot] using (one_ne_zero : (1:A) ≠ 0)
  obtain ⟨M,_,hM,hmax⟩ := zorn_le_nonempty₀ s hchain ⊥ hbot
  let I : ClosedStarIdeal A := ⟨M,hM.1,hM.2.1,hM.2.2.1⟩
  refine ⟨I,hM.2.2.2,?_⟩
  intro J hij hj
  exact hmax ⟨J.mul_mem_left,J.mul_mem_right,J.closed,hj⟩ hij

namespace ClosedStarIdeal

lemma quotient_nontrivial [Nontrivial A] (I : ClosedStarIdeal A)
    (hI : (1:A) ∉ I.toNonUnitalStarSubalgebra) : Nontrivial I.Quotient := by
  apply nontrivial_of_ne (1:I.Quotient) 0
  intro h
  apply hI
  apply (I.mk_eq_zero 1).mp
  simpa only [map_one] using h

lemma quotient_simple [Nontrivial A] (I : ClosedStarIdeal A)
    (hmax : ∀ J : ClosedStarIdeal A, I.toNonUnitalStarSubalgebra ≤ J.toNonUnitalStarSubalgebra →
      (1:A) ∉ J.toNonUnitalStarSubalgebra → J.toNonUnitalStarSubalgebra ≤ I.toNonUnitalStarSubalgebra) :
    CStarSimple I.Quotient := by
  intro J
  by_cases h1 : (1:I.Quotient) ∈ J.toNonUnitalStarSubalgebra
  · right
    intro a
    simpa using J.mul_mem_left a 1 h1
  · left
    let K := J.comap I.mkStarAlgHom
    have hIK : I.toNonUnitalStarSubalgebra ≤ K.toNonUnitalStarSubalgebra := by
      intro a ha
      change I.quotientMap a ∈ J.toNonUnitalStarSubalgebra
      rw [(I.mk_eq_zero a).mpr ha]
      exact J.toNonUnitalStarSubalgebra.zero_mem
    have hK : (1:A) ∉ K.toNonUnitalStarSubalgebra := by
      intro hh
      apply h1
      change I.mkStarAlgHom 1 ∈ J.toNonUnitalStarSubalgebra at hh
      simpa using hh
    have hKI := hmax K hIK hK
    intro b hb
    obtain ⟨a,rfl⟩ := I.mk_surjective b
    exact (I.mk_eq_zero a).mpr (hKI hb)
end ClosedStarIdeal

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_TracePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma no_tracialState_of_map (f : A →⋆ₐ[ℂ] B) (hA : IsEmpty (TracialState A)) :
    IsEmpty (TracialState B) := ⟨fun τ => hA.false (tracialStatePullback f τ)⟩


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_DenseUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma isUnit_positive_shift {a : A} (ha : 0≤a) {r : ℝ} (hr : 0 < r) :
    IsUnit (a+r • (1:A)) := by
  exact ((IsStrictlyPositive.smul hr isStrictlyPositive_one).nonneg_add ha).isUnit

lemma denseUnits_of_unitary_polar [Nontrivial A]
    (h : ∀ x : A, ∃ w : A, star w*w=1 ∧ w*star w=1 ∧ w*CFC.sqrt (star x*x)=x) :
    DenseUnits A := by
  rw [DenseUnits,Metric.dense_iff]
  intro x ε hε
  obtain ⟨w,hi,hf,hw⟩ := h x
  let b := CFC.sqrt (star x*x)
  have hb : 0≤b := CFC.sqrt_nonneg _
  let y := w*(b+(ε/2:ℝ) • (1:A))
  have hwunit : IsUnit w := ⟨⟨w,star w,hf,hi⟩,rfl⟩
  have hy : IsUnit y := hwunit.mul (isUnit_positive_shift hb (half_pos hε))
  have hn : ‖w‖ ≤ 1 := by
    have hh := CStarRing.norm_star_mul_self (x:=w)
    rw [hi,norm_one] at hh
    nlinarith [norm_nonneg w]
  refine ⟨y,?_,hy⟩
  rw [Metric.mem_ball,dist_comm,dist_eq_norm]
  have he : x-y= -((ε/2:ℝ) • w) := by
    dsimp [y]
    rw [mul_add,mul_smul_comm,mul_one,hw,sub_add_cancel_left]
  rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
  nlinarith

open scoped CStarAlgebra in
lemma DenseUnits.map (h : DenseUnits A) (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Surjective φ) :
    DenseUnits B := by
  have hd : Dense (φ '' {a : A | IsUnit a}) := hφ.denseRange.dense_image (map_continuous φ) h
  exact Dense.mono (fun b hb => by obtain ⟨a,ha,rfl⟩ := hb; exact ha.map φ.toMonoidHom) hd

lemma DenseUnits.finite [Nontrivial A] (h : DenseUnits A) (v : A) (hv : star v*v=1) : v*star v=1 := by
  have hn : ‖v‖≤1 := by
    have hh := CStarRing.norm_star_mul_self (x:=v)
    rw [hv,norm_one] at hh
    nlinarith [norm_nonneg v]
  obtain ⟨b,hbv,hb⟩ := Metric.dense_iff.mp h v 1 zero_lt_one
  have he : ‖1-star v*b‖ < 1 := by
    have hbound : ‖star v*(v-b)‖ ≤ ‖v-b‖ := by
      exact (norm_mul_le _ _).trans (by rw [norm_star]; exact mul_le_of_le_one_left (norm_nonneg _) hn)
    have hid : 1-star v*b=star v*(v-b) := by rw [mul_sub,hv]
    rw [hid]
    exact hbound.trans_lt (by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hbv)
  have hs : IsUnit (star v*b) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one he
  have hsv : IsUnit (star v) := (hb.mul_right_iff).mp hs
  obtain ⟨z,hz⟩ := hsv
  have hzinv : v= ↑(z⁻¹) := by
    rw [← hz] at hv
    exact ((Units.mul_eq_one_iff_inv_eq (u:=z)).mp hv).symm
  rw [← hz,hzinv]
  exact z.inv_val


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_MatrixDenseUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
open Matrix Topology
section Algebra
variable {A m n : Type*} [Ring A] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma isUnit_lower (C : Matrix n m A) :
    IsUnit (fromBlocks (1 : Matrix m m A) 0 C (1 : Matrix n n A)) := by
  refine ⟨⟨fromBlocks 1 0 C 1,fromBlocks 1 0 (-C) 1,?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_upper (B : Matrix m n A) :
    IsUnit (fromBlocks (1 : Matrix m m A) B 0 (1 : Matrix n n A)) := by
  refine ⟨⟨fromBlocks 1 B 0 1,fromBlocks 1 (-B) 0 1,?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_diagonal (u : (Matrix m m A)ˣ) (v : (Matrix n n A)ˣ) :
    IsUnit (fromBlocks (u : Matrix m m A) 0 0 (v : Matrix n n A)) := by
  refine ⟨⟨fromBlocks (↑u) 0 0 (↑v),fromBlocks ((↑(u⁻¹) : Matrix m m A)) 0 0 (↑(v⁻¹)),?_,?_⟩,rfl⟩ <;>
    simp [fromBlocks_multiply,fromBlocks_one]

lemma isUnit_schur (u : (Matrix m m A)ˣ) (v : (Matrix n n A)ˣ)
    (B : Matrix m n A) (C : Matrix n m A) :
    IsUnit (fromBlocks (↑u) B C ((v : Matrix n n A)+C*(↑(u⁻¹) : Matrix m m A)*B)) := by
  have he : fromBlocks (↑u) B C ((v : Matrix n n A)+C*(↑(u⁻¹) : Matrix m m A)*B) =
      fromBlocks 1 0 (C*(↑(u⁻¹) : Matrix m m A)) 1 * fromBlocks (↑u) 0 0 (↑v) *
      fromBlocks 1 ((↑(u⁻¹) : Matrix m m A)*B) 0 1 := by
    simp [fromBlocks_multiply,Matrix.mul_assoc,add_comm]
    simp [← Matrix.mul_assoc]
  rw [he]
  exact ((isUnit_lower _).mul (isUnit_diagonal u v)).mul (isUnit_upper _)
end Algebra

section Topology
variable {A m n : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma denseUnits_blocks (hm : DenseUnits (Matrix m m A)) (hn : DenseUnits (Matrix n n A)) :
    DenseUnits (Matrix (m ⊕ n) (m ⊕ n) A) := by
  let S := closure {x : Matrix (m ⊕ n) (m ⊕ n) A | IsUnit x}
  have hc : IsClosed S := isClosed_closure
  have hunit (u : (Matrix m m A)ˣ) (B : Matrix m n A) (C : Matrix n m A) (D : Matrix n n A) :
      fromBlocks (↑u) B C D ∈ S := by
    have h : ∀ d : Matrix n n A, fromBlocks (↑u) B C (d+C*(↑(u⁻¹) : Matrix m m A)*B) ∈ S := by
      intro d
      refine hn.induction (P:=fun d => fromBlocks (↑u) B C (d+C*(↑(u⁻¹) : Matrix m m A)*B) ∈ S) ?_ ?_ d
      · intro d hd
        obtain ⟨v,rfl⟩ := hd
        exact subset_closure (isUnit_schur u v B C)
      · exact hc.preimage (by fun_prop)
    simpa using h (D-C*(↑(u⁻¹) : Matrix m m A)*B)
  have hall (a : Matrix m m A) (B : Matrix m n A) (C : Matrix n m A) (D : Matrix n n A) :
      fromBlocks a B C D ∈ S := by
    apply hm.induction (P:=fun a => fromBlocks a B C D ∈ S) ?_ ?_ a
    · rintro a ⟨u,rfl⟩
      exact hunit u B C D
    · exact hc.preimage (by fun_prop)
  intro x
  simpa only [Matrix.fromBlocks_toBlocks] using
    hall (Matrix.toBlocks₁₁ x) (Matrix.toBlocks₁₂ x) (Matrix.toBlocks₂₁ x) (Matrix.toBlocks₂₂ x)

lemma denseUnits_ringEquiv {R S : Type*} [Ring R] [Ring S] [TopologicalSpace R]
    [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (h : DenseUnits R) : DenseUnits S := by
  have hd : Dense (e '' {a : R | IsUnit a}) := e.surjective.denseRange.dense_image he h
  exact Dense.mono (fun b hb => by obtain ⟨a,ha,rfl⟩ := hb; exact ha.map e.toMonoidHom) hd

lemma denseUnits_matrix (h : DenseUnits A) (n : ℕ) : DenseUnits (Matrix (Fin n) (Fin n) A) := by
  induction n with
  | zero =>
    have : ∀ x : Matrix (Fin 0) (Fin 0) A, IsUnit x := fun x => by
      have hx : x=1 := Subsingleton.elim _ _
      rw [hx]; exact isUnit_one
    change Dense {x : Matrix (Fin 0) (Fin 0) A | IsUnit x}
    exact Dense.mono (fun x _ => this x) dense_univ
  | succ n ih =>
    have h1 : DenseUnits (Matrix (Fin 1) (Fin 1) A) := by
      exact denseUnits_ringEquiv (Matrix.uniqueRingEquiv (m:=Fin 1) (A:=A)).symm (by
        change Continuous (fun a : A => fun (_ _ : Fin 1) => a)
        fun_prop) h
    have hs := denseUnits_blocks ih h1
    exact denseUnits_ringEquiv (Matrix.reindexRingEquiv A (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1)))
      (by
        change Continuous (fun a : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) A =>
          fun i j => a (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
        fun_prop) hs
end Topology

variable {A : Type*} [CStarAlgebra A]
lemma DenseUnits.cstarMatrix (h : DenseUnits A) (n : ℕ) :
    DenseUnits (CStarMatrix (Fin n) (Fin n) A) := by
  have hm := denseUnits_matrix h n
  exact denseUnits_ringEquiv (CStarMatrix.ofMatrixRingEquiv (n:=Fin n) (A:=A))
    (CStarMatrix.ofMatrixL (m:=Fin n) (n:=Fin n) (A:=A)).continuous hm

lemma DenseUnits.stablyFinite [Nontrivial A] (h : DenseUnits A) : StablyFinite A := by
  intro n hn v hv
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact DenseUnits.finite (A:=CStarMatrix (Fin n) (Fin n) A) (h.cstarMatrix n) v hv


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma faithfulQuotient_nontrivial : Nontrivial V.FaithfulQuotient := by
  apply nontrivial_of_ne (1:V.FaithfulQuotient) 0
  intro h
  have h' : V.IsNull 1 := (V.nullIdeal.mk_eq_zero 1).mp ((map_one V.quotientHom).trans h)
  have hv : V.val 1=0 := by simpa only [IsNull,star_one,one_mul] using h'
  exact zero_ne_one (hv.symm.trans V.one)


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_SimpleAmbient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

universe u

lemma simple_stablyFinite_quotient {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (V : QuasiValue A) (ht : IsEmpty (TracialState A)) :
    ∃ (M : Type u) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M) := by
  let u : Ultrafilter ℕ := Ultrafilter.of atTop
  have hu : (u : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  let B := V.UltraQuotient u
  let : Nontrivial B := (V.ultra u).faithfulQuotient_nontrivial
  have hB : DenseUnits B := denseUnits_of_unitary_polar (V.ultra_unitary_polar u hu)
  obtain ⟨I,hI,hmax⟩ := maximal_closedStarIdeal_exists (A:=B)
  let : Nontrivial I.Quotient := I.quotient_nontrivial hI
  have hd := hB.map I.mkStarAlgHom I.mk_surjective
  have hmap : A →⋆ₐ[ℂ] I.Quotient :=
    I.mkStarAlgHom.comp ((V.ultraHom u).comp (QuasiValue.constHom (A:=A) (ι:=ℕ)))
  exact ⟨I.Quotient,inferInstance,inferInstance,I.quotient_simple hmax,hd.stablyFinite,
    no_tracialState_of_map hmap ht⟩

theorem simple_stablyFinite_traceless_exists_oai :
    ∃ (M : Type) (inst : CStarAlgebra M),
      letI := inst
      Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧ IsEmpty (TracialState M) := by
  let d : CuntzDimensionState ActualAlgebra := Classical.choice
    (cuntzDimensionState_nonempty fun k hk => actualAlgebra_matrix_not_properlyInfinite hk)
  let := actualAlgebra_nontrivial_separable.1
  exact simple_stablyFinite_quotient (QuasiValue.ofDimensionState d) actualAlgebra_no_tracialState


end KaplanskyConsequences

end

end OAI
end

theorem solution : type_of% @OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists_oai := @OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists_oai
