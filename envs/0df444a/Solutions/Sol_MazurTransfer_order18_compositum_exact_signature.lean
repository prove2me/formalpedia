-- Prove2me | solution 1 for MazurTransfer.order18_compositum_exact_signature
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:07:10.478483+00:00
-- url     : https://prove2.me/submissions/526b88eb-c857-480d-b0b3-d42ba692d928

import Mathlib
import Definitions.Def_MazurTransfer_Order18CompositumField
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

noncomputable section


/- Source module: EllipticCurves.Mathlib.Basic. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Material for Mathlib

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section

section Group

variable {G H : Type*} [Group G] [Group H]









end Group

section Units

variable {α : Type*} [Monoid α]





end Units

section modPow







namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup





































end Units.modPow

end modPow

section Ideal



end Ideal

section LinearAlgebra







end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}









end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]























variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]



-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.


-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement
















-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only


namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]



variable {A}



end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]



-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them


variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]







end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}



lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  convert resultant_add_right_deg g 1 g.natDegree 0 n (by simp)
  · simp
  rw [← C_1, resultant_C_zero_right, one_pow, mul_one, hg.coeff_natDegree, one_pow]











lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]



section

variable [Nontrivial R] {q : R[X]} {n : ℕ}



lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the
map that `mk g : R[X]_(g.natDegree) ≃ₗ AdjoinRoot g` turns into multiplication by `mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is
`q ↦ (q %ₘ g, q /ₘ g)`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · intro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

/-- The inverse of `Ψ` is division with remainder by `g`. -/
lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    change g * (w.2 : R[X]) + 1 * (w.1 : R[X]) = _
    simp
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester



end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)





/-- `mk g` is a linear equivalence from the polynomials of degree `< g.natDegree` onto
`AdjoinRoot g`, for `g` monic. -/
noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · intro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl



/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]



section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)



end Map

end AdjoinRoot



/-! ### The norm on a product algebra -/





section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}



namespace Factors





































end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}











/-- The discriminant of the power basis of `K[X]/(f)`, for `f` monic irreducible with
derivative of the generic degree, is the discriminant of the polynomial `f`. -/
theorem discr_powerBasis_eq_discr [Fact (Irreducible f)] [Algebra.IsSeparable K (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.derivative.natDegree = f.natDegree - 1) :
    Algebra.discr K (powerBasis hf.ne_zero).basis = f.discr := by
  have : Module.Finite K (AdjoinRoot f) := (powerBasis hf.ne_zero).finite
  rw [Algebra.discr_powerBasis_eq_norm, (powerBasis hf.ne_zero).finrank, powerBasis_dim,
    powerBasis_gen, minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one,
    aeval_eq, norm_mk_eq_resultant hf, hd, resultant_deriv (Fact.out : Irreducible f).degree_pos,
    hf.leadingCoeff, mul_one, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]























end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]





variable [NumberField K] [FiniteDimensional K L]









end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]









end Discriminant

end

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The real-cubic elliptic quotient of the `X₁(18)` sextic

This file records an explicit elliptic quotient of the standard genus-two
model for `X₁(18)`.  Its coefficient field is the totally real cubic field
generated by a root `tau` of

`T³ - 3T - 1`.

Only the algebraic point map is proved here.  In particular, this file makes
no assertion about the Mordell--Weil rank or the rational points of the
elliptic curve.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenRealCubicQuotient

noncomputable section

/-! ## The cubic coefficient field -/















/-- The polynomial `T³ - 3T - 1` is irreducible over `ℚ`. -/
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial := by
  exact MazurTransfer.order18_rational_cubics_irreducible.1








/-- The defining cubic relation in `K`. -/
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    AdjoinRoot.mk cubicPolynomial (X ^ 3 - 3 * X - 1 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul,
    map_ofNat, map_one, AdjoinRoot.mk_X] at h
  have h' : tau ^ 3 - 3 * tau - 1 = 0 := by
    simpa only [tau] using h
  linear_combination h'































/-! ## The elliptic quotient and its point map -/





















/-! ## Change to the rational-coefficient model -/











end

end MazurTorsion.XOneEighteenRealCubicQuotient

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q




theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial_irreducible
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 :=
  MazurTorsion.XOneEighteenRealCubicQuotient.tau_cubic

end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/



theorem relativePolynomial_monic : relativePolynomial.Monic := by
  simp only [relativePolynomial]
  monicity <;> norm_num

theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 3 := by
  simp only [relativePolynomial]
  compute_degree!









/-- The coefficient-field relation remains exact after base change. -/
theorem t_cubic : t ^ 3 = 3 * t + 1 := by
  simpa only [t, map_pow, map_mul, map_ofNat, map_add, map_one] using
    congrArg (algebraMap Q.K M) Q.tau_cubic

/-- The defining relation in the relative cubic algebra. -/
theorem s_cubic : s ^ 3 = 3 * s + 10 := by
  have h : AdjoinRoot.mk relativePolynomial relativePolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk relativePolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial Q.K) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : s ^ 3 - 3 * s - 10 = 0 := by
    simpa only [s] using h
  linear_combination h'

/-- The relative cubic algebra has the expected rank `3` over `K`, without
using irreducibility. -/
theorem finrank_M_over_K : Module.finrank Q.K M = 3 := by
  rw [(AdjoinRoot.powerBasis' relativePolynomial_monic).finrank]
  exact relativePolynomial_natDegree





/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumber. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Integral arithmetic for the `X₁(18)` two-division compositum

This file begins the independently checked class-number certificate for the
degree-nine two-division compositum.  The first essential step is to prove
that the relative cubic algebra from
`XOneEighteenTwoDivisionArithmetic` really is a field.  We do this without a
computer algebra oracle: if the two rational cubic fields met, their power
bases would be related by a rational change-of-basis matrix.  Their exact
discriminants have opposite signs, which is impossible because a basis
discriminant changes by the square of a determinant.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic

private theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

private def coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic









private theorem coefficientPowerBasis_dim : coefficientPowerBasis.dim = 3 := by
  rw [coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!



/-! ## The two incompatible cubic discriminants -/







/-! ## Linear disjointness of the two rational cubic fields -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]









/-- The compositum has degree nine over `ℚ`. -/
theorem finrank_M_over_rat : Module.finrank ℚ M = 9 := by
  rw [← Module.finrank_mul_finrank ℚ Q.K M, finrank_M_over_K,
    coefficientField_finrank]

end

end MazurTorsion.XOneEighteenTwoDivisionClassNumber

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrimitive. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A primitive element for the `X₁(18)` two-division compositum

This file gives a kernel-checked monogenic presentation of the degree-nine
two-division compositum.  The chosen generator is the simple difference
`u = t - s` of the two cubic generators.  Its polynomial is obtained by a
bounded resultant computation, but both the root identity and the inverse
formula recovering `t` are verified directly from the two cubic relations.

No assertion is made here about the ring of integers, an integral basis, or
the field discriminant.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionPrimitive

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

/-- A primitive-element candidate for the degree-nine compositum. -/
def primitiveElement : M := t - s

/-- The exact resultant polynomial of `t - s`. -/
def primitivePolynomial : Polynomial ℚ :=
  X ^ 9 - 18 * X ^ 7 + 27 * X ^ 6 + 81 * X ^ 5 -
    81 * X ^ 4 + 405 * X ^ 3 + 729 * X + 729

theorem primitivePolynomial_monic : primitivePolynomial.Monic := by
  simp only [primitivePolynomial]
  monicity <;> norm_num

theorem primitivePolynomial_natDegree :
    primitivePolynomial.natDegree = 9 := by
  simp only [primitivePolynomial]
  compute_degree!

/-- Direct verification of the bounded resultant identity. -/
theorem primitiveElement_root :
    Polynomial.aeval primitiveElement primitivePolynomial = 0 := by
  simp only [primitiveElement, primitivePolynomial, map_add, map_sub,
    map_mul, map_pow, map_ofNat, aeval_X]
  linear_combination
    (84 * s ^ 6 - 126 * s ^ 5 * t + 126 * s ^ 4 * t ^ 2 -
      252 * s ^ 4 - 84 * s ^ 3 * t ^ 3 + 378 * s ^ 3 * t -
      624 * s ^ 3 + 36 * s ^ 2 * t ^ 4 - 270 * s ^ 2 * t ^ 2 +
      441 * s ^ 2 * t - 9 * s * t ^ 5 + 99 * s * t ^ 3 -
      171 * s * t ^ 2 - 108 * s * t - 90 * s + t ^ 6 -
      15 * t ^ 4 + 28 * t ^ 3 + 36 * t ^ 2 - 12 * t + 541) *
        t_cubic +
    (-s ^ 6 + 9 * s ^ 5 * t - 36 * s ^ 4 * t ^ 2 + 15 * s ^ 4 +
      153 * s ^ 3 * t + 101 * s ^ 3 - 108 * s ^ 2 * t ^ 2 -
      198 * s ^ 2 * t - 36 * s ^ 2 + 171 * s * t ^ 2 +
      108 * s * t + 120 * s - 234 * t - 127) * s_cubic

/-- A rational polynomial which recovers the coefficient-field generator
`t` from the primitive element. -/
def coefficientGeneratorPolynomial : Polynomial ℚ :=
  C (1 / 2673) *
    (1944 - 1944 * X + 2511 * X ^ 2 - 810 * X ^ 3 +
      135 * X ^ 4 + 216 * X ^ 5 - 72 * X ^ 6 - 6 * X ^ 7 +
      4 * X ^ 8)

/-- Direct verification of the inverse elimination identity. -/
theorem coefficientGenerator_reconstruction :
    Polynomial.aeval primitiveElement coefficientGeneratorPolynomial = t := by
  simp only [primitiveElement, coefficientGeneratorPolynomial, map_mul,
    aeval_C, map_add, map_sub, map_pow, map_ofNat, aeval_X]
  rw [map_div₀, map_one, map_ofNat]
  have helim :
      2673 * t -
        (1944 - 1944 * (t - s) + 2511 * (t - s) ^ 2 -
          810 * (t - s) ^ 3 + 135 * (t - s) ^ 4 +
          216 * (t - s) ^ 5 - 72 * (t - s) ^ 6 -
          6 * (t - s) ^ 7 + 4 * (t - s) ^ 8) = 0 := by
    linear_combination
      (224 * s ^ 5 - 280 * s ^ 4 * t + 210 * s ^ 4 +
        224 * s ^ 3 * t ^ 2 - 210 * s ^ 3 * t - 768 * s ^ 3 -
        112 * s ^ 2 * t ^ 3 + 126 * s ^ 2 * t ^ 2 +
        744 * s ^ 2 * t - 1894 * s ^ 2 + 32 * s * t ^ 4 -
        42 * s * t ^ 3 - 336 * s * t ^ 2 + 986 * s * t -
        510 * s - 4 * t ^ 5 + 6 * t ^ 4 + 60 * t ^ 3 -
        202 * t ^ 2 + 51 * t + 264) * t_cubic +
      (-4 * s ^ 5 + 32 * s ^ 4 * t - 6 * s ^ 4 -
        112 * s ^ 3 * t ^ 2 + 42 * s ^ 3 * t + 60 * s ^ 3 -
        126 * s ^ 2 * t ^ 2 + 336 * s ^ 2 * t + 382 * s ^ 2 -
        96 * s * t ^ 2 - 284 * s * t + 195 * s +
        256 * t ^ 2 - 546 * t + 168) * s_cubic
  linear_combination (-1 / 2673 : ℚ) * helim

theorem coefficientGenerator_mem_adjoin :
    t ∈ Algebra.adjoin ℚ ({primitiveElement} : Set M) := by
  rw [← coefficientGenerator_reconstruction]
  exact Polynomial.aeval_mem_adjoin_singleton ℚ primitiveElement

theorem relativeGenerator_mem_adjoin :
    s ∈ Algebra.adjoin ℚ ({primitiveElement} : Set M) := by
  have hu : primitiveElement ∈
      Algebra.adjoin ℚ ({primitiveElement} : Set M) :=
    Algebra.self_mem_adjoin_singleton ℚ primitiveElement
  have hsub := (Algebra.adjoin ℚ ({primitiveElement} : Set M)).sub_mem
    coefficientGenerator_mem_adjoin hu
  simpa only [primitiveElement, sub_sub_cancel] using hsub

/-- The single element `t - s` generates the entire compositum over `ℚ`. -/
theorem primitiveElement_adjoin_eq_top :
    Algebra.adjoin ℚ ({primitiveElement} : Set M) = ⊤ := by
  let A : Subalgebra ℚ M :=
    Algebra.adjoin ℚ ({primitiveElement} : Set M)
  have ht : t ∈ A := coefficientGenerator_mem_adjoin
  have hs : s ∈ A := relativeGenerator_mem_adjoin
  have hcoeff : ∀ a : Q.K, algebraMap Q.K M a ∈ A := by
    intro a
    induction a using AdjoinRoot.induction_on with
    | ih q =>
        induction q using Polynomial.induction_on with
        | C r =>
            simp only [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
            change algebraMap Q.K M (algebraMap ℚ Q.K r) ∈ A
            rw [← IsScalarTower.algebraMap_apply ℚ Q.K M]
            exact A.algebraMap_mem r
        | add p q hp hq =>
            simpa only [map_add] using A.add_mem hp hq
        | monomial n r hr =>
            simp only [map_mul, map_pow, AdjoinRoot.mk_C,
              AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
            change algebraMap Q.K M (algebraMap ℚ Q.K r) *
              t ^ (n + 1) ∈ A
            rw [← IsScalarTower.algebraMap_apply ℚ Q.K M]
            exact A.mul_mem (A.algebraMap_mem r) (A.pow_mem ht (n + 1))
  have hpolynomial : ∀ p : Polynomial Q.K,
      AdjoinRoot.mk relativePolynomial p ∈ A := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        simpa only [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq] using
          hcoeff a
    | add p q hp hq =>
        simpa only [map_add] using A.add_mem hp hq
    | monomial n a ha =>
        simp only [map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
        simpa only [s] using
          A.mul_mem (hcoeff a) (A.pow_mem hs (n + 1))
  apply Algebra.eq_top_iff.2
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p => exact hpolynomial p

/-- Integrality follows from the explicit monic degree-nine equation. -/
theorem primitiveElement_isIntegral : IsIntegral ℚ primitiveElement :=
  ⟨primitivePolynomial, primitivePolynomial_monic, primitiveElement_root⟩

/-- The power basis generated by `t - s`. -/
def primitivePowerBasis : PowerBasis ℚ M :=
  PowerBasis.ofAdjoinEqTop primitiveElement_isIntegral
    primitiveElement_adjoin_eq_top

@[simp]
theorem primitivePowerBasis_gen :
    primitivePowerBasis.gen = primitiveElement := by
  rw [primitivePowerBasis, PowerBasis.ofAdjoinEqTop_gen]

theorem primitiveElement_minpoly_natDegree :
    (minpoly ℚ primitiveElement).natDegree = 9 := by
  calc
    (minpoly ℚ primitiveElement).natDegree = primitivePowerBasis.dim := by
      simpa only [primitivePowerBasis_gen] using
        primitivePowerBasis.natDegree_minpoly
    _ = Module.finrank ℚ M := primitivePowerBasis.finrank.symm
    _ = 9 := finrank_M_over_rat

/-- The resultant polynomial is exactly the minimal polynomial, rather than
merely an annihilating polynomial. -/
theorem primitiveElement_minpoly :
    minpoly ℚ primitiveElement = primitivePolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic primitiveElement_isIntegral)
    primitivePolynomial_monic
    (minpoly.dvd ℚ primitiveElement primitiveElement_root)
    (by rw [primitivePolynomial_natDegree,
      primitiveElement_minpoly_natDegree])).symm

theorem primitivePolynomial_irreducible :
    Irreducible primitivePolynomial := by
  rw [← primitiveElement_minpoly]
  exact minpoly.irreducible primitiveElement_isIntegral

private theorem primitiveRoot_satisfies_minpoly :
    Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
      (minpoly ℚ primitivePowerBasis.gen) = 0 := by
  rw [primitivePowerBasis_gen, primitiveElement_minpoly]
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root primitivePolynomial

private theorem primitivePowerBasis_root :
    Polynomial.aeval primitivePowerBasis.gen primitivePolynomial = 0 := by
  rw [primitivePowerBasis_gen]
  exact primitiveElement_root

/-- The explicit monogenic presentation of the compositum. -/
def primitiveAdjoinRootEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] M :=
  AdjoinRoot.equiv' primitivePolynomial primitivePowerBasis
    primitiveRoot_satisfies_minpoly primitivePowerBasis_root

instance primitivePolynomial_irreducibleFact :
    Fact (Irreducible primitivePolynomial) :=
  ⟨primitivePolynomial_irreducible⟩

end

end MazurTorsion.XOneEighteenTwoDivisionPrimitive

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSignature. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Real places of the `X₁(18)` two-division compositum

This file starts the signature calculation needed by the unit square-class
count.  The relative cubic `S³ - 3S - 10` has at most one real root.  Hence
restriction to the real cubic coefficient field injects the real embeddings
of the degree-nine compositum into the three embeddings of that coefficient
field.

The complementary lower bound is kept separate: it will be supplied by the
signed discriminant certificate for a rational power basis.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionSignature

noncomputable section

open NumberField NumberField.InfinitePlace
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

private theorem unique_real_root_twoDivisionCubic
    {a b : ℝ}
    (ha : a ^ 3 = 3 * a + 10)
    (hb : b ^ 3 = 3 * b + 10) :
    a = b := by
  by_contra hab
  have hfactor :
      (a - b) * (a ^ 2 + a * b + b ^ 2 - 3) = 0 := by
    linear_combination ha - hb
  have hquad : a ^ 2 + a * b + b ^ 2 = 3 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact (hab (sub_eq_zero.mp h)).elim
    · linarith
  have ha_sq_le : a ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (a + 2 * b)]
  have ha_le : a ≤ 2 := by
    nlinarith [sq_nonneg (a - 2)]
  have hcubic_le : a ^ 3 - 3 * a ≤ 2 := by
    have hnonneg : 0 ≤ (2 - a) * (a + 1) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr ha_le) (sq_nonneg (a + 1))
    nlinarith
  nlinarith

private def restrictRealEmbedding :
    { φ : M →+* ℂ // ComplexEmbedding.IsReal φ } → (Q.K →+* ℂ) :=
  fun φ ↦ φ.1.comp (algebraMap Q.K M)

private theorem restrictRealEmbedding_injective :
    Function.Injective restrictRealEmbedding := by
  intro φ ψ hrestrict
  apply Subtype.ext
  apply AdjoinRoot.ringHom_ext hrestrict
  let a : ℝ := φ.2.embedding s
  let b : ℝ := ψ.2.embedding s
  have ha : a ^ 3 = 3 * a + 10 := by
    simpa only [a, map_pow, map_mul, map_ofNat, map_add] using
      congrArg φ.2.embedding s_cubic
  have hb : b ^ 3 = 3 * b + 10 := by
    simpa only [b, map_pow, map_mul, map_ofNat, map_add] using
      congrArg ψ.2.embedding s_cubic
  have hab : a = b := unique_real_root_twoDivisionCubic ha hb
  calc
    φ.1 (AdjoinRoot.root relativePolynomial) = (a : ℂ) := by
      symm
      simpa only [a, s] using φ.2.coe_embedding_apply s
    _ = (b : ℂ) := congrArg ((↑·) : ℝ → ℂ) hab
    _ = ψ.1 (AdjoinRoot.root relativePolynomial) := by
      simpa only [b, s] using ψ.2.coe_embedding_apply s

private theorem coefficientField_finrank :
    Module.finrank ℚ Q.K = 3 := by
  calc
    Module.finrank ℚ Q.K = Q.cubicPolynomial.natDegree :=
      (AdjoinRoot.powerBasis Q.cubicPolynomial_irreducible.ne_zero).finrank
    _ = 3 := by
      simp only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
      compute_degree!

/-- The degree-nine two-division compositum has at most three real places.
The eventual unit square-class computation is the named downstream consumer
of this bound. -/
theorem nrRealPlaces_le_three : nrRealPlaces M ≤ 3 := by
  classical
  rw [← card_real_embeddings]
  calc
    Fintype.card { φ : M →+* ℂ // ComplexEmbedding.IsReal φ } ≤
        Fintype.card (Q.K →+* ℂ) :=
      Fintype.card_le_of_injective restrictRealEmbedding
        restrictRealEmbedding_injective
    _ = Module.finrank ℚ Q.K := NumberField.Embeddings.card Q.K ℂ
    _ = 3 := coefficientField_finrank

end

end MazurTorsion.XOneEighteenTwoDivisionSignature

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionDiscriminant. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The sign of the `X₁(18)` two-division discriminant

This file gives a bounded Euclidean certificate for the sign of the
degree-nine primitive polynomial.  Each line of the remainder chain is a
polynomial identity checked by `ring`; the resultant identities then show
that the discriminant is negative.  Transporting the corresponding basis
discriminant to an integral basis proves that the number-field discriminant
is negative, and hence that the number of complex places is odd.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionDiscriminant

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive

private def p₀ : Polynomial ℚ := primitivePolynomial

private def p₁ : Polynomial ℚ :=
  X ^ 8 - 14 * X ^ 6 + 18 * X ^ 5 + 45 * X ^ 4 -
    36 * X ^ 3 + 135 * X ^ 2 + 81

private def p₂ : Polynomial ℚ :=
  -4 * X ^ 7 + 9 * X ^ 6 + 36 * X ^ 5 - 45 * X ^ 4 +
    270 * X ^ 3 + 648 * X + 729

private def p₃ : Polynomial ℚ :=
  X ^ 6 + 432 * X ^ 5 + 1395 * X ^ 4 + 1854 * X ^ 3 +
    4752 * X ^ 2 + 8748 * X + 7857

private def p₄ : Polynomial ℚ :=
  -862 * X ^ 5 - 2796 * X ^ 4 - 3705 * X ^ 3 -
    9513 * X ^ 2 - 17550 * X - 15795

private def p₅ : Polynomial ℚ :=
  -2563 * X ^ 4 + 13305 * X ^ 3 - 12276 * X ^ 2 +
    44037 * X + 75708

private def p₆ : Polynomial ℚ :=
  -439913 * X ^ 3 + 123783 * X ^ 2 - 1979568 * X - 2717793

private def p₇ : Polynomial ℚ :=
  1577 * X ^ 2 + 1829 * X - 1147

private def p₈ : Polynomial ℚ := -39 * X - 29

private def p₉ : Polynomial ℚ := -1

/-- One adjacent-degree Euclidean step for a resultant.  The explicit
remainder chains below always have degrees `k+2`, `k+1`, and `k` and a
linear quotient. -/
private theorem resultant_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) :
    f.resultant g = g.leadingCoeff ^ 2 * c ^ (k + 1) * g.resultant r := by
  change resultant f g f.natDegree g.natDegree = _
  rw [hf, hg, hrel]
  rw [resultant_add_mul_left (f := C c * r) (g := g) (p := q)
    (m := k + 2) (n := k + 1)]
  · rw [show k + 2 = k + 2 by rfl]
    rw [resultant_add_left_deg (f := C c * r) (g := g)
      (m := k) (n := k + 1) (k := 2)]
    · rw [resultant_C_mul_left, resultant_comm]
      rw [Even.neg_one_pow (⟨k + 1, by omega⟩),
        Even.neg_one_pow (Nat.even_mul_succ_self k)]
      rw [← hg, coeff_natDegree]
      rw [← hr]
      simp only [one_mul]
      ring
    · exact (natDegree_C_mul_le c r).trans_eq hr
  · omega
  · omega

private theorem resultant_neg_iff_step {f g r q : Polynomial ℚ} {c : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : f = C c * r + g * q) (hc : 0 < c) :
    f.resultant g < 0 ↔ g.resultant r < 0 := by
  rw [resultant_step hf hg hr hq hrel]
  have hg₀ : g ≠ 0 := by
    intro hzero
    rw [hzero] at hg
    simp only [natDegree_zero] at hg
    omega
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg₀
  have hfactor : 0 < g.leadingCoeff ^ 2 * c ^ (k + 1) :=
    mul_pos (sq_pos_of_ne_zero hlc) (pow_pos hc _)
  constructor
  · intro hneg
    exact neg_of_mul_neg_right hneg hfactor.le
  · exact mul_neg_of_pos_of_neg hfactor

private theorem resultant_neg_iff_step_scaled
    {f g r q : Polynomial ℚ} {c d : ℚ} {k : ℕ}
    (hf : f.natDegree = k + 2) (hg : g.natDegree = k + 1)
    (hr : r.natDegree = k) (hq : q.natDegree ≤ 1)
    (hrel : C d * f = C c * r + g * q) (hc : 0 < c) (hd : 0 < d) :
    f.resultant g < 0 ↔ g.resultant r < 0 := by
  have hscaledDegree : (C d * f).natDegree = k + 2 := by
    rw [natDegree_C_mul hd.ne', hf]
  have hstep := resultant_neg_iff_step hscaledDegree hg hr hq hrel hc
  have hscaleResultant :
      (C d * f).resultant g = d ^ (k + 1) * f.resultant g := by
    change resultant (C d * f) g (C d * f).natDegree g.natDegree = _
    rw [natDegree_C_mul hd.ne', hf, hg, resultant_C_mul_left]
  rw [hscaleResultant] at hstep
  have hpow : 0 < d ^ (k + 1) := pow_pos hd _
  constructor
  · intro hneg
    exact hstep.mp (mul_neg_of_pos_of_neg hpow hneg)
  · intro hneg
    exact neg_of_mul_neg_right (hstep.mpr hneg) hpow.le

private theorem p₀_degree : p₀.natDegree = 9 := by
  exact primitivePolynomial_natDegree

private theorem p₁_degree : p₁.natDegree = 8 := by
  simp only [p₁]
  compute_degree!

private theorem p₂_degree : p₂.natDegree = 7 := by
  simp only [p₂]
  compute_degree!

private theorem p₃_degree : p₃.natDegree = 6 := by
  simp only [p₃]
  compute_degree!

private theorem p₄_degree : p₄.natDegree = 5 := by
  simp only [p₄]
  compute_degree!

private theorem p₅_degree : p₅.natDegree = 4 := by
  simp only [p₅]
  compute_degree!

private theorem p₆_degree : p₆.natDegree = 3 := by
  simp only [p₆]
  compute_degree!

private theorem p₇_degree : p₇.natDegree = 2 := by
  simp only [p₇]
  compute_degree!

private theorem p₈_degree : p₈.natDegree = 1 := by
  simp only [p₈]
  compute_degree!

private theorem p₉_degree : p₉.natDegree = 0 := by
  simp only [p₉]
  compute_degree!

private theorem p₀_resultant_neg_iff_p₁ :
    p₀.resultant p₁ < 0 ↔ p₁.resultant p₂ < 0 := by
  apply resultant_neg_iff_step (q := X) (c := 1) (k := 7)
  · simpa using p₀_degree
  · simpa using p₁_degree
  · simpa using p₂_degree
  · simp
  · simp only [p₀, p₁, p₂, primitivePolynomial]
    norm_num
    ring
  · norm_num

private theorem p₁_resultant_neg_iff_p₂ :
    p₁.resultant p₂ < 0 ↔ p₂.resultant p₃ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -4 * X - 9) (c := 1) (d := 16) (k := 6)
  · simpa using p₁_degree
  · simpa using p₂_degree
  · simpa using p₃_degree
  · compute_degree!
  · simp only [p₁, p₂, p₃]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₂_resultant_neg_iff_p₃ :
    p₂.resultant p₃ < 0 ↔ p₃.resultant p₄ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 1737 - 4 * X) (c := 864) (d := 1) (k := 5)
  · simpa using p₂_degree
  · simpa using p₃_degree
  · simpa using p₄_degree
  · compute_degree!
  · simp only [p₂, p₃, p₄]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₃_resultant_neg_iff_p₄ :
    p₃.resultant p₄ < 0 ↔ p₄.resultant p₅ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -431 * X - 184794) (c := 3) (d := 371522) (k := 4)
  · simpa using p₃_degree
  · simpa using p₄_degree
  · simpa using p₅_degree
  · compute_degree!
  · simp only [p₃, p₄, p₅]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₄_resultant_neg_iff_p₅ :
    p₄.resultant p₅ < 0 ↔ p₅.resultant p₆ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 2209306 * X + 18635058) (c := 557283)
    (d := 6568969) (k := 3)
  · simpa using p₄_degree
  · simpa using p₅_degree
  · simpa using p₆_degree
  · compute_degree!
  · simp only [p₄, p₅, p₆]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₅_resultant_neg_iff_p₆ :
    p₅.resultant p₆ < 0 ↔ p₆.resultant p₇ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := 1127497019 * X - 5535786636) (c := 343373147568)
    (d := 193523447569) (k := 2)
  · simpa using p₅_degree
  · simpa using p₆_degree
  · simpa using p₇_degree
  · compute_degree!
  · simp only [p₅, p₆, p₇]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₆_resultant_neg_iff_p₇ :
    p₆.resultant p₇ < 0 ↔ p₇.resultant p₈ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -693742801 * X + 999806668) (c := 193523447569)
    (d := 2486929) (k := 1)
  · simpa using p₆_degree
  · simpa using p₇_degree
  · simpa using p₈_degree
  · compute_degree!
  · simp only [p₆, p₇, p₈]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₇_resultant_neg_iff_p₈ :
    p₇.resultant p₈ < 0 ↔ p₈.resultant p₉ < 0 := by
  apply resultant_neg_iff_step_scaled
    (q := -61503 * X - 25598) (c := 2486929) (d := 1521) (k := 0)
  · simpa using p₇_degree
  · simpa using p₈_degree
  · simpa using p₉_degree
  · compute_degree!
  · simp only [p₇, p₈, p₉]
    simp only [Polynomial.C_ofNat]
    norm_num
    ring
  · norm_num
  · norm_num

private theorem p₈_resultant_p₉_neg : p₈.resultant p₉ < 0 := by
  norm_num [p₉, resultant_C_right, p₈_degree]

private theorem p₀_resultant_p₁_neg : p₀.resultant p₁ < 0 := by
  exact p₀_resultant_neg_iff_p₁.mpr
    (p₁_resultant_neg_iff_p₂.mpr
      (p₂_resultant_neg_iff_p₃.mpr
        (p₃_resultant_neg_iff_p₄.mpr
          (p₄_resultant_neg_iff_p₅.mpr
            (p₅_resultant_neg_iff_p₆.mpr
              (p₆_resultant_neg_iff_p₇.mpr
                (p₇_resultant_neg_iff_p₈.mpr p₈_resultant_p₉_neg)))))))

private theorem primitivePolynomial_derivative :
    primitivePolynomial.derivative = C 9 * p₁ := by
  simp only [primitivePolynomial, p₁, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    Nat.cast_ofNat, mul_one, zero_mul]
  simp only [Polynomial.C_ofNat]
  norm_num
  ring

private theorem primitivePolynomial_resultant_derivative_neg :
    resultant primitivePolynomial primitivePolynomial.derivative 9 8 < 0 := by
  rw [primitivePolynomial_derivative, resultant_C_mul_right]
  apply mul_neg_of_pos_of_neg
  · norm_num
  · simpa only [p₀, primitivePolynomial_natDegree, p₁_degree] using
      p₀_resultant_p₁_neg

/-- The degree-nine primitive polynomial has negative discriminant.  The
proof is the finite pseudo-remainder chain above, rather than an external
computer-algebra discriminant computation. -/
theorem primitivePolynomial_discr_neg : primitivePolynomial.discr < 0 := by
  have hdegree : 0 < primitivePolynomial.degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [primitivePolynomial_natDegree]; norm_num)
  have hres := Polynomial.resultant_deriv (f := primitivePolynomial) hdegree
  rw [primitivePolynomial_natDegree,
    primitivePolynomial_monic.leadingCoeff] at hres
  norm_num at hres
  rw [← hres]
  exact primitivePolynomial_resultant_derivative_neg

private def rootPowerBasis : PowerBasis ℚ (AdjoinRoot primitivePolynomial) :=
  AdjoinRoot.powerBasis primitivePolynomial_monic.ne_zero

private theorem primitivePolynomial_derivative_natDegree :
    primitivePolynomial.derivative.natDegree =
      primitivePolynomial.natDegree - 1 := by
  rw [primitivePolynomial_derivative,
    natDegree_C_mul (by norm_num : (9 : ℚ) ≠ 0), p₁_degree,
    primitivePolynomial_natDegree]

private theorem rootPowerBasis_discriminant :
    Algebra.discr ℚ rootPowerBasis.basis = primitivePolynomial.discr := by
  exact AdjoinRoot.discr_powerBasis_eq_discr primitivePolynomial_monic
    primitivePolynomial_derivative_natDegree

private def primitiveDiscriminantBasis :
    Basis (Fin rootPowerBasis.dim) ℚ M :=
  rootPowerBasis.basis.map primitiveAdjoinRootEquiv.toLinearEquiv

private theorem primitiveDiscriminantBasis_discriminant :
    Algebra.discr ℚ primitiveDiscriminantBasis =
      primitivePolynomial.discr := by
  rw [← rootPowerBasis_discriminant]
  calc
    Algebra.discr ℚ primitiveDiscriminantBasis =
        Algebra.discr ℚ
          (primitiveAdjoinRootEquiv ∘ rootPowerBasis.basis) := by
            congr 1
    _ = Algebra.discr ℚ rootPowerBasis.basis :=
      (Algebra.discr_eq_discr_of_algEquiv rootPowerBasis.basis
        primitiveAdjoinRootEquiv).symm

private theorem primitiveDiscriminantBasis_discr_neg :
    Algebra.discr ℚ primitiveDiscriminantBasis < 0 := by
  rw [primitiveDiscriminantBasis_discriminant]
  exact primitivePolynomial_discr_neg

/-- The number-field discriminant of the two-division compositum is
negative. -/
theorem field_discriminant_neg : NumberField.discr M < 0 := by
  let integralBasis' : Basis (Fin rootPowerBasis.dim) ℚ M :=
    (integralBasis M).reindex
      ((integralBasis M).indexEquiv primitiveDiscriminantBasis)
  have hintegral :
      Algebra.discr ℚ integralBasis' = (NumberField.discr M : ℚ) := by
    dsimp only [integralBasis']
    rw [Basis.coe_reindex, Algebra.discr_reindex, ← NumberField.coe_discr]
  have hchange :
      Algebra.discr ℚ primitiveDiscriminantBasis =
        (integralBasis'.toMatrix primitiveDiscriminantBasis).det ^ 2 *
          Algebra.discr ℚ integralBasis' := by
    nth_rw 1 [← integralBasis'.toMatrix_map_vecMul primitiveDiscriminantBasis]
    rw [Algebra.discr_of_matrix_vecMul]
  rw [hintegral] at hchange
  have hcast : (NumberField.discr M : ℚ) < 0 := by
    nlinarith [sq_nonneg
      (integralBasis'.toMatrix primitiveDiscriminantBasis).det,
      primitiveDiscriminantBasis_discr_neg]
  exact_mod_cast hcast

/-- The degree-nine two-division compositum has an odd number of complex
places. -/
theorem nrComplexPlaces_odd :
    Odd (NumberField.InfinitePlace.nrComplexPlaces M) := by
  have hsign := NumberField.sign_discr M
  rw [Int.sign_eq_neg_one_of_neg field_discriminant_neg] at hsign
  exact (neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).mp hsign.symm

end

end MazurTorsion.XOneEighteenTwoDivisionDiscriminant

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionExactSignature. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The exact signature of the `X₁(18)` two-division compositum

The compositum has degree nine, at most three real places, and an odd
number of complex places.  The signature identity

`r₁ + 2 r₂ = 9`

then forces `(r₁, r₂) = (3, 3)`.
-/

open Module NumberField NumberField.InfinitePlace

namespace MazurTorsion.XOneEighteenTwoDivisionExactSignature

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSignature
open MazurTorsion.XOneEighteenTwoDivisionDiscriminant

private theorem exact_signature :
    nrRealPlaces M = 3 ∧ nrComplexPlaces M = 3 := by
  have hsignature := card_add_two_mul_card_eq_rank (K := M)
  rw [finrank_M_over_rat] at hsignature
  have hreal := nrRealPlaces_le_three
  obtain ⟨k, hk⟩ := nrComplexPlaces_odd
  constructor <;> omega

/-- The degree-nine compositum has exactly three real places. -/
theorem nrRealPlaces_eq_three : nrRealPlaces M = 3 :=
  exact_signature.1

/-- The degree-nine compositum has exactly three pairs of complex places. -/
theorem nrComplexPlaces_eq_three : nrComplexPlaces M = 3 :=
  exact_signature.2

end

end MazurTorsion.XOneEighteenTwoDivisionExactSignature

end

theorem solution :
Module.finrank ℚ MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 9 ∧
  NumberField.InfinitePlace.nrRealPlaces MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 3 ∧
  NumberField.InfinitePlace.nrComplexPlaces MazurTorsion.XOneEighteenTwoDivisionArithmetic.M = 3 := by
  exact ⟨MazurTorsion.XOneEighteenTwoDivisionClassNumber.finrank_M_over_rat, MazurTorsion.XOneEighteenTwoDivisionExactSignature.nrRealPlaces_eq_three, MazurTorsion.XOneEighteenTwoDivisionExactSignature.nrComplexPlaces_eq_three⟩

#print axioms solution
end
